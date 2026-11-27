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
private theorem tv_b11_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149229249241009241249349348049048008208041205248000201248041041000009024904a49249249040248249249040249049249249009209249249201241049249040248141249241009201249248200041249040201248124159248200049205649249040248144a0004925924120904124964904800026d2c9a0905934824100920482420d34c301348125148a4104924d241200048249a49a6020db4c30030810824924d34d200a4134020004900904d04904024824104a24dc61209200049a4d24120904124934904800024d269a0904134024100920904920820824920924800020124822104924924104124934934924904104d24924120504134924904800064934930902490904904000104024125934900100820da49351b78208249279b4d60820935934d35824924924934d600008369a682c1049001040248240800049049009041049241201200209249240041041249249048000249249249041049249249208209249249241041249249048141049249241208209249248341124249841041249049b4104c04d209240001009a413480012413682492082692492090cec1830c3cf608209a492482418032cb24908824e34820e449209049c7184040144824824d241009209009249240040240241241009209248201009241009041040248249000040249049649a18049309204849249249241009a0924924924004024124104100000924820100924104904104000824900004004904934920804920510514924924904024824924904024904924924900920924924920124104904904000014124924100020924924820104124904020124812412d249040009240a49249041a49024a2000124920124084124924904904924920920920d349201009240920a24a4f249041249028a4c20904024902524924824824804120934c04902484104104120000104820920924104134904800004000004034904104924120000924124904824824104104924000904124d249208208249249241008069a4d04920460904124124810504104104800814104d241200208209249241841041249248208041249249049049049249249209209249249241041049249000141049249248208209249249040209041241248124040041000041009a4920824920020924924000024924824824804f24904124904100926d341241208249249000008249249209209269248241341249248248248040241000241049209241201241049251a1804d309349040301348249208040249049209241009241248249248049008008208049208208000201248041241000041049204904925249348209348149249249209205148209349249348249249249249200008249a4824124936d248348121a49a0800024814924924920920494404124924904814924924924920924924d241240924144924a292492492493480612092692698448449249452492492493490082412493492049090490080010402412412410012090413a937584824800144934904824105124d241200008349a68241049001248040240a4124100024130904924924804826920824d34d24d30924924924934800026da69209041240049201209041049241241201249241049241049249249049049241049249249241249249249249000049a41241301249349241241209a41041049a41a4c000201248249000040269048009249048008241249249241a08209a49248241208269249209000049269241209c6c00060336c240920924a49249041049029249249241240a2904124924904904924924924124000024924804814924924920920424934130c049029249249241240928a08249249041029249249241241249248248248249040040049024828924945249249249049008041249009204908924928a49249249209201048249201240921209341000069048249248201b4124900004924900904820924924004000006904c04000134934984904134db41011a08249249241240148248201041241209249249049049241049249241241249249249049000009a4120100904936d24804820820924924104024924820824820924924920920924820924924824824924924920920000134924124100926da4904904124820820926834d00004824904920000804920900124924904904004124124924104104124900024104924924c20000124d241041248000201248248124149a4820004d20524924904024814d348241009204a0004924124100904124904924800020d20920804484924824100920924924104924124924924834824924934904902924924104d241249249041249008248249249204001001249248224905249248001048149249249201204249249248040128a41008248208200000041041048108241241041201249249040248249249041349049249249209209249249241240a49249349049049249249209209249249241241149041041249248124124900049249049201049241241240001249249248041249049249029245224905041249048248041249049049049249249209209249241249240a4914912400024924824900004d05865120000924924b2400013412486682492c924902484924924100b20924924104924124924924004024924924804905924924100f60934904104000824124d341011c08209201009241049349040060000040040249049049208049205109269040009240a49249041249024a20009241009040841249040249009a4920824920892124924904034824924904024904924924920920924924924124134924924804014924924920d209249249241241049249048040141249259201008249249a40201041240209248124249249208049029249249241240a49249249049024a24249249a4824804124904024902482494104924120b20000924900924104124924804000024924904904924924510504124904804804124904924904924924920920924924924924114914912400024130d24900824920924920104924d34924020924824924824924924904490524924800134814924924900d205148009049041048241041249241200009a48249a01121249248000248149249208209204944000248201248108009208049201349241041240924124969249249209204a29041209208209869209208009204824949249249209204941249241009205049249248348049249249049008249208049204904924941049241209201049241241241249249248248249249049249049249249200009249209240209248341348000249249269008259249059a09249249a40920a49249040249029249249201240a2904120924824904820824924924000124924d248144249249000049029249241041240928800049040249021001241009240269248209248224824929249249241240945208241249049204904929249249241240928249248201340a0924924904900924924920920104924100924092092492820924824134020924824924824924924904904924920924920924924924000124924126804124904924900004924924920104924920924124924924812424a24c30004120926924904004824920004d85934920904124964d24800026c2c9a4904004925934920904924824100120925924304304134d44924834834d24925906904800104166d44820824825934920820820b38a24000100124944800020024936904366934b38924120926930800000c249a4da41001208349249248040249240008249209200001069641a4c200041a590492012492490400482496490c10c104d249249201009249249241a412492492410012092082082c9269040008009249a4134126964d2480c1a412ce24904814490004924904120000a24b00b2400016492496480000692480690492592492050412490482480002082002c904104d349201000000009001a4124964924800024924820900005024005930000924924b26000144904046826d2c9a4904104824120920000904800b241041069248040000241208069049a5934920482926930800104824924d24100120924800104934934824104124924d200009b09a4a24136d04924934024124920904004824924906106104924924920d20d249249241241249349061061049249241049a4020920924934820004004924920934824924a20c00c00924924924834820d34924920100924906020924826800c04034d06d008009041241340049249241001209249241049a4124924924824824924924904904d24924d241b4124924924834824924934906904924104104924d209205144001249241048041269069269000049249249201049249249241349249348141049241209201049241249a4124924924824824924904924904924924920000924920824000106130030000024924926900004904d201a0a249a49a4104100904824804126984926904924db4920d209249b69249a4136d24924812124d04100000904924924820004124900024924920904820924924834000136934934804900034924904184d341361a09248249249240249241208000049249208209209249249241241a4924824824824924920820920924924820824804124124924d04000800924924100020024924904904924924100134124924924904904124924824020124124836924d241200041b4d04d201048249209041041209248249009249248201041249248208248249249249049049249249209209249248248248249249249049049249269209209248208209249241240a2880024124824100824920924920000924924924020924824924824924924902820924824124020924824924824924924904904924920924920924924924000124924100000020824104d00004124124920000c00124124124924924814104db4121920104836120924124936d24824824926d8493490492492692042490610412490492410490cb209a40001009a41248000201248041269248249040009249209241001209248249040049a4920924104020820924824904936924826d209249041201a48241049241241041249049049249008341049049209000049049001079bcdb5904d609e730616414482092410410092412490402012482490000402690492000080492010492492092410412482012480002492482690000492490492000482492092410012692482490082492490492092412482082034cc249200008049208000248248048041249049049008249209209209241241349240300001b61b6c2400010416400412481000692482d920104924920d6400012412012480410493482490492492c9208001a49249348041249248249008241249049201041241009241a49a4924820826924924900004d349249308208249249240001309249248269249249028209a4924924000104134934c20820924924900004004924d209a49249240000208000000000208249359000008000049200008019249243249a49b481248248, 1161157431922880, 176007898337472, 176007898337472, 1161164015079872, 2926047329103871894500397539599507536832125555522, 105639091177537, 
    105639091177537, 2923103628355649043345064893418267210537546849090, 88064621873217, 88064621873217, 72670922213441, 283777154746433, 
    72670922213441, 72670922213441, 72670922213441, 283777154746433, 72670922213441, 72671391975489, 
    72671391975489, 2923059026695110798638776533868285602931350182722, 1161155284439232, 105624522264768, 1161157431922880, 736461225016239252020611922737686042278021318467, 
    105641702133952, 1161157431922880, 28545062744644064534248331768592456701458782018, 1161157431922880, 28545062744645362613124612948571607843645428546, 316943362040129, 
    28545062744645362613414725632641110425137583938, 7759266745884737787867324976944749980485722624375035250067026618173873121655095158826676605278186391594791347470899107736782885057838547342102842199388598299896765166383686, 105639156256960, 105639554650304, 176007898337472, 176007898337472, 
    1461551814177927718966802813083140508057218389826, 1461685619159542453087059722587838309373906588482, 1464361718791837135492197912681794335707670582082, 2923728054330613674209183686974062803386152043331, 2923728051608354738841675979267065943932006351683, 105639156256960, 
    736461225016249006906417448941417149233564238659, 105639554650304, 176007898337472, 176007898337472, 97064015254883712830238274351438535409233040194, 736462597029632807621210545061950931699069129538, 
    1461551814177948488233465114907918967636079220546, 1461685619159563222353722024412616768952767419202, 1464361718791857904758860214506572795286531412802, 2923728051608375548673157488395185251405369787203, 2923059026700301878071872940871696244821928789827, 2925868931314211294597268040470350072472380982083, 
    2923728051608375548673157488395185251405369787203, 2923059026695132865974237472842459703569821996866, 2923371239680027774975382019335992857489536242242, 3957317799008873970763761087600879064355349768222307227823009895186894345464850552884558577587570585657343013183326204198912114978524210747931749569711917015096112631334828102, 4122072778085587604135317497207966599391823681702799072397628402997300760947198444949474626087446531662455736956979728320499903168662998492694330838424831101769458083461855302, 354123285533120, 
    362919378555328, 369516448321984, 362919378555328, 1161157431922880, 105641702133952, 387374383376705, 
    176008300990656, 176008300990656, 73221215373889, 636171168795201, 565802424617537, 567434990326464, 
    74869945468993, 571833036837824, 90813401418305, 90813401418305, 1128584672983489, 1128176516859969, 
    1128176516859969, 636171168795201, 73221215373889, 73221215373889, 365555209771702847741843769402179107210917843778, 565802424617537, 
    2923103628356146553102912887598425071514746636867, 1130719271727553, 1130723566694849, 1130723566694849, 1130719271727553, 1130719271727553, 
    1130723566694849, 123710547255613018228348411142505057998181807326591802087084713443152720578991573927422672915048542396672609685286737146873183725142089826460086718505174140527390546896834118, 1125908774125633, 580614097474240, 2923728051608334579317428267299204586957942310723, 1134971155128641, 
    1134979745063233, 580629129859776, 580629129859776]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_0 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_1 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_2 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_3 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2490410412490492c30590db209a60001009a41248000201b48041249248249040009a49209a41001249248249040049a0920924104020820924824904920c20824920925860b21b641248000201b4834d00004046d04c20d34980dc4300065964c0790582090c164134824100000000804d209241861009241a493cc60124c26980004026904920c308049301049a692092410413cc60124c000289a4826900004d349049300049249209241001269a4824900004924904920b24134930c20126c2492182c02d9049241808059a0d340001009a4020930d801200408251280281000049a6805820000d34d001a412410598182090032680032c13c8348279a0826924924900004db49249308208249249a400013092492482492492490c8209a4924924000106134d34c20820924926900004004934d209a69249240003449a69c0800020c269279000040271840000008019349a4338f2492882490, 1161157431922880, 1161157431922880, 176007898337472, 176007898337472, 531505989080171503924627602730668462947096288158612346587480898640016841059646993111555723558917796997, 1161187433711681, 
    1161187635038273, 72670922213441, 74870213904449, 74870213904449, 88064621873217, 537795352846196041671507569279952325299455087475904461258978390803441652633241965525854702358807213189, 
    581395120223413659886870272707617451862079527438797565435372240897817044558833799765779204380370171013, 33283751484824631724446758483998282963383523775345330851677092576751280428005072725496196894568248453, 565252131457089, 72670922213441, 72670922213441, 72670922213441, 
    1461685640257277664118065548106308916232797098818, 105656740808769, 105624528554049, 105630971004993, 72671391975489, 79268461742145, 
    143039666391105, 149636736157761, 4217239420481885636210124823264605328798184035944545049769453061068939475632327179968554065035804804, 188397414113969463843049580055301381630942263106, 188397414113883141907776438539059533101827897154, 188397414113880545769250691441834153062069974850, 
    188397414113883790944883755392513099413869049666, 33283751484824631724446758483631415207216873055400705851425990098864539836687399302926211978635015301, 72670922213441, 72670922213441, 72670922213441, 72670922213441, 
    79267991980097, 79267991980097, 72671391975489, 72671391975489, 72671391975489, 72671391975489, 
    79268461742145, 79268461742145]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_4 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249208208000049249308209209a6920820020124924d24024820920820800004824820820100120920820800004824920804800824824820000020020820126020826106026100004904904920006a20820d60000000020124804924004100000924924104124124926924834834d24904904904924924104124124924904104900804924924b208001041249268200040049249209209248208201001248208000240269249249008049249241008009a49248240201209a4924900904d349241201008249248240200001361241a48209249209008041049241201008209801849841041240209248201049008248201248208000208249249041049049249208209a0d249249241241249249049049069a4920920920134924d241240001001259a48248001041a6924824800024130d04f00824920924820104924d341340208240241248249a4b24904000124100130020924c24924800024984104d00824930904920924d34924120820820900d80000824000930820924824020000124904020824924925900000920800820104924124924000124820826804124904924904924924920820820824134000126824824c208249249009841049249209a09249249240001209048268041249049249008249249209a01049241249241249249248208041001040000041048209a08201001800200001801a6824835124924d02000f06c363360001b1180c00c00037b3cd80c000001b6d811b0e38f36de608, 1161157431922880, 1161157431922880, 2923192831676891686892331857971211080878925028162, 2923371238319044665719341070644141482634509294402, 2923192831336609319971393394507836473447156816706, 2923059026695276952772074948466513279562236828482, 
    2923728051603351272410466812825045137181028392770, 1161157431922880, 1161157431922880, 2923036725865007830418698796882396979342788795202, 176007898337472, 176007898337472, 
    961578463299327237377672734290142200631025010630026512836437250688914458290332136583342627066982594119442469555783589517075827937515374918731579763881345256508255971953092029827261829069905511785493427969625652573684611597027590296956357508613335079760953368246197512]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_5 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14924004900c20524800020134820820920904906000db0c30c30824820924020180030c30db0020820920904904d20c308249008208208241240a6986104124802500104104824804920820824900524800020024812104924124924124934934924900804104900820480024904904d00184104920920504134d248248104928208208241240209209048048209249249009009249249201208208248241240a08208209049041041041209208240001009a41a48000201a4812092504124924824804124904905104924924920920924924924924104124904024814104d34920920020924924134112420824924924900004184924d208208249249240001001249248165248a25000008208209001049249201240000200200248041049048249025144a85108209a69a4d24020926934030824920924936904920920806d204928a4d12104124924b24804124924804104924124926920924124100924092514912420824924924900004d44924920820824924924000130d24924824924924902820924924924000106124934c20820924924900004004924d209a6924924104104924924800020824924904104124920100000800924924124924924820826924924900004184d34d308208249249a4000100124d348269a492490248, 2923059026695317195761007399259447548966695685955]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_6 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_7 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a4d34900820524830c201240208209209049040008208249008248249240200a0820920904904d208208249008208208241240a6984104124802500104904824804920820824900924820920924124800020134824900004834902820924900924100034934804902420904124020824104100004000834d24924920420934924924810524800040134814920000804d208208208241240001001048048209208249009041041041209208208248241240a0820820904904104124120920824000100a24136d00130030810920000804d201248208200240249208240041049200008049209240001009240209249041a4820824924035100004924900920000924920124020924924924810024d341049201049248209042248001a4124812420824924924900004db4924920820824924924000130d249248144a48a25028209a6a25124000136d34030820820924946904100d30c069005968a51960a0824924924900004924924920820824924924000120924924824924924902820924924924000106125934820820924924900004004934d309a6924924104124924926800020824924904104124d20100000800924924124924926820826924924900004db49349208208249249a40001309249248249249249025041349249248000289a4924904104124920d20000a0692492412492492480, 176007898337472]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_8 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924920804904924920804920924924924020124924924024824100824d30924120824924934900824124904920924824924d24100000924924822c849348240009205249249248248125100009a4804920420024924124804d249041249044909249248201040a49249249049025a4924820d268228209249249440a4920924934900104924d201008a2134d249040288149249249209205a49249a4824812400926906026810024926920920124924d341240209249241248124228a24001a09048268041249049249008249a69209201049241249241249a4924800024904024d0082492092492000092410493402092492412482492492490248]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_9 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_10 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492cb2080db049249208249209a492092022c1a49209a6024824820920100924104004104035904104900804920000000100d24000020124124823884944820004920524d24820924812510004920804820420924820124804d24904124904490924b2482036c1249248201248249249249069049249249009204a49249208349a0100104100d000800000040349041049259201008a2124d208001268149249308249a0524924924824812512124924d241240209248201248124124800249248259000049248049200008249249240001249248248249249238820009249209000209248249248000209249249008249349649204a48a48a200012080092480412490492490082492082492010492412492412492492482248, 1130371530101696, 1161164082123200, 590608166306099525328571617575567872744187068034581869736699980166939635990935231343567059602965229700, 145216076255680, 11441676168657864343435068292608088897990177346, 590616252744673935204111399712143894211080115680331694050611155081055799873539044089862740801544745092, 
    388257367873469144944101173266606174640034304834, 388925086097253839141686021431602643233543312194, 393921778761834660491047924470429590160674936642, 4081464883438992850785358374033573555988170995106787438201214591105341372011600408649789637042557790303738975914966168291072562571170803013332598180663889654011374654752861766, 129777547423926009027780781102568141247763251276905386647639470286044418502448246036744426645147012, 354123285533120, 
    362919378555328, 354123285533120, 360720355299776, 360720355299776]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_11 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_12 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249269269a0806d849248248200201209269a0806d049a49208069308248208201341040208200208269c6d060269859029249249a68201341249248201248249249248069049249249009208248248201b4120920820804d049249241009a09248301809a41240a4924920805904924920820920924924924020124924924824824b249a4804904104924d34124120824924900000824924920920824924824124024924824824804004100004c02f36e38c301e60849a6824100920526924924c24812514004920930820520924c24c248249249049049049208008009204909249248201341249249249049024a28209249241040a49249249049009249209209201001001001240a2112535926906027814404104124c00010924924120aa092492413412402090482402481240000410600480082082cb069000001041001201b6f20800028834d24100004d84124920804a20c34924100134184da6820024824820826800024c36d20804024904902500020820820804d249041049001869b61b0000124924d24124037920900027820000db6db0db0801820900027804124904904904d64db69b09209249241241240000269a6824820020db49209208249049041a59069a0004904920924820100934120024924920920800824824924830c20824920004c309a69249060000249a6820834d0002482490490248, 72671391975489, 1130371521974976, 259775872474346304570794861899807299688635041448163778901837578323946549999492910257291563320873284, 132875738930441511880114383112647046282648624617247888141963968498560211978899773226283105209008394564, 74855930663616, 567434990326464, 
    736462602474296063222862073249387112259945272130, 45850507033398638143327887258441336434852889411, 91522607424561220392997203428533394313526117187, 79253977174976, 571833036837824, 580629129859776, 
    580629129859776, 580629129859776, 580629129859776, 732180859396240491379674120818832770101200065346]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_13 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144a49249208049068249a69200201a4924920804904d24301804d209248208201241000000200348249a780c024b02504492924924100924124934934804900820820800900420000020024824104100004106944180c051605104929249a68201241249268201348269249248049069249249009209249248201240a49269a0804900924d341009209248301009ac112092524924904024824924904024904924924900920924924920124124924904024814924d34100920124924820104134904020124812424924920804804924924924020096524104da4920c20800124924824824826c269040025249249248348049249241049240a49249249049025108249249209004001249248248000249349349051208008001005249249248348109a49a6820124124926830c34824924924906904924924920d204928a0004924920d208209349a0180112124924904024824924904104904924924920920924924924124092514000924924124104134924020812420920920804800824c24d30900824924924020120824db4e30900924924db4d20800820934d34824024926d26984004904904d248040028248248201200001001248348209249249008049861b6db6c30c20006db6db0db0904136d34830c20004924920d208248469a4180124924d2492012010410490402402412492492010092490082492490410400092492412400490c164800024924924924124024920305904d20aa4800124136820000b21924120db6000180db6000120924900800120924924806db0000c06db00049a09249200249041a480002490000402490c9240001009a410248, 532345381924043839394585471685569663539336728579425720792526200257865007856619901120107746520337760388, 581395120223413659886868512815490779319294179563963339699702884897982466989714258056885431652973822084, 597874794202302461400066704273791789939787055835885018850693724696275807734689517976428164784847077508, 90813401418305, 23192863480302672141767185263145513620831995715, 996326080379589994933119520496743091777794366958514459569193963077839165442708115462282127422270493287427112931742998829383005960305421012779728711342591558516320983363142, 
    996326080379589994933119520496743091777794366958514459608595969276527143270977227074038535219853036444871288158186550446233045153137793723631354559433409291735064762428998, 565733168267841, 565733168267841, 565733168267841, 565733638029889, 565733369594433, 
    581126800818753, 581126532383297]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_14 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, false⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4920820100924124804104024004924100804920824000100924124c00024024822c828a45249248201248249349249009209201041009000a09000040249009248200008208a20969248200049205a4924820d24812510000924900920420924924c248249249049049069a49008049204905125a79248209248145a61048201248129249241241240209049a60248124040041040249008241049049200000001009240200001241a4804120824824904920820824920004820820924904186020826920804024d24824902301b38dbcf360821001041009200800000040249044209249248248249009209249208208209248000a08269a49241000009269208201048209209240a20201a0800120804d249041249001009b08340001249241241240279248209248208049369a0920800026924c00004124934d049008648341308209249241241240201208001208249049209009208249b798c036d84924830180db6124904020124824904920804920924124924024804124904024d0410482010093402092080002082490248, 565733638029889, 565733369594433, 1130371521974976, 567434990326464, 74869945468993, 981230230681843689449189081081973547746330706239295001358958049426379793908978714229549540697144055562023874588600954154526523101397623052402684756620644437574927076601414, 
    15015934901227361551021311223829871171380923692652681855766858788408077767505568957711904761501106680343530028779589528748172162796241117095118778821419372289545447684822781992163222476233750726880647400889059203776511383001961846419541883001208520984018968496956552, 285976178001985, 74869945468993, 571833036837824]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2_15 : TreeValid ⟨some ⟨1, 1, false⟩, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 104 ⟨3, 129, ⟨0, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144a49249208049048249249200200a4924920804904924f31804920924820820124120030c6012482492598c024902504924924924100924124924924804904824920800800920904020020824124100024004920514924820820124124960c0010002692c9a48049049259341009009249248201240a49269a0804900924124100900926830100a261b71860301348149243018059201249249249040268249249040249049249249009209249249201241249249040268249249241009a01249248201301249040201248248249249208049049249249240200944a4904f35920800820134d6482402482782c9840025249209040248028248208201241049000000048209249249009041241041009205861b6e38e38c16186db8db6db08a0004d34d209008209469a0180106136d34d348141049a0c00c200a0920920804900824824d30900824924924020120824a24e309009249249a4d20800820924934824024924d26984004904900904024802924820920924124900034824902820924924924100034934924900824d24924900430934d24924004164934904004920820824920534830c209248108248248201240001001248448209249249008049061a89e6c37820006a279b4d60904137934c31820004924930d608248469a6180124124004100920104020820924824120804804104920000800920924000100924020924924924020024924904100004924920920000924924924020924924924010824d349249001049249249301348308209248124249a680002016c826db0c40c36e31a50c56e30f6cc0012092492480c0049a0924920000b30324920024904104124904920820824920924184104924128934c2493480252492493490402482412410490010090490490402482492080402490410410410092080000010092412694d86013482480, 636171168795201, 11462627949732559191911268076304973784449816386, 636170833250881, 28545062744811623229150929020351233038473516867, 28545062744819385083467344820072816018719246147, 537795352846196041671505809612560320537211636560031302972369990547075915448550356800272564453487427716, 
    171826676859754011028522233684303235495009780610186054717712868711311536907632695552425154546470811907524317222361941918490318792658254370789978566468017098219099413587811320622309680699519179045142293008017348398010468760975087797439942920696278060052325270359852158401288759517272118789890088233810652575503030020395330537552031107903142130462594029351118707506930686489086386332139580342066334076086742209623546727238558245843801674667779981668162793339006707298032125967871889893364484490617790351559070073727998454048633881531855730842681865168502344296716485416622206597955271919163066520159224237812038711163267541373031923122412445788722464534095, 22881261642536442218942783389336077859289044802, 22881262833524726442227405511147203870477784898, 7759266976116651237019934406609902287483102732879349909718690764862993955939360957707372528382541146012093195217561559882205242494312694143437849084577399824504218350562886, 73221215373889, 90813401418305, 
    97053213331554088238777339717889696355141555010, 97053213331555386317943733581938350078820356930, 176347473785281, 97053213331557982476276521310053671924687442754, 176068032467393, 97053213331563174792942096766248286819402650434, 
    176063737500097, 35193239371841, 316936651546945, 316936651546945, 316934504063297, 316943093997889, 
    316943093997889, 563534614774337, 563534614774337, 563534346338881, 290349455052992, 588343926851645907328321837564062108668569230177526888225920805260696923712410215088328632451088038980, 
    290349455052992, 565733638029889, 565733369594433, 91433404103817034175486912042844732677184033602, 581126800818753, 581126532383297]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨0, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_2_0
  · exact tv_b11_2_1
  · exact tv_b11_2_2
  · exact tv_b11_2_3
  · exact tv_b11_2_4
  · exact tv_b11_2_5
  · exact tv_b11_2_6
  · exact tv_b11_2_7
  · exact tv_b11_2_8
  · exact tv_b11_2_9
  · exact tv_b11_2_10
  · exact tv_b11_2_11
  · exact tv_b11_2_12
  · exact tv_b11_2_13
  · exact tv_b11_2_14
  · exact tv_b11_2_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24904104124904924004d04d20924000101124124800124136826000c20834931120826924920904924e34e209269a09049300209249a0924c00024136824104104824024124904904920104d66c36d34934100000d04904906a24104d04d20dc7046db69341209241041049a4124900004036904820920904800836db0db6db6d84924a249241a08209a49248241200042269261a1b3c001b30de61b8c000601a4824134c000301b8c24920000806d20804000824920804124920900900820820924020924104104824000004824800020000020920020800034134904136d801861a4d04800000104024800004305924d200001001011240001001249368251249249000008269249201049249209240000201a4124804104934824904924924920000004104820020928934238800004004000900820924904da0934924da40000309a49268041249248249008200289049201041241009241a69249248124003249a49a88000208249269000041a6d869a00008019249a4326b2492682488, 1161159514394816, 1161159514394816, 246376577503424, 531505989080171503924625842850281660983936116414791458100709158212594194589074306498577837570538370181, 176007831228608, 97064015254883712830221349325400326342803723074, 
    653213599025729, 72671459560001, 635621412981313, 3968729083630699560964075902362029628063327047848247627791577557224294583635574877376841177134867969651032479359297897633301181222880409727514619155876520762645383515905932870, 635621412981313, 565252668803649, 
    565252668803649, 582844854848065]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4104d04930926800020124c20824924920904924824924824120824924920904820924924824124d30820824920904920020824d209248309a09a4124800020134c24900024826d04c00c00800804136d861861b01859b7836db6db6130030030db0c04934104d34d30db7046db6db61209a6800030247024920000806d20820924924824000104d04d040249209a49249041341349241308209249248241208249249209041049249241209c70000301b6c24124920c268369049240001009a4104104924904020000004000904924134924130db6db6db6c36104104924904024104124924920936d801861b6d84820824924924900004104d34d60820824924924000100124924c24924924900000820824920000820904904000020020134c00020024904904924d24d20820924924924000104134134c20820924924904100100804d30a269249a4104124924934c00020024904104104124924d300008009241241349249348208249249249000049349349208208249249a4000120924924824924924902820924924924000104125134c20820924926900004004934d2092492492410412492493480002682c9a89841041249241200009009a4a2612492493481650, 176076617814208, 105776662384832, 283777154746433, 582844317977153]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24904104124904926104d84d209a6000100da41a68000201b4826db0c30c36db0e30188200006184120924924806e30c40c30e3ac2490410412490492410c308924126931038d248049461b4db49a0924d861361368208061b6db49a0104104800024020186136136804904104000104d36c36db6934030186db6db6c000000000041069b6184d84d20db6c46db693412092400410092c1248001361b6824900004036906920004906da0804020936030800036db6c30d800049a49060201048249249201450000201b4830c00006030d80824046e00800b2c000101b2c124900004036904124c008249b4824934000c06d208000000000208041241200009000208240001a01241041000240300008201b6c20c00030c34d80800000000904238c00c3cdb8c36d801861a5108db0030d349b08208249249249000049b4db4960820824924da4000120924924c24924924900004934db49a010492493092400012412612680410492483490492493492082092cb2ca2400016db6d925820820924934904100961865130b2c929b2c0001b6db6d2c804124d24c349008241a49869a0104124100d241a69a4da4814800326a249b0c00020c24d36900004801006c30000801134db41b6db6d2a82488, 33283751113574826881502646815875691083990377550963979501440233531026413562184023832286249308430824581, 1128184905009217, 1161155217330368, 1161155217330368, 1161155217330368, 1161161670529472, 
    1161161670529472, 2923103628355834668665709044154670410802313302850, 2923192831676911158079213650491135611680642306882, 2923371238319064136906222863164066013437300314946, 2923036725865214224371716010433579428474607637314, 2923103628355855437932371345979448870381174133570, 
    2923192853455003410285937613971888946892668670786, 2923192831676931927345875952315914071259503137602, 2923192852944579859904529918776827035745016353602, 2923371238319084906172885164988844473016161145666, 2923192831676931927345875952315914071259503137602, 2923728051603390863826903590334705276529477161794, 
    1154573452716865, 1136981266672449, 1136981266672449, 105639084888256, 3965649587878131208883460940364844451279921343390911641318833099812236577141935032742565257869078389366426940024193355847698505559876552358492310888700101023024286569687151174, 90263645604417, 
    90263645604417, 72671459560001, 90263645604417, 90263645604417, 582844787739201, 90263645604417, 
    91700752730188707135246255681167111616439785282]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨0, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24a24934934930926820820924c20824924920904924824924824120824924920904820924924824124d30820824920904920820824920924820920924134c00020124834d000040249048209249a6984100036db6db6d849361b6db6db0004934830930d24124d04134134824920c24c249009269041341348249a0000c04d20820924924824000104104104024920924924904104924924130820924924824120824924920904104924924120936c00020124824124820820934c24920c24c24d04d20000804d30924000100924020924924904020824d26da6100004d34924d30000db6db6db6020924924924820824924924100186db6db6c30134d00034834904924000100d24020824924924900004924924960820824924924000120924924c249249249048209249249240001249249258208209249249041009208249309249249240a08249249249000049349349208208249249a4000120924924824924924902820924924924000104124d24820820924926900004c04934d2092492492411450, 2923036725866190380617914583852746440586544812610, 105639084888256]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x269a0b3cde18069a0034da0000924824db7124126986f3490006000c8269a6d30c36c3cf37450134d300349c71b6d80008804026d211270491d8124100020304938806dac1a69a00009241048240041a6926986c00844d24134920104124104824004040230e38f36c34924d20900104186d05164dc612082c82c924e20c30d86db6de6000180224b3c8209a4826f368601a6820d09000824924934db0b049249b69a0120806126986c30c36db6db8db0d84d88226e38db8c379b69b79b6920000100000800000030d89030c44920934d86800186db6db0c301b6b04b249000249249209001069a6928920020d34924d248241049249349201069a492c9a4121934924d248243249000361b6db6d8486000c0269a82a00009449a48040001009c6006000024964d2090c9ac924e20d6492000c02c9248001040008240240001b0224800804120034920104e34924f20c311b91c7046000200db8d80c30c46e49636d800081b8e362311371c6dc600030ab24908804124920900900826928920da0104924124824124b2493480, 1161224003915968, 2923192831676892985013066089480552921016694232899, 2923728051603359709889844585577618803100916123459, 1161224003915968, 97053213331555386518584462618587385993420625731, 371085815678538653198010106239388398838524413763, 
    1161157705480641, 1161230446366912, 1161230446366912, 176068028272832, 531505989080171503924625843064953579354509860124984292537889600874033555250990297408811093149414356101, 1161161866217537, 
    97053213331563175070315765646824481064986609475, 2860081461121140688163856849192748199921059651, 285950610507841, 567430016416193, 571823633729601, 88047375878209, 
    17678631700545, 2924430527799382744556857392048762468904806647619, 88047375878209, 88047375878209, 176076617814208, 176076617814208, 
    105776595275968, 176076617814208, 176076617814208, 176076617814208, 5720162922200742842393525768293283987898506050, 1462220839086188312811835063792808377352266008387, 
    3957286427485527111805477507569384677388197752060051652729996753382972449793947249485911536061608457065777600394253231908016601208923628725595528680101940678125982499569917510, 79251551291457, 360726528011073, 3957287367290623191565779140878084427802216213286506017857991018671715379244991432551158729767460208880575852777361794982081087755051369382071975824909439006870213263007666758, 531505989080171503924625842850281660983936116408053649098292779063888990054896413044635462020133057669, 167212481518529, 
    88047375878209, 88047375878209, 88047375878209, 650997329316417]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24e34134920000936d04924904024004924924d30924920004934924d309041249249348049241a4924100da6186826000134d06d24904836db61a69a60041b6006820000136db0da6a00004186d04d24a28108db634cdb6d80824824924d20c30db6db6db60001001249448309b8c20d04000c24db49b49441208041249249348249249241249049249040369a69a0980184d34d349241209a6da6d268261069809a69b00041341349441209a6c26db6820124d000361b6db6d848241048249241200009a69a8806104100924934800026da4a209049a4924d209249200041a4924900000000820020000140124904800000026826004d34934d30904124924904800020b20800984104d24924d20820326120826134d24d3480, 6707465090285017895107818191389901621926133054257685855525791364560159653211020209671377933933401792413443986069145816305038416077576282507155909462808839490572717863979023762415453167264216245555305923204298859739710265085280781912118799601257685850970672822534170091608093093750865353585958229398080821034493593903888598455914318629155012027174055545485412446161055567401031242, 6707465290317740354642250853982272085327249495267424299173368799134817048895976581470149896209164965057803021502078480202732665892445888212580138136788982163563929091913840703591367251940959161974864542716197957642554855816014087623705551138209925446974672441333128186422907658604935582228718818268157068612549770605439134750731364133557962839271145116516383523890319093608919627, 176076617814208, 176076617945280]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2490630c365906db6186d86db0a2600020162a1b6c000301b6c0c120820b65806db0c6186cf300009208200201861209a69b500418482082c96016524a20c30b648134c30c30f28806db0c6186cf30924830920db41b6c000301b6c44d0000403690cc30db6db6d861a4b24934830920da4336f06dacd34c24d20c24c3690092400030c96c1b4f209ac1b6c28980004038a04d30020806f301048208209300043209ac0300000209a4800800c041249063001848249201303061208209a4c00004134d3c800dbc000280ebc1241b6b209acb3cc24920c24836d06db40019069a0d34000100da4060b269acb00030c36db6db6180004db7936820b24934d00034836d0cd34000100da4064c30db6dbadc60002b76db5b7830c30db6db6e86180de186aec0dbcebcebc12596490, 1161187433711681, 531566814649450785657876692755873057561058574624967249286978283030288697046251541507296091565176668292, 1161224003915968, 1161226151399616, 1161230446629056, 2923103628356831593465514038909212078358858306370, 
    2923192831677908082879018645245677279237187310402, 2923371238320061061706027857918607680993845318466, 2923036725866211149171521005188121131215524729666, 531566814649450785657876689321122363631879437915036905068175173641273992667535504922488239424142590084, 2928712635661257196045706962217318768679130764098, 3966977959076672256971232807554050299232938779681435635647164338630971258871635011348315382085501894558710320255499749018595807037014125997581032226141252665417883801819804230, 
    176063733305536, 176063733305536, 176063733305536, 176063733305536, 176076618207424, 565252131457089, 
    565252131457089, 565252131457089, 265751470930879079173625990593753080964209891387315479669662697425455516227880961839306975587241325701, 3967944174538650542346113567387258296924358342001061481783214127391733418968238398982191086297871048931861386321761811693643899273032029142183108428403185238997260049355633222, 90263645604417, 90263645604417, 
    996326080379589994933119520496743091777881706056527201096785548209996931451653678659942041214862220623012574496266089929174426284623384909317728350166327176472774684487238, 4217239420481885636211902306774912349440754979958782807633082870870782705912121386921211952693002372, 33283751484824631724446779524440940144001730970033865548963398665974538611054788509071419324135391364, 33283751113574826881504427844407618465709599022215469622294174018133283754661199024533471075829563524, 33283751113574826881504427844407618465709599022215469622294174018133283754661199024533471075829563524, 635621412981313, 
    265816731696893447730563648338298532271686799263586337390751455781923227517926766423228073299417514116, 265816731696893447730563648338298532271686799263586337390751455781923227517926766423228073299417514116, 582844854848065, 565252668803649, 4152865693042607965995069177739958329511498795945467500771156724001255848246313359467453428263043204, 582844854848065, 
    74869945468993, 79267991980097, 88064085002305, 97064363705232057337638366688658994084918072130, 97064015256088330296651780193060983954269541186, 565252668803649, 
    565252668803649, 91433404104813958975277399632215014603260695362, 582844854848065, 91701014068043427215791218641610617236637094722, 635621412981313, 90263645604417, 
    91701014068043427215791218641606395095880307522, 537795352846196041671507587096070627557854207506909961914684289146773051988838437478776189649749819524, 3957316615500260807304151141992831500103344884535467570324121745176846991985807377761381584982430091069911911740621161325496332202124968368959241088361240984769931848509992518, 3968910228068469036001766895125066278449836009470395657905861091054779038888584778512759564433537251097246796591671800698987465655300287671609496589429745852117319898407843910, 365555209772865926674932671589773089917728985922, 365555209772865926674932671589773089917728985922, 
    365466006451789437261428065253307889039936852802, 365555209772865926674932671589773089917728985922, 365733616415018905501941884262703491673313252162, 3957316615500260807304151141992831309566934254062380027132100791853866600646739817085991542725913483608991353828358975182979786819233982349731201074043741373986436410447670854, 3957316615500260807304151141992831119030523789603651955899915922174428091309662868716944737715959297422901156776084976709205218004649536265124879407003636153708626123332693574, 3968910228068469036001766895125066087913425467722822939161670917974809795631704750493442095672864684258517740562427231737121483387014726574138885967953657245484154004634024006, 
    3957316615500260807304151141992831119030523789624636516557989324557936835536131930148596267429194392198006315874505334610227324055346470636695869297406191287904233271042682438, 565252668803649, 565252668803649, 91433404104813958975277399632210792462503908162, 582844854848065, 91701014068043427215791218641606395095880307522]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨1, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24eb4134920000936d04924904024004924924d30924920004934924d30904124924934c049241a4924100db618786600c144d06d24904836db61b79b0d840009269249a6124920824824924d308309069269a40001001249248000641a4b26d009bac00d34000024db4224924100804124924934824924924124904924904036d861e1980305134d34924920db6db6db6c36100024124d26984934124924100924920c249a4926904000d049369a40241048249241200009a69248001041009249348000271249208049a4924d309249200041a4924900000db6926800000130124924800006da4820d04924924d2090412492490480002c9a492030410593492492000022490082412492493480, 3957339337591055769107053545864656162519075236374334189532962770466037522181448595860383036318744008745233176638508473638933855205707413699985287259721443790615842271321388615, 6810605479372839467676686575988707432105478129026264635705998860926826766647170267710467233212195942761625152014563179259649078980197922037926105601289138613136305074758764325729907916811338622012017293513681554172277364652626754866057113716455051213218795573755089685960613395255603576621729076096464331874575109992474456334867839743764281970769075906743596251537108203564354507, 188398111014491906338793875293194513772953236034, 538580850148118187424936391308467065105863925515978889602693531461748210273162002716171114762797784133, 145212987939265, 145212987939265, 
    105707875733696, 105639084888256, 3864567008898268209855935384570472752230604793519486511525948587724649738202839230495694625276401011709825348762739452216026175682535902168149532499274899572872808937180743, 538580850148118187424936391288341572671153788583326325323555170598312467138486641495994591097920887877, 145208692971969, 145208692971969]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x36d80d34d000069a0024130020d36836c36104124806820d00830c34db6de71800069a69acdb0c30d36db69c6124d00064d3596698000c1a4d0cda010084d5d09241248009a6d368069c00208240009a6c20820d00824924c001b6186d861371861b0d801800009a0824c20000d86d86d86020826820130820d36034938000134da4db0d80104c30d34d379c6026820906c00830c34db6da7184800336dbcf36c38dc6db81b0c300011349379a4000336db6f36c04020db6c269041b7008db6c00026db6db61b0030830924820d048249b0d80c30d80020e36c30c36030db6db6186c36100c061861b6d84830c36c30c0018000ceb6db6030c30c36c360300001b6db6d8cc34db6de7184c30db6db60060001b6db6d80c30c36db0db6d80006db6db61b0d36db69c6130c36c30c0018000ceb6db6030c30c36c360300001c6db6d8cc34db6de7184c30db0c36006000336db6d80030c36db0db0d80006db6db6300d34d379c6120000036c30030000d86d86c00000006006030c00006de61b0c0cdbaeb6e300018371e7980000306dbcd80000040f4d006d8000003cdb63019b6de79b610, 1161368023863744, 1161368023863744, 1161368023863744, 2928712984111730155855994636736367829576029582146, 97053213331553114679482479827091651439802992451, 266594411932911499093404785391064154659195186632900150291824168070803934832648991689609222542419588229, 
    266594411932911499093404785391064154659195186632900150291824168070803934832648991689609222542419588229, 188408564488886449535656343252475743710312674114, 188408564488886449535656343252475743710312674114, 583925458845267980548559346308943340335940677614606395823229413579985575909007924718815994839594117, 7759266745884737787867324976944559444075180876167705075617573173554365237872717539787181405995559843175587190953274518437637442829229180860800980365331336133789291728812103, 15015491880072309539971164536928681804323212865234115017722660854226675176185803216055622160117977909396543926086974433802332005374385042695800269572616597109850518497279157455142422401414415546458925300333684842670949170307612203409324926490023373966409985745997513, 
    1161361581412800, 188397414116204756494125174450991927353369704258, 1161359433929152, 2928712984111647079086451038860845340841796973378, 316934504059328, 1161368023863744, 
    2928712984111652271403116614317328186112663892802, 316943093993920, 1161368023863744, 2928712984111652271403116614317328186112663892802, 316943093993920, 1128184905009217, 
    1136981266672449, 1128184905009217, 1128184905009217, 1132583085808577, 1136981266672449, 1134782243211329, 
    1128184905009217, 1128184905009217, 1136981266672449, 1128184905009217, 1128185039297473, 1128185173650241, 
    2923728051605758559929334276762255195482823340866, 1134782243211329]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24904104124904926104c04d209a60001001a41248000200348041209248248049208208249200009249208241001209248248040048269a0920104020820924824934c20820924804920c208349209248209809a4124800020034834d00004006d048209249a49841861b6db6db1000034d34d26104c30db6db6d860001a6934900824144db6930004db6c30d80db61a69801001348209240000009241a4920000034826980004006904920000004d20104826826920004120c348300000209a49a0900004134d241000048249209201001209a6824800004124904900000006b269a01861a4934d36820100824d34da0134920000134824920026026904924000c00120d340001001a4030926db4900020824d269261000049a6d26c20000d34d249a41241059379a48001841a4934d30836d80036c06d86824000920000000000104000c6000002480000c200004000c301a0db6b269260001a69a0980004134926826d00006984c04c20104124d309b41a4934d36830c36db6db6d80006db6c36db0c30c36db61b60001b0db6db6c249249249000069a6824da01049249a09b4000126130136804104934c26d04924924da00000041009200001801009008000040040069800040049219a0936da49a4000020824938004124926826100000800906da0104124d209b412692493882490, 6708709454003498711712893720301969512853088724843040759837900541143406465717631566625276611971480008669755918976504901886503221981473367809460304578580537153405617093922561470621064453023191955829882789045213506075206439147216775229402147860092712197048791576947047128457692588964901267944517406240052655755645119646244115000777916424663471394568550867199445057472722578982522955, 1161363729027520, 28545672530831212176498521947500707856509306691, 15121341268955092079109659562871695680436436085337612081943056528982723273771759213441244267027355813619225171031473199732179149074655419668362662296872053919022161064489321362654127300950217961788922664022842653598408169758804808232655297114450222383112245956552, 176347343753664, 176347343753664, 
    105624529012801]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 0, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24926c24800004d20c34826c360001248209a6d048269209249208049a48269a4820138b06e26906024d04104126904d30004b04d20924000100da6124800124134804924924104824004000820906c00824904104920104d44104d659c4006806186800025100125100006a20826924e20d35904d059c61a4800024336820924924820904800830d24930d800049249a49240209a4824924820134820820d348269209a6920806da42269a00009e41041049a4238f209a0b34c249000040369041a4b24b06b249000249249209001061ac9a89200209259351348241a6b089a68000261ac1861a0000935834d34830134904104136d848249209249208008348269b4d20824924924c20120c24806004d20c3c8208260000269248209008209240208240209248269268201a6924924904804124124926904104c34824d20000924924020000124924834800820806104da0124104824004104924904920104820820020100824186d34d64db40269251a6d04804d24934920900826806104da01b7105104db60001a49a40368208248269a68201a6820904000824924924920904924924924020934d249a09a0104800924920d348249249249209089a49269241200009008209a40003209a0b34c000249249069041a49869a4d00034924120900104924926934020d34924d248241a6db6db61b6030924d361b6db4001134924d248241248009a4900800034904106d848125a6b069a68000251a4da61b0020b041640608261061e61b6db0030d349b6d24804324920134920104d349249248241008261a4127900000980000c300009259241a4034d861861e7184d361861869c6100100124d000049249241200200041048340041248209a69048061841861e71841861041079c610080082090002cdb0c30c36e319b7986de79b6106db6c36c36da0db6c30db0db61b6f001c0226836d80036c36d815b9036c3db2080030098002682104d44b049260b269a09241041069a41b6d801b01b6c269800040369041049249269241000209249809041869249269a41061a482082090492408, 513258889781001788509570720035985265731968141806702144541163691612551015439548369316646175685868760021903981322251315966690459439192410357592829888520025403765686634757702, 106174278078656, 106174278078656, 513258889781001788509570720035985265732063972932810994878576520927802486476726203516297122533471274484567087622455338387289388271372266473973393985548682296011154511576646, 5777511356834555515219647630061847477074702918647034492580000267644424107759305187858171693335561120613301092601108927869281436339017249992738947069412923402862317832662456387116890667247950542555145567328107730873023725020458136249479471563609309248448338870870752591488233847408274250949729578306739540056693151178710352788246251495207536508511086212525130427256661802318671081112579799163939941987588600514141358464089859300136673698110059841684445791511762675968234259309289097409660700527376700461420981570655880742527981200325737724943936123351443382326291864014593536957925160478334247753731829500928012105648068604904111704183352163567745113173521313359, 106174278078656, 
    106191457947840, 513263957357499961965874025930937844684687755509034700457331070021919002657736208453064040864493699554359739999048942959870871764339755777419621940202920010577860548836934, 72670922213441, 519108211630325995749163152320071978886436882708079592448056326571139683790314565820614696488170629, 519108211630325995749163152320071978886436883117206517336114223651536246370383581194875170719298693, 72671459560001, 
    90263645604417, 74870213904449, 74870213904449, 88064621873217, 7759266745547319253286405420057457481651520827188237384294715472799794950081142025682043225350483246862036169907544440179775650023214100984438992561463436460886613920046662, 176474304942272, 
    537795352846196041671505809399565523336294915725345763769790271227313801628491385458934440820022473861, 290348657018945, 597874794202302459786551183924199431720058198209105808611286459207167705997988571202655581305166132357, 123695392678943148537638517488188094684088047980923624725711966272128745695210382098822573891420289594897776698079250850350780527468062497020228611187784289939524761379188295, 581395120223413659886868512827230649898919355688238867946184121321689193554083219698858942841585431685, 853307737271105, 
    33283751484824631724444998603506660727581470337262126848647669400660456940470309468388740233768236165, 2928712635670479399483487569554815279923908842306, 535719165589160008864095959973165177952639864209766663449546980468152943098653672695558809115155788933, 290348657018945, 290348657018945, 285950610507841, 
    285950610507841, 265755020079053651050095576156439049301051500042493046242902664405975706027437650451224420899689440324, 290348657018945, 431081984637377, 290348657018945, 853307737271105, 
    565252131457089, 3969846174205101288043620558039672284235688039050254419199317763359991499785517512973042828897914678349138206584833870392917314650076882139550663218700532437250058249052336710, 565252668803649, 72670922213441, 72670922213441, 730778694809709219337979637835778616269599740482, 
    72670922213441, 587500716325144747500371213144797737697921083577527879386290135244273926195837748829885668276477392005, 3353732745949935050668354960890948598241340268178191102085203869943202996658419757200250003444304889287791564268245088501745259208536645832704057526790825151831481883636664062593091390954735943673139287846608945927726990958258214530788421369533701489738500502295267152484694341604194526548055995161897087131443197671524370028801203182408656385185891494637668889020707683082543051, 571823633729601]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 0, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924920924920804820820804d30924824924924124920924920804924824924820124904924904024d34106804d40934800020134c049240209000009a4136d861861b0184d34124924100db79871bd9b6134904924904034920db6d00004920820824d20db60009009a4124800020134c249000248269009a4924824924820104104d04c010249209a4920904d341349341309248249248201249209249208049241249241009a6c20820d34c24124924904924904020004000026904924134924130db6db6db6c36134d049249040249241249241009248269a4820136da00540269049240001009a40249209249208048249249249241208249a4904d30924904d34d24904824104d30804d50800164924124c00c30820804d201241048240041049249049201041249361009a4124104924924d201b79d61819b6134d24924904804924d30d00100c34924904d200309e69049a4000124924934c00024924926900924824924820104904d860000209a4924920904124924934130838da8d301b6826924134d34924120820da6820134c24134d04924904034924d30d00104924924924130924924d24824104124da4826904924924924924c24100026d841269040009249249a4026920924920804d24da4924d209249249249a41200249a4904130924924934d24934824924900004150800924924134c02a24824924820134d06d24904824924924920904800926924134824924d35144924120904104020134020004d34904d20134d04924904034d24d30d80104d34924924d20924d24936c24100024d248269049249a69a69248261008249860269040009369a09a4016db6c30db0db61b6d80036c36d8cc001b79d61d78371800010011c0d86c00030007806db000c03618cdb050, 105656740808769, 23014456839146578817244339563401578457912578882, 519108211630325995750944070581072928708144539509232109123721905032689721878461591042265919762219140, 387108095404353, 387108095404353, 150958497008678147900342096783323651760441105890494707020687780555064386874623674774049414387864027705039324108467670678578655538443188930621723508884741846791456191458886, 
    387108095404353, 105624528554049, 387108095404353, 316739351030081, 72671391975489, 1461685619160767839819535334074161335489435538242, 
    265751470930873414351166178763727948598599229417831093628394994857138119847117183464340711135640830084]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 1, false⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924920924920804820820824d308248249261a41249209249208049248269a68201249349b49b4d20924c20821134804924b2c824b2cd20924104824004120c20920f34824904104120104d24104d259a41249001249000049a082482cd20d35934d359b6126c00120334820924924820824820124920904c00c209249248009069249249341209248249248201249209a69a0806924134924100db6db6d86db81b6c30c30db6c241a69a68000008000249241209001001a0824000020924105904824000020000030c20000820830c209340041048001a6a269a0a36834904104136d86db69a6826d30824804104120904920000100024020924924904004124924924904000824926024104124924926904104920820824124900820804006d20124104824004104924904100100836824826d208201a01001b48241a6d34904da4024820104c00804924120900100826804006d201b6d04d04db60001a4d201b48208201041008241b6d861b61b6c248000040009800049249001200009249209241000208248008069a6104d04c200009249208241a6904134136800024820820900824186d04c209a4126800984c000249241209001049a0824130020d34924d24024020924104330c20024904104c20820924104330c20004924930e20d24904824004124800904000800064904106d8030c82682cd30816db6186d86db0924830920db4324920c24836d0c9b0c01b661b60249bcf209a583082c920db6c36db6c30136db0db6db0c041801041069a40248209048008060041041a6904920820824020830b2c9a6b34c289800269200001049241049a41b60209a69b6c040208040269041271c6db61b01d0800124104030c24134000006900034904104000d24186824004120930d048008249001209001049800061200009249048240040003208208348008661a4106900004800004100000924d341b4024db6000b209261a4984134136824006000b209a01a49841341308041a6924924904924104904da09069001a0184126906124130824904db6c30db0db6136d80046c36d80c36db6db6db08001861860000269b6c209a483002692092498613413482492000490cda090412492012480410002c8208000048249009201069a492492412492000080610493400600692092408, 72671123736641, 72670922213441, 72671123736641, 72671392434241, 176474304942272, 176489337327808, 
    143039666391105, 143039867914305, 143039867914305, 4217239420481885636211459223909292780767198892747729071515133004449734879936641331589600336568139908, 7729134014253644380808226066748522678926094992404318798487032536507106058357910048733309578667603482962723217659767361575720695673507180428006228972303132481923332844761670, 4218126459056976522932464163831125384393172883087168024143158358742621214415871752548784194078392452, 
    4218126459056976522932464163831125384393172883087168024143158358742621214415871752548784194078392452, 72671123736641, 74870146992193, 4156413851247922482656873748831850459650821676658225887614505309378707400614716384105808741278171268, 4217239420481885636213200642537217579202479411725254542942548138419533071187295987099445502543151236, 4217239420481885636213200642537217579202479411725254542942548138419533071187295987099445502543151236, 
    33283751484824631724446425946767516071457919959945176410476881697724917018754819830408809301411065988, 33283751484824631724448431841172770712073758559264579842896226576883126281273856340803408443036889220, 33283751484824631724448431841223546080548926648187531856947380427588394947115033230667173323521355908, 317211797623232, 33283751484824631724446425728741345977411954196982427817694101772852561392173905807884371237633486980, 582173687498006831640714275388229315184330056827872214793789514985906806787646607199957105875564917893, 
    989322077752893486994204211112992893429643555281817028700077039663807414195740086661600167552008766317921948159397951993194788257486827740167065362113953573633571089013979206, 72670922213441, 72670922213441, 265751027411102706756238804040073728187637940755499410225882485664261306652375304135491705871818768516, 72670922213441, 72670922213441, 
    79267991980097, 79267991980097, 265872615188032345003444305628126799011506052606411668973715655295076482178175598230572338284548538500, 265856395036478320592505898608001162507671038883402993138344869050926001959306610063693064390019858564, 265872615188032345003444305628126799011506052606411668973715655295076482178175598230572338284548538500]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, some ⟨3, 1, true⟩, none, some ⟨0, 1, true⟩, none, none⟩ true 103 ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩ [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924920924920804820820824d20924824924924124920924920804924824924820124934924904d20924c20820134804924b2c82086cd30924104820004120c20c203348349041041a0104d34104d379b6124d001b4d800049a08349ecd20db79b6db19b6126c001383348209a6924824924820134d05800000024920924920904d341249241009248249248201249209249208049241249241009b6c30c301b6c24124924904d24906024924d00000104d24924934120d24924926824124904924986024d24134924180d24826926830136d86186036d848249209249208048249249249241208249a4904d20924924904924904024904920804d20820124924134804920820824920c30db6db0d86104000020104830c36d86036180824924904920800124924134820024924904120800d24924104820804104120804920924824924820104d049a68000209a4924920904934124924100936d24c201348249249241249241009240a49209249208049241a49241009249249248241200249a4904d30924924904924904024924900004d208009249241348029248249248201249069249040249249249209048009269241348249249241249241009041240201248200049349041201379801b6d80004db6c36db6c30124904924904020004104126904924124924d20934904924904024d341249241009200248268269048301001809a4014db6c30db0db61b6d80036c36d84900036db6c36d84920020824900d44000820924020024000120004920524820820924824920000804d30820924924124820004d34905930000db6db0db602092492410482003492490412092410000482012480, 387108095404353, 580628585138753, 736462602474296063222552435942676993166358906691, 72671391975489, 72671391975489, 265751027411102706756239023864118139655102690199042144488528597729936491584679724562828793041743462532, 
    72671391975489, 735038153295407254265949365575100471625558102594, 72671391975489, 79268461742145, 79268461742145, 1978690386430320492280268009207877730187255961980803920004303992422097616498222124125433669670486604634237898323784552877975626280724515584251469877331649817132659566299836998, 
    265872615188032345003444305628126799011506052614412373232962767755820198775591905692707351020787155076, 265872615188032345003444305628126799011506052614412373232962767755820198775591905692707351020787155076]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨0, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 103) (cur' := ⟨4, 128, ⟨1, [1], 1, [1]⟩⟩) (prev' := [⟨3, 127, ⟨0, [], 0, [1, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_3_0
  · exact tv_b11_3_1
  · exact tv_b11_3_2
  · exact tv_b11_3_3
  · exact tv_b11_3_4
  · exact tv_b11_3_5
  · exact tv_b11_3_6
  · exact tv_b11_3_7
  · exact tv_b11_3_8
  · exact tv_b11_3_9
  · exact tv_b11_3_10
  · exact tv_b11_3_11
  · exact tv_b11_3_12
  · exact tv_b11_3_13
  · exact tv_b11_3_14
  · exact tv_b11_3_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149229249349241041289249249040249349349349024a59249349000049a00008249205248000201248104a4924924924904024924934904104924924924920924924924d24124924924904014924924924100924924924c30112415925134920000564934d249040144a59349249241008ac9a492492080000513412192050412090486480cd3692c9a400193492593410412492493490402492493490490492d2c8dbceb00019c6d65924000120100820020a201049241041241249a4c37804024924934904900534d34d248000125148a48248269248201001001240000141201008241001249249249041049249249249241249269a4d24920c049b4d24924d06004124924904906924924924124024934d24920000924d24924904024924d349249241009269a6924920800004124120120904120904804804924924d249241009a6d35124000134924924904836da4924930c04924d24924100924934924904024924800920924124900004024900924935924c000249259349241009bcdb8db6d86024924934d249040249a49a49248200009059240040249259249201000a49a0006decdb09a4920924920804000820824d30824824924824124920924920804924826924820124db4004d24d209248000209348049a00008249209268000201248221049341049241001249048248249349349049024800249009259059b0c208249205104a4900124904824804124934924904924924920920924924924124100124904824814004924120920800924824134124800020924812404924924924926180926d24924000124924934c04024924924930c049249249241805249449249860149b0000d249209248009209241a6c000201a48249000040249005149249249248040249249249041049249249209209249249249241249349249060149249249261809249249240001248000209a6812412d249349340000a4924d249841024a2d349349241040940001001341340841241048049021249249249041049249249249241249248001001200208041249049049061861b6d80c301249249249240224a4f24d249041028a4f24d24984102522484924d24d26180924934934986024d24934924104124d249248060349a4924924904924d24924d000008200008249208200000201a48204a4db4d34d000049a4924920820924924924934124924924924824f24d24904104924f249a4900004900004100004100824920920920904120000934124924824924804db60050049b09348009209241a5000060134c24d00004024900004924100020000124124924026124904034c00c249249041000041041000204061049248208159c40049049209e79001241248205b79001641348148041249248208041249049249009249249209201249249249240041049040008101049249208200209249241041e73001e61c6c124104925249349248308149249249249205149249349249348229248249249a4020934d248348149249249209201a49a49a6904014924924924920494492804020000824814924924920920414924924d20c204924a2924920924920900c36db6db0db0484492494524924124924920490934935934800024d25934924100924924934d249348249248249249a60001059048048241058341201200a4924924920c30924924924934824924924d24924d20924920924928980024134920130924934924834804924924924104124924924924904924924924924924124124124924130104924924124124924924904900924800020934824924924924820004924904000820924924920904124924924120924824924820124924924920804924924924100a36c00030f36c240920924a49249249041029249249249240a29145a48001a48248041249049049049241249209209249249249240249349359208029249249249240928b4924924924902520804c04104102924124100924082924924d24104092494524100d008208204908924928a48921249369a69000049249a69a4c301249249349349b4904924924924d241b6800db4986000006980904904d341b4d26180820986824104014924924924104124924924924904924924100036920020104924124124134906d249848249249249249009a49a49249241a4924924820824924924924920924924804004d24924020924824824830920da49349049249249249200924149a4d24d20000524934924904014d349a49241004a48a0004124104120504104924904804924924924100924924924104124924924934824924934924902924924d241041249249349041024a0824824924920400100124924810524926944c30814924924924d205249249249248128a48061269a6da4c141249249249040249249349041049249249249209249249249240a4924934924904924924924920924924d249241149124145124a00049a49249001049241241240001269249248041249049249029224a45105041249249048041249049049049249249249209249241249240a4914912404924925530000924926d241041249249359450249249a49a490592596596c300924925944a060249249269a0c04d24d34d36180524934934986010c30c30c3af30820900d25524180004004024900926d249240000a49249249041024b4d24924904102d369249241040969a4924920820000000904904084124104804902124924934806024924934904104924924924920924924924924134924934934814924924926d209249249241241449249349b4c14d24924d26d30b249249a4f280208300209a68124249249269a08029249249241240b49249349249024b6db6db6db6d825249249a49248224825144a41068280302a0000964d24904104020030004000064d64da490ca3659a9a05041a51868068041251349049049269269b0920924d25936924194996d92410524934934800814924d249241205b4db49b69840149228001049041048149241249241201249249248040149249249209204949249249208204939349259341040000040008248149209208009204124949249249249204a29209269269b6920482494924924924920494d25134d241005249249249348249249249249041249249249204904924948920a49269349841029249a49249240b69b49471a0c02914586036dbcdb8c041209348449069248249249240249349349000029249249249240929249249241040b4da49249041025a692492482082000080410410212412410092408249292492492412409452c1041349269a04904929249249249240929a49a6924c300a4924924924904924924924920892092492892424a24d34920000926924924904024924920004d04925920904124924964804924924924100925925b64304134d34d24934834d24d25946904db71b7246206136db6dc6d881849208248249259208408609a8b2400010012492480002002492c900926936d24c000249a4db492410093492492492482492492412492492490402496496d90c104d24924924920924924924da4136db6db6db6d84d24d34924100db6db6db6db6124920c20c269ac904000800924b240144944a0004924924900000a009a0804000166d2492480000102482090513492592050412492490480002412682c104104924924920000124900824124924964802926934924800024924d24924100924924800104924934824104124924d20124924924904024924926906104924924924d20d249249249241249349269061049249249241841248209209249348300040049249208249249a4d30c30924924924934824924924924920924924904924924924100924924924184124924924924824924924924904d24924d249b41249249249348249249349269049249205145128001249249240041269a6906900004db49249201049b69249241349249348141049249241201049249241a4124924924924824924904924904924924920124d249269000049249249a4820124924900020920924904800824824924024924924920c04924924920820924924924d241a4924924924824924924920820924924924820824904124124924904000800925924104924934936104124924924934904924924924924124920134924d24100040d34da6104100c259469a4d009249249248201249249248208249249249049049249249249209249249249248249249249249049249269249209249240a28925000251249248008249249209200009249241240209249249248249249249048209349248240209249248248249249249349049249209249209249249240249a4004934920926800020924820820924920906000c30c36db0824824924824120820924920904820826924824124db0c20824920904920c20824920924800920924124800020134834900004824904c20934d24904020124924904000044d44924904934134d449200049249001241248209a6800144134824920000804d208208249248240001249041048209269a49209041049249241208208249248241208209a49209041041249241209b6c00020124824124800020924824920034824904920000804920924000100924020924924904030824934924100004924924920000924924924020934924924820824924924100104924924c30124820826924924900004104934d20820824924924000100124924826924924900000820c38b20000820d249040000200301248000200349249069a89249208208269249240001001041048208209249269041001008241209249249a4104124934da6800020834924104104124d249200008009249241249249a6820826924924900004d349349208208249249a40001309249248269249249048209a4924924000104134d34c20820924926900004004934d209a492492412490248, 17127037646893740555325536179699309789936091971, 143078384996544, 176076617814208, 1161223934644416, 271725294617026576778587223680276627038125798480115150594820631617674603730028641866035804789204629825939403650137811540662025808495183528230433788678204606514036735656518, 1161223934644416, 
    457822182060481, 105707804364992, 105707804364992, 565304150201024, 563105126945472, 567503173456576, 
    580697312989888, 580697312989888, 105707804364992, 105707804364992, 28545062745182767387997134877826174654330443586, 105707804364992, 
    563105126945472, 565304150201024, 563105126945472, 567503173456576, 580697312989888, 580697312989888, 
    2926582557882823209905246862501370372664751899459, 2923906458250528527500108672407414346330987909955, 1128665941819969, 1128803648820161, 145290293153984, 145290293153984, 
    1139244651778496, 1161234884202944, 457547442557376, 457547442557376, 457547442557376, 143087117537728, 
    158497460196288, 28545062744684385483917565098884251405678543683, 290413081530816, 284241213538881, 284241213538881, 426761117503936, 
    426761117503936, 290413081530816, 290413081530816, 439955257037248, 426761117503936, 290413358355392, 
    23014456838481962284050643317772173420391306050, 531567448248155956624631563661565778669274727921193943892106734364477886087763591032388992032921789316, 6707465288651853479360495980958811345921609375746675568970714380959931488484015875868622091053248403566506894901015251889425515589624072847027273533206813734124220414125540964566937137922100968833727162609609570095005134494076800848605556261369393406586952712586432470250060605650169791769616349589905188264808553864714198898407019758212951118009110692431274053816358049136618058, 294824566592448, 294824566592448, 94198707057520514261017247657215916548175237954, 
    1461512798593285618585439387753370289777974252354, 1461507223406985985929654003823802127687597757250, 94198707057520514261017247657215635057092399938, 733608112533796630262035467439773275278805111618, 732180864841090670380977181470328283750639702850, 1464361718792397905691770575762701117960363250498, 
    735038153264170277205847118285400244185448157762, 94377113019108759246149533403396821966320112450, 567503173456576, 567503173456576, 571901219967936, 571901219967936, 
    1461551814178488489166375476164047290309911058242, 2923059026695609261038671777662968632824010120002, 735038153264170277205847421108303879706054332994, 735038153264170277205847421108297265018868699714, 531566893848442985190980866565838319814510725970038352137472845857340833307965674835776787600474547076, 3957286482768179822531042257984468785437068082030258016383769115544942809057608321147370888756246284286255693059950817639862260315512013855012130446437285934927226024354608711, 
    145281569001664, 312416337400768, 312416337400768, 2923728051603682931639956325186457639407451118402, 149675454763200, 149675454763200, 
    149675454763200, 149675454763200, 149675454763200, 149688339665088, 149688339665088, 149675454763200, 
    149675454763200, 2923059026695608287479296972801716333552219461442, 2923059026695608611999088571267728496983139161922, 366090429703230115313587502811779246858310797123, 580684428088000, 580697312989888, 
    580697312989888, 158488727654592]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4130004100926964d24004024de4d3492412018cb2c9a69ac120c64d34934d60934d64d24d358000209269a0904004024100920904924020100100924004004820124964c24c0402492c92490010418c9c41601d412000192193010010c9a43301bc124964c2403582492c9249069008041200041601879b60301bc1609a6800800c060249271269b0120831534935037820824da79b6de0924000820926824004134da5005824124920d001008049249a4924024126dc4926c04828e48905206900c64da19b0de0d04d80d04004c04326d0cd06b049249a41241a4000134864c358361b618100798481c912504120d04834c04128d069a6e049261249b0d20924e249369a41c4926d34800020924824900005130d30030000b2692482400004cd64c06c269a49a6b00004020806d001042341a6db600010080018080413790cda6104d2d9b69e0400104da4164804106d06927980005926924120104a64324a041349e492580, 1161223934644416, 1161292725424320, 1130438095606464, 2924441673409005353028209606766414086653685568322, 736460005439583261659593149001266642145497860931, 2923192841886358645760592555771045387912758760258, 
    51386513902450287887062717442484616599899753283, 1161223934644416, 1161292725424320, 1161223934644416, 1130438095606464, 2924441673409005353028209606766432136236701356866, 
    1161223934644416, 2923192831677887638132283606544289657538786399042, 2924441673409005353028209606767557965783121302338, 123695392437752162267297064228050704891931953232392857209965434562195525412895398249253533934232014555082304969400906757094743142347449805722689569569392983291353154990340678, 531566814649450785657876670215531265998023650814469149445962678396974550855641480900928967934390477700, 1128307859395264, 
    2928723415891629091193415133217131434807367078722, 2928723416487123232671248800015070982561261949762, 1130437626303168, 2923192831677887638132147941883454188907778806594, 1130438093968064, 2923036726461497923770140233772942061223291130690, 
    2923192831677887638132147941883454188907778806594, 2924441673409005353028209606767551210383680246594, 2923059026696272904645699412188197311218051978050, 1134842306105793, 1134842171888065, 1139244781810113, 
    531501997402235135570266057528833763471682157651696387902154135095012962116346792151183095000307549060, 1128307322524352, 1128170351235776, 583988817845715522282548277057316118034242066726001551816895432248113847622710215999529601363035012, 1130506553398208, 1130437626303168, 
    1128170082800320, 1130437626303168, 2923192831677887638132147941884609362220789273410, 1130438093968064, 2923192853455959121072209603540584237853954806594, 2923036747642912185665507549982626855135656088130, 
    3957286895545320061413919472958409645424085186261335607198354468214506283902308234226851265542558106707857435551514029830420640234258369851367470619126668493135111716970475078, 2923728051608334274446298948382990576094680273730, 33251311180870637908850362346532789462154372962339655884440062191249805143996469626718623616042214276, 33320817064557699315718245208452227334774223121968803112560286138454195804553410831699237208856150916, 1134842306105793, 1134842171888065, 
    1139244781810113, 2923192831677887638132283606544289657538786399042, 1134842306105793, 1134842306105793, 1134842171888065, 3957339332984168043494820449866664730648709415620473584837467617283755975736734667435069339337563622868884245518104840654559129936665604913092196844736817062989590191461596742, 
    2923728051608334254163888740266685466162673767234, 33251311180870637908849606701380125042695486034569822421310516445121656221240162115429772072142939012]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249201208049069200000061209a6804924020124980184004820004d34920d208209b69a69ac124104d34930c60800134d24c35824828926980004904100904024804934120004100924000004820124904000d04024920000100100904100900d301869b61b01ba026134c248348661a6d85806980004d2193010010c9b63301bc020934c24035824926d861061008000000041001879b60301bc16c36cf00c09b009248048201241a49040000040269a0024900904924004900100806136f66db1800026924906b04004db99b0de0924820a26920004000134da5034024134c00984004c34920800100804924006920120924800124024000d80000c008061e71a4806d01034db1980e60d86dc61b01d8104326a26806b049249c61241a4000136c64c358361b6d81807984d24100900d30810006240c00db00011c81b6db60001b0000c0c000036dcd98718cdb71b8de040000030cdb6c00067b06db6d80000181a380600019b79b61e61b6f6db3cc20824120904900004104004100820824924020000100124004026d249a49041008201209200009a40201a8104104024824820806100806984d36934d30820904824124000135804d35020820824904904104c34930d209a69249a4000180000834c04107b069a6e00820180030180104db69369841b6dccd36800020d248249000000040041000009049248260001001240000289269a4b0000000c906d001041b81a6db6000030036d86004136d8cda6104dbd9b69e08001001241e0804136e069a7980000c04966020104dbab28a34135134d2580, 1161223934644416, 1130438095606464, 469678024263016139997925092733038148265021498842876956298899586531685883355582303001179184179484421505256473335555695682572593678469943427326089789243350715906782197321511398600367900246175960134773535431392425133688886754632352241094341393512964122738728749535112, 2923192841886358970280384154237057551343678460738, 513258889784516564910739244558081963448152154053759574390080210393235551783210799614336310876033095827373151273664681914249514836972170100563990566103931347903534153562694, 1161223934644416, 
    1161292725424320, 1161223934644416, 1130438095606464, 3958161982852239929516173254380978619403184328274099921641252158115666795481697524248544194229144757116520398718548948582373663893513306882365824203913593675212566168355174982, 1161223934644416, 1161224003915968, 
    2923371238321369853829870283440062922772571045442, 2923103628696429223626470449069872177170108980034, 2923371238321369853829870283440063344987452030530, 1161292931142080, 1161567947461056, 1161567611916736, 
    1161567947461056, 1161567611916736, 1161567947461056, 6707465390364365307182095125680381202604781665227609877328574156601727837705869409039535838733798526089830611224902398092939828445654538508177808970880009785881228387377778044972296904404234289644434375946643860355757921812174761143343958352578074515722619043879131173698053671971036301571056132237624565684563133360225817524369442886024518088916964712497316474466030790139724362, 2928723415975703082009977653683026330563047864130, 531503486361603566275760653220519167430128034432585754209242425308879491362098076808896265269632361284, 
    960962154094212046835217857624440951424096275637579796069636816868642619264984785735035035233159779123873894784105522962006944061387967525299830948233227962960507173447202066213000921174324906279652650463844006422091132013856551239973742609450114369047233064499877512, 960962154310961563796381349092987141023482347080576280328732927650018768590002535445326502868749945654328487325878141426743632794923418040965390371636405517744364308925008086054178346212446573993770133999868561300655409331624781512045027757814438056855339560499877512, 2923371238321369853829870283440063344986646724162, 1241673271418550916396520376575730307540178349248654888986342499781980523833003359678130618967144495355375247878611979269935328552090049822727441431498363516596854523599460406346019893258988385028762334054296295675416490048876598575474269615835495363515257797547724224731831809652044908322745263378386696615118235344170368721756988023768459969739642396170380162451989596124324268706684102759167462281964331762988994398623781702700405784282383367016942362884716605009232598699741549410557652649622216277737721996, 960962850714049710040085628873609825802750427199226412457475441315295320467282615802139671429763247131503308992727617149271589935272404068657789616807057977244950933366442408181616720959548670762524733992606946770400653272203573821493730554059483890873008680499877512, 3957286482768179822531042257984468785436994218109606309930234532562980941598398225378073911498917026042393541056101850350873541938853003773173799117632595723917690409479797319, 
    3957286482768179819956743135435490142320235095902675067235294942625017422144181710904869853845358986894794954384283188081039807268475209140374578660951386650069499003568880199, 1161292662706624, 1161155422982592, 1128170342584768, 1130506821571520, 17127037647350908525252730186018423426786544451, 
    1128307859395264, 531501949882260587742187610211575808429016602674890689220920176913593323479167887967834110454298681092, 2928723415891629415713206731683143598238286779202, 2928723416487123557191040398481083145992181650242, 1130437626303168, 1130438093968064, 
    2923036726461498248289931832238954224654210831170, 2923192831677887962651939540349466352338698507074, 531505989080216822504543739506933666532098555589091239672336767272436127382411072883958701082366222596, 188397414114875523427701518915615177720647914306, 457547304145345, 6708707854819202884603636176463012108275106188018871525410317605420485298173177239391271040804994390939444670675304637642598103426392960448823243829310950313614222498375136128620182622192123406006692395420123847061904761902192414415189849435634182303620932461687551170554279555971604293708250251710432404755890494070856847791788553979125550136905191054059114549564845323962975306, 
    371085815679525842285135295996346575438936544066, 176063737500097, 176063737500097, 1128307322524352, 1128307859395264, 1128170082800320, 
    1128170082800320, 1128170351235776, 1128170351235776, 1128170351235776, 3957317794862675017712751301202686775671948970471113989644739306733616777002398946886346849952058556984040205422925154294805554256831536723390849030727781783431479816196423239, 1128307322524352, 
    1128170351235776, 1130437626303168, 1130437626303168, 2923192831677887962651939540350621525651708973890, 1130438093968064, 2923192853455959445592001202006596401284874507074, 
    960962161246946106553613076086465357131036759734445265952704583892608121699889201417465547452352078905714281121615382651059410505247127097265534266940790355068065121667465879483907934496929324859610837293975661863466069849915511879355934624910469995803198488496988552, 960962161246946106553613076086465357131036759734445265952704583892608121699889201417465577640365967297555312577253637411714181501830834549476031170755071700726930095338330103503316309929346644574099847128060571483361575854149071618040396581222838424314070040496988552, 51381112941387784284626186105048579849049871170, 97053213332550363998984630375231429278622028610, 123695392443150858820748899887420302518541014260326841061158186576529611100498503793981114644910379067544109727358190191350206942874425679651380597416081380556891046597852743]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924920806d381c6d20000a26824924824134db6e34984024104924924100924905124924904024004d20004d60800104924104c049241a4924100d24c36da0000134d07124804844d00006c00004904126d000000000000000241b6d051b4000c66dc11b6c00004db6c36da00001b6186d340000000209000009848041240041001340441a0000104104100d048059611068000009248249248201b4d049340000289a0924926904d34124924100840104924134c24924986186e36db6c24134904964c00034920930000004d34105900020d34c06006c200209009249040000001a08001008040241041201b6006366c00125186c06db6c06000c00366d860051001001a0c061b60379c61801340040008000200041a4904900000db6a288000001069249c5000036da6a40c04926db4d309269a0824924920900004d24d44000820924924824000144925104024924926980005124db0800000dc61b61a8000104d36030800006006db6d06db4db4d30820924924824000104934c358208249249269041049249259309249249a400013496d90480002690000cb00004165937920000160005824167924f6d80, 1161223934644416, 1161296953413824, 1161223934644416, 1161223934644416, 1161296957673920, 1161296957673920, 
    960962154094212046835217857624440951107806712262279983817202050448170655034580029768328270786130071086255209997667329915222847213978934493506894479760741258540216311797478417141812949510751527537735416576355285350567129064275513333446765515775448629278408977249877513, 960962161246946106553613076086465542205615557573065515190921183565451612352787909040766079651138504729560130847144480128054657021091273596257255677441175188003488634192908011397797557038327425985696040234368119260657581080499582776292379833173043636877656337249877513, 2928723418528153142183535662865341642988447616835, 531504151641267062747400581313134447814776641310020136407040600421095136971018494699882397050804997829, 6707465390550522946789860969267752413002088172480926926541585090883387819013547084458945004730414139790283293070701334527544043748459028808557486946071787493952723610901651723461976923565990621044545831332474965983261825946061646445214050015887480410611159304617642589943727007581707197414776706452717812727263249325011955224053987889730113471294446059336556949617795332672078411, 3957286427485527111966371202728695842583086004901931236426995506072616775467236419197880985702117199732300272127969839083181903243704474501254127869454457735409499212361988678, 
    3957286427485527111805477507569384677388288559763998033758561781701494055501347887043305732098769822285575360460981172691317294826805862336704176590911882168293987249492556358, 1241673271419102399023427401133548204471370824065041576931930751793245901092937601375328472750869528716746384022830975495660185690178315642122727179826232549738257263072802218181797474442858829895469816834511231689340764301839590437087960378183908898204340194813175771655560307727029625104367850038390135927112611265014671134205332874743476389962985081200629236542068282858462937114549855491166107546704954165083013132243328098020608170382930046506745984569209047269480853129615180579419389316073912484609089165, 2923103628356146532186677983832639946819143748163, 960962849765770573335414260340456838955501032558072554501011143307895769897686897087650781750248923248430203378468996578137453723023060965205965129494716045943761917513471052103537293181196325162830112350391848023053113231124683945121667374530847616209518865249877513, 6707465088723695756462041669077627629859943211427288058831457131341713279935809002271610882710813650485932675803784137863628345841985103568306745798581158147074384868595037607039921568856802764523077785237723707149458663997015577662365705601035296011234305753111001077961187066934169305745251765191385971926028346252459572608401380585183041787493444181934441944049748146458592330, 3957286427485527111966371202728695842583086005118546056260009108200713492655297261866719173303911703721646443879684709915012693108972297993093731426110884722610876029629068870, 
    12995352556590391547090711667250586426391464357400076912311375531663343041567560235921482852927579133498948800089452705365656115620026971764559472355651110622181767127857590587927179238076744149701088107269902873047117215703868736895155459350219604231982115670174825017692413245610156680971634011868477351001548578204349992936331137670883174982342212605507445228146260197963, 15129686125361116623662076964425833005300797141065786733771617122180420467800614305581003132509406426081820115971944083728535400350138856055965882219289475661849478727905111567136729357121261803806524436290884170232385150084321080018460196674985032417553249877513, 74906789228993, 976563712720603260717777208750273388250964354637735816037109208872807088797734534422239527110693287867625175355091054681840218667956039101278308826770678063676805075758418892739755570867542993144119977818300023679158541664666348610788485954023038737390240017249877513, 976564170999001315532889733368560382196048653792845013125397604553351615971739256936707821033609179570993235993437151075672307392693014210318830869321238190238546648645050696628398084573719567137091969899038660482915993533584565483038374436874249341142827281249877513, 3353732746239847217010914814318849298566905040794536831012404095733855747015685328105455445614511438747860069146739202176916172054926006715991653242498100339323605223143262503674726879258102296563997567577195456737890012686995592247419021381276322840265517165278041021951755024528224512932768467024239214731342252799698110236944158590070528170832997529251349291066893776252584523, 
    480481543610929162069102182369623637111361219363730816803003684398040793415174390128664562072029200448464726304424941761958425749148170173470610399787612253549960695277237647187638784797851857228654951883595831998347037543821604132457978340149899358659150097249877513, 15407740796022820280058372756542060607757472298366080610665729006692088462919363511911619188621057648357570321524917160670434088752609718255196776881183792203418856019024805437798534338484836664891000007689371276988194940494833215676780089686602964549641246988552, 978462815493721806278134885430146034205676095304594973089764006051352659120935699267056063013479087928900653210361051580144021980659710616549762709878643817470668494384776292862222111402248264634900175948900512175693105652568945233783308441362338627947856145249877513, 439944649650625, 64880622651665479313570421941734428103329393415307907375364420830872620750229776869725410527645381]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4d34930000926934d24d04024924d349249241009209a4924920800034d34930100964934d24c040049249a49301009249a6924106124934d24c35824926da4924904d269c4d24d30000920000820100d201049b6136126124934c2403582c96d9a48349009a69b6db6c00024926db69b4d209a69248248249249a4124124926da49041849249b6924924126db6d26db4834db6db49b6d20d34db6d64f04064800db6d24db6804126d84d84984b249b6124924014912520824924920900004d34934c60820824924824000134d24d34c2492492698470, 1161226083111104, 105694919921856, 1128172498719424, 1130440241976000, 74913231679937, 145277823488704, 
    2923036725864841676285091483993723892218483249986, 1128309945799616, 1128172498719424, 1128172498719424, 2923192841886359619319967351171369706816222073666, 11596442630309896371493455873971242593641632578, 
    531501997402235135570266057959618885364843945119649996695113265960375500761426589461802113610699719556]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924920806926de6d200009a69a49248241249a4db4984024d34924924100924934d24924904024004d60004d60800104d24104804934924930000924926924106124935934c31824924936d24904d369b6db4d30000920004920100d20104936136126020d3583403582cd34936c349009249a49248201a4935924c318269a4924924904925134934120944d26da49b4824924904136da49a4824134ea49e4c04034924b44904304924d26924d20924924d249241b6db69b6db6836d64800db69b6db6804124b04d84f04b24924124924014724920824924920900004d64934c60820824924824000134d24d34824924926904820924924824000135924c3582082492492490410593493592092492492430, 1161226083111104, 1128240733753536, 1134838011138496, 1128240733753536, 1134838011138496, 105694919921856, 
    316801360073152, 1161226290729408, 1128172498719424, 1128309939311296, 1128309945799616, 1130440241976000, 
    88652976755392, 299759215580096, 163419769541312, 1978643215499139501476759980673466366837641082419634725217316849180467675371691424846428161795472944102266062071535185640373199643838906357575393595692246502019106527801997894, 572163074560448, 1128172498719424, 
    2923192841886360917399133745035418360539900875586, 2923192841886360917399133745035418888307495473986, 11596442630311194450659849738019896317320434498, 313228237214656, 513258889784516564910739244558081963448152154688373304437953710590429281036325532766740036008266566811423691687121005099007201418620862075209443223827333043817359960144454, 51386513902451585926615030049402227426713422659, 
    572713384022976]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24db5144930020936d36d24904824de8db6db6c301251249a4924100920a24d24920800004104900120904100124804804d249a4d30100d349349a6186124938d24844824934934db6d04d34d24d35130000db8db6db61881300049a4100d30186db61b61b8124938d2480483d1b6e49336d809b6db6e37000024db6db69b6d209b6db6e37041038dc6db8e08186db6db6dc10309248249c69249a4124134d34d26986184924d24d36da4136d24c00db6dc6db6c061b6d86d87b04824d24920824d24920900004d34934030820984924824000136d24904824d24928900006db6db0d80186db6db61b80001b6e36db70061b6db8db6d86db6db6dc090, 2923059026695286044396378167530761086920820823874, 2923036725950082318941076920140305752668086771266, 2923036725864850767909858660842160036384792976194, 2923036725864850767909858641952698467784994132802, 290279660720320]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924e34db4920120924d64d34930c60934d36d24c35824826926980004104100000100964930d24004004924d24934d361841269ad22d930100d3c9a5b3618c124964f24c35824926da4906900820020100120000000000020124904c24c0402c9649248001009a49b6db6d34c368269248209a6920004004136da5004024124924934934d86904da4b26d3cd063049249b6d241a4184d349e4c00000020000000804b24924d24024016db6db79b0f3092492924d9c7b41361b20126a279b0c40000db73061e60019bcde6c3cc209b6db6da6c34824924926db6db6db0db08269a69a618c006136c660318201a49a19b0c601249249a49849269b6c30c00c36d86186d84812534d24d24984024d24d369800049269249b6d20924d249368241b4d349389b6d049269249b6d20924d24936da4126c30db0db6db6c34820034d30d30000804db4d64d86020c36db6db6db0a30db6db6dbcc249841241249269860008009249a4304000000006d001341341a60001861c6c379b7804d0490cda0104134d241b69b41249a48261b4804d34904da6d06186db6db79b19b0c30c36db7b04d34c269a4d20906106125934860400100126d04805964d06900004124924f24834104d24906da6d041349241369b4060d80db6de6c648609a0d24934820004004924d2180, 105707805348032, 105707804823744, 17127037648035969725953415877778136662720648002, 105707804364992, 583925458845267951737559787845705858078069422078953452252870657727135882444280837827823654859457412, 74921966310080, 
    271725294590665780579838582906530425241001979754924540940371749673933795902132261525798371270406481307669588476372105058610166631050494127404626305364425977194100696205894, 11596442630329367558989363832413219838119449410, 105707805348032, 105707804430528, 105776595144896, 105776595275968, 
    28545062745826614654543026945341863418623169346, 105707804364992, 74921966310080, 22858351027200414543624372995685307459374682946, 22925253518007781603752827692693975896590127938, 2928712330768194127084839835472144625729577947970, 
    72709779231169, 83713619669441, 72722456514752, 91366196720943522954298776217293308340905972546, 72722456514752, 91388541107355611187798251113377374225194554178, 
    17127015955035078516109412005043323733551354690, 11440325928725681894328383885796911526022499139, 143086979125697, 283816011764161, 424562224280001, 123665204429260709806041275404950103065106839006371825385887742384525504741431190098856672538069473033701390782185833154404304975798942197773725826176420164092253956925814854, 
    182711399383615229120058316389949143136392502850, 143086979125697, 33316191787932682377736156598914966886223234806159449376287367214012985907029481669818082140308120452, 33219377757385355898276676558133420927633009508555753967628598589638704107931478782362227714807309188, 33316952107536777270252622523404637640295426669632118437616922537135571102989902273999706339065734020, 11596605965191786516834128977657726817316916035, 
    308705900893120, 313240719463360, 299634376315840, 299634376315840, 14272531372904220926604199939954193483414129475, 308705229804480, 
    132875514200551213644534943466699757943913113481531885460569004211995459697284908673494695994392100036, 424561955836353, 567502705791680, 568052530811584, 567503173456576, 265751030381101160251914683300529874584537523200926801998866621618494077194568517710875160529360864132, 
    265751030381101160251914683300529874584537523200926801998866621618494057942125098465582083880917615492, 567502705791680, 562967687992000, 581109361414848, 567502705791680, 568052530811584, 
    567503173456576, 567503173456576, 585644716856000, 581109629850304, 581109629850304, 265751026421103222257673731594671456316706378116872244712286550381837024397207851725655527060393116548, 
    2923092521540375294034049636274836970428673561410, 2923181724861451783447554242611302171306465694530, 567503173456576]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a49a4b24920d60936d48d24834834924d24d300009a69a6da6000134d34d248008671bcdbae00000804120000100104db433418c134d34c0080480513d908d06300526926d24db6db6db61b6134d04d34831804126d0cd06304124b3433418c015924924920120db69a89a40061271a7224900904924924144104d20c601b69b69a618c1089acb269863004924a0a24924920800004920180d008249249249a4000db6db61b6c26144906db0c609841349249c4c248051249249040208249249269868248249249a43000041208000001868361301b6036124d368308061b0184c07004030d371b618c1b4d014249c8a06180004d269a4d30c31904d2413486040410492410402cd00036c36c01934924924d208040340001b4100824b36d863059240209379289a6104124924934c35934124924d2180, 3957286427485527111966371202728695842583085996584535613842205048532931637559024792454676594885102530300326874915430557200564843686240101516439781353523324332893815637085747782, 3957286427485527111966371202728695842583085996584535613822031221059764213607287271275062586856623376003749114044050296952064157115542802480544484574112730521911805733804930630, 143078384996544, 2928723418528173262410614767758102531130679937859, 72709779231168, 283816011764160, 
    1978643215499139501476759980673466366837641082419677032799321887716186797528880044286962371098750802617672973149194224654242296885267189409649612888270026505836691182839626310, 3957286427485527111966371202728695842583085893995756930222147094929657700017230586965463770213679233447073219249255551686190996045575467353576994022483000614697262923756041798, 3957317558990021722707811217621617241899455792712998545897505020871721015964960858576339838852076527262401400707611589775995748003734029386733327720270461186289006376101305927, 960962154094212046835217857624440951107806712262279983817202051032305909028505607052679838320672778845095049841217856243603849385796115252505321835475675341065510428351930151868775859847687494995239146840468358833571914579672284591186471487166100603412676648499877512, 72709779231168, 3957316621027682531930283469287840356503070084155185420312377571513895226036658818375155384434455899024341213408320040503500599653478164790654640209284022677149014617009125958, 
    2923049270119604375078001797464796007911740460867, 79306641379520, 79306848997824, 79306848997824, 79306641379520, 514441938550696451800852168418246012599396848631606762116069806470162270161030665220851666174386518037494121215601151110054705649698322250288304769884726851702264956935751, 
    290546493952448, 88119914270912, 12845278236346304838727439830892752979621843778, 88669879800768, 88119914270912, 24263303334136949767317050898456479735524365122, 
    3958026120435310950272415561010871165701690878757941519967916877189444258053882503978388137504624738121278944312605649603582967744044951823376025522949129092294366903131929158, 88119914270912, 88670223733440, 88669879800768, 88119914270912, 25690556471360780462618914796164031373742445378, 
    159322110694336, 158488727654592, 88119914270912, 18159659651264]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249251c49a4920d60924965124d30000924d4c934c04024826926a00004904120000100920d00904004004926934d3c930100d24934db6180124924b24804836da6de4d869869a4d2d930000d3c9b7b3618c124934f24c31824926de6d06106824120000120000000000020124134c00c040201000000001009a69a69248208209a61860041369248358241a4934934924986d069b49b6920120d24b26a269863049249b6d241a4184d001e4c00000020800000004124c36930100b24806d24024018dccdb71b0c6092723c9a71b0c60a493279c6c3182892cdb71b00011bd9b6e3618c1a5b269c68318209200000001a00019c6e4618c0240208008060000671b91863005a4b2cb269b6f6cc0c0679b6dedb0798c9b49adb20f20820806f0c0008000679edb063089e49adb20021824924924920804924924924924128d48d36db00009249249a6000124984124124926984104104db4d30800100124f65804926926926100da69a4da6000144d34da49a48269c6946930804db6db6db61861b5134d24c30c36db6db6d86206930836826925130c30c309b6db8100060026b6d900924924924820124d34d34c000269a69a4924904934d349361209b4db4db6c000269a69a4986104d24d24db0000924104904924a241861861b6db70241b4db91a6800024d659369800069a89a6db0c61134d649368541a4d34d369861849ac9a6db1860934934da61881ccc36db11b6db6c30008006f36db0824820920800904820824924020104104134d31820004004924120100824000820124104104934d60800100124d358248209269a4b0620418d9b6e609041061e6d35804006180036de01341341a6000186249039a3780510510cda0104134d249a6186184d34d36986207986de6dc79b19b0c30c36dc7204d36c36926d209001041b6db4c60924824820124124d34c001040269269a4900904924d349001009b4000000006020b209801a0904d041200041c092482082092c9a40001001a5235824000300021906805934d06980004124134b28834104d34926986184125964e2630c134000d8124d1b6060b311249b6820006004966da180, 105707805348032, 105707804430528, 105707804364992, 105707804823744, 105776595210432, 73272422044608, 
    73272422044608, 82068515066816, 82068515066816, 74921966310080, 11596442630350136825651665657191679416980280130, 11817588341826699396317970302767653210963611185882153913679623398069348454260600086407679955076200607055172234813416090469942163514607148194469584070212729216199194471796902614094712559184434442907052108560256553156335531171279495733257947037267578810315720170704498550129829246266356694315627194877171084467243774900256282420269831830637242682201863956353048171561043439032599627, 
    6596795743491659889631815078102655738080388990084945831753243356064616085725985103364067106020480594810109411248505434439745044689794157093613045258291454219767847759437069895, 246514016391360, 35201686311104, 298361598154858736684295120604870072349307936449131751858627461007079088732740502906317379879879888711330173385244450807635832977117684099223670630280757754250776880337972907316085918690168510587958430036424219260630063836584622505922751127928268616068346952423884660211181299848609159232522639518980301752827428956001296497052406254184636265975316711226252564236469306829255572711615899420096341184058316154500991477791545604653990627996407388106094908752221775435062753130553296249380834916915530614541, 105707805348032, 28545062745847383921205328770120322997484000066, 
    105707804364992, 583925458845267980551799711377795049308086085399811146184188763902463013035507390191242477029310596, 513258889784516564910739244558081963448196690018413810497298718240619332172135219707525983134099381484601228388249135010864460401227756949204629923085059900752906531338822, 74921966310080, 22858351027221183810286674820463767038235513666, 22925253518028550870415129517472435475450958658, 
    513258889784516564910739244558081963448196690018413810497299018854069927222787933213759285040973409213848777201703119696256594189236808721957711886443809275952048107387462, 105707804364992, 246514083500224, 105707804364992, 246514083500224, 105707804364992, 
    105707804364992, 105707804430528, 105707804430528, 105707804823744, 176076617814208, 176076618731712, 
    45694401223467090200652287561921186431619832642, 45716702053736212554030861729266570815917268802, 145290293153984, 163432654443200, 143091269898432, 163432654443200, 
    163432654443200, 176145272344768, 176145272213696, 176145272213696, 176145272279232, 176145272344768, 
    105707804364992, 105707804364992, 105707804364992, 123665204423862013091695744586263243078332998781788532443937729108824167316601303465923524800550402188448545940316143953459162024929319252363569025041935812941769520032210502, 365399103960235674681222881499668458386685446979, 365399103960235674681222881499677324848451832643, 
    365399103960235674686174641656810120224307170115, 365399103960235674681222881499668458386685446979, 284378453251008, 1247795335031679740211755820867567658480886057824150441860710899214638449120397363202936635480417289862134534403552837248809046347695392550364377704510455658777022910025458327001828441433619029094462221121046663863178117212697780503612852906363162027865749447185893232181234711149417156371019058369127380014563219816169835246338221773071851770013178070100935094841209540479578801845469055278170666470026535639666769606307313186295931187813300891875706458355720550685865900643364477785742973453778608734068891533, 123665204429260709645147580245635889287654958915624612548026939817015984744549619529060323945780795294368614152585940953452286067509007634933849711662548787237835425391278662, 15015033664604734385304171617226701436605314496455237494291795681606021681079827736075617074811617342380978787129425599223626254634291809215979749825612586198191405910132609334920639918923026833078032612311753068285899564227583555518907634320631966795309609248877512, 
    123665204429260709645147580245635889287654958915624611256901998368654085156184808168726255668631932398534921866647624125484334249239569044458419361319126873244571446596827718, 284378721686464, 284241213526976, 365421404790504797034599033083784758606133480259, 365421404790504797039550793240926420443755203395, 365466180675615229776067913288732542660198288195, 
    299634644751296, 308705229804480, 299634913186752, 299634913186752, 15015033881354251346468457975036149315255745592249626807130963813530430696979169062042352290376891651855992138139960607797816754048365006110807534918824188602283939297982743186520619222551560803989415138683059648793330372839059494246350461168582697859162664249877512, 286852440396736, 
    286853245703104, 286852440396736, 286853245703104, 286578229384128, 286853245703104, 365555383996691719189572519625197743537990421315, 
    308705900893120, 313240719463360, 308705900893120, 308705900893120, 365733616414272509981865155261421828173995199299, 366090429698578467635883580607282631685163731779, 
    284378453251008, 284241213526976, 284378453251008, 284241213526976, 304169662550976, 299634376315840, 
    299634644751296, 286577476506560, 286440236782528, 286577960948672, 299634376315840, 293174546273216, 
    282042190271424, 282042190271424, 293174546273216, 290838283293632, 365555230955401810099649026171064542342724801346, 308430469338048, 
    132875514200551213644534943520367738736129365738126414663182246494013883153221939729806370531322576068, 736462597711360620395576480229845721093811213122, 567502705791680, 567503173456576, 1978674347003634112218199995566338988832912183588640546304204714223072158528591288348600150942804823285205454608948385692021558914042724342302296695287698348270132987078598215, 567503173456576, 
    567502705791680, 562967687992000, 567502705791680, 568052530811584, 567503173456576, 567503173456576, 
    585644716856000, 581109629850304, 572588691559360, 562967687992000, 581109629850304, 145290293153984, 
    567503173456576, 480481772431995833936977635595058420856696696400866965468298777672980886608954939286177861865716603764065919412666578866712239511616264433690789175962263888360271958298313807903937871472519636324421802757500467319309247657133922918915014276817907262934778128249877513]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, some ⟨1, 0, true⟩, none, none⟩ true 103 ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩ [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14a24dd69289260041249a4924d301009349b69a618c138d24924835836da6da4986804804124100100800000000020138d24924804000020f24800000526926da4e249009049269a6b24986304db69a69261ac104d04934c000200208000008040248269200200159b71b6e36000145124934984046dc6dc6e30c049a69249a6020124924004924924d30d60494d349249241009a6db69b618613493492493486db2cf249e18049b6924db6000124d34104924924d30186c369b09a61349049249348618003249e18005269a6b26d80004da69c6926da61269a4d26980804924d04124924934c061a09a6c26985824826927b2c0209a49249208040000040000008249a4924a26000d34d441860261b49371c00009269a0824924926980006244db4d30824824924a2610c000165b6d804004124100920800000000800100104924804000020024800004000820920c04124004124d349201048369a09ac134d049249358000000249a6800004124d44960186c47b30dcc106000180026800520b20b00020001004164d04d60d24806920020100820024920904906020b24826b04c268269269ac000104934d25806020decc37304180830f309ac00, 3957286427485527111966371202728695842583085996583901000112159022001775974898460997604587533080905206625930433367066715127016441011480512660979073945684687739754042164644903494, 1152442948129729, 3957286427485527111966371202728695842583085996583901000112157175032735518907247923067545258732264969682596322764855773509150852414470878293151875831008069909979482069814704710, 1134850761429953, 1134850761429953, 960962964310898367382301938902646276349377519627757552540401868042180777248320108221814391545751077208583700358376607925680190956995426044781419772607336861244773452362120906079825087230313950277939574083510665485239321678311851662533963370221740755077071120249877513, 
    1134850896040897, 1134850895647681, 1134850895647681, 1134850896040897, 1134850896040897, 33218933866359174949877372674399432634343736118208805752558438466148870432097754168208672471810208644, 
    132875514200551213644534943439865769747021837150540490529241855995902909421377311899824289493453683908, 3957340527089466535057134519817468916524261375970515950134004926747441005182718644414907784517257780201416706539228155132037153921864302748267186490590877833918660618848533063, 1130452714918849, 1130452714918849, 960962964321386247235056381253461827797765469288975759184695917556199717483712209159929176243987798912963861102689240340834509557865411060012965750565810170580705988224201767023743208786965891718628590235860800374090717664754998099038585219708253339734016273248877513, 1134850895647681, 
    1134850895647681, 3957286428406904657088817821929855003232605641917737774910070203597475306224504309091224925363371038781774563297741287984482810289903783603596214615033682603648042760495128134, 1241673269674354631661583483792702917289146103012755030367832985387752201327204752918835362528563757907210425608592592790103110853033084887175018453424497656007029091400457806870824125194495438299988959454030269490762957354299259888975240211171759249964284622710569864538255181224080183887443805768230234775118116738160853513739710455801204382695722340659648888723948399421218584685000896543425592192571469935813288648164633444323570616243674690737989273380965143163662802215723502888879936906095029755406768012, 3957286429328282202264895672847662803729832874854110013482035372848509214884458285388636460367108075432957274687753981981107703383041123799075718430646429193888531466623613510, 960962154094212046835217062735177693144831915984781891015893758922530030516304011605573163101835244119791208582505006540332078075036196470796044316184263873682906512662854818610038689061627980858081891117625138773977020151598218412423474866834884418991063313248877513, 1128253893530561, 
    1128253825881025, 1128253893399489, 3957286482768179822531042257984468785437039667493644440214733377798282814588238147466117280930717378191047784854173491835470213605103452774862588813963687423373277315242883654, 3957343033236389474055868572116567475524140360006627866971631389379461384180206809195567571292430416306795982450679946727658914255349388708438342068342248992199867289344899655, 3957286482768179822531042257984468785437039667493644440214733377798282814588238147466117280930717378191047784854173491835506131834717906398973740058368265019020813137214405190, 3957286482768179822531042257984468785437039667493644440214733377798282814588238147466117280930717378191047784854173491835476199915810308602359298429196743426604841817939606086, 
    286582255915968, 6707465440524460278504407947217064193565144913477838832915923365910817711847894720380013894508772549479915123592700578131793860462899094996569086035081738717069754626849807139254440754856174056036313147392194427917604408015820700038723698772176938183423000590416155528955556028127344471024411647666569556409815325901569525771748674633810453723711153192003589989990828965322048075, 960962964310898367382301938902646241647893995021180950029750172500901218725489372880962134428916139248126030067792362797595051915879036857279433143428568194875282366180451328521659386190575544001032300795803106026018605267548561435575265359980058570238492944249877513, 960962612589359618611493873711274145089832674245279469494933829144313762538157790426175286328577647597616455987094026122544183819627912398403626389920584027534901302846443928060476125249635346995081937603713257243127698082344406966011729581585923919436611856249877513, 6707465440524460278504407947217064193565144913477838832915923365910817711847894720380013894508772549479915123592700578131793860462899094996569086035081738717069754626849807139254440754856174056036313147392194427917604408015820700038723698772176938183423000590416155528955952790675652261050169366582329041789253715337798463430778112833064329461715597791079275406787705975886594635, 960962964310898367382301938902646241647893995021180950029750172500901218725489372880962134428916139248126030067792362797595051915879036857279433143428568194875282366180451328521659386190575651837527960308239052974785620169415793905178556317768587051333091600249877513, 
    164355756867840629297624517120193371162607798818869224158203524522212048504272454274402124986489797, 15473349476422865172402064722852595413522650061700783273762056920914168010606341532069811101509294610002856285470389469507354421276177828288180275908732720509594985364036532586737861874522811763186133937219549473896983202595344558004504307053618146607376249877513, 286582255915968, 286582255915968, 567503173456576, 708794716787392, 
    567503173456576, 567503173456576, 960962620364374549603910442865360528676463723758862272072103780586770449121558082299511922264467487830030034724064617938087423281031413882176754860693894483846499540468134593781750054962789161126622627130265504658138267133647055095054090169497160342023733520249877513, 290555083887040, 7744170896184572928367605492308398962918322100044047392462223627950619324256281460698045561057973222631771548675776970105160303446211040320174464033006040736141232069114438, 7744170895847154393776865763597799111252415208201536270500323368881330808072369953608466525815805349562628431779790050464863029844248802643403308008742721507211093630483014, 
    158755158233536, 14892230037610365927376964827022806198444545536537706258966878375343996092944422490223168176748225220020785526260571049830094962057719048816409562930418283300566774607447811980130789862987282209044813119253013551559040316192556249112750570399869391864840749871112, 469686358631619202126767564541658546003566768368157574066152597399496376710451263232788417363529609707118410171656917531924986728451347071504887149950995651710994469416465168305238738050344702897700148977332629094962440079502422184589726997394624635502864249877513, 961549145396301712888233932915903532238216493621725906621316756328618737719485750390829676222672359549440302807698076025655867830242294996651479446297983230112471907445835401336144371525546338198993420017333825986585444205056903135984877987795219263799722256249877513]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 103) (cur' := ⟨4, 126, ⟨2, [], 0, [1, 0, 1]⟩⟩) (prev' := [⟨3, 127, ⟨1, [], 0, [0, 1]⟩⟩, ⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_5_0
  · exact tv_b11_5_1
  · exact tv_b11_5_2
  · exact tv_b11_5_3
  · exact tv_b11_5_4
  · exact tv_b11_5_5
  · exact tv_b11_5_6
  · exact tv_b11_5_7
  · exact tv_b11_5_8
  · exact tv_b11_5_9
  · exact tv_b11_5_10
  · exact tv_b11_5_11
  · exact tv_b11_5_12
  · exact tv_b11_5_13
  · exact tv_b11_5_14
  · exact tv_b11_5_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144a49249249208049249249249240a49249249208029249a4924820124934d249059205248308201648049249249249261041249249249a4904924924d24d000049a49a69ec9209249041a6324820514924924924820124964936c0002492c9249249049259249241009249249248200a4926924920804924d249241009941249249249249060249249249841049249249249209249249269241249249249860249249249241809249249248301248249249249208049249249249240944a2924924924904024904d208059204201349241648029249a49248201349349a6800026924924926904924d249241005948a4924d249241009140a49249249208049249a49241009249249248241249249a49a61009249249249249040249249200059208009049241048029249a49248201249369249040249249249209049b6db6db6d86024924924d24924100904104000124820005924904120135934d34900004924924924c30124934924904024925124924d20924934924904024d24d24924100924120824824904924000100924012924820920924124900034824902820924920924100034934824904920820824900534c30820924004904104004104510524820820924824920804024904920000804920924000100924020924924124820824904024900004924904920000924920924020924924104810824d24904120104924920104112404934924524934d249860149308208349a0924820920d241348000201248249800248249005148a4924924904104926924924924114924d24926180924924d34000124820820926814920000804920412d249349240000b49249249841024a2d349249241040940001041241240841249048049020a24b4f249249041028b4f24924984102522484924d34936180924934924d860249249249241041249a4924924904924d24924d000049249208249209249040201248204a4db4d24d000069a4924920820925966936104124924924924834f24924904104d369b6924104134f24d24900004900004100004100824920920920105960000124124924824924804920820804930924820920924124c000201248349000248249069a41049049209a6d041241268269249a48308304061041248208179bdb259049609205a4820820124c169200008049208841249049249041241241249241a4904120020810104d249208200001041341041e730c1641348144105129249249248201a49269249249049249249248200a4926924920804924d24924100934d041361648149200008059201124a4924924904104924d24d24924134d34924904014924d24924100924d349240001248208209248149200008049204124a4924924920804924924920c209249249249241249249249248249249249208029249a4924820124934924904024482494924924924100924924924104124924924924824924924924904924924924100524934924904024924924930c044909249249248201249249249249025148a4924924924d20904134c20934810004924924920124924924904102924924924924094544924924924814924924924d20924924d341040209249241248100049249249204249269249208049249269b0c209249249249a41249249249348124a29249249249348244849249249241009249259341041249249249248249249249249024945249249249249044909a49a4924820124926924924824924924924904934db6d269b4c24924924d34924920924934c00104820024124904d200a69269249208049249a4924d209249249249a4126db6db6db6db0924924924924934824104100024d30800134924904804924d24924100964924924934824924924924924924904020924104924100024924924900492124934934d34c00024924d25135120924934d34986024924d3492418092492492683033adb6db6f4ac24924d349c4909a6c30d20d240924104104934014924924d24920000924924924104124924924934824924924924904924d24d26180924934924906024924924920c04920524924924800024924924904104924924924920924924924924125924d25924824964db4964920924924924906014400024800020804124904904900000900004920124924124924024d34d249208029349249269240928a4934db4da49025200041049041029041241209240849249249200009249249249248125149249249249205241009208208205248248201248108929ac93493cc300a2db6924926c300a48921b6db6db6d86026db6db6db6180db7964d340001a69249a6c00024924924d841069a49269b0820d26d34d36924124d359659668201248129a49a4d349241a69249a4820838db4db6db6d849249269249219bc96496cc301659bcd3496cc301648040049249240209248248248301001a493490492492092492009241492596596c300924924924104134925925145834924d34da490492452493496598601082082082c9a08209209259240000600201248000040248249009289249240000a49a49249041024a289c9a4924920820000924905924084124924864902124964964f0c024924924904104924924924d20924924926924094924924936104114d34924d26d30a26924b24f2c020820820b268100008008049204249a4924d000029249269341040a49249249249024a25249249a49248224824944a0006926b2cb00000924924904000304a2792480006492492490492471c9204001a49ac32c0041249249049000061269e4920105924926924094917b144105249249249040249249249041049249249249209249249249241249147040209a692480412092482490c9300389e49209240049249240249a4d259208029249249249240928a25a6924924820860004d241249039241249209240849249249241005249249249248139249249361041145369a492692490c1049249249207249049249248109a6924924c300a4924924924902d24924d24924092db49349348300b4d249349249049249269a4920892114512892424e34924920000936d249249040249249200049249259209041249249648049249a4924100925965b6630c144d36d24934834d24d359a6904924920824824925920b3c9b6926b2400010012492480c166124b2cd009b8d36d24c00024db49a49241009b4d2492492482492492412492492490402496596d98c304d34d34924920924924d369a41249349249241009249208269a492c904304d84936b240249249200049249249000009b6926800000167124924800006d24820c049249259209041249249048000269a49200041059349249200001a4900820124924964802926934d248000249a4d24924100924924800134d24934024104d24924d20124926924904024924d269061849249a4924d20d249349a49b4134934d26906184924d349a4186124820930924934830004004924d20c269a49a4d40c30924924924934826d34924924920924924904924d24924100924924924186124924924934824924924926904d249249a49b4124924924934824924934926904924920924924800134924924004126da6906980004db4924d201049b69a49b4134d24934c24104d249241201049a49241a6124934924934824926904926904d24924920124944d34d860249249c4904104d34934d34100924926926924134934d34d86024924d34930000934934d34d880679e5934d00004925124d382009a6924924c30306f0cf38d8602490410400490c1bc33ce3618010410410010402492b1a69b10049249249208209249349249a41a6924924924824924924920820924924924820824904964134d34904020820d35924104924d34920000925964d2c000134924924944c24924924900004d24925124d20964d249249348269a49269249051249251251419e79e6dbc18612492494493482a9a492692a984920925934d34000124924924820824924934d04106924924924920924924924924834d2496492490c9a492692492192492432c9145041b4db6d86800034d34da0004106936e34d30000d24d36c301a49a69a6800064d34d04000824924920920000924d34104020924924924824924934904108d38a36220000d34d36124104224a29134c208349351b4d08938e34920001934d34c44020924924824804124934d249008249209249209259249240149a4d249349205248308209248208209249209040008208249209248249248240a0820924920902820824924824124d30820824920484920820824920924820920924124800020134824900004824902820924924904100034934924904534134d44920002524904124124810524800144134814920000804d208208249248240001049041048249209249209041041249241208208249248240a0820924920904104124924120936c00020124814124820820924824920834824904920000804920924000100924020924924904020824934924100004924924920000924924924020924924924810824d24924100104924924c30112420824924924900004d249249208208249249240001309249248144a29244828209a4924924000134924934820820924926904100d208249205948a49140a08269249249000049249349208208249249a40001309249248249249249028209a4924924000104134d24820820924926900004004934d209a4924924112482524904124134814920000804d20820824924824180020c20da48249209249209048208249248240a0820924920904934c20820924812124820820924814920000804920484124924904904924d24d24924114000d351241241249041241248124124a0820924920900824924104120924924924824124924924904820820924920902820824924824104104924904826920000806920482494104924924920104924d24124124924924924824924924924904104924924100504134924924830824924934d044908209249249240001041249348208209249249000040049249205148a4912000020820924804124904824900000800804920104124120924094514912420826924924900824924904d209248249249a41248248201348124a2924484104924924920104924120924124904924924824904904024902494524490820924924924000134d24d24820820924924900004c249249209249249240a0824924924900004104d24d3082082492492400010012493482692492490410412492412000082092492410410492490480002002492490492492492049208, 1161224003915968, 1134704867147841, 316668216082497, 1161226152317120, 1161226152317120, 176076618731712, 
    286027789898688, 145290293153984, 145290293153984, 145277408252096, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 721438697853632, 567489873318080, 567489873318080, 567489873318080, 
    176076617814208, 176076617814208, 75815711701953, 79251551291457, 79251551291457, 88047375878209, 
    75815711701953, 79251551291457, 79251551291457, 88047375878209, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 1161223934644416, 1130448420344257, 1161223934644416, 176063737500097, 
    105707804364992, 324403033980877376724792265494057886010407732018087535292715172116177671346562732714989721940666500, 105707804364992, 565304150201024, 565304150201024, 563105126945472, 
    567503173456576, 580697312989888, 580697312989888, 580697312989888, 105707804364992, 105707875733696, 
    105707804364992, 513258889805605223322660477602494454131821906417436425401954131678589188043617615869024416369775915524836131041587477539724146942973341322231844948095281765125775685548614, 105707804364992, 150958497008678147900342096783323651760374258554442482869308600899621325748552629907475280140323260605753139019145061334051369936521687823288664909265913570772532619226694, 513258889784516564910739244558081963402702725677279480281182334527220246357053258615938065774926797822529802323224436913058772031776564043128562108981036355347293772151366, 105707804364992, 
    563105126945472, 565304150201024, 565304150201024, 563105126945472, 567503173456576, 580697312989888, 
    580697312989888, 580697312989888, 1134850761429953, 1130452714918849, 1128665941819969, 1128665941819969, 
    431159164015040, 3957318030735326623977467098143893436221372734628537056023189273985612203448364188614295704988074761134951721014452164602277256034414089925139682768283701111557228183337008710, 531501997402235371604541297741964151506216033423070360103893110266016177980798396564002092520869982277, 580697052943296, 1128665941819969, 1128665941819969, 
    1128665941819969, 1161234884202944, 1161234883940800, 1139244651778496, 2928712330767010603405032701554041134169840681795, 105624529012801, 
    105624529012801, 176061992669633, 1161234884202944, 1161234884202944, 457547442557376, 2928712374323320047938246037930230725566697834307, 
    316937188417857, 105624529012801, 105624529012801, 176061992669633, 105639091177537, 143087117537728, 
    143087117537728, 145286140793280, 565716458684993, 565716458684993, 426761117503936, 431159164015040, 
    2926582546989799708388883299025645080215080227650, 2923906457565976033611899012832927276834362577730, 426765412471744, 105639091177537, 105639091177537, 105639091177537, 
    426761117503936, 426761117503936, 456741910946662225458538074884174806672027439938, 431159164015040, 565716458684993, 565716458684993, 
    426761117503936, 426761117503936, 431159164015040, 431159164015040, 1130440241976000, 145277823488704, 
    145277823488704, 567503173456576, 567503173456576, 531502187482143476356237171037180367409888194274759943660699032364826606309462253195201734780861944132, 145295007552192, 708244960973504, 
    708244960973504, 567503173456576, 567503173456576, 145277823488704, 145277823488704, 162887193596608, 
    162887193596608, 580697312989888, 580697312989888, 149693054063552, 571901219967936, 162887193596608, 
    580697312989888, 162887193596608, 580697312989888, 88064621873217, 1591594326637577600647941483606635186317604045925679886301118391049474428870400935549834564511388548476471017792702479516761007046092988263064621488110822964193771877505840627966285309198677474975277954962986907567267359818174444355674349064145188908657819656246197512, 1591594326637577600631662151495112104592011274040546679571523390270932411359645637650370532973769069291060295925456982066739779604126980148806151653729421148863442381691393164912185698939335874002224392442206515330754037232651716908419367728835335144867905544246197512, 
    1591594326637577600631662151495112104592011274040546679571523390270932411359645637650370532973769069291060295925456982066739779604126980148806151653729421148863442381691393164912185698939335874002224392442206515330754037232651716908419367728835335144867905544246197512, 88614378228289, 88064621873217, 88064621873217, 88614378162753, 158489281303232, 
    294824566592448, 563534614774337, 581126800818753, 72670922213441, 283777154746433, 283777154746433, 
    72670922213441, 72670922213441, 72670922213441, 283777154746433, 123685552124668716964593401259976672143884867360692665728364351358132232992228045026131486171641770218893403051252267765652686889450805906844254441444425492297947509178710086, 283777154746433, 
    72670922213441, 531502187482137811533747440811209723809112975222517406794007534883014172457120404713992090352425243716, 531502187482137811533747440811209722209682545506305133819377489437269481613901143318152438129328002116, 567503173456576, 567503173456576, 708244960973504, 
    567507468423872, 571901219967936, 571901219967936, 158488727654592, 532215620711611644107079985924085209306506344382539751160664147184823426042957778928780812297015829380, 3958161982852239929516173254380978619403138834309758787311036041731953396395882442808937794839305503546873831886611898929396335836668657856524391753623316717829471453526850118, 
    316934772236609, 316943362171201, 290417238085824, 435552772952256, 290417238085824, 72671391975489, 
    72671391975489, 735038153264170279741148017101846260697687757378, 563534614774337, 581126800818753]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨1, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x14a249b69249a60001249a4924d30100934934926000138d24924804034d24da4980804804124100120904000000024138d24924804004d20da0800100526926da4d26980804924924924980004d34924926020104d24934c00024120900000904d348048200240149a69a49c6000134d249349840269a69269b0804924d34004924924d300008249b6da412002092c936900494d349249241009a49a69b4000134d34924934c36d2792c9b0c04924934104924924d200008269b09a4134d04924934c30c0002c9b6d005269a6926d00004da69b4b26c20124924d04124924934c00020926c26904c20804b26da40209a4924920804004d340000008249a49249a6000d34d34d860249269a0824924926980004134db4d208248249249a610c000164a368040041241009208000000008001001049248040000201208001040009249a6c00124004924d349200009349209ac1001049249348000040249a6900004924d349400019cd9c6db6120520920900021b00004924d04160c048348200241200241269a0804900024924826b04c009249269a4000124934d24c000673671b6d848049249349349a60201249269249a60001249a5926980804904924d300009208240000241241a012080090092493594d9b6000125364f66d8000493593d9b60001a6b29b36c00024f64d66d000049040000000341b0f31b36c00024c04100100c06c3cc6cc30000144d291b4db7580004924904104134c00c04da4126980804834d259ed9eda48060125920920027180180c36c36c30180902924934934c201b6db6db6c30c36db6db6d86206db6db6db0c309249391bcdb8d80006db6db6db0c301069049649a4100104d269248000300241269800000059289a00a4924924924100924924924924824924924925000024930824824924d308248249b69a410012012c9b69009b6db6db6c30c269b6d24d3698cf36dbdb36db09369a69249800049361a49a49349a4186186136db4c00820b249a69000080059b6da0124924924904026926926980005145524924d209a69a4926820136db6db6d86184d34d34d30c20db6db6db6208124820920924934c31031026db6d84001800b271b40269a6924d00004934924946186134934e369a60001b6db6db6c410249069a6934d36906104104da6db0800100124a348049041241001209041049248040208249269a63041009049a68200201048001040248209249269ac1000241249a6904904924d34930dc198d9c6db6120806321b36da0830c20c36da600000482ce368201049049b6924106120d36d80000024126d84800834824e36d201b6924936924186106126d27800026b26db6e0000c004e349a09b89249b69281b6f21b36da6824124904904024826820900020b051241249201209a4824820024136d86180180c04134130034100db6db6006c381249041341359350201a41a6db6d84b269249b69b402012090000490c82482c0000201471e636766d981820804d461808040000008201b6db6c00187024104104944960800300326d24820d241a6e36d86dbc86cdc69a01069049b8da4100528924926934c040369a4da6d800049349a4d20100da69349e6020124924934c00026da49a6d80004d34d34d200019e6d369b6000020104800004820000000000804d34d300201000040300000040149a49b69349b60201a49ac9249b8000136db4da7180804134924d0000080082400002013c930da00009005249249348040369a49269800049a69349a6020124924904d04134800000c24da69800040309249a6000012492826924924820000104806004c20924924926900036d87186180984d24136c30c26104d24926d309a01449249241008209249249a6000187136db60209209249269063000079b8db0030104820000006db6da61800001849349a0c301b69a8d86c301269240611d6dc61860001349a6934800030da6db6800004134904d30030000f44db4010d341249041001a49a698c000004124d24934c07906e2c900c049249014479db187584104924924d200008269b69a0104104d24934c2180002c936d00124924d249269808049249a4924980004926934926020124124934c00024820900000904906834820024024925965b66d80004938d399b6000124d64f66d800069aca6ce300009369b79b4000124100000000906c3cc6ce300009300000040201b0f31b39000004d34d34924104134d000001b69069b6000126b24926d800009249249248249349b6006030db0db0c060240a4924925920806db6db6db0db09a6da69341a61b6db6dc6db6c24a26924936820124db6db6dc6db6c061241259269840041249a6920800000160a248049349369249b60201249ac9249b6000126db4da7180804d34924d3000080082400002412c130da00009004a6db6db6db0c30b24924906124124926906184184db4d30000b049269a40003001649b68029a6924924820124934924db6984d249349a6da0806db6db6db6db09341869049349a418410c136934c20004004928d20124024930026904186db6db6db6124924c209209249348041a09a6da6900004004924d3010d000b24db402018c860e36820c308009b69b0000120836dac824184824db63009061a4124da49061840049b4960000d86936dac000180134d24826da4926da4a06dbc86ce369a0902824824800124320904924980804860820136d0402c9309a0000906db6db6db01b0904106124925830c20c36da6f000040069249208349249b69261b6f21b3cda68240149c6924926000126da4d249a08049bcdb6db6d860249a69349248201241349a4924100000824820024120024120980900924934924c201249a6934c30c289a92249049069a6926b30d209a49b6db6db6c30c26926926980006100934820da41001309801b48000271a4900b01829a34100d201371a6926b000049b69b49268201379a4d24936986f36db6f31030924904936d24934800c26a24d861840209b89249a6024924d26980804926a24db0c309a69c69241ac1249a49a6db4826d2c9861b6db6db6d84004d26006d208609a6d001348049249341049a49241200009249a8800104130924904800024d26a208049a4924d300009349a61200001008361000000271a4906b000000341001009a49b69a4120824d269b09000041202240008209c6925a2c000000d30804026d2c9b69004949249249241009249b69a6186144d34924904824936934db09049249249248201249269a49249208048309241809a4100020926826900924924934820124924d24820c269b6924e069089a69a69a09a09a6924926da4820c34db6da698000492c9e69208609009248009a4104126da0124c20820826020800000926d80920124934924904034924926980005134d24924d209249a49a6820134d24934c24924926d80004924b34b208309a49a49b61841a692492c9248371b6db6db6d86dacb2492db249209a6924a2c9248061b6db6db6d841049368069b08000249200248028a49241049249241200009249a698c1041049249048000249269a6904924924d200009249b6100000120c24d218000269a6d861800069261b69209a69349241041249249048000249269808041049249249208209249a4820134d24934c000249271209000049309048600009ac9a99ac000324820324836dac9349005251249249800049349249268201249269a4924920804904d24924904000020920980904800924826024024924924d20804924d349208309a69b69361241a693ae26826826db6db6db0c409249249a69208309249a49a6000124b2c9a48218040249200269041041868069300000009000200000001340248049349a49c4000124d36da4d20804d34924124124924d20030a2693818610083cda4da69809249249a6020124936d24820c26936da4986904924db4924920db6db6db6db61b6db6db6db8c36db6db6db6d86db6db6db6db0b24924b649248269b6dac9b0804924926924920186db6db6db61041061a01a4c200000048009200a44a29041249249048000249269a63041041249241200009249a69a4124924934800024926d84800004c309348600019e69361a60001b6d04da4826924d249028209249c48240001208249218208659249e6b0000492092c9209b6b64d24024924924920806db61b6d80c30aa68249248241b6d86db6d86c24d24924924100924904d24924904024204920c04d20860904934134804924da4924100924c369a0186144d07124834844d00184186104d86dc6c019b8134db6c36db01861b6d86d34000000060306180184804924004d20800984c009a6104124130d0580012c9b0c069009248249248201b4d249340000289a0924926904d34124d24100820104924134c249249a6134924934c000249301a6006185134134d00c60d34c06d06da4020930924934c061b61b10375808040241041301869849469a6164c30c00db6db6020026930036d860051008001a40249249a0824924920900004924d44000820924924824000124935104024924926900004924e308000008041b6800000105136031800030db0c00804d34da4d20820924924824000124934c04020824924926904104924d241009249249a6000124938d048000209001a0000004144d3d16000004cc0402013c964db6804924024100920924000006820144d00924804024930034d809041869249a6120134124d35164024820924926180100024924986804904924d300009209a01208049009248048001241248000009040269800242009089a0000820020104924980d24030d26d30100004024926030800c249a4c06930924924900800106136d201b0000020826026000000db4c00020920800000804034c00000020804920000020100124900904024834920900000805134004920120924804820020106de73671b7000c049a4d30900206db6dc61c0124904124134000036da49a6da6c040349249b63000249209000009849200000240009a48200060201a690012c8048061b0000180180c3c864d041800009b6d80d80040db8db01b0c24104d34904000800030c20004830c249a6020000824001b20020004934980d261a69001ac804802000834960920000134d00136c000061a4126980006c34100db09249469b60a41048241209200009a48069a410410492480400002612c9869049249349200008241009a40001b1100036c000268001a6900000c04180da09249369ac104120904824800020900820904104104920120820804820026136d24934800020920106980004d44020d40000924906030000130024834834da49249000041a4904920000db6800920000120924934c000261ac986c04924d349300000019b0db60003399801b0c0000618cdb7180006c3c000f3194d9b6d341205251209000248049348048201261200249269a0900004924d641209000249249a0984820924926826000124934d048200201208049048249201200049049200200241009a68209000241a6934a20806820c44824c04000904124924020804004da4806c000000209009a800003693400482482002002010092082400082c124b0c800b05804934000000024124d301a0c009040019cda58006134920004104d341600009369b6008100024926da0b00924804820026124800800900026936924980804924d24920120db6e36db6036031229130104020826d26030206904136920100c209b01a0800980000d2080012082092498080002096c864800824924d269201200a0824121900900004d24004f60820c28904020000240d0c034c24924e26a00004124984930000e048001860001e4d26d34c0006992c980d04924db4d60480020924826900004c24000db0000b249269a400034c964836824924926b028209048241a6000130900834020834924d80800004d20920d20d369349240001049241248000269a0024800005134924d300002068201b0124924d24c00060306036d8000d266006c30001186006d860001c0f0003cc653671b4d0280, 1161155215167680, 1161155416494272, 1161155215167680, 97052951994695319398814934404883112480695392066, 105624522264768, 317005641093568, 
    105624522264768, 15015491880075510186898946866980240133138633850871926095099288191923415731983681695637612608616657831272039420191083181679602521812897554533972715096279627719302863274910334528551209802459606660012359524989608972905859821883166561837654602186681055612764168245997512, 3957316615499469982613701026949970134706107163677637049482056031673668179493822684662937313670739005730673944106189473697454408072584700007541359263651444110953419189037215302, 1161292658380992, 4217239466888111472081033948911911090723115095701422148294400255968512562053252437724562309733696388, 869984056672615977916084678938091954347359896361437496532782265934476080496272031877953766540456510340, 
    338482122661285688195662983179639853183876869822911406399565008553369461268663805669337954144093488004, 736460179664830126306997170297233696473661592387, 1161292658446528, 4217239466888111472083012365311614297905860015578807091210244425301422783690334930106508750272873348, 869984056672615977916084678938091954347359896361437496532782265934476111856697846727155354866481906564, 869984048783557585818182782961577136704415037014297558188423530267698427841433019237457917450593256324, 
    736460179664830126306997170297233977949712044867, 2928712330767010603405032701554040008746677064514, 105624528753088, 387374385467840, 531566878008451233214018804595757111584413080691598135607677833726825052702266985334622990065847255940, 519551737206768539845371963960358868861511854413975519386190453845460028174387355613251880255077572, 
    583925463686802920756302398407720731955998245297226165024213550582766202937391601720926326509911236, 523099895412083056702840543082620617654604548860040302178486015590414799433155049629228491729542340, 1134842306105793, 1128247450948545, 1130448420344257, 1139244781810113, 
    1139244647584193, 519108211629617864126928102893067682170168214688142375658358707034396340051667011478302552002872196, 583988817845715522282548277057316118034242066726001551816895432248113847622710215999529601363035012, 584432337618311376975107105251316735604525171917081014993297262500517205061115854733005836317574020, 616365761228219484123654826578024136089869414397355209731563686758358176944482015259143044381229956, 797771997395037670914329805378565143967467438717830736752006091371049693027090085808764992451671180164, 
    1134842306105793, 1161155215167680, 1161155416494272, 1161155215167680, 97052951994695643918606532870895275911615092546, 105624522264768, 
    7759266745547319253286405420057648018064745132688693403369457741039117005247691238538972162655508311768991198030199349566474206610201077150443885937990064658116026988198470, 317005641093568, 105624522264768, 3958161982852239929516173254380978619403184182708940979088042399895683726564489886850217773548526528601798354751521522725675108156164356545373052867311579859901346078068275782, 537795352846196041671505821657877172492377355633971245512669409794201748010818051808117631629679180421, 1161292658380992, 
    537795352846196041671505821657667532046277022203406536563453042373247388385426969689363383839442909829, 2141060021566760805619958339863162448647961151603781882358819279201296727536136810457312274011428037, 548111488095409560198014945598504422642712341342042183063808410423041622354137148464903497186088996677, 531502052904088552333204831556982386178563819770374328137867514341477674637004020465542227209570635589, 483126158547075540575865916427061310057260709485834365906897126517371747867208475420517810347536851250177418892427732153096886690730229984434868890004742606578233391406662, 188398111017150352190319398145544176944581464642, 
    188398111017150352190358084509641608026554126914, 16609561973137537182290751526316306357249402635669633828242213621854882748109377371988426733597904709, 17127037648015850766510413492928138475756066626, 176063737500097, 457547572588993, 457547438363073, 
    316805655040449, 1161292658380992, 1161296953413824, 188397414124184667727311679710653564572529603394, 1134835863654849, 1128238861013953, 
    2928713681008605949141658853330486082307734132547, 537795352846196041671505821419725513050022113918006256636331319153897868567532409491733362410583538309, 6935395655930469910398077417638322420772058911600190443821750500073242595414486298536113088858973347865251676513714855550417875589189410695042657330869046231556095516885352006, 17127037646852466605837501641345280452558082626, 90575098211533486263658875835525405512541319067890695926653018156550426850861679026810345565233135285358199719712218660637232426639224126765015218074364636911909553352263, 513259132768038800474175964706704692215687323335298469485210754465879468935606785420924542234847811458899275547115097480239174019740302872273230198262040296895811759156807, 
    532345381924043839394585483492734856052147205937440450685197304721294747070572883139296921764510087813, 371085815683523277197194658829025044817323774786, 30946492127316258178995131472793951164346851918616230180733066051849813369939930762591126683372422025110814904606259131431850798792250838734279696914960171927875273599921735, 1161226082193600, 1161226082193600, 106107236782272, 
    1134833716171201, 1128258188366785, 1134833716171201, 1134833716171201, 106107236782272, 316797065105857, 
    316797065105857, 106107236782272, 106107236782272, 145277823488704, 145277823488704, 145277823488704, 
    162870009533120, 283815873351872, 143078800233152, 158471963022016, 158471963022016, 1161226082193600, 
    106107236782272, 106107236782272, 1134838011138497, 1128258188366785, 1134838011138497, 106107236782272, 
    106107236782272, 106107236782272, 140879776977600, 140879776977600, 145277823488704, 145277823488704, 
    158471963022016, 162870009533120, 563504558904000, 563504558904000, 581096744948416, 143078800233152, 
    149675870000064, 158471963022016, 1161299100831936, 1134846601073089, 2923059026696273228925333169803710908365287774019, 17127037648025586360258367473293041403347081026, 
    324403033980877376724785785085323545110961549440855704299366436025978546393480695531479105150401732, 537795352846196041671505821660602499680249709454013166493886347446902241577876489088454820390944946821, 833535301821033078197094502345517333207618458434, 290279929155776, 290279929155776, 290279929155776, 
    159026152215232, 105905851208128, 513258889805605223322660477602494454160133474203318410536949208382254794632262244623805168739871730798989614250025695078792301778777783926248329251854758587650674129862214, 583925464646046181219545853813918507147474569568530087588209965726488176576428642043216195018078853, 563508853871296, 290279660720320, 
    105776662253760, 105639084888256, 105639286214848, 105639084888256, 105707804430528, 105707804430528, 
    291962730389430358255065549124031663228198513391666585210269762670011608764689567846058101418769604, 583925458845267951735947601712544179192701984263859588437597962168765231393740139538404500113212292, 324403033980877376726543988373962108531692698033287685333191247561185241818254673125086616503991492, 105639084888256, 105639286214848, 105639084888256, 
    105707804430528, 105707804430528, 513258889805605223322660477602506362659528382209838204432578318469912044314247578986744369859336859764078554732393325677877245362109370427546690416596173326736047174842438, 513258889805605223322660477602506362728372384382655120168340072357821676781195023537628929459970438611007642802737029571496279562130169495327505499692029694511278716876870, 106120323010752, 106120121684160, 
    105707804430528, 106120121684160, 51381112941740212778304580556473372804732950338, 176145272279232, 176145272344768, 4217239466888111472081253880099224491962888354275469193042410039182227694763087095839838833444406148, 
    4217239466888111472081034056038230129802841229091888451979691008022887473209959728082473090029994884, 531501957804189230382695363707091504638436981970408045837009817090119485326478668119180513805175372996, 708790421820096, 188398111013183097736753796800123847113340621378, 188398111011853864670441428978660688019264115266, 299084620501952, 
    833535301821043462830425653257906562997048873794, 565716467061440, 565716198625984, 565716467061440, 565716467061440, 565716198625984, 
    565716467061440, 563517443805888, 567915490316992, 567915221881536, 567915490316992, 581109629850304, 
    581109361414848, 581109629850304, 563517443805888, 581109629850304, 581109361414848, 581109629850304, 
    581109629850304, 581109629850304, 1134850895647681, 1134850896040897, 143078384996544, 143645740110528, 
    870568038588502396666659898542722388349060930763277150772642055257861313429839524216260137793380795268, 143645740110528, 1134850895647681, 143078384996544, 1128253825881025, 1128253893399489, 
    498163040083692684825827049565582885655953330916193946101899920490904830069334416145458734400311057629101003683079601067162841362053651796356284287895985654190700022947398, 159038902899392, 159039037117120, 158488727654592, 299359766844352, 105639084888256, 
    105639286214848, 105639084888256, 105707875733696, 105707804430528, 105707804430528, 513258889805605223322660477602494454133516007600563610155242053940535953614464459835875004739229979226393827836450129699057630616683851383337703256382498641456577606811206, 
    105776662384832, 105639084888256, 105639084888256, 105639084888256, 105639286214848, 105639084888256, 
    484010680990405960825093326566560644588228667926695128786694218193218071290817090404580864935830656744855649046492173522340431926973620020400479665830377840858790405037638, 513258889784516564910739244558070054945096271426815236933093297158619012129480773659182405687098127426031234147168046107910986637920701112802245304515891852389946268540486, 583925464646046181219545844170453424094357176034536339325071427934404704660406257081414283568396933, 176076617814208, 3957769494675932387296373331950072729104347818216540865706960547824497319576178570660356181419647957040451631021624930102353447798972899406375847214833708456051224114634907206, 105639084888256, 
    105639286214848, 105639084888256, 105707804430528, 28545062765785879917034395110138928214730348354, 105707804430528, 150958497008678147900342096783323651766030504731438431058007711295363176669167158252246475347853331940020225887278227679140489338167535114433751832751559823489865006558790, 
    513258889784516564910739244558081963442372697326242275744056435399474695206276432053100221528678347866002801369829871187394638309894583038823188293100336519314966681975366, 106120323010752, 106120121684160, 105639084888256, 28545672530851981443160682100743757219959412546, 105639084888256, 
    105707804430528, 106120121684160, 246514016456896, 246514016522432, 176145272279232, 4090643159813280760437425141056665775805359973477781171211225668032900472958380302676410270947520362390172515357697958342549161616283769246413904190057240936252636239964926535, 
    163432654443200, 145840468398784, 163432654443200, 163432654443200, 163432654443200, 246514016456896, 
    188398111013183097815981959314676415083036283458, 188398111011853864749708277267019380329034027586, 290563942257600, 16609561973137537182290751526316306357249402635669633828242213621854901398914293888016219049585692485, 2077193653402100029587205108054967324915818600624529664368124952569032082271038316973793253553265093, 563517443805888, 
    563517175370432, 563516906934976, 563517443805888, 563517443805888, 563516906934976, 563517443805888, 
    565716467061440, 565716198625984, 565716467061440, 565716467061440, 565716198625984, 565716467061440, 
    563517443805888, 563517443805888, 563517443805888, 567915490316992, 567915221881536, 567915490316992, 
    581109629850304, 581109361414848, 581109629850304, 563517443805888, 563517175370432, 563517443805888, 
    563517443805888, 581109629850304, 581109361414848, 581109629850304, 145290293153984, 1134850761429953, 
    531621557660250733138761542221330899994272767628772113165815378618315257282236965432384884275431187141, 1152443081954241, 1134850895647681, 1134850896040897, 519108211629617864128245490578488554047386157558718454404317703956745085092249700551172199989658500, 3958011028271135025048524738931952261246208698685396720862443343978236992350333947859521507303500771111089321898802123573721585276353981078822973629010044633122973801156402758, 
    1130452714918849, 1139249076646849, 1139248942420929, 1134850895647681, 1128253825881025, 1128253893399489, 
    1143646988669889, 145840468398784, 1130452849136577, 145840468398784, 708794716787392, 2923728070660200336199320681031687754952082543427]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149249249a49249301009249249248248349b4934d80c048049241009209249349248248205249249249b69a4924124124904924c208248124a4924924924100924924924924824964934944000124936db49371b0c04104924924920924904924924820936db4d36d80c04db6db6db6db6126da49351208049249041249249268248209a4924920c040040048208208249249249240009049241248200069a6826db0924980236e38db6c20824924924d000241a490492082482492492410c800924d24804824924100920924924924824824934934000934124004924934920924904924924806184900000c00004d249449309209249241249310049049249b6824924d24020904924124824804924924924924d30180926924d24104124934934834c24924934904904104820800000926924104124124924934904900524924924924934c06024924d24920920904904820020824812494d369a4920000924924924104134db7944800024924924d34904d249249300009259349a4930000924db4d24c40c34da49249041000009208249a0104924920924104004904024900534dc5934c00024d24d34d210209a49a4d24104124924924820824964d36924c00024924d34920820924924924104000024820926824836db79b6d80c04d24934da4d34d00004d34924d34104104024100004d04d24924104124100004820804120100924104924000004020124804024904104900c049200049209200049a0004130104924100924000184c201040041049040249000048208049209205249a4924820924824984936800104c26124130824920d249241041240009348201248248104927249249249049041248208248128a4824824924820000124826824820924924924904b04924026c2082c10492492c9a0920104924d24920820924924924120920924924904092092524924924924924924820824812534d34d66d800049249269a6924d841049a4da4936124104d26924c000209a69041849048249a49361240149249a5924124124924924924d24920820920924924924124124924924924924924104124104924924904000024104104104124924924920924904d24924906024124d24924920004924d24924104024820924824120920804920812412492524924924904104924924924924124926da4924920c04904d24924906004124924904904924924924124024934d34900c04924924d24124124934da4924904104900004104904d04d24924124124104924924924124124924920920924924db6db6db6db6124924124924904124924906800024924924104104124d241a0000924924924124924926824824924924920c049241249008209a48249249a41249849a6d24824924904d249249060241049208049208001249241248049349a49a0000924d049260208240009041241641269b4124900820900034100006180004820820820820924820024820924b24924820124904924020824920924924904924124934920820924924126824924924134c249a6c060249201269b4920800024800026820004134104d041009208209a0924c06006db6db6124820006926a24980000924926904000204e26d2c800034d249a49049a4a24b209249041a49b8d86800024d34da0004108938e34db0000d24d46c301a49b8da6820824924920d00004924934820820924924824000124924d248249249249048208249248240209049a402482492492492490492412493492092492492410248, 1161368023863744, 105624529012801, 183402028136003777047981896509819979927025365826, 960962161246946106552188634526707087480201830394741335189666882919984826144676576187843769675172808086375302592761204555625208029251098511684736373482917607757814436030842851127672670479768043601644481013914425904036317836267272807364644896802039305907225736246156552, 580835028767680, 589631121789888, 
    1128184905009217, 531501965722252339719151417920491632846355695692230610666282065409489895151537623558253888890803244869, 132875517170550389995170533287665926974926292182759735332294667494323924454595001720561174665300987717, 290547030823360, 708378247566272, 580835028767680, 
    299359498408896, 589631121789888, 290563673822144, 3957316619184925684297189135165343748734441777755736966890242703393197053613353795175308343941530529861781529862284377213928076087438296444621909332206400175416978829932977734, 286156768940480]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149a28b49a4924930100928924924824836db4938d80804804924100100134c361801801269249248248049000208000004a48a2d14db69a6b26020134d04124c30004d30c06006002124824300300012495134924924100d249249249248371b7a479b1002e249249b60000bcda79b6d800049389b49371b0804104924925120d24904924924806187a079800004b6dc7939180004db6db6db6c360a4da4936da0802d14d04124924944c321863601860000209a4924920804004d048000008249249249a4000d341341a4824900124904904024980234a38dc4c208249249289800441049851008248249249a4100000104c04005004924100920d04124924824800038240000002e369240009a60bd1a7980036d84004924934920944104924924808204900000800004904d44900180c371c0db01000000208208004b61c98018061848a6124930c06982d14c00826b26c26000d04124134000130c47036c02004824f30b20004924894924925130100b249a49b800012494492483482493692d900804104900c00000b069a40001a40a4926920000900925924d34964b24000334d2492c90c10410096400032432492490c10c902114922924924934c04014924924920d209b6db69261e4104904020030006db6e06d861021249243343040149649125041649060081058828a4d349349200009249a49a6000134d25934800024926926950804d34924930000895934934920000d24944d24c30834da6dac90c1000009208251200009a49b09a40800069041289009a49a6d340001a69269a49061049a6e369b69240001b6da6e26906186da6dc4d20c200009a61049a41861269a4826902134945924c00014d24d34940c309a4a26926206124944d24c30c34f64d3c90c102924924da4184164d24d24800014924d24960c309a89a6e26000000024820944c328169a8a25121020d34d34db41841a8928a34830834d34d269061089a8a29121021934d34db42041a8a289c4840812526926944840800020004120900db71b1230000db6db600c0000800049010041201009a40009a4000104020104004026900000800c049200049008900049000041200009a41809a400010402010400000690c020800004920c04960ca09809860001241a6026e001061010371c10011b0206e381809a81b80009b61801041861a6e06006100c06dc0c20d200009b618092c1a2114924944c20104024b64d0c13c902926924184da4104124000104814134120804d009a49a6000226000904020134c061b6e06036d02100924300b24014934904d00120904912424924800804804144d08028900c36dbcd891b02872cadb0e3a080524b26927b3cde680006492cda79b1831a48e3ba4806012033cc0006486492cda1831931a4824d8002e80149249249249241a6da0c30d20534d2492490410412483082481249282692492482000012400604402092492492490003cdbdb07700985124126c30c20104924920d209201049249241008209249249a412092092492490010c920984d201120a4914924d2492c90080c92492492432412400490000c90c9249249243240825249248a49249249a418411216493492c924d2c90c1049249b69241a4104d34d34c00020020000000904924924924024022924d56ee8d80004d24926b2c926d80004924e26b36020105124d44c0002032c900006904b24e2680002402c92492492080cb24924924b241149269a692492080c9a49a49249a4138924b2493682080490412c90cb24124100b24084924b2792622c125934926db6da4d86904925134931060136db81b8186104928d8cd8c3005249249a4900824924924920904924924924120924924924824124924a269048249249249309049249249241209a69a69248200a4924924920904924924924120800020104824036db6d86c00012104d24924904020000020100104124d34934d200049249249e4134904d24924904034124d24934d208069b79348241040248209348001c8e26c26904120100804d208041249209d4020020820804901836181801b40800800924024060db6c66066c11836db18079b0306db6300f36060db6c601e6c2000698c004801836db18079b08061b6100324100100024800800026d8c0249000071c180db408825249249249240241249049a48200240a4924924900904924924920120104924180a24030db6c30246c12014512524d269a49800049349a69268201249289a4924920804904d249249040000269a09869048009a6826024024928924d3080492cdb5921820924db69360241a4936da4800826db6db79b1830db6db6f363061b6db6de6c60c2db3cdbd9b0000d349b6b243041a4936d64860804020820030901b4cdbd9b1830000000900024104d359b6b36304124936da4da6904d34924124124924d20238a389b8184104936da4dac9009249a6926020124936d36800824926da4920904924db49241209249b69248241b6db6db6d86c36db6db6db0d86db6db6db61b0924926da4930904924db49261201249b79268641e6db6c36d800241349649041249249048000269a89a00041041249241200009a69a682012492494480002cb2db0480082db65b61920001b6c96db24020b6d825b6c82db2db2c9048209a6964c24020936d34804824926da4926904924db4924d209249249a40249249249208069241071200009a68249249a4124984db6984024924905124924904024104940805130800124d24144804934905980000925834b20300124904d26040024900100021904000db61b61b8100026186180906984105100000d00006d00008180004920001120180db81b01a8020924020044c20127a0500ad009249249248201a49041240400269a0924924904924134934120830d24924144c24924924134c24986c0403490010080000492012698492092402410498400002480004483080698618c904100920821130900007a07986184c06007036c46000c00f0c98c800006a060096048241a41009b40100069269a69000009a6a26800000184da6d34c000369aaa30804924db7120400066c00c36000066dbcdbc180000300c06db0000db6db6e6613cdb6de6c249041a49b8d848000249b6da0004108938a34d30000d24dc6c241a49b8dc4820824924920900004d34935030820924924824000134d251448249249289068209249248240001041240440208249249249041041349341209249249240002499b6d88c00066c0803618000c1b723cdb00001c0c00de61bd23cdb8c04920d20824100924db89a0184134c46820134834d08e04028904d34900d20020100924034c00804020026d84100000824d20804d20830db6184da4000136c20124800036e24926d00928db69040001249b6da6006104db6106db89a01841a0826dc0d20da0000db61341a41841b6d86d06904124834820104024936d86006104920db0804d20d241b89209b4134d04006020024024920db0800d20020db8184da4020934c20134830004db0824d20824986d048000049269b61a0184106136e06906906e24820947034846826d04d30004d24926900000db69a6a080001471249a4c00006da6828d84db4927130c00134d249a4004136e26906980004db4926d20104a389a4a361371349b4c00036dc4d35000826dc4d20d20000db91b41a40209471a6946836e26936900004d24100900000db6db0984000136d24824000006e24826d04d369a4d20c00134d04824004136da6906900004db4920d201049b89249b4134d2493481052482482090402496492c80c104d20100804d209241241009a402012492416482480093492413482000593490412082012410482012182490c12c904000924924a240249b4d24100004924924b0030410c036dbcc0c18490403492c80c10c924924820900800004104d0c90c100924034324104920920804100924924300304124824820134824904904020900004924925120920024d24904d208001349249348000249249289059209241b41000301249049040269041249241248041241801b6db19b61249249209a4120800c36db61b6c00186db6c66d840a4904134924904800026e24920004105134924d200001a6900820134924934864104d34924120104b349a41a6124934924934824926904928904d24924d200019b4d34c54020924934804804124938d2c900824920924d209259249b410412492490480002492c82c104104924924120000124900824124924964864104924924120104924b2432412492492493482492490492690492492592040, 1161292792533184, 2923036725949911298892420738389280604927333241410, 2923192831677887638132147941884609362220789273410, 2928723437583466907273104775285591114700208214594, 1161292654121152, 17127081202995416362877276380294988442334401090, 
    97053213332550039479209989994115152010427765570, 1161224003915968, 2923059026696937518009773799981289903537227045698, 1134979745063233, 2923371239680007010146582249151779078144723522114, 2928723437584629981769433534747762163269922460482, 
    2928715058480931516551339288382584126063012516674, 23014456840475811566738462659409634732848194371, 28545062745806169907672325878547489632074863426, 730778694767257288931108104308465983466883781186, 1461685619160685087272677725241068527100501168962, 531502187482143476377818619855298188867150774844081443105714296981722962051134229590665350278342648260, 
    531501949882260587742187610640932542974807645288718787159258359276071519261369751487658703919732362628, 531501949882260587754793200643663733273399277000704587559796742886554155369913756405635147438314098052, 2923103628706398111610211875375280288138142978626, 129777060159262446238422811503203643686845212634435217573208488514032403018124995332322383748533636, 91522640114182568184866291352428233366660256578, 129777060641716494936562169218017892090865933014533700821321902706178511329047346603174009498111364, 
    94377123929994012635075105536590570959306560322, 1464361729701953931084911194244059196936981386050, 259775872474346340734494496237376779717631190860734371120257524878508783488642358406593784689861060, 94377113721523005006921201635352348006260216642, 316934772236609, 316934772236609, 
    28545062745806169907672325878538763907796833090, 176205873820097, 316934772236609, 66437760565274650815391970859409088130775720314414130179415934863934938011945396206652517079549873540, 730845597523744101648899242963889249931787014722, 1464361729701953931084911196605242438371803992898, 
    1161296953413824, 1161296953413824, 1681702556773223372025779039082047975160891038391612539042977033474208837775768404569079043122394797140100850237884485115007088798029396053440397282844026728005092939700238775149552865029692773741342790309519539634287720156753355236124608569645971325973430280749871112, 1128376031535937, 1134973369738049, 6431345230814476999516792228354305107893828394351460477494440924272788223775181000467206029647981534065693543146551775458373198927337946106100545352832610670018958943177374278, 
    2923059037416497019607617152897935878572501706563, 1161576335872448, 1161368023863744, 2928712984111652271403116614317328186112663892802, 8369598326593329836429401746227057171012358197331121174813435619547218916551656552280963885625774981, 28545062748464960577589134621688073079947801410, 
    176347343753664, 316943093993920, 8369598326593387000979265560356319812834796094080823273449055556265727436259350854334548610697401221, 72845070704961, 143213814882625, 143213814882625, 
    6707465088747716097056592057044847211785017742511363564315519141123414899959941057390130493328243102964908091651434380531121473832008755752266682471855329528294623338969207376676567722482149883978252615812633742401017742158586657966035919839614596562391384827985797553688806415923171511683537619667224846833007263532878588042335272994681903924500581950006321056147405837244095050, 3957286482768179819956743135435490142320314616111810030344696593651721324007809315540422430692700720171346622425879243595339621018403319253173131398773377016631096842787977798, 3957287367290623150376993181293177581232188345792858320693918860941725795956629121518203157172498055509568363915677147395409831345692808024650841696544613686074759980469156422, 531501997402235843673078394370202012189031973137347305445790812637943366126795403318989555866873905284, 259538272650938341294947767169113093325635067094950858434229167130748701232626785480151989349058437, 551485156945714612346251258390801551517872774763147615065613975798769071263536993816534233129466948, 
    290548373004609, 290548373004609, 299344466026817, 1130581832774081, 1161294801604800, 1161294805864640, 
    1161294805930176, 1161294805864640, 1161569692291520, 1161294805930176, 1161569692291520, 2924486279832833090386478609973687294596365721154, 
    2923036725950410729147263372871971432190185610818, 531566814649450785643489625298385510092493004557859318314847116133985937659079788171675280056686913092, 2923103628356147504477157211758476680990587657794, 2923371238319376972717671030767872283623964065346, 2923103628186006321016687980026789377274703552066, 2923371239680506440401424884621370713351036919362, 
    2924441672897918158405180123123148278965062377026, 316934504063297, 2928712417879795969856746367469438327126602292802, 35459527352641, 176205739864513, 35459527352641, 
    316934504063297, 316934504063297, 316934504063297, 2923036725950410729147263372871971432198775545410, 2923103628356147504477157211758476680999177592386, 2923103629036712238319034138685225895862714015298, 
    2923103628696429871398095675221851288430945800770, 2923371238319376972717671030767872283632553999938, 2923103628186006321016687980026789377283293486658, 2923371239680506440401424884621370713359626853954, 2924441672897918158405180123123148278973652311618, 35459527352641, 
    176205739864513, 316934504063297, 35459527352641, 316934504063297, 1161226152317120, 25690556491297937666025632576929645307138938690, 
    72842923221313, 75041946476865, 72709640818880, 25690556491297978230709440779922386597386917698, 159021857247936, 581096744948416, 
    129777060159262431828520058003339599079716807593464332396309333901886560264650857385104672713991812, 11507272315958460350008018996701151615235658306, 129777060159262446248977371395605286642688353112934656672920049199098304328599725770586055247521412, 194641826383608102212024793110882656818963601612769409429189227582998744384142499139474125701637764, 11507283630347160471211929153906848721528689218, 25690556491297978230999582976629897599316399938, 
    1038105554919000589888667791951627596821966661058901901685911761263313477198969711967228343820609156, 145827583496896, 129777060159380794717048560242760432046740436548996701950303643225876580664257022104909383904913028, 708777536918208, 145827583496896, 163419769541312, 
    163419769541312, 163419769541312, 159021723030208, 163419769541312, 8304733559403131920742078009139868234940234453690802694763918000986057414093462084736255486688040580, 286839958148032, 
    1038105547184658891025249418612479145866196104555366580480403233355918848421222073177121105158727300, 708777536918208, 8304733930652940451719904773955361484382386172958004604853412567636686225452994373632557678799005316, 286839958148032, 66437760565274650815391973865169739335423590548883624320103924451973039400125659378058890166498102660, 568040044368576, 
    581096744948416, 2923059026696625651954756173487696723901421721410, 2923059026696625651954741628525142509099325331266, 2923059026696625651954741628525142509099325331266, 2923059026696625651954756173469249979827712169794, 2923059026696293344955809935056291273430389494594, 
    2923059026696625651954741666304074583198153054018, 2923059026696625651954741666304074583163524880194, 2923059026696293344955809935056291273430389494594, 531501949882260587742187830062401799953215849079026943354492420063848471352652912485240046385537326852, 2923059026696293344955809935056291273464749232962, 531501965722252339719151417920478735039370464156461321356592191633207068031340928061933560489470911300, 
    531501997402235843673079044447661183416441387491179182655763862949035275717492152334841279536377952132, 531501949882260587742187830062401799953215849079026943354492502752463633403916537179603088307849056004, 2923059026696625651954741666304074653531463751490, 2923059026696293344955809935056291273429584188226, 531501949882260587742187830062401799953215849079026943354492420063848473721605920162725860327895179012, 531501965722252339719151417920478735039370464156461321356592687764898039060440100656135099337607902020, 
    531501997402235843673079044447661183416441387491179182655764359080726247348230184021737631985489315716, 531501949882260587742187830062401799953215849079026943354492998884154604132196280227457220355498860292, 531501965722252339719151417920478735039370464156461321356593349273819335169729668664692027915602604868, 531501997402235843673079044447661183416441387491179182655765020589647542855880892937599746962509645700, 531501949882260587742187830062401799953215849079026943354493660393075900542305277782361555733980749572, 531501965722252339719151417920478735039370464156461321356597318973351909353992163649554569996945994564, 
    531501965722252339719151417920478735039370464156461321356597318327347103402523049418304338700698530628, 531501997402235843673079044447661183416441387491179182655768989643175315901785146432770566555400585476, 531501949882260587742187830062401799953215849079026943354497629446603666368543222165194612115178655108, 143220257333569, 72851513155905, 260282747372651161212903225843974082412994490023174186669276392053522896870299549306040994924608708, 
    513317857966736529804287377832471779733921983965610793583895691553220819577224260712032850696214019294918817351421953638824212622538308964709791017323522917614338306963526, 11596431741293626088667823016935682239608394562, 3958041289995212968397553248671716484861253594691677304115089301813983020361837037262376002833433660089762399674472941191544870033226859961555530521021390806815172719506586182, 371085799355296981772496073061743110782600663874, 265816607946957885396184671811826340294809054067532915479131228410120589165165673209793635700632208260, 562967687992000, 
    581109361414848, 2923192831677908082879018645245677068130149471042, 2923192831677908082879018645245681501377944097602, 2923103628695950885890123742910424362979013169730, 2923103628695950885890123742919674791763912954434, 145290293153984, 
    2923192831677908082879018645245686004994751337282, 23014456839084271017257434084499408995510915906, 568053067682496, 2923103628706418556357082578734046584286084108866, 568052929270464, 324403033980877365921752557461513281167436944902601627728862438440932930168388594178696663542283460, 
    324403039781655621515434535743637919327946121335631634779571525715231721160686088874719604748476868, 28545046421577633914807599363830066590957705026, 145290293153984, 172503365325760, 163432654443200, 581109629850304, 
    2141060067007134623143062694756765395406564391272087419740371142746069136989649619497116625352856772, 145290293153984, 163432654443200, 581110166721216, 158897688088768, 88528942796992, 
    12856477618929251834571839558599497324435608130, 158896682438848, 158897689071808, 158896749547712, 33218934237609691583666909999527528259666470571293752121964644840906291035155431576218026886465845829, 72860103091009, 
    143228847268673, 283966872494913, 143228847268673, 283966872494913, 6059641067476281988648990779362422469953458162361642738353269607466412728208331322813288070593838684175276740774449068859644096840650436413781789131868716417346658210154534471, 243420576405382887722894995025380542555837810346566019446622409830614862209001595961718959348012037541247245292195640377490467590535938171327851631029449606252330921150022, 
    12845283712765775040426583168491713422881305154, 12845283712765764899220799090427536795456508482, 537762904653304503692742592672783709152845711984711478500218142677326103717006464663231926074245137092, 18160195604672, 18160195473600, 551485156945714612346274229963188378808147325411661199656862361966469036036824595332359409904172100, 
    532053411279217730194373964049058433007097683354667395092969529052948274150140109329546249059323657284, 23192863482566482911253706374503938596515390275, 23549675405742972881518277866866875332711981891, 48526606687543884775186521684641575747987708738, 159038349250752, 159038483468480, 
    538541471927897675417775580661059992163428395372310219847455409113834552558254907806689567024997483204, 18159256998080, 18159122780352, 4184799132117481470136590384804912716631711481930189956367360876904346571741896068571371550359700164, 159038483468480, 18159659651264, 
    18159122780352, 18159659651264, 18160196522176, 2924084864890064517583333434774755740380458656579, 2923192831253074353992912680416568138762947663682, 2923192831677928852145680947070455492524503995202, 
    25690545772443660675905679853973299177189283650, 94198696869611080628851069788616468078128010050, 18160195735744, 581110165934784, 2923059026696480267721928393282578873446295409474, 2923036725866024222047819687789738788734275424834, 
    2923192831677928852145680947070455598078022914882, 45761303712945224195000282668839431503492420418, 145290293153984, 145290293153984, 562967687992000, 25690546282867211056771774215820401528516122434, 
    172503365325760, 18159391215808, 581109361414848, 299634913186752, 15121578994231863346194646252285204089463426227677758856305609596208903234679795524617231418726741307072675907960417072488465158888134553069545083708504097926422958155137126532889425545865363626474029267176223340429663659510394078113872924855549789470764746156552, 145290293153984, 
    581109629850304, 308705900893120, 2924430527809705070088485477137584102265078158146, 2924430527809705070087866507117941412127628596034, 18160196522176, 130014654237596239297271792083490816575478600337087968944669845606237963766353617992215976049185988, 
    11596431741314395355330124841714141818469225282, 45761303712945224195000282668839431503492420418, 158897688088768, 18160195604672, 88528942796992, 25701619751651552236791400185509199390789605186, 
    2865656668356194139858815229552715920150893378, 158896682438848, 18159256998080, 158897689071808, 158896749547712, 18159659651264, 
    18160196522176, 25690556661479402145936510681964114706377480002, 145290293153984, 145290293153984, 163432654443200, 3957286425642772021614215500889958493038270111059487942233511113109997309326662754090791192480055088311977902091347125502893343687363171984319542315847498732215818531707989574, 
    1143784428020545, 1143784428020545, 1742525631811259563293252532985757070180870609017440473753100349909090211485386140737983987655568163549159752981794509888720854604956001332660328045783570095427394461585285902521722771703823509989993641578532218503975489948023817054345609034373986897264410632249159112, 937005778363786898938722978379335981311233725456463833803353661102298313851330862795735772423834256260, 283958550204864, 1978643215585518646329475387231881846403692219709812386182779538427882290416409009058521461858001588914181473573950452607718759217179575019923622094010585445256367644321239622, 
    538379777262849792601510077977051104322875638007368583243326261163230190074160617433042823321896633220, 16609689126190662643631579766809599731947675847607965175098664460632736644932036152107246656292137092, 708794716787392, 6708539740594511671084603868066853898227080819564986650430195350470651349754669578171551990343840485516587080521087283279889576081437127738577463365191673167933030598784695553754490951569313808828337127340833141030895651210783261598383530735482463533026862443790363351974791610946767221773335691047747944639260103648390953941422408736754069994639354493807557479750247935809477194, 3967672427131056788308956829168969871048389362912191121491771376972129532642078328703511531054371052518806375483229003824745748636840175201029117500384593989592535551172377158, 286156768940480, 
    568336141259712, 708794716787392, 708794716787392, 249081520052720181906982371079378026031147705009005921719670247154613193624829464719053026852490869063346965484915885301379680592834013734930956909125537718583456207121990, 551485161054599160949027408895524450534332997108279515471173462822045779273009807621880817717101252, 158471547785408]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x2492cb2493d925930000924d64964c0c02486c83cd8000494d920001921920d6490406c8049249249a49269c0000926924da68208248249200009209269258208248209a492c924924965130180820920db42001ac1a49269a6945134db60301049241a4c20824822924924935924de6c000259b49379b0100db6db6f30000135924c60c06035b349379801000a492cb249318049a4aa6a24d20124934d34a060249269a6930c0492492c9a4c6012492cb249218049249a4924830124d24924986004006184126d80024834924920001b001b0e360000200209a48049249249261041249249249a4904924924d24d00004935964926300924d34924986066db79c7180000924820824920804120024124820924926924c40124926d24c000269a69a49308049249349341009249a49a4c30124934934d860249249a6931004924924d34000924b2c924860124926924920c04925964d363001001001049b6124134926924800024d249349841049249a4930820d34934d369241249659e6b0c024d34936da61809b6934944820124d34934d340000301208209a482482482c8208001048208208200201041248201000248269a0806d0492092082000412482082080010410492080492092082482000400002082013402486c90c024984d04924924106924124924924804904924124d00025900924820800820804120020020800024834834904f4d9a18049309209249268201b432492cc00124826926a248089849249341009209269a48201b43249249a0806d04934924100f309208208200041248209208001049659641003018209603009a41041240201248261049808349201209268000268249249041a49049249a0800920d24934d3012412496598606c824d34936180da09349348001241241049040000001041240201a68248049449269a4924930000926924d341041b6da7124820834e249249049008049200009a09269241041241e51a8c20804034e24924904900524d249a6924924800026db49a4920820820124800026826d249a08209208124949349a4930000d34924924104134927924c20834d249249349049a6d24d248208279bdb649600009b6d271358418451a4924904100004820824820104924920d24060800024124804004924824900524d24924c00024d249b49208209249e6f6d925800026db49b4d20c30d34924924104000120820920820c249a0904920836e3db3cd81804d24934da4934d00004d34924d34104104024900004d04d349241041341008049a0000800100924104924000120020000004024924904904820124c2092482000482080082010492410092400000002002080410492482490000d86180493092072492480002602cd249b0826920924800120820020820024820800821934924104124000360860124c24810924b24924f65b67000024934935930300921b20f36000124f65800064864830b30001b20124924926926924c000249a49b4930820928926d2c1241209208000248249249b0830920824924924920924836d06006904924924936db6db6d80c041249069808209204a4924924930db6c36d861869069249a49349349300009249349248248308008000009a0a249349248248209249a4b24c60126924928934985124924d28d309a49249a49a61269a49249369871b6db71b0db09a4924b249a4126924926926904934d24d26d401001841049b4000120124124800000006036d800000008049200a49249a6930c049249a4930820924924924da4124924924924824924926926904d34924d26d30924924924da412492492482482692492c9269049a49249a49a41349249349b4c04004004126d049059b6f379ba066136db6db6d80d849259261b6d879b0000339b3cf3a000108decdbcd800009208248200641208209209008041049008248209a08249a4020126820924906804104900834820820824824020104124020924820820920900800000800804920921b203009241340a4924920806d0c9249208249209249249241a41249249248248249249269008049249249241a412492492482482082492090080482492482402013492493480406082480c126904902124d26924924924c00024924934d80004d24d24920000d34d34936020124024800020824124900004905928d30930200d34d348301240149249b49249349300009349349248248249009000008209249348248248205249249248209249a6820824812512924924d34124124924d24104924d241041241869249a6000000024104104d061a49269a0820924986de79b6d8c0261b6db6db6db0004924d249240001208209a48200249208069208124124a492cb249218049249349308209a6a249a4a24124934924924824924934d249249000249a4800804920031b06180db6020924124124804925964924300924924924104124924924834834d34b249849049249a6924924c20836db6db6d861848049a60049208041269a0d24820924926924860124926d24c00026924924928b049249349241009649249649348249249241249269a5000024924924d041049249a6930820d24926d369241249248209a4d24d248248228a4920820824920100004924934000820924824824000124924d04024924924d000049a69208001049249201240001269a4c208041048249a490492492492082092092480400012cf24824820820924920804104934924920b249249240001269a49008041249248049008249a693c920104926100924124924924802924b24924860124924924c20826924926928904924924924920924d369a69a6000924924924924000904120820124800030db6db6d80004124924920124d269268000249249a49b08209249a6924924c208248001268268248208249a09b09208249249a49218049249a49308209249249249a4124924924924824924924924d209249249049249249300009249249249248249349649204a48a48208249248040001249249208208249209209000049249249209249249340a082492492010082492c920920924924924824124924924924824924924902134d26924c00034d24934d041049349b49300009249249241241249b6da69a6d00036da4934d000069b69b69b4000800120800026804124904104d00834a30860100924924924124034e34d34d00c04d36924924124124934da4924904104900004134d04d041049249241241049349a4930000924d26d24c20824926db6db6db4db09b6db6da6d248200048200009a0820926da4c24820db8dd6db8000134da5234d84104924db6db6db6db61249241249248001a0800020000024934d24100006800c00800000924d249241249a69a682482490c3000059049249008349209a62001800201248300200248268361a6986004820906820000124a361a6986004924804920800824c009a6200000b2012482402486c12098000524a28c000248134c20800028804921860000b20924920104924124820020034834d04824804904920824934da41049249a4924000904126924d208000249b49b4904b26924020124820924100000160124920000024826904004008b049208000009209a0d80b26100164820060004020824020800004104804920c009291809a6180120930028a0800010d8241300008209009a03041041249a6d24820104824900820124920800026824924804124904924800800920d241001001241e6f66de6db0026186db6db6c30820924d26904124004934d34c001861249a6d20824822000db6db0db6000366c061b6c00036db6dbcf000071bc180f30926f369ac0a08000001040000049b40069a08200000000200001a0d86024c34d249251800049a0804920104924120924000126820d24804104924824904924934920820100004100000120c24020820800004000804100800800900db692692400012080083000412490482410082480080082010412410092432692492480002cb2482590000d904004900000924b24b2600012430404c06c92c9a4984902925b258301641249248201248269349b6e0080492692c9b0920d24d389200009a0186db99c9b30104120b26020800030de6c08f000001269b0920920001b00000136dc6dc0c06d849269200009a0124d2680012c8249249a0864920924800126b26c2c8208249ac9e0920926926d261240201248201248248249649e0c059049249a0830920924d24d361a41249a49a6c248349269269b0d20966e46067186004000c379b61b61c6db6e36c46c2082400000c104904926920000b209249a482102482c92492002492c9b09209204a48200240041000001289213268208008000008000091269b0920d299379460a08048001040008249a09369a09240241000241249b49a6d24836964db490c001b25930964000365960934800034b3cf2c98000002c900f21b2db389240a208, 1161367889514944, 1161368023863744, 1161368023863744, 1161368023863744, 1161368023863744, 64888527178777394292726084530644438057171389755550550944434849681920774757862638406422031404955140, 
    4217239466888111472080135761448141428706796460770295487278445782208685478647792114049786043235917061, 105624528554049, 51381112945374834483894122934317143330327122754, 105624528554049, 105624528554049, 4217239420481885636210233041391608226202741985955576732733150974919101614712730766578795046897938564, 
    33283751484824631724445106821371616141461259251934954545948386242870102205413946404683897570887692420, 33283751484824633568462844125612451598509071355751755472915384923368627530884029838717752451633575428, 33283751484824755273633521923436043029485874619799508328075090853890665954975543090854182612312847876, 105624528554049, 175993272736193, 105624528554049, 
    316730761095489, 1161368829039040, 1161368023863744, 1161368023863744, 1161368023863744, 371089997073237616976474383349547598989246878530, 
    2928723418532815193509639225596081491855743669058, 1134980550365632, 290555620233664, 532345381924043839394585579903696666436741286529437285192836705285848569740956579215530728817861816452, 51381112942052109256960923385871402824857836355, 97053213332550074973426909719602348724288770883, 
    589699837819074158287220465640199798039190773543901636070630101367690770513641555007310572554298814596, 290555619971520, 1461685619180623542704268012551727621345646826307, 290555619971520, 1134979610841536, 1134979745059264, 
    1134979745059264, 1134979745059264, 149818131878336, 290555620233664, 537795352846196041671505917830687323434616194510042867372680495575059477332887034895695546751011483780, 589699837819074160131238203182591064576023755411538723235102216852391869984930547171387231661943124100, 
    469678024263096156171119672210160399660265126676396637222044838783415648420899669744859334922503222302818647087075637990826647966696461733992022489632914108954509512100921495038126474550537316613863478574435581475142187299860831041717051132543877272043792749877513, 51381112942052149821780130689214502527764028227, 97053213332550115538246117022945448427194962755, 97053213332550115538246117022945448427194962755, 3894729222530060908604147091557245241200436209806034724911944401619598107810210937562331681241904347784145593110680992986492187836733271939579336136029370694009348656090695, 97053213332550115538246117022945448427194962755, 
    170376978805149628973502015288812659393637142607302973438502839047929144885401079020508016979863388677, 290555619971520, 1461685619180623583269087219855070721048553018179, 290555619971520, 290555619971520, 1161363598741952, 
    1161368023863744, 1161368023863744, 3294089090345329113525181418652120263633986933570, 371085815683523277117811753219554224322121847618, 105624528554049, 105624528554049, 
    371085815683523277197194658829025044817323774786, 371085815683523277197194658829025044817323774786, 105624528554049, 105624528554049, 105624528554049, 1161368023732672, 
    1161374271476160, 1161372188938688, 2923728051608344333965626677512354229235935630146, 531503961562178941065939689227052601091872534272466044560015968666961643318623781628624186866634227972, 387305663899969, 316936919720257, 
    2923728051608344334045009583121825049722547622722, 2923728073386415816985071244777799925355713155906, 457684747293120, 316943093993920, 316943093993920, 371085815683523277197194658829026170708640682818, 
    532345381924043839394585579880531386182885432853993773382132745751665884622510470722443980983789383812, 4217239466888111241578026998041479823527757052505514180070973955356654836631036393584111138028875908, 4217239466888111241578027001395728598050171987921906544441328393801679552990875933069063335563194500, 365555209776780933718674877191735917372977992514, 368231309409075616123813067285691943719626888002, 371085815683513561766781950086125462647656695619, 
    33218886717633724322929770282846208316897019609211577292832712416569939541302584441939165261338834436, 365376805856876505665456302569967727422375744322, 366090429703239870199702515210530500352336220994, 365376805856886890259173372225805752784144847682, 365733616418933912545684089864669696841167688514, 366090429703239870199702515210530500352336220994, 
    365733616418933912545684089864666319128562258754, 581395120223413659886868621243258330693075244354194211265808066555767430205477487702404564516085133444, 589699837819074158287220465640199798039190773543901636069275329845245723626821855781758671367752085636, 4217239466888111241578027001395728598050171987921906544441328393801679552990875933069063335563194500, 366090429703239870199702515210527122639730791234, 365733616418933912545684089864666319128562258754, 
    366090429703239870199702515210527122639730791234, 2923728051608335247372312066421852925612542417730, 1134971155124672, 1130577689318336, 565703573783105, 565703573783105, 
    290546225516992, 960962612318422722514276120579029485995887052264404733803492738012784614595180564899611510714785712260476098493168229733472560874418871043571893016023348837390089483686641979850920728111360275670343077846593966675936434955989176399802383307471012949586347016249877512, 1161368023863744, 1134979745059264, 1134979745059264, 286156768940480, 
    299351445344704, 424699667419584, 565703573783105, 572047257244608, 1461529513368741998433685863018524930873030148931, 290555083887040, 
    290555083887040, 589699837819074158287220465640199798039190773543901636070630101367690750358739775402030175611111305348, 17127037652171710163778034218543780236125033283, 565703573783105, 290554815451584, 290554815451584, 
    72709645013441, 283815877546433, 143086979125697, 290564210168768, 105639091177537, 105639560939585, 
    290547030299072, 105639091177537, 105639091177537, 105639292504129, 259538272591457719330497892307323205754262264456771438428920569731979583890393579381732155989579589, 143224422273472, 
    143224552296896, 143224552296896, 143224422273472, 143224552296896, 143224552296896, 143224552296896, 
    143242021573568, 22883352347638052929493300967077774727510525763, 145420085891520, 48526606670938856039062264002223371786284718914, 158634899149760, 158634899149760, 
    158634764932032, 286156768940480, 286156768940480, 143641432576961, 286156768940480, 567635910595008, 
    365399103964886692344315616704312860016990245698, 11440369486862507520805723326157816451106353730, 365399103964886692344315616704312860016990245698, 1461529513368760171542324862125027419277165134659, 22880651861439062988432703675872125127529354050, 365420707896870956764147862711047968171111764802, 
    365421404795155814697691768288430286136345121602, 365421404795155814697691768288430286166409892674, 565716458684993, 565716458684993, 565716190249537, 365466006455694059394540549071740703431563694914, 
    145419146367424, 145419146367424, 286156768940480, 286156768940480, 286156768940480, 286156768940480, 
    290547030823360, 2923728051608375487825870648783506772095565648706, 2925868923147434427647516106398384290313191641922, 2925868923147434427647516108464419626568661422914, 290564209775552, 290564210168768, 
    308156395951040, 2923192831681916551344843010764715566828812849986, 2923728050244566794963132091203300995613354750530, 2924084864890002220300904370550234744395520930370, 2923728051608375487825928679510245383864087302978, 365466006455735597927865152721874083341588847426, 
    145427740496832, 286165358875584, 708378247566272, 286165358875584, 171816153781184, 299359498408896, 
    580835028767680, 299359498408896, 299359498408896, 580835028767680, 2923728073386446970765990339100188300954388484930, 541406973809109697134427777592910947458798470398271077176537859574431216540629344993538186917516838882682826035607350942451317857716850203640607702089205455101757956782662, 
    171816824869824, 149825921225664, 290563405386688, 871106098500544, 290563405386688, 290563405386688, 
    589631121789888, 290563673822144, 290564210168768, 79449387438528, 72852317671872, 79449387438528, 
    79449387438528, 105639091177537, 105639292504129, 105639560939585, 290555619840448, 290555619840448, 
    290555619840448, 299351712862656, 290555619971520, 371085815683523277355960470052578371796090245954, 290555620233664, 290555620233664, 
    105639091177537, 105639091177537, 105639292504129, 105639560939585, 79449387438528, 105639091177537, 
    105639091177537, 105639292504129, 573029569385977991062543329210225784855044328448243064202701118971729437383135997309438785211258335364, 565716190249537, 565716190249537, 145419280585152, 
    149817327096256, 149817327096256, 45694401243405505067210609680605083117594692419, 290554681233856, 290554681233856, 143091274093505, 
    290554815451584, 290554815451584, 154219538551232, 145414855594432, 143091274093505, 149817327096256, 
    149817327096256, 4080981816248566486622747978162396661559107566827178809714655490908935916825065799353238743431507995160276165642878409082244248254428907737720141366673807565817544353709862470, 4080981816248566486622747978162396661559107566827178809714655490908935916825065799353238743431507995160276165642878409082244248254429269798158545245198933776991472472498155078, 143091274093505, 290554815451584, 290554815451584, 
    143366286226369, 290554815451584, 143641432576961, 290554815451584, 290554815451584, 365399103964897076938032686360146663233707594562, 
    365399103964897076938032686360147507658637726530, 1461529556906314653900892778530526403797608116802, 365421404795166199291408837944262963453155627842, 1584806376596168463253968013908706081342648324518585627243378283275113548289568895156944396007966929045608555120826038077844916423354752823878658999346624344903558003853616194506987744241674839899966023154157819433614202739604766949177896435966219377333781544498877512, 283966335624001, 426898422239680, 
    989865974961088, 426898422239680, 989865974961088, 33218886717633724322929770282846208316897019609211577292832712416569957590468626176316426178208527876, 286156768940480, 290555620757952, 
    589639979373504, 283958550204864, 72845877121472, 283958550204864, 1461529513368780940808987163949805878856025965379, 72845877121472, 
    283958550204864, 283958550204864, 565716458684993, 565716458684993, 565716190249537, 365466006455704444027871699984706393973297533762, 
    145414855594432, 286156768940480, 145414855594432, 286156768940480, 286156768940480, 290555620757952, 
    290555620757952]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a4930004920524920d0402481400092cb2882c0a0004935924120904126d6490480002492c9a0905834824100920484924824000920925924304b24124924920824824924934906d02824924800964820824805804100c30db6f01b06000024920164804924900120903924924800964810524924800804814924924920d205248a400082692482c0001249670008108249259a412012492090403482492490c12c9049249249201209249249241a4124924924834824914924924920d20924924924024104120960160836db6db6d86d824120009269309a4020824804c06800024924dac900824920934020924b34b24110004924905920104124024804000124924964804124904920102925923910504120904824804124900920904924924920120924924924824124914932400024924824900004925804d200009a6924b240000249240348249ac92490c48, 1161156221800640, 1161224003915968, 387314253637953, 4217239420481885636211459009447011759740246693930719218008231716707284503742370822740980676046372996, 1161292658380992, 1161224003915968, 
    316934772236609, 316934772236609, 1161292658446528, 1161224003915968, 316934772236609, 324403039781655692647088007821301667198396256771944731613634334653699525851601226272190744861414980, 
    97053213332550074973426796383383220605107049282, 565701971022528, 567900994278080, 1126175062106433, 2923059026696272904011891032377754336666484478786, 1128376031535937, 
    636139436774080, 17127081202995492422529844575575664447885152834, 1102970368515542617896172687962525255428290906041628146779008017300459051501816079219365639975839108, 1102970368515424571948192825821603358479436035586220133618658775503870172831614896926999548995020164, 97053213332550115538246003687879241812620088130, 97053213332550115538246003687879241812620088130, 
    97053213332550115538246003687879241812620088130, 11440630906297679322585746363461267944565117506, 565701971022528, 567900994278080, 581095133811392, 565701971022528, 
    1128376232845633, 1126175062106433, 1134979745063233, 1134979745063233, 1134979745063233, 1134979745063233]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492412080490492db318259209a6824924020124936d24834814920926b289200a5924935921800800124d6483402482482c980002524920904024804924824000920925b66304b241249b6d20824834d471b4106d04d36ded98c1bcd84924805804000f30db0f01800000100120100804900000120902de7b68307b3c124934c00964810924904820124124924c00064826920824904904924834100d207268a482092a92000030c135967166810104d359a0c20124920c0003482492d98c12c9049259b0820120d249b69641a432493cf2c83c836de6d8780c000db6e46db61b6092124800124004186134160100836db6db6d86d844145a0824120904900004934005920820824924020000120d040348148ac922500004960805920104000020804000164c21964804100004020104d659c3910820904824124000124c04964820820824904904104834920d307268a4b14000126900824804120800920900825134920120104800924824136c92934400024d24824900004934004900000934924b2600013110406402492c9a4b0c48, 1161156221800640, 1161155215167680, 1161224003915968, 28545062744809569627808806337319509373564753730, 387314253637953, 1161292658446528, 
    1161567746331072, 2923059026695276303732182258223596675297148147522, 1161292658380992, 1161224003915968, 1161499024429504, 316943362171201, 
    51381112941387784284643146475174781189865083714, 316943362171201, 316943362171201, 316943362171201, 1161224003915968, 105624522264768, 
    97053213332550399493218394849395384036026749762, 3020056487994356235900588060281961423347891835714, 3020056487994356235900588060281961423347891835714, 7183239312607841750779775743275536352613639600624194042416712907887156666376688669189352791297820139120313794094609455850452557039672638299397037507921909748284887751194571334, 581095133811392, 736462597040059628525269258032755211749604496194, 
    736462602484577499260284673446748930657895879490, 567900994278080, 581095133811392, 736462597040059628525269258032755211749604496194, 502750920750644668891194207713356234686294187586, 565701971022528, 
    567900994278080, 567900994278080, 572299040789440, 17127037648015849498874310985141379010987561794, 316943093997889, 316943093997889, 
    316943093997889, 316943362433345, 316943362433345, 371085815678528917485961367649310328800329865026, 1461551814178073752873021527768158459336975193922, 636139436774080, 
    73189483352768, 73189483352768, 22880673485650519144870035991783536253292582722, 75388506608320, 75388506608320, 79786553119680, 
    90781669397184, 95179715908288, 97053213332550440058037602153891405243539788610, 97053213332550440058037602153891405243539788610, 4217239420481885636211459009447011757397331037038499409718394504232562165564677752716142049323401348, 97053213332550440058037602153891405243539788610, 
    284501880607680, 286700903863232, 288899927118784, 291098950374336, 308691136418752, 565701971022528, 
    567900994278080, 567900994278080, 572299040789440, 581095133811392, 105839008948545, 316943093997889, 
    316943093997889, 316943093997889, 4217239420481885636213217601802303497115326521374029147114658860942937824903218094559125145584418948, 316943093997889, 565701971022528, 1461685619180623907788879271669994605197041668930, 
    1461507213219035662803746985923813418304993825602, 572299040789440, 581095133811392]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492492492080492c335901800a268249249a4124986d26db4824924904d249249040243049218059208001249341648049249a4924100925864b20300134d07124834844d01904186104924824db002c904965865b203001a69241640000241001008000048049240059208609a1b06b26104124120d0400002602498c9009249249248201a49241640000289a0924924904924924d24100820924924164824924b26124924104c00024900120000004d24134900020d348049069a40209209249648061a4124dac980804824104100db6006006c06104100100020104d34c049369a4030c00f0cd8cc2002603006c9840009009063340145041209249048000249269ac1841048249201200009649a682412692496482c920824924920900004925935830820924924824000124934d0482492492c900004905b30800000928366b06000105924060000034e20860904935b35920820924924824000124164804020824924924904104924d24100924924b260001249089048000241869ac18000410493c130000106d00c3412d134b6480, 1161155215167680, 1161155215167680, 1161296953413824, 1128376031535937, 513258889784516564910739244558081963442372524097847763678341462119322553913772024308689219249574908711180919529804515306533364243744321390766637433569087183701404312107590, 1161297087500480, 
    2923728051608334598332112317035909472843903027011, 1161155215167680, 1161296953413824, 1161292658380992, 513258889784516564910739244558081963404033433880928535218402325917022788325591231375586339473331589236029757671376666782388726726323105879930730694581580115782578296814151, 316936651546945, 
    28546369434083170030383713766576205968546219843, 513258889784516564910739244558081963442372524097847763675878836732047898963004584302430243383978414865081240422893612603993343514738225042933674172295823528822190959983174, 1862771912242165652843398957547466467620506365395872802101552661682054016951388531025561481832547885408302702136577531972696398500726144101988137235878063510861758193444626554132601266558789575477433074324763266946929238966335231491648906356513739932233105416246956552, 3957316615512914002351405356928354737105499913128815553575500078503183272219543287050254281466715874554855711555593318019135453090169253849406224821059153538782321990224227911, 176199297413569, 316936651546945, 
    1161155215167680, 513258889784516564910739244558081963442372524097847763675878836732047898963004584334258930514204759963025704304293284921290230506150396853834972526666082515346559011355206, 176063733305536, 1161361582203201, 1161164006428864, 316668207698112, 
    513258889784516564910739244558081963442372540322805462294172548550168886716865465354003962317343780688634800435538976770606671853524441522034873659782320196638341488147014, 105641702133952, 105641702133952, 17127081203161890658570681095987885601437261378, 72845070704961, 75044093960513, 
    75044093960513, 188398111012331902686419061334552080206912314946, 105641702133952, 2928713681012593648340898175235560319970032240451, 316936919720257, 290548641440065, 
    105641702133952, 105641702133952, 90575098211533486264477223487511349534073453679028298407165298405837874137032738784004696605600463353623662632703342634440830116374366391445779242315257849035030441143878, 105641702133952, 4050065516057230157794282668569750880526849546903012688426423258396565652475587254490067567554752223679588720735620831205619810153611342609583167387983518584828890603003620935, 28550550818823270679482731688152566453315311426, 
    149810884649281, 4152422188735213528166535053721975608662291842260646782126342810497117474434459974800612663206853700, 290548373004609, 286150326493505, 290548373004609, 290548373004609, 
    299344466026817, 16674315922253828236781220379183689059877952370862543678015821053923117706964451100628460413375006660, 260536679396684181049248953103489095909743378276927810441479935530373253024329701006102699699966149, 265751028401102427289069447553604734446076100293966357408385390086151063885012604398609637672373173316, 290548373004609, 290548373004609, 
    290548373004609, 387305663899969, 316936919720257, 316936919720257, 316936919982401, 265751028401102427289069447553604734446076100299785051415110562814237621680927605927037384721285233732, 
    290548641440065, 290548641440065, 290548641440065]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a4934920000524924d249040148a59249249241008a09a4924920800004934121920500124d04864804924924924100925924b24304124926924824824924d34906d02d249249a41841a6924964800834924926906102de79b7b36306124924964800824924926906100804904005920f00d81800f36000000120004810524934d36800814924db49241205248a4824824924924006166d27860810924db49b5920124924d24804024924d2c90c104924924924d209249249249a4124924924934844d24924926904924924924d209249249249a41149249249241209249249249a4024924b2493c830c3003603cd8241291c520824924920900004935934000820824924824000124d24d0402492492c900004935b3090010402080002400033cd26c64804100004800102f33b3591050412492c904804124920900904924924924d2092492492482412491496240, 1161157362651328, 1130581832774081, 1161157362651328, 1161294805930176, 1161294805864640, 1161294805930176, 
    316934504063297, 316934504063297, 316934504063297, 176205739864513, 316934504063297, 1161157362651328, 
    176063733305536, 1161226152317120, 28545062744810257964560610345572175332469905218, 72842923221313, 75041946476865, 565703582159552, 
    567902605415104, 72709640818880, 72709640818880, 143078384996544, 283815873351872, 17127081202996467249091011506551730081514918466, 
    28545062744810298529534560745272427624647366466, 17127081202996465981440411278288516420145779266, 17135443982445916232769087400903973217079661122, 708777536918208, 143628560241344, 145827583496896, 
    163419769541312, 163419769541312, 163419769541312, 708777536918208, 565703582159552, 567902605415104, 
    581096744948416, 2923036725865007830418698787419181170363757238082, 2923059026695276952772074939003297470583205271362, 567902605415104]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2492492492080492db259218209a69a49249a41249349249348148a2934d24924904024304931805920420924d241648049249249a4100925b64b243041249a4926824834d46d34d06d04d239a693496480082495b92890a104804804005920c60dbdb00f36104160920164810924924924820124924d64c000269249249249049249349341007248a4b1412492692680002492d92d90c1049259a49a1820d249a49649a432493cb2c93c8348929249b4d249b402093cb2c93c830c361b603d18441452c920824924920900004935934000820824924824000124d24d040148a292c500004a65b30800104004800024000166925860804100104000104d23b45910820924924824000124d648048208249249249041049349241207248a4b1400012c9249048041209209009008259a492192010482492482413489296440, 1161157362651328, 2923059026696441324713111315021351724340645729090, 1134979745063233, 1134979745063233, 1161226151334080, 1161226151530688, 
    1130439826215104, 1161157362651328, 1161294805930176, 1161294805864640, 316943093997889, 316943093997889, 
    316943093997889, 176210034831809, 316943093997889, 316943093997889, 1161157362651328, 176063733305536, 
    1161226152317120, 28545062744811556043727004209620829056148707138, 72851513155905, 75050536411457, 75050536411457, 79448582922561, 
    283957745688897, 563504558904000, 581096744948416, 581096744948416, 581096744948416, 563504558904000, 
    844975584203575910019615504572259328988016580418, 994925446435776, 565703582159552, 563504558904000, 567902605415104, 581096744948416, 
    572300651926464, 28545062745808441546213515136165062818161234754, 316943362957633, 567489873318080, 472395693875842482956046913392939744696981894344502252394457110387779620296581413491328976561767727236, 472395693875842482956046913392939744696981894344502252394457110387779621481057921742590850848549781636, 
    28545062744811596608700954609321081348326168386, 513258889781001788508752372384011230221984426090761528496969611538775695048092312526040383399720275402700216841501237472386162153188475053436590889326500832454382995847238, 28545062744811596608700954609321081348326168386, 513258889781001788508752372384011230223304216865169491994824153961901942688858064103720685153071493012635290298849532918329073210819799017689873884031588249152162203908166, 15121341268955300454560687058317760675804896124643772855641161530271676940097517645367644241470617776362471646784484213091683849195801144848853623815585243479933782260327626931735494833929035527252690443073274514328938652222867791331570501633938447925257246956552, 28550550818825297504239691914989740906040530754, 
    163419769541312, 708777536918208, 4217239420481885636211459010914495579850478051834331480633611333426392334692182368737416746323165316, 565703582159552, 567902605415104, 581096744948416, 
    572300651926464, 581096744948416, 316943362171201, 316943362171201, 316943362171201, 316943362433345, 
    1461551814199011120787062467951552942996774262594, 567902605415104, 581096744948416, 572300651926464, 581096744948416]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x144948a4924935920000924d26d6480402482482c980004934930001920520924d0406480492c9249adb2d9a0001926966b6686082482d8200019219259668608648205145248a48208269200001c79459670008149249259a00201249249249049249b48308348129a4924964926966c00824db6db49b0120926926b26000160d30c000648249249249b19201249249249049249b6c30834812965925b24304124924934926d02d34924d349b4124924924926905921824824925921b36de6f68f36000100124964810524924924904024924926906104924924924d209249249249a4124924934926d049249249261209249249249a4114820920d26964830c30c36dbcd82424804806005920820924b2cd3c824830db6db6db6c2c90412412492c900004105b55920000800924b24000100124d6480296592430db2430c1861e6de6c34d34934986d02d34d24d361b418c1861e6de6c24d34924d869018348359b4921860c30f36f36000180126de4800030036db6d853349b59b49219105249249000248249249061269049249249201209249249241a4124924934906d04924924920d209249249241a411490410416493486240, 105640091521216, 105776595210432, 105640091521216, 105776595210432, 28545062745826610851591228548041198310933926722, 105776528167104, 
    105776528101568, 105776595210432, 28545062745826610851591228548041198310933926722, 28545062745826610851591228548041198310933926722, 105776595210432, 105639554650304, 
    17127081203514317805215536662316159062780157506, 17127081203514322875825191185635800234919468610, 28545062745826610851591228548041198344219923266, 17127081203514317805215536662316159063585463874, 17127081203514322875825191185635800234651033154, 28545062745826610851591228548041198344219923266, 
    28545062745826610851591228548041198344219923266, 73204515738304, 22880673485670559509961326503815560465817343810, 75403538993856, 75403538993856, 90796701782720, 
    95194748293824, 105639084888256, 246514150609088, 105639084888256, 246514016522432, 105776528101568, 
    105639084888256, 2928712635661194888245720056738522574537407599426, 72851513155905, 75050536411457, 75050536411457, 28550550818843470612569206011670893037543757634, 
    176145272213696, 176145272213696, 176076617748672, 176145272213696, 176145272344768, 176145272279232, 
    97053213332902791225012424598498878331639830338, 1102970368515424571948412247303579007569981664179232600548237794730884721995889129938148039405790852, 97053213331573563229227470946662926839221065538, 176145272213696, 176076618207424, 176076618731712, 
    143641445143232, 145840468398784, 163432654443200, 163432654443200, 163432654443200, 91366196719946597521282589673529834935400011586, 
    91388541106358686388607364683728601568040195906, 45694314204870956538934068744800732650565312066, 283957745688897, 145290293153984, 708790421820096, 143091269898432, 
    143091269898432, 1027663288861981544434363037134624928077837285186, 844975584203594047633728212277508432895299065666, 585508212249280, 581110165803712, 581110165934784, 
    581110166196928, 565717003932352, 1461551835806959593375293896982334075249681831746, 1464361729701974451891127397484688824334624559938, 1464361729701974451891127397484692202047229989698, 567915020554944, 
    581109227197120, 563517443805888, 581109361414848, 567916027187904, 585507273708224, 581109629850304, 
    581109629850304, 581109361414848, 581109629850304, 581110166721216, 72654742687936, 72654742687936, 
    565434869883201, 145290293153984, 145290293153984]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149a49349249259300009249a4b3a000124934d24800c64938d2ca809008049000019209049a4000320124934c20804004904120800900524926d24926d2cd80004d24da4936024104d24d6400002412610000c804924924936324014924924924d2410492000006092cb26000106d249ac9800004924a09a4924920800004900181920824924924924000db61b6d860261349049b0c3080412492480402480512492490402082492492c980006185b07980824824924924180000000000c019b492080000033092cb0a0060061259268608015a5a2ca00904900c24f64d8c2059018471b92861800049069a5920000820b60f200001059241648000000208009004049249241040009249ace00180104934925920064124b268241240219269351a6164050db72361c610412492496480012082d82c80412413492592080400482002400, 1143784226431809, 1143784427758401, 1152580520649537, 1143784427758401, 1143784226431809, 2928723421255084513510478084215474338173804397379, 
    283953450717632, 143645740110528, 91366501613926146501184731904124236344063955522, 72709640818880, 143645740110528, 1134988133409601, 
    2929437042379178558083424565806454830707014419267, 1134988334736193, 1134988334605121, 1134988334736193, 1134988133409601, 143078384996544, 
    2928723418532825578142970376508477478719658705731, 72847218184640, 283953450717632, 283953450717632, 143645740110528, 22880564743836239526991616807231090143927472962, 
    72709640818880, 283815873351872, 143645740110528, 284503491744704, 265751028401102427289069447180654201188962128707989100574659411042167841008391317327611930407236779076, 265751028401102427289069447180654201188962128713807794581384583770254398804306318856039677456148839492, 
    1128391264969537, 1128391264838465, 1128391264969537, 1128391063642945, 531550657856897444840950424683310771935430631770051307026752874919687343577192543873110405175316888644, 79306710585536, 
    79306710585536, 79444287951296, 79306710585536, 551485161054599160949015281399527600627153221871381660619777391944797718023169200236380321195801668, 551485157187413703439291501099138753684484580098853538949984661410565341663646023005349752892341316, 97049358902081, 
    158488727654592, 551485156945714612344934677186017527250719757583056372118147707473031807548550839877750907872787524, 532053411279217730194372624496281262155540255786838790265430814398454856155294398937367107198511266884, 158488727654592, 158488727654592, 158488727654592, 
    158488727654592]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924964925930000924d2c964c0402482492c980004964920001920920d2c90406480492cb249ad92d9a0001927b24b6686082482d920001921927b248608648209a49269248208209241861241a492c92c90490c1b48308348145249249ac926b38c0c03c9b49acb20f209a0926b0803c83c9a49acb20f2082492492492080292492492492411492492492c0000ac90412412492c904124905b35920400920124964802965965b2c3041259559559a7504934d34da618412492596c9861059c19249649a5921b3cdbcf6cf36004104125964810924924924820124924d648000269a49a4924904934934924100524b2cb648608249a49a49041869a4926d20c208a4104904924b26366db79eda66c14124926926800024924926906104924924921820d249349249a4124934936908104924926da0020924924da4184092824926da6964830c30c36dbd184424824920800902820824924020104124164d000141009240009200a4104905925920800120164934c2482492c9a4b0c50296596430db2436c1b79e6de6035144d44d87104934d34186da412592590c336901b349e59b4921b60dbcf36f380041061279e680006c03ce38e04b649b59c4961910924924820124124924c001648269249a4904904924934100d20524b2c860b64824b24984120806924920c26d208a48209a092ca2610610416736c8141041059a4d201209208000248249249061269049249a0820120d249249241a4124934906138904924920020da09249241849a409290410416694486440, 105640091521216, 105776595210432, 176076617748672, 176076617748672, 246514016391360, 246514016391360, 
    176076617748672, 35201686311104, 581110166196928, 565717003145920, 1464361729701995221157789699309467283913485390658, 567916026401472, 
    563517979890368, 581110165934784, 636154469159616, 105640091521216, 105639084888256, 105776595210432, 
    28545062744850459121550213054852101669447014210, 28545062745847380118253530372819657889794757442, 105776595210432, 150958497008678147900342096783323651760706978917778538736433208750063996791941753920982603384547702913322574253456206693024691222153710683516225573224402983133407612284486, 105776662319296, 105776528167104, 
    105776595275968, 105776528101568, 105776595210432, 513258889781001788508752372384011230195043953622777658304224379201057319822478333293950863052555775002700148453465259835972192144104343970537642935353347931164625279596614, 28545062745847380118253530372819657889794757442, 513258889781001788508752372384011230219177270641386485795667921523907969662550470556698043565841414558023559936037915334916978231533217146255088972699936583932570859681862, 
    28545062745847380118253530372819657889794757442, 105776595210432, 105639286214848, 736461225016249006906417448941417149233564238659, 105639554650304, 75128652436416, 
    75128652436416, 92720838480832, 103715954758592, 28545062746179687117185259333206702516231739202, 28545062745847380118253528085423392783096353602, 90575098211533486264477223487511349505858766871860494260045355757216553622604165527732262863385989092612607512615890717615497089548403209986244158370152730019705325268550, 
    28545062745847380118253530372819657923080753986, 90575098211533486264477223487511349511359743547103306841967846907715661734576538819644427889028390236703688212810900395820146029247114190762544473446972840294462770032198, 28545062745847380118253530372819657923080753986, 73204515738304, 22880673485691328776623628328594020044678174530, 75403538993856, 
    75403538993856, 75403538993856, 90796701782720, 95194748293824, 28556126005163792673338563575708371988420499266, 105639084888256, 
    176076617814208, 176076617814208, 105776528101568, 176076617814208, 176076618207424, 176145272213696, 
    176145272213696, 143091269898432, 246514016391360, 246514016456896, 246514016522432, 246514016456896, 
    996326402273357218109927400851526269960105248795421382739998720182090520650510331407544195673293637749330119195194414192685813951788936987033480899605377828544545123642950, 996326527343160706410786843079002843264608698114789021533217573384470084971430727409899468453882429729489876114139537216141351259030794282873951900070794751500305571163718, 97053300443880264256136419395340888950744028994, 246514016391360, 1461546326125036362266283430743942550092410591042, 990540016391104, 
    581109361414848, 563517175370432, 581109361414848, 708790421820096, 176076617748672, 176076617814208, 
    176145272213696, 176145272279232, 176145272344768, 176145272279232, 996326080379589994946213082928518195668570504168111214115093299032323937080599706757103496796310703306557858909477375807202432728942919591023812179790401145328020699065926, 37895173739116018890760751996630483019218920843790094762211611662036861783836937424729206323197632312890429587681508953571343756002908564451129645361848147206467716253304218478881553906530622179899182353288098443134481861701557132185444839666227012157295376210283191183515867616215428346646929410923189355008432556473068144200149848971185868521619951597574501016707070411570537862993804294679297886320191104718379386112289469756714101398800817712255034664020584491476756213825633615801227204312222676523148, 
    996326080379589994946213082928518195674071480843188762704818228033085556309726214239297896963597435663987097245155469617937513774107106595820864842401339040364523924074054, 97053213331594332495889772771441386418081896258, 176145272213696, 176076617945280, 176076618207424, 176076618731712, 
    145565313668032, 154361406690240, 171953592734656, 163432654443200, 163432654443200, 163432654443200, 
    143641445143232, 145840468398784, 145840468398784, 163432654443200, 163432654443200, 163432654443200, 
    163432654443200, 105639084888256, 105639084888256, 246514016522432, 246514016456896, 105639084888256, 
    176076618731712, 145290293153984, 308156396475328, 365399103964897076933080926198393332420095001411, 365399103964897076938032686355534994257716724547, 308156395951040, 
    183045236629706994930798009932235091868616045122, 365421404795166199291408837939651294477164757827, 365466006455704443988879006312931628472263000899, 299359766844352, 299359498408896, 299359498408896, 
    365555209776780933402383612649396829350055134019, 290563405386688, 290563673822144, 736462597040100518018391694730651869333248054082, 736462597040100518019010664750294559470697616194, 563517980676800, 
    585508212249280, 581110165803712, 581110166196928, 581110166196928, 565717003932352, 1461551835806980362641956198807112534828542662466, 
    1464361729701995221157789699309467283913485390658, 1464361729701995221157789699309470661626090820418, 567915020554944, 581109227197120, 563517443805888, 563517443805888, 
    563517443805888, 567916027187904, 585507273708224, 581109629850304, 581109361414848, 581109629850304, 
    563517980676800, 581110166721216, 72654742687936, 11440325928267459949207758002657319230745088834, 72654742687936, 565717003408064, 
    1461551814183099266523630238299371192178517821251, 145290293153984, 145290293153984, 145290293153984, 567915490316992]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none, none⟩ true 104 ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14a228a49a49259301009a6924b26000138d249248040349a6dac900804804924101920b06924000324138d24924804036d261a080c9004a68a252c9a492c980004d36926b24020104d24964c000261a490000c9029a4906820324012495924924924100b24926b66000164d24924964c6c925a269008028ac9a4d24920805924104924925920000920b60b24164d04924964c008000209009004a49a492d180004d269369a6c200a256490412492496480002482d82c9028209068243240209a4924920804004935820000824924924b26000d34134d8402490012492490402c9a082492492c900004905b05920824824924b26100000904c04805834924100920b36926000b66164d2492480406c1a5a208069828ac1a4d20804904004925934920000920b20b20164d049249648000000209209800049059349019204a6924900027980004905904100d849368201240a250002482c82c804c00926b24826000124164d2406280, 531501997402235843673077274021725842911483841064560589280840357724673930170459758502121706259873053764, 1152580520584001, 1143784428020545, 1143784427758401, 1143784427758401, 1143784428020545, 
    636156616643264, 531501997402235371604539981213064686716613139783140165133717431474319011008406032441629104561390402628, 1137187357795137, 1134988334605121, 531501997402235371604541320929354944417811889186862475624481607899517730610381301894690400398798535748, 1134988334736193, 
    1134988334736193, 1134988334605121, 565725593080512, 6937448691489467385440750068787062186885616665577801344132201073430500415271184974291486959224913765267281657359022672089623342078725673307701448557662884321208761477872187974, 565717003408064, 565717003408064, 
    1461551814199382371272980162574091396072859572034, 636156616643264, 73204515738304, 565717003408064, 565717003408064, 1128391063642945, 
    1128391264969537, 1128391264838465, 1128391264969537, 1128391063642945, 1128391265755969, 2923049270124277460077097079587552656526114113347, 
    581330302976198009799261525613809957314638369308175611521468928201425303804919612368507245360285131909, 531502440922011507987659837301142041274031040853228475323851894931054875329101233260989640031068273732, 1143784427758401, 1143784427627329, 1143784427758401, 1152580319454017, 
    1143784428544833, 145840468398784, 1134988133409601, 2923728051608375487825853723753442065139785352003, 1134988334736193, 1134988334605121, 
    1134988334736193, 1134988133409601, 1134988335522625, 567923811816128, 708794716787392, 567915490316992, 
    567915490316992, 2923718295032351130678381627111041663109555110723, 568057362649792, 708794716787392, 145840468398784, 567915490316992, 
    567915490316992, 88032873091264, 88032873091264, 97049358902081, 158471547785408, 158471547785408, 
    159038902899392, 88032873091264, 88032873091264, 88599826010816, 532053411277163287962389350442714345972601651671339620610792398098506997056905948370834975666964176900, 158471547785408, 
    158471547785408, 158471547785408]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨2, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨2, [], 0, [1, 1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_11_0
  · exact tv_b11_11_1
  · exact tv_b11_11_2
  · exact tv_b11_11_3
  · exact tv_b11_11_4
  · exact tv_b11_11_5
  · exact tv_b11_11_6
  · exact tv_b11_11_7
  · exact tv_b11_11_8
  · exact tv_b11_11_9
  · exact tv_b11_11_10
  · exact tv_b11_11_11
  · exact tv_b11_11_12
  · exact tv_b11_11_13
  · exact tv_b11_11_14
  · exact tv_b11_11_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x124944944a4925125920000924934d6480402492682c980004925130001920524920904064804924924a269a69b01809249a6da4c24824924934904904a208261809a0924b249a4c248205125148a4924d34d201008208269a0000134d36c30030814924920c00c201249249249249249241241249049240208248249249249a4dc0100924924924d200009249249348040249249269800049041200001209249009040048028a3934924924104124934934924904924d24924100524934924904036964934900004920820824920524800020124810924924924935934c31824924924930d609248209a60001049040000040241259249001000b69349349000049249249241009a49249248301249249249040389249349041059249249269209a49249249241249249249040149249249241009249249248301208000209248124249268208209348200209241300208009a69a4d0082492092492080d9ecdb6f3cdb09249a4924820000b3cf24900024904104126904d40184d84d209240001009a413c8001241368028a39649241009241249349348049049208208009005268000200248009049000041049251318049205104a49209249040248249249040249049249249009209249249201241209249040048148249241001200049248201041249040201248124024928924a29349349260000a4924d249041049249249209209349040001440a49249043049021249249249249249241240041049240208248224a28a25249249a4824824920934c04102484d34d34d26180534d34924906014924924926180924d349349040249249249200059659649243009249459249060249269a4920c00820820824a209248009209240600000301bcc040000040249005349249349860149249249241809a492492403012492492498602492492490410492492492492092492492492416596492490c014924924924180924924924800020820020926812424926928d2c1241249369a492412412492492490000492492492082092692492413412492492482480410410000590492492082092000012610c000024924924824806d36d21004d205a51040301448108249241009a092482010090402010410400402492080402410000410410002092482010092400090410400086490000402490d92c100804920b205949a4924904026824924904024906924924900921924924920124004104904000810124d24100020d249248201643649040201248124104925125149249349248308249249249209209248249a4000124934c208348149249249209200924945a4924924804014924924920920924924d241241a48208000248149249249209204144924a2924924924834820820926800004484492494524924924904904924124900820490924924936936c04024924934934800024924924d201009249a49a60001241048000048249248241001200a4924924924d34d20c309249249248348249208269000041241000201309049349248048049249251201009249249249249241041249249249049049049a41200009249241041241049249249049009249269209b48249048249048008200249249240209248249248201b4830c20f34c24926924920804904b269200009241041049a41b6f36db6db6c249000040269040920924924a29249249249041049249249241241049049248000249249041049049249249241240224928a4924924900802924924924124124924924824824904100004902924924d361240828924945249249249049041041249008204908924928a49249249209209248249201040921249249269269249000049a49a4924020104904904c000269269000049049a4984820124014924924924924924104124924924904904104104120000824924104124120924924904900924924924030124924924924924820824924924920920924934924000124924820824820924924920920124d24d24135904920924924904104004924924924124924924906024d24d24924180904964d240001248208209248249200008049208124144944a492492592000092492496480402492482c900004924e300019205209249040648025145128a482692092430010413d93486081492492492182009692492492612492c9208209205249249249049249a4820824812d249249241040b49249249249029249249249248245208241049249204001249249248105249249249040249249249041049249249249209249249249240a4914820904124924812420c248269b4d3082092092493482092000082002092482692682002490482090482d9ecc36f3cdb0904124924926904104034da4d200009249249a4000100924936802d249241049240b4924924904902924924924824820824004924920400120924924824d240059249205105249209040248249249041249049249249209209249249241240a4914904120924924812404924924924d34d36d80c041249069b08209208924a2924926d340000a4924d34d041049240000001640a49249041049020a28a24a2520924934904102482524924924904924925820824814924924926000554924924924814924926926924124924924934904920004924924b200209009249241a69a4d24c24800024924924900534924924800024924924904104924924924920924924924924114914820904124920812424934d36d00006924924920820d24934d341041a4924924924824936db6e36db6d84924900034d34d04904920820000b2055482002000401010c024134120924920920124004100104904824904004004906d30004d34900020904926924184c00104d048000041249249041200049249209a69a41240248205349a498602c8249249040249049269209b0920924d25936124336de6db6c6cc149b6db7986c36c16db6de79b01b0db6db6db61b6004100820924812410512714934924924830824d249249211208249a09a0000135920820834814924924900120092494524934924c040149249249209208008040000248149249249209204124944a2920924824906004482494494524124924920820490492494924924924100d24924d241041249249249248249249249249049249200241049249209209248009040008249200249040209049001a09b48249209249a09048009841a6f34c20026126e36d200048209249a4006f001b6db6c000209249269040920924a29249249249041049249a49241241049b41240000249249041049049249249201240224928b4d26924d00c03934924d34124104100820c04102d249249341240824928945241241049208204904928928a48249249241040920924929249249a48301249249248208249249249249049249249249209249241048209249041241249849a6d24834920124804104924004d24924124100024124104924124934920924000d24dc6d340209041249208200041249249208124249a4925930100924924924da5930000924924964c040249269ac980004124e20001920900924904064804924924924100924924924924824934934d34c00025930824c24925930824800b68f2410012002493c900924938d64c000249249248269a0924000024d00164c00024924825940000094494924d35234d39234124934924904044926924da6905920824924925920820a04b6ab2400016492496480002092492c900524924924904024924d34924920934936db49b6d04924db6936da416482092492496482082002d9ac904000924924b240249269a49249a6820030db0db0de6c2c98412492492c904134005b459200009a4924b26000d0c134b66804924800b00c00124105248d38234104940d04034004938da4d86900824825934920000a00b38b24000166d24964800020024926904924c3593496192050492090402480412002c020804124924920100934924934986d041048259b41209249249361a412082412c92c9040009249249a4124900164d24864802936d24924834024924934946934800024d249249201008249a69a4000104906c00034824024924100d20124924924904024924924906104924924924d209249249249a4124924936906104924924d30c30924924da4184124820900124934824824924d24d20c309249249209a6824906180db4db4d30c40934934d24830c025249249249869249b4830824814924924924124926d20c20920524926d26906104924924924924134924d24924d20924820904124934830004924924920814924924924100924924924184124924924924824924924924904924920824104924d209209a6980d340300248208001868068269209a69a08049241b0826c209a41049249249a4186101136934c00026924926900004334d2d1a0104126d861069049249b6924124134924db4920d20800900124924820004db49249209049001349258348141248241009209249241041a4124924924824824924924904904924924104824924d20920134924db4904904924924924124124924924d24900004924924924030104d04904800000904d00004904da4134130180804924820104015a66db7366040124924d24936924124124104d04d20020124b249261041049269249841004a49249b4900c04924936da6db4904904900924944904104902924924924824924d241041240a4926da4920c049249249208209249249a4924824924924924924124904120c24924d04000924924924102924924924820124924924820824924924924904924924924920924924104820924934124104d24924906000064104107184924100004904904124134d34180d24836104d24124830d24924926820020124924900004924d24920000864d24924000024924904900924920824920824924824824824924924924124104120024924d040009249249241009300249249849041241b4d26100924836120104124906d249a4824920db4934904000db61b61b6124920036186db6db09209249048200040249248209248249249249049049249249209209249240209049249241240149308208369a09248208209a6824104924124104024926826820824904d04924904926c008249209001049049000049269a082492092490402012482073ae36e36f4ac24804924924800024924924904100924924920820924d34d34924124834d34d6483012481080082000c9a0104924d201040208000208208041249349249048249a6da4d2482082493693492092c92000482c9208041208218248209248249249248201a49249248208249249249249049249249249208249a49248201209249249208041249249261809241049b4924800004924904804106924126920820d24924d249241b6db6db6db6c249249249249209b6db6db6db6c24924820926924920800824c24925930824924924924126924924934c349259208209349249648028249a49248200209001249348209249249249049249249349b6824924926924d20924904130d34934c20004d24924d20306f08f38d86004960034d34904b04124934924904124d3493c3019249249249241a4820da49b6da6800024124934900008938e449200009259249240249061041249049240001009241041269249249089200069049200008209248241248000201248041269249249041048209249241249029240001049241249001241248249000040269049200008049201048209249241041209248248000249249209000049249249201049a492492410412082492490082410492492092408248, 176473902289088, 535719680387928928508262249315211790043800904100680798194342126502350872680351353718441731798748054596, 72576635240513, 72576635240513, 2928712461445908185002432382697755260693117934402, 176488934674624, 
    75815711701953, 79801307122497, 88597131708993, 106105088839872, 106105088839872, 106120121225408, 
    15015491880075510186898946187753574751556412114141009501157290458110295674639292416584694498377759973325484679858805799723969723490737781130176123771299197292699552381596896654966451351659275812832828198638481167501254231887237666809210384485435327259870216246197512, 315644150232281319585688704440047274065724013520331876459065755326633320315834625820092725894961131652, 581395120223413659886869390627426463909128703296510162803564572373518361470654454492263457341803032708, 123695392498937389873713026031008379330873147599292021254716145819189694294113370892888727216937027601078762810012756927741905225260625999316449695889315624205286446057434694, 75046241444289, 88614377704001, 
    88614378162753, 6766436808714252632737273865956557597569202668128533978826908726598803611992413954778805629476373320047573216598054496145768205916791936412635906316587934156168959734803823880171532508322662095690684534984234228246276075404903871312826147980730520886577197191195875103783151735899901467233207010417833512082166915104164751462828749422511552396261243248782819027484657259203953739, 176489337327808, 143516631045056, 158901044515008, 158901044515008, 
    158901598163648, 158901044515008, 246842581389504, 246842581389504, 51381112945375625460657926278988331512219330371, 2928712374333621279683420232168416862858240857922, 
    176473902289088, 246842581455040, 176473902289088, 97053213341854670943921207492707819102463333186, 97053213341854670943921207494865043340079928130, 2928712374333621604203211830634429026289160558402, 
    106105088839872, 176473902289088, 246842581520576, 736459918337267226897142980726781806680328902466, 246842581455040, 176473902289088, 
    176473902289088, 97053213341854995463712805960877206770999628610, 106105088839872, 106105088839872, 97053213336538205175016370549171180941791487811, 246847010574528, 
    106105088839872, 246846876487872, 246842581455040, 106105088839872, 97053213336538205175088906375057665178942326595, 736459918337267226914435455504128431309451171650, 
    106107236323520, 106107236323520, 246844729004224, 246844728938688, 106107236323520, 176476050690240, 
    106107236323520, 176476049707200, 176476049903808, 106107236323520, 246844729004224, 246844728938688, 
    106107236323520, 176476050690240, 143490701856960, 143490701856960, 158901044515008, 106120121225408, 
    106120121225408, 246857613906112, 246857613840576, 106120121225408, 176488935592128, 4271982446720362678929490552409326234582905009315688334122046632055282832463910806957539511283865285, 
    4272742766112970863757579415470423357565237917123566944636124662476265716750659562135333145765074629, 143228847268673, 145689725112512, 145689725112512, 158883864645824, 299634913186752, 
    2928712635670479399483337662181333999621249176386, 2928712287221337619561115135868052714890182267714, 73135779483840, 290839088600000, 123665259711913420370712330660723045920375066272762722792612405426671465952784306927935906448863087380884105541961280486000954278974625379023493718242036543539143828633024582, 423201418669900436894417346185342967410023744323, 
    468873519061063016608775790455525957577621128003, 308439881094080, 284252772766656, 290847695049664, 308439881094080, 371085802077566301694106769168011028512028808002, 
    308439881094080, 123695392443150858820748899887423351101132307054565268552766093658242440827669435164447072354331192915657762337793580403624261472104201492538901389108252674512484253374085190, 366090429708556802465251782354390361484608688962, 371085815688840209422975101621124966807578366786, 2207891062849, 16611463205385845350240742841008783679067940038725230171725206270922124447388264516427401581822509508, 
    176473902289088, 176476049772736, 176476049772736, 176476049772736, 176476050165952, 176476050165952, 
    123695392436852379508388424951488597190394651499170539944560793554970187448512661530917438987332575687947553230095259101970544988183732519253840532112740455086381884541712455, 283815877546433, 73121888473280, 73121888473280, 284228328624576, 73121888473280, 
    3957920452942559774011439111213755252686269257527929192149412905855699754193710145100742682950678823764154570270101304172962907019650316529246160080122319746648494769478563398, 73120746639552, 73120746639552, 284516628325185, 145689725112512, 145689725112512, 
    2207891062849, 72670922213441, 536757350297632015557065429965716794350645091018284442124589173478570895517717151593292361194990223492, 565226563962945, 565252131457089, 72670922213441, 
    72671391975489, 581110165803712, 581110165934784, 1464361729691402895160015768674762119416280847170, 72602404061249, 72670922213441, 
    72671391975489, 735038153274139525203751994769350037710166921794, 567916026270400, 265751090771077031726494845045363044277985876845089954931336330694022152937812004578622981429587266308, 567919386825408, 145412703924673, 
    563508853871296, 563517443805888, 563517443805888, 1464361740580438636629737113312336591446727529282, 1464361740580438636629737113312336591446727529282, 581101039915712, 
    145412703924673, 581101039915712, 581101039915712, 581109629850304, 581109629850304, 572314072781760, 
    565252131457089, 1096172223465924855102190768643887475217028634434, 847200578180032, 565802424617537, 565634720086465, 565226563962945, 
    565226563962945, 565252131457089, 538834321680677798773598620115276163213045110872527081709825075604588176197499980136157002477779304580, 538834321680677798773598620115276163213045110872527081709825075604588176197499980136157002477779304580, 565252131457089, 565802424617537, 
    565802424617537, 145702610014400, 6059625031706314223707550154661728396192740636449871314918306649817884444022675186291152654844532043355990048385154516023714760346726880324934587010969510043391605279501012550, 2923181724870736943724769552151322256780935828290, 2923181724870738241803935946015370910504614630210, 849377322079168, 
    145689725112512, 849398796915648, 572322663109568, 73120746639552, 73120746639552, 1462220839091132028457958050653357908828440512323, 
    145689725112512, 145689725112512]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x2498010402c904904924924820804924920c000200209a49209a41009249248208040249249208201248000201048249a4100804920924800020124804924000100b241241249249248201249249248008049249249249009249249241201249249248201049249249208009249249241009241109a69a08200008249249b6c20820184d24d24920824924924934820924936db0c20061964db61041200000208201200600301b01040209240000048209248009a4d008249a49a4900c0004780410018013ae64920820820924920980135134920000804d30924904020104e34924d20924920004134924120904104924904804f300018059209240019209243249000040249009249649661809a79e4964000024934d259258069a6924921800da4924d26201834924d249860079a4924900004920820826924824004935134830c20d24924924d20834924924934824924800904104904c24d24d24924120020820800000004934d28906100184928d349201249259249b4304924936d0610c9a49061849b6d86804100020930904820900004920924925924804024924105904920924800020124820820924924900920000804d209248249249a412082092492490482082492492412cf3c309986b20906f300018079b09b6000d30924326d8000402490c9a61e6124000306987985900000c3c3040069a1b36de6f60f36036db61b6c00006184100000004b30c008269a092c800060164c20924820824924924020924904004824924924920904924924924120820824924924120820924924904104124924920b2c80006012482408, 563534145012289, 563534145012289, 563534145012289, 90744144611905, 70952935768641, 70952935768641, 
    70952935768641, 563534614774337, 91366501614338898914080676127645201571923367746, 563534614774337, 91366501614338898914080676127645271939325368130, 563534614774337, 
    563534614774337, 11451432787134444715784545940866033436233568834, 11451432787134444715784545940866033436233568834, 283815804145856, 8304733930652938607698653482023569652679522766682352961665499681692860565896535569000761990077226692, 11451432787134444715784545940875005451116220994, 
    16609451526312730749257019139755621499183353105004212119791240419460840353791592869667261257506690244, 11451432787134444715784545940875005451116220994, 11440630821309764079556171128527841354575778370, 563534614774337, 563534614774337, 563534614774337, 
    90744144611905, 563534145012289, 11451432787134444715784545950089405438997041730, 11451432787134444715784545950089405438997041730, 563534145012289, 563534145012289, 
    563534145012289, 1135254622585665, 2928723415815867998090976523802380808245504672579, 2928723415815873190407680785032377043863486890819, 143091269898432, 143078384996544, 
    91366501614006591915148944879870617561723835202, 182710702396331751036856703677606123433961198402, 91366501613923839368291336046768942677200212802, 143078384996544, 283815873351872, 283815873351872, 
    283815873351872, 143078384996544, 143082679963840, 91366501614006591915148944879870617561723835202, 731467230115671196968166887104846162481666622275, 563534614774337, 
    563534614774337, 563534614774337, 736459858447570324292259325925985831132153807683, 129777056292194962637718395595851078983462307159534998860830360605859770513949921767314671251017476, 129777547423926009027780781104177171385278515580803939357287225289307232585037654894281691150470532, 283816011764160, 
    283816011764160, 424828382220736, 563534614774337, 563534614774337]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4da483c906db6186d8cdb09b6d862381b6c24d369a0c00020236e36db0db6036f36f3618c00012402480c904000800820026100000186184834904104026904db41869869209bc000100924136c00124126806dc6db6f07a40db6c30db19b61b6db0c36c37187980000f01980da71c6d04000006dd75862390069c6dc41318059371c71b61800069b1060d86e309a8b060301e6c20926936936f241b6d861b61b6c26db6186d86db0934d26926c00808db6db6db6d80db49a49341a0906db6db6db0c049249b49b0000d241061069a4126d800040249041c6d861b61b6c36db0c36c66d86db6c30db0db61809b71800000369b71b41000009a6db6200c301a6db7104c30036db61b6d86030f36db79e61801b6db6db6c001b6d801b61b8c29260000c0d7308269a0c0403cb06db41849069209b6d060201a48049249a4920804d349b49200001a49a6924924034d24d24904004924924920804124926924820034d24924904024900180800820000030dd7206104006126db6c20800c36db81b4100184db6d30820806136db6c308201869b6db0c20031934db61041200000008201200300302301040000200000048209a6830100f2c1b6d861b6236c26db6180c06db01249269a4c20134d269348008069a4924934900db49249261200249249a4c201069249a6930800924934d26100d24000000804004800c379e618410018cdb9a60820040db6f36d34006164964834c20184d24926d20804134964834c20104d25926930900c00c0c0041001841e99808208000201a49b0d80184db4920000804130924904020184e34926930924920004034926130804106924904c04d3c9b6b6d9b0db68309219341b6da0c24834d049a79b6964000046dc71b71b70069e6de4921800db6db6db62019379e4d35900006930c30c349b09a68000201b4c20000800926c36006136d34830c20184db4924d20806136d249b4820186db6db6db0924800100104984c20004d24924120006020800000000c271a89061001849a6d308200309b6d34984006164964b65800c34d48d061009a4d24927960030dc6e461861a68001809b6d848000000209309000048000009200009241048040269801041a4904db00079849a09a60001009241b6c00124124824184000806c20db60001801b01861801e01b0c30c30db6db6d84c30c30db6db612cdb0007986b20906dc6de6d87a30db6830d20d341b6da0c34835101b36db79e00009a61b61240000579b6db79b6c069b6db4d00000c300040069a1b3cdbcf61346036db6db6c000061b4d00000006b30d849a6a209a490016c1e4c209a60001049241b6c001e61a6826980004034906db0006d06b20800020904004836d80006006c040048249240209248000201a4c20004004904920b269002641a682408, 581126331056705, 581126331056705, 73151959024193, 581126331056705, 73151958567489, 11440325938776708879716073214513810158104118083, 
    73151959024193, 73151959024193, 581126800818753, 581126800425537, 581126800818753, 469219808792227002373687925420293652424159928649468681277453441047704230390403543294155844452294355087892956425588148681318860602331225542973921526949798478173475459120949814307078940769840931061776860806709887789510658645194703383743243965900707850092553246156552, 
    581126800818753, 581126800818753, 581126800818753, 72709571612864, 72722456514752, 72709571612864, 
    72709571612864, 72709571612864, 72722456514752, 581126800818753, 981485938198129445952565290611119015062394574222794697707348949635771946069391345256785930324548219589945821444828182132140123144476351561225992803877949866976500593083830397340895516666585963452518966017070035810525229116353060504464200417373280593516691464245997512, 73151958567489, 
    581126331056705, 581126331056705, 91388802444275714268525096463978473499658294082, 581126331056705, 72709640818880, 72709640818880, 
    72709640818880, 72709640818880, 28545041147190562006388805607453408801539000131, 143078384996544, 283815873351872, 143078384996544, 
    143078384996544, 143078384996544, 91388802444275714268525096463986917781171868482, 182733003226600873390232855261722423653409231682, 283815873351872, 283815873351872, 
    283815873351872, 283815873351872, 73152495438401, 581126800818753, 583325823615553, 0, 
    581126800425537, 581126800556609, 91388802446934169972912257540783189965320237890, 182733003229259329401629146081148888824464552770, 91388802446851742233048336287469556724085569346, 143361995444672, 
    143361995444672, 143361995444672, 284099483800000, 143366290412480, 143361995444672, 143361995444672, 
    283816011764160, 91389499366447733741321569958191511415398938434, 354747398755264, 581126532383297, 581126532383297, 283816011764160, 
    581126532383297, 581126532383297, 73152495438401, 73152495438401, 90744682007105, 72710056055488, 
    72710056055488, 72710056055488, 73152495438401, 581126800818753, 73151958567489, 12845278330802008872723117017785090653548479043, 
    11804813857773979614755196014476642063957793862915126836458324986019588655989242666163980876291247742631575481430400239823499572253017740167973987826791735436029593611486824995771654736794393380326526545334300659833208857332700605806599778634803874287880023033335594737031200248305678230375940188187636544378869925808632634830921473865956728167554608954384808490639162576052628554, 91388802465543362201374498196869793484747380546, 182733003250526977492915529957965472362708154178, 123691028792797361560258551675728934420908892118358658238831916157607938069551762789541321337209733052695882156314494280986953670293440680276056388573966919635086407544815175, 13206933071602446336550894114957137148539673951191151661899749706387021787482249241011159505491573424931676790607059198121632268867105664712429670551113320024599126981157101872085812307893844205011378296852218992539771822361578107310729931569553205833764415238334565277728923748940047703021291854839621711019983915745588437818056712795566792441681471391373655242205966379328916426, 863690695288658164592981944579899582493124273280552962250267840554589916195111809962988175477196669060, 
    73151958567489, 581126800818753, 581126800425537, 90744614898241, 532410317973131812080648677752118156376815261219291186038797647437099396150726205138477694901744320644, 182733003226600873390232857549118688793393632066, 
    1101836620742989203133207196839787368194401948483, 182733003226520392788925567716264780081863332674, 73152428329537, 581126800818753]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x26db4936decd209a4924924920804134d35100000824924924924124924924920804924924924820124e34104d04d30934c00020134806d30021804930d26000b209a61a4c00020134c3498002c836d84d26820980d80126d34105000c20db6830a30db6006186db6c36c36db0c28c361879b0035904d60dc7800f30de6120934c20820934c24924924924820104d24d340000209269a49249041349349241209249249248201249249249208041349249241009a41b6d31820dc6c351061861a6d86f34f36c379b0d349b61b4c00030984126d800081b69a79b0c00836d34d36c041b6db6db6d86049a6d3361b6d871b6dc71b6180104db6db68001b6f30000c08db0816134906d80000c00800e04000184d241a6c30000124930d26106134924924d00c36924da4180184924924934800020d85100906134926db0c00c37934e46186120004120000120000000004020000124006c04c000219041001005841869b69048000000001000061041249241300249249249841001a4920926d049318302379b6184800100db6d86c000300001300001041269b4100024824924834024144104920000905104924904024124eb4924d20924920004134924160904104924904c0d1a61041879a61369249249261008269a0da0000184944924d248009a69269b0808d24924d261009b49249249840309a4926980804d30904d04135030024124d24934d20904938d24934824924800d04104104c24124124934120184da09b8d840309b00309800001349249241000069b6826c301009a69b6d06005820834d378261a49841849b8d848000000309b0900104924924100c208369a6c04024d34104904d30934c0002013482082092492490492000080512092482492492412082092492490482082492492412ce3c207a06f30906dc6dc7b079c0dc61b8db0db61b6db0c36c36d8cc361c01b6000180186d87980000c3c186006db1b4d249361348049249249000006186c00000006f39046db6db09b6e061e01e7020934d04134134c24820824924924000104d040040249209a4920904904134924120820824924924120820924924904104124924130b35000020134c241b71e0c4d036d8cdc6000180de60002079b6d88c0718000cc4180103c1c623cdb120820924924903cdb7230001008f30c0, 73152495438401, 6707465288621971031835132697190279390877547052123107247825090773972256777994121116798437386848173509973660817664628159842055867063324543920466853158535712435278139222606045962444596049495972841195545502460507647186625749270179761531380632314090637427429430334785817761851714426616033233377174332554616480009854906728384354611475908352998520626078673419983863434425587238785047114, 1128650909180737, 1128657620067137, 6787310963707271593047490618342430243421323160957026664142750599390248325869293334144208201536937793815349775578071734171764087409461491540593411500088126581294595862487591564884709751068069085743493973056260779659447470060588423854222008558442465940807252783513005705075707136154096898556956246676467066618773509889349488685820338958058531065129067243349538897240457091391292490, 7760525347272199341705156789529932210115349322908591399568390346757495377862136516055356765362915144113934604893347240797137422832018604985914503037669421473726647850991174, 
    2923059026705577860035993535773693007241471379267, 73151959024193, 1128683121689153, 565733168267841, 284258191557185, 565733168267841, 
    73151958567489, 73151959024193, 73151959024193, 565733638029889, 565733637636673, 565733638029889, 
    636102449384001, 565733638029889, 565733638029889, 3957316615499466468212719094225360144690030576193401326336176225563880792474660491750709789220521317904490689962216329872920372967147657015317969530776042648644147663859002950, 123695396123260585422513779322611143084594008737823888648488820666983576921622347887368783222057903019207773616799909268359534297135181945061858604790490644129921884907099718, 3957316615499466468212719094225360144690030576193401326336176225563880792474660491750709789220521317904490689962216329872920372967147656940881222046754477339130615685612744262, 
    565733638029889, 565733637636673, 565733638029889, 73151958567489, 565733168267841, 3958131796911442227299865864612431999304107343535334080602125508309095516285683046796553395950236807053290717152065605547380631224506822439245035561819907208537178779638790726, 
    565733168267841, 2923059026705577859996379454516559780847925888835, 531501965722252339719151636859109374009038628548458645621288762925965574117652089572644905425041379141, 73152495438401, 565733638554177, 3957286427485527111805477507569384677388265727109133885469174485938400837146355648543989569038032184035623952487150786971389566167876809028946180645693182702892724347738225223, 
    1128670504833985, 1128665941819969, 960962621259340297057677422063182199245840617938388148096835402268020387733275207765024462706128980588707503671014813324349295268446704631925299327998312358231314773816045950471307936211617807282735030474848144285478772487826135717043345540760678042798391304246988552, 284241213538881, 73152495897153, 92771453931595159638478330492603361684097110850, 
    92949859893183409694213017151702717515058680642, 819094724547689046692294113858450459903427921425627552301372002683041496736621848608300331865470707612729224595928737885511600770258654638204993113983254804979948209734076716881114513016452388274238236519192099719582715830741011680100977994820456621846293265759072786517254988920699233840460840788619087866117662981444183911569072217660949535941141455877211844017732347711562, 565733705138753, 284250340352833, 565733705138753, 66437805115251438498460996820496420607349404312803139216634408890439242835508994651390812884326572933, 
    565733705138753, 1427253137306948247696859085716632393096368706, 73151958567489, 565733638029889, 1891923037283693717032062335410709978026517395481973560092923343744026414596003938235769960261279574949235257365603165584074682316904356669091425511955122902409212505618803666934153616018217822599802088587052666134734194749625369073131816428338225267523747848245956552, 636102448859713, 
    636102448859713, 73151958567489, 636102449384001, 565733638029889, 565733638029889, 73152428329537, 
    735038153295407254265949365575100471625558102594]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24d34935a300009b4d26d34d84026d349b492010092d1b6e379b0c309a0820924920980004104006120984100d04804804934f25930100924d34924a24d30100b26a28b38004134d36d24844824926da4904900904024100120800000000024004136d24804004926da4900100524d36d64c04024934db6db49b0d20d24926dac9001049249b6924124104d04d04c000200200000009041249b6924024014d34db49201009b6d24926124126db4924d849049a49241341349000001b69349361041069a4d24d84100494d34d24924100934da4b24184134d34924934834926d249369059b69b49361841359b6934f24104124104124924120000004800824104904924904824920124920100524d26da6906104d249b6924da4136db6da4db6904d679e79acd249049041049249048000200200209049249249248240209a09249208061340040000008248249249a6180c00d04d86020104106c00000986186db6d86c2c1b61b7a00c309a082092492090000003400412082482492482618610d134b00800d34c241009001341b6004824004134d24804004926da49009040309b6106004100c371d6180004104024134920000000800804134d001249048249200249201000041341349600301b6304000120504106d04d04804d24d00120904124924924024106da4924d80900c349a41b4120d04124d20920904924924924824000104d04d2480000798c10000480, 145207477735616, 145207477735616, 145207477735616, 2923059026705577860313292104573617131222101690179, 2923059026705577859996379454516559780847925888835, 2923371237138357288720360954572377351454170588995, 
    565701426299457, 565701426299457, 145277408252096, 145277408252096, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 145277408252096, 427027405476288, 145827583496896, 145290293153984, 
    145290293153984, 145290293153984, 145840468398784, 145290293153984, 145290293153984, 145277408252096, 
    145277408252096, 145840468398784]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249a79a6006124926db79a61801649b6da6986c04924924d30100924934d24824846db6dc9186e049040241001201b6db61b6000104900124824804920c04a009005249249e4980904924d24db6db6db61b6124904d24c00c06db6e06d800048149249c6924224124db49249241049000301c6db6db8180120494925124924100924944924944824e249a6db81861349249a6d289a61341041249241200248201b0000124904924904820524936db6db6db6d84d24d041049249048008000048008048269209249208049341b4d00c30924824924a24104000d351b6c24124106c00000a26db4148d80c309a08209249209000000040041009248249248241b4109935180c04125024100920104820020026104934d248048241000000000001040000208001841040241349208248201200201249001249048061b00001b00000041041449300249a6186030104920034a30900524926b048009049041b6f209801841049bcc36c28124db6db6db6c36020935904d04c0080698498080480, 960962621521537293379979556454214614816879939158999368111922360097167671287111974086245154287976443772186300180164100333240201567448050508407135749937076602727591508392418692617335607918771078939298960964473806393203537879860813043396254518789519043813442057246991112, 1130861005534145, 531566893848442985190982632027721153298974477039181845727692407481501007018660946012629567639888556932, 531566893848442985190982632027721153298974477039182200872590278890944639315755260370169481374003852164, 531502060762209460540526932838284008223569222564131113543963862755709990040225088294634811120303936645, 562967687992000, 
    299634913186752, 299634913186752, 562967687992000]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14db79379b60001351b71b79b6000126a28927180804924924d30100b24a289ba000124934d248440269b4928986804904024100100800000000020104900124804000180020800000536da49e6d80004d2492c92cb249800049a6d249361a0104d04904c000201208000008048263249260200149a69349a8020124e349241241049000000309b69b618010092ab26e06000494d351249241009a8da69a61861249349249348269b6f26a36b049249a69361861259a49a6da61861341041249241300000008008201249049249048208361a69b61805269269a49861849a6dc69269ac124936da4db8904966b36da4da6984d04104924904c00120820020804820f34926da6026a20924920804d041c5900000924824924a26134c00934c06024924106c0000092cde61b6e00c309a08209249209800000040041009248249248261041089651b0c041340241009208280301808001049041248040001b6e208008048248201080001208201200308041040241349200000008008001049001249058208341209a0300004134144930000000000006100020831220980520920804020004826c269260201209008240009000241641c4140900120b209a0a04820d24936826000104904d24c00000000000184000838c3882600, 1130861006058433, 1130861005403073, 960962154310961563796381349092987140300534773651272601109761063753628270890533113124306455439617455967588188662125391583243788144481475754480825080846446781297179869698504627824979610632529512033688914217177329333396545536339463755614266714138011686066471172249837513, 2923192831687194541621695782678886395318913520451, 531502440922011507987686434078471823144490727441255193011203247165108951455453122644695538789370259717, 125691878918129693493783394816696916882606847555, 
    567900449555393, 567900449555393, 531572897205346960813053586246472961869587765350608661900433813730418093169203568008606169196654773124, 567489873318080, 145277408252096, 72710056055488, 
    145277408252096, 72710056055488, 290413358355392, 83984072577472, 514202380385463515241139586161635078410688986624763101920421075198042071779084697497216874400286692569397115670143843515082581651371729116946872756556354465366530458635846, 172503365325760, 
    172503365325760, 163432654443200, 581109629850304, 163432654443200, 308705900893120, 581109629850304, 
    581109629850304]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14922924924924d20100db6db6f380061249249248248249041241001201a69b61361041249249248248105248a49149249249248008069a6d84d841024149249249249249249000201b6db6db6186120514924d249241009249249249248239e7964db61041259e6924f249241241041249241201e79640301041249049249048105248a4914904104d249048061e59008041024269a09249208049a41a5900c209a68249249a41a4800924934824004006800020926db41a99008209208209249209000000040241209a68249248241a4908924900804d34c34100900186d34066030030d249248048061b5146d80c02187934186000030db6c060060061b4d061818041040041249201869240200200001001249048200040041249201861343060001105248a4914820924904904806184d0c98000240, 149605524246720, 149605524246720, 4081435634987215259147902240561829092450605837772288908711909046125484282167616829695328326869657935732542189527043426390243426910066846590186962430904486230976931596154697798, 290343019090368, 983484711733143416758284759350834243573552108981590457820256009415469240541679843966623251808802090552781541883876702767808339915242059490529919089063313455901849113010376268666431776592239513583375668921261202833323509312999558756812331353395385730156479512496988552, 581094589088321, 
    581094589088321, 79306641379520, 79306641379520, 79306641379520, 79306641379520, 11775143275264820397667391612402724349656699458, 
    149675454763200, 149675454763200, 149675454763200, 290413081530816, 290413081530816, 431425451987392, 
    431425451987392, 150238095478976]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12496da49269a4db6db0000db69269b6c310208040300001201b6db6dc618c134926830c35030512524db6db6db6db6124924d04104924904c08c67981006185826920924920804926126985120924824924a24104004820804820004120000100a46186db6031024926148984d30904204a38d84c20820924920900d04100c00000924824924824106dc6181800000948db8e06000004904d40800100db69860001b4126da6980006904134130000180934104020006c00828980006d849041008000001b69b6180000108d2898600000048, 91344201462890542310196355290660744747953427266, 531566814648484225306163577302677546008594848531308561761224158580391135107348483123674124676961156292, 72709571612864, 72709571612864, 519076537507080908344362193818004329642150064802537230771376243605042645409088071232959907757837892]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x245248a59249679c0000924924d34c040209a0830c00004004100000120424824c00004804924926924d24d20000f3adb6f3a0001a69249348308208041200001201a69b61361041249248208348109148a48a4826820924000034d36d248208109249249208201248a48928209269868008069a6d84d84104414924926924924d301009a49249248348209001200001201b6db6dc61861249249248248205269a49249208049249359b0000524924d24d84024d34924920d308a6db49e7930820900820924920900004104004120404104d24904804d34db69a0000db6d44b26104134d26926820836db51379b4104d34924924920db7934db6104134da49a6db48249b6934f241041200040069a4120db79340301040001009049048109a4924924824126926924830814924924926d208a48a40208249248261b6da6c060208141269269a68008248a4892800106da69048361e5900804104db49a69b01004269840040008049249000041a05248200000048000209a09a0904d3080080010000092082482c0800209a09a4900004134124120000826826824004104d049248000209209a4b06db0801830000504c34c30000920db6d34006c30136d268209068371b5100180c04c34924920100db7934206000136db4c20c048361b4d0c1800000040041269209b69340000200001001049848200040361b4960db61343060001109a4924924024126926c209048149249249201208a48a40008208248260000001048008108249041241201269268208068248a4892820820986904836184d0c980004c349269b010040, 149605524246720, 149605524246720, 531505989080216822504545441425927894600129048394091335845287042994591954481742645668229179213212825092, 149880410739136, 290343019090368, 92057827351270032357989517169260258875251103554, 
    2928723415986004638274329526957812464670444914499, 2928723417176992922497614149227198041214517552963, 79306641379520, 79306641379520, 79306641379520, 149675454763200, 
    290413081530816, 290413358355392, 150225630008256, 149675454763200, 290412943118528, 150242809877440, 
    150238095478976, 150238514910144, 149675454763200, 149817327096256, 150242809877440]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149228e4924924d30100924924924824836db6d36d86d0490412410010012693613610c124924924824804824b248043004a28a4914936db69361a4124d34d24c018049a6d84d8430212492412410c0149249a49249041049000301b6db6db6000120494935124924100d269a6d289a61249349249348399b793d1b6102e37934e461860e59269a6d269a61241041249241200319b60401041249049249048604a2936db6936da40a4914904104924904c00c67980c041038269a0924920804d041b4d808209248249249a4124c00124c04024d0410680003092cd04138d00c309a0820924920980000004004100924824924824124107924c01804934024100920d269a61200201249041248048399b6db0180d02e379b620600008c336d8c3018041040241349201208201200201249001249048001b00001a0100004124134900000000000000100020820820b004a2936e249360240e4914936e24936824000104d04d05800000100000002004824c2482c00, 1135254622716737, 3957316621027680774542082373564540321482664065521719412090731549915495369561945031466348726599268933136967068562803597910521654087075697734352808232621123914160736946047909446, 531570869686402707761686297389117202236281552858089490700227594933126821163870356277668544982762562436, 3957316619184925684297189135165343748734485873947333919467745773701685480151136059254356671545768756957589054654312539754863293613874907849095359872841232727821546962118729286, 979746076449939809731335274314589080849127594013935360025482241992544157271737945857433326421343175310091858839748602122331494967632477299995305376773318972826776361362979386265140824060174366886834367144101550147460798922570102416350964476954704597015855656499877512, 818984051495632020652039655804615544499890324135165325949095874018110009116439897787280181456946962979382062940661865460795932606620142447798992006196616913156283766016757935581726493664518381453554146146679003096453821996860296043524230668236311529215818453959224023455827998583621564323704596776312554637487002614981868193292652891548765568418979893834533498121142685418058, 
    469687317398635759755275189391451669165155153116673744159535664390165911623069412878086764629415261746033778871968850124827492677707250147112221190204053172295794035619648261005321386151137935471891129579976207442769404593427796208712601255838565663769128499877512, 3353732746053689577403148970731478088170981789197854567558981016789814358045213061831964934684629118667353939146196299676736199590153173525366024640020399429450048725997384248372980919151216826588751589376765966970813487412548250744329427883491741743384766494242342479021587839918389494082594308015028117509360775924667086768389660015823701208889097465373568765621680147916931658, 480481544559208298773773550902776623958610614004884674759467982113444144456949614850118468986724879538371207454775726776024241170745538807907726679283009133647659636195720204204554668936132633849374265301077114728323286195092126869827563720679305867981488680499877512, 290343019090368, 581095133811392, 531566814648484225306163577301891393959875876369159785164467980674765342921701774333070150214625803460, 
    1135248247907137, 572298496066369, 531566814648484225306163577302677546008594848531308561761224158580391135107348483123674124676961156292, 72709571612864, 72709571612864, 3957316619184925684297189135165343748734485873947968533197793647201883748957865419333530142843195663281826603584564668709830788875181056312579598349864052793147435670730399302, 
    72709571612864, 145277408252096, 1135263213437761, 290413081530816, 163419769541312, 581096744948416, 
    581096744948416, 72722456514752, 72722456514752, 3958041221582930242412316992220802673878394518160826139846580469297350018351820479952846069080365523882981808473566601705747663874042362532865291550677479541699110749350100550, 72722456514752, 82068515066816, 
    72722456514752, 290839088600000]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14924924924925924921820924924924864824824926900004925930820120924924924804804924924924924d20180da6936d36184124924924834824924934906d04920820000da0db6db61861b61249a49a6c048209249249249249249219209248249201841241249249249249249241a4124904934000836db6d86186d848249249a4d30100924924924d24d200009249249248040249268269800041241200001209049209040048029249249248348249249249349248308249249249209209a48249a4000124904c20804824924924920920124924924804824924924926926900104924924924024184984904800004926980106906db61b6db01b09249249241a40249208249201200209249a49a4904820924924920804824926924820184b049a6800024904104126906f30c30c36db0924000100924106db6186d86db0d341b6db6db61861b6db6db6db6d80006d86db6000836db6db6d80006de79c6d80006db6db0c36db09b6d861b61b6c2048, 243420576429546975486548347881097322600702188721975096977029226645937522675705709088721150500212735547643404717473897717746653301778246382588337282814701174905486609803334, 243420576429546975486548347881097322600702102076047155701564864747138148387095483617604733599980318541178401519335823080861763012585429857347179328460523390475138256922694, 88545121813057, 88519553860161, 651602460414656, 299688867926464, 
    88652490215616, 88652490215616, 299758930366912]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249249249a4d359e4931860926934d24c65824826db6d80004d359b0800100926964d240040049269a69a69a4d30000da6936d361841a69a6d34c30824924944d06d069a0820000d20db6db61861b61a69a7030c04820d24924926db4924921920924834d30186124124924924924924d341a4124b069b6000836db6d86186d8c8369249249a0804d24924924820126db6db6db6180db6db6db6c30124924924920808e36db6db620092492c9248201a5b48b24908024800104126900820004004d20904000100a241248001241408079d6db8db6db6db6181a36dc79b6d8604b5eb1e6db00099b6de0c379b19b6c30f6133a2671860301e6c66d8003ac6cd80da49269268201369249249208049a69249b48308249249249249a09249249248201b4924d24d84024924924920806924da69200009200041049a4236db61b6c080249000040209041a4db69b4c0602d3379b79b01809249a49b6934c00024936d36d00106924a24d30020924924d34044000000800034804906d80106900824980000100924924d341840249a6d86036d049a6830100b3c1a6986030134826db6180c06c30c30c401800061009801000048069a4180c04da01300001001a41248001241308249a4d86024b06db6180c06db0906db6188e06db0d341b6db6db61861b6db6db6db6d80006d86db6000836dc6db6d80006de79d7180006db8e30c36db09b6d881b61b6c20924924924830184824924924900120024104100120104900004004904934da000092092683418092c1a408, 73152495438401, 124540760033609317283011069906777433309309331109417141642192466939757901614809833909998897802112269627676696627853743876201584784776631160627210187980631736464710439516230, 124540760033609317283011069906777433309309331109417141642192466646261750651094059020653503333903852370685521420690961949293117156246795598891749683860669025049364510783558, 73152495438401, 90744681941569, 90744145068609, 
    159038483468480, 159322110694336, 159039037117120, 159038483468480, 581126800818753, 581126800360001, 
    581126800818753, 581126331056705, 581126331056705, 581126800818753, 581126800425537, 581126800818753, 
    581126800818753, 581126331056705, 94198707079452854785805611489279266655878320962, 581126331056705, 159021303599296, 159021303599296, 
    159026152215232, 581126801343041, 581126801343041, 159021303599296, 159021303599296, 159034188501184, 
    18151086494400, 185542907863107242071967655474533528196777849666, 581094320652865, 651602460414656, 299688867926464, 299688867926464, 
    88652490215616, 88652490215616, 88652490215616, 88652490215616, 299758930366912, 299758930366912]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 0, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨3, [], 0, [0, 1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_13_0
  · exact tv_b11_13_1
  · exact tv_b11_13_2
  · exact tv_b11_13_3
  · exact tv_b11_13_4
  · exact tv_b11_13_5
  · exact tv_b11_13_6
  · exact tv_b11_13_7
  · exact tv_b11_13_8
  · exact tv_b11_13_9
  · exact tv_b11_13_10
  · exact tv_b11_13_11
  · exact tv_b11_13_12
  · exact tv_b11_13_13
  · exact tv_b11_13_14
  · exact tv_b11_13_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1252492492080490cb2c92180db209249249200201249a49a406c8249249208049059241808059209248208201241000000201648249a49860249044845129249241009241249349348049008208208049204200000201248049041000041044904929249a4820124124924820124824924924806904924924900d209249248201240a49208208049009249241009209248201809ac112092524924904024834924904024904924924900920924924920124124924904034814924104100920124924820104124904020124812424924920804902924924924020114924920c24d20524924820934824104c24924d208001249249248249a00269249044849249241049241449249349049025249248201248108241049269204001249248248000249349049069249008249204909249a48201a4124924820934824924924906904924924920d204928a000492492412082080482482c1b6db6c30c36c12124934904024834924904124904924924920920924924d24124092514000924924124104100924824812424920920800904824924924020120824004c06920924934004d249208209041349248249a01269a4900824024d34920902924824820024120924924900804924824800800024924920024130904130d34934c20004924924d208208009a49a4000136d24934824124934904004024d24924920100934924904104904d24924104124120824124924904000924924924134d00134934824824926106d06da0924800124146824100820d26c209248203009a400012092490080412692492490c1048209249241659001a49b482690248, 35751442124992, 35751442124992, 5709012570246128593160424297542081653499761474, 72671123540033, 17127037649345234683319261330543580319475312451, 73151959024193, 
    91433404124752454971072644254356169290638431042, 90813401418305, 90813401418305, 853797648470976, 183050877158176070545050561016594388340183219778, 853797648470976, 
    366090429719180931125303793857215068650942256962, 366090429719190666996350316642116839174364484418, 366090429719182878244053384655593892245674152770, 853797648470976, 290821908206016, 290839088075712]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12524d26860124c24820920800904904db1804db09249249200200a4820920800904924f318049209208208200241200000601248249a490c024904934db1804930482534d06030167814924100c059209208248200240001248001248249249248009049049241001209208248200240a4820820800900904124100120926820180b2c134d8c020166814924100c05920134920824824904d24000d20924100824104924104924100804920000104124924020934924934820824104924100125800d34c00124920000804920824824920804902920824924020124100164d34c144a490400592492082010416492482482612c9a49044849249249241009241249249248049049348208040009249000201208340241000249049249248201248209209a4820024020124800134824820924906904900920000d204209a48009b6810824920024d208a080410412413082080082482c1040000000008141048241a4120124db4820100024924100804820924924904024904924924920124020c20820106020800000804920100904000934126924924900920824820920800904820824924020134130d34d24820804824c06920924904824d249208201249349248248241269a4900804824d34920904924820920924134900034824902020904124924124904020124800004104924900824d24924920420904124934804960034934d02510920824820024120820924900804104004d34d60904024800000020004920004120904131934d35820004924934d608208009a6a24000136d24944824124800020904024920824824104920000804920924000100924020904124924800824104924100004924920920000924924924020924924924810824104924920104820924934112424b2480032c13c8269a6104c06da092682030092612090413013080412692492490c104820924924020b0032492882490248, 176476049772736, 176476049772736, 97053213352571288021877350616839643469805785922, 72671123540033, 72670922213441, 22925253517073183618693855505297186403796911939, 
    23014456838149654017439458418321364831040964419, 88064621873217, 106107236389056, 106107236389056, 317213676540352, 106120121290944, 
    176476049772736, 28545062747135879611908872398089292676868351811, 176476049772736, 176476049772736, 176476049772736, 176488934674624, 
    176476050165952, 70952935768641, 73151959024193, 73152160350785, 73151959024193, 73151959024193, 
    90813401418305, 90813401418305, 90813401418305, 90813401418305, 73152495897153, 91433404124752454971087151419531988168901399362, 
    90813401418305, 90813065873985, 92057827372287880865619395774788394329552458562, 90813401418305]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a49249200049269249a4d20134d249249860249269a6930c06924d249a0820926a26a240301a69349268208269269a4930c049a49a4924c30134d24924986006004104126d84004804926920c00020020124802b36dc6db740cc26db6db6db01b09249bcdc71e6c0c024c26980c340000651d15e7400021136c379b00000b4f269b4d000049a4924920820d34924d341041a6b25b25924824a38db6db8c30c24b04f20034d36d849069c49249209209249269249a69a00009a49269a68208209208200009208249268208248209269a692603012c92c9b692c1241249a6924926000124924da6820824924926904904964934960920000924820104024924c208248048249209008049249309009201a71249248248249249ac9249268060269a49249209208209248060208209249209209208269a89a49200049a4934920820924924b24d261249349249248249249061a0824926d86904004924921841b0924d2480209041249a68069a4d369a0000924924924104124924934924904924924b268208249208240069a4920900120a249248209249a6924800124d249a48000269a49249389849249249281809249241068209249b61241269249248000249249249041049a4924920820d349249249241249248209001a69a48248208000000001000049249349208201000000200001809a6da480c9b01a69ac90402080082482c1008300269a49809240049249a0026c009a6a2402098012492680082012c9a4984106820aa6dc6100004924920920124924104924104924904904904824924820826820824004926a308001209249a68201860279b4930920920020000004020024800024826804904000804900920000820000dbcf38f3c120006db6db0db0000c30e38dc6000136924da4800036db6e38f00c061879b6f30000806db49a40041209a69248200048269a49200268248000008049249041249009a49208209201349249241241248001249259a48248041209a69a682480, 176473902289088, 176476049772736, 176476049772736, 176478132310208, 176478132310208, 176478132310208, 
    176476049772736, 469678024263096156171119660081112803560976570824994383608742994714423205456177000511392500225258753929224450213863525481751775939535724058068846756318798925108353196372914746115787636185749809293346863462381071362899838642047192899902686722572958040065048249871112, 176473902289088, 176476049772736, 7759266745884737787877145148768247869707928956658233390514133441169626715139761082634133985774728768439309400775956985870221268406337908348105628720016858296505132738641478, 176473835180224, 
    176489337327808, 145689725112512, 176476049772736, 176476049903808, 176476049772736, 469678024262996135954626474396049201883404307809439465847209469036293517491662853868777365327554786199044271007167583316742716881029232605415329987486170661629921476336782700808944639187026876486184352385882573413847886813390504831827153888766743329898520246197512, 
    145689725112512, 163286759772864, 145689725112512, 145707324412608, 145689725112512, 163299510457024, 
    158897689071808, 176476050165952, 176476050690240, 145707324412608, 163299510457024, 150105370923968, 
    163299510457024, 158883864645824, 143490701856960, 143490701856960, 143508301157056, 45850507054584585683350108326387688803185728322, 
    145689725112512, 145689725112512, 48526606686879268241992863291730869224441125698, 158901044515008]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125249249249040249269249208069ac926f218209249249249201249a49a498c824926924920804924d349241009249249248200a49208249208000440041001205248000200048049249249261005249249249840129249249241041249349349249044b49249249000008008208269205248000201a48104929249a49248201a49249348208249249249209049249249241209249a49248200a4924924920804924924924100924820924820036db6db6d86012092524924924904034924924904104924924920920924924924924124924924904014924924924100924924924830112424924924920802924924924924114924924d20c205249249248308248a4104c34924d20400124924924804924d251661009249249241041349249249b4c249249349a49025249249248208169249349208204a08060068209204001249248248109249a49a4020124924924830824924924906904924924920d204928a49248249a0180030db6db6030c12124934924804024924924904104924924920920924924924924092514912424924924920804924924924924124924924924004925920820104124964802924924924820124924924924904924924934830c24924924d20c30924904130d24934c20004d24924d20124934924904024d24924926930934924924904104924924924104124920824124924904000924924924024804104120904920000100824020904124904004124924924904924106d04c200008209248240209041b413080412492492490410482092492412690248, 246842581389504, 246842581389504, 990140584432576, 172213702513601, 597813960960527290976094133971908173373739148041654284595482607509685154866197222996090333195090960516, 290829978571712, 
    853797380297664]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125249249249040249249249208049a49249261009249249249200a49249249208049249249241009249a49248200a4926924920800024c349001205200208000648025a4934924984014924d249241009249a49248201a49249248000249249249209049249249241009249249248200a49269249208049249249241009249a4924820110924d24924100124934924904024d24924926d2092492492492002003c904104800820b240249249249208029249249249241144a48a4924004925920420904124964804924924924924104124924924904904924924924820834da4d2490000083482400c9208209001203248209249a4a24020124924934c00024924924900904924924d301005a69a49b6800816924924d200208a49a0826a200001249b4db6000810824924d00020134934d24986024924d24d20180924924924904104924924924924124934924924920d36934924000120020800126826920000800920824924924920804924924924924124924924924824925920820924924964802924924924820124924924924904965924935800025924924d20000924904141925934820005924934d30124924924906024924924d26d40924924924904104d34924924104124920824124924906000924924924024804104120904920000100824020934924934804124924924904000824924824104124924924904104820924924126900824d249249009248209209240209349249240041000348249020209049241240209041240208000041049249025041b0024924d0451052400002090480412082482490492000080492092400010092402090412492480002412490490000492492492000092492492402092492492481082410492492010482092493411240, 854023419870960011236627802010097679097868147134809660628665189460710117407963691920351114754433131396, 176473902289088, 64880730932859096344032658499980910768042536981449543630859397463586982860997805638096830647198532, 18151086494400, 708644527149760, 18151086494400, 
    18151086494400, 106105088839872, 106105088839872, 265750967022100860209987475400698700642985871362512850690766706999080307499633799629332845527040669188, 1464372861018823477429589516038269041656136274754, 106105088839872, 
    106105088839872, 106105558601920, 106105558601920, 11451563423661946516976354343763199406276350530]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x228a49249a49249008049249249208209249249a41241249369a4824804004100004904924920820920d26d36dbc02012492492402480449251c9a49a49201007249269248248208249a41009205a49269248248108a25229249249240200a49249249049041001040001240b49249249049021945127289269b6c06014804920924820812424d24934db4d34d80c04d369269261241041b4d30c04d04d34926926124102924924924924924030124924924904906de6db6de0db01049248201341349249249049040a4db6db6db60301269b49a6f30000934db4d34d80804d36db69261241b6db6db6c06004184130c04904d340009261241025a69a69349000249249249041049a49a6924920d349249249241249a48209801a69a08248249209658041049241249008209248009a4924824820004820920924824d301041248061209b6da6824100034d2490400080412092410248, 45768272717046277528868664777451796336720562755, 91522607445746516357816004025188922380548921155, 290847426876352, 286453008438208, 286453406897088, 308431006208960, 
    299634913186752, 308431006208960, 290839087682496]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24926924924d34964c04024920826800004d67131800020934d24860000802924924924924924920d209248249a01801a4094924924934924930000924924924c20824924934904900804920000920924924821824820524924924924924d341241249049a60208248249269269308049249a49a4c20124924924d248249269249208049249a49249a4124926924920804924924924820124d249249060040061041269008041049049208200000201248029249a49a4c20124926926930804924d249201009249249248201249249248208249249249269049249249249209249a49248201249249249208049249249241001001041049a4124166d24dc6c040249b79b6db7836c24964936960920934924924c00034924934d04104934924d20920924924d24124000020800020804924904104900000900000100124924124124000026980024904000820000b2c0201249240248040269208049041009a492002010402092080090082410080492010082482002402080002012480602690c0249049029249249248201241249248201248249249248069049249249009209248248200241249209208009049249241009201808203009a412408, 283777154746433, 283777154746433, 284258191557185, 284258392883777, 145689725112512, 708657277833920, 
    145689725112512, 708657277833920, 145703012667584, 853797647815616, 91522607445746191837734148922904239919733936962, 91522607445746516357525747388916403350653637442, 
    823700679248421806075577567570261703412022285122, 145689725112512]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24924924924d34e00004924936d3410412492410000490492493c1041241044925149249ac920000524926b248208249249a00009205249268208248105145125a692cb38c00012804920826820812412924924934924926000124d249a4984104964936960920904924000124124d249841849040a29a6924b249240a4924924984104924924920820936926926000124924926820824900024924924d00104804924920000b248249240001248249248029249249261041249249248208249249249269049249369649204a4d249249841048a41048209249040800249249249021249a49b48000249249249041049249269a0820d249249249241249b6db6db6c30c249248001a69a68248229a61003000200a49248041a490492490082492090092000010012492402092080000412492400010482493492000000082692400032082492480086c12c9a498490292492410092412492482012482493493418690492c9209009204a492490412490410002010190008000096400490c020001b009240a208, 371085815699474073874710073185701877383497274178, 324410952043160650859974030848767479835062692201186926807968369422735110609415634418902542565723845, 15015491880072522916433016692265452359580515945483623649988975255275310110108900507927035805356958221677495114067783219606867874521778266072277790468576885387376404238363822916112661411800245198480613643559621149883548931905719783805099156320508774629508104246197512, 1102978226636332548769622337346846429261623513427542260925652726079421808411823819631641161844870853, 33283751237324762443823554423958000340146145984530851938681001185152501036029693000406479491804865220, 308439880831936, 
    317213546516928, 33283751113574826881503524441640741768576169950950084777294579894926474418183664229308439652855935108, 33283751113574826881503524498662970085759807968100323821326067926185781321970689891097753088469201028, 513259120171080175753226092837196870740343357413711208872743735545406521996694640062524841190256452314723440362954293053238810926744565900254343528567137832978193468141127, 365555209792773268890190957244931464517570876226, 286427637093312, 
    30946491887137527512635394397712577111473074314849674795086644395861206193842267413398017365635650130930164826770571877090783614662878288831690414054862765795048525934145094, 286449380365248, 286453008438208, 286453406897088, 308431006208960, 308431006208960, 
    299634913186752, 308431006208960, 308439880569792]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x228a28e592c924924901804924924920820b24924b24124324924b248248000041000041049249208209211c71271c6020324924b2482480449251492492cb301005a6924da58248249249249049049208200009205a6a24824c248109224a29249249240300a492492490490492492c9209201001040001040a4934904304902112714764d65924c0c016d34924d209a0924925934124124904a24020812434d64f36db6db604013cdb6db6d81806f36e36db0000f36db6f360601b6db6f3cc06000006180006186f36000000db1048db71b8040030d8030c036c025269b6f26806026db75b6db0300b26de6dcce60200b24924964904104d64db69b09209249259241241249001a68000249249041049041249259241240249a4824826920924124820920820d34104100d24000920924924836da8a24921004d368209248301209001a6800034d04104124904d34800d2092410248, 730842809600945818425847656311988328427132328770, 567902605415104, 567902605415104, 567902605415104, 132875738930441511880114602507350890244861752721157929325008698131872232389871549546074746903849472324, 567919386825408, 
    567919785284288, 567919785284288, 567916027187904, 730842809600946792059498852296260204163491732290, 567915490316992, 736462602495211039271591609267314827003162563394, 
    736462602495211039271591609267314827003162563394, 736462602495211363791383207733320235069000946498, 581096744948416, 581096744948416, 411227135938211784948209295296228910612930102083, 585511572869824, 
    581109629850304, 581096744948416, 456899062104803799221240840182661408700856795971, 581109629850304, 581109629850304, 736462602495231484018462312626081123176873497410, 
    572300651926464, 265755020079053651050093817564057552493173034142096504571744353372508200131434791297151662857538348100, 572313268392896, 572313268392896, 572313536828352, 572313536828352, 
    572314073699264, 563517979759296, 581096744948416, 572321724109760, 572313805263808, 572313536828352, 
    732180859417093159628416751358966341594014323522, 581095133811392, 581096744948416, 581096744948416, 581109227197120, 581109629850304, 
    457433236683831554579308718714658583575664001859, 581109629850304, 581110166721216, 581110166721216]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a4924924924d34920c309249249248248249269a6900004924d30820d309249349248248049249249249249201009a4924924824824924924906d04920820000d209a4924924824820924924924924924920d209208249201861241249249249249249241a41249049240308248249249249249a4d200009249249348040249a6da6980004904000000d309249001040348029249249269b4830c24924926920d20924936d24830c24924924920d209268369a4000104930020834024124124920d201249651348040249249249269249061049249249241a41241001348000249269841069041249249241a4024934824826d20924124820d20c009241041009a40009209049068249269249208049248209248201241001a68000249041041269069240001009a41bcc30c30f36c0448, 565802424158785, 565733168267841, 990140584432576]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12494492514924924930000524924924c20824924924904904924920000920524924821824810512514512924924d241241249049a60208124229a69a4924c300a492cb24b249a412cb2cb249218049249249248301a69a69a6906004104104124d049241049049203000001009240200001241248028a49269a4930c045249249248208249a4924926904924924924920b2cb2c9248600a4924924920c049a49a6920000104104104934084000004024902124934936960920924964936960920926926924c00024924934d041049e49b49308209249249241241209208000208249249041049000009b0860100124924924124022d268303009ac0a4100b24b20020134104104004004924100804920c0600010012432680012412486c96c90c0249849028a452492482012483492492480690c924924900920d201001001000b09000040049049a49a0000b21b2db203009240a208, 72670922213441, 265750967022100712688568472009397377696347321951545877532997366477235412440128935081288687756520338948, 72671123540033, 72670922213441, 72670922213441, 72671391975489, 
    581110165803712, 581110165934784, 72670922213441, 1464361710646224212118018748179132717475383284546, 72671123540033, 72670922213441, 
    72671391975489, 735038153274139565768570899841235981947375817282, 1464361729701956278782797883390316892924940456770, 1464361729701964067257796246572302972244914672450, 565733168267841, 565733638029889, 
    567916026270400, 567902605415104, 567919386825408, 567919785284288, 567919386825408, 145275264963009, 
    563508853871296, 563508853871296, 563517443805888, 563517443805888, 74869945468993, 145275264963009, 
    581101039915712, 581101039915712, 581109629850304, 581109629850304, 581096744948416, 581101308351168, 
    581109629850304, 572314072781760]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a49249249249259200009249249648040249249ac9800049249200019209249209040648049249249249249259301009208269200001249248600000249249218000000a49249249249b5930000924924964c040249a6dac980004904800001920924920904064804924f34924924924101924934d249040251671e49210049208208259209a4860b60b2416480002016482690002482c900924924936db4c00024924da6930100924947924c00024924d349301009268369a6000104900020004024124104900100124924924924100db6db6db6c30124924924904036db4d36980005934924920100db6d349b6000124924924904064924d2492410092492492483012082082096482182002d82c904800000100b24024926830820964c24924184100b261b0c30c30de6c2492692492080c924820924820126f001a698002490410412c904934825b05920924000100b2613d020934b66804934f349208218009009ac860300b24166c00020064806c00024820904934db18049619205249a410180592092092490402482492492490010092092490400482492080c02c904824d24100120124000100824124d2686012486480, 11440369494919715325275011960477919146747630146, 581126800360001, 563534614774337, 563534614774337, 563534614774337, 563534614774337, 
    22880651877470340693396783005751126471376639810, 583394610203201, 583394610203201, 581126800425537, 581126800425537, 581126800818753, 
    581126800818753, 581126532383297, 581126800818753, 581126800425537, 22880651877470340693396783005751126505467942722, 565733168267841, 
    565802424158785, 565733168267841, 565733168267841, 565733638029889, 1461551814199091523101041218842834364359778568003, 565733638029889, 
    565733168267841, 1461551814199018990391466676570213486574356727619, 1461551814199091682825016847599747819439971698499, 22886228254758257571886502450106103723936716610, 565733369594433, 565733705138753, 
    22925209981865619519409208342070645366873659202, 11507271985727082384786912202086861564878524994, 114269105871190017787265289338582760755732420418, 114269105871190017787265289338582760721104246594, 114269105871190017787265289338582831123134420802, 22925253538008585399534949514882997928408913730, 
    91433404124752454971087151419540713926465426242, 145702610014400, 849377322079168, 581126800818753, 581126331056705, 581126331056705, 
    581126800818753, 581126800425537, 581126800818753, 581126800556609, 581126331056705, 145689725112512, 
    145689725112512, 581126801343041, 581126532907585, 532345469047865660768623210452172779275560895643470799451774814268582418982072058175317214408426699844, 532345469047865660768623210452172779273998951876088448917398370632985506669843137228465139981595491396, 567900449555393, 
    145689725112512, 145689725112512, 91344027248952259365819571539208731765881442882, 91344201484158271372393461642735216458605794114, 145689725112512, 73120746639552, 
    73120746639552, 572298496066369, 145689725112512, 145689725112512]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, false⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_14_0
  · exact tv_b11_14_1
  · exact tv_b11_14_2
  · exact tv_b11_14_3
  · exact tv_b11_14_4
  · exact tv_b11_14_5
  · exact tv_b11_14_6
  · exact tv_b11_14_7
  · exact tv_b11_14_8
  · exact tv_b11_14_9
  · exact tv_b11_14_10
  · exact tv_b11_14_11
  · exact tv_b11_14_12
  · exact tv_b11_14_13
  · exact tv_b11_14_14
  · exact tv_b11_14_15

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_0 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14922924924100924124934934804904800020004920934c36100d34124800020104804100d000049029109241061069a41249000040269048208208048008249269a692402082082492482433cc20820b388208209a492098000c3369a6020b3cf2c83633c824124920924904024824924904024904924924900120924924920124100924904024814024924100920904824820104124904030134822414924930004920000820820820120926d040248148249241009204a0004134124120900104d049248000209209a0904484924900060160824824924100920924934d24004024d24906026904024924100120924800100804100924d04005804900004020904d348018040009349241009a4124924904026900524524926c001388148a400413412413030692082482c0208000000008108249241a41201249249249b6924924c24020924986d048361b61b0c06d84824d24920004120000826820924130924904004824c349a41001209200041241249209001049049248000209209a4904004024134920904920820824920924800020124822104104024804124934934920104104124924921964104104d641041049249048000619349301039e7964d34964110944d35800104000020b20820b04934824900100940d26904004824800d05904d05824934924934160000824826824104d00124904824100104904826824904104924924804124900920104924924926120924924924824104104924924814104124924920800824924934106184100025902424904104124904920004904d209a6000100b241a48001241348249248000048009b6c30c30d80c2082092492490ce3c826b2db20820824924924100306f2492082490cf3c9b000000036002c800030c06a209658461009341ac8000601bd8200001e40359049bcf090301b702048, 88545322680897, 90744614373953, 45694401221847087400999984630773642043230000962, 1038105601325226425755159398259884754816672447901262635629669173324412258497029679114535357032701636, 2076195269845423313358769181551325633333386860215257060010495816457201890744074329741287652568861316, 539676945898339347431183000665951489235077234891212776954463777412077029041128370659036608333730824324, 
    11451824793418054830788595578823495186984735298, 11451955462677719969140690103133002886696407618, 563534346338881, 563534614774337, 11451563456061799052245864367341202208307810882, 45705377412077478058231608522965712185218568770, 
    531501942024138971432050989280639261308838171650065839030579138047505842236854601888139919678180234436, 11451432787134440913449299766917787152245854786, 11440630863678902642865118403379473102141395522, 11440369484451964996480985082908144254737977922, 1157240694338497, 1144050715542081, 
    90744681482817, 90744681482817, 90744681482817, 538768617409380387675483264215295903829515660072753042527675721351724070906504697882132396314399621252, 538768617409380387675483264215295903829515660072753042527675721351724070906504697882132396314399621252, 581126800360001, 
    90744614373953, 3957769494675904269259458121709599304855121671632245881239321978696997660274090767951609559632537108229325235033861708341905650991767839174488363435327476423796114162483984454, 1135246032651073, 1135263212520257, 1135263212520257, 1135263212520257, 
    1135263212520257, 182710702416228708806950648826534121477888881474, 70952935768641, 282059369628225, 282059369628225, 563534614774337, 
    563534614774337, 1126458529956417, 1126458529956417, 90744682007105, 563534614774337, 563534614774337, 
    1128650909180737, 960962154094212046835217857624440951243359382280315518482490121323070426323277455699297059175538939419593693333797690981723307594003155694007602096057773658415023000518012293814292953099664337727248978538383433816528626210766128166183634468110730717040738313246988552, 91366501614006607126956147618615554192749630274, 532150803464395994019471282958774145585060550316055734381728350257546591090122477707965320439827440516, 11440630821309779291363373867848675787951575618, 91366501614006607126956147618615554192749630274, 
    70952935768641, 70952935768641, 282059369628225, 282059369628225, 563534614774337, 563534614774337, 
    1126458529956417, 1126458529956417, 90744681941569, 563534614774337, 563534614774337]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_1 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_2 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14db69a61809a61241249208049049249249200200a0124920804904924100804d208049248201241000000201348249a498c0249825049b6db70301b9024824924100920924924100934365965924004034934d34804900824030c04db0934c46100db6030d060001368041000000000029905b6eb6d88036e06904924820120134d24800036c208289a4800904c34d24100d308049248201200a0124920804984004124100900926820300b361b6d06020126816d34100c04da01a6dc6d8100ba50920928c00036c24924d04024d0cdb4820800da0d24d341001240929040000200001b6d0c030136824414db75b6040180034924db6c00104026db4906026904900020c009009b6800100804000000020004800000024820d04d34831804c009b69241009a4134d26c001348269a4d040269005361b6d80036d8cc30db0006c30d86db6c301b6330da6d8603cc24c369b6180e30b30da6d8603cc2cc369a6180a30800924104c24000020986d048361b6181806d8cc3cdb0006f30814db4904d80c20936820980186138c200301b4020020924924904db08200009009048249248240a082092492490ce3c824b20860820824924924100104d24926820c20924924902500104924924804db4834834920db6d049a0d34136d00120124867184106034d04d30820804920000104024804134c20c301a48000041041201041041249249219c7904964964104104124904800000034d301039b6104d34964134c208209a4c10738c30db61b6026d84106034806e30c30c06d808008249249240001048048048200209a49209040041249261208208249249240a0820924924904004124926920830824924924336c209b6dac01400000080092c8371b4126834106db08270088201d6104180d44000104904924800024100920100004924126120000d34d24824092801835924904106184100025904c30820020920426d84104124904db0834d84960934000100b26138c201441b6c24db4930004800920c2092492490cdb0c66c3db30830824924924100306da69b8c24b0cdb6db74302c703d836de6181b6080618618600002086c030c069a09658361009340209800001b18200001840359049bcf08c301b702048, 73152159892033, 73152428329537, 45716702052116209754376136214889942262678034242, 45672100752795752764220705974573161575069320003, 581126532383297, 581126800818753, 
    3958071411439552635652121272354445634660917244688260331573570631943746103765445682593843518814748360563658105267700421513862899870078377706635521434945085387637531047605779014, 3958071411439552635652123113636662683417450056840474450342661713213058513601405951097923375698389510712179848249931016211311138492670938565118938931319116201397776312474483270, 72639710302400, 532280556760699734867903915729482694186183203220721286079364966272539738698480049761187809785878461508, 72639710302400, 72646152753344, 
    72654742687936, 72639710302400, 22880651856534919897796543629063870979659274050, 2923059048494365635494605660826195472311457482563, 2923059048324151759600890908533661607584340182851, 73152495438401, 
    73152495438401, 73152495438401, 182733003226600873697241985004343890882752156482, 583325823615553, 73152428329537, 653694634904129, 
    6707484278935245677443871926042663546428451696335479928125394343202035005707895149821991662309759551252189069364600070056838241962833178935214887938163509470974848600417342337879195245494720323324317888258551516895588194714350094337988897126950803254021743626956331922360347596500797897894939281051763007230534452956350522827872758965828644697345849904484447419062309438034936906, 2926760986318959465246822282636117070324529451843, 2925868942219166618116724409036016356669282911043, 2923036747578943168864441935011821590815512265539, 11440325949410573410814607501085114534866256707, 581126800425537, 
    581126800425537, 73151959024193, 581126800818753, 90744682007105, 538768617409379679572675565121760137165086613868781210265583929922652793340206759935434558937520947332, 536692438010464554972587600588612638580513648363120199554392296090834891463236798122591239348106313860, 
    581126800818753, 581126800818753, 483070875915456208615035990446623592629548687235456895394391576110234042336562234422725376790026764094813997094116511138268023308945891622922124540703358460568374534468166, 538768617409379679572675565121760137165086613868781210265583929922652812705457536981553146620092366980, 538768617409379679572675565121760137165086613868781210265583929922652812705457536981553146620092366980, 581126800425537, 
    283958550204864, 283958550204864, 283958550204864, 469964748914436200411615462179390012196485388946442197664154329422414404061921788308312865783347626541518735207062553157324645899784720713590912046771979074689305709165194209293607637371328070457005008735457866791828138687817268916950786672396529301471520246988553, 1464361740590990722173661867003038113295356724035, 15008466959166475145822119029636068685455119171, 
    1464361740590992020252828260867086767019035525955, 283958550204864, 283958550204864, 182733003227849625855912549492006038705610437442, 91388802444275729480332299202731854412197663554, 73152160350785, 
    73135779483840, 581126800818753, 73151959024193, 90744681941569, 354602191426496, 354602191426496, 
    73135779483840, 73135779483840, 73135779483840, 90744681941569]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_3 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨0, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24a26e64e6cdb09a4924924920804824924924924124924924920804924924924820124db4124d24d20934c00830934804934d3c9059b41b6db6dc11b6c36dc71b6db7984824924924100900934924c04024026180026904db695c9059b4020904c30d34800004004100d04934d20c34d209b6c30d809a6124d04020134c26d80004066d00934c30820934824924924924820124924134000020926924926904134924d341009249249248201249249249208041449249241009b6f099b9336c261268208209648251041a61a6d05341820c34d30936924134c000242351349b0820c361c6db6d861249a6d00036836d849a40001009b4014904dcc8019b61879e79b6040030db6db6d860049241061041a6986db6db6db6180c36db6db61801869241b4c000311b61b6d86004820820824d20904826800924120800020004026100020804d005260249200269861861879e00009801040009a41061049249248260041041208049a4124936d20906104924934824184124d341209660661b61b6d84824134904920000904d249249040241349a4924100924920004134924130904104924904c0cde6decdb79b61bd9b6de79ec300986db6dc71b70661ec3379e6d849b6db79b7b0c02ca3d866b2cdb09b783c9679b6236900366336c66d801841b7980904d04134c00024124d24944120904926924904024924800d04d04104c24124d449441201211a00269000061b6c08230000c069b79348243211e41c4d30006da69001a10209319881881c9248230c46825934824024934924d04d30924c20830134820820924924904d3082082410092482492492412082092492490482082492492412ce3cf36db6db09049b4920db49209368309b0926136d04020337034d80006034d04e30820824900936106800c00128c208311240359b7936db6d64336f36db6db18061841000241059b7966db6d34120934d24934d34c24820824924924000104104004024920924920904104124d24930820824924924120820924924904104124924120b38c30db19b6c26134da0c2682498d156000100d34000104906904835984026900c0080413413c130de8186dc7066134b675e41b79b5104dc0820834d2080, 4152422219672461153971700860087374445029905492763729035961579946243871562385329141021122841377664517, 3958131796911442227514390791491513552897291597941468676088585603218590741412052392497743371063667882832442413080517398995770062994268524264786044623475011209809701504500595270, 565733168267841, 2923059026716294152554543999170220596678291949379, 2923059026716211400007686390337118921810679760707, 2923059026716231844754557093695885217941709457219, 
    1128650909180737, 4122285245674505847143378038682325532780561649984459292953562054229768522310403176464356902532242023653823350575266670014422101491096919650886260548324734505213925934856370758, 1128683121689153, 45716702563868993202171186048492105709423433538, 565733168267841, 3970812310658842606243409763219332193309600602732137481385080615665610406047073591883834892880821803181990874724106368677817323589588485583953053910660384063170046271577619014, 
    3958131796911442227299865864612431999304107197970175138048915750089112447368475409398195146582488352193470728721156780018364778600166459930441362926863523134239434321300519494, 565733638029889, 365420098126900712146843956507366608516111468355, 284258392490561, 565733637636673, 73151959024193, 
    284258392883777, 565733638029889, 73151959024193, 3970812310658842606243409763219332193309600602732137481385080615665610406047073591883866721567952029527088819187987768350134620476579897755763955209014754322156570639628991046, 3958131796911442227299865864612431999304107197970175138048915750089112447368475409398226975269618578538568673185038179690682075487157872102252264225217893393225958689351891526, 565733168267841, 
    2923059026716221460084160277430812838527122868035, 960962154094212046835216466568230249808153488794632213862604341661820121257320324344402051223638643593944080528739691005858281203826562502150501679238709288476359217300901184775497239757900991242421444983351474027741018874838761778212934916998851562370514945246156553, 365421404811116996275681924507672079662707705667, 1128657553736257, 91388802464141517949917177629442814288502785859, 636102448859713, 
    636102449318465, 73152495438401, 73152495962689, 60384320188748996953713361270138551216993652362094270212453005521901530561086538586919199195267264894615697226892948375508917676914127092676730891911865429943158180195911, 73152495438401, 565733637636673, 
    23014456840475806813029255436305807732268602178, 565733637767745, 73152495438401, 7729134245387100980419546709765111513115876230993414493979970113377534627768159798236022005985189901341107893903411785006419240240198251733274650171862036768366276602146374, 91522607425890448388782005968676274816346493762, 91522607425890448388782005968676837768447398722, 
    7729134245387100980419546709765111513115876230993414493979970113377534627768159798236022005985189901341107893903411785006419240240198251733274650171862036768366276602146374, 73152495897153, 143489095455681, 143489095455681, 143497685390273, 143519160226753, 
    182866808208215607817498894509041692199440356162, 60384089844362716342876909802990039264043478959723066095727268653604847046350608090138070362204572658965826928964570103787886343050984043472881304278866562416202367544903, 182866808208215607817498894509041973675490808642, 182866808208215607817498894509042536627591713602, 60384089844362716342876909802990039264043478959723066095727268653604847046350612036895276022052881886479595672277537414454762368410015225749306927196629913877509297057351, 182866808208215607817498894509041692199440356162, 
    284226718032705, 284226718032705, 284226718032705, 284250340352833, 284252487836481, 365421404811148150175984863140104831836805482307, 
    284241750418241, 73152495438401, 1461685619180706259756309676630628670922303804226, 1461546935911079423121566222054685537540373546819, 565733638029889, 565733638554177, 
    3958133210304596500051360997841081017104641452421440471258132524900569410221524580399184397501832724621660867677744116012517055479035163929557090643335628524047267190347364934, 22880653047523204120500879143850686141842855746, 1128665941819969, 1128665941819969, 989321606928967874533254122535557125569888479846245085006947075618292445050922066283409278675220401348103969151551279576875460607391949060678409959012292023727503847779088711, 565716458684993, 
    989321606928967874533254122535557125569888479846245085028382690473651233902092527075614958403407624352813004741043526049342731159019815688669784130630009699710135833070025031, 1464361710646224212118018748179132717475383284546, 1464361710646224212118018748179128776823561851714, 732180859406542047643711596624480504912541684290, 565733705138753, 565733705138753, 
    73152428329537, 23014456840475806813029255436305807732268602178, 565733637767745, 636102448859713, 636102448859713, 94377113039711876845755382275474252474458641218, 
    636102448859713, 73151958567489, 735038153274139606333390711017191249011835769410, 73152428329537, 735038153274139606333390711607486637156465742402, 735038153274139606333390711607487059370541421122]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_4 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14924d34924000124924d24984024d64d64d20c02924924934104336db69a6800034d34d349049029a69b69a4800024934d24900004800c00004d20904c00c00d34000000020044810934d24d34c00024d349b4934100934d26924904024934d34d24904c24824824924826000104104c04824104034130120134934924906025134d24d00004924924920100924924924830124924924804024924d24904104d24924921120924924924d24124924924904014924924924100924924924830106836c2c900024130030034102414924934920000924926d24904014d349249241004a48a0004104124120504104d24904804934d36da60001249249449840249249a69a0c04924924924100934d34d24804826da49269861049249249261009b6924924184134924d34c04026da4924906104820820824d30800800800da4100000004006900736f38e48c00c26db6db6db61b0526926d388000148a4900024c30d84014136db6db6d80184db6db6db6c36124924930006d861b0c04824d34924920000934d24924904024d349a492410092492000412492412090410492490480cdb6db6db6000234925935a08036db6db6db0c0d92496596c300b24964965965826d24934d36180934925925b0c02cc3d836f3ce30925866965924346c00360336c24100184125900934d34d24c00824934db4934130934d26924904024924800d04104104824935924934130124924924900104924924924824124924d24920c04924904120820920906924924924824024004904d040008208249248241000200201040208209249249040008208241009a482492492412082092492490482082492492412c000c36db6db0904000830824930000000000104300000020034820000000024102000104800024300030c30de0000004104800103800104104d643000208209bc000000000024105801964d24d24110500000d0490490410412492612082082492490410410492492480002492090090410492492412082092492482410410492492481410412492492082082492493416000410413510240, 22925209960930198089983668851268689126804690754, 45772279902884845118360063275314612843562668610, 11518335277941807972961200008526729570376749634, 11507271975259332055992885324517086672868872770, 14272542282624853759616689511842680221349249859, 114269105851583824987449965834799312324295399234, 
    91433404103817034175472404877669124905958904642, 114269105851583824987449965834799312289667225410, 22925253518402392599719663790031693963201615682, 114269105851583824987449965834799382691697399618, 114269105851583824987449965834799382691697399618, 22925253517073164603934710138195742436691547970, 
    531502440922005843165170292766406819743994871674924620132331644797675234542208788608137651636622500740, 11507228420279444475150122159390805960752632642, 91433404104813958975277399632210792462503908162, 91433404104813958975277399632210792462503908162, 75479248513869236564314003539780746969839170396924060909615428939136413543628659212020991815184273073790604162757204459116885335347130733818501345422236103748861493030471, 91433404104813958975277399632210792462503908162, 
    22925253518070089403739733226936518318145672002, 22925253518070089403739733226936518352505410370, 22925253518070089403739733226936518351431668546, 22925253518070089403739733226936518351431668546, 91433404104813958975277399632210792462503908162, 3971778498249206391465486329607687329162224467107849155903326710881160735299501866074158728442661737732266729621072562994197100735969053295787840607107806278748908022604445766, 
    91433404104813958975277399632211636890655265602, 3966947826345434818534600772790982864272500708725195642772778360100464469088748678847144189480367387792179418993735624207240346610018584753349330508276380483223119076928731206, 91433404104813958975277399632210792462503908162, 152285188477889, 152285188477889, 145277408252096, 
    145281703219392, 91433404104731206428419790799117843335544312642, 91433404104731530948211389265130006766464013122, 145277408252096, 145277408252096, 426756679930048, 
    145277408252096, 284226718032705, 284226718032705, 145277408252096, 145277408252096, 145281703219392, 
    145290293153984, 145277408252096, 145277408252096, 145281703219392, 91433404104813958975277399632219518220067935042, 145290293153984, 
    145290293153984, 797253407943141529731982798330850982027501575227953348303094888561537591720441465052122670994056981060, 145703012667584, 567915490316992, 567915490316992]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_5 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249a79a6000124964db71a6980c049249251301009a69a6da6000124934d248248371b6e36d80c04904024100100000000000000104900124824806f20c208000005249269e4980804924d249c6dc89b6020124904d04c000000000000000041bc8260360000149349a79a60001249249249a69a6000124926e249808041041341400008049a0000020120926e24800800494924924924100924924924904824db6d66db60001349a7924da6020134104124924130000006800c3612490492490483cdb0336db0300524926da4da6980c04d24d04104924904c00000020030d84f2db669a6c0c0269249249208049341b4d00030924824924824104000d34c07824104906000000926db4936db00009a08209249209800000040341309248249248241e410b134d8180412482410092010482002002c104900124804824c36d000001b61040000269800041040241349208261040200201249001249048000300001b61800041341449300000000000001000202209a6f00524920804800b049000241a0800c04d24840c36836da6020905904d34c00000000000004000826c369bc00, 1130861005534145, 6707465088747716097056592077363274021238845272324962137946396857010650052059691504918520009667669386597626852455549003138538311871782493420495270203678150856562192241460833984355209338614664342616255357967562856222399300498188839190186415069120881937269492425752605443015459851858833872932387624858121588971332301730848261107451499000779361302936952479175440547021572413197602891, 531567574968091860714535146135474618407457192071345451360548408300679180699322904207957703030438577028, 531502440922011507987658956443774514321547210362790003662384839489877527930630668667403258707272415877, 960962154310961563796381349092987145361167787657713389617951164985618107792747851905544178417377376502624540592463359047841779352336736476888780957081269300635875520202041717980807598451319376577981618984626781317828060073964527763495183813038511046457835808246988553, 960962154310961563796381349092987145361167787657713389617951164985617650185498760628366169405430576423119591751901597642601230563096839412281911152878132034246409610264449725437613072785540109157407536065769053844567352915838813948599706524979644198654329120746988553, 
    960962154310961563796381349092987145361167787657713389617951164985617650185498760628366169405430576423119591751901597642601230563096839412281911152878150382165345507643486230424855418213302597986019460526176156589668939223792997829487137355783883685000921376746988553, 961665984013443560290120001100922282247251736714171625493199534749555314903314525057660227111873261293911351465540414345367529362332774153742517677748896040685271582176038903895640317351377058152018883560881978530918075604406119858766459822389098736674423072746988553, 1130856710566849, 1130856710435777, 531567701688025876530273738202096154635994909443782046235443451831044039793646845824294541534972643716, 1130856710435777, 
    531567574968091860714535146136942102229910339004679479244727808287624359292614613317371239671193781124, 531567574968091860714535146136942102229910339004679568030953599157819228775214254013450350720665994116, 531502440922011507987658956497442493914190586708596035656525231969881260845299452530031999506703858309, 960962154310961563796381349092987145361167787657713389617951164985618107792747851873885887028807399184255496952076649214872198421207922042025270278750072247314019796186671298878038803461214964549001765483761583468565447642730487216119267083340789008495034656246988553, 960962154310961563796381349092987145361167787657713389617951164985618107792747851873885887028807399184255496952076649214872198421207922042025270278750090308615620717999825234092589307395873737498291465697611016980686767310720016512109139048759418693391237408246988553, 145277408252096, 
    426889962328512, 563508853871296, 584685777486343008397113790163115288660430914245364379764898362283143544232497579839127728018441092, 563517443805888, 961665984013443560290120001100922282247251736714171625493199534749555598263309140831763854046376458491890149935539918097054594856183772749881171693479826814130228799703393319789543338862961131208073150824878541432858543962598205741909433810928197036127830304246988553, 299359498408896, 
    563517443805888]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_6 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249249249208049249249249240a49249249208029249249248201249a4104904920524800020124804924924924924100924924926104365965925365834934d349b4902925536db6d80004b34e30db4d20934c36db6d341249000241348105a49249249248201349249348000269289a4926904d24d249241009249249248200a4924924920804d249249241009b6f06db6f36c14124924928924800024924924904106d249a4920c20924d34934924092935935924830124d30db6db5904414924924db6d64c00026d349269861049a49249261009b4924924184136926db4800027124d24906104920820824d209848008009a4004000020004006d00024806d005371e6dd75b000cdbcdb6f30000b38da6db6c00024e369b6db6000b38da6db6c0002ce369a69b0000936186d861b000cdbcdb6f30000824d34924920000934d24924904024d349a492410092492000412492412090410492490480c92c9d79b79d79d7824b2cb3183082ce309258349659242a4800060324825900164925900934d34d24c00c24d24d34934120934926924904024924800d04d04104c24124d349341201279271a4900106e389b8e362009a4925924824327164d64921006b24900120020920106e389b8e36200824925924824014924904d04db09248200201248208209249249049208208241009248249249240a082092492490282082492492412cdb08269b69a0504924b309a4b30d36104d249a412490c020134824920820824900004104800024134820c30d34000104104000103925964924d64336f2c9a68308000000000241059b6104d24d24110736f30e379b6c248208249249240001049040048209209a49209041041249241208208249249240a0820924924904104124924120b36f30e379b6c14134d84105937104930820834d20800100924904800124920900900024824126120824d04924824092801835924904167184135935104d3082082492040, 4280726152865126802493572857811643688837776284755806092635494255197199970487563435057776772223988869, 581126800818753, 531502440922011507987687974781368610325476896705720919805306584078495041462938923349436719347416712260, 531615475104112858878084760800675182941629683550929241525331067646940115892777286178222686895882237061, 3965981691964736737354108487317947643332031169096169509278040889521531456337817940099799166000360708524882529252844851905882015360819589735754003766456662302350528963223171654, 45850507034727868674423561698492932803686044482, 
    538769060929150387167604234746425968876630490252949458179303952396237642984131091797930913702621757572, 581126331056705, 45850507034727868674423561698497366051480671042, 538769060929150387167604234746425968876630490252949458179303952396237652591551658724832782917631754372, 581126331056705, 581126800818753, 
    299651555279425, 299651555279425, 581126800425537, 88545121813057, 299651555672641, 299651555672641, 
    581126800818753, 299651555672641, 88545121813057, 299651555672641, 581126331056705, 2925868931330130876765535821979424580814864712515, 
    1157240695321537, 145281703219392, 145281703219392, 1144050716525121, 145290293153984, 145290293153984, 
    581126800360001, 483126158568166773286091175980224065836216998944578023527326638667816362832807668750849379327271204353999101525529383735134240540785983859458844544482308073094390361354822, 581126800818753, 90744681482817, 90744682007105, 90744681482817, 
    581126800425537, 581126800556609, 90744681482817, 91522607425890448388782005968676837768447398722, 90744681941569, 90744681941569, 
    538769060929150387167604234746425968876630490247096670262383125333882457789284719599411428049803296900, 91522607425807695841924397135583044213336445762, 145277408252096, 426756679930048, 145290293153984, 536692881530235262567516270213278470292057524741435659551191491502064555912314757786568108460388663428, 
    581126801343041, 163280304755649, 308415973843777, 581094589088321, 286148179005888, 286156768940480, 
    286156768940480, 286156768940480, 286156768940480, 286156768940480, 286165358875584, 426889962328512, 
    90744681482817, 145707324412608, 145707324412608, 90744614373953, 581126800556609, 90744681941569, 
    91522607445746191838024292226416395344236516162, 91522607445746516357815890692428558775156216642, 308415973843777, 427169424610240, 427169424610240, 145703012667584, 
    145703012667584, 145703012667584]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_7 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨1, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14944dcd9b6000134924924926d80804924924d301009b69a69b6000124934d248040269b6926980c04904024100d208008200001a4104900124804000180120806d00525137366d80004d249269a69269800049a6da49c6020104104904c00020026800006904826da48001a4014dc6dcd9b60001349249a69a49a60001269a71269808041041341300009869a00001a4120927120806900494d34924924100926924926000124934d24904c249e4d26a008049a69269b60001259b79c6de6000124104124924120000004800824124904d24904c208301269b0100524a24924980004926d349a60201269a4926d80804966de71b7980004904104924904c00020920020904820c349b6c240269a4924920804d049a4d00000924824924826134c20934c06024d3493600000092ce3cdb6f300009a082092492098000002400412092482492482610410a934980804134824100920826900000980104930d248040001e41208069048269200001c6120820120c349041040241349200000068008061049001249048208301209a0100004134134941847980000d86120520a24800026004826d048201a41209a4120c008000041341b41409000209209a0984820c24846824000104904d24c611e600003618480, 532345374011783750598791458929309759981390344916459905798522614537972613552896258726727006453036817476, 532345469047865660768624092324406907120610135223090523682313516224697832559181252832426046135191518276, 532345469047865660768624092324406907119048191455708173147937072589100920246952331885573971708360309828, 532345469047865660768624092324406907119048191455708173147937072589100920246952331885573971708360309828, 365555209792773268929805038495146121329163457347, 145688118711233, 
    286425741288385, 567900449555393, 145277408252096, 145277408252096, 145277408252096, 145277408252096, 
    145277408252096, 145277408252096, 581096744948416, 581101039915712, 581100771480256, 581109629850304, 
    581109361414848, 581109629850304, 581109361414848]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_8 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_9 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12494b249249b6d26db01009369a6d3600012c9a6da6c040289a6da4980c04800120000d209049a600012412c9269a6c04026926da0804d00492524f24a24b00004946d369b6c201279a4926d80804966de7b37980004904104924904c00020820030904860c36b640240249249249208049269269a01009248249248241040048208040200041200001209bcdb6db6d86024d3c926db01009041849b8d84c2082092492098000000403618092482492482436c18db6c800c049b49249200009369b6930000126d04030000826d87986000104db0920804100936100186000126c24820d04024d840000008000041349361b19b6138d04000000104104186c000000209200000041269a4120000000804c20000104104104800000000100100524824820904024986d24000004930100804121b64364b20c24124924000000005b36c46db7836106104924904c66de5b359000049b4d34934121046825934804104104924904800000120120804935924924121b64b64b2400400, 1135254622978881, 1135254622716737, 531567321528223829083114236531192012525116514603112004014657761339353863210663605599448713970871083908, 1135254622978881, 531567321528223829083114236531192012525116514603112314766445714103845885136136531000720871406960067460, 1135254622978881, 
    531567384888190836990969573736948910544147210671938209891201808785184776256483129453665818420185310084, 1135254622585665, 3957316615499754682076567428340131713358304911266936092898968258547390679017749547673178036328285734761804327806983895174880169631324255707929152158261548483495741816837680710, 182866808208132855270641285675948743072480760642, 91522607425807695841924397135583044213336445762, 3957316615499642208373604140914235235522875161835290193147831541939832804642287975329444602547409166457806537645738017605326008603781893974387840340489466602455325823129267782, 
    91522607425807695841924397135583044213336445762, 2923371238340020326829870083350405716595653550915, 960962612540416179297681272317137036444875860593623397668097447612218259087555972619434397913460824426266829514599082974054045285632946197571380954841489066219473396706323390489871622833774770412086119121359699051701786795931935238928230828227736910788829192249527112, 1135254622978881, 45850681268521611112905863822398878623373201986, 91522607435112327306771014844782722987621093954, 
    182867505105091116851181862729765459309229003330, 178406642153343911774761542110589500996457026, 730934800504538340765321210116402967671681946178, 730932012911388443307789499080874462018294288962, 91522607425808020361715995601595207644256146242, 91522607435112651826562613310650771505342845762, 
    1135248180134721, 1135248180527937, 1135248180134721, 1135248247907137, 1135248247382849, 1135248180527937, 
    3957316689209620870776808260935523474645644222461326429605951472388156237070390171320891371400321600029317030312724556157212893933446543905470468302872393152190626337090666054, 1135248180527937, 290823787799361, 572298764501825, 1135246032651073, 1135246033044289, 
    1135246033044289, 145277408252096, 286014896607424, 145277408252096, 145277408252096, 145277408252096, 
    435686055350720, 163419769541312, 581096744948416, 290280733675712, 290279929155776, 290280734462144]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_10 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149249249a69b6db0000924924da6c30836db6db6d86d849a69b0000da0924924c218368209a6b2c9249249a60201b6d34db680002c924924900806db4d3492010092410400002400010400000482c9249249008000040341001201249269249a6db6c060269269b69b0d20db6db6db61b6124820c000368269269269b0d20824924924934925920000926d249648040248249ac98000496492000192092d1209040648029249249249b49259301009208269200001359040300000251641018000000a49a49a4d30100924924924934d30000926924934c040249269a6980004124100000120900920904004804924934924926184136db6db6db6d849a4924924100926924924904025164de4920c04c20820824920820830920924100000020134820000024824900938d36d24824824924924934d24c000249a4d349301008248269a6000104904020004024024d34900100124d36db6d80004924d349300009249a69a6800134d24924904024d24d24986104d34d34924d30db6db6db6db6124924924904024d34924924100934926924830100020820934820020c24824904800000100924024984d30004d209b6c30db6c00024820820824d309b0c30c30db6c20d2492492080cc3d866f3cdb0834924924820100f36da6980024104104126904834d34da4d209840001009a61a0c00134b348049861060201268249349241009a4136db6db6c06d84c30820800900820820100924100000020024800000024824904f34d31804960920524824d30004920920924904024824924d04026904d34d34900100db6db6db01b6120924904004820820c0402490400492410012000000010092412690402012482480, 11774883299618267346435258064055031849468039746, 23549676765605515298271977582192924462690603842, 23549676765605515298271979869589189602675004226, 11774839743475301466311934752105280583136973378, 90718577115713, 92057827352349384869809643987467198607048840002, 
    7729193213548252452244917101174675024314794946757258605166766589413764145675061872145625752798639518361081653131436742973771153180602958750083699615914449943293190007336518, 92057827352349384869809643987467480083099292482, 92057827352349384869809643987468043035200197442, 7729193213548252452244917101174675024314794946757258605166766589413764145675061872145625752798639518361081653131436742973771153180602958750083699615914449943293190007336518, 92057827352349384869809643987467198607048840002, 149675454763200, 
    149675454763200, 92057827352266632322952035154374249480089244482, 365733966234513979144671484604210573759309959746, 366089384361115885470781157463745042957582996290, 149675454763200, 79236780069056, 
    12131651666569038890335451926717870306832159554, 79236780069056, 572299040789440, 366090448774993478697625632866510587116296161091, 149675454763200, 149675454763200, 
    290280733937856, 290280197591232, 290280734462144, 290280734462144, 572314072781760]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨2, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149228a492492493010093c9a6936000124934d24804024936da4900804904124100d209049a6000124124934d2480402c936da08049004a28a4524b26924900004934db6934020104d04904c00024126900004902b049b68001240149349249a69a49a600012c9a6d269808041041241300009869a40001a412c9a6d208069004949349249241009369249b6000124934d24904c249349a49308029369249b60000a59b794c934000124104124924120000000800824124904d24904c208001ac9001004a4924926b00002934d36934c200a4da4926d80804566de5b25900004904104924904800020920020902860836b640240269a49249208049049a4980000924824924826124c20164c04024d3492600000092cdbce66f300009a082092492090000000402412092482492482610410c964c008049348241009209369040009ac124930d248040249341a08049029069240001b60a41040241349200000008008001249001249048208300209241000041241349019b790c000d041204a4924900026b02934d068301240a4e24120c06a000041241b4160500020920920b04830c36834924000104904d240661e430003410280, 283745942835392, 72639710302400, 72639710302400, 1135254622978881, 1135254622716737, 90781669397184, 
    283745942835392, 72639710302400, 72639710302400, 90781669397184, 1135248180527937, 1135248247382849, 
    150086165222337, 853773741220673, 290823787799361, 572298496066369, 930132433671875323876521948840236477858989728666343910663177640253861027723673198853890970049192678533, 1135246032651073, 
    1135246033044289, 1135246033044289, 145277408252096, 286014896607424, 145277408252096, 145277408252096, 
    145277408252096, 163419769541312, 1135263212913473, 286014896607424, 145277408252096, 145277408252096, 
    90788111848128, 163424064508608, 73135779483840, 145703012667584, 73135779483840, 145703012667584]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_12 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x149148944a4924935920000926924d6480402482482c980004924930001920526920d040648025245948a4db49359201008268209201801a69040500008149249218000201249249249b69249241a41249049b6030834824924924d30100924924924924d20000924924934804024926926980004124120000120904920904004802922934924924184124934934926d04924924924100924924924904036d65934900004d20820824d209b6830920d34124800020134810936d36924824824924924d35924c018249b49249301608248249a6000124d058200040249b5924900100124924924986024924924924904024924924906104924924926d209249249248241249249249040149249249241009249249248301000200209348261a0024834d024249b4db09a4d20924920820824d209b6c36c30db0c2092492492080cb31830c3ce30824924924820100b26f24908024904104126904b24104c04d209b60001009a41248001241348029b6d860301b6c229349241009a41bcd860601e6c34934d34806d04db0830c009009348201009241a4800020034800004000004104f349b18049209105249249249040248249249040269049249249001209249249201a412492490400481492492410012092492482010412490403013482240, 90744681482817, 90744614373953, 563534614512193, 563534614512193, 563534614512193, 88545121813057, 
    101709532656577, 88519553860161, 90744681482817, 92771453920961300177846494679189650057537262402, 90744681941569, 90744681941569, 
    588240024178366012649841856584208775512405191778624369731445050010868123886755007739306191764741858180, 980451500981820707584169725689562792406022030117741869241050738323941680398031158168027468038262501896242847369113719261879681551913085513021563085748461577554225765023390498820281649185849616968314605230500687442476235828091675289588519445757425571109798440499877512, 6244766299353608099518552330902488402640987473596040914503187486516068983979209439269603013355125956, 3966962863227027669513609145828533571934246840134843074904401864784838395956437661643092695638566766181182199536178511623963556475974330115728066360862480370795232263600561734, 440221545009600, 158471547785408, 
    158471547785408, 92771453920878547630988885846095856502426309442, 158471547785408, 88032873091264, 88032873091264, 310614997099329, 
    158471547785408, 158471547785408]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_13 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 0, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_14 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, false⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x14d125249a69a49b6924d341a41249849b6030836812db6db6db6c301269249249040249249249208049a49249261009349249248240a4924924920804924924924820126924d24906024800104126900824904d84d205260000209348029249349249241841b4924d24d26d049a4924924100936924d24904036d651b4d00004d24830824d209b6830920d341a4900124134810534924924924820126924934800026da89a49209049a49249261009249249248200a49249249208049a49249261009200041049a61b6d861b61b6c1412c9a69a6800024926924934800025524d24906106a24924920c20d24d34d248240929459359248301801200209348261a0024844d04412db6c30200f36134d24030126824820920804904d34931804c009049249200200a4020920800904924900c04d209008248200241268200301040249a490c024b065029b6d860301b6c249349241009a41b4924d24c06d04db49b0c008209348201009241a8906020030800004000004104b349b1804960910534924924820124124924800134826da89a48049049a49241019209049248200240a41249208009049a49241001009a68201009a61269040301b6814924101004d201249209208000348249249040269069249a0800120924d441001a409292410402010412498803013482440, 369782736294336, 73152495438401, 73152495438401, 73152428329537, 73152495438401, 73152495438401, 
    94198707058185130793920196062632864102211392322, 90744145068609, 158471547785408, 158471547785408, 158488727654592, 158471547785408]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_15_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, some ⟨3, 1, true⟩, none⟩ true 104 ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩ [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, some ⟨3, 1, true⟩, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 1, [1]⟩⟩ [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 0) (rem' := 104) (cur' := ⟨3, 127, ⟨3, [], 0, [1, 1]⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 1, [1]⟩⟩, ⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_15_0
  · exact tv_b11_15_1
  · exact tv_b11_15_2
  · exact tv_b11_15_3
  · exact tv_b11_15_4
  · exact tv_b11_15_5
  · exact tv_b11_15_6
  · exact tv_b11_15_7
  · exact tv_b11_15_8
  · exact tv_b11_15_9
  · exact tv_b11_15_10
  · exact tv_b11_15_11
  · exact tv_b11_15_12
  · exact tv_b11_15_13
  · exact tv_b11_15_14
  · exact tv_b11_15_15

private theorem tv_b11 : TreeValid ⟨some ⟨1, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [1], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 1) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 1, [1]⟩⟩) (prev' := [⟨1, 129, ⟨1, [1], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b11_0
  · exact tv_b11_1
  · exact tv_b11_2
  · exact tv_b11_3
  · exact tv_b11_4
  · exact tv_b11_5
  · exact tv_b11_6
  · exact tv_b11_7
  · exact tv_b11_8
  · exact tv_b11_9
  · exact tv_b11_10
  · exact tv_b11_11
  · exact tv_b11_12
  · exact tv_b11_13
  · exact tv_b11_14
  · exact tv_b11_15


theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H4 := by
  intro M hFirst hM10 hRun _hUsed hForm hMissing hLoop tbl hNeSp1_raw hHalts
  have hNeSp0 := mk_good_ne_sp0 M (by simp [hM10])
  have hNeSp1 : M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
    refine ⟨hNeSp1_raw, fun heq => ?_⟩
    have h10 := congrFun (congrFun heq 1) 0
    simp only [reindex23, swap23_1, hM10, Option.map_some, tblOfList] at h10
    have h23 : swap23 2 = 3 := by decide
    simp [h23] at h10
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts, hNeSp0, hNeSp1⟩
  obtain ⟨hm0, hv⟩ := mk_base_hm_hv hFirst
  have hm1 : Matches M (baseTable.set 1 0 ⟨2, 1, true⟩) := matches_set hm0 hM10
  exact tv_b11 M hG hm1 rfl hv (by simp)

end OMA.BB4H2

-- Step BusyBeaver.BB_4.R2.H2.R1.H4
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H2_R1.H4 := OMA.BB4H2.step_proof
