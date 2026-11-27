import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1

namespace OMA.BB4H1

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
  | some _ => (cert.edges / 2 ^ ((2 * nodeId cert p + a.val) * (4 * cert.dfa.size + 1))) %
      2 ^ (4 * cert.dfa.size + 1)

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
  let extra := val / 2 % 16
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 32 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 32 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩ <;> simp [nodes]

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (nodes cert).all fun q => !row.testBit (nodeId cert q) || cert.onBlank q
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
              (nodes cert).all fun t => !swRow.testBit (nodeId cert t) || pRow.testBit (nodeId cert t)
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
      have hn := allNodes ht q
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      simp [he0] at hn
      exact ih rfl hn
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
      have h''' := allNodes h'' t
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      simp [hf'] at h'''
      exact Reads.push h''' ht

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

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t, M.multiStep (Machine.init []) 107 = some ⟨some q, t⟩) ∧
  (∀ q a, M q a = none ∨ ∃ q' z, M q a = some (some q', z)) ∧
  (∃ q a, M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0, t0, hRun⟩, hForm, ⟨qm, am, hMiss⟩, hLoop, hHalts⟩ := hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      | v :: rest => if checkCertificate tb v then some rest else none
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
        split at hCheck
        · rename_i hcert
          have hns := certificate_sound hcert
          obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2
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



def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩
def h2 : HistItem := ⟨2, 128, (startPos.move ⟨1, 0, false⟩).move ⟨2, 1, true⟩⟩

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1, h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 0, false⟩ rfl
  refine ⟨hm0, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide, hrun1⟩
  · exact ⟨by decide, rfl⟩

private theorem mk_step2_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right))
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left)) :
    Matches M (baseTable.set 1 0 ⟨2, 1, true⟩) ∧ HistValid M [h2, h1, h0] := by
  obtain ⟨hm0, hv1⟩ := mk_base_hm_hv hFirst
  have hm1 : Matches M (baseTable.set 1 0 ⟨2, 1, true⟩) := matches_set hm0 hM10
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := (hv1 h1 (by simp)).2
  have hrun2 : M.multiStep (Machine.init []) 2 = some h2.c.view := by
    change M.multiStep (Machine.init []) (1 + 1) = some h2.c.view
    rw [Machine.multiStep_succ, hrun1, Option.bind_some]
    exact step_move hm1 h1.c ⟨2, 1, true⟩ rfl
  refine ⟨hm1, ?_⟩
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl
  · exact ⟨by decide, hrun2⟩
  · exact hv1 h1 (by simp)
  · exact hv1 h0 (by simp)

private theorem tv_b11_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580646329190496, 564325454709793, 567624123810849, 2415337909841188095370712234775366329940453084132835857266049504924725359055737824086313825244435698113625555515733320703791997618422932927130876340507898974831970862671654, 580646329190496, 580646329190496, 
    123421290727520, 2882796044642559668108902217020520358754473355747317255172904314760325720334361532773108504038751962284028800442695113019516352733425134481345224526966300459507143189351526178370926382825721534092318953103670718174424119329185788576830694338878844557781286032910710689422553902452623873990057666526701974999530886347673382191768792548486618074901339582464486231871538912960222515656341996994752960799037203108568009715665921153204216701908497077194728422621327257706615989181783185410547749396684621433172105626132111176179217887604293375585249575061890587333070652089718419241680632333119825792068387873447150074385988539986849667476727416845296400413797898030, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 268897676423098020835753784209898587196409585209998967526066458530490122002452774864774889699538971972, 580648478836960, 564325454480417, 
    565425436073185, 567624392152225, 567624392152225, 580577608665184, 580577608665184, 580648476706912, 
    580687135738080, 1461551814183058052351566407747190105717760066978, 265752994540108411252272281131948634137862342345329376603206483602215547622169549049995749800335678340, 564325823677473, 564325823677473, 1464361708588496461248882028300339658628276687779, 
    1461507212527836739910363371722207058301473523106, 1461529513358105862263739523306341408103803127714, 1461551814188374984617115674890475757906132731298, 1461551825077410726087146505718463195722715497890, 265752994540085751962200810330748666540694791401796776248839312137504071611063059066227675669033714564, 564325823677473, 
    564325823677473, 567624358565025, 1464356230722953767981422175021998432235200972194, 88236917590112, 88236917590112, 94198707067427454380637360583561794639385597858, 
    567624358565025, 1982749284860969392887280207987783610871466996499715810074701766986012142199930256843420905335557281536995470394971298990700930294072251032205285481135405141467279224284882726, 1982764410194750122970980988588570105092407386125972114495166369041701948151521137401203421325884975014295109256012642819327829699128722755981148234415443998050459234917656358, 2968221476721395911463059958353637030322414197924683716333860813541162146582843238778888601151044450904936008831456644952262218590266075805562031838614423566094237396703880998, 283125590787105, 283125590787105, 
    284225102417121, 36835019719713, 36835019719713, 37934531349729, 45631112750369, 91411103124259396610367800923972526316529911714, 
    3381578341693589203573397599502001423639513874536637613221310728339829316874796487253223026680119849966547847779811295526602203675139398579783224951447040395043042776665879888771289405782298835781885756287199381360951160787191653843175950355377602966232978134527769802133505143970573051151282948859550946683343286998854869092510922792053880067272728644218934002996092895288807403, 142388236649505, 182710702416187494792801618027792928452528048034, 283125590787105, 283125590787105, 283125590787105, 
    283125590787105, 2062153481806272082696230099498809485374663185562076457660896771723864471687240533595123451007167003469957402452784032660537998172102876044099509281235822902922248959058492711, 142388236649505, 142388236649505, 580578715961440, 580578715961440, 
    1461864025804167289658714133649602292448175063971, 580613075699808, 580613075699808, 1461596415838362441859455598862257813112626611107, 1461551814177824197152664610067797544538059572131, 1461864025801591910099930732245425747610332038051, 
    580578715961440, 185542907841756801165800578694734280144485352355, 580613075699808, 580613075699808, 580613075699808, 1464356317830588357568695271320917333352907279778, 
    88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 88031866652768, 
    580681799370976, 580686094469344, 1464356317832582207168276303168047247359289601442, 228842373646560, 185542907841756780883390975043062730293032256419, 580680791098401, 
    88238024886368, 88238024886368, 1464356317835240673301050880071292279017733361058, 48526606668269102587544453187528831558675071907, 88238024886368, 88238024886368, 
    88238025082976, 88238025082976, 731110419545566014228979025326678953383424164771, 132876499250053204127652857062343501514054441412196596376778551283343757072117136448543640861693941573, 551485161054599252787988895751659964160240593110359001461221882560037137441668838095124126113264644, 488939176371167750122479837506656181880713256327783968008718928137630499674157553141026467699594272342208380717694967334119649877412147711245273705106453586113949278238775788022828987654694102913814260144579999718710659035175260194100678821683777910097313920622998761, 
    551485161054599252787988895751659964160240593110359001461221882560037663875678388681061817867629572, 234839012131548078085559836105080199830132563338198318611022250068046974525065296633660349376597227498932487400348255543883611114902617517719545809388974783844475022006519385603974406137512067969002604175890734842711639481328222617932207504951225870188562122998760, 282850713142305, 282850713142305, 290547294545185, 16641875742412316784231373977134354840303423123443909307375798524182157023640718156546980745872471044, 
    61847696218876081133648532114025352445965965699128136345754243197869796781017837059089805213469640129870189656078346966552879686632455327101377501606759866467488212049706022, 239867512599282460298726820536461589501687638947, 368231298520029814262402438815419302682451772323, 282850713142305, 282850713142305, 282850713142305, 
    283950224772321, 282850713142305, 286149248029857, 53054727620704, 53053653846112, 88238024886368, 
    88238024886368, 88238024886368, 88238024886368, 551485184257712170723207426278453692238237792974056778249639716234397629292367806759544118629702756, 158606773258464, 730764756684370066222287342824270999519756551075, 
    730775907099504627398975418616329149663840306083, 730753606354306096775833882898056501233614848931, 290547294545185, 283950224772321, 286149248029857, 291962732323023090610657363470801025536376144116876581682062578581469852247580880010041601814506820, 
    45287664297291153648993808650978138268244481317250563670330160614406471449324272285505525987296899035862993609343178554740246496181212267370373719589899750409497238656807, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 268897676423098020835753791724149516861767552324333036874781215910617549419682959670109645048299728196, 269416721272826801985775785541464292775933284380511360933836614225917810256486157768406234569394695492, 2108619733444055966542291085149140100899869405817194885692192211412797122692729368549036842889311236, 291962732323023105016161381752216401732287115977390200477850003430571063239184130926755080711762948, 
    2108619733444055736040073892350231783795746672362558990133177616847413947728243467106780154618508292, 1978658307750130403652078844387023550925337190128941335339870008173111329784261698424267587418865036631653673914376007536767498120442862374124968042252530295595862118915200806, 2108619733444055736040073892350231783795746672362558990133177616847414474162253017692717846372873220, 1978658307750130403652075570996415654783467132576529401807680038276438053742805961390967333919391516468557901239719110707364130424259195728813801516938705951306234377877935910, 183045258415733431442659162770716032405625643939, 142113359004705, 
    16641875556787413440751762143777470093037922804221074878260175784881357109795955222746260086824122949, 282850713142305, 282850713142305, 282850713142305, 290547294545185, 283950224772321, 
    286149248029857, 580584157186272, 265785719963038019306933667855116887407957207679802917800136637640007690955765678458397693222433418116, 1978658810821847388679108615728090579101047978651067971390831864667978036068914964279267975461877719973145713458247487217472370067234666897373050072632793955033044407770146598, 580684011931872, 564325454480417, 
    1462220837730002255269132840286975734142606771107, 1978643241384089909763846640838663517566217621753008739587996067383891851968163714416576312575760263035096576365305019323099566474405700406895824989303594373791173648048973606, 1978643329836334255033792478930624166828642580121624955203296598685449033502152596269628231799593697231084375488892598070056567149897712844548243021114342535062640154720818982, 580584157186272, 580584157186272, 256629561980004568547537148242723635068352586470684813130995139968140735703653191367933689101704056524915884114980518457546403268038815154592510599874165501662802299475750, 
    256629562921964637577751621226329656263099133917018383194382296224208889934676538586616993256519272046398497064536421679184748467731469186822593655338578177267449182443302, 580617442101472, 580617442101472, 228773721278688, 564085171422241, 564085171422241, 
    580617442101472, 580617442101472, 1464357014728881003962411330610203687763667594658, 228773721278688, 16641875742412316784231394584905083586404828919108361468810981153902126270517065813883039218458996357, 158471546996960, 
    580684011931872, 1464356840506301691967284378834157612050862843298, 158471546996960, 53052547564577, 368230612510778101650421410878405158918483608483, 480481077047106023417608928812220475621679691140126938132446925915845818451067871585851485674779503600845030881056129750655237608253697744866894986898412447880805374588361001744356287680997204065845466733522940692808401884709191053896157578041545593395879938624578280, 
    1978643215585518646978916083887156159871267932237536735174074438944238569036254857207932212696333830359420182067519764989913271592453338160472424492767452828466360228944434982, 48526606668273970384419034640617149741071345058, 256629444902802611661739412627240199085161552244778173243235960756986740629479012524466927876685169630196651010660950068126077086006890664238863144024107773695580581127974, 256658928973702200747542086469917423923579749103233441683948161990923798346693511671057231103149319381624985341298556766003577177861368323591714707605544658233161775294246, 259775868603384269922686089263728683130131485468566016744427326236565791813395494038655170418665508, 288621376783731252276945334416367344685631943167213647335793373173177097307585339572461144268354632261, 
    291962732323023105016161448155859307603112226308791559182205673817679543385067670516841524379085700, 283125355906081, 286424025007137, 2967964847334094142790534565495942894290806081588745824760363666416087143454039040971400032281964117562013341988928980736524487739552181626804592627772791707390608062505008422, 268897676423098020835752910709862756525011056959003128318165659576948934283754155627785639305082059333, 2092399566058740735068065036014131628472055539333215595492349126397264093748269972767056759030486116, 
    2108619733444055736040121984730598892290064572253298904587185658392444794017452800824077821914738180, 465066216835937661938260974420118238929494864333171955331588820126930513860957300690797535541515270725, 148985071338529, 185542907841761638558905876609777112021473961378, 989321635434085677161180641965087114300653893817659666921525389682807852426274726002283072800574735964671661775949301924111670603124108066973411608864548411697693072246684966, 283125355676705, 
    1984440019912342195969222754386660348744783430703271039525651334900562624373468978272959509454090119334829458194915764463288214899187813372483771881778855272441588476353160998, 36834751054881, 36834751054881, 36834751054881, 36834751054881, 17160510691429025185760866878542165099105616675, 
    2062168592398009454738483073582752505135686806555657344191751879816041378989950389955011373384394234210699757771692549331437069259438179541574865077308736997365389976064212263, 132875735960437393561945257729544290316199400617296354943943213104411722037246814990504141715744265316, 731110419564195731373076798821243516127178958242, 145274085835809, 145274085835809, 731132719118385533065640293497218937665729332131, 
    1483982438409087793570614092836927756076648413234323876023726887110886219417453821481492099791862292729260962945004370035641778919709488547275921178719928762804513259320753446, 564600567268385, 22858351047118790312341079409045840127043569058, 399673823145441, 1462215438485637117535219554264088352308708273059, 293021195251169, 
    564085171192865, 564188250407969, 568620656759969, 567486785393825, 568620656759969, 568483217806497, 
    568483217806497, 567486785393825, 36834985935905, 142388102202401, 327106055906593, 182710702416187819312595634354685742761533506978, 
    45631079195937, 1461596415840942698722724592725701640651419428258, 365767153431434634298232246806513907940846863139, 36834985935905, 24263303354094267839379794032493113305297618338, 399673823145441, 
    327106055906593, 145274320721057, 145274320721057, 36834851816481, 162201519890827817511536265787101897056688430089044941540925893613117369005752599293441561715644260, 75479248504339073950171048391661825880178811269791609704816428123630267173093951473673537873593226185371165783743980864686518509561406950282497291308893924052517132064550, 
    45287549105766743132238611743755674752840668836765965462870242264128797823041825421436451638355902483502400082387368534219350395076108937133483371175779989151133829977894, 36834851816481, 25690556491317449418341342858051310647612278178, 2108619710240942702854620989769378371493332699280136643416557431851649308117252986145175367680339652, 36834851816481, 37934363444257, 
    44531466765345, 2108619710240942702854620989772628414078086633454879002907031792481733166579700258732935756126432964, 2108619710240942702854832306403898621896351482245503451496233976121316639492875668088214478861184708, 36834986165281, 108303241972961, 36834986165281, 
    72019123143713, 72019123143713, 72019223905313, 72019223905313, 72019358254113, 74905442321441, 
    298937397101151230930536545322285907068455008716405370289812855926230733386576862681559111381363210821, 88004150495328, 2108619710240942818105621363643031080818009042086879280656051476713042161879809224100738728112237892, 88244668663904, 145274186499105, 149672233010209, 
    1070530010783380518061108401250008830808941323650020090672272810615024616868070985346791216033844324, 290697560111706829943434310504335278661232069711091651872526776330472898002617775934295241476430117445, 966149122907510248296126204581808566603189877065825473055087098563131319285553601390346849682955695287455925608994834009148524735293456218521750626645390215573554569369382, 283950224772321, 16609688693064941272390051504078365796348309773574930072459219318007600310722599722875078786511161028, 182866808207135930470836328696010979763768533923, 
    183045214849288909297845541368941381519352800163, 183045214854273533296870515141649719302077817763, 25696131656432430395413549300015874831639119138, 25696131656432430395413539855282838723604514082, 154207986922913, 185542907841761638598597329414512522271222408610, 
    185542907841761638598597329414512522271222408610, 145274186499105, 185542907841761638598597329414512522271222408610, 185542907841761638598597329414513085216880862626, 989336701756513946551633305859901898115936771060957333712967801314443117209407033117605087431733340660226519630279920940350038322847302712359872640711260359131573531414867750, 36834751054881, 
    36834751054881, 36834751054881, 36834751054881, 36834751054881, 145274186499105, 145274186499105, 
    731110419564195731412768251625978926374779921826, 145274186499105, 145274320721057, 564188250506273, 564085171192865, 564085171192865, 
    568620656759969, 564085171192865, 36834985935905, 327106055906593]) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel


private theorem tv_b11_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44538848649505, 44538949312801, 44538848649505, 282033360478497, 282033461141793, 519044857478258431224927348913358577860456706946898352136632176955061585460679309884105158674298117, 
    266529538259592713261084123339689282262670312031212436050035342328378926152146714291314930460641040420, 266529538259592713261084123339689282262670312031212436093176308139508280139940854537552190859284420644, 267886954284390445574071078493450397308759794386031781446571119598062259318942787106971927180902722405, 84121267315105, 2135991223254437984746673734937780556798411501574317053291269305080394540947142966953732060909988709, 266140254622296127312129299186440290769307979327943446858122296418142644139076025152119188581832038436, 
    91355351197792352758278187256483970604033640354, 141872971417696, 265750970984999482815610430483453287654720476041595239667395950134249470782536131160317453919024420900, 265750970984999482815610430483466287825253209414949977460405333147096644468692756544807131083335374884, 141872971417696, 36319855151200, 
    36560373319776, 36319855151200, 519052773592314808620951952878429528499687685824660793738222441783778821940779783000071940679505956, 11429175534193259687576444552099457472706119586, 571789033906465, 1461507212517389554755246540980438905766912491939, 
    571789033906465, 571892213784865, 35742755856673, 141295972786465, 141295972786465, 563096120992033, 
    563096120992033, 519052773592314808620951953245298884096815844001878235966239972047389959731348967837099172441462820, 1038097623321096073894050824243954207278306299171730693471514646715681313533111146990003211752020004, 571789033906465, 571892213883169, 567425447829921, 
    177061642766560, 177061642766560, 177061642766560, 519052773592314808620073089333369249175410802349572862293192422692837790373524405521134468995323940, 177061642766560, 141979275102432, 
    61832600598648638020570484964173728965800415309145707011219247430918064923509617443035525406669674676445523033360990694982933502699656427947531190752809713633409444409648934, 141979275102432, 35742755856673, 141295972786465, 141295972786465, 563096120992033, 
    563096120992033, 268086696572633456944473943235793159315930706974597350010997670356238355588508488977327167771408150212, 401481222952930212500126771340084097847224634114064840642560768271170241801574665029668293250677550788, 730764778453157326950446389265263201898803537186, 36842267255073, 36842367918369, 
    36842267255073, 290829453500705, 290829554164001, 22836050387010971646546585449079425585419157923, 81922479172065, 267859962938431858908404585158080272904445380002028743049414247542502765231922026912406642013778923877, 
    74225662665185, 2108999877295851319080180399567656152483997117571278656134397249520900453926382772388446893786190181, 81922479172065, 91366501612926913934966263048542120713757656994, 141872971417696, 141872971417696, 
    36319855151200, 36560373319776, 36319855151200, 290829688381729, 11440325949327820864264520344157607582430136226, 1461529524151540669285956585730406476968523498403, 
    1461529524151623826848418907526698991945001239459, 1461529524151623746352605793034131996904347698083, 1461529524154116058352118279920486170193756717987, 36842502137121, 36842502137121, 36842502137121, 
    83021990505953, 291929199781153, 36842267484449, 145694019297697, 73126251864545, 45638595421473, 
    290829688381729, 45638595421473, 81922479172065, 290829688381729, 145694019101089, 36842267287841, 
    145694019101089, 1461529524236694338082845244603254143563006518179, 290829688185121, 1461518373778941403974384608945450520566342648227, 1461864035332094017699241315694576423383941030307, 1461864035332094017699241315694576001169865351587, 
    1461864035332094017699241315694576001169865351587, 81922478909921, 290829688185121, 177061642766560, 177061642766560, 141979275102432, 
    234839179937625725399785637170026631905791442318244139240761352556851894793540841549500167086573721909217168821110234999747824250231339354401499247709445993959818928543200940140226929902426912180625618004737454192103263063350298457329886160329890452218000123494281, 11440325938693956333165386317042978760876885922, 177061642766560, 177061642766560, 141979275102432, 141979275102432, 
    423600289090016, 1461529524151623746352644478660360197203579405219, 36426158835936, 141979275102432, 36842368147745, 488927266614483527188666297671265138138231160342456660308215515478150195860818728940971640348494930510471421205511727851498656121261255892701331139423825376713200670136530577424803526330487453414830152084163308519250188992099775978930420842800017353081897088124938761, 
    1978884747222783456185379191100483388765130552759692159062909161175373963017227322123509295609850297551749768951612288320888437991541760332204659286546943485011581351409725222, 45638595388705, 290829688381729, 36567889741920, 290829688381729, 45638595388705, 
    22858351047138910539610666257579863707628897187, 283132872106273, 283132872106273, 283133106988321, 283133106988321, 36842267484449, 
    142395484414241, 177579889860897, 36842267287841, 142395484217633, 142395484414241, 283133106988321, 
    283133106988321, 1461529513350150899104942563246621978563360883619, 564092452512033, 564092452512033, 1461529513347658677108622692564555205986360525731, 564092452512033, 
    564092519657889, 564092586828065, 141983167815969, 282858229343521, 564195632881953, 45694401224110967890824698060184156271556985763, 
    182710702405574075642589569169902778042418234275, 730775907099525072145846121975095445811797984163, 71752063923617, 142120875205921, 282858229343521, 564332970909985, 
    564332970909985, 282857994461473, 282857994461473, 36567389839649, 142120606769441, 282858229343521, 
    282858229343521, 142120606769441, 36842267255073, 318317512631585, 36842267255073, 24976929922695149516470799243815114423536763171, 
    290829688381729, 290829688381729, 265811792590005360315000283544750211689065523584806084539262089115086989585203733232451731961627343429, 79723590263073, 290829688381729, 290829688381729, 
    44538848878881, 150092065808673, 150092065808673, 290829688381729, 44538848682273, 150092065612065, 
    150092065612065, 290829688185121, 1978643226642049188448275514282335596360334153916591705545571203266111934756485911779450602938525638149413622843903736911000338623614780312303907709066347647824836608274421542, 265807737552056429439041995755217920631544499608146838780830061328379358059949560130303250816518912581, 267827399859917987289356521017186770752455264120739252408581600694254743145051321482077415516658008964, 150092065808673, 
    290829688381729, 150092065808673, 1462934465657105647298634020235175039534737949091, 571789033906465, 571789033906465, 1461507217961907425490261956394432624675203875235, 
    571789033906465, 571789168222497, 571789168222497, 213449211119840, 72707427797216, 571892214276385, 
    72844862556256, 72844862556256, 72638704126048, 72638704126048, 72844862556256, 72638704126048, 
    72638704126048, 72638704126048, 2052371371315403541614559934292352371708363918009079696877117222637762781027665102380355344071577886433240535861246868602575022030417201507659756204906286921336954565718697766, 143078384470240, 495070292216288, 241537395990455532404661607022772314804523262191177869786697130884535018194882324987273827821308005168166669084639520559219005995437555796326056955693086049214837369231142, 
    44263971234081, 213380558751968, 213380558751968, 213380558751968, 213380558751968, 143078384470240, 
    495070292216288, 495070292216288, 72920234199392, 44538848649505, 44538848649505, 44538848649505, 
    44539117314337, 44538982965537, 72920234199392, 72920234199392, 143291127957984, 22880651856306457964047589284486984122350699938, 
    149576703549729, 354397358393696, 494932987480544, 72851506333792, 72851506333792, 8305731417490991822198750988250692466801143723125570014684467186718712480143613388964821325217687653, 
    11507206662063704983404066160907277331625150370, 265815784267942908839380841476552725439264220120388200709031968028485073768323732822143885558332333381, 8305731417490991822198750988250692466801143723125570014684467186718713077082177825095652088836417637, 1461864025804187743912926861876721035868440142243, 11507228440135187924085906766956143749842339746, 22925253537925832852675517834519905690251167138, 
    11507228440135187924085906757732771712987563938, 567494167306657, 564092452512033, 564092452512033, 1461529513347658677108622692564555205986360525731, 564092452512033, 
    566291542913505, 568490633339297, 213449211119840, 72707427797216, 567494167765409, 72844862556256, 
    72844862556256, 72844862556256, 72638704126048, 72638704126048, 72638704126048, 143078384470240, 
    284168070629856, 283961905908064, 143078384470240, 72844862556256, 213380558751968, 213380558751968, 
    213380558751968, 143078384470240, 143078384470240, 424699398457824, 72709640292576, 143078384470240, 
    6559998005155875671795276005997647789902152602174762625604399404117417065935997527971294023111235392136759542020291619114137023820374324012857883704173123032327190092380811577800534872248024462474358933150740587733950518564325381772113812045549899634725638159458207573952838609726233641081931896193930554956572997287475958743066428468826280697071433785127138398307621839915, 11440328570585812451527870566639035493134680995, 354397358393696, 72920234199392, 143291127957984, 91522606786552546612432809996723952924590379427, 
    354397358393696, 354397358393696, 494932987480544, 354397358393696, 143291127957984, 283751586728288, 
    284026464635232, 354397358393696, 283751586728288, 284026464635232, 283957745158496, 732180853993946377509377030002552157031226180003, 
    283751586728288, 283957745158496, 284028681324896, 22925253537946277599698546427630048251549844898, 354397358393696, 72920234199392, 
    72851506333792, 283957745158496, 283957745158496, 39618390034528, 39618390034528, 265751980780621178533169708502942808043426501670120649039660670347236940229473550247493808884040398788, 
    180360177649888, 145171509545184, 180360177649888, 180360177649888, 282362429731406690676345327770024509745648094966542045806405476232422908495307235237568497501207905156, 571789033906465, 
    571789168222497, 571789168222497, 35467878211873, 145206540765408, 145206540765408, 215579582007520, 
    215579582007520, 39724693719264, 39724693719264, 145277809920224, 145277809985760, 281758482833697, 
    74908663548128, 145277340616928, 145277407725792, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277810378976, 145277810378976, 39618390034528, 180360177649888, 145277810116832, 
    145277810116832, 39618390034528, 265752994540108411252271842382692025685938813880171198419623098311608482187255858523174602410685691844, 180360177649888, 180360177649888, 180360177649888, 
    11774838382263161731821259345920656661845378978, 1461529524151623746352605793034131996904347698083, 36567389839649, 145206540765408, 145206679177696, 74837727381600, 
    74837727381600, 74837727381600, 145206436956256, 145277541943520, 215579582007520, 39724693719264, 
    39724693719264, 145277809920224, 145277809985760, 290554575855905, 74908663548128, 145277407725792, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277810378976, 36567490502945, 
    145419544300000, 74837727381600, 74908663548128, 249081520042175852701008967875103546052691429028832122841110366012771736957970197074685083815900635637666742658164775363776965385185003547980719153351579303204077353025318, 44126632943905, 79235773892704, 
    79235773892704, 79235773892704, 79377579116768, 79235773892704, 79235773892704, 79510651799648, 
    79235773892704, 79441932322912, 184758224160992, 219977628518624]) (b := []) (by decide) ?_
  decide +kernel


private theorem solve_canon {M : Machine4} (hG : GoodMachine M)
    (hFirst : M 0 0 = some (some 1, Stmt.write 0 Dir.right))
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left))
    {r : Fin 4} (hM20 : M 2 0 = some (some r, Stmt.write 1 Dir.left)) : False := by
  obtain ⟨hm1, hv⟩ := mk_step2_hm_hv hFirst hM10
  have hm2 : Matches M ((baseTable.set 1 0 ⟨2, 1, true⟩).set 2 0 ⟨r, 1, true⟩) := matches_set hm1 hM20
  fin_cases r
  · exact tv_b11_3 M hG hm2 rfl hv (by simp)
  · exact tv_b11_7 M hG hm2 rfl hv (by simp)
  · exact tv_b11_11 M hG hm2 rfl hv (by simp)
  · exact tv_b11_15 M hG hm2 rfl hv (by simp)

theorem step_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H4 := by
  intro M hFirst ⟨q, hq23, hM10, r, hMq0⟩ hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  rcases hq23 with rfl | rfl
  · exact solve_canon hG hFirst hM10 hMq0
  · have hG' := goodMachine_reindex23 hG
    have hFirst' : reindex23 M 0 0 = some (some 1, Stmt.write 0 Dir.right) := by
      simp [reindex23, swap23_0, hFirst, swap23_1]
    have hM10' : reindex23 M 1 0 = some (some 2, Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    have hM20' : reindex23 M 2 0 = some (some (swap23 r), Stmt.write 1 Dir.left) := by
      have hswap2 : swap23 2 = 3 := by decide
      simp [reindex23, hswap2, hMq0]
    exact solve_canon hG' hFirst' hM10' hM20'

end OMA.BB4H1

-- Step BusyBeaver.BB_4.R2.H1.R1.H4.R1.H4
-- Credit: @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H4 := OMA.BB4H1.step_proof
