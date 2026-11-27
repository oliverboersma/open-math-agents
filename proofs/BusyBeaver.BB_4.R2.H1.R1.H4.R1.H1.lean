import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1

-- Checker and branch certificates from @hyprspacecoyote, PR 4446.
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
  let extra := (val >>> 1) &&& 15
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := (val >>> 5) / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val.testBit 0, ⟨extra, (val >>> 5) % dfaBase⟩, payload >>> width, payload &&& (initialBase - 1)⟩

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


-- Each three-bit tag selects a recurrence time, a certificate, or traversal to the next missing transition.
-- The soundness theorem below applies to arbitrary tags.
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


def witnessPos (tb : Table) (i : ℕ) (cur : HistItem) (prev : List HistItem) : Option Position :=
  if cur.step ≤ i then runPos tb (i - cur.step) cur.c
  else
    match prev[cur.step - i - 1]? with
    | some h => if h.step = i then some h.c else none
    | none => none

theorem witnessPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {i : ℕ} {cur : HistItem} {prev : List HistItem} (hv : HistValid M (cur :: prev))
    {c : Position} (ok : witnessPos tb i cur prev = some c) :
    M.multiStep (Machine.init []) i = some c.view := by
  unfold witnessPos at ok
  split at ok
  · rename_i le
    have live := (hv cur (List.mem_cons_self ..)).2
    have eq : cur.step + (i - cur.step) = i := by omega
    exact eq ▸ (show M.multiStep (Machine.init []) (cur.step + (i - cur.step)) = some c.view by
      rw [run_add, live, Option.bind_some]
      exact runPos_sound hm _ _ ok)
  · cases mem : prev[cur.step - i - 1]? with
    | none => simp [mem] at ok
    | some h =>
      simp only [mem] at ok
      split at ok
      · rename_i time
        have eq := Option.some.inj ok
        have live := (hv h (List.mem_cons_of_mem _ (List.mem_of_getElem? mem))).2
        simpa only [time, eq] using live
      · contradiction

-- A recurrence witness gives a reachable starting configuration, a period,
-- a guarded tape width, and a choice of side. Both the run into the cycle
-- and the guarded period itself are checked by the kernel.
def checkWitness (tb : Table) (cur : HistItem) (prev : List HistItem) (i p width : ℕ) (mirror : Bool) : Bool :=
  if 0 < p ∧ i + p ≤ 107 then
    match witnessPos tb i cur prev with
    | none => false
    | some c =>
      if mirror then
        checkGuardedLeft tb.flip p c.state c.head (takePad width c.rs) c.ls
      else
        checkGuardedLeft tb p c.state c.head (takePad width c.ls) c.rs
  else false

theorem checkWitness_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hLoop : NoRepeatHyp M) {cur : HistItem} {prev : List HistItem} (hv : HistValid M (cur :: prev)) {i p width : ℕ} {mirror : Bool}
    (h : checkWitness tb cur prev i p width mirror = true) : False := by
  unfold checkWitness at h
  split at h
  · rename_i bounds
    cases hr : witnessPos tb i cur prev with
    | none => simp [hr] at h
    | some c =>
      have live : M.multiStep (Machine.init []) i = some c.view := witnessPos_sound hm hv hr
      cases mirror
      · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
        exact hLoop i p c.state c.head true (takePad width c.ls) (ListBlank.mk c.rs)
          bounds.1 bounds.2 ⟨ListBlank.mk (c.ls.drop width), by
            simpa [Position.view, takePad_foldr_drop] using live⟩ (checkGuardedLeft_sound hm h)
      · simp only [hr, ↓reduceIte] at h
        exact hLoop i p c.state c.head false (takePad width c.rs) (ListBlank.mk c.ls)
          bounds.1 bounds.2 ⟨ListBlank.mk (c.rs.drop width), by
            simpa [Position.view, takePad_foldr_drop] using live⟩ (checkGuardedRight_sound hm h)
  · contradiction

def witnessTable : ℕ := 0x200a010002de085960008680441b812a100431780244400612001c58004230010460c50a00205c00c040220220041480106400b1a81163e086960118420078f013e00008128036260460e802a1c0082c0021080081483140e08a0203103e0118580183800a15823c0600f16032600006170018600071b800a6a0118701300c0071702120a0c70382143a0041882300a04e8180367a0c9058024540d286001c4604593801e4a04897801e4c04492041e040898a01125010b01021264044ba81144400984020a5e0c80100206e0068f801c780419300284a1090684344609900804b0e04d040428060080e83b41005283801e2c08c81801f000c4888424200870401127600c46001056008a0052e0600d08801c5a08989002a120088803202a00a9802381008b000124140029a01185c1058b013a1000c06011a240c58a822e0c0c6838025360841382102200811800a4c0c7030022340079703260600e23010c3a0080480126200b86821a1e0880381241e00908802a180478900165600846003098045988344020009d000a5800d1103240a00985820c3601285800c4404a0180066000f0a80074800792801e1c0079a010e5408e0102400600d97802a9c0080d026614056880020cc0070e001cdc0079c001a6004392801aa00880b80165e0059e00202a005a08016aa005a400502600b3001203c08b8702084400a8b000e540088706b8060121906900604e0582302e00901802c0604a850002c60c48e0460041950181221c0cb01814c140009f00027a006898116320069581484a04a8181361408982812e040051303145409500023c0008e8080320604c8b842a0c1120102360608589010e400468e01040800699010c3e00b1380143404f0b832c0e04419000884002128222120051a811c34001a70006500449002080a00b118018700c40b820e3e043980290020d480001c60091060004581058900284604b0784300204e07802a2a00a09841c0208e82820c320830e821e360439e8238020480d035016042958010540088484340004e13800a5e0cc0082161c0c50a8028360078982360608c010330260079801204c08c0202340a0429904360804807822a080ca85051e1e10483013a14010040034100490c011c240538283101a10b060118440031882320608f06821c2404d848026640459101045008c018316060068c832a060478a0002d204888820c1400413859c0004510021c3a0458b012434000b5811a3811c01012a1a04591824a0a0009c811a4a08609801c6c08587000c4c0069300501a008940024620860d00285c0440f8018240041a82181c04214011634045a001166804592802a3e0019380204a0498980083a002118008420449b81183c0088a0026280c78002182e005170230100861200342c0c6058016240009b81303a00217805492000a38116560061e801c8a0093402300e04b848220260050a02381a007090410180821280026000c020002e000a0201480804e0281381808a8600343c08e00801c5e006268014a215f000104660868981301808488001a3a0039302200800696032c000ca0002280208804011a420c38981342c0421602184600615022c160c38b812e000850d821c1600d81823e1c08d040002820cc8c86544600aa581249a00c4f8038cc00e838210520440e02086e04f1d0226300498d80230e09e01842a3601e1b0124380198300c00c0c80601162409104003a1c000b600460c08c05014a000148304281c08d01032a1808784800a7408a8281222c0d185800c6000722001c9800735810c340080f80185a0878400067404118801c660052e802caa008328018ca16300000c8216f000024160058d0016640031585a40208a0e010c5608c0000424e014210016440c60c83180e0838b803efe0009982204600d0e80224408a0403301008b0401105600805803a160c4070014a00850c032c90098820330980098c00262e004a08012a20049e801a4208983810e5c04a87810e760439583141c0071a801672005a6811e1a0c6848110460c38f8016940498601321a0c48703520004e06014c200478e8334a804f82800e9008312022c0e08882000c4a04918821a1208991023e080839080303808a058012a60099b02401405180023c0e00c0b0018501050d0016581040d041c360051400203a00983001e2404b07031834005940022180c90900163c00e850034140840d00321404c840038140098582201a04180801c500088800301400889000a6e000818234020440c81401e045908138320cd07021e16047020126200051501162c04f008004420c582831e0a00109802e120010d0310301060f020c440490700202c00c0a003a32086030030000c60304241400a0e80025a005968122100838f812a3204a11002678007880212341100082220e0429781224204809012e200480d82181000998002a1c0448d01163e0c8040312180011a00265804908002e2800810001c280c50402087004c0c02203004f0e030e1600423801ca60062700164208499814c100498c002c2000a0b836a000820f002c240ca028030e6083978366020d380820e3208789811e2200a8482242e0c48a021a18088868136540c408011422084038226100c680821030104898022060480281244204b0080246404b03020a30108010028100c3030134000c489010c340c4038218220058f011e2a0c501842c020418f810c3e00316820a3e0050c820c3c0d201820c280091182162c00982002c1800197001842089028134140011700064a0848b8210360488501144c0c51303280408b818316240478801063800196000a5e0080d810e4e0080c81064004785801c2e0c58383300c10488820c4a0068a030e2010588012e020848a80183e0858800241e043168108000848903121c0090f01102608903801c2a0870701182e00707811e340830d030c3e0868b0108460071381280e047058220140c5038002080820e011c1e04803801a6000633841602086850116520468980029c04e008108260039580104c0440b00242c044100018460488902204200895001a680500201044a004248024880478b8004040cd018014080488d001e3a0060d03200800592010e380c410812c220448b02181a04782811e1c000988234120840e001e3c0091303141c0830e030c2c00787013208002188020260c70403241808682801cb00058d02241a0009b0220120029b0218220069d0322020049601083c00294801a5a005908016620059a0208360058c8002c80460d80025004f06010a4800497800e620039e822a0200c0381125e08f04801266004a180241204903801a9c0011381123e0068e020c3c0c508011c280840e82221c0470800064c00986021a2600799001450049068012720049281221a0450c80025e0051080241e0078a800a5a08507011a1c0450e801a4c0480681163a0480482304604a040218280858a820c200450c02241c0840c0008540078a02220c0070b002a280438d031e0c0090282142400705022414048050014380060e8012500c407802c840070c0234020460681182608504822c020418d802a300029800124800a88000a4c0c48581082800980002e0c0c40503101000410001a4000687030e240458e030c180009c00243200711821816005910136380060c02280a0438e8342020838a000e6000399820e420d68003240c0c5058312180078b001a2e0080a001c4204906810c2e0c601801a2e04588022a020448c0116280448e810e3200312800a4a0080683200210583800a5408a83000a4a0c681011a280049981300600708021c1804784001e0a0440b8012320058e030c4000214810c400888101242a008078008360040f83100a0088580026a0060a83180a04704011e0e089800124060080881201808702000c3a0019281181e0460c8010380c3080314180009a0136000019800123a0058881320404a0382320008409002c0e0071000143404282801c3c08b01820c2e0878280143e00592041c180448b001c3604706811c440c606012e0808a0380261204c09801e46005950318200850900281404b0601261004b0200201804b86001a240c40a80083000397820a2e08404011c1a08586811246046910014420438b820e360010e0214280c50c82121800a83010e2c0c90500025808c0081220c00808811026045098316160450b800a520418c030c1004c80030e1a0049a001c2408783811a2000394801494048080014320888000125604490010a4008902021e1a08a8680248c00191030e1e00083031a0600102031e0400295022200083898106440448c8010360c48303161e08b81821e0c0058e822806009068328000850880024c08c0602220a00410000c400860502241004903820c260c383833c0004c020110300860981201604a83801652088028228000040d02120200490813c0e046868012460448d83121600783011e1804884012a100c510001a340488680145600a05810a4a04508801a2004210011838001950318280c70a83140a0050b030c1c089000320140068a00103c0860200262204489022a04086848212200450a03121000807801a1600513020e20085840012460c70280181000989831e020009281141e0c701010a340c501810c32001918224000878081260c0050f82122604312810a3e0450a01122a003910228040020f822c04003110114260478502200e08981801c180040e800e4804a8280221a0049f02240c00112002014006868012921068002161a0058b8116280850700025e049048018220c600020c300030f001e3008705810a4e04589800e2c04489010c320438d01083a0c482800c3c0440a002424007080008400c3848322000049300182c00102800e3e0c500820a2a0078600280c0490481163404686800a460039c031006006830208320448e02102c000990224040c30c801c100078502121e0020b0014440488880064204687811e120840601181e082898020060428e011a2204505020a2c0c30501220e0440a8014240088380164c0411000025608901022604084858010440870380024604684000e4e08485820e3a0c388821a0c0438c030e040c801012a00089800324060c88180102e04605801a1c0028e0018580418d810c260030e0024100830b031c0608a81812406003940128100088580280e04b018002560048d80124e0058a011632088810130000019082140e0048b0012360078501044c04685810a440058c021a140470300183400589821c0c0040b020e1c0011180141e08585002a00001148014380c4060014480078402181e009058014220438f0310380430b811a1600705000c3408805011c1608505830e0a04981820e100820b01162004507011e0600310001828082890018240410f8220040040c020a280488100162c045878010300009280160a0048a831c020cd00832c020060701063200390800e5a00497011c10007868212120448a821c10084080120100080481161c0068801044608306800a4204800011820085040006080029180042c00392801e100428e821a08003900024000468302121804181800608049820214160049580200e0048e0124080420c010e280420d811a0a085840018200050a820c1e0030b00123c0010f01280a0068680043208389800e30084028122040488200161e0018e03180604703001c1808801021a0e0420802082a0438a02160c0418b010a2e0048f00122e0010a801a120848701200e006060002520028f8128060430a001a160c680001c1e0030d80080e0428d0014260010402120c0098300240e0c9000028000009381081a083888118100039100202608407020a220040a0118180428981121c08506000c320420780063c0038c000e380860301161804488821c0a08583810a300048c0216000c581011a10002908210140010381062c0028f0016280018e021812045068116120c682800c300850200083804505801026043080212100830a012c000050b800e3404980811222087808218080480180060604783801e060418a800a3a08284020e180060700122a0070101160e048018008280018f00200c0820901240204306000e3c04388021a000430a0004400410302101a00587820e1800507800c2a000900116160880082120c0070281101a0428a821e0604586801c0c088008012260028d80180e04780810a2c08383820e1404389801020005860110200840781102200584001e0c00880011e0a0058501280204603821c06083878012080c481800e38046040118160038a020c2204503800a3208381801814000918008240010e00200a08288810e240018d01220008405011c040428c001024002008108160828580121c007038110140020d80023e0c48000082c08286000e3400489810c0e04683011c0800588020a1c084030116120430701043a00505020c0808700800c220460201160a004840120080428a001614006848012200048802140c04485811410007040218000060581161400508001a0a00106820a1e0418302100000606821a020038902082008781020e16086018014120050680161a0020801082c046818006360008402081e08286020c2600108820c0a0840001062808701810a2600583020e100040a82160604486000c2e0c58001082a0040701121c08281000e2c0020c82100404309000a32044040104340850081060a04189010a1e0868102081a00483800a2e04204810a0608501800a2a04485811c02084818216080868101120800683810a220870002080c04504810a02043888006320440381160804308021604000908012180030a800c240028d800e20045060010200420181160c0018c001e00044070118080028a01062604483011a080830582140a047010108080008f81121208383811e060040280140c04603010e1e0418800023a001070002100830701043000487020c1200307011018082050016120420280121604304010e1604407810e1a0040502101208402811a000448401042c0028b80023404382000e240820401120e004048218020068101140a0008e00141a0040301200200207810e1c042880112180038a020a160850082120a0020201140e0020600181004209800e1c0010d00101c0828480062e08580010622001830008280010c00160e0468180101a0828200180e08283000c240830381140a002828118020430500062c04405020c180038780081400486820e020448280062800183800a240410400080a042868008060028800140c00582800c0c0028000200000505810c000008d021804083010012160038201042804187011c0004780010c0004208010e1a00304010a1800307810e0e04187001c000028981061000602800c1604384810a1c00209811602002048118040038800101404402010c1c08401800a1c085010014100438400062a0038480062400288000c2200385800e1a04385800c1a0008c000216083820004120038300042c00406000c18043068018040440301101000483001210004820014080848181061800189810a16042838002160430101042400287010a040008c010e020018881140600286000e1404581811604043838016040038680022c04601800c080428501081c0010a810a120018780022804184000a1a08480010c140068000022e00184000610002080006200420381061404680800a140040200080e0050101061400282010c0a04402800a1000404010c0e04500010a0c00305020e040020701140400403010c100458080021804284010414041860104200460001081800285000c100010581120600185000e10001878006180448100042400383800a0e043820002280448081100604381800a0604480810c0a00089000c0000283810a08003820018000030201081404500810e000410781100000206000422004810104180018500061a00088000218042040002240430101100200087801004003030016000010600041c0438100081000205000a100440100021e0030100022000500000e020038100100000480


def witnessAt (tag : ℕ) : ℕ := (witnessTable >>> (22 * (tag - 2))) &&& 0x3fffff

def checkTag (tb : Table) (cur : HistItem) (prev : List HistItem) (tag : ℕ) : Bool :=
  let v := witnessAt tag
  checkWitness tb cur prev (v &&& 127) ((v >>> 7) &&& 127) ((v >>> 14) &&& 127) (v.testBit 21)


def readTag (code : ℕ) : ℕ :=
  let low := code &&& 15
  if low < 3 then low else if low < 15 then 3 + 16 * (low - 3) + ((code >>> 4) &&& 15)
  else (code >>> 4) &&& 4095

-- Each word ends with a sentinel; the next word and the automaton data
-- occur in exactly the order in which the traversal consumes them.
def advance (code : ℕ) (rest : List ℕ) : List ℕ :=
  let low := code &&& 15
  let next := code >>> (if low < 3 then 4 else if low < 15 then 8 else 16)
  if next = 1 then rest else next :: rest

def advisedStep (tag : ℕ) (tb : Table) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : StepResult :=
  if tag = 0 then limitedStep 0 tb rem cur prev
  else if tag = 1 then .done
  else if checkTag tb cur prev tag then .rep else .done

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
  by_cases hz : tag = 0
  · simpa only [advisedStep, if_pos hz] using limitedStep_sound 0 hm hG hsum hv h01
  · by_cases ho : tag = 1
    · simp [advisedStep, hz, ho]
    · by_cases hw : checkTag tb cur prev tag = true
      · simp only [advisedStep, if_neg hz, if_neg ho, if_pos hw]
        exact checkWitness_sound hm hG.2.2.2.1 hv hw
      · simp [advisedStep, hz, ho, hw]

def guidedTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, _, _ => none
  | _ + 1, _, _, _, _, _, [] => none
  | holesLeft + 1, used2, tb, rem, cur, prev, code :: certs =>
    match advisedStep (readTag code) tb rem cur prev with
    | .rep => some (advance code certs)
    | .done =>
      match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some (advance code rest) else none
    | .missing q a rem' cur' prev' =>
      if Nat.beq holesLeft 0 then some (advance code certs)
      else
        checkMoves (fun m rest =>
          guidedTree holesLeft (used2 || Nat.beq m.state.val 2) (tb.set q a m) rem' cur' prev' rest)
          (movesAllowed used2) (advance code certs)

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
      have hstep := advisedStep_sound (readTag code) hm hG hsum hv hu
      cases hsl : advisedStep (readTag code) tb rem cur prev with
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


-- A subtree starts from a partial transition table and an already verified history.
-- Each group of successor moves is checked by separate kernel computations.
structure SearchNode where
  tb : Table
  used : Bool
  rem : ℕ
  cur : HistItem
  prev : List HistItem

namespace SearchNode

def Valid (n : SearchNode) : Prop :=
  TreeValid n.tb n.used n.rem n.cur n.prev

def result (n : SearchNode) : StepResult := stepLoop n.tb n.rem n.cur n.prev

def branches (n : SearchNode) : Bool :=
  match n.result with
  | .missing .. => true
  | _ => false

def child (n : SearchNode) (m : Move) : SearchNode :=
  match n.result with
  | .missing q a r c p => ⟨n.tb.set q a m, n.used || Nat.beq m.state.val 2, r, c, p⟩
  | _ => n

def atMove (n : SearchNode) (i : ℕ) : SearchNode :=
  n.child ⟨⟨i / 4 % 4, Nat.mod_lt _ (by decide)⟩, ⟨i / 2 % 2, Nat.mod_lt _ (by decide)⟩, i % 2 == 1⟩

theorem check (n : SearchNode) (fuel : ℕ) (certs : List ℕ) (hCount : (holes n.tb).card ≤ fuel)
    (ok : guidedTree fuel n.used n.tb n.rem n.cur n.prev certs = some []) : n.Valid :=
  guidedTree_sound hCount ok

theorem split (n : SearchNode) (h : n.branches = true)
    (children : ∀ m ∈ movesAllowed n.used, (n.child m).Valid) : n.Valid := by
  cases hs : n.result with
  | rep => simp [branches, hs] at h
  | done => simp [branches, hs] at h
  | missing q a r c p =>
    unfold Valid
    apply branch_one (q := q) (a := a) (rem' := r) (cur' := c) (prev' := p) hs
    intro m hm
    simpa only [child, hs, Valid] using children m hm

theorem cover12 (n : SearchNode) (branching : n.branches = true) (used : n.used = false)
    (h0 : (n.atMove 0).Valid)
    (h1 : (n.atMove 1).Valid)
    (h2 : (n.atMove 2).Valid)
    (h3 : (n.atMove 3).Valid)
    (h4 : (n.atMove 4).Valid)
    (h5 : (n.atMove 5).Valid)
    (h6 : (n.atMove 6).Valid)
    (h7 : (n.atMove 7).Valid)
    (h8 : (n.atMove 8).Valid)
    (h9 : (n.atMove 9).Valid)
    (h10 : (n.atMove 10).Valid)
    (h11 : (n.atMove 11).Valid)
    : n.Valid := by
  apply n.split branching
  intro m hm
  simp only [movesAllowed, used, moves12, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

theorem cover16 (n : SearchNode) (branching : n.branches = true) (used : n.used = true)
    (h0 : (n.atMove 0).Valid)
    (h1 : (n.atMove 1).Valid)
    (h2 : (n.atMove 2).Valid)
    (h3 : (n.atMove 3).Valid)
    (h4 : (n.atMove 4).Valid)
    (h5 : (n.atMove 5).Valid)
    (h6 : (n.atMove 6).Valid)
    (h7 : (n.atMove 7).Valid)
    (h8 : (n.atMove 8).Valid)
    (h9 : (n.atMove 9).Valid)
    (h10 : (n.atMove 10).Valid)
    (h11 : (n.atMove 11).Valid)
    (h12 : (n.atMove 12).Valid)
    (h13 : (n.atMove 13).Valid)
    (h14 : (n.atMove 14).Valid)
    (h15 : (n.atMove 15).Valid)
    : n.Valid := by
  apply n.split branching
  intro m hm
  simp only [movesAllowed, used, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15

end SearchNode

private def nb3_6 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb3_8 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb3_9 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb3_10 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb3_10_15 : SearchNode := nb3_10.atMove 15

private def nb3_11 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private structure BranchChecks1 : Prop where
  tv_b3_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b3_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b3_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b3_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨0, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b3_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b3_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 0, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb3_6_0 : (nb3_6.atMove 0).Valid
  vb3_6_1 : (nb3_6.atMove 1).Valid
  vb3_6_2 : (nb3_6.atMove 2).Valid
  vb3_6_3 : (nb3_6.atMove 3).Valid
  vb3_6_4 : (nb3_6.atMove 4).Valid
  vb3_6_5 : (nb3_6.atMove 5).Valid
  vb3_6_6 : (nb3_6.atMove 6).Valid
  vb3_6_7 : (nb3_6.atMove 7).Valid
  vb3_6_8 : (nb3_6.atMove 8).Valid
  vb3_6_9 : (nb3_6.atMove 9).Valid
  vb3_6_10 : (nb3_6.atMove 10).Valid
  vb3_6_11 : (nb3_6.atMove 11).Valid
  tv_b3_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, true⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb3_8_0 : (nb3_8.atMove 0).Valid
  vb3_8_1 : (nb3_8.atMove 1).Valid
  vb3_8_2 : (nb3_8.atMove 2).Valid
  vb3_8_3 : (nb3_8.atMove 3).Valid
  vb3_8_4 : (nb3_8.atMove 4).Valid
  vb3_8_5 : (nb3_8.atMove 5).Valid
  vb3_8_6 : (nb3_8.atMove 6).Valid
  vb3_8_7 : (nb3_8.atMove 7).Valid
  vb3_8_8 : (nb3_8.atMove 8).Valid
  vb3_8_9 : (nb3_8.atMove 9).Valid
  vb3_8_10 : (nb3_8.atMove 10).Valid
  vb3_8_11 : (nb3_8.atMove 11).Valid
  vb3_8_12 : (nb3_8.atMove 12).Valid
  vb3_8_13 : (nb3_8.atMove 13).Valid
  vb3_8_14 : (nb3_8.atMove 14).Valid
  vb3_8_15 : (nb3_8.atMove 15).Valid
  vb3_9_0 : (nb3_9.atMove 0).Valid
  vb3_9_1 : (nb3_9.atMove 1).Valid
  vb3_9_2 : (nb3_9.atMove 2).Valid
  vb3_9_3 : (nb3_9.atMove 3).Valid
  vb3_9_4 : (nb3_9.atMove 4).Valid
  vb3_9_5 : (nb3_9.atMove 5).Valid
  vb3_9_6 : (nb3_9.atMove 6).Valid
  vb3_9_7 : (nb3_9.atMove 7).Valid
  vb3_9_8 : (nb3_9.atMove 8).Valid
  vb3_9_9 : (nb3_9.atMove 9).Valid
  vb3_9_10 : (nb3_9.atMove 10).Valid
  vb3_9_11 : (nb3_9.atMove 11).Valid
  vb3_9_12 : (nb3_9.atMove 12).Valid
  vb3_9_13 : (nb3_9.atMove 13).Valid
  vb3_9_14 : (nb3_9.atMove 14).Valid
  vb3_9_15 : (nb3_9.atMove 15).Valid
  vb3_10_0 : (nb3_10.atMove 0).Valid
  vb3_10_1 : (nb3_10.atMove 1).Valid
  vb3_10_2 : (nb3_10.atMove 2).Valid
  vb3_10_3 : (nb3_10.atMove 3).Valid
  vb3_10_4 : (nb3_10.atMove 4).Valid
  vb3_10_5 : (nb3_10.atMove 5).Valid
  vb3_10_6 : (nb3_10.atMove 6).Valid
  vb3_10_7 : (nb3_10.atMove 7).Valid
  vb3_10_8 : (nb3_10.atMove 8).Valid
  vb3_10_9 : (nb3_10.atMove 9).Valid
  vb3_10_10 : (nb3_10.atMove 10).Valid
  vb3_10_11 : (nb3_10.atMove 11).Valid
  vb3_10_12 : (nb3_10.atMove 12).Valid
  vb3_10_13 : (nb3_10.atMove 13).Valid
  vb3_10_14 : (nb3_10.atMove 14).Valid
  vb3_10_15_0 : (nb3_10_15.atMove 0).Valid
  vb3_10_15_1 : (nb3_10_15.atMove 1).Valid
  vb3_10_15_2 : (nb3_10_15.atMove 2).Valid
  vb3_10_15_3 : (nb3_10_15.atMove 3).Valid
  vb3_10_15_4 : (nb3_10_15.atMove 4).Valid
  vb3_10_15_5 : (nb3_10_15.atMove 5).Valid
  vb3_10_15_6 : (nb3_10_15.atMove 6).Valid
  vb3_10_15_7 : (nb3_10_15.atMove 7).Valid
  vb3_10_15_8 : (nb3_10_15.atMove 8).Valid
  vb3_10_15_9 : (nb3_10_15.atMove 9).Valid
  vb3_10_15_10 : (nb3_10_15.atMove 10).Valid
  vb3_10_15_11 : (nb3_10_15.atMove 11).Valid
  vb3_10_15_12 : (nb3_10_15.atMove 12).Valid
  vb3_10_15_13 : (nb3_10_15.atMove 13).Valid
  vb3_10_15_14 : (nb3_10_15.atMove 14).Valid
  vb3_10_15_15 : (nb3_10_15.atMove 15).Valid
  vb3_11_0 : (nb3_11.atMove 0).Valid
  vb3_11_1 : (nb3_11.atMove 1).Valid
  vb3_11_2 : (nb3_11.atMove 2).Valid
  vb3_11_3 : (nb3_11.atMove 3).Valid
  vb3_11_4 : (nb3_11.atMove 4).Valid
  vb3_11_5 : (nb3_11.atMove 5).Valid
  vb3_11_6 : (nb3_11.atMove 6).Valid
  vb3_11_7 : (nb3_11.atMove 7).Valid
  vb3_11_8 : (nb3_11.atMove 8).Valid
  vb3_11_9 : (nb3_11.atMove 9).Valid
  vb3_11_10 : (nb3_11.atMove 10).Valid
  vb3_11_11 : (nb3_11.atMove 11).Valid
  vb3_11_12 : (nb3_11.atMove 12).Valid
  vb3_11_13 : (nb3_11.atMove 13).Valid
  vb3_11_14 : (nb3_11.atMove 14).Valid
  vb3_11_15 : (nb3_11.atMove 15).Valid
  tv_b7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem checkedBranches1 : BranchChecks1 := by
  constructor
  · refine guidedTree_sound (holesLeft := 5) (a := [0x11baf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 5) (a := [0x11baf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 5) (a := [0x11baf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 5) (a := [0x133cf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 5) (a := [0x1286f]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 5) (a := [0x120ff]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 4 [0x123] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11, 0x2108404210860] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x123] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11, 0x2108404210860] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1157f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x19c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x154b3b33503030301593434382323230, 0x2101404220860, 0x10c3c3c37b3773735522201463146377, 0x10122ff43dbf37737355222074437443, 0x184c33637f373932762074437443122f, 0x1f3287ff377be0cbfbe0043043d4c3,
      0x1350303030740740122f84122f8458cf, 0x1137737355222014631463140f54d5b3, 0x2021204220860, 0x1f4008e5731c23920744374430c3c3c3, 0x13637f373932762074437443122f0122f, 0x16600e5e70be0be004304366c366c3,
      0x175b3940333030740740122f0f4f122f, 0x1c3c3c3cb3737735522208463d363f354, 0x100000f40046bf3773735522200430430, 0x100043043d4c384c33637f3739327620, 0x1330000008408446cff3167ff37700cbf, 0x1552220146614a40faf75d5751332aef,
      0x2101084220860, 0x1008e501c55395500000c30001377373, 0x501204220860, 0x103637f373932020740740122f0122ff4, 0x10f4f122f6600e50000250000066066, 0x122207754b3b3350303030740740122f,
      0x1552220d4c3c3c3744374437b37737355, 0x12e320122fd4122ff4744374430377373, 0x1e30cbfe300c30c304384433637f37393, 0x1631463122f0122f0748474840f30f377, 0x17373552220140f54d5b335030303014, 0x108e5731c23920e6c3c3c374437443137,
      0x2014082108021, 0x12e320122f0f4f122ff474437443181f, 0x1258fe300c30c3664366433637f37393, 0x1122f0122f0740746600e5fe5e7182fe3, 0x1440cbf67565678333333003014631463, 0x12220f35475b394030e3fbee3e3954495,
      0x12e320d3d4c3c3c3043d443037377355, 0x1d63303300c30c304384433637f37393, 0x17373552220630be00c40d4077673656, 0x1f37700cbf006395f4959500002aff37, 0x13333330095be956908408433dff3288f, 0x1076e3e3e3954495440cbf67565678,
      0x158df1304f1259f207f2d1f1aaf2d1f, 0x2014082108021, 0x2014082108021, 0x144ee676756783333330101037ef037ef, 0x2014202108021, 0x2014202108021,
      0x1550a40faf75d575176e3e3e30440cef, 0x10004400110080022000804020101002040080da2, 0x1f47407415bf181f08e51eaf1c5539, 0x1070e622ef36a63610000122f0f4f122f, 0x441404220860, 0x10122f0740746600e5004c02501e0000,
      0x1014c344444400001377373552220122f, 0x481404220860, 0x1141e4406446606603637f37393202] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1115cf125f1dd1dd00e4f380d5f380, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x15d289f169f210f01126f1126f1d2f, 0x2101084210860,
      0x2101084210860, 0x10102f0109f2b0f0d6f2b0f119cf1126f, 0x2024084210860, 0x2024084210860, 0x1221f1d3f0220f169f37ff169f0102f, 0x10102f0102f0305f0d6f1ebf0d6f240f,
      0x10f0f2b0f109f19cf1126f1289f1210f, 0x2024084210860, 0x2024084210860, 0x2024084210860, 0x101ecf00306f147f25af00000002b0f, 0x13dcf0f8da102f0102f0270f046df161f,
      0x111d2f183f0e6f242f211f241f14cf, 0x2102084210860, 0x146ff242f380f33ef46ef0128af1edf, 0x2101084210860, 0x100102f0102f033ef016ef013ddf12ef, 0x2024084210860,
      0x116ef240f1daf12ef12ef28bf0212f, 0x1380f1a4f1bbf0102f0102f00270f16ef, 0x100000000f0f028af3ddf1d4f241f1a4f, 0x101ecf12ef1d4f306f147f25af1a4f, 0x17373552220102f0102f00016ef161f, 0x15656783333330c3444444148f0eef,
      0x1567833333309544954476060606011df, 0x109330954495441e0606061dff11dfa6, 0x1090044044006c4060faf2b1f1a56b933, 0x19509501e0d407014dfa61a148f7a213f, 0x10ac440944307f16d730f7f20ecf2047, 0x2101104230860,
      0x1004404476060606011df05678333333, 0x11c6f3300000006006002e560b330933, 0x100090044044006c4060faf2b1f056033, 0x111eef0e304700000070058ef02e1a0b, 0x2021204210860, 0x1133ff169f0010270f11ebf1e0f11eef,
      0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2024204210860, 0x1045454513df11dfa65678333333025af, 0x10010306f115cf5d1dd1dd01ee3e3e3,
      0x2021204210860, 0x2021204210860, 0x2021204210860, 0x2021204210860, 0x116ff1fcf14b14b0d5c71d2f1220f125f, 0x2024204210860,
      0x2021204210860, 0x2021204210860, 0x1470f1abf018dfba12bfba0010148f1, 0x2021204210860, 0x2021204210860, 0x101003def0471f1305f167f2d2f241f,
      0x2021204210860, 0x2024204210860, 0x1460464646148f0eef737355222000faf, 0x10469946270f1e7732529920d3c34646, 0x2041204230860, 0x1079ccc40d4000a61a000137f0046046,
      0x14444440706060600eef737355222079, 0x11e44064400600600e773252092014c3, 0x110119df270f11ebf1e0f1011abf0014, 0x2080a0a122121, 0x2080a0a122121, 0x2082208122121,
      0x2082208122121, 0x2082208122121, 0x10243f1e0f0001abf0176f0011ef1d5f, 0x128bf07dd5d5177f0011ef0000058ff, 0x1141f244f1daf12ef472f28bf0212f, 0x10018efa40473f114f590f141f0141f,
      0x101e00f4f070f4fe605ea6a6110f00f8f, 0x1d8999a9a0340ffcfc14ff05757018ef0, 0x1123f0909909a00000005701446090909, 0x119ef2e560b33591f33096e3014147f09, 0x1475f4b0fac7960e30e3045592f45474f, 0x10ba0ba0022ff0593f11eff1fcf1e1f4b,
      0x2021204210860, 0x10476f0307f1230f109f308fdd594fdd0, 0x2021204210860, 0x10464646080eef08735522200125f010, 0x2024204210860, 0x1002b0148f08e55d1c5539550c3464646,
      0x1307f16d730f7f20ecf20245ff4245fd4, 0x2041204230860, 0x1e5109f2d2f5b595f250046046046eb46, 0x1080eef0873552220000009d2b9d596f1, 0x10004402000840021000804020100802020080da2, 0x1cc008e501c5539550c34444440060606,
      0x144006006000730202095f495950cc2b, 0x10951b95e9002b000e50000250ac4409, 0x1270f381f129f309f231f01f0f477f096, 0x119df025af1c7f3e0f3dff10222f597f, 0x2012208122121, 0x1000f4f00f4fe613df5ea6a6110f00f8f,
      0x1183f0e6f242f211f014cf3dcf01e0, 0x10d5fa1d2f1a4f28bf242f101edf1306f, 0x10000c0004802000d000300840041040041008123, 0x2012208122121, 0x11fdf148f106f2a1fdf12ff0105f19df, 0x101d6f598f018df28cf19ef28cf101fef,
      0x20422081221a1, 0x1101eaf33ef471f28df1acf309f1d6f, 0x2022208122161, 0x1148f08e55d1c03910af0028ef025bf, 0x100d7f10af018efc39de69d66066138f, 0x100f4f00f4f138f270f106f1adf5d0d7f,
      0x109660660008e501c03910af018ef000, 0x10001adf00d7f00d7f10af014c3090c4f, 0x1141e09246f09000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1333333014333433637f373932c320230, 0x2101084220860, 0x17833333300440440c4c4c4067675678, 0x13656d633763300000007002b2f67a656, 0x136a63617617600440440c4e6c47767, 0x300a02108021,
      0x300a02108021, 0x10303075596834b62300000e60e322ef, 0x173735522203c63696314ef5454b33503, 0x13637f3739320200430430c3c3c37b37, 0x13637f373932762004304328ff025cff4, 0x177f3599ff314ef0000043043d4c384c3,
      0x108e5731c239200000271f8425cf84, 0x111dfa65678333333074437443182f, 0x1110f00f8f150954495440c4c4c4181f, 0x133095449544178f0178f07181f5ea6a6, 0x10004404479c479c4141f6c2e560b33c8, 0x10f4f178f79272f0e5fa62e182f0258f,
      0x1d363f35475b39403f4030950950178f, 0x100430430c3c3c3cb3737735522208463, 0x193276200000e6f4003637f373932452, 0x1f34ebe1be0043043d4c384c33637f373, 0x300a02108021, 0x1f411e5115a125000004e8408477f36e,
      0x2101084220860, 0x2101084220860, 0x2101084220860, 0x2101084220860, 0x2101084220860, 0x1100000c415bf0011a61a10100746674,
      0x4080022000820020800804020102002080080da2, 0x501204220860, 0x501204220860, 0x501204220860, 0x100a04000020200808020010800420204008041a3, 0x1950178f0178f07181f5ea61110f00f8f,
      0x100204008020200808020010800420204008041a3, 0x14c10b00000795a790112e1a0b0000950, 0x501204220860, 0x501204220860, 0x10000c000220400810020010800420404010081a3, 0x103030950950178f0f4f178f7911a611,
      0x100014000420400810020010800420404010083a3, 0x100404010020400810020010800420404010081a3, 0x1001040040204008100200108004204040100a1a3, 0x10004400102040081002001080042040401008ba3, 0x100007e8b8b3a4b45454505454b33503, 0x1437b3773735522200e3f0e7f0e7f14ef,
      0x1433637f3739320720d4c3c3c304310bf, 0x14384433637f37393207200d40f4043e9, 0x1000084e98477f30f30e307e300c30c30, 0x1696900002b2f67152f56783333330630, 0x100003e1f7730af77478fd60d60636907, 0x12220140f54d5b335030303069cc693c,
      0x1e5731c23920000074437443137737355, 0x1080042000804400100804020102002080080da2, 0x1433637f3739320720000074437443008, 0x166740258f0e5e70e30e30e60c300430, 0x17443744300001377373552220000f474, 0x1021404220860,
      0x10207443744300002d3f08e5731c23920, 0x1e5e7101007643c34300003637f373932, 0x8000a00024080102008001200048000c000201a3, 0x421404220860, 0x13656d633c4330030747974f40660011, 0x421404220860,
      0x421404220860, 0x1220f35475b394030be0e3044d4447767, 0x120720d3d4c3c3c3043d4430373773552, 0x1d63303300c30c304384433637f37393, 0x1f373932020630be00c40d4077673656, 0x10e7ff34a00006369f4693c070003637,
      0x1d633c4330069be6930bf078408477f3, 0x12d4f2d1f0760e3004404477673656, 0x1101247f059af0025df304f1259f12d1f, 0x304042108021, 0x304082108021, 0x304202108021,
      0x304202108021, 0x11760e304a44e64477673656d633c4330, 0x880022000880402000804020102002080080da2, 0x100e600722ef36a636100000faf75d575, 0x821404220860, 0x1a40000740740008e501c553955095095,
      0x1783333330000f4746674001e50101250, 0x3db307983cc003db30798000001e600798003cc1f53000f303cc1e60f33cc01e7e60079bcc01e6303e4, 0x80404000000810000800040000008100008040402020001000000100008200000020004040200004100000020000800040002004000020004000080020000040040000100018fbc26, 0x404000200c10000800040000010100008000000820180004000100020200000020001040000008100c00040000800040002001000004008000040040000100040000100018a5726, 0x111c55395509544954400000cbf675656, 0x421404220860,
      0x156d6330330740c4f740900002d3f08e5, 0x111e511ad12507644c444ba0e60776736, 0x8000a00028080202008001200048000c000201a3, 0x421404220860, 0x421404220860, 0x421404220860,
      0x421404220860, 0x1747974f40660c4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1248f214f0faf10cf110cf11a5f110270, 0x2100884210860, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x130af30cf167f479f25df2aff01341f,
      0x2101084210860, 0x1012b3f232f0000000001059bf011bcf, 0x504084210860, 0x504084210860, 0x104000000810000004040000004100008000400020081004000104000200000020001040000008100400040000800040002000400010200800040800000100010000100018b5726, 0x13e2f159cf47af273f0000000248f233f,
      0x504084210860, 0x110faf100000000274f0000faf1bcf1, 0x504084210860, 0x8000400020081000000084000000410000001040002008100400040400020000002000084000000810040004000040004000200008001020080004080000010001000010001895726, 0x77536165ee6b2f73597ba8c4242e5001dd4d85940077536165ee6b2f73594000f047fe5eea310927848ebf047fe5ee6b28001dcd65ee6b639acbdd4d8594001deb396123bae6b36e6b28ee6b2f735a2e6b2bb9acdb9acaef59cb091d9bd664ca000ee6b36e6b28ee6bb5de10808, 0x1e515df1f41250000012b4f0033ef0faf,
      0x404000200810000800040000010100008000400020081004000104000200000020001040000008100400040000800040002000400010200800040800000100010000100018b5726, 0x2101044210860, 0x2101044210860, 0x119169f137f02b452d5f45167f15df, 0x10f8f2d5f00000d405b0115dfa61a125f, 0x504044210860,
      0x10950950245f00e616af5ea60110f2d5f, 0x100000c4000125f15df2e1a881988137f, 0x111ff110950950245f000700a60079088, 0x2100884210860, 0x2101084210860, 0x11aef1aef011bcf382f1d7f5dfd1fd1,
      0x2101084210860, 0x2101084210860, 0x2101084210860, 0x10000102d2f0119cf221f234f109f59df, 0x504084210860, 0x504084210860,
      0x110000001382f0fbf011d3f11ef00000, 0x404000000410000002040000004100008040402020001000000100008200000020004040200004100000020000800040002080400020000800080800000040008000100018fbc26, 0x4004000004010000020040000040100008040402020001000000100008200000020004040200004100000020000800040002080400020000800080800000040008000100018fbc26, 0x3040c4318860, 0x1000000f0f0005d19cf1342f159ef25ef, 0x504084210860,
      0x504084210860, 0x1ce1115f000001161f00383f5d15d1001, 0x3d77a050000f5de8140003d77a050000430e234000059682fee9d7a0f5b94d4704862f41b92800ee6b2bb9aca3c8967729a8dcd6c75367ae534fe44b3b94daf3597b9acaee6b28ee6b36e6b2f82431729b5e6b287735cf9aca3b9ad8ea6cf5ca6aae6b36e6b28ee6b3ecf58be8, 0x80004000201e100000008400000041000000104000201e100f000400004200000020000840000008100f00040000400040002000080010201e0004080000010001000010001895726, 0x204000000810000002040000002100000800000048000000440000002040000002000800005ce800004080000020100000020080400000801000f04000000404000003000195727, 0x80404000000810000800040000008100008040402020001000000100008200000020004040200004100000020000800040002080400020000800080800000040008000100018fbc26,
      0x2101084210860, 0x111ef126f011bdf11bdf235fba1ba1, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860,
      0x100000f9011ef010fcf10f5f0d8f0c7f, 0x504084210860, 0x504084210860, 0x13c03c00f90f9240f0184f00125f0125f, 0x1000eb0000d8f0fcf10f5f10c7f1126f0, 0x504084210860,
      0x504084210860, 0x504084210860, 0x10da3c03c000010df000000d3f0000, 0x101179f195f384f125fba1ba1ce1115f, 0x2101084210860, 0x2101084210860,
      0x2101084210860, 0x2101084210860, 0x101010fcf12bf0f5f0d8f0c7f11ef1fcf, 0x504084210860, 0x10080022004004100100804020100802020080da2, 0x1000f9195ff901184f169f000000000f9,
      0x104000000810000004040000004100008000000820180004000100020200000020001040000008100c00040000800040002000400004200c00040800000100010000100018a5726, 0x10000d8f0fcf10f5f10c7f215f1fcf000, 0x504084210860, 0x504084210860, 0x100275f125f1125f100169f00000eb, 0x806040002000100000018400000041000080480020000c0001000200010200000020004040300002100000020000c0004000208050002000020008080000004000a000100018f9c26,
      0x806040002000100000018400000061000080480020000c0001000300010200000020004040300002100000020000c00040003080500020000a0008080000004000a000100018f9c26, 0x110cf110cf11a5f3e3f1aef00000110df, 0x404000200c10000800040000010100008000000820180004000100020200000020001040000008100c00040000800040002000400004200c00040800000100010000100018a5726, 0x2101084210860, 0x2101084210860, 0x1167f343f25df1012d6f30df216f109f,
      0x2101084210860, 0x3040c4318860, 0x1000000001aef05a0f011bcf59ff241f, 0x504084210860, 0x1207f0000001aef01002d7f207f47bf, 0x40040000100100000080400000201000080484024000c0001000300010201200060004040300002100c00020000c00040003080500020000a0008080500004000a000100018f9c26,
      0x1000274f0000faf1bcf12b5f1343f47cf, 0x504084210860, 0x504084210860, 0x100002b4f001aef0faf10faf1012d8f00, 0xc000000090000000240000000300000800000408000004040000020040000020000080004ca080004480000020140000020080400000801006004000024004000090004985727, 0x806040002000100000018400000041000080484024000c0001000200010200000060004040300002100000020000c0004000208050002000020008080000004000a000100018f9c26,
      0x806040002000100000018400000061000080484024000c0001000300010200000060004040300002100000020000c00040003080500020000a0008080000004000a000100018f9c26, 0x12220d34409440faf0fcfd5c71c31e300, 0x2101104210860, 0x2101104210860, 0x101c55395500000044444410eef737355, 0x504104250860,
      0x1732520207407402b9a123f9a16af08e5, 0x10e5007902500000c344044109f2b6fe7, 0x1fac796c396e30477407402b0e6f40, 0x1080eef08735522202b44142f445d0fcf, 0x1142f9a008e501c553955000000444444, 0x1044109f2b6f139f735c202000002b9a,
      0x102bf40025df1e0fe501002500000c344, 0x80004000201e100000008400000041000000100040201e0040000400200200000200000840000008100f00040000400040002000080010201e0004080000010001000010001895726, 0x128ef10cf110cf11a5f11f1f0e3047000, 0x501204210860, 0x501204210860, 0x501204210860,
      0x119cfa61a10747df190010169f1000, 0x501204210860, 0x504204210860, 0x301a04318860, 0x1fd1fd111ff1196f00e30e3d4000236f, 0x501204210860,
      0x501204210860, 0x501204210860, 0x10fcf1ce1115f0d5c7010125f100028af, 0x501204210860, 0x504204210860, 0x501204210860,
      0x501204210860, 0x1110cf11a5f1100ba0ba1000235f0fcf1, 0x501204210860, 0x501204210860, 0x500a04210860, 0x501204210860,
      0x501204210860, 0x501204210860, 0x1737355222033ef0faf0110000faf10cf, 0x501204210860, 0x504204210860, 0x1000a61a000137f00000000028ef0eef,
      0x10028af2b6fe773252020950959ad40c4, 0x1ca46011df5656783333330d3c3000d40, 0x107eb008e501c553955095449544c846, 0x1046046000560330330740c4f74092beb, 0x17974f42b007000e500002507644c444, 0x101011fff28affd1fd111ff130ef0074,
      0x2080a0a122121, 0x2080a0a122121, 0x209120c122521, 0x2082208122121, 0x2082208122121, 0x1fd195ffd011ff030ef0176f000d8f,
      0x1110cf11a5f100177f000d8f000003e4f, 0x2080a0a122121, 0x2080a0a122121, 0x209120c122521, 0x111a4f07dd5000010310f30ff0faf10cf, 0x2082208122121,
      0x2020a0a122161, 0x10141f5a1f309f290f12ef290f1161f, 0x2020a0a122161, 0x1a60110f00f8f0018efa400114f0141f, 0x10009e018ef001e00f4f070f4fe605e, 0x1014c4090c4f09e60142f000a61e2f,
      0x1e30140d3f09311f090000000000019ff, 0x117af0000faf19cf2e1a0b073e5f19096, 0x10fcf10fcf1ce1115f0fac7960e35be3, 0x501204210860, 0x501204210860, 0x501204210860,
      0x11fd111ff1196f0385fba1ba1000385f, 0x501204210860, 0x104000000810000004040000004100008000080020180400000102000200002000001040000008100c00040000800040002000400004200c00040800000100010000100018a5726, 0x501204210860, 0x501204210860, 0x501204210860,
      0x10eef0873552220383f125f0110005dfd, 0x501204210860, 0x504204210860, 0x10309f08e510cf1c55395500000000008, 0x117af0001e0f2b6f6d731212000002b00, 0x1e6f3001e9cc00f3f306bbe6607981e6007a73003d977903cc3cc1e60f3e79c7980f31e61e601e631344,
      0x901204230860, 0x1f40d42b000167f9ce59c1c41250c3000, 0x501204210860, 0x501204210860, 0x110bf44c846046011df56567833333300, 0x1245f00005ea6a6110f00f8f001f2f44,
      0x14404604600056033033095142f950c4f, 0x195799507245f00000a600008807644c4, 0x12d9f167f13ef113ef1312f5a2f00960, 0x2010a0a122121, 0x201120c122521, 0x110cfa610cf1075a3f880000010386f,
      0x2012208122121, 0x100014020002400090022010800420400810083a3, 0x11a5f3e3f001e0000f4f00f4f10cf1aff, 0x110000001030df216f109f10cf110cf1, 0x2010a0a122121, 0x201120c122521,
      0x2012208122121, 0x2080a0a122121, 0x100d50000102d7f3e6f5dfd1fd111ff, 0x2080a0a122121, 0x209120c122521, 0x2082208122121,
      0x100000010345f344f5dfd1fd111ff5a4f, 0x2050a0a1221a1, 0x206120c1225e1, 0x20422081221a1, 0x100010313f478f167f13ef113ef1312f1, 0x2020a0a122161,
      0x2020a0a122161, 0x202120c122561, 0x2022208122161, 0x10e6066066cc167f9ce59c1c4111af00, 0x2080a0a122121, 0x2080a0a122121,
      0x1cc1fcf9c1adf9c0d7fc40d7f0018efc3, 0x1000e5000011af018ef00000f4f00f4f, 0x100d7f00d7f7c014c30912cf0966066, 0x1141e0947ef090000001adf] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 5) (a := [0x120ff]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1291f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1249f8b8b7e185f3a3a4b4545450030, 0x110ef0fcf1befd9d90caf19191900cbf, 0x10caf19191903c9a3c9a0e7f24af10ef, 0x13c9a0e7f24af12bf10ef14df1befd9d9, 0x10eb10efcc249f0cbfd96e190e1903c9a, 0x114df0cbf10cbf9d137f3e0e009a09a0,
      0x20240c6108421, 0x156783333330033c03c0276f012bf10df, 0x1130f87875be3e3e307716767970f9f56, 0x21020884208e0, 0x187875be3e3e30690669067b0dcdcba, 0x14be30690669067b314fbddc18df130f,
      0x197bb3e4b00060060046dcc8077874ee3, 0x106816869069013ff0bdca18df77177, 0x20240c6108421, 0x21080884108e0, 0x1343f0e1fbd111fa9119bdd0e0c7f0c7f, 0x21010884108e0,
      0x21010884108e0, 0x1010e1f111f111f05a5f3a3a4b4545450, 0x9040884408e0, 0x113e7f162f1ad7c16ff210f14b14b0000, 0x2014082110021, 0x2014082110021,
      0x2014082110021, 0x204428a1129e1, 0x10e1f010fd107f3a0d9f450450e90e90, 0x9040884408e0, 0x1ad343f5a6f126fd89d2d0d9f0000099, 0x148b3b3350303030e90e901f3f0162fce,
      0x1838315df257373552220f3a3a3a317bf, 0x18389830d257373552220744374433683, 0x1083c3837625f373842c6207443744336, 0x1089f40df31f317bfc6120fc60043043, 0x20240c6118421, 0x1a37e4875b3d30383030ed74074011cf,
      0x10433683838302525735522200cbfa389, 0x1c6200000368389830257373552220043, 0x10c60c60043043083c3837625f373842, 0x1885678333333000000f48900f31f3, 0x880022001004400101008040202002080081da2, 0x187875be3e3e30770e1f195f67880f9f,
      0x10cefe35a7fe300060067b0dcdc9c130f, 0x1e300060060012bfdc1e3f1a4f7787, 0x10cbf00060060046dcc8077874ee30cbf, 0x1277f012bfca1e3f770cbf770cef05a8f, 0x13a3a4b454545048b3b33503030300000, 0x12220f3a3a3a300000cbf18b8b7e185f,
      0x9020884408e0, 0x15522207443744336838383025737355, 0x173842e32074437443368389830257373, 0x10f31f30e30e307643c343083083025f3, 0x10004040110004400101008040204002100081da2, 0x13a4b45454501351350747974f400890,
      0x1e60f3079800f4e6003d398007b66001ed98003ccf3f3001e60f307983d398003ea60007987981e6aa964, 0x1e60f3079800f4e6003d398007b66001ed98003ccf3f3001e60f307983d398003ea60007987981e6aa964, 0x11c8f0cbfd9d9d90cbf08b8b7e185f3a, 0x1170f7e7c16ff186f278f12b7f103f096, 0x1e60f362b800097e0001e61e67980799e600f33cde705fc1e60f307983d3aafc7b660007983cc1e6aacc4, 0x13e8f0f3158ff30d00d0278f170f162f,
      0x1170f0170f5a9f1bbf11bbf2b5f0241f, 0x204128a1429e1, 0x16700f9f56567833333302b8f010279f, 0x20442081421a1, 0x10036561334533014c4060606770e3f67, 0x8880884508e0,
      0x1d433c4330030140d3f069a0600e3f067, 0x104875b3d303044e3440c60c60b93656, 0x120a3000077c6c6c67eb9565678333333, 0x10e00a3000036838983187f2573735522, 0x122200f40770cbfc689c6187ff31f34b0, 0x9010884408e0,
      0x13333010bf43e94336838383025257355, 0x19544954400f1f116f67088152f567833, 0x10e607643c343083083025f3738420720, 0x1247f0a409579950700116f0000000d, 0x10100012bf292f0f2f110f5f1eef0289f, 0x2011202140021,
      0x2014202140021, 0x2014202140021, 0x10c7f01e1901900116f000000070e602d, 0x133330a901000bd111fd8119bdd00c7f, 0x2011202140021, 0x2014202140021,
      0x2014202140021, 0x1ae07787878777067677e0f9f56567833, 0x11234f1278f001117f0faf117f150f111, 0x2020ac6140421, 0x1e60f65a18003ea60016c81e67980799e600f33cde7028b3e60079f983d42fe07b66000799e601e6ae984, 0x2020ac6140421,
      0x2021ac6140421, 0x1e60f5e098003ea6000f6cc0079bcc01e6f3003cde79a101e679807983d42fe07b66000799e601ea76cc4, 0x1e60f5e098003ea6000f6cc007a73001e7e6003cde7b8701e6f3007983d42fe07b66000799e601ee42cc4, 0x1770067880f9f88567833333302b7f, 0x1387f150f19df0217f47ff07700130f, 0x100e4500d00d05abf0162f5aaf7e0faf,
      0x10158fc307700cbf08967187ff31f34b, 0x2011202140021, 0x10000010116f670f2ff377f36606645, 0x100104024020100810020010800480102004021a3, 0x1010100111fcd1bbfcd9bdd00c7f0c7f, 0x100104004020100810020010800480102004021a3,
      0x20442081421a1, 0x114c3069a06008900f31f30c404501a6f, 0x5b5cc79f9f9801e7e6798007b66001ed98003ccf3f6cc1e60f307983d3f3203eaf7e07987981e6aa964, 0x1141e061c6f0600000f377f366c466450] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1c810eff19b4945115f4507373552220, 0x21010884108e0, 0x21010884108e0, 0x1115f133f3a3a4b4545450235fc8bd, 0x1ac16ff115f14b14b0000013e111f111f, 0x9010884408e0,
      0x2014082140021, 0x2014082140021, 0x199450450e90e90315f388f162f11e1f, 0x2014082140021, 0x11ce00000208f3ed813bfba133f107f3a, 0x2014082140021,
      0x10e905acf0162f208f235fba480fba10, 0x2014082140021, 0x119056567833333300876080eef25e9, 0x13e015ef00d81d8011ef0107fcb190daf, 0x20242084109e0, 0x11eef0c7f0c7f0c7f09711df11dfb9,
      0x1218f2baf223f223f1f1f02b9f2b9f, 0x1333333095449544188f224f188f481f, 0x17e5c11ef2a107fcb190daf190a65678, 0x195445e975e11df0b0015ef0106f0106f, 0x1bd171f291f4f87875be3e3e303309544, 0x109b4945115f450330dafca45450ba,
      0x10107f01901901a5600000c8bdc800eff, 0x10137f0137f07600000d8482fd8011ef, 0x10107f3a045045097c40000000003e03e, 0x1e3e3044316f133f316f134f993ed80ba, 0x1e9cae9e9274fbabd171f29087875be3, 0x1274fc8bdc8169f0317f9b490115f0044,
      0x1291f4f87875be3e3e300e9133fe93c, 0x187cbe345e302946454545bcbabc171f, 0x10a61ad40450457aba7a232f971f4f9b, 0x10195f11ef483f0d8f10d8f10c7f10c7f, 0x2014082108021, 0x2014082108021,
      0x2034086110421, 0x15c02a107fcb00daf005e070b00147f00, 0x105e15ef0eff0fdf0eff106fce106f7e, 0x1090909bcbabc171f29087875be3e3e3, 0x1099a097aba7a09709b870e30e309546, 0x19515ef] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x117cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x117cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1d9d90caf191919020aaaa0cff8585850, 0x1e3020e7f00daf0daf06b6b6b0f2f209f, 0x1757b029290868686d81b0f87875be3e3, 0x1eb110ef10ef03e9fd9d90caf1919190, 0x8282084409e0, 0x1137f1d8f1d8f0750e7f140f1bef1bef,
      0x114ef05c002aff0e7f10ef7e7b07b18ff, 0x1369393930838383187f177373552220, 0x1093093083c6830f2f17f373c32c62036, 0x12220000b29c407b00361bdf36000190, 0x12d620a83693939307838383017737355, 0x15be3e3e300930b93083083017f373c3,
      0x17833333307b002908686865a1b0f5a87, 0x1001b1d9f1b14ef7b07bba196e1905656, 0x18c08c10c7f00c7f06767e61fdf05c, 0x20422084209e0, 0x103a3a4b4545450000000e1f00e1f484f, 0x10c88c8880f9f7c9c7c185f9908b8bbb,
      0x100366e360e30e30b3b33503030300c0c, 0x18b7e03a3a4b45454500760b767b00e7f, 0x1009648d3a3a3a37c134f7c185fbb08b, 0x1760b76186186200f366e360caf0137f, 0x842000180021, 0x842000180021,
      0x1ea2cea2c96163f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1d90caf191919020157faa0cff8585850, 0x100daf0daf19ef019ef219f0f2f209fd9, 0x129bc0bc171fd81b0f87875be3e3e3021, 0x2014202108021, 0x124bf131f5adf1bff1bff075d5751029, 0x2014202108021,
      0x1220225f05c0106f0106f389f7e0faf2a, 0x1207d369393930800837187f177373552, 0x12207d0930935e05e370f2f17f373c320, 0x1d620a83693939308c408370177373552, 0x15be3e3e300930b930c4037017f373c32, 0x11d5f01515000029000171f5a1b0f5a87,
      0x1342f5aef190f1190f388f38af3eaf, 0x2021a06110421, 0x1ba216f6e980a63b3d00105b0f05aff, 0x1e60f362b800097e0001e622357e088b0000f31e7e705fc1e60f307983d3aafc7b660007983cc1e68c6c4, 0x11fdf05c0106f1b106f1b2bbf5d2a24bf, 0x1485fbb02a143f103f0f6f605e3ebfe6,
      0x188c8880f9f5e19c5c185f106fce106f, 0x1024204180421, 0x1a6360e30e30d5b335030303024cf0d0f, 0x12a143f103f0f6f600760b765e05e0036, 0x1134f5c185f106f47ff106f485f7e0, 0x102e56033033094a8947da47d540f1f,
      0x1ea2cea2c24cf791c9f79b9bc1bc116bf, 0x1084210182121, 0x1084210182121] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1187875be3e3e30f33434382323230850, 0x20412084109e0, 0x126620e8ede82d318f45450fdbd171fa9, 0x1191902703030016cf330003700f37366, 0x10e0e0012bf219f0f2f1d9d90caf19, 0x1e60f3079800f4e6003cc0f4e6003d398007a7300f3f3001e60f307983d398003ea60007987981ee24364,
      0x18b8b7e6e3a3a4b4545450030852d486f, 0x15656783333330039d185f0caf0caf00, 0x145d945068970f9f5b5b016767974e, 0x20422084209e0, 0x10680fddd0caf00e1f010fd107f3a0d9f, 0x8482084409e0,
      0x100000e1fbd111fa9109bdd0e0c7f0c7f, 0x20412084109e0, 0x155550a3a3a317bf84b3b3350303030d8, 0x10a389a37e8475b3d30383030ed17bf48, 0x10346f5b00000f37bf366066450048055, 0x1004855550a3a3a3084b3b33503030300,
      0x11dd0caf0140f0101107f3a0d9f45dd45, 0x4040000010001000020001000040010080002000200008000800010002000020000200400000200010002000010002000100800000102020000100020001004000001010a8f6526, 0x8482084409e0, 0x80402002100404010010400402080022000895a2, 0x1004878550a30a308475b3d303250300, 0x1aaa900000bd111fd8109bdd00c7f0c7f,
      0x1e60f3079800f4e6003cc0f4e6003d398007a7300f3f3001e60f307983d398003ea60007987981ee24364, 0x15b1f0e3f1bdf0137f0c7f137f0200d2f, 0x11d8f1d8f0caf020487f000001a7f0, 0x114ef0144f0010e7f10ef9d7b07b18ff, 0x20222084209e0, 0x124af08608601b0f7787144fe33ae3075,
      0x17e360360caf19137f137f07502938bf, 0x1173a735522200e7f0148f00867b86, 0x11d905505503693939308383832bcf, 0x20242084109e0, 0x1f373c32c6200360360020af0187f201f, 0x1f4488f000930930832bdf83347f17,
      0x1222014ef0000865b2f86187f008718ff, 0x1237f5503693939308383830173a7355, 0x12003615ef3608620af860ac1017df55, 0x1000000834000008050000010040000020800008002000080008000100020000200002004140002000100020041400020001008030001020ac000100020001020a00001010a8b6526, 0x1f40000930d1f93083083017f373c32d6, 0x10b3b3350303030029000000002daf00,
      0x101f5f00760e7f760e7f3603649e3f9e3, 0x1c679c6d4036560330330a3a3a3e61aff, 0x1232300c0cef480cef491edfb91edf079, 0x1008489841f30f34e336e33034343823, 0x20412084109e0, 0x1e60f37302020e8ede815bf116f0116f,
      0x1000c158f27158fa3bd1bd166159f6637, 0x8421081810a1, 0x8421081810a1, 0x1045048000a3a3a34536b3b335030303, 0x10687804800d3a32a3333675b34503203, 0x1cc0d9f0e1fd9017ef0107f3a045045,
      0x17bf300000a3eda315bf68489ffd489f, 0x10303030238f1238f1b660cef668be6f3, 0x8421081810a1, 0x100fef480fef76d4a3a3a3134f0b3b335, 0x10f4f0e1f0f4f15a012af210f078078, 0x8442081821a1,
      0x1a3b9075b300300300fef112f0fef1c0f, 0x1288f126f000000fef480fef76d3a325, 0x10feffd0fef0dbf0f4f460f4fcd5a1c7f, 0x100f310cff3033033034343823232302c, 0x1a9087875be3e3e309584958477089, 0x1137f00e8ede8e9318fe9e99dfdbd171f,
      0x1e61e0fcf116fdc200f36120f360caf0, 0x136b3b335030303002c14271414690769, 0x103a3a4b45454507448747433a3a3a30, 0x103675b300320303c185f3c3c008b8b7e, 0x1679705656783333330d3482190a30a3, 0x1dd00c7f0068107f68690f9f69690067,
      0x148afe91f2f9d0e1fbd111fa902b0f9b, 0x17474c6a3a3a317bf0b3b3350303030e9, 0x1836b0da389a37e075b30030030ed7448, 0x1116f8b200f0120f3a1eef0247f00d348, 0x114481474690769e61e144f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1a9187875be3e3e30f334343823232300, 0x2011202110021, 0x10f30840840f85929454545bc0bc171f, 0x1e3e3e30b6030303f80e378e3008900f3, 0x112bfcc124df10f5f9c0ef90e087875b, 0x2011202110021,
      0x2011202110021, 0x105b3f0f5f9c0f900bc171fa910100cc, 0x2014202140021, 0x2014202140021, 0x11904545bc101137f48bfcc12bfcc226f, 0x1014202180021,
      0x1014202180021, 0x10e0e0012bf219f2d2b5fd9d90caf1919, 0x187875be3e3e302303230290daf10df, 0x1220f3683429454545bc0bc171fd815df, 0x10303059933333330800837a917373552, 0x2011202110021,
      0x1840840a82227d07d5417bf5ed5b33503, 0x175d5755ba4190800e30e300000f30f30, 0x1d5b335030303003a805507d07d3717bf, 0x10075d5750a4093003a82227d07d5405b, 0x14945f94507373552220a83355337d07d, 0x10f900080eefd410100c8bdc810eff19b,
      0x2011202110021, 0x2011202110021, 0x2014202140021, 0x2014202140021, 0x1081010caf226fc8bdc813ef05b4f9b49, 0x1014202180021,
      0x1014202180021, 0x100000c8bdc800eff09b4945f94507878, 0x1fcfc14ff225f5757000d2f157f0d2f25, 0x109e130fae0fff0fffbc0bc340f9e13bf, 0x19c48cf13bf1a8f190f5b5f225ff657, 0x105e340fe69ca61e2f19ff00004605b6f,
      0x1170ffdcc243fcc9c13bf48df00000, 0x125ff0fcfc14ff0575705e1140f215f, 0x1024204180421, 0x10057088130f163f319f319fbc0bc340f, 0x1260f202f0461c0f0dbf9c0dbf01a8f00, 0x11f31f34e336e3303434382323230885c,
      0x2011202110021, 0x2011202110021, 0x1f34e06e00f85915bf7700cbf00848984, 0x15454f81dc1dc10cf84898410cff3167f, 0x1004200180021, 0x1004200180021,
      0x17d54f636d5b335030303023024cfb654, 0x155131f75d5755b20caf2023a80007d0, 0x10cbff348ef3313306834a80007da47d, 0x1001040040088002010100c040201802040081da2, 0x16ef3000007d59a90000084162f8477f3, 0x136cb0db007d1a9aca94e84162f844ef3,
      0x1084210182121, 0x13503030304d9717df9713ffd41d40360, 0x8442081821a1, 0x13600000a89779977de67d540f1f0d5b3, 0x1000d1f970edf97cad4b7d4db360e3f, 0x1a89779977da47d935c75d5752900daf,
      0x100f31f30330330343438232323024cf, 0x820020810008400101008040200802020081da2, 0x1171fa9087875be3e3e307784d6840089, 0x1036560330330f85929090909bc226fbc, 0x1b6636363f8c406d40614dfbebd6716bf, 0x143437d07d54036d5b3350303030230ea,
      0x1a4151f557d07d0075d5750202023a843, 0x108408400000f30cbff303313306834a8, 0x1e9cc00f4e6001e9cc7980131a600f3798007987983cc79bcc007983cc1e601e63cc1e61e601e6c82a4, 0x1934444440813ef0837a907373552220, 0x143437d5e7d5417bf0d5b335030303059, 0x10621afbe162f670036560330330a843,
      0x17dba7d3717bf75d5755b01900c406d4, 0x1eaa8634363a8a419ef08] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1149f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x115ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1898304250473162b52053b8650305030, 0x144a9c6c6c6b4b9b4567833333307983, 0x10116f67b488b4b4180d7150954495, 0x1c6fbb9fb56d43329330954495440fef, 0x107b479b4fb180d7130f00440440c6c4, 0x14813b3350303030539509500fef0116f,
      0x197838383025737355222079a3a3a313, 0x183898304250473162b52074437443, 0x183c383025e773842c620744374430fef, 0x1089f4047904e716c6b5c600430430, 0x1a3264826b3d30383030ed7407400fef, 0x1430439783838302525735522207aa389,
      0x12c6200000083898304250473162b5200, 0x1c6b5c60043043083c383025132f7384, 0x1b4181a5fd73d000000f489004004e716, 0x10d4f08d0fff01e239f116f10efb488b4, 0x18d8d0690690970bd10ef5830ef581a8f, 0x10690690238f0bdbd58cd58580d4f348f,
      0x100000004610ef100f0100f05a05a0fff, 0x1690238f0bdca587a58100f0d4fac8d5a, 0x18de30a3a3a3134813b3350303030690, 0x122200000124f86bd86582958870d4fe3, 0x12b520744374430838383169f25737355, 0x1842e3207443744308389830425047316,
      0x1e716e3b5e307643c343083083025e773, 0x1153f135f0e4280747974f40089004004, 0x100195f0104f117f104f104f1a0f144f, 0x108d57013961313a5147f293f213f293f, 0x1ce8b8b8b124f0bddc58130f58fc0d4f, 0x10162fdc100f0100f00cef00570158f,
      0x10bdbd58cd58580d4f08d8d000000edf, 0x1b43b3d349f151500fef00fefa9124f, 0x10ddf15014c4060606006767b40f9f, 0x1140d3f069a060006700048ff0dff349f, 0x1448d440c60c6fbb9fb56d433c4330030, 0x104250473162b520a3264826b3d3038d,
      0x1c6042904e7160b500a300007a838983, 0x1838334af2525735522200f4007ac689, 0x1b488b4b4181f6fd715010bf43e943083, 0x102507384207209544954400f1f116f67, 0x10b40b4fb180dd7e607643c343083083, 0x1b4fb1807d7e60e4a409579950700116f,
      0x101326a51e2bbf13df2bbf00116f0b40, 0x1cd30ef7a0116f10efb488b4b4180d73d, 0x17a0896704130f040e0f160b5f60131e0, 0x1670c9f00c9f066066f60158fc3014af0, 0x158cd58580d4f08d0d4f00000ac0116f, 0x116c4b5f600fef00fefa9124f0bd38cf,
      0x1c466f6014c3069a0600890040040e0f, 0x1141e061c6f0600000c9f00c9f172f66] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x117cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x117cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c7f0c7f0c7f020c5aa0cff8585850, 0x10f3f0f3f0f3f1c1f23af129f2b9f1eef, 0x10e6f17efdd0e0e0e02490f1191f1f1f0, 0x2024204210860, 0x1d5c7227f1154f196f0ececec244f1f7f, 0x2024204210860,
      0x1d60bd60c6c6c613dfe6a656783333330, 0x1148f141f12ef38df28bf1212f131f07a, 0x2020a04210860, 0x1735522203ecf2dcf31af2dbf0027af0, 0x14b45454507a939393083838313df1773, 0x1109f5c115f0f7f7f7244f0d9f2a3a,
      0x1093083c6831c1f17e773c32c62015ef, 0x1552220000b29c400000a61a000190093, 0x1c32d620a80939393078383830177373, 0x15b0ecf5b00930b93083083017e773, 0x100dcf196f002bdf0148f5a6a2b0f0f7f, 0x10e30e3013b33503030300c0c0cc5124f,
      0x109648d3a3a3a3130760b76000000a61a, 0x1ea2c96163f760b7618618610a61a0000, 0xc41048180421, 0x842008180021, 0x842008180021, 0x1ea2c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1153f9e00a0a0dffbb0ddff600c5f8e0, 0x11dbf0195f0104f0104f172f1a0f0fbf, 0x14a21afce162f8b0a00dbf148f0dbf, 0x100172f0172f0f1f27bf11e4f104a1e1f, 0x1088208142121, 0x1088208142121,
      0x10e4f50c5c5118f0edf3edf0edf196f00, 0x13eef0fbf1d4f2bef0eff164f491f9e, 0x11501326a500c6f3eff0c6f0161f01a7f, 0x10137ad60bd65e05e67b4e6b4b4180d7, 0x17d7a93939308008370417041d160b5f5, 0x10930935e05e370c9f170c9f0c300f50,
      0x1939308c408370417041d168cb5f507d, 0x10370c9f170c9f104fc38cd6f50a8093, 0x1bc585a58580d4f08d0d4f00930b930c4, 0x124024cf0d0fc5124f00dcf196fbc0bc, 0x105e0b40b4fb180fbfd75701313a5bbe4, 0x16c0000094a8947da47d54130760b765e,
      0x12cea2c24cf791c9f79b9bc1bc1fb0fb, 0x1084208182121, 0x1084208182121, 0x1ea] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x158870d4fe38de305334652305230850, 0x10e8ede8530ddf290ddf45086bd8658a9, 0x1e4038d08d0000370c9f00c9f066066f5, 0x1d40473162b52053b865030503085e427, 0x113b33503030305318251878083898304, 0x1b3d30383030ed164816550a3a3a31384,
      0x10c9f066066f600480550a389a3268426, 0x13503030300d4f00d4f14ff00000c9f0, 0x10325030a5164816550a3a3a3138413b3, 0x10eafaaa5184818550a30a3268426b3d3, 0x11ecf141f1d4f1148f1231f131f023920, 0x2020a04210860,
      0x2021204210860, 0x1151f33212f330fac7010275f005b7f0, 0x2024204210860, 0x119ff00d60d60c62bdfc60ccfe62e56, 0x10492f014df6c1caf5b9f1dbf5b8f1dbf, 0x1838331cf172a735522200225f031bf0,
      0x1141fe52b9f1c55395500939393083, 0x173c32c6207a115f0109f0020af01e3f, 0x10f40000930930832bdf8324ef176a, 0x15522207a000086492f861e3f0e517ef, 0x101c5539550093939308383830172a73, 0x1073c32d6200015ef008620af860ace5,
      0x100000e500f40000930d1f93083083017, 0x133b533053346523052300c0eaf029000, 0x1e853116f0116f0084898404d404e716, 0x1159f66370c9f00c9f34bf000f50e8ed, 0x135030303000c158f27158fa3bd1bd166, 0x8421081810a1,
      0x8421081810a1, 0x11603b503005048000a3a3a3134513b3, 0x18d45053b86504800d3a32a3264526b3, 0x1eda35300000c8bdc858a9589b0d4f45, 0x10cef668b0c9f0cef0c9f113f00000a3, 0x1a313013b3350303030238f1238f1b66,
      0x8421081810a1, 0x100e1f01a4f00fef480fef76d4a3a3, 0x10fef1c0f0f4f0e1f0f4f1fb0fb31df, 0x8442081821a1, 0x176d3a325a326026b300300300fef112f, 0x1cdfb0e5ffb1e5f000000fef480fef,
      0x1052302c0feffd0fef0dbf0f4f460f4f, 0x1840089004004e71633b533053346523, 0x1dcb40b4fb180d700e8ede853958495, 0x103002c14271414690769e61e0fcf116f, 0x10057448747433a3a3a313013b3350303, 0x1b865d3482190a30a326026b31603b503,
      0x19525959508389830400473162b52053, 0x1487474c6a3a3a313013b335030303053, 0x148836b0da389a326026b30030030ed74, 0x169e61e144f116f8bb40b4fb180d700d3, 0x1144814746907] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x103f0f06d197f38eff934cff90058a00, 0x10d4f08d57053fe6519e135f9e001c1f, 0x1008208142121, 0x10f85953b7f6f6f614df0bddc58a958fc, 0x1f80573d5700890040040e0f1684b584, 0x10fbff95baff90e48a00c5fb6242424,
      0x1a51136f2ddf136f00003f1f01caf1acf, 0x1088208142121, 0x10162f00a00a15af0dffbb0ddf0c3f0, 0x10294f57024ff0d1f1dcf14df1dcf13ff, 0x1000021af0162fdc100fa9100f01a0f, 0x10007d07d54135e1313a50e42405924ff,
      0x100000c9f00c9f15af0840ddf840a8, 0x113106f1326a5a4e40800136f24ef136f, 0x15bbf02b3f261f1db1db0a80007d07d37, 0x218208142121, 0x218208142121, 0x111bfe4240192f0eff5bcf0eff250f010,
      0x8482081421a1, 0x10a80eff1e3f0eff7d07d541301313a5, 0x134df0eff00000005bdf161fdb0c6fdb, 0x17d07d01301326a5a4e49301e6f0eff, 0x100e4240c50eaf118fa80effad0eff, 0x10d8f104f11bf104f172f1a0f0153f,
      0x10d75701313a5262f000316f0d8f195f, 0x1007d54130b07a05e765e76b4e6b4fb18, 0x1f607d0b0005e765e76b4e6b4fb180d7, 0x1124f02def97bd97584e581a8f0d4f08d, 0x1bc0bca9585a58100f0d4f08d193f0ee0, 0x14e100f00dff00ddff600dcf0124f0,
      0x1034cf00058a0c5a800000974a97100f, 0x101a7f0f91c1ff93f0fdb6d197f38ef, 0x18404d4040e0f160b515053fe6501a7f, 0x1160b500f85953bb011bf0113f8489, 0x15454f81dc1dc10cf84898404d4040e0f, 0x1004208182121,
      0x1004208182121, 0x154130ddf1313a50e42408a024cfb654, 0x1f93f1fdb1caf1acf00000a80007d07d, 0x11326a50e4f50017ff17df17ff0f9493f, 0x115af0dff00ddf00a80007da47d161318, 0x10d3f16bf13ffbb162f0c3f0a104f0a,
      0x10c9fd40c9f0180d715024ff0d1f16bf, 0x1000007d5924ff0000494f84162f84, 0x11a9aca94e84162f840c9fd40c9f15af, 0x1084208182121, 0x19717df9713ffd41d404901e2f101007d, 0x214208182121,
      0x214208182121, 0x8442081821a1, 0x19779977de67d541301313a50e42404d, 0x197cad4b7d4192f491d4f1acf00000a8, 0x1a47d93130b1326a50e4000d1f970edf, 0x1125f212fae0058a024cfa89779977d,
      0x1123f0260f014af38ef0139f1cbf34cf, 0x10040e0f160b515053fe650e8f123fdb, 0x12d0125f0150f85953084d6840089004, 0x1636363f8c406d40614dfbebd67fb0fb, 0x1d77d541301313a5153fe42408a0eab6, 0x10001cbf493f125f1f0fae0a84343437d,
      0x1e4f500e8f123fdb123f0260f014af, 0x1a8a4145f167d07d01301326a511ef, 0x18400000c9f00c9f0180d715024ff15af, 0x17d541301313a5195fe42405924ff0840, 0x1670a00a2d0125f0150a84343437d5e, 0x11301326a50e400c406d40621afbe162f,
      0x1eaa8634363a8a419ef087dba7d37] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11883f2f8815075157faa0cff8585850, 0x21011084108e0, 0x100fc000570113fd8105f495fc4198f2e, 0x17c6afc0f7f10ecf570006006bc0bcf60, 0x504044110421, 0x108c000d85700000113fbc105ff60cef,
      0x16a1a8f97d8bb130f000600609c460c8, 0x100d0f0d5f230000113fca105f00cef8c, 0x117ff14cf199134f132f17c2dff7cf6, 0x21011886308e0, 0x21021084208e0, 0x109a19ef119efae0000c3f101980113f,
      0x1e6102379801e7e60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x1e610237983cc1e60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x1e600f379803cde60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4, 0x1ae14df117f6d0c3f151f1189f98009a, 0x40800820040009000220010800420008800201a3, 0x100eb0cc0000009800000113f19ef14cf,
      0x114cf014df06d197f9d03e1bef009a09a, 0x1333333034343823232300000113f10df, 0x10e329e3077d4d4d4067e3e30be565678, 0x119059030301b000fdf0189f454609b87, 0x100000fdf1212f0eeb00f5fd90190daf, 0x100104004020100804020800804040021000825a2,
      0x1cd1096da340e4f230d5f23047644764, 0x2021850140861, 0x10fdf0189f24df460146f1bbfcd1aef, 0x13f3f112f0112f10f8176f0301b0112f, 0x204285a1414a1, 0x14764000183f0fdf0212f3f4feb01caf,
      0x1037033076f373c32932023b62304764, 0x10e30be3656c433d633068340170f7f78, 0x10ecf33c30f3730293200d4155fd4067, 0x1392990d5b335030303003017000fdf37, 0x1750940daf940590f8fa40f8f330f1f54, 0x13503030306400000f1f3739339975d5,
      0x17509409406474a47474054392076d5b3, 0x117c07cf602707417749500390075d5, 0x2010850140421, 0x1e5e70f4025000011d2f014cf1990132f, 0x2010850140421, 0x1e6102379801e7e60079bcc408c3cc0798f301e61e7023079bcc00f307a364007b660007a73001e705ec4,
      0x1c402e1880881502be30e3000f8f00a9, 0x2010850140421, 0x16a9b0ca0290dab800001d2f0105f495f, 0x10e1fcd0cd9d00140f0000105f00a9, 0x1030303000000fdf0189f5bef460146f, 0x1176fd33333330f1f108f392990d5b335,
      0x1000eef0f1f00f8f2f40fab3960396030, 0x10212f1eb01caf5bff112f0112f1d6f00, 0x204285a1414a1, 0x139201b1fd5b335030303000000fdf, 0x10200fab396039603047d34343430108f, 0x1472b43444300] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x101c2f1151f4b4619b8729e345e30230, 0x21011886308e0, 0x21021084208e0, 0x10111f111f0caf00daf0daf3a4b454545, 0x10cafad0daf2a3a4b4545450009009, 0x11b103a0450e45000001c2f111f151f,
      0x1e60008118007b66000f3f33cc0f307981e601e607a7300799e600f3079803cc1f5300079bcc01f6343c4, 0x1ad12a107fd80ecb19000900901990caf, 0x1e60079f9803cde600799e63cc0f307981e601e60f3f300799e600f307983cc01f5300079bcc01f634de4, 0x304042108021, 0x1c31e77325278202300001c2fce151f0, 0x21011886308e0,
      0x15b029295678333333017af10f7f78, 0x21021084208e0, 0x129a656783333330044044011df11df, 0x15603329330000017af11df0f7f5b17af, 0x11a61ad429cb5b004404400c45b7600, 0x304042108021,
      0x100d2f157f0d2f000017af070f7f017af, 0x1018df9c12ff103fc49c2e18838ff885c, 0x21011084108e0, 0x114ff00000bc1bc103f5c05cfc11157, 0x100800820040101004020100804040021000825a2, 0x3041485408e0,
      0x9041084408e0, 0x9041084408e0, 0x1bc12ff1d7f0cef7c6a186f0f7f10ecf, 0x504044110421, 0x100469c0109c8c0d85c0f0570000018df, 0x9041084408e0,
      0x112ff00cef198f6a261f97d8bb130f000, 0x1353546943434382323230000018dfca, 0x114630545555093b3b33503030305a59, 0x114630541c55093d5b33503030301463, 0x1063054d355849375b39403780301463, 0x1140140001ca4075d5750780780063,
      0x10305a591c35a4946834b623542300e4f, 0x103030063063054545509393b3350303, 0x1033703000005a541c555a93d5b33503, 0x1370d9f370063063054d355849375b394, 0x1884688bc000005aa41c05a75d57515bf, 0x115c1f15700ceffd12ff103fc41bcf2e1,
      0x21011886308e0, 0x3435f307983cc00f3f303cc686a3cc0798f301e61e7a1a87981e60f307a50d40798f3007a73001e705ec4, 0x15d5f3003cfcc00f3f303cc2baa3cc0798f301e61e6aea87981e60f3079d7540798f3007a73001e705ec4, 0x110ecf14ff00000bc1bc103f5c05cfc, 0x1e6f30079bcc00f3f303cc29c43cc0798f301e61e6a7107981e60f3079c8240798f3007a73001e705ec4, 0x40800820040011000420010800420010800403a3,
      0x1000cefbc12ff1d7f18df7c6a186f0f7f, 0x14600001bcf1acf279f154f380f057000, 0x1018df1aaf6a261f9703e130f00000, 0x1e3094343438232323000000cefca12ff, 0x1355a05a01c2f1151f4b4619b8729e30, 0xd011886408e0,
      0x9021084408e0, 0x105a0ad1151f4b4619b8729e30e305935, 0xd011886408e0, 0x9021084408e0, 0x16314630545555093b3b33503030305a, 0x16314630541c55093d5b335030303014,
      0x18463d36305405509375b394033303014, 0x1380146614a4001c0075d5750330330, 0x1151f4b4609b8729e3d9e300e4f380d5f, 0x12b5fcd109fcd1096da03a03a1c2f0, 0x2021850140861, 0x1dde30000112f1c2f0151f2b5f460146f,
      0x100caf00cafad0151f4b4609b8729e3, 0x1151f2b7f460146f5c2fcd0cd10f8177f, 0x204285a1414a1, 0x100eef78780b97373552220000106fad0, 0x100078006d730f7f20ecf2047c3444444, 0x1370780d6f373932c32023047ac440944,
      0x1c3d6f373932020946834b62304333430, 0x1d5b335030303035ad0ad0ad370f7f78, 0x19975d5752900005900000d541c559993, 0x15509393b33503030300a4000d371c78, 0x17800be5731c239203c63696305454, 0x109375b39403f403074437443008110f,
      0x10110f000e5005a02508463d363054055, 0x1990132f17c07c5c3f0270746674f40, 0x2010850140421, 0x1000e500f40250000031ef0211f135f, 0x1103fc402e1880885c02b4504500110f, 0x2010850140421,
      0x178c30e7732529b20000018df012ff, 0x112ff78c3007302020da056056ad00f7f, 0x1460146f24dfcd0cd9d0000290d1f0, 0x10d5c72900c7fe3000001c2f0151f390f, 0x10fac796096e30177fd30000d01c7899, 0x15c4fcd0cd117f000000d0110f78f4,
      0x1c70c30e300000ad0151f390f460146f, 0x1fac796c396e3047d3440944001c000d5, 0x1472b44142f44000000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1228f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x110fdf16df46119ba90d9f14b0031030, 0x10080402010002400101080080400402080082522, 0x21030886308e0, 0x21030886308e0, 0x21010886308e0, 0x21020884208e0,
      0x10001111f111f02d003a4b4545450155f, 0xf3f3005b5cc016d7300f3003db30007a73003ccf307981e7e600f307983cc01f53001e63cc01e704c64, 0x1010fdf473f1c2f2d16ff210f14b14b00, 0x304042108021, 0x304042108021, 0x304042108021,
      0x100000991000113a0d9f4504500000, 0x1023000f6cc1faf1300f3001f53001e7e6003cc798079f99e600f3079803cc1f5300079bcc01e740fc4, 0x1023000f6cc001f5300f3001f53001e7e6003cc798079f99e600f3079803cc1f5300079bcc01e740fc4, 0x1080082004002200101020080404002080082522, 0x1000ce0fdf01c2f11126fd80d9f8c1c3f, 0x5040c6108421,
      0x304042108021, 0x10effc3f377f3ad45ad1d2f068f36800, 0x11d2f01d2f567833333300ccf67114f, 0x1152f1bdf178178000007767670eff, 0x304082110021, 0x304082110021,
      0x13656e63303300000077114f77ad0fdf, 0x1496f0cbfa9e62d2d00000c4670100f9f, 0x9040884408e0, 0x187b33503030300000007114f0ad0cbf, 0x183830257373552220f3a3a3a30f0f48, 0x10d1f83025f3734b2137f200430433683,
      0x1083c3837625f373842c620043043083, 0x1000000d1ff40f377f30c677c60043043, 0x10295ff3124ff3997a1c8f3a13513500, 0x21030886308e0, 0x21020884308e0, 0x10e7fdc15ef227f0f31f30caf45137fac,
      0x1e60f5e098007b66001e6f3003db3001e6f3003ccf3079879e86a0f3079feb881e63cc1f30d401e741aa4, 0x115ef0ac165f02bff01b2f00740740, 0x1c300f377f3ac45ac67074074008915ef, 0x17407400015eff400000660ac000000dc, 0x122200da30ccfa3f44875b3d30383030, 0x1734b2672004304336838383025257355,
      0x125f373842c6200000083083173f25f3, 0x1f377f3263fc677c60043043083c38376, 0x1207f56141fa4497f45000000f400173f, 0x1f31f30450770ad6716af0e1f990f9f, 0x1e7f53000f6cc003db300f3003db3001e6f3003ccf3079879e6840f3079fdc581e63cc1e679801e741aa4, 0x10000000165f0000000000005c5f02e0f,
      0x100c30000f377f31eaf455c6f77074074, 0x1350303030740740000f4000006600000, 0x1199f391f0f0f11126f164f00004887b3, 0xd030886408e0, 0xd010886408e0, 0x1552220f3a3a3a3155f0155f498f20bf1,
      0x9020884408e0, 0x14b2e3201b3f433c43368383830257373, 0x1f373842e32069436943083083025f373, 0x100f377f30e30e307643c343083083025, 0x17b3a04504501351350690d3f69f4000, 0x10080082010002400101080080400402400082522,
      0x10080082010002400101080080400402400082522, 0x10000001c8f0cbf0d90159f8b0099185f, 0x10010103f069069000180f007a156f, 0x505284140421, 0x1000f30d00d0159f170f0170f997c1eff, 0x1000f3e90e9120f00264f00ac16ff000,
      0x1170f0170f312f1bbf190f1bbf0499f, 0x1180f00f31f30450e3002b4f02baf295f, 0x3ccf3f6cc0079bcc01ed98003ea6001ed98003ccf3079879c08c0f3079fdc581e63cc1ee4e401e741aa4, 0x100124f165f12bff01b2f007406740600, 0x402080090002400101080080400402080082522, 0x1f304516cfe307412cf749a114f89180f,
      0x1180f00000066000cc06c30600000f377, 0x10c60b93656d433c4330030747974f400, 0x13656d43303304875b3d3030440e440c6, 0x12020a31e3f01e3f014dfc61ccfc6c4b9, 0x10000a300000ccf830d1f830725f3734b, 0x1200f40770ccfc60d1fc607f377f31cbf,
      0x105c7f43102f433683838302525735522, 0x11a1f1cbf00ccf156f87346fe316cfe3, 0x1083025f3738420720690669062d3fbd, 0x101a1f0000000cef0187f07643c343083, 0x1950e00180f000000e600700697a69ca0, 0x1a42d010e1c9f100eb110f5f00000950e,
      0x301202140021, 0x304202140021, 0x100800a2001002080101080080401002400082522, 0x304202140021, 0x10330a90d9f14b155f10046119b00000, 0x301202140021,
      0x304202140021, 0x10080082001002080101080080401002400082522, 0x304202140021, 0x1ae07708700d1f6700c40f9f3656033, 0x120bf170f000e8f0faf207f0140f1392f, 0x505284140421,
      0x100c40f9f3656e6337b3302b7f0278f0, 0x10faf225f000e9f000770130f014df67, 0x10ebf31f30450000d00d0159f170f0099, 0x2804020004400110002010080480002000001a3, 0x10d00264f0000004c0ce0000014df670, 0x177670ccf670007f377f3045000e90e9,
      0x1170f00461bbf279f9b5a1eaf5a00c367, 0x1203f00087875be3e3e30099031ff1c2f, 0x100180f000165f000000690669067bdc, 0x1000130f77874ee3d8e30743f5f74123f, 0x1f400180f000000660c40c80646060dc, 0x1747974] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10dcf540dcf290b36d5b3350303030230, 0x120744374435c375c4a2907373552220, 0x10744374435c085c5c0dcf79e5731c239, 0x15cf400430430daf37330930f37302c32, 0x12920237407405c665c330dcf0e5e70b0, 0x1735522200dcfa40dcf550b75d575252,
      0x1e5291c553955000005c375c4a297673, 0x176f373c320207407405c085c5c0dcf79, 0x10dcf0e5250b05cf400000293778dd93, 0x10cbff3133133068347407405c665c29, 0x21011886308e0, 0x21011886308e0,
      0x14d1bed956783333330d6842c0f8477f3, 0xd011886408e0, 0x111e1f0152f4a178178000000cbf6767, 0x304082140021, 0x304082140021, 0x1008000a0040041001002010080440001000001a3,
      0x1d6be3656c4330330000049af0cbf229f, 0x177236fd622efd610710000007767d4db, 0x304082140021, 0x304082140021, 0x1d61cdf452c1f450b6000049bf77229f, 0x10ee00393f0c6f229f0c6f34efd62c2f,
      0x100002c2f4e308f0c6f2c1f7749cf774a, 0x1229f7a156f2c1f2c2f115f49df115f0, 0x1774600006906905c8f2c1f308f2c2f, 0x1ca00000192f4e49cf0c6f192f7749ef, 0x11cdf393f1cdf3f6f1cdf34ef02c2f, 0x10300dcf590dcf6906905c9f1cdf308f,
      0x1229f3a03603629e30dafe30b3350303, 0x10e7fd4036036b7e34de3000156f00e6, 0x1000229f00d60d60450450b70000d4, 0x18b0c6f0003a4b45454505454b700229f, 0x1152f567833333306349ffcc49ff07e8b, 0x10063690769691b4f67229f0daf1e1f0,
      0x1693c1b4f8b229f0c6f0d60d6dd00c7f, 0x1a63629e30dafe30d5b335030303069cc, 0x1540dcf290b0760761b5fe61b5f05c36, 0x14374435c375c4a29073735522200dcf, 0x14374435c085c5c0dcf0e5731c2392074, 0x143c343154f37154f0930f3730202074,
      0x15c665c154f0dcf1e3fe5e70b05c0076, 0x12c0f09377f3732923320030747974f4, 0x1842c0f840f30f30330330030f4033037, 0x10000d47bd40360360e31e3075b300000, 0x1e60008118007b66000f3f30798f307981e66a5007a7300799e600f3079803cc1f5300079bcc01f6343c4, 0x1033054d3000000000b70b70190190940,
      0x1063213fbe213f9cc467d40d603656033, 0x1006369f4693c07372c0f0930f3730202, 0x1be6930bf07842c0f844af30e7ff3000, 0x102900005c375c4a29777373552220069, 0x1d57525c30330037009377f373292332, 0x1e61b5f075c36a6362900daf000b75,
      0x1567833333300dcfa40dcf95095ee1b5f, 0x1553955095449544169f670daf4d4a056, 0x1330740c4f74095c085c5c0dcf0e5291c, 0x105c007644c444ba67e60d6036560330, 0x1747974f45c665cc40dcfade5250b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10faf75d57512120157faa0cff8585850, 0x21011886308e0, 0x21011886308e0, 0x100095379595117737355222074947494, 0xd011886408e0, 0x12074074095089595066e501c55395500,
      0x10000f40000036379367d617f373c320, 0x1230470d0f4747c474074095095000e5, 0x19395930f31f3b7334d3303434382323, 0x10004400104004100502010080400802020082da2, 0x10102f00fd0fd00c7f00c7f0b702b095, 0x12304764476414591414001edf0102f,
      0x10952500e5e70330330da340e4f230d5f, 0x1ad02a2a12ff24df105f193f0002b095, 0x1476414f814144c9d4c0d9f3c106f3c3c, 0x15474740e9f36d5b33503030302304764, 0x1074947494075d57502020230a439274, 0x1009377930f30cbff303313306834001c,
      0x10002400104002200d81020080400402080082522, 0x11c3379367d60f3730202059b65494000, 0x840100180021, 0x15474740e9f0d5b335030303064e917e9, 0x174940faf75d575000006474a4747474, 0x1747400d5b33503030300741774957494,
      0x114df17ff6d197f9d03e00d322274108f, 0x139030113f014cf9e10bf10df10bf1bef, 0x11a8f9703e000202960960800fab3003, 0x1012ff19ffe9cae9130f18df0f2f6a, 0x1290d1fa96a9b200f0179f00dab80cef, 0x1ad27cf2a5cafd802d001ecf000e9cae9,
      0x10120f0014274c163f4c236f3cce3c7c, 0x12b15df5e171f95f495250da9e5e717bf, 0x1434374108f74740d0d5b335030303014, 0x14396ca960814df0fab3003003047d343, 0x1472b4344] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10303014591414e3f334343823232300, 0x1030301463146374547474450b3b33503, 0x10301463146374547474f666d5b33503, 0x1e3019a4006306394542033075b3003d3, 0x14b45454501401407427420e9f75d575, 0x10caf19191903c111f3c3cad2d8f2a3a,
      0x103c9a3c9a10bf219f10bf10bf2d0d9d9, 0x110bf10bf1a6f0edf6dd9151f19189f19, 0x100f5fd9019eb1903c9a3c9a10bf19ef, 0x101f5f10df009a09a0daf27df0e5cbf9d, 0x110bf0d3f10bf0e1a6f155f6d0f5f1c2f, 0x10b65903452f36834e323032303c03c0,
      0x10303030063063054540000b335030303, 0x175b3003d303000007454747410d5b335, 0x8800220008101004008010200440011000403a3, 0x175d575e3a41900063063945420330, 0x10d8fa61ad4e3cbe3000007427420e9f, 0x1e9cb1b87875be3e3e306907695b17af,
      0x1ac6acb0f7f5b0ecf5b00000e9171fe9, 0x11b9b8746e30e30690690e9bce9e9296f, 0x1a917af01f5fca00000291fcf4b4a0f97, 0x1157f0d2f690690e97ae929296f06a, 0x10330343438232323047594714c40d2f, 0x13a4b45454500840849509500f31f3033,
      0x880022004004100d02010080400802020082da2, 0x1014591414009113f090111f111f0000, 0x10146314637454747400b3b335030303, 0x10146314637454747400d5b335030303, 0x10e008463d363945469cb0075b3003003, 0x1380146614a4746774690e9f75d5754b0,
      0x13c3cad02a3a4b45454500e4f380d5f, 0x12500e500e30e30da0f5fd9d9d93c111f, 0x102a2a12ff241f105f394f0002b095095, 0x12014f814144c9d4c0d9f3c106f3c3cad, 0x1c3444444950eef95950ccf073735522, 0x10944e93e5fe910bf22ff06d730202047,
      0x1547474036d5b335030303023047ac44, 0x10557407400e9f75d5750202023000074, 0x108477000d6f30cbff3133133068340a4, 0x480022004002201f81020080400402080082522, 0x1023000f6cc001f5300f3001f53001e7e63ca1a798079f99e600f3079803cc1f5300079bcc01e740fc4, 0x1e644d667c40c6f76036560330330084,
      0x110efeb120f0dbf00cbfd901901904a44, 0x137c30eff760f37302020cc9a49ef9a4d, 0x1541000b3350303030b6596943694393, 0x840100180021, 0x195950dbf0e5731c239203c636963154, 0x840100180021,
      0x154f4cbbe075b30030030744374439508, 0x195250e5f0e53a6c0141f008463d36394, 0x1074074e900d5c7020200746674f4955a, 0x11bef14df3f7f6d265f9d03e00d3055, 0x1023920113f014cf0fff10bf10df10bf, 0x16a261f9703e00000096096000fac7,
      0x100cef012ff135fe9cae9130f18df1e0f, 0x13a2d3a690769107fad0d8fa61aa902d0, 0x1071f2f1f1f1ecf0d8f2e1a00000dad4, 0x13c7cad4a2f2a4a1fd802d0017af0000b, 0x117bf0120f0014274c13ef4c1aff3cce, 0x1142b2d5e111f95f495250d125fe5107f,
      0x144094474c374e90d0d8fd5c7a902d00, 0x196c3962def14df0d8ffac70000047d3, 0x1472b44142f44] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x100f5fd92d190e19020aa0cff8585850, 0x187a9e34be302000486f001ebf1bdfeb, 0x10c3f11198075000318f0115cfd94619b, 0x20e12086309e0, 0x20822084209e0, 0x1888208c409e0,
      0x2a82085509e0, 0x8882084409e0, 0x10750e9f1230f1eb112bf174f6c16ef6c, 0x8882084409e0, 0x1088208c409e0, 0x1088208c409e0,
      0x1000faf1d3f174f990faf010d4a3f0d6c, 0x20812084109e0, 0x136152f560378787eb177373552220000, 0x11221f266f141f30af141f174f1119e00, 0x2f776c80f307980f31e67981e61e601e679807981e77bb07981e60f307a364007b660007a73001ead1ec4, 0x9066601ed98003eae1181e61e601e679807981e7026d3981eda7307a373307b660007a76cc1ead1ec4,
      0x20476c803cc7980f31e67981e61e601e679807981e702307981e60f307a364007b660007a73001ead1ec4, 0x1e76c807987980f31e67981e61e601e679807981e702307981e60f307a364007b660007a73001ead1ec4, 0x1870717f373c326720166f1305f10f0f, 0xf316c80f307983cc1e67981e61e601e679807981e77bb07987980f307a364007b660007a73001ead1ec4, 0xf316c83cc07987981e67981e61e601e679807981e77bb0798f300f307a364007b660007a73001ead1ec4, 0x1000141f1a000190036011af03716ff,
      0x101773735522201b4f0156f3ac4030af, 0x1c327720165f166f36152f5607378787, 0x11a4f01b4f36156f11af037087017f373, 0x15ccf10e8f0195f00e5f00e5f100f0f0, 0x3e2c8003d39800f4e67981e61e601e679807981e702307981e60f307a05d70798f3007983cc1ead1ec4, 0x1088208c409e0,
      0x1ec6beb00cbfd92d190e190201b1f2e1f, 0x11b6f7787a9e34be30203f8f00daf06b, 0x113df0111131f07500029086f78646, 0x804080110020400802010080404002100086da2, 0x2282085509e0, 0x8282084409e0,
      0x1239f2dcf0f0f127af275f13df141f, 0x8282084409e0, 0x1010d1f5cdf0d1f0f1f07534ff2dcf, 0x20212084109e0, 0x1552220000002dcf199f275f0e8f2dcf, 0x1c32c62036369393930838383eb177373,
      0x136000190093093083c6830717f373, 0x1017737355222000029c407b0036213f, 0x100147f00000003693939307838383, 0x183017f373c32d620003ecf010df0490f, 0x18646077870e30e3009320bf930830, 0x1100f5f2d0c7f00e0330000290862e2f,
      0x80000008200000200800000202000100800010040000040100000401000000401000010040000040002000400002000400020001000004004000010200000100040000102108a2726, 0x146109ba92d04b0330000011c1f2c3feb, 0x80000080200000200800002002000108000100040000400100004001000004001000010040000040002000400020000400020001000004004000010200000100040000102108a2726, 0x20612086309e0, 0x1c47b3656773387330000001244f16df, 0x20422084209e0,
      0x1170f6c197f000000c800f9f067148f8c, 0x17b365677330cbf3300000eb012bf06c, 0x1010d5cef0d6c00c800f9f0671ccf8cc4, 0x20212084109e0, 0x127df0c7f000000170f148f2c3f99392f, 0x10000006713df0e1febf30f3dd0c7f,
      0x10148f350f0e8f1010f1f5cff0f1f221f, 0x20612086309e0, 0x20612086309e0, 0x1006713df0e1f07f30f3c367067000000, 0x10000000c400000141f00000c7f0000, 0x111cf100000070000f3210ff300f9f,
      0x1e60f344580005b20000f32046000204600081181e702307981e60f3079fa7307b660007983cc1ead1ec4, 0x100112f0013df0eb02e3f33df11cf4a4f, 0x11b1f0000000000f30e3ff3c300000, 0x100000013df350feb00216f11cf011cf, 0x136113f360e30e30b33503030300c0c0c, 0x1360e30e30222f77184f8716ef01eaf00,
      0x1004504500760767b00e7f00363f9f, 0x1360000048d3a3a3a30000000000113f, 0x10d3f0d3f20cfdc0edf147f0e8f36113f, 0x1155f76186186036036000000d3f0edf, 0x842008180021, 0x842008180021,
      0x18b0edf17df0e8f0113f3a0000022af76, 0x13503030302c0d3f0edf0d3f0d3f20cf, 0x1697600e90036213f360e30e301c8fb3, 0x1140f102f117f9901eff0000f606976, 0x12c74a47474f45495950d0e9f0d7c0f1f, 0x1000953395330e06900f30ef303303300,
      0x12d0247f0e136f01b3f1eb00c7f0f5f00, 0x284202180021, 0x1000c333783300000f345f30330c7f330, 0x1330330a901eef4b2d010bf1460dd9b00, 0x284202180021, 0x11abf0777b870f9f0cbf673c1c4036560,
      0x84200180021, 0x11ebf23bf01f2f004a6f244f4a5f000, 0x110bf1c40365603303301b3f305f1b3f, 0x8100202010200408020800804100024000875a2, 0x1170f102f19900000000777b00f9f2d67, 0x204709d04e41e60f30000799e600f33cc01e67981e7023079c08c0f3079f98007b66000fa98001ee9df24,
      0x169e9ebf35d0ff3000000d304f0d00f1f, 0x1107f38bf30000095952e4f95e91b3f67, 0x84200180021, 0x174c87469f4c3678b67a967e9] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1d92d190e19020157faa0cff8585850, 0x19b87a9e34be302100daf00100eb10f5f, 0x300a02108021, 0x300a02108021, 0x304202108021, 0x110d4a3f0d6c075d575102900100461,
      0x300a02108021, 0x300a02108021, 0x304202108021, 0x500a04110421, 0x12220225f134f5c000faf00990faf132f, 0x1a6110f00f8f00000003700eb17737355,
      0x1672095095185f178f5e178f0700f4fa6, 0x100f8f00360930037000717f373c32, 0x194950950178f5e178f0700f4fa60110f, 0x1074b9178f08178fc4066e501c5539550, 0x10740740178f0178f000e50000f409474, 0x1000cef13bf6afc0f7f278f0ecf57015,
      0x1190f1190f5d1f38af11d5f000000bc, 0x500a06108421, 0x501204110421, 0x1bbf604a7f015d2f297f342f208f03f2f, 0x505204140421, 0x10130f0ca0103f0cef8c6a1a8f97278f,
      0x11198f1198f5d3f3fbf3faf214f00d8, 0x500a04110421, 0x500a04110421, 0x1189f9802e04a8f03faf0351f03e6f, 0x19c5c19c1b01b198f5d132f198f1216f, 0x501a06108421,
      0x8800a2000814022002014080404002100082da2, 0x13fcf8c5d4fced80132f0000f60c41fdf, 0x1113f06d6d151f0189f189f01095c09, 0x484204180421, 0x12d0d83c9a3c9a28ff19ef28ff10df, 0x128ff10df113f06d113f151f25bf189f,
      0x1000fc0005703c21bf3c117f28ff19ef, 0x14699c808c0000570880065c06bc0bc99, 0x10e30d5b3350303030885d06d8069c9c, 0x100f600d61ed60f4f00f4f0036a6360e3, 0x1a40f1fcc5c06c140f6c0e9f990132f00, 0x1183f176f2401463146318ef5418ef,
      0x1880f4f00f4f000a62e000570d5d5177f, 0x16c0e9f990132f25bf05d5f0278f0001e, 0x163146318ef7d18efa47ccc7c06c1daf, 0x1132f1000f60177f106f176f2800d0f14, 0x884208182121, 0x10d57c2dff7c0c3f113f17ff12ef1990,
      0x884208182121, 0x10170f0001e880f4f00f4f000a60000f6, 0x17c1c4f7c06c17ff6c0e9f990132f100, 0x824208182161, 0x1146f183f000001411af18ef7d18efa4, 0x1014cdcacd106f1fef0f2f10c4fce0f2f,
      0x8422081821a1, 0x10245f00f31f30330330343438232323, 0x4004100110004400402010080400802020082da2, 0x16c06c9d4609b870e30e300932b93245f, 0x12304764476418ef5918efd3115f1b290, 0x1005ce5e70330330da340e4f230d5f,
      0x1146f1bbf01aef0000882b25245f0245f, 0x118eff818efd3cd1bcd06c112f6c9d460, 0x133036d5b335030303023047644764, 0x10075d57502020230a43920f8f540f8f, 0x1f3033133068340941c94110f0110f, 0x4002200110002402501080080400402080082522,
      0x1c30f37302020b793779300000f30cbf, 0x1b3350303030d3d6179300fdf370fdfe6, 0x1a4178f178f178f54178f178f990d5, 0x137178f5d6f9975d5750000059178f, 0x1030303009464b664178f94178f94178f, 0x1000f60d32223d108f15330164fd5b335,
      0x1003390307c07c0212f1212f0990132f0, 0x1014210180421, 0x10c402e00001509629620003300fab3, 0x100fdf1000ae0dab8880880151f1151f, 0x1014210180421, 0x24040801004100120020800804100024000825a2,
      0x11146f0e1f000000d1f00d1f001000e8f, 0x20040801020000820020800804100024000825a2, 0x79800f6cc0079f9800fa980798f3079879807987980025f8000fa980025f83cc1e6001ed980079843465, 0x10d5b3350303030cd112fcd9d6c16c046, 0x1024210180861, 0x1003003018efd3c4c4c407108f070799,
      0x12718ef96155f960eefbc1bc1f40fab3, 0x1084210182121, 0x1084210182121, 0x1479647] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1220fdd4619b87a9e34be302303230850, 0x20e12086309e0, 0x10cbff373ad2ad20f368340318f04501, 0x20c22084209e0, 0x1350303030e8011af033037114f4a9fc3, 0x10e807a1b2f2054124f124f99ac1c8fb3,
      0x13503030300300000370099750750a400, 0x100027016cf1b2f2054352f45001c8fb3, 0x103085011af248f330000075170f750a4, 0x15d7f18ff010001117ef1f7f0e0c7f0e0, 0xf307983cc3cc2d90079f981e61e607987980f301e6798079bcc00f3079bcc001f5300079bcc01f635804, 0xf30798f6cc001e679f980799e607987980f300798079f9bcc00f3079803cc1f5300079bcc01f6343c4,
      0x1080080410020401001080080404002080086522, 0x100010fdf16df46109ba90d9f04b00301, 0xf307983cc3cc0798079f981e61e607987980f301e6798079bcc00f3079bcc001f5300079bcc01f635804, 0x20612086309e0, 0x20422084209e0, 0x15d8f5b0670104e3656e633773306800,
      0x8482084409e0, 0x10effc3f30f3ad45ad1d2f06800f9f, 0x1a30f0f8487b33503030300000067114f, 0x1099ac1c8f3a03503500484b550a3a3, 0x18475b3d3038303007a2bff0caf00124f, 0x100994e0560a40000480550a30ccfa3f4,
      0x1550a3a3a308487b33503030300000067, 0x1006701001c8f00d9f350c7f3500484b, 0x8482084409e0, 0x1550a30a308475b3d30325030012bff, 0x804020041004040100204008040800220008a5a2, 0x1382f5b000000225f00a4000048346f,
      0x10f2f395f01d8f021200d2faa00f9f, 0x1e60008118007b66000fa980799e607987980f3007a730079bcc00f3079803cc1f5300079bcc01f6343c4, 0x1e37be3075000001199f2e1feb101bdf, 0x20212086309e0, 0x20222084209e0, 0x1075029396f314f08608601b0f7787a9,
      0x1000861ccf86c4360361e3f191e3f3fdf, 0x1939308383832d4f171bdf7355222000, 0x1003603600173f00717bd905505503693, 0x20212086309e0, 0x1000093093083188f830717f373c32c62, 0x15522200000086353f86071b0f0870f4,
      0x155ac5503693939308383830171bdf73, 0x1c32d62003620cf360860860147f7b0ac, 0x100f40f1f00093155f93083083017f373, 0x177f373dd23320030029000000000e3f, 0x10f30f2f33033003025000833383173f, 0x1360361e31e3075b300000f4078173ff3,
      0x1e60008118007b660f9a503d39803d398007a73007a73007980798f3079803cc1f5300079bcc01f6343c4, 0x20612086309e0, 0x12daf00000a30ccfa3d3000049761767b, 0x20612086309e0, 0x1199f1199f22efac0dac4aaf0ccf0f1f1, 0x4221081810a1,
      0x8221081810a1, 0x10f37302020000000000490490190190, 0x10004813ff2513ff0199f8324ef83173f, 0x113fff9199ff424ef3fef173ff37bf300, 0x1e35a361c8fb33503030302300c13ffb9, 0x107515bf20d9f2023033352f4505416cf,
      0x10f31330330683400397f00a40555a75, 0x20612086309e0, 0x100000e879e8a400004e84173f8477f3, 0x10a30f1f10f1f1795a7919cf5a215f11a, 0x4421081810a1, 0x8421081810a1,
      0x8421081810a1, 0x1203f54264f264f5a01c8fb335030303, 0x17515bf00d9f0027180f180f180f180f, 0x1180f1c5f203fa4264f180f5a75170f, 0x1a3113f360b335030303000c180f11af, 0x105a0e3f1c8fd90350350048000a3a3,
      0x1333675b30d9f033303001f7f0000141f, 0x15a7707715bf330d9f33004800d3a32a3, 0x1677707b0365603303306800000a46cdd, 0x100000a379a3a468203f0f9f203fc8e6, 0x11264f0dbf795a79344f5a113f1126f, 0x4421081810a1,
      0x8421081810a1, 0x1203f76d4a3a3a3000b3350303030264f, 0x167203f15a01c8fd90350350203f48, 0x8442081821a1, 0x1075b300300300fef112f0fef0dbf264f, 0x100d9f00180f48180f76d3a325a3b9,
      0x11b264fa4203f1a1f5a77225f7715bf, 0x11c8fb33503030302302c0fef0f9f0fef, 0x175020202374337474665416cfe3036, 0x10331330683474a47455660000750e9f, 0xf30798f6cc001fd499180799e607987980f300798079f9bcc00f3079803cc1f5300079bcc01f6343c4, 0x10c30f373020200843c8400000f34ef3,
      0x1350303030e8ad11afad1d2f5a37114f, 0x10e8747a74746654124f124f9901c8fb3, 0x16974a474e666374c6e99750e9f750000, 0x1a3a3a30369eb335030303002c742774, 0x100001c8f00350c7f350e948e91b3f33, 0x10a30a303675b300333030740747466dc,
      0x1a474066000000e9f00330330d348219, 0x1114f0effc3f30e7ff30000068366874, 0x1a3a3000b3350303030ad185fad05a67, 0x19901c8f3a0350350e948e91b3fc6a3, 0x1075b30030030747a747466dc124f227f, 0x15600000d348836b0cefa30ccfa3f4,
      0x1741b3f74a474e666674c11bf9900e9f, 0x17448] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x13e7f9b875ae35ae30f33434382323230, 0x100f30f30840840290450048df0046, 0x1019efe5e700066074337433122f0122f, 0x1000e500006605974337433122f0122f0, 0x1e3b3b335030303074bc7425122f0122f, 0x1b335030303014631463122f54122f00,
      0x103d303014631463122f54122f0066d5, 0x1d5750930a409463263054000e375b333, 0x1142142122f0122f0075] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000111f00ad2d8f2a3a4b4545450e30, 0x10ce00cafad1aef2a107fd819cb190e30, 0x10cc241f24df10f5f10e10e09b8700019, 0x300a02108021, 0x300a02108021, 0x301202110021,
      0x1cc3fcfcc0000f5f00000461010efdcc, 0x304202140021, 0x304202140021, 0x100e6f139f4abf0320f001010e5d9f, 0x284202180021, 0x284202180021,
      0x1010bf212f271f203f271f0edf0fdf, 0x1001001d2f109f15cf125f1dd1dd010bf, 0x300a02108021, 0x300a02108021, 0x300a02108021, 0x10fdf1f3f0e6f173f4abf0320f00000,
      0x145010bf010bf154f271f203f271f0edf, 0x10e09247f111f111f0e9f0003a4b4545, 0x100900990e9f1b003a045045045247f09, 0x129009] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1045001004619b87a9e34be302303230, 0x300a02108021, 0x300a02108021, 0x1003700c30cbff373ad2ad20f3683429, 0x1030033783300000f30f3084084093033, 0x1750a400059000005400990d5b3350303,
      0x1d6e3e3b33503030300202037009975d5, 0x1e375b33303d303003456333634554540, 0x1b69463263054000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100011df0017af11efa65678333333020, 0x15b00705b17af0d8fa61ad4e3cbe30200, 0x1c80c8208f0eff19b1451450e7730460, 0x300a02108021, 0x300a02108021, 0x301202110021,
      0x13fcfc8271fc80009b00000c319914bba, 0x304202140021, 0x304202140021, 0x1ac1f5f02a132f296f0320f001014b, 0x284202180021, 0x284202180021,
      0x11ba10e10e0e90e9151f25cf180f25cf, 0x300a02108021, 0x300a02108021, 0x301a06110421, 0x10320f000ce0115f00fcf00fcf235fba, 0x15c25cf180f25cfac1f5f1a1f2aad296f,
      0x111df11dfd800056783333330e90e9, 0x1d87600560330330781eef444b441eef, 0x12504404400c4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1157f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1bc01f5f13bf6dfc2e5f225f5daf5700, 0x1186f0f7f5dbf0ecf14ff00000bc1fff, 0x13e225f189f57000000bc000cef298f6a, 0x1980d8010469c251f038ff13bf8c190f, 0x505204140421, 0x10ca01d7f0cef198f6a261f97225fbb,
      0x115d15d399f4acf398f1fff00d80130f, 0x500a04110421, 0x500a04110421, 0x100000c49c2e04adf0398f03fbf03fbf, 0x1001134f215f01cc12bfcc013bf0197f, 0x44621c1835a1,
      0x484204180421, 0x128ff0d3f113f1dbf6d1caf277f01edf, 0x101edf009c3c21af3c112f28ff1c5f, 0x11c5f28ff0d3f113f13ff6d14df277f, 0x16d03e2dcf11bf9e03c21af3c112f28ff, 0x10000ae08808c01bef00f2f001f5f0,
      0x116bf0c4ffd13bf0e8f166f0dbf0198f, 0x1885d0c4f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1f31f31d9f333f8f3303434382323230, 0x1080042000804022002010080400802020082da2, 0x1840f3287ff30000046000008408433df, 0x1e5e74c00e5f0074be74be122f84122f, 0x1005974be74be122f0f4f122f666c19ef, 0x125122f0f4f122f666c4ce55a4c00e5f,
      0x154122fd400b3b335030303074bc74, 0x1e60f1f0d5b335030303014631463122f, 0x184075b3003003014631463122f54122f, 0x175d5752900daf00946369634d54d3d4, 0x114761476122f93122fa45c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1f60f6660866000e501c12bf3910af00, 0x110e5f381f0e5f0eb01caf104aef000c3, 0x814208182121, 0x814208182121, 0x110000001adf0000f8f10af0112f0112f, 0x80040002000040002800400020000400028000600020000800080001000200004000040042028040002000400420280400020040000020040000020200000100200000102129faf26,
      0x1183f4c0460146f10354f0000d7f00d7f, 0x814208182121, 0x1321f12ff4aff105f9e0d5facd0cd14c, 0x814208182121, 0x10018df000276f106f1fef3fff1c4f02a, 0x17c19ef6c28df6c0990132f1daf000,
      0x166138feb0e511c12bf3910af07c39af, 0x804208182121, 0x11adf104b0f010af018efc39de69d6608, 0x8442081821a1, 0x10d7f8c0d7f10f4f106f0f4f138f070, 0x8442081821a1,
      0x10e8f0a6a6110f4aff0f8f9e0149618ef, 0x1141e123f355f123f0f4f5e0f4fe6] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10230000054005a36d5b3350303030230, 0x1340370370a40555a75d57515bf20d9f2, 0x10cbf674e8408477f30cbff3133133068, 0x300a02108021, 0x300a02108021, 0x1167271f8425cf840f30f300000a47767,
      0x84200180021, 0x10f4f178f796c0e5fa62e4c00e5f00167, 0x84200180021, 0x14ca65a4c00e5f0059950e5f95bc178f, 0x10303030954c950b178f0f4f178f796c, 0x10030030548b6367638b5454d4000b335,
      0x1b6946337636754d3d484075b3] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1100000c30011af66066000e500005700, 0x814208182121, 0x10e8f112f183f0e5f163f0e5f0eb01caf, 0x100d7f5e0000001adf0000f8f570112f, 0x1cd106f4c134f4c0460146f1000000d7f, 0x814208182121,
      0x1bc0ceffd1caf197fc402e100000cd99, 0x884208182121, 0x1fd276f1bbfc400e6f100000d5884688, 0x20040901004120104020800804100024000825a2, 0x16c0990132f10000018df460154f1fef, 0x824208182161,
      0x166cceb0e51000007ceb7c19ef6c163f, 0x804208182121, 0x10701adf10000018efc3c4e611af669c, 0x8442081821a1, 0x1149618ef0d7fc40d7f5e0f4f9c0f4fcc, 0x1880f4f134f0f4f10cf0e8f0a6100000,
      0x8c42081821a1, 0x1141e07117f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100360c6f360e30e30b3b3350303030, 0x10f1f09907b3a04504500d41ed4000c6f, 0x10f0f087875be3e3e304accbb00f1f8b, 0x11463122f54122f469797977adc7a0ebf, 0x11463] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10f5f4609b870e30e300e4f380d5f380, 0x1000e500e30e30da293ad93a173f1139f, 0x1004210180021, 0x1460146f2b5f0109f0000882b2500117f, 0x10e8f0a61a00000cd39afcd06c112f6c0, 0x14418eff818efc4166fd41b1f79179cc,
      0x1004210180021, 0x1470947] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x193f4252f3303700077f373023320030, 0x1075b3d68418400000f34af3033133003, 0xf307983cc3cc0798079f981e61e607987985b201e6798079bcc00f3079bcc001f5300079bcc01f635804, 0x804020041004040300204008040800220008a5a2, 0x10330330b7d47bd400000364d360e31e3, 0x3cc007d4c0079f9800fa980799e6079879815d50799e6079bcc00f3079803cc1f5300079bcc01f6343c4,
      0x1e3e3e30d6bed401ccf671ccf0c403656, 0x17302020469797974ddcdc0ebf000875b, 0x105493f4271f6725cf3725cf271f070f3, 0x1271f8425cf6725cf0c6f07f34af30000, 0x19463d363d684] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1000000d32555452b02b000d5c7020200, 0x10239207c154f7c01edf11edf0991132f, 0x404000208810400010040000010002000010002000081044000400080000400080010040000080104000400400000400020080000010200000040800000102000000100108b5726, 0x1014210180421, 0x10c412e000000960b9645000000fac7, 0x404000208810400010040000010002000010002000081044000400080000400080010040000080104000400400000400020080000010200000040800000102000000100108b5726,
      0x19bc30e77302020885c8801fef11fef, 0x1014210180421, 0x1c305c7302020da25569b5617af1132f, 0x1004210180021, 0x1146f24df000000b00b0296f1191f5dcf, 0x20040801020100804020800804100024000825a2,
      0x1990d5c700000cd112fcd9d6c16c0460, 0x1024210180861, 0x1f41fac70000018efd325d49d2b12bc8, 0x1004210180021, 0x400080018c004000100020000100020000100020000800c6000400080000400080010040000080104000400400000400020080000004200000040800000102000000100108a5726, 0x196472718ef960b96111f245f1245fc8,
      0x1084210182121, 0x147] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x107a61a2dd6136fd60c5aa0cff8585850, 0x1136f4e87875be3e3e30a9455b450fdf, 0x16a136f0f7f5b0ecf5b0000086454545, 0x1e3b7e306906902bdf86356f86114f5a, 0x1023bfa90000046450452d4e9b8797, 0x1c5690690ad01dcfca114f7a6a2d0fdf,
      0x15678333333034343823232300c232323, 0x119191900d4d4d4c6e3e3e3144fbe56, 0x123cf6c209f6b0e0e0e2d0dbfd9d90caf, 0x1533465230523047644764e80303036c, 0x12932023b623047644764ed0324035396, 0x1b8340fdf170f7f78033033a976e773c3,
      0x100d4155fd40e30e30be056c433d6330, 0x10114f31ff045045a91b9b8746e329e3, 0x1a41533a322200d5b335030303003114f, 0x10020af003355330c3d5c70940940033d, 0x1a47474a322216bf76d5b335030303064, 0x1950055016bf0d5c7eb9421cf9406474,
      0x103d004004e716f4b525005270741774, 0x1f404e7160b525053b8652be3357fe389, 0x113b3350303030532b0cd089e33de304, 0x126b396039603028d3333333a322213eb, 0x1013b3350303030ed033033892152260, 0x1026b396039603047d3434343a322213,
      0x1472b434443020226] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1149f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x12e1a23bfd6322fd600eafaa658505850, 0x14e129f875be3e3e30ad45400f45ad07, 0x10f7f5b0ecf5b0000086454545322f, 0x1e3b7e3000002bdf86086114f06a136f, 0x123bf000000464504523bf4e139f8797, 0x10230eaf0000adca00114f06a2d0fdfa9,
      0x1030ed0316ef03531d6f533465230523, 0x1e424014631463a3222135b13b3350303, 0x1387f03014631463158f0001301313a50, 0x1a596e40006306302d3226026b31d6f03, 0x12705a3023140140158f00a413661326, 0x113b3350303030ed2213f253d353b865,
      0x1116f1313a50e42800000a3222130d6f, 0x1f926b3890389030140140158f005413, 0x100a413661326a596e48900000d320226, 0x15678333333034382323230140140158f, 0x133333306a9b6a87c6e3e3e31b7fbea6, 0x1289f00d4d4d4c6e3e3e3401fbe565678,
      0x127df6b05b01b7f0a61a18ffb91d8f, 0x1c8e5731c2392064e803030324ef024ef, 0x1e31e306495f4959520af33033199f, 0x28824814a521, 0x12305230951b95e90000199f0e5d95ddf, 0x12c4f67b479b4b4181d6fd73d0533465,
      0x11ddf294f0fff00353950954e116f117f, 0x111ef25af11ef20df020df20df5def, 0x1222131e13b3350303030ed030000243f, 0x1131e1313a516efe424014631463a3, 0x103d703014631463158f402f182f13cf, 0x126a596e41508463d363020226026b318,
      0x12023b6230146614a4158f00e5f013013, 0x1034114f1712ff78033033076073c3293, 0x133d6330a60a600e30e30f4e5e702509b, 0x1e50000000d4159fd40e30e30be056c4, 0x1200fab30030ecf0300300000450450f4, 0x10330c3fac70940940030a403302299f,
      0x10202076fab3f4030ecf030640000033, 0x1000000fac7f4942c5f9406495a495e9, 0x18900004004e71625b5f4009517951f2f, 0x1f404e71625b50053b865270574337433, 0x1b33503030305300d6f0089e3357fe304, 0x11a0f144f153f135f00000a322213013,
      0x1000195f16bf213f14af104f0104f104f, 0x1edd303308921f6f226eb26b300300300, 0x1074437443833333330d6f07373552220, 0x1158f4b1f182f541301313a5213fe428, 0x1c3430330330cb0734922520149a1406, 0x1a4158f00e5f01301326a596e4c308443,
      0x1146614] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x115ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11f8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1552220a345794513b913b33503030300, 0x1790473162b5207443744383000007373, 0x1000e77302c320744374438900fef6b04, 0x133042504e7160b5f4004304384033, 0x1b926b31603b50300574074089330fef, 0x100430438300000073552220d34524526,
      0x17302c3200000896b000400473162b52, 0x1042504e716f4b5000430438403300025, 0x14518af450532753b86500008933033, 0x145450db97124f9718af29194f9b101f, 0x14b00000f7d8d8d818af133f3a3a4b45, 0x1f7264ff729bfac16ff18af194f4b29af,
      0x1101f133f107f3a99450450e90e900f3f, 0x14b2f101f18af0267fce00000cbd8bad8, 0x1d7f60e90e90101fcb264fcb403fdb, 0x108d00116f5a1ee6b488b4fb184b3f, 0x10000bd1b4f97166f58130f581a8f0d4f, 0x1238fbd587a58580d4f182f8d0d4f0,
      0x1100f1100f358f460000690690bd0e5f, 0x501080240860, 0x158100f0d4f08dca000005a21df5a166f, 0x19b145252f450690690bd4c238f5a58cd, 0x21020884208e0, 0x12e6f3a4b4545450cb97f797db29ec,
      0x11eff18af04b04b00000f7d8d8d81133f, 0x9020884408e0, 0x1115f3a994504500000ecf70f739bf0, 0x139bf101f0ce0000000cbd8bad8db133f, 0x1350303030ed0000dbcb101fcb4b4fdb, 0x107a05dffb9a61a1f1fe32defe3013b3,
      0x1018af29194f9b045045013076076196f, 0x105829589b0d4f458d45009709700124f, 0x10f3f9b18af4529af450000a9bd0124f, 0x107373552220a3cb97f7970000101f29, 0x100400473162b5207443744383000169f, 0x18400025ff0e77302020744374438900,
      0x174f489000042504e7160b5007643c343, 0x1104f1a0f144f153f135f0e42807479, 0x1a500213f0195f16bf014af104f0104f, 0x11e0116f07ae6b488b4fb180d7f601313, 0x15a58cd58100f0d4f08d21ef05413cd0, 0x1144f0ddf103f00fef00fef0bd0124f,
      0x10158f0d3f000162f7e08b0a00a0a0dff, 0x114c406060667000b40b43b3d349f1515, 0x1069a06162f0008808848ff0349f0150, 0x1008907a004290473162b520030140d3f, 0x1f40788907a0042504e71633b53300300, 0x1115f0002e7fb92e1a1e30ecfe3026b30,
      0x504084210860, 0x1097000012919b045045026196f76076, 0x9040884108e0, 0x9040884408e0, 0x1450044044d40c40fb0fb560330330097, 0x1220d3cb97f7970000db29ec9b045252f,
      0x11f6fd715010bf43e9438300000073552, 0x1730202095449544116f000b40b4b418, 0x1b4fb180d7007643c34384007015df025, 0x1160b5150095799507116f0d0e6b488, 0x1d7150e4c303d08907a8c0411af040e0f, 0x1961326a50000660668c0c9f00c9f0180,
      0x1124f5a58cd58100f0d4f08d1a2f0a413, 0x10e6b488b4fb180d7000fef00fef0bd0, 0x1040e0f160b500158f1e00ccf0116f07, 0x1172f0000014c3069a0689c4000411af, 0x1141e061c6f0666c46600c9f7c0c9f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x107d5c7eb20f0f20c5aa0cff8585850, 0x144440f0f177373552220469483940e8f, 0x1830f0f66e50f0f1c553955000008344, 0x19344eb17e773c3202074074020af83dc, 0x1460f0fcae5eb0e8f01c4ff4000004644, 0x13823232300c646464c57407409946eb,
      0x1190002b0093c693000e703303303434, 0x16b0c4f0c4f0c4f2d0d9d90caf1919, 0x123047644764e86363636c23cf6c209f, 0x106725048804e71633b53305334652305, 0x103023047644764ed63636353cd02b089, 0x12020230a4392a343434300d5b3350303,
      0x1e70330330b834001c0094839400d5c70, 0x12909a909b870e30e300000093093000, 0x1e7730202063b663114f19cf114f04609, 0x135030303064ad172bdfc6c3449344a90, 0x1000006474a47474a343434316bf0d5b3, 0x1030300741774954694839416bf0d5c7,
      0x103005d3222a3434343130f2f13b33503, 0x153b86502029643964326026b31603b5, 0x189f46725048804e7160b50054275396, 0x143434313013b3350303030ed2b09109, 0x1084208182121, 0x143964326026b3003003047d3434343a3,
      0x1472b43444396] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x117cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1030ed636363538d5334652305230850, 0x124014631463a343434313013b3350303, 0x1014631463158f43434313661313a50e4, 0x1a40063063b543b54326026b3003d303, 0x1085140140158f960b513d71326a50e4, 0x103030ed270dff35531653b865030503,
      0x1a50e42800000a3434343138413b33503, 0x1b3d3030030140140158f005413661313, 0x1181326a50e4a40000016431643268426, 0x10e8f239200eafaa140140158f9601613, 0x1172a73552220c4940f0f949907fac7, 0x10e50f0f1c55395500000834444441f9f,
      0x117ca73c32020000020af832d2f830f0f, 0x1cae5eb0e8ff41c4f00000046449344ca, 0x1230ed6463640eaf00009946eb460f0f, 0x10025204f8700e5e7033033034382323, 0x10e300000093c693000e70330330a60a6, 0x12392064e86363630000000000e500e3,
      0x100006495f4959520af44444400e5731c, 0x105230951b95e931bf090c4f0900e5d90, 0x18489250004004e71633b533053346523, 0x14313013b3350303030ed636363530840, 0x11301313a516efe424014631463a34343, 0x126026b3003003014631463158f434343,
      0x11301326a50e4008463d363116f430643, 0x1b300339030230146614a4158f964c06, 0x19400fac7023920230a402043094300fa, 0x1132f060f1f02e5603303303400000940, 0x1093000e703316cf3302a15bf2a0c406, 0x1b9191f142f0f1f02e1a000000000093,
      0x1132f730202063b6631e7f1b0f1e7f0c4, 0x10030641a6f17404fc6c34493440fdf0, 0x1006495a495e9f44309430f1f0fab3003, 0x19517951f2ff4942c5f940f1f0fac7000, 0x10050000a343434313013b33503030300, 0x165d3020043043260f2f26b31603b503,
      0x1116f881a4f07b479b4fb180d70053b8, 0x116aff4047904e7160b50053957c95e6, 0x1ab127f145f010ff00740674068925, 0x10d3f3c2c4f12bf112f277f10dfab0edf, 0x143834444440d6f07373552220ed273c, 0x1158f11541301313a5213fe4280744374,
      0x10442081821a1, 0x1084208182121, 0x14349442544309f02a7302020149a1406, 0x1158f964cc3131e1326a50e4008443c3, 0x1146614a4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x117cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1289f13bf1d8f020c5aa0cff8585850, 0x101f1f166f0001c1f1a5f129f288f140f, 0x111ff0e6f205f8c136f13bf18ff0201, 0x504204210860, 0x14e29cf4e0d5c7010196f0e9f000244f, 0x504204210860,
      0x11dcf00d60d6187f00013df07a61a1cbf, 0x1000148f161f12ef4a5f0e1f1faf1ddf, 0x10013df17737355222002dcf02dbf1b1f, 0x1095095b900c4000a61a0001900000830, 0x16b0009300f2f0001c1f17e773c3202, 0x10115fd8000244fce2a107f8ceb13bf,
      0x120af830783066e501c5539550940109f, 0x17407400007000e50000f409474074b9, 0x10000119f1a0e30e30b3b3350303030c5, 0x1144f017ef17efdd0e0e0e00d61ed600, 0x1d3d30f1f19cf0f1f2d5fec011bf11bf, 0x10e30e3013b335030303014631463a3d3,
      0x1631463a3d3d3d313001eb9000000a61a, 0x1d600100011a0e30e30b335030303014, 0x1e78ae07987980f31e67981e61e601e6798079a04709cf9801e60f307a4570079bcc007a73001ead1ec4, 0x1e76c807987980f31e67981e61e601e6798079a04702379801e60f307a364007b660007a73001ead1ec4, 0x14500d60d600000011a0e30e300d6156f, 0x1e601e67980798f300fa981e61e601e6798079a04709cf9801e60f307a4570079bcc007a73001eaf04c4,
      0x100639363a3d3d3d30000000000000450, 0x146b7f7b70f2fbb10bf10f2f99ec9b000, 0x84208182121, 0x100e74d330c6f33034343823232300c, 0x14764e8d3a4d3115f0932b93b700021cf, 0x1004e71633b533053346523052304764,
      0x147644764edd3a4d3530882b258900004, 0x1392a33333331faf0d5b3350303030230, 0x1941c94000000d5c7121202321dfa4, 0x218008108021, 0x218008108021, 0x10b7930930000000e71330330b834163f,
      0x8004200110020400810040201008002200088da2, 0x1fd4b6ffd105e0f4b5f111ff1125f0000, 0xc21048180421, 0xc21048180421, 0x822048180421, 0x1a3c4c4c41faf0d5b3350303030d33e4f,
      0x1941861861c3d5c700000d307a40707, 0xc41048180421, 0x842008180021, 0x842008180021, 0x113b335030303009464b664134f9420af, 0x1026b31603b503005d3222a3333333130,
      0x104e7160b50053b86596296203303326, 0x113b3350303030532b88025890e6004f4, 0x126b30030030a4d3c4c4c4a3c4c4c4130, 0x147964727ed96c496c489c446c4260] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10ddfae0b4b418e6d73d00c5f12df0, 0x11e1f0162f0222f00a00a15af0dff13cf, 0x1145f11bf10fff60116f071edf67b400, 0x113cf0fbf0233f013cf15af015af6e, 0x10006e1a0f11bf153ff60113f233f0fbf, 0x110ff10233f0fbf13cf0fbf0233f013cf,
      0x1088208142121, 0x14b7fac359f000015af015af113f145f1, 0x1088208142121, 0x1351f27ef5e1f1abf0e4150c5c5118fac, 0x101326a5005e2f001a5f01cef013cf01, 0x4040101100014000500010080402020080807a2,
      0x10b05e05e0fafb407b4fb18134fd7134f, 0x1008008fd04c4040e0f160b59e0137a0, 0x105e05efd0c9fc40c9f0c300007d7a093, 0x1080080040040e0f1639cfb5ae07d000, 0x1000c9f00c9f0ac339cf0ae0a809d939d, 0x158ca58100f0d4f08da9009d0b9d00,
      0x128024cf0d0fc5124f00dcf0bc0bc25df, 0x105e0b40b4fb1813cfd7f601313a5e6e4, 0x10fb6e011bf01507da47d5413000b05e, 0x10150a80dbfccccccbd175f138f0dbffb, 0x1cccc162f175f1c0f0dbf0a00a6e011bf, 0x179134fbc1bc1fb0fb6c000000dbfcc,
      0x1084208182121, 0x1084208182121, 0x1057013a72816bf2424024cf79295f, 0x1444413076d676004a000a61e2f024df, 0x1153f18491fd7f50240ead343434354c3, 0x115016bfd744d7440153f0060c9f00c9f,
      0x1181a0f00000c9f00c9f0dff18351fd7, 0x1127f19ab407b4fb180d7004b8f18f4, 0x4422081821a1, 0x100024df105f57015af100f1b8f58116f, 0x110c4fb407b4fb180d700076076000000, 0x4422081821a1,
      0x15e3f0f504415af100f1b8f58116f120f, 0x1440944116f12cf09060c9f00c9f4b9f0, 0x1a91090c9fc40c9f162f00000c3323f, 0x8422081821a1, 0x1ea7a430643116ff4116f162f116f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1589b0d4f498d4905334652305230850, 0x1c36b0e77302842053029045bd00058ca, 0x10c9f00c9f066066f5019af4333430c30, 0x10c30c300073028420d743d7430c30c3, 0x1c30c313e313b3350303030ed86432543, 0x10c313661313a5294fe424014631463a3,
      0x126b926b32503d303014631463158fc3, 0x1001301326a5d7e4a40b563b5630c30c3, 0x149053b865030503085149614b5158f0, 0x103030530250788900004f404e71649b5, 0x1066066f600000a3000138413b33503, 0x126b3d303003018018000000c9f00c9f,
      0x113a51a0fe428035ed160160890002684, 0x1a4027140dff143d158f0dff054136613, 0x1aa14961416158f0001301326a518e4, 0x1161f1d4f1148f1b7f231f10239200eaf, 0x500a04210860, 0x501204210860,
      0x139df4e0fac701213f275f405f0001ecf, 0x504204210860, 0x100d60d60ccf0000ccf072e1a199f4e, 0x114df10df1caf324f1dbf1b7f1dbf39ef, 0x1172a735522200225f39ef31bf31ef000, 0x10e5288f1c553955000008300031cf,
      0x1176a73c32020000020af830831e3f, 0x1405ff429df119f0009300d1f00024ef, 0x10940115f0109f14df0001e3fc4e5205f, 0x1094e90e90404f0000ac2a012ff0105f0, 0x10196f001ecf00024efca6a288f0a900, 0x1352f338384084001735522200300eaf,
      0x40043000100008000200000000200040080002000200002000800020002000020008600430001000080080000100008000400d0000020040000080500000100400000101208fbf26, 0x10c7b30931930000001e70330330030f4, 0x40043000100008000200010000200040080002000200002000800020002000020008600430001000080080000100008000400d0000020040000080500000100400000101208fbf26, 0x10080402100404010100080402080022000895a2, 0x1454500d686d60000006b1a0e319afe3, 0x139ff1fcff716df4bafbb0003a4b45,
      0x18384147f8400073552220d339ff1a9f, 0x1d40c40e7dd00c7f00d31c5ff41c5fd4, 0x17833333306394631a1f93193f7d4147f, 0x8442081821a1, 0x1230102fbe102f4bbfc6d4d4d4005656, 0x18408404ca04e71633b53305334652305,
      0x143d4c384c36b0e77302020530250089, 0x166c30c9f00c9f16ef0402f0f501e431e, 0x1d4c384c3cb04973020201e431e4366c3, 0x1c3d4c313013b3350303030ed86432543, 0x1c31301313a53a0fe424014631463a3, 0x126026b3003003014631463158fc30f4f,
      0x113661326a50e4007963796325c3d3c3, 0x1216cf2003014961406158f112f0f4fa4, 0x103316cf330030f49333084084000730, 0x1316f0711a00000b3093c6930000000e7, 0xc211881818e1, 0x10e335afe30cad686d60d1f4e2e3f0f5f,
      0x1316f07117ef000000d686d600000001a, 0xc211881818e1, 0x102020d3ca1a9f196f00d1fbb21bf16df, 0x100d307f493d40ccf840d3f841dff0173, 0x841088180861, 0x10793c6930ccfd40d3fd41dffc41e7000,
      0x841088180861, 0x1d4159fd45e4f01560330330639463, 0xc811881818e1, 0x100134913b33503030300c4bed6ee155f, 0x10d3020264926b31603b5030050000a30, 0x1c4db01a56033033053d353b86589089,
      0x10c9f00c9f1e7f00000db448644d4c476, 0x1049560330330116f1116f1660e8f6699, 0x8421081810a1, 0x8421081810a1, 0x1195fe4280a3edcb44b944d4c476c4cb, 0x1162f1467158f162f0f4f541301313a5,
      0x1116f0f4fa413661326a50e4002714, 0x1335e5f3303438232323014961489158f, 0x1330c6f330a625a68700146f010e5e71, 0x40801000100404010100201008040021000845a2, 0x402008090002400401000880040402020482723, 0x1e31fdfe30093093b7000325f00e74d,
      0x1109f167f01fdf01fdf0e51e0f1aff, 0x176002e560330330d3242f109f406f, 0x10e9649564e8d3407f07326fe61760d3f, 0x8421081810a1, 0x1b40b4fb182c5fd75701313a5117fe424, 0x10d4f1c7f8d8d0c3130881ee6116f000,
      0x1c30fefca0fefa9bdc8124fc85805858, 0x101700fab31033903023014631463158f, 0x218048108421, 0x194000000fac71239202325a4105f2017, 0x218048108421, 0x1146f107f1f4e5e70000034b99412ff,
      0xc211881818e1, 0x10000000e713316cf330a625a69b11b0f, 0x8221081810a1, 0x8004200110040401010040201008002200088da2, 0x13a1f1f1f1f4e5115f00000b793093, 0xc211881818e1,
      0x11710fab30030030d31fdfb91b910d9f, 0x8221081810a1, 0x18243081831e1, 0xc411881818e1, 0x1e61c3fac700000d325a41c5fe61177a, 0x8421081810a1,
      0xc411881818e1, 0x1161b515009464b664b994404f941e67a, 0x8421081810a1, 0x1008208142121, 0x1d7150e4c311af3d98890ae0040040e0f, 0x126a56688663a2f00000c9f00c9f7c181,
      0x1088208142121, 0x11e880e6116f000b407b4fb180d70013, 0x189990e8f9904c4040e0f160b50013, 0x1058580d4f1a4f8d0d4f0c311af670e8f, 0x1000000fefca0fefa9bd112f124fbd58, 0x188660e8f116f991a4f990c9fc40c9f7c,
      0x1149614a4158f66] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x111bff00000029ef1101fdb1db0052400, 0x28820810a121, 0x1008208142121, 0x1008208142121, 0x104f4040e0f1649b54905314bf6511bff, 0x1008208142121,
      0x18413a728024240539303d0890113fdb, 0x10d300240f8c8f5f5f55400ebf0ebf13, 0x113a728db24240f80f50f589000268426, 0x1d3db152402857f5f5f5540f6f61384, 0x12400c5fb693f515f5000f6268426408f, 0x1232f34df232f00000001101fdb1db0e4,
      0x21820810a121, 0x1088208142121, 0x1116f016af0b40b4fb18e6d71a8f0a51, 0x1088208142121, 0x100dff49153f49024ff1b8f327f0d327f, 0x124024ff0000116f01edfdb0c9ff40c9f,
      0x1a50e4280c80000000ebf588458a7000, 0x184b40d300240a80007d07d54135e1313, 0x19c13c31326a5a4e40800000116f000b4, 0x10588458a70dffdb153f240a80007d07d, 0x1a5bbe4280328f11ef34df11ef116f01, 0x8482081421a1,
      0x1240a8207f1e3f207f7d07d541301313, 0x111ef24ef11ef000008402e8fd3db192f, 0x1ad11ef7d07d01301326a5a4e49301b8f, 0x1040e0f160b51500c50eaf118fa811ef, 0x10180d7150e49307a008150815049c, 0x19c13a41326a50000c30000c9f9c0c9f,
      0x11000ba1b4bcf1b0d8f9c268f1000007d, 0x4040101020100804020800804100024000825a2, 0x20040801020100804020800804100024000825a2, 0x1093000080080040040e0f160b5007d, 0x10bc0bca9585a58100f0d4f08d1a2f, 0x1c30000c9f00c9f15af000000dcf0124f,
      0x105757134913a7280242400c5a80b000, 0x1d30002649260160b52400515f6f6f654, 0x1492e100000f87653d35314bf650000, 0x1004208182121, 0x1024240f810d8f10d8f49761ecf761aff, 0x1004208182121,
      0x1004208182121, 0x124054d8d8d8d8540e9f7e7e13013a728, 0x1b693d89dd8d30e9fd87e26026408f000, 0x12801500000057b449b4a7000240024cf, 0x1d7240a80007d07d54130ddf1313a50e4, 0x1a50e41500000d3000100f49100f0180,
      0x1b4fb180d700a80007da47d1613181326, 0x10e9f7a0e9f116fe616af1a8fb415af, 0x16e491d4f1000007d7624ffd324ff1b8f, 0x1084208182121, 0x10153f2407d17e0edf7e4976316f76, 0x1084208182121,
      0x104d970edf97116f7e10e9f000a70dff, 0x8442081821a1, 0x10e9f790e9f7de67d541301313a50e428, 0x1d37e8c0e9f100f0100f2e8f000240a8, 0x1a47d93130b1326a50e4001b8f97ac97, 0x1013a7280eff24240024cfa8d879d87d,
      0x1160effb524005154343435484575713, 0x15314bf65d3432c6f430840026026263f, 0x10539300089490004f4040e0f160b500, 0x143434354840ebf0ebf13013a72802424, 0x1438984113fcb26026263f000240f8c8, 0x10eff1e4f2400eab6430643f8d343d4,
      0x128015434343bd844bdf57b40b4a7145f, 0x10912cf097dd77d541301313a50ddfe4, 0x12c6f4308400000263f180effd7240a8, 0x1167d07d01301326a51f4fe4150d343, 0x1f40c9f172f0000024fffba8a4145f, 0x101e4f24024ff1e1f000116f49000c9f,
      0x1280c8434343bd84260f0ebf000a7145f, 0x10912cf097d5e7d541301313a539efe4, 0x143116f841edfcbb40b4263f000240a8, 0x1087d4e7d9c13c31326a50e400d343d4, 0x1eaa84312cf43a8a419ef] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 6) (a := [0x15e6f]) (b := []) (by decide) ?_
    decide +kernel

private theorem vb3_6 : nb3_6.Valid :=
  SearchNode.cover12 nb3_6 (by decide) rfl
    checkedBranches1.vb3_6_0 checkedBranches1.vb3_6_1 checkedBranches1.vb3_6_2 checkedBranches1.vb3_6_3 checkedBranches1.vb3_6_4 checkedBranches1.vb3_6_5 checkedBranches1.vb3_6_6 checkedBranches1.vb3_6_7 checkedBranches1.vb3_6_8 checkedBranches1.vb3_6_9 checkedBranches1.vb3_6_10 checkedBranches1.vb3_6_11

private theorem tv_b3_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨1, 1, false⟩, none, none, none, none⟩ false 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_6

private theorem vb3_8 : nb3_8.Valid :=
  SearchNode.cover16 nb3_8 (by decide) rfl
    checkedBranches1.vb3_8_0 checkedBranches1.vb3_8_1 checkedBranches1.vb3_8_2 checkedBranches1.vb3_8_3 checkedBranches1.vb3_8_4 checkedBranches1.vb3_8_5 checkedBranches1.vb3_8_6 checkedBranches1.vb3_8_7 checkedBranches1.vb3_8_8 checkedBranches1.vb3_8_9 checkedBranches1.vb3_8_10 checkedBranches1.vb3_8_11 checkedBranches1.vb3_8_12 checkedBranches1.vb3_8_13 checkedBranches1.vb3_8_14 checkedBranches1.vb3_8_15

private theorem tv_b3_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_8

private theorem vb3_9 : nb3_9.Valid :=
  SearchNode.cover16 nb3_9 (by decide) rfl
    checkedBranches1.vb3_9_0 checkedBranches1.vb3_9_1 checkedBranches1.vb3_9_2 checkedBranches1.vb3_9_3 checkedBranches1.vb3_9_4 checkedBranches1.vb3_9_5 checkedBranches1.vb3_9_6 checkedBranches1.vb3_9_7 checkedBranches1.vb3_9_8 checkedBranches1.vb3_9_9 checkedBranches1.vb3_9_10 checkedBranches1.vb3_9_11 checkedBranches1.vb3_9_12 checkedBranches1.vb3_9_13 checkedBranches1.vb3_9_14 checkedBranches1.vb3_9_15

private theorem tv_b3_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 0, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_9

private theorem vb3_10_15 : nb3_10_15.Valid :=
  SearchNode.cover16 nb3_10_15 (by decide) rfl
    checkedBranches1.vb3_10_15_0 checkedBranches1.vb3_10_15_1 checkedBranches1.vb3_10_15_2 checkedBranches1.vb3_10_15_3 checkedBranches1.vb3_10_15_4 checkedBranches1.vb3_10_15_5 checkedBranches1.vb3_10_15_6 checkedBranches1.vb3_10_15_7 checkedBranches1.vb3_10_15_8 checkedBranches1.vb3_10_15_9 checkedBranches1.vb3_10_15_10 checkedBranches1.vb3_10_15_11 checkedBranches1.vb3_10_15_12 checkedBranches1.vb3_10_15_13 checkedBranches1.vb3_10_15_14 checkedBranches1.vb3_10_15_15

private theorem vb3_10 : nb3_10.Valid :=
  SearchNode.cover16 nb3_10 (by decide) rfl
    checkedBranches1.vb3_10_0 checkedBranches1.vb3_10_1 checkedBranches1.vb3_10_2 checkedBranches1.vb3_10_3 checkedBranches1.vb3_10_4 checkedBranches1.vb3_10_5 checkedBranches1.vb3_10_6 checkedBranches1.vb3_10_7 checkedBranches1.vb3_10_8 checkedBranches1.vb3_10_9 checkedBranches1.vb3_10_10 checkedBranches1.vb3_10_11 checkedBranches1.vb3_10_12 checkedBranches1.vb3_10_13 checkedBranches1.vb3_10_14 vb3_10_15

private theorem tv_b3_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_10

private theorem vb3_11 : nb3_11.Valid :=
  SearchNode.cover16 nb3_11 (by decide) rfl
    checkedBranches1.vb3_11_0 checkedBranches1.vb3_11_1 checkedBranches1.vb3_11_2 checkedBranches1.vb3_11_3 checkedBranches1.vb3_11_4 checkedBranches1.vb3_11_5 checkedBranches1.vb3_11_6 checkedBranches1.vb3_11_7 checkedBranches1.vb3_11_8 checkedBranches1.vb3_11_9 checkedBranches1.vb3_11_10 checkedBranches1.vb3_11_11 checkedBranches1.vb3_11_12 checkedBranches1.vb3_11_13 checkedBranches1.vb3_11_14 checkedBranches1.vb3_11_15

private theorem tv_b3_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, some ⟨2, 1, true⟩, none, none, none, none⟩ true 104 ⟨3, 129, ⟨1, [], 1, []⟩⟩ [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb3_11

private theorem tv_b3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none, none, none⟩ false 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 1) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨1, [], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨0, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBranches1.tv_b3_0
  · exact checkedBranches1.tv_b3_1
  · exact checkedBranches1.tv_b3_2
  · exact checkedBranches1.tv_b3_3
  · exact checkedBranches1.tv_b3_4
  · exact checkedBranches1.tv_b3_5
  · exact tv_b3_6
  · exact checkedBranches1.tv_b3_7
  · exact tv_b3_8
  · exact tv_b3_9
  · exact tv_b3_10
  · exact tv_b3_11

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_branch (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (q' : State) (hq' : q' = 0 ∨ q' = 1)
    (hM10 : M 1 0 = some (some q', Stmt.write 1 Dir.left)) : False := by
  let m : Move := ⟨q', 1, true⟩
  have hm_cmd : M 1 0 = m.command := hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
  rcases hq' with rfl | rfl
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
    exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) := usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    exact checkedBranches1.tv_b7 M hG hm1 rfl hv (fun _ => ⟨h01_1, hprev01⟩)

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H1 := by
  intro M hFirst second hRun _hUsed hForm hMissing hLoop hHalts
  have hG : GoodMachine M := ⟨hRun, hForm, hMissing, hLoop, hHalts⟩
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1, 0, false⟩ rfl
  have hv : HistValid M [h1, h0] := by
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl
    · exact ⟨by decide, hrun1⟩
    · exact ⟨by decide, rfl⟩
  obtain ⟨q', hOld, hM10⟩ := second
  exact solve_branch M hG hm0 hv q' hOld hM10

end OMA.BB4H1

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H1 := OMA.BB4H1.h1_proof
