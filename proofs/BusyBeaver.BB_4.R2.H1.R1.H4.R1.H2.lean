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

private def nb11_0 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_4 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_8 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_12 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_12_6 : SearchNode := nb11_12.atMove 6

private def nb11_13 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_13_2 : SearchNode := nb11_13.atMove 2

private structure BranchChecks1 : Prop where
  vb11_0_0 : (nb11_0.atMove 0).Valid
  vb11_0_1 : (nb11_0.atMove 1).Valid
  vb11_0_2 : (nb11_0.atMove 2).Valid
  vb11_0_3 : (nb11_0.atMove 3).Valid
  vb11_0_4 : (nb11_0.atMove 4).Valid
  vb11_0_5 : (nb11_0.atMove 5).Valid
  vb11_0_6 : (nb11_0.atMove 6).Valid
  vb11_0_7 : (nb11_0.atMove 7).Valid
  vb11_0_8 : (nb11_0.atMove 8).Valid
  vb11_0_9 : (nb11_0.atMove 9).Valid
  vb11_0_10 : (nb11_0.atMove 10).Valid
  vb11_0_11 : (nb11_0.atMove 11).Valid
  vb11_0_12 : (nb11_0.atMove 12).Valid
  vb11_0_13 : (nb11_0.atMove 13).Valid
  vb11_0_14 : (nb11_0.atMove 14).Valid
  vb11_0_15 : (nb11_0.atMove 15).Valid
  tv_b11_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb11_4_0 : (nb11_4.atMove 0).Valid
  vb11_4_1 : (nb11_4.atMove 1).Valid
  vb11_4_2 : (nb11_4.atMove 2).Valid
  vb11_4_3 : (nb11_4.atMove 3).Valid
  vb11_4_4 : (nb11_4.atMove 4).Valid
  vb11_4_5 : (nb11_4.atMove 5).Valid
  vb11_4_6 : (nb11_4.atMove 6).Valid
  vb11_4_7 : (nb11_4.atMove 7).Valid
  vb11_4_8 : (nb11_4.atMove 8).Valid
  vb11_4_9 : (nb11_4.atMove 9).Valid
  vb11_4_10 : (nb11_4.atMove 10).Valid
  vb11_4_11 : (nb11_4.atMove 11).Valid
  vb11_4_12 : (nb11_4.atMove 12).Valid
  vb11_4_13 : (nb11_4.atMove 13).Valid
  vb11_4_14 : (nb11_4.atMove 14).Valid
  vb11_4_15 : (nb11_4.atMove 15).Valid
  tv_b11_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb11_8_0 : (nb11_8.atMove 0).Valid
  vb11_8_1 : (nb11_8.atMove 1).Valid
  vb11_8_2 : (nb11_8.atMove 2).Valid
  vb11_8_3 : (nb11_8.atMove 3).Valid
  vb11_8_4 : (nb11_8.atMove 4).Valid
  vb11_8_5 : (nb11_8.atMove 5).Valid
  vb11_8_6 : (nb11_8.atMove 6).Valid
  vb11_8_7 : (nb11_8.atMove 7).Valid
  vb11_8_8 : (nb11_8.atMove 8).Valid
  vb11_8_9 : (nb11_8.atMove 9).Valid
  vb11_8_10 : (nb11_8.atMove 10).Valid
  vb11_8_11 : (nb11_8.atMove 11).Valid
  vb11_8_12 : (nb11_8.atMove 12).Valid
  vb11_8_13 : (nb11_8.atMove 13).Valid
  vb11_8_14 : (nb11_8.atMove 14).Valid
  vb11_8_15 : (nb11_8.atMove 15).Valid
  tv_b11_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb11_12_0 : (nb11_12.atMove 0).Valid
  vb11_12_1 : (nb11_12.atMove 1).Valid
  vb11_12_2 : (nb11_12.atMove 2).Valid
  vb11_12_3 : (nb11_12.atMove 3).Valid
  vb11_12_4 : (nb11_12.atMove 4).Valid
  vb11_12_5 : (nb11_12.atMove 5).Valid
  vb11_12_6_0 : (nb11_12_6.atMove 0).Valid
  vb11_12_6_1 : (nb11_12_6.atMove 1).Valid
  vb11_12_6_2 : (nb11_12_6.atMove 2).Valid
  vb11_12_6_3 : (nb11_12_6.atMove 3).Valid
  vb11_12_6_4 : (nb11_12_6.atMove 4).Valid
  vb11_12_6_5 : (nb11_12_6.atMove 5).Valid
  vb11_12_6_6 : (nb11_12_6.atMove 6).Valid
  vb11_12_6_7 : (nb11_12_6.atMove 7).Valid
  vb11_12_6_8 : (nb11_12_6.atMove 8).Valid
  vb11_12_6_9 : (nb11_12_6.atMove 9).Valid
  vb11_12_6_10 : (nb11_12_6.atMove 10).Valid
  vb11_12_6_11 : (nb11_12_6.atMove 11).Valid
  vb11_12_6_12 : (nb11_12_6.atMove 12).Valid
  vb11_12_6_13 : (nb11_12_6.atMove 13).Valid
  vb11_12_6_14 : (nb11_12_6.atMove 14).Valid
  vb11_12_6_15 : (nb11_12_6.atMove 15).Valid
  vb11_12_7 : (nb11_12.atMove 7).Valid
  vb11_12_8 : (nb11_12.atMove 8).Valid
  vb11_12_9 : (nb11_12.atMove 9).Valid
  vb11_12_10 : (nb11_12.atMove 10).Valid
  vb11_12_11 : (nb11_12.atMove 11).Valid
  vb11_12_12 : (nb11_12.atMove 12).Valid
  vb11_12_13 : (nb11_12.atMove 13).Valid
  vb11_12_14 : (nb11_12.atMove 14).Valid
  vb11_12_15 : (nb11_12.atMove 15).Valid
  vb11_13_0 : (nb11_13.atMove 0).Valid
  vb11_13_1 : (nb11_13.atMove 1).Valid
  vb11_13_2_0 : (nb11_13_2.atMove 0).Valid
  vb11_13_2_1 : (nb11_13_2.atMove 1).Valid
  vb11_13_2_2 : (nb11_13_2.atMove 2).Valid
  vb11_13_2_3 : (nb11_13_2.atMove 3).Valid
  vb11_13_2_4 : (nb11_13_2.atMove 4).Valid
  vb11_13_2_5 : (nb11_13_2.atMove 5).Valid
  vb11_13_2_6 : (nb11_13_2.atMove 6).Valid
  vb11_13_2_7 : (nb11_13_2.atMove 7).Valid
  vb11_13_2_8 : (nb11_13_2.atMove 8).Valid
  vb11_13_2_9 : (nb11_13_2.atMove 9).Valid
  vb11_13_2_10 : (nb11_13_2.atMove 10).Valid
  vb11_13_2_11 : (nb11_13_2.atMove 11).Valid
  vb11_13_2_12 : (nb11_13_2.atMove 12).Valid
  vb11_13_2_13 : (nb11_13_2.atMove 13).Valid
  vb11_13_2_14 : (nb11_13_2.atMove 14).Valid
  vb11_13_2_15 : (nb11_13_2.atMove 15).Valid
  vb11_13_3 : (nb11_13.atMove 3).Valid
  vb11_13_4 : (nb11_13.atMove 4).Valid
  vb11_13_5 : (nb11_13.atMove 5).Valid
  vb11_13_6 : (nb11_13.atMove 6).Valid
  vb11_13_7 : (nb11_13.atMove 7).Valid
  vb11_13_8 : (nb11_13.atMove 8).Valid
  vb11_13_9 : (nb11_13.atMove 9).Valid
  vb11_13_10 : (nb11_13.atMove 10).Valid
  vb11_13_11 : (nb11_13.atMove 11).Valid
  vb11_13_12 : (nb11_13.atMove 12).Valid
  vb11_13_13 : (nb11_13.atMove 13).Valid
  vb11_13_14 : (nb11_13.atMove 14).Valid
  vb11_13_15 : (nb11_13.atMove 15).Valid

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem checkedBranches1 : BranchChecks1 := by
  constructor
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x133163f94d594111c70c5aa0c8585850, 0x2101044210860, 0x2100844210860, 0x2101044210860, 0x10000055333333117737383222013383, 0x2101044210860,
      0x504044210860, 0x1207407401c55055066e5020af833983, 0x10e50000000000c333033d617937312e7, 0x504044210860, 0x123232300cff232323c5740740000f40, 0x10002b00e3c6e3093193000e703434e8,
      0x10004400100800820024020100810002100084da2, 0x16c209f0caf0e0e0e2d0d9d96b191919, 0x1ed230523047644764380303036c0dbf, 0x102b016e367e3040042589fbb5e705334, 0x19be3023b82304764476465032403530, 0x1b6341c2f129fff70450454602987a9e3,
      0x218002408021, 0x173a92e72000000e30e3093b793000e70, 0x1030303003114f17114f0033033c3093, 0x194000c700367a41533352220d6d5b3a3, 0x1d5b3a3030303064001c00338333094d5, 0x1d819126fc706474a47474352220e8f0,
      0x1ed2605b8074177495008300e8f94d594, 0x12b00016067004f4042589fbb5e705327, 0x1d33333333522213013b3a3030303053, 0x16503303316215296096b326032603054, 0x1047d34343433522213013b3a30303030, 0x1472b434443020296096b326032603] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x145029454545ad12a8746e39be300d2f0, 0x2101044210860, 0x100090094b1919190111f111f3acc4545, 0x145000004b191919ad111f2a3a0454545, 0x1107f00090090190f5f1900993a1b450, 0x1c700d2f0000d80f5f019adce2a001cb,
      0x28000a000800820020804400100802020080da2, 0x17302220294545450dbad573d3ba0f5f, 0x1e502b453945000005533333300eef73, 0x1033c3ba07302e7207407401c55055008, 0x174074000e62500e5f42b000000002533, 0x10303030380303035a593434a42323230,
      0x16603030301463146335222054b3b384, 0x1b38403750301463146335222054d5b3, 0x100d5a466750750063063942732054d3, 0x1d534a42368230157f14014007315bf73, 0x122205454b3840303030b60354035a59, 0x1000352225a54d5b30030303006306335,
      0x1750063063942372054d3b38403750300, 0x12e10000015bf370375aa4d500750d9f, 0x2101842310860, 0x15e7f1570884688bc0ceffd6afcc43a3f, 0x1358130007d4c001f5304d5c80f31e6010230004bf09ab9f3003cfcc00f30f307983cc07987981e6314c4, 0x1186f000ecf0000001f6f6f6bc1bcfc0,
      0x3db3000f6cc001f5303e2c80f31e6010230004bf099c6f3003cfcc00f30f307983cc07987981e6314c4, 0x1358130007d4c001f5304d5c80f31e6010230004bf09ab9f3003cfcc00f30f307983cc07987981e6314c4, 0x11acf57000000f7f1214f14ff0cefbc6a, 0x1e6f30079bcc00f3f307b0ae11160000f307985b288d31f079bea6000f30f307983cc07987981e6314c4, 0x1bb261f00000154ff60f6460000298f, 0x122200300009700130f0cefca6a001aaf,
      0x1763333330553333330ccf0eef7373c3, 0x133333309544954478e3e3e3011df5656, 0x11a3309544954478e3e3e3011dfa6561e, 0x11e001a0044044b9e345e300c456c833, 0x1a673c32e72003950950019d44500a607, 0x111df11df56c833333302533783317af1,
      0x2101044210860, 0x111dfa6560333333004404478e3e3e30, 0x1e300c45676330330000078e3e3e317af, 0x12905b17af07a6001cb1a00440440e329, 0x28000a000800820020804400100802020080da2, 0x1330ccf377373c3222023232300000d4,
      0x1ad12a8746e39be305934340000553333, 0x504044210860, 0x1b300303030380303035a05a02945045, 0x154d5b3003030301463146335222054b3, 0x12e320540b30037503014631463352220, 0x114a40e30e300d5007507508463d36394,
      0x1553333330ccf0eef7373c3222001466, 0x13333080eef0873c322200d5f1a333333, 0x108e5279fc31aaf3957003333335533, 0x146e39be306606601c5d1d5f10af0ccf, 0x11fbf0f8da03a03a2945d945ad02a87, 0x1038000106fcd0cd1ad02a2b7f460146f,
      0x202418c4718e1, 0x11befae0fffae173f00e6f1eb0197f98, 0x20441084410a1, 0x133333300eef7373022200e4f380009e, 0x133f6330007302189f2047c344444455, 0x1a673c32f320236823047ac4409440f7f,
      0x154d5b3f403030303400009333033ad37, 0x10d37d573f4750f5f750590000352220d, 0x133c33303707302f320030a400290450, 0x122205454b300303030b603043e34393, 0x11c331533008e5730239203c63696335, 0x1d363942f420540b30037503074437443,
      0x1200746674f405a02500e50000008463, 0x1132f1003303325339b33ad0a673c32e7, 0x2014042440421, 0x1202000007c07c139f14df06d0c3f990, 0x1139f5700330330330330d1f06a73c3, 0x16606607c00fff11af0ccf0e5fcc31aaf,
      0x10dad300029045450d0d573f400f5fc70, 0x15e8f0000096096450d0e573f40fac7, 0x10270000cd0cd117fad02a269f460146f, 0x101bef0ae0fff0d1f0a6fcc40234f1e2f, 0x102e102b190190f402500e5000000e600, 0x20441084410a1,
      0x10d50000c700000880885c18df06afcc4, 0x19645000000fac7047d34409440c30450, 0x1472b44142f4496c3] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x133cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1f30f303434b623232300c8f0c8f0c8f0, 0x1878729e3e3e30008900e3d6e30841840, 0x10080400100800820020804020804002100084da2, 0x15938030303bc1bbc171f5b454545a90, 0x1be676778e3e3e37e05656d63333330f8, 0x13a3a0454545068013af13aff80d1f,
      0x156c3f30f3068008b8b4b1919197e185f, 0x148b3b3f4030303000890001919001bdf, 0x11901d93a045107f4500a3a3a3352220, 0x10004400100800820020804020804002100084da2, 0x1204873b3003750300140f010d9f19d9, 0x2021050840960,
      0x1001d8fa9000010c7f9b00a30a3d3225, 0x799e601e679803ccfa9800097e0000f30f305b20f307980799e601e61e6003cfcc007a73001e9fd164, 0x1e300f9f5656c43333330200bd111fdd, 0x1970f9f565603333330200676778e3e3, 0x117bf48b3b30030303001676778e3e3e3, 0x1024060840960,
      0x128320480b300375030ed0a3a3a335222, 0x1660661900152f560f37bf300a389a3d3, 0x15b454545290878746e3e3e3022200000, 0x1000000eff115f9b07373bc0d8fbc171f, 0x10080eef55333333250c8bdc84919019, 0x1226fc8bdc8490137f01013ace0115f9b,
      0x4280044210a1, 0x4280044210a1, 0x117cf121f17cf121f291f85858508] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1b50e0f053feb61058a00c8f149f0c8f0, 0x1e60f3445800097e00025f800111600016c80003cc88ce60222c0003cc8127307b660007983cc1e612ec4, 0x124242453008901657d6570484048400, 0x17302b52005b800cdf13aff826f85965, 0x1c30b50e0f0083898316331533042504, 0x1b3f403030300089016fb9898040043b,
      0x1b3260326030530a3a3a335222134813, 0x13bc40151502530a30a3d32252044804, 0x103030306520067673d575757b40f9fb4, 0x1260326030ed0a3a3a335222134813b30, 0x13b0c9f00c9f000a389a3d328320480b3, 0x115ff858e850cdf00006606698b40b4,
      0x117cf121f17cf121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1030303034b623682300c8f228f0c8f0, 0x10000f30f3079547976352220b0d5b3f4, 0x10b0d573f475297500840840e3196fe30, 0x120b0d5b3003030300379a47929250450, 0x125330330b0d500752975003054003522, 0x167be78e3e3e300056c433333300a4055,
      0x1f6f6f61b5f06afc46321f0ecf570167, 0x218050400421, 0x1466c154f130f0597abc7a0ebf0f7f, 0x17a5a7a17bf5c01fff01b5f06a0c3f, 0x194d5940750750157faa27858585013af, 0x1057880880c402e150e50e50033b9330,
      0x1680da0d0fda340cff2323232a12a0057, 0x4281044110a1, 0x106700e6e377e300f9f16ff5603336330, 0x1030303006700019000000c3f30f3068, 0x10f43313300a3a3a33522204887b3f4, 0x10004400100800820020804201008002200088da2,
      0x1b300375030067010d9f35035011c8f, 0x10004400100800820020804021008002200088da2, 0x2021050840960, 0x11d3f56f400000a30a3d32252048152f, 0x10e8f0e205f0e0200000a4137f000f9f, 0x109b0200000137f0c7f137f048af017ef,
      0x103030010fdf16dfa90d9f04b0000461, 0x224860940960, 0x1024060840960, 0x13a000000a3a3a33522204887b3003, 0x1f4037503000124f003526af3507a1c8f, 0x1000003303300a30ccfa3d328320480b3,
      0x1290458746e39be300d2f0067000a400, 0x1f30157f34270d2f1a6f11a6f0045045, 0x228002408021, 0x1880c412e0000000e30e3d6841840f34a, 0x10004402100800820020804021008002200088da2, 0x1eabf1e607982046000fa984366e60079f983ea603ccf3003ccf301e679faf0b66e6003cc03cde60f6a45,
      0x134343323232301fef11fef00000885c, 0x4281044110a1, 0x1e3234023682303305900380303030e3, 0x1330332507873c32e72005900003203b6, 0x10329034340e8f2323230296f0296f00, 0x10cd0cd146329f146f004c594c0380303,
      0x8040201100044004040101004040041001029a3, 0x1b605434a423682304c183f4c00354f0, 0x1cd106f46409f146f004c594c0003003, 0x1030308585850854c134f4c00000cd99, 0x10157faae6108f15333522200d5b3d303, 0x102e1500370e3c3339333017a67302f32,
      0x10cff23232300189ff6885788570000c4, 0x1f63d57575700a63bc41151500d0f2403, 0x1e60f30798002046000811800097e0000f30f303cc88b0002046000408c3cc003db30007b66001edaab64, 0x1450008746e39be300d2f085e63ebff6, 0x1d573d300c700d2f1c2f1151f4b294545, 0x1084060840960,
      0x1030943434a42323230001c000454500, 0x1094d53402368230157f0593535380303, 0x1880885c0000c402e10059035b6039303, 0x904800088b000222c799e611160000f307985b216c87980f31e603cc3cc007a730007b66001edaaec4, 0x133330b97373c322200318df012ff103f, 0x1783300073c32e7200300eef78785533,
      0x10309434340232323017af10f7f782533, 0x1084060840960, 0x194034a423682300e4f5a593535380303, 0x10000c43a3f2e105a591c35b60354030, 0x294860940960, 0x185850121f0ceffd12ff103f884688bc,
      0x1108f747435222990d5b3d3030303085, 0x194749403303300d500750750157faa74, 0x19709e00cef06a143fce0f2fbb1a8f074, 0x1470d0f47470cff232323e9cae9130f, 0x10990d573d3ceebc700d2f9b0d2f0121f, 0x1038703434a42323230740774e946045,
      0x10d53402368230157f14591414380303, 0x10c3fce1e0fbb261f0b659000030036c, 0x12323230e9cae9130f9701fff00cef06a, 0x173c32220145914143803030345034340, 0x1332368230950eef9595553333330073, 0x1a6000d8fcb1a0b659219450320300034,
      0x1475947146907695bd44504517af0] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13bc311afb50e0f02705b80149f1f8f0, 0x1b3f4030303089fb140af16098004004, 0x298250442521, 0x1004b326032603053a32223522213013, 0x122213013b30030303053d3202020204, 0x1003d575757b40b43bc4015150a322235,
      0x1265d32332162152000b3260326030670, 0x135bf29ef5757570003bc43e8f29ef150, 0x1f4b50e0f00514bf0ed229ef4bff4bef, 0x19c5ebf5eaf1605e9f004267f044c0f93, 0x100001f61f649766d76002e0053a7b689, 0x2012048440421,
      0x2012048440421, 0x10f6f628f5f5f513f613a75702424053, 0x1000f616f515f5d3f6151260262405754, 0x2010850440421, 0x10ebf28f5f5f513013a7c82d4f2424065, 0x10f5d30fb126161f26240f85413ef0ebf,
      0x218050440421, 0x1c5aa278585850f88915df127f4c1f0f5, 0x123c50000133b933163f94d594000c70, 0x2002008440021, 0x1850eaf8500cdf0c3434340cff2323, 0x1000133133b9946a9400fac7053aa0eaf,
      0x20421084410a1, 0x20421084410a1, 0x10650324035325533415230523023530, 0x16606523d25327533516005b8023ed066, 0x10523000000e3b7e3093193000e70ed0, 0x10004400100800820024020100810002100084da2,
      0x193000e70ed000650324035305334023, 0x1532753a389d305b8000000e31e3093c6, 0x3b9aca001ddc4bb2800eea6c2ca0007823ff280077712eca00077712eca0001dcddc359401dcd82cd650861c4680007735b1cd650861c46f7359b7359b735943b9ad8e6b2bb9aca773597b9ad1735a2e6b28003bd664ca0003c11ff94000f224d4a000eea6c2ca000ef5a1236fdda8, 0x1d3030303085858500cdfed000650670, 0x1a92e720c5aaa33333333522213013b3, 0x1232323c50e30e3c33393330fdf17a673,
      0x115cf0101fdb1db0242400c0303030cff, 0x1e60f325f8002046000811800097ef300f30f303cc88b1e6222c0003cc25f8003ea60007980f31e616824, 0x1013a7d3111ff114af116bf0135f00, 0x1e60f30798002046000811800097e0000f30f303cc88b000222c0003cc25f8003ea60007980f31e616824, 0x1e60f30798002046000811800097e0000f30f303cc88b000222c0003cc25f8003ea60007980f31e616824, 0x1e60f30798002046000811800097e0000f30f303cc88b000222c0003cc25f8003ea60007980f31e616824,
      0x1f51300001f6d6f622af76a6760001e2f, 0x20421084410a1, 0x157570baa63bd4101f15150151528f5f5, 0x1230aa0eaf850eaf850546707f6f63d57, 0x12020ed2f526503240353045334a42305, 0x1005b800e30e3c3339333114f176a730,
      0x165232423ed00065275713534953b3a4, 0x12f5265032403531d6f53340230523003, 0x1ed3303365270a35305300d305b8003ed, 0x13522213013b3d30303030858585015ff, 0x19403303300d50000c70c5aaa3434343, 0x185017cf0c6464640cff232323c509483,
      0x124035305334a42305230aa0eaf850eaf, 0x1094033033000000fac70ed6363636503, 0x1270a1365057053053b3a40405b80094, 0x163636503240353053340230523023ed, 0x10dff356520253053001605b8023ed63, 0x117cfed646364ed27] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 5) (a := [0x15ecf]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11f8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1030303038b3b3b315934347523232300, 0x2100884210860, 0x10303014631463357373737754b3b3f3, 0x101463146335737373140f54d5b3e703, 0x1a400630639473273f35475b3003d303, 0x1014014012259f20faf75d575001eaf,
      0x2042008440021, 0x101dd1dd1d2f115cf125f1126f1126f, 0x2101084210860, 0x2101084210860, 0x2101084210860, 0x2101084210860,
      0x2101084210860, 0x10c7f119cf1126f109f1d8f0d6f1d8f, 0x2021084240860, 0x2021084240860, 0x137ff0d6f0102f0102f05d43bf169f, 0x11ebf169f240f221f1d3f0305f0d6f,
      0x101d8f0f0f1d8f0102f0102f0220f169f, 0x1161f00000143bf10c7f109f19cf1126f, 0x2021084240860, 0x2021084240860, 0x2021084240860, 0x10306f147f25af001ecf00270f046df,
      0x1b303b37559683412303230102f0102f, 0x2100884210860, 0x10630633573737305454b3f30303030b6, 0x10000035737373140f54d5b3e70303030, 0x10000630639473273f35475b3003d303, 0x110e10e0000012259f20faf75d5750a4,
      0x902008440021, 0x2101084210860, 0x2101084210860, 0x110f5ff9011ef001ce1115f235fba1ba, 0x2101084210860, 0x2101084210860,
      0x2101084210860, 0x501084240860, 0x10f90f9000000d8f210f11ef126f10fcf, 0x501084240860, 0x1eb00003c03c00125f0125f240f0184f0, 0x110df000001210f1126f0d8f0fcf10f5f,
      0x501084240860, 0x501084240860, 0x501084240860, 0x10d2f157f0d2f3c03c000d3f000000000, 0x138b3b3b315934347523232301b31b39c, 0x2101084280860,
      0x2101084280860, 0x504084280860, 0x1631463357373737754b3b3f30303030, 0x16335737373140f54d5b3e7030303014, 0x16394738773f35475b30030030146314, 0x1a41872aef870faf75d575000008463d3,
      0x424084280860, 0x1125f0126f0126f0fac70d5fc70146614, 0x10f8da1126f1126f1dd1dd1d2f115cf, 0x421084280860, 0x421084280860, 0x421084280860,
      0x421084280860, 0x421084280860, 0x11d2f183f0e6f242f1d4f241f14cf46ff, 0x138d538128af1edf1211f241f12ef3dcf, 0x1021084280860, 0x421084280860,
      0x14455565656148f0eef73731a22200e4f, 0x10f7f562a56307f16d730202047c34444, 0x485084280860, 0x1140f54d5b3e7030303023047ac440944, 0x10000faf75d5751212023000035737373, 0x504084210860,
      0x504084210860, 0x1563637f37302020b3755968340a40361, 0x504084210860, 0x15454b3f30303030b6b314387439356c3, 0x424084280860, 0x1e5732e239203c6369633573737314ef,
      0x1b30030030744374431c56a656182f08, 0x111e51101008463d3639473f473f35475, 0x8000a00028000c00028010200410000c000201a3, 0x80012000480014000480102004100014000403a3, 0x424084280860, 0x424084280860,
      0x424084280860, 0x100003a00d5c7020200746674f415a125, 0x424084280860, 0x424084280860, 0x111a5f100faf10cf110cf00000d301a, 0x4141544814a1,
      0x814058480421, 0x814058480421, 0x1000960963a00fac702392010248f214f, 0x1014050480421, 0x100102d7f3e6f111ff105dfd1fd000000, 0x4141544814a1,
      0x814058480421, 0x814058480421, 0x1014050480421, 0x1da11bdf11bdf1ce1115f235fba1ba000, 0x421084280860, 0x421084280860,
      0x421084280860, 0x421084280860, 0x421084280860, 0x1195f384f1ce1115f125fba1ba00000, 0x421084280860, 0x421084280860,
      0x421084280860, 0x13e3f1aef109f10cf110cf000001179f, 0x421084280860, 0x421084280860, 0x1110cf000002712d6f30df216f11a5f, 0x421084280860,
      0x421084280860, 0x421084280860, 0x100001341f310f30ff11a5f110faf10cf, 0x821084280860, 0x421084280860, 0x421084280860,
      0x421084280860, 0x102bd92d5fd91f4125167f15dfe515df0, 0x441084280860, 0x441084280860, 0x1011bcf382f1d7f111ff115dfd1fd0000, 0x421084280860,
      0x821084280860, 0x421084280860, 0x421084280860, 0x421084280860, 0x147d34409441c313a0faf0fcfd5c70000, 0x481084280860,
      0x481084280860, 0x144142f4496c3963a5d0fcffac700000, 0x1472b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x133cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x103030013af13af0d2f0c8f0c8f0c8f0, 0x145450f3a3a3a335737373048b3b3f303, 0x108b8b4bd9d9d97e185f3a3a0cbf45, 0x100a30a3d37327304875b300320300cbf, 0x106767788787877e0f9f565677333333, 0x1210f210fa9119b126f00c7f006816877,
      0x2021090880960, 0x421090880960, 0x421090880960, 0x1454545073343f0e1fbd111fdd1bdf, 0x1249f8b8b4bd9d9d97e185f3a3a0cbf, 0x1878787970f9f5656773333330730cbf,
      0x1737317bf48b3b3f30303030771676778, 0x1024090880960, 0x1737e4875b30030030edf3a3a3a33573, 0x188567733333300cbfa389a3d37383, 0x11a2220770e1f195f6778878787880f9f, 0x149d9115fd910eff19bba0115f007373,
      0x421090880960, 0x421090880960, 0x1aa0876080eef5556565625235fc8bdc8, 0x117cf121f17cf121f291faaaa] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10303000cdf13af0eaf0c8f149f0c8f0, 0x1030050a3a3a335737373134813b3e703, 0x1b8260a30a3d373273264826b3fb03b5, 0x18389831656b45604250473fb2b52053, 0x173134813b3e70303030657313735379, 0x1264826b30030030ed79a3a3a3357373,
      0x1b4b4100f0d71a8f07aa389a3d3738373, 0x10cdf1e239f116f10ef181a5f583db488, 0x117cf121f17cf121f15ffaac5aa] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1d5750940940157faab885858500c8f0, 0x100fcc402e08808815000390056056075, 0x10d0f0d5f230cff343434113fd8105f00, 0x114cf10000c3f990132f17c2dff7cf60, 0x218050440421, 0x218050440421,
      0x14609b8729e345e302300c8f113f17ff, 0x1e7732529b2023173f1139f0f5f03a03a, 0x218002408021, 0x10d2f157f0d2f17af1132f9b056056c30, 0x218002408021, 0x114df9c1caf197f0000c49c2e08808800,
      0x10059e7f338b3b3b30f33434752323230, 0x10139f0f5f03a03a4609b8729e3d9e3, 0x1590f30b373b30f36834b62373230173f, 0x10ad0132f9b056056c30e77325278200, 0x15a59e7f338b3b3b3460343475232323, 0x15a592ef30b30b3a406834b62354230fa,
      0x1fd1caf197f0000c402e1884688bc0, 0x218050440421, 0x17304887b3f303030300228f13af0cef, 0x1135001c8f00f31f30f3a3a3a3357373, 0x10002400100402200084080201000402200088522, 0x10002400100402200084080201000402200088522,
      0x1d37327304875b3003330300f30f3135, 0x10002400100402600084080201010002200088522, 0x168f36800000a400000003303300a30a3, 0x1114f0effadd9ad1d2fc3f377f300000, 0x1a90d9f14b46119b00000731730ccf67, 0x10002400100402200084080201010002400088522,
      0x1425090a80960, 0x425090a80960, 0x1425090a80960, 0x10f0f4887b3f30303030155f10fdf16df, 0x1024090880960, 0x17a1c8f3a0f30f30f3a3a3a335737373,
      0x175b30030030295ff3124ff313513599, 0x1425090a80960, 0x1025090880960, 0x156000000da30ccfa3d3738373f448, 0x16716af0e1f141fa4497fd9990f9f207f, 0x129357373730b0d5b3e70303030230ad,
      0x102900b75d5752522920230dcf540dcf, 0x1f30cbff30000068340dcfa40dcf3625, 0x1e70303030b3b6d6842c0f8418718777, 0x4a5090a80960, 0x4a5090a80960, 0x100b30dcf540dcf29357373730b36d5b3,
      0x1a40dcf55255629560b75d57525029, 0x1d934efd62c2fd61cdf02c1f000dcf, 0x1590dcf393f0c6f229f0c6f1cdfd92c1f, 0x12e100015075157faab88585850aa0dcf, 0x481090880960, 0x13434113fd86d50ef883f2f88fcc4198f,
      0x199134f132f1000f600d0fd5b30cff34, 0x4a5090a80960, 0x12300aa113f17ff12ef17c2dff7c0c3f, 0x1084090880960, 0x10e30059353538b3b3b30943434752323, 0x12301c2f0151f4b293a453a4609b870e3,
      0x102020059035b6b303b3094683402303, 0x1157f0d2fad00f7f7825569b56c30e773, 0x1103f8838ff885cc49c2e1000000d2f, 0x481090880960, 0x13ad93a4619b870e30e30b318df9c12ff, 0x4a5090a80960,
      0x17856c31e77302020b31c2f1151f4b29, 0x1084090880960, 0x4a5090a80960, 0x14694343475232323017af10f7f782556, 0x1084090880960, 0x1683402302300e4f5a59353538b3b3b3,
      0x11bcf2e1000005a591c35b6b354b3a494, 0x4a5090a80960, 0x1850121f0ceffd12ff103f884688bcc4, 0x1561560faf75d57500000157faab88585, 0x4a5090a80960, 0x1470d0f47470cff343434c4749474941,
      0x4a5090a80960, 0x11438b3b3b3e3034347523232300121f, 0x14bd9d9d9ad02a3a0f5f4545450145914, 0x10b30b3206834e323032303c111f3c3c, 0x102d0ad0d8fa61ad4e32de30b6590345, 0x123230c40d2f157f0d2f690769107fa9,
      0x14501459141438b3b3b33af334347523, 0x13c3c4bd9d9d9ad2d8f2a3a0f5f4545, 0x1d93ab373b356f3683402302303c111f, 0x13acb3a17af0d8fa61aa90cb00b65973, 0x1475947146907695bd4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x15605600d5c70940940c5aab885858500, 0x10149f0c2323230cff343434c5001a00, 0x1a65600fac709409400eafaa26850585, 0x1b35305334262305230340eaf0000056, 0x153053b826270535034ed0300365b313, 0x1530533426230523023ed00065731373,
      0x1b8262705a3023ed0316ef0365b313b3, 0x10cdf1f8f0eafed21e7f265013053d353, 0x105a30003573737313013b3e703030300, 0x1b826d302007307326026b3fb03b5030, 0x13573737313b913b3e70303030532753, 0x173b47326b926b3003003013a3d979d9,
      0x129194f9b101f018af0065d3d956d916, 0x10d700db97124f97101fd918afd918af, 0x15a1ee6184b3f580c3fb488b4fb100f, 0x197f7971d915cfd9db29ec9b00000116f, 0x1024090880960, 0x11a2d0136f00c5aab885858500cdfedcb,
      0x13434c5a9d95bd92dd6136fd60fdf07a6, 0x15334262305230850c50cb3b3b30cff34, 0x1b826030503085ed7307365b313b353b5, 0x11a000000eafaaed000652713e753053, 0x10eafadd9400fd923bfd6322fd6ad072e, 0x1b3531d6f5334262305230b365341334,
      0x1d353b82600500b3ed7316ef7365b313, 0x1858585015ffed56213f56652713a353, 0x10f0f560e8f07d5c7eb00f0f00c5aab8, 0x10c6464640cff343434c546948394eb56, 0x165b313b3530533426230523085017cf, 0x1013053fb53b826030503085ed636363,
      0x19907fac7000000eafaaed27127fe765, 0x105230340eafc4940f0f940e8f56a656, 0x10034ed63636365b313b3530a53342623, 0x1ed270dff3565731373531653b826005, 0x117cfed646364] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 5) (a := [0x150ff]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1fd1fd10c7f10c7f0c5aa0c8585850, 0x2101104210860, 0x2101104210860, 0x2101104210860, 0x1121cf5d02aef00111ff169f125f28ef, 0x2101104210860,
      0x501104240860, 0x105d05d00000169f2acf1eef126f119cf, 0x501104240860, 0x10102f00169f6e6f169f4b6f01d3f0, 0x11126f109f19cf121cf0f0f0000102f, 0x501104240860,
      0xd031046408e0, 0x100147f000000000161f0000012acf, 0x501104240860, 0x134e823232300cff646464c5102f0102f, 0x14b9a9a9a144f1a9f3a3af7454545034, 0x10c4f2d23cfd9d96b19191904d0bbbb,
      0x1386363636c0dbf6c209f0caf0c4f0c4f, 0x163636353265334ed230523047644764, 0x1434300d5b3a303030302304764476465, 0x100c355c7094d59402020230a43923543, 0x12000000070000000450450b6340020af, 0x1114f17114f529fa944e744c309373020,
      0x14ba9099b0946029870e30e3063b863, 0x1430e8f0d5b3a30303030640fdf0151f, 0x10e8f94d594000006474a47474354343, 0x1013b3a303030300741774950f2f055c7, 0x1096b38903b503005d32223543434313, 0x10425890b5005327ed02022643264396,
      0x133028b8532b0100f190f1603de704f4, 0x1030652b00016f43de704004258933b5, 0x1d343434335434343130f0f13b3a30303, 0x12b4344432643264396096b3003003047, 0x147] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x12220354343430b54d5b3330303030230, 0x123920744374435544444429377373e3, 0x120744374431c4444440dcf08e5730ecf, 0x1f400430439344f3440daf37337302c3, 0x1237407400b03de70dcf66e533154f05c, 0x173462220257555750ba4d507c422920,
      0x1e529464639460000055444444293773, 0x1ca73c320207407401c5514ff550dcf08, 0x166e5ca4605cf4000009344f344ca37, 0x168630b59d5347407400b0130f250dcf, 0x13a192f45454505454b3840303030b663, 0x14343373fcc524f0c6f4b9a9a9a7e8b8b,
      0x106061e1f67152f563c3333330633543, 0x130af3a37ef00c7f0063690769697806, 0x10030303069cc693cddd6115fd6166f8b, 0x10f7f0909091b5fbc6a87124fe30ecfe3, 0x1737a2220354343430b54d5b369066906, 0x1737a239207443744355444444293773,
      0x17302020744374431c4444440dcf08e5, 0x17a05c007643c3439344f3441b5f376a, 0x10030747974f40b1e3f3de70dcf66e587, 0x10030f40339344f34403716ff7302332, 0x1033054d3b300000f30f3084084033033, 0x11dbfbe2c0f9cd6063606c467d456033,
      0x144f344073716ff73020206394437543, 0x1f307843acf84000006369f4693c93, 0x12937737302220069be6930bf4af30e7f, 0x144f34403707302332029000055444444, 0x1291b5f5a6aca124f0154f00c3033093, 0x15ce6a6077a00daf0069069a95c01bef,
      0x10257555750ba4d59587958729365b36, 0x195449544780606064a675656ac333333, 0x174091c5514ff550dcf08e5297a03900, 0x144d6063606ba67e6560330330740c4f, 0x1ad130f250dcf66e5c47a05c007644c4, 0x1747974f40b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x133cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1333303434b623232300c8f0c8f0c8f0, 0x1e3e30006767780606067ebe5656d633, 0x163bc0bc171f5b090909a91b878729e3, 0x100f378f30840840330330f859386363, 0x156c43333330030303013af13aff80089, 0x143e648b3b30dc6c6c678060606bbb956,
      0x106113fb987560330330a3a3a3354343, 0x1878746e3e3e30222079c679c6d40636, 0x14425767373bc0bc171f5b09090929ba, 0x14b9b13e13ace0115f00080eef554444, 0x1084110880960, 0x1084110880960,
      0x1121f291f2c2c2c08226fc8bdc84913bf, 0x117cf121f17cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1f927ef125f1ae0058a00c8f149f0c8f0, 0x2014042408421, 0x1532653feb6001010135f197f2d0ff96d, 0x2014058420421, 0x1e60f3445800097e000260733cde6003cc03ccf30088d22c1e607983cc8127307b660007983cc1e612ec4, 0x1048404840125fb5150f85965636363,
      0x10cdf0eaf0cdf13aff8008901603d0e0f, 0x117cf121f17cf121f15ff2c2c2c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1434300d5b3d3030303085858500c8f0, 0x144017073029320157faa0108f3923543, 0x10c800880881500fdf370ecf33c344f3, 0x10cff646464113f0105f217fc4062e06, 0x1132f9a0cc017c2dff7cf600d0f0d5f23, 0x3e2e6603db3000f6cc3cc03ccf3003cde600f4e607b6d9800204603cc7a7307b660007983cc1edaaec4,
      0x1e345e302300c8f113f17ff14cf1999a, 0x1084120840960, 0x173d3250e3023010046099b0901b08729, 0x80402020080082002100404010080022000885a2, 0x1003434a423232302b02b00055c700d5, 0x1d534b6230230157f6659668438636363,
      0x12acf000088088d80059084063686300, 0x107607325278200d2f380d2f0000c402e, 0x16308434340232323000fcf00c344e744, 0x114ff10af00e50c313957005900386363, 0x1e60f3445800097e000222c03ccf3003cde600f300904800222c000408c7a7307b660007983cc1edaeb84, 0x16863084034b6235423066086601c12bf,
      0x10660000000e5fcc30011af005900a463, 0x117937302020157faa27858585013af66, 0x1c88852af0001506a376ae6c344f344d6, 0x1da340cff6464642a12ad8c4062e0688, 0x1004110880960, 0x1834b44f344025073023320030da0d0f,
      0x10f4000f2ff30f3000003303300308333, 0x1834b44f3440d1f25152f7302020b3, 0x1f30d1fb9152f5600000482c9f83152f, 0x1a3d34375431dfff422ff2c6f0f2ff37b, 0x112daf1dff1184f17ef00000a30ccf, 0x424104a80960,
      0x1c2410ce809e0, 0x103434223232300ac0dac4aaf0ccf0f1f, 0x109291b45870e30e3005900386363630, 0x103342523032301a6f01a6f2baf46099b, 0x1560330330157f3427059000636863b60, 0x100001f3f671f3f190fc4063606d6bed4,
      0x11fef11fef190fc412e2acf885c88d80, 0x8c4118c809e0, 0x1084110880960, 0x1c344e74425767873020200d2f380d2f, 0x12984343402323230296f0fcf296f101f, 0x1cd10329f0004c594c13cf38636363,
      0x4a4114a80960, 0x14c183f4c374f46354f146f354fcd202f, 0x1594c13cfa4636863b68454340230230, 0x1460c4f146f0c4fcd99cd106f000004c, 0x1003030302302c228f2c4c134f4c216f, 0x1022920230b541c55354343430b93d5b3,
      0x1f40303030340ba41c0257555750b0d50, 0x102900940b541c55354343430b93d5b3, 0x16368630ba41c29257555750bd6d573f4, 0x1b3d303030308585850121f0b591c35b6, 0x10094157faa74108f74743543434300d5, 0x1970f2f103f1a8f0cef9c6a143fce0bb,
      0x1470d0f47470cff646464e9cae9130f, 0x11438636363e3333434023232300121f, 0x13c4b9a9a9aad9d2a3a04545450145914, 0x1452636863033034023032303c111f3c, 0x1074074e90055c700d573d30000b65903, 0x1145914143863636387563434a4232323,
      0x10dbf766368636cbed5340230230157f, 0x1261f0cef10cf6a0c3fce0bb00b65976, 0x1c30d2f380d2fe9cae9130f971e0f1d7f, 0x147594714] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13543434313013b3d3030303085858500, 0x19b090fdf02a8746e329e30c5aaa3222, 0x10c2323230cff646464c5045045a909, 0x1040043bc311afb5f608505850149f, 0x1265334a42305230aa890101603d0e0f, 0x2014050408421,
      0x10f40000e5000000ed030036563636353, 0x100065028b853053b3a42705130045045, 0x15326533402305230230eaf640eaf64ed, 0x1053002705a3023ed0316ef0365636363, 0x113a7150eff242400ed20265d328b853, 0x1930effb524005540575728434343139e,
      0x10000053a7b6000026432643d3012eff9, 0x114bf53106e7f2a0f1ca10242f496a49, 0x814058480421, 0x814058480421, 0x1014050480421, 0x100c4f16f43d0e0f04060406930b50028,
      0x12843434313224f13a7c802424065890, 0x1432643d34900000240f85400ebf0ebf, 0x1fd1fd00000c5aa278585850f88900026, 0x421104280860, 0x164c51210f1210f111ff169f125f28ef, 0x421104280860,
      0x421104280860, 0x421104280860, 0x1b523052308500cdf0c3434340cff6464, 0x10503085ed00c9f6b6563636353265334, 0x1053aaed00c9f065028b8532753f4c303, 0x13a1f1f1f1f41115f1affb9e5b90000,
      0xc21104280860, 0x421104280860, 0x13a4d45454500eaf640eaf645310d9f, 0x421104280860, 0x1f716df4bafbb4b9a9a9a2ddf1a9f446f, 0x16b6563636353265334100f2305230,
      0x1071123fca1a9f196f3a00000edcb0c9f, 0xc24110e809e0, 0x12753a389005000d1fbb21bf16df262f, 0x112df1f8f0cdfedcb0c9fdb65d328b853, 0x1a34444443543434313013b3003030300, 0x100d34424426432643000b3003b503005,
      0x189000c4f1611af3d0e0f040043bc30b5, 0x14444354343431325ff13b3f40303030, 0x1264326430415df04b3003003053a344, 0x185015ffed44144652728b853d344fb44, 0x840120080860, 0x143433543434313013b3d303030308585,
      0x19b090fdf19cf2a870e30e30c5aaa343, 0x10c6464640cff646464c546092909a909, 0x165636363532653340230523085017cf, 0x1065028b85305300030503085ed636363, 0x16563636353265334a42305230aaed270, 0x12e1a21bf1b0f6a8700000ed636363,
      0x153b3a400500c4b9191f142f0f1f0c4f, 0x1640eaf64ed270a13650428b853242f, 0x117cfed6463640eaf] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 5) (a := [0x152bf]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x15500011773738322200c5aa0c8585850, 0x500a04210860, 0x11c3f373f12e6f34af1194f1194f00000, 0x501204210860, 0x501204210860, 0x501204210860,
      0x10c30330d6179373123320000011c3f0, 0x501204210860, 0x500a04210860, 0x10125f28effd1fd10c7f10c7f000e7, 0x501204210860, 0x501204210860,
      0x501204210860, 0x186e3e3e30163f94d59400f0f05d111ff, 0x501204210860, 0x110100690669065b46464619bf4e8787, 0x212008480021, 0x212008480021,
      0x1e3e3e30950951a10e8fc4eb313f1a6b9, 0x242008480021, 0x242008480021, 0x139830c710060065b4646463e4e4e8786, 0x10080022000820020800804020110002400080da2, 0x10740741a1c550755268f66e5020af83,
      0x100000000701a1000235fd6a6d61e31e3, 0x504204210860, 0x504204210860, 0x504204210860, 0x10b3b3a30303030c57407400007f400e5, 0x11a18ff494a49179fd618ffd66b01d8f0,
      0x1144f19bf17ef17efec0e0e0e0ee01e, 0x1d30f1f138f0f1f2d5fdd2c3f11bf11bf, 0x10013b3a303030301463146335d3d3, 0x11a1c3f49db491e7f7ea6b90f3f0247f, 0x1a303030301463146335d3d3d313ac01e, 0x10156f1a164f4e1d91c4fd61d600000b3,
      0x2211044810a1, 0x2221084810a1, 0x11a164f494a491f9fd61d600000531f, 0x2211044810a1, 0x1bb1e7f2d6f1c4fee13a00000003bcf, 0x2211044810a1,
      0x1063e76335d3d3d327cf02d7f2d5f164f, 0x101eef0f5f164f01b3f1eb0dd0daf0000, 0x284202482121, 0x1939b0126f003434e823232300cff0f2f, 0x1a4d3107f9b02be70f5f49b7492daf931, 0x2211084810a1,
      0x1890b5005334ed23052304764476438d3, 0x1d353100f02be7164915af4904fb0425, 0x10d5b3a303030302304764476465d3a4, 0x1a92136f20231b7fa4392353333330f1f, 0x100b6340dc320afc72d02d00f1f94d594, 0x1a9e3136fe30000e7049049093b793000,
      0x1d3114f07114f1a2d023bf00fdfd6a6d6, 0x107a4070735c4c4c40d6d5b3a30303030, 0x164b864001cc705b05b094d59400000d3, 0x1010bf00fdf109f2a115fd819136f190, 0x13313013b3a3030303003cce3c107f2d, 0x103396096b38903b503005d3222353333,
      0x113b3a3030303053265327ed262262033, 0x10030030a4d3c4c4c435c4c4c413164f, 0x133047b86526c426c416c446c496096b3, 0x1472bf4127fe7160e6004fb04258933b5] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000550000ccf377373c322202323230, 0x109b0290450ad12a875ae35ae30593434, 0x500a04210860, 0x1207443744355c3c3c303773730222046, 0x1022207443744355c3c3c30377373022, 0x1030303038043364355c3c3c319373773,
      0x1003030301463146335c3f4c3054b3b30, 0x1f303d30301463146335c3f4c3054d5b3, 0x1200d50000a40063756394c32c30540b3, 0x11475147502f4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100004b000ad111f2a3a0e4545450e30, 0x1d80019adce2a11ff0e8f19cb190e3, 0x1115cf125f1223f1223f02a87000107f, 0x501204210860, 0x501204210860, 0x501204210860,
      0x1d9d90e9f1919190ad00001dd0dd1d2f, 0x501204210860, 0x10451cdf9a126f9a0cafebebeb2d219f, 0x109a0cafebebeb0219f0d90e9f191919, 0x1eb259f111f111f3acc45454502909a, 0x13a04504509b126f090f5f094beb10df,
      0x1461b090090eb0eb0099] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10e30d1f1a687c415bf289f1902303230, 0x500a04210860, 0x1000d54d5b3f40303030340001a0dafe3, 0x12020d37d573f4a4173f190590000350, 0x1774355c3c3c303773730222007507529, 0x143364355c3c3c3193737730222003043,
      0x1f36335c3f4c3775454b300303030b60, 0x1756394c32c30540b3f303d303068063, 0x1c30f30930330ad37a67302020063] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10e0e0000055000190eef7373e322200, 0x100000dd000173f292f0e6f17ef0c7f0e, 0x1d573d3e30e70250450c3ba3373d42332, 0x100fcf1ce0115f1fdfba1ba10e10e0, 0x501204210860, 0x501204210860,
      0x501204210860, 0x501204210860, 0x1ebeb140f219fd9d99d19191900d00fcf, 0x1223fa6d9d40247f003c9a3c9a0cafeb, 0x10d4e30e30950951a1c3f0c40f0f117f, 0x12b4539450c7290001a0070023bf0a6,
      0x110e0740741a1c5507551caf08e50f5f, 0x504210210860, 0x1f42b00e8f0000001ce0115f0ba0ba00e, 0x504210210860, 0x1744674469900725ebcae5] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1cb377373d422205a593434a42323230, 0x117ef377373e622207443744355c3c3c3, 0x1c3d9373773d422207443744355c3c3c3, 0x154b3b384030303038d943364355c3c3, 0x1b36603030301463146335c3f4c314ef, 0x100300301463146335c3f4c3132f54d5,
      0x1660eb008463756394c373c3f354d3b3, 0x1147514754673f4739907d5a4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1157f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10230000350005a54d5b3330303030230, 0x107507515bf370375aa4d507c420d9f2, 0x14355c3c3c3cb377373d422205a59d534, 0x155c3c3c310ef373773d42220544d4377, 0x1c3775454b3840303030b610ef433643, 0x1f354d3b30030030687763f36335c3f4,
      0x1a48463756394c337c3] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x198000001000bc1bcfc98515f15700, 0x501a02318860, 0x501a02310860, 0x501a02318860, 0x100f7f1014ff0cefbc6a186f189f10ecf, 0x501204208860,
      0x3db3000f6cc001f5304d5e6603cc1e60f30799357bab9f3003cc1e60f37980799e60079bcc01e6314c4, 0x10527f0463a3f112bcf455f189f570000, 0x501a02310860, 0x501a02318860, 0x16a10dfeb4a6fbb98048cf01acf0154f, 0x16afc01aaf0261f9711ff0130f0cefca,
      0x13a3f041bf01bff02e1884688bc0ceffd, 0x3db3000f6cc001f5303e2e66001e7e60f30798f3099c6f3003cfcc00fa98007b660008118001e6314c4, 0x1142f1bcf1f9f1aef1f9f1bbf2f4f274f, 0x1c4224f142f27df] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x15b979797155fdc878746e3e3e302220, 0x110ef17efd901901903773737a07a0ebf, 0x1c3c3eb0e3f0cbf19bf4d192ff92d173f, 0x17443744355c3] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c333333355e3e3e300eef7373022200, 0x1137f0c7f137f173f10e6fd9019019, 0x812008480021, 0x125e345e300073023320eb00f5f0e0daf, 0x1166fd41b1f0d1f1a687c40000033e733, 0x812008480021,
      0x1870ccf0eef7373072220790791a0daf, 0x10ccf1a67302020d5c3565656558787, 0x421204280860, 0x10c3f00000071e711df25171f111f171f, 0x425210a80960, 0x14699532f132f17c17c1daf14df25ef6d,
      0x4e7208e809e0, 0x4a5210a80960, 0x1290cafdd0caf1c2f12a870e30e3099d3, 0x421204280860, 0x114114c74619b4b, 0x4a5210a80960,
      0x484220280860] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x15b9797974ddcdc8746e3e3e302220, 0x100043364355c3c3c3b73737730000ebf, 0x10c6f7b4dcb0cafcb1c9f10ef456fd900, 0x1997b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100007800017af11dfa65645333333020, 0x10101ad42905b17af07a6ce99e3cbe302, 0x501204240860, 0x14646cb171f8787d8e3e3e3017af1a673, 0x501204280860, 0x187d8e3e3e307821cf060f5f065b46,
      0x1533f064faf065b464646351f171f351f, 0x146ca46126f11df11df56c8333333025, 0x1294611c4560330330e70f5f449b4478, 0x425210a80960, 0x4a5210a80960, 0x1c37644144146,
      0x4a5210a80960, 0x4a5210a80960] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1333355e3e3e30ccf0eef7373c322200, 0x155e3e3e3080eef0873c322200d5f033, 0x10e610af0ccf08e50c30395700333333, 0x1d9d9d9ad12a870e30e306606624bf1c, 0x421204280860, 0x11caf2a2b7f0001fbf0f8da463a9b3a29,
      0x1c70e4f38a438461146f106fcd1cd1ad, 0x4e7208e809e0, 0x4e7208e809e0, 0x4a5210a80960, 0x16f8f2e8f3f5f4b7f13caf38df0000047, 0x485204280860,
      0x1474cef13e5f6f9f2e8f, 0x485210a80960] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c3f00000d300c700191900d50020200, 0x12392099134f132f07c07c014df134f6d, 0x1fde5fcc3000000fac7960961900000, 0x173f4000066066cc7c21dfe611af0ccf, 0x100000dad3ba0f5fc729d9d9d90dbad5, 0x10000f4bafac796219f96219f0dbae573,
      0x11aefcd2b5fcd117fad10cf2a269f0, 0x114df15df6a8700000a427462faf146f, 0x16afc00000c415df2e1a880f0f88274f, 0x1a67302020c49c2e18838ff885c18df9c, 0x424210280860, 0x1730202047c344e74425069b06ad0fcf,
      0x147c344139f445c06188f060d1f0fcf6a] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x17600137f00b3b3d303030308585850, 0x1454500360b360caf86186200f760caf, 0x12008480021, 0x107c185f4b2d6f8b8b7e534f3a3abb45, 0x100760caf767be30e30964835a3a3a37c, 0x1177373022200aaaa960360b36000e7f,
      0x10170730233201909393935583838319, 0x100caf87c401d8f00e393f393c3833383, 0x1730722202d360b3618ff00f3f6b120f, 0x173020205bd993939355838383d91773, 0x108317bf4e93f393c383e683120f1756, 0x1836b17729a986f7861dcf13a870e30e3,
      0x827204e809e0, 0x827210e809e0, 0x1796b0f1f125f2b0f870000075a8755b, 0x13a9945454503333330a9365b3679119f, 0x1019056567c0e7f7c185f4b08b8bbb03a, 0x1eb1aef9d10ef2f4f175f17efd9019,
      0x1880f9f780e1f6767e69c0e3f0cbf1b6f, 0x11b1d9f1b14ef0e3f18ffd910df06e00, 0x1ea2cea2c0cff0c0c0c8817b5c7bba, 0x8c42184809e0] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x176a6760000013b3d303030308585850, 0x10964835a3a3a313100b1a18618622af, 0x812008480021, 0x812008480021, 0x814058480421, 0x1200c5aa96000b1a0000076a6760e30e3,
      0x10137f00939393558383830177373022, 0x1119f0c7f119f1c1f0129f1bdf0137f, 0x18301707302332017ff0126f21cf136f, 0x16b188f0a687c40000093e793c38333, 0x117737307222016bf00b1a136f00f3f, 0x17302020d50f2f9393935583838313df,
      0x100000187f93e793c383e68313df17a6, 0x10f1f0f0f0f1f141f148f13ef12ef174f, 0x1244f12a870e30e308316bf535f139f1, 0x1425210a80960, 0x421204280860, 0x110e6fd9019019083d819b29a986f786,
      0x1425210a80960, 0x421204280860, 0x10d6a8c70f2f10f5f0daf2d6bdd6b244f, 0x1425210a80960, 0x1c57e12e1a796faf796b148f16a870000, 0x421204280860,
      0x424210280860, 0x1ea2cea2c0cff0c0c0c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x116ff18710000b3d303030308585850, 0x1e78ae079bcc00f31e6c571e61e601e60f3079b15d09c8f301e63cc079f98007b660008118001ead1ec4, 0x4111044810a1, 0x1000002d4f36184f360f2fdc11bdf536f, 0x8121044810a1, 0x1000000360360f2f86186457f76176,
      0x4111044810a1, 0x812008480021, 0x10f2f8b1e7f2d6f1ecf1ccf1b7f498f, 0x1e30e304835a3a3a3274f02d7f185f, 0x100d3f360d3f36000edf007700d3f20cf, 0x1450036155f36000e7f00760767be30e3,
      0x10d3f00d3f0000edf00000d3f20cf450, 0x110152f565537878719177373022200aa, 0x4006020004004000040040000040040000004200000002100000021000000021000800042022000002008000008020000020084040020200000010000200100040000102108fa726, 0x11ebf2b9f173f1f7f15cf17ef00e0e0e0, 0x13387017073023320001d3f1bdfdd292f, 0x10011bdf00187c40000e30f311afc337,
      0x1e78ae07987980f31e6c571e61e601e60f3079b15d09c8f301e63cc079f98007b660008118001ead1ec4, 0x1e78ae07987980f31e6c571e61e601e60f3079b15d09c8f301e63cc079f98007b660008118001ead1ec4, 0x15655378787d917737307222000156f1a, 0x137e68713df17152f730202011c4152f, 0x8e120c6809e0, 0x1e76c8079bcc00f31e6b641e61e601e60f30799e6102379801e7e60079f98007b660008118001ead1ec4,
      0x1365f174f11ff0144f004ec4f311afc3, 0x115cf265f9d10df354f120f14df25ff, 0x1730222000f0f75165f75a937187141cf, 0x8802084809e0, 0x20800808040201008100104004100024000865a2, 0x100e0e0e0093939355838383191773,
      0x13aef196fddececec2ddf1f7f6fbf17ef, 0x100e393f393c383338301707302332000, 0x173072220036036000f3f6b00187c400, 0x1e601e67980798f30100242661e601e60f3079b491c4810799e63cc079f98007b660008118001eaf04c4, 0x173020201d993939355838383d91773, 0x1e601e67980798f300fe641e61e601e60f30799e6102379801e7e60079f98007b660008118001eaf04c4,
      0x11faf004e93f393c383e68326ff17456f, 0x11e7f179f1ecf22af452f32bf1a5f0, 0x1e30e308322ff50cf1dff458f1b1f161f, 0x1a983ec17729a986f7866fcf12fef870, 0x827204e809e0, 0x827210e809e0,
      0x1ce6b1c4f11ff6fdf8700000750e3f75, 0x1331f7f04b00330e330099365b36cece, 0x115cf43bf001c3f000f30f34533223f, 0x102f7f164f1eefdd1c1fdd173f1f7f, 0x100ef378f3c3330330000033dd3302f7f, 0x14b5607017ef00000000000003ac4000,
      0x1119e01dfff31f33a56223f561f7f1b, 0x861218c809e0, 0x6211024810a1, 0x1e76edff9bcc00f3007d5f1a6000f4e60f30798007a78b21e7e6003d39f98007b660008118001ead1ec4, 0x12b8f16df11221f167f16ef11174f1a5f, 0x8c6218c809e0,
      0x8e7204e809e0, 0x8842084809e0, 0x8842084809e0, 0x1e61aef13df1b152f56000002b8f47df, 0x1186f11ff0144f00134ff378f3c310ef, 0x1367f9d10df148f120f14df13ef365f,
      0x12e3f0f9fa9670f1f0e1f21af537f21af, 0x17b0caf7bba1b11b10e3f456fd900000, 0x8c42184809e0, 0x8c42184809e0, 0x10333333002c682c0cff0c0c0ceb0e7f, 0x10dd00e6191914ef7867671136fc8d956,
      0x850a204209e0, 0x1069e669694b78e978ad136f152f1bdf0, 0x119360f9fc467e3289f0c80560334533, 0x10cbf690cbfa907e90ad0000452d45045, 0x114ef7867671136fc8d956ca333333069, 0x8612084809e0,
      0x178e978ad1152f1bdfca45dd450e6d9d9, 0x8c6204c809e0, 0x11d2fc816ff56033033069e669694b, 0x13aca02d009c8c360f9fc467d81aaf, 0x11690cbf690cbfa907e92dad0fcf538f, 0x8422204809e0,
      0x1c3f378f3a967e9] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x133cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cbf003434b623232300c8f0c8f0c8f0, 0x1541a43dff389f377dc1dc0f5f8418400, 0x8111044810a1, 0x12008480021, 0x100f5f8408477330cbf330f859385454, 0x1030013af13aff80f5ff389f37700cbf,
      0x10770a3a3a3358383837748b3b300303, 0x100f3a375a3d3832830480b3003203, 0x1f37701cef10ef0f5f01bdf56c300cbf, 0x18383837748b3b3f403030300cbff389, 0x1d9219f2daf1d93a045045077a3a3a335, 0x1025204a80960,
      0x173b300300300f5f140f107f10d9f1aaf, 0x1021210880960, 0x1330330839bf3a375a3d38325830f5f48, 0x168f3837713667e6dc8bdc126f187560, 0x1025204a80960, 0x1025210880960,
      0x1776610ef234f0e7f152f560000068ed, 0x117cf121f291f0c0d0f0cc777f37bf366, 0x117cf121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1f927ef125f1ae0058a00c8f149f0c8f0, 0x1018042408421, 0x1053feb6539f139f1197f10002d0ff96d, 0x1eace35b23cc0798f3025f81e61e601e679807980088d5f8222c0003cc812afc7b660007983cc1e612ec4, 0x1018050440421, 0x1268ffb890e0f16dc1dc0484048400b50,
      0x1012048480421, 0x1048415af125fb5150f8596554545453, 0x113aff8127ffb890e0f160172f00484, 0x1a335838383134813b30030303000cdf, 0x126a3d3832830480b3003b5030050a3a3, 0x11601cef10ef040043bc30b50026a3,
      0x183134813b3f40303030100ffb890e0f, 0x1044804b3003003053fba3a3a3358383, 0x1586fef000150835326a326a3d3832583, 0x1000026edb86583fb1fb67e6dc8bdc581, 0x421204280860, 0x1425210a80960,
      0x10c9f127f66100f6610efb41cafb43b0, 0x117cf121f15ff0c0d0f0c0cdf0c9f100f, 0x117cf121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1333310d5b3d3030303085858500c8f0, 0x2181044090a1, 0x1e300d500941940157faa1108f3923533, 0x218050408421, 0x1084220810960, 0x111ff10df11bf1bef0236f7539751e31,
      0x1084220810960, 0x1084220810960, 0x136af0f2f14cf197f3e013cf0106d150f, 0x4181044110a1, 0x112300c8f0e9f0d0f0d5f230cff030303, 0x80402020100204008100804010080022000885a2,
      0x12302b12bc710d4010d573d3251e3023, 0x218002408021, 0x2181044090a1, 0x218008408021, 0x218002408021, 0x1157f6659668438d4e6d4003434a42323,
      0x1100755968840d40d410d534b6230230, 0x8010200500104004008100204008104004021a3, 0x6181024110a1, 0x1232305dfd1fd0000101d3f186f111ff, 0x6181024110a1, 0x4181044110a1,
      0x14181504114a1, 0x1a687c400137f00590038000003434023, 0x10100000034b6230230790791a00d4000, 0x80402020080202008100404010020020800885a2, 0x10ba0ba100000000ce1115f0755968, 0x80402020080202008100404010080022000885a2,
      0x80402020080202008100404010080022000885a2, 0x11c12bfe610af1d4f0e51c31395700d2f, 0x1018050440421, 0x1018042440421, 0x1fcc323cf163f11af00d2f66086624bf, 0x18585013af66fd66fd134f0e60163f0e5,
      0x114ea68728cf94d59400000157faa2785, 0x1084204880960, 0x14e1d96fffd61d600000d5b31e575e575, 0x4281044810a1, 0x1084208880960, 0x1084208880960,
      0x10300da0d0fda340cff383f36156f361, 0x1084208880960, 0x1000000a3a3a33583838314887b300303, 0x8004200100120004810040401010002200088da2, 0x10480b3003330300000035135011c8f77, 0x1024220810960,
      0x1024220810960, 0x11a40000000331330f3a375a3d383283, 0x4002200104020400810080401000402200088522, 0x4002200104020400810080401010002200088522, 0x1a33583838314887b3f403030300f30f3, 0x1021210880960,
      0x135181f35111c8f77f433033077a3a3, 0x1025204a80960, 0x1021210880960, 0x1148152fb30030030369f6753af10d9f, 0x1021210880960, 0x1021210880960,
      0x10f9f1d3f56f40000f3a375a3d3832583, 0x12b9f000008353bff3700ff31a429ef11, 0x1024210880960, 0x1024208880960, 0x1024210880960, 0x1111126f17ff28ef136f28af701f11ebf,
      0x1025204a80960, 0x1025214a80960, 0x1025210880960, 0x1025210880960, 0x177702f10f9f16ff56033033068183, 0x1024220880960,
      0x1025210880960, 0x134223232300f368776736201fe6249f, 0x110c7f10c7f01591daf7738007b0034, 0x8040201100104004008100804080102004021a3, 0x2281024090a1, 0x2281024090a1,
      0x1703f1240f00dd25afdd1d2f015cf125f, 0x2281024090a1, 0x1342775596800007bb600334252303230, 0x14af318c4e5f0e3fd68418400000157f, 0x10a5204a80960, 0x10a4204880960,
      0x1704f7b10e3f34340e7f2323230177f3, 0x4281044810a1, 0x1084208880960, 0x1705f167f0002aff01591daf7738cb, 0x1084208880960, 0x11305f207f1706f3def1abf2d2f347f,
      0x1084210880960, 0x1084210880960, 0x1771cb181f7bb6ee707f340230230538f, 0x1084208880960, 0x1116df708f1def1ce1115f00000755968, 0x1084210880960,
      0x1084210880960, 0x1084210880960, 0x100c134f0d2f1caf0d2f28afba709fba, 0x10735c4c4c400d5b3d30303030858585, 0x1469346117a67302020157faa07108f07, 0x1081210880960,
      0x11163f6d150f11ff011bf003637f3cac3, 0x1004210880960, 0x1d3161f0f2f161f197f3e10df0f0f1bef, 0x1340232323000ca40d0fa4a40cffd3d3, 0x1125f0010015935353855555519434, 0x80402010001200048100404010100022000885a2,
      0x1080a20840960, 0x1084220840960, 0x103230306f1220f5d1dd1dd1d2f115cf, 0x1084220810960, 0x1084220840960, 0x1084220840960,
      0x1084220840960, 0x1d3000075596835b6550355094034023, 0x13434a42323230001cc70000caf00d573, 0x1340230230157f159353538555555194, 0x1081210880960, 0x1081210880960,
      0x1186f0000075596835b6559355194d5, 0x1081210880960, 0x11551555dfd1fd111ff1111bcf1d3f, 0x1084210880960, 0x1084208880960, 0x1084210880960,
      0x1084210880960, 0x1084210880960, 0x1084220880960, 0x1084220880960, 0x10d2f121f228f121f9c0d2f0e4f0d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13533333313013b3d3030303085858500, 0x100c70e383e300d500940940c5aaa3222, 0x18505850149f0c2323230cff030303c50, 0x1fb10e0f160670040043bc311afb5f60, 0x1018050408421, 0x11e5f03652025305334a42305230aa89,
      0x10513000fac70e30e300000940940ed03, 0x10523003ed261b865054053053b3a427, 0x1088210412121, 0x1003ed031e5f0365213cf25305334023, 0x123ed260b8653354335305300270535, 0x1f613013a7150eff2424000eaf230eaf,
      0x1f9930effb52400554179f575728f6f6, 0x100053a7b6261c1f262c7f0000d3012ef, 0x12424053112e010d8f10d8f49766d7600, 0x1012048480421, 0x1012048480421, 0x80012000480014000480102004100014000403a3,
      0x1014050480421, 0x10545407e7e28d8d8d8130e9f13a7d80, 0x165260267e16d89dd8d30e9fd8000024, 0x1d59400000c5aa278585850f826f814bf, 0x1340cffb3b3b3c5111c71878387163f94, 0x421204280860,
      0x421204280860, 0x424204280860, 0x421204280860, 0x10005305334b523052308500cdf0c3434, 0x1650540532753f4c3030503085ed00065, 0x1c714e14eb9946a940000053aaed260b8,
      0x421204280860, 0x421204280860, 0x1864951dfd618ffd6ee01d8f005311fa, 0x424204280860, 0x421204280860, 0x1341cef23052306b70bf70af1a18ff49,
      0x144ffd600000ed1661a65498b49532553, 0x424204280860, 0x100256f51ef1c9f1a2a4f49864910dfd6, 0x100ed2666b8654954495327533516005, 0x170cfe70f5f49c64953cf931939b0126f, 0x1021210880960,
      0x149149173f93c693000000eaf9b0f5f, 0x1025210880960, 0x1858500cdf0eaf0d1f155f0d1fe722ff, 0x1c4c4c435c4c4c413013b3d3030303085, 0x146c34693460fdf17a67302020c5aaa3, 0x100d0f0cd3d3d30cffd3d3d3c5a946e7,
      0x1c3c3c365c3c3c353b553340230523085, 0x1127fb865275405305300030503085ed, 0x165c3c3c353045334a42305230aaed26, 0x1c3469346114f176a7302020edc3c3c3, 0x165275413534953b3a400500ad46ad46, 0x10eafd30eafd365d3c3d3ed26127fb8,
      0x117cf0eaf17cf1f8f15ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x153df1b4f11bff0fff0f7c61c608e8e0, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60008118001e616824, 0x1008210442121, 0x11bff266f1bff03cbf01fff1c4f01f1f, 0x14d04d0163f00fff000000000152f1cdf, 0x1021df011c4f02d2f1b7f1b4f033ff100,
      0x80040002200000001000200010000800018000402020000001080000004200000010000440020001000020001400000004000200040020000020010000200100000200100029fe326, 0x84000002200000001020000010080000018000402020000001080000004200000010000440020001000020001400000004000204000020002000010020000100020000100029fe326, 0x1143ff7bbf6f6010713d188f0188f300f, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60008118001e616824, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60008118001e616824, 0x11fff099989898103f9eaeae1f9f0143f,
      0x101d5f1f9f02def3cbf36cf70df214f, 0x1f7bbbbf60201f214f1d5f214f0217f, 0x1ecf71f70999898987e9e9eae000143f, 0x108821240a121, 0x19e2e5f9e1187f1103f1f9f016ff3cbf, 0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60007980f31e616824,
      0x1e600025f80003cc3cc16c83cc1e60008118001e6088b000222c0003cc25f8003ea60007980f31e616824, 0x1057571171d1d830f5f500c5168f0c99, 0x20422084121a1, 0x112e6f53ef1012a1f00715151510af, 0x2080a0240a121, 0x2080a0240a121,
      0x2080a0240a121, 0x115f50297f301f2bbf301f10119df373f, 0x2080a0a422121, 0x2080a0a422121, 0x11fd1010fff0015015c30057d61793010, 0x100004000002204008002100084002000088041a3,
      0x2080a0240a121, 0x2080a0240a121, 0x20c0a064131a1, 0x194d594161f05d0111ff1125f28effd, 0x2080a0a422121, 0x2080a0a422121,
      0x1ca0fff984a4eb710119f0570157163f, 0x100804000010200408010100404100204008041a3, 0x4121846808e0, 0x1c457571171d1d836bf5f5010f698f697, 0x100804000020200808020100804100204008041a3, 0x414084280860,
      0x15757d61793106b0f5075015151510af, 0x414084280860, 0x103600009e00a6b90005700155715c3c4, 0x1d6a6d600000d5a7a3f7242402424c5c4, 0x1141f000100763676179f4e217f981c4f, 0x80040002200000001000200010000800010004402000002001000020004000020010040042000100002000100400000400020080000020200000010800000102000000100108fe326,
      0x1376f164f166f3e0f10e8f236f154f, 0x8120884808e0, 0x10f3f15150f5f5f528a415150f1f00f1f, 0x18a12dfc45757573d15bff6f600a63bc6, 0x11103f0016ff10f3ff71f70242408a8a, 0x28821040a121,
      0x1008210442121, 0x1e600025f80003cc3cc16c83cc1e600081180020460f3000222c0003cc1e61e63cc07987980f31e616824, 0x100a6b9076076013a7a3eccb70efcb1ce, 0x1e600025f80003cc3cc16c83cc1e600081180020460f3000222c0003cc1e61e63cc07987980f31e616824, 0x100a63bc6ec151501515130036000098, 0x1d3f5f5f528d45757573d07f6f6] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x153ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x18e] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10a10ff153f00ddf00b4b40ddf67d7f60, 0x13db4001eff00dff163f1edf13cf0a0, 0x1010ff1a9f1e4fbb10fff6018071fef, 0x100cef0fbf6e11bf6e00fbf011bf10ff, 0x1011bf104f0104f1a9f294fbb153ff6, 0x10d1e4f110ff100fbf6e11bf6e00fbf,
      0x1088202442121, 0x1088202442121, 0x1ac3edfac287f000010ff010ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x101f1f53df1b4f1412f0fff0f7c61c60, 0x80040002000040002800400020000400028000402020000008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26, 0x1088210442121, 0x1000001cdf70ff266f359f03cbf001c4f, 0x1710f184f0366f2e6f310f02f2f12b3f, 0x3cc01e6f30079bcc01e6f307983cc0000f3079803cc0000f307983cc25f8002046001ed98001e652644,
      0x14d04d0163f2adf13cf00000000002e6f, 0x101071f3f3d0000000135f0000000000, 0x80040002000040002800400020000400028000402020000008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26, 0x100fbf011bf10df04a1a9f2bcfbb98f6, 0x132ffbb2a7ff60371f0fbf6e11bf6e, 0x16e11bf6e00fbf011bf10df04a1a9f,
      0x110df0712f711f32fff72a9ff700fbf, 0x117df459f17df287f000103f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1168f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1f50e40000160000417041d580b5f500, 0x1013b41304b40000c3000b417b400a0d7, 0x1713f1f4f12ef362f204f1a7f212f266f, 0x1153f20df000339f028bf161f2f7f131f, 0x121af1a0f104f0e5f104f104f20df195f, 0x14e0a104f01a7f05700031ef01a0f11ff,
      0x110efb5f50a5001e3f097ca21ff1d7f0a, 0x10014df016c41a1f131f0417041d58, 0x1c414ef131fb417b40a010ef0f500e2f, 0x1079058ab5888ab08d22df000173f0c3, 0x1000079] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1105f00000010af00001701d830f5f500, 0x10100f500014df012ffce21af0002a000, 0x1e600044580011160001e6222c00088bf300f33cc3cc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0x128effd1fd1000fff00000c3000d61793, 0x1e600044580011160001e6f6cc003db3f307983cc3cc1e60f6d3981e61e60f303cc3cc0f307981e64f7c4, 0x1e600025f800097e0f30000fa98004458000fa98003d3981024e6003d39803ea6003cc79803ea61029745,
      0x1119f022af94a694005d0011ff0125f, 0x1131f715f1f4f1328f208f119f714f, 0xc121846808e0, 0x1a62c9f10f8f1000716f0529f161f540f, 0x211084280860, 0x211084280860,
      0x100360ccf36110f071a1f11f6f1dffa6, 0x811084280860, 0x12ddf097ca2f6f1d7f4a4eb710119f057, 0x4121846808e0, 0x10110f071a1f11f6f1a61110f8f1000, 0x211084280860,
      0x211084280860, 0x2800080420200808020100804100204008043a3, 0x411084280860, 0x411084280860, 0x811084280860, 0x1131f338f172a1d836bf5f50000ccf,
      0x11793106b0f50750034df010afc414ef, 0x414084280860, 0x1b900105f57000371f0c3c414ef131fd6, 0x100000000000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10e400f301615015045804b4580b51500, 0x104b40000c30670b40ab411af0a0d715, 0x11ebf388f717f1cef3b8f541f013b413, 0x1000405f040cf1a5f254f1abf718f13cf, 0x1104f0e5f104f104f20df195f153f20df, 0x101cef0f600031ef01a0f11ff21af1a0f,
      0x10b500a50024ef0d8ce2b8f19df19c11, 0x4121884808e0, 0xc121884808e0, 0x8120884808e0, 0x100f3016161f1a1f131f045804b458, 0x10c3161f0131fb40ab411af000000e2f,
      0x10079079058ab5888ab08d193f000173f, 0x100] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1448f194f3c4f1fff1fff0135ff71f70, 0x84000002004000002840000020040000028000402020000008080000010200000040040042000040002000200420000200020080000020200000020800000102000000100128faf26, 0x12aef19df30ff71af503f282f719f282f, 0x136bf71df13c7f71cf0000071bf2aef, 0xc131886808e0, 0x1000002f2f45af1d3f13caf366f3c7f,
      0xc121884808e0, 0x112faf433f13cf44cf253f1186f29af, 0x4131886808e0, 0x4121884808e0, 0x171ef38df477f010000c6f2aef0c6f, 0x644ac92b4c4fa767d90ba1afb864930e38cc41966d40388c7c8c9916550712d1039bbe2c04973b7a1a6f8d47d027c8b3246cab72999998077412b19341923ee4c0764d06ad44e13677dc3b94154077412b19341930716024a0c920d165f1341923f490b3c9b9dbd137c7308b86beaa01d6c3225632683310659b500c92262c32fcb58caf48bb6eb603228857cb58caf48bb6eb6191442be5ac657a45db75b0c8a215f2d632bd22edbad8064510af96b195e9176dd6cc8a215f2d632bd22edbad80191442be5ac657a45db75bc8a215f2d632bd22edbad80064510af96b195e9176dd6c0c8a215f2d632bd22edbad80c8a215f2d63879aefb15a40498d48a70ea8dad180d9fac64d096b503829de0d16f9f496081e3951858832cda806495e4c9d0d096b50343ef247d6536264d0648fa029f558cfe5758410abf0f8e70cc91f594d899341924011a0c9347d6eae546148fa01d8512b199863ea3513e8a666a72495e4c9d0d0648fa0367eb193425ad40dd8521e8e104aed1bc835983b53e9e532922ea8d7fa0c9e7d5c7720c91f72603b268646d33353924e14bb1ad0655835aa060c91f403ad8644de8a338b12c4b37f9cf3419ec7d93f50c93852ec6b419560d6a818324834597c4d07118f8e70cc951659dfe83279f571dc83247d027c8b1940a27cb1a8241f72603b268420cc3e34825ffe3ee35058f3152c35,
      0x1103f00721f01720f71ff1abf32ef50bf, 0x8120884808e0, 0x1011bf00ee2b6f0144f9eae01ce21ff, 0x84000002004000002840000020040000028000402020000008080000010200000040040042000040002000200420000200020080000020200000020800000102000000100128faf26, 0x1722fae02ddf11ef0d8f0eff0d8f011ef, 0x10eff0d8f011ef011bf00ee2b6f0144f,
      0x1000135f00000ec45bfec011ef0d8f, 0x1237f723f237f169f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x17eb4141f182f0d70013130e5f8be4240, 0x14c135f1307612af76184e0e5f24dfb4, 0x138bf038bf2b1f542f164f0fff9e0a5a4, 0x1377f9e05a11ef5d0eff5d00fbf013bf, 0x10eff5d00fbf013bf0002b1f543f164f, 0x10000141f0141f5a181f18d1011ef5d,
      0x1088208442121, 0x1088208442121, 0x17920bf79198f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x11c4f129fa66d00000a7a3f7105f240, 0x10000000e6f3baf6a26df129f129f204f, 0x100763676315f4e23ef24df1f9fd62ad6, 0x117ff280f724f1c4f0fafa645cf0000, 0x10fff9e0110fa41a1f135f000f1f0544f, 0x10eff5d00fbf013bf000c6f2b1f0164f,
      0x1000c6f2b1f0164f725f9e024ef11ef5d, 0x101105f15011ef5d0eff5d00fbf013bf, 0x2010080500024000820800804002020080825a2, 0x10edf256f0edf198f0000001e6f191f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1b446b40d4f0dff0d70013131854e43d0, 0x128130138f12af138f18134f0e5f13cf, 0x111bf0d4f00d4f4e145fbb8d150a5a44c, 0x1bb0ddf1505a0fbf6e11bf6e00fbf0, 0x100fbf6e11bf6e00fbf011bf0004e1a0f, 0x179287f00000d4f00d4f5a145f18d1,
      0x1088208442121, 0x1088208442121, 0x17945df] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x100301f02c1f546f545f11d5f214f0860, 0x21821240a521, 0x1726f0fff9e08642ff427f1d5f102e5f, 0x29821244a521, 0x10f3f0fbf000019af00c6f547f2ccf, 0x11192f0192f19bf01001266f2ccf2dff,
      0x3b9b0d0e251cd651dcd662a05f20001dcd660c389473594773598a817cf7483818cca003ba9b0b2800eea6c2ca000ef599328003bb8976842771373597b9acaee6b2f73595dcd6c735941dcd6c735a2e6b2800eea6c2ca003ba9b0b280077712eca000ef599328000ef59b955ba1c8, 0x200001000800004002000010004000028000002020001000080000008020000090080040001000100000800000802000100080000004200000080800000042000000100809c5c26, 0x415290a80960, 0x1014ff2aaf0ee201fee113ef727f101f, 0x415290a80960, 0x145ef372f372f548f02fef00372f0398f,
      0x11cdf54af284f01fff1bff0ca00549f00, 0x11def2dae980362f019df1000026cf0, 0x1e60004458000f6cc0025f83cc1e600118f8005b998f300f33cc03cc1e61e6003cfcc007a73001e9e2824, 0x10d6ff9dbf900d6f0db0d6f04d23ff, 0x100d6f0db0d6f04d23ff12d9e980728f, 0x21821240a521,
      0x100e7f729f218f6b16b00d6ff9dbf9, 0x109821240a521, 0x1378f4ecf378f0fbf00019ff16bf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x154bf02a2a43cf1f0f105f1d9f0860, 0x108672af7b3e0f7b12ff14cf377f377f, 0x1072cf348f2a45ff54cf10ef72bf3fdf, 0x100000204f172dfce3ccf45ff003fdf, 0x4010100500024000804800100900024000805a2, 0x11202f113ef3cdf101f10e9f255f0e7f,
      0x411084280860, 0x411084280860, 0x411084280860, 0x12a72ef379f105f1d9f014ff3ccf0202f, 0x172ff7b12ff21ff379f379f54bf345f2a, 0x119ff730f211f2a3b2f54cf0000ca07b,
      0x12d4d7f9800ce3ccf151f1200f3b2f, 0x411084280860, 0x1f9dbf900d6f0db0e7f00daf23ff14ef, 0x10e9f00d6f23ff12d1f0f9801e3f0d6f, 0x21821040a521, 0x111212f42df00d6ff9dbf900d6f0db,
      0x1088210442121, 0x109821040a521, 0x1155f0edf460f00001155f2fdf154f, 0x1088210412121, 0x10edf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1731f1000546f0e7f154df1d5f0860, 0x21820240a121, 0x4bac702061882a61172f474ca2a537dc3b94154075b0113cda185f6abd608330d6536264d06620cb36a019257932743425ad40d0fbc91f594d8cb597c4a6b2bd800ecf12b19341c463e39c33247d659a7113534f42fbd896c1912b199863ea350da3fa01d8512b19343236999a9c9257932d87edf70ee505501d6c03eaebbf023ee339a0678c313771860c5f84b5699e82563ef18b1170d7d5403ad8c898aef03efa264b7d8ecf12b25bd71ed88d07a594d899344b494b2dde247d00ebc44ad2d65f129acaf6003b3c4ac96f5c7b62341e900eb7912be1c9a5bdf4994f03ba0958fbc62c45c35f5500eb60065135bd9a0558bf5da6d8c8971dc525c60d4d6bbf6b30c41562b0fa980412a919b500e231f1ce199498411b7e25bc20b76d50648fa01d6cc895f0e4d2defa65ba336a0192a2cb3bfd0648fb9301d9341ab513208f1ab513208f192a2cb3bfd064c1c580928324834597c4d0648fd242cf26e76f434df1af3eae3b90648faca6c4c9a0cc41966d40324898a4429a0c91f4cc430c9a191b4ccd4e491f4cc430c9a70dcba50b3c8fa6621864d386e5d2859e47d3310c32684b5a81a1f7923e9988619373b7a1a6f8d47d3310c3268388c7c7386648fa66218650289f2c6a0907d3310c326833d8fb27ea1923e9988619344b494b2dde247d3310c3268646d333539247d3310c971782880b9aad2550009c5715434, 0x1263f6b734f6b0864b8f7b733f7b0732f, 0x107b54ef1cffce201f3cef0000000547f, 0x1ee113ef433f101f35df192f0192f0000,
      0x415290a80960, 0x1000e7f2b8f379f1d5f014ffce19bfee1, 0x415290a80960, 0x1ca07b549f7b21ff2f6f21ff45ef2aaf0, 0x100ce000200f019ff2aaf000263f0000, 0x100d6f0db0d6f04d23ff1def2d301f98,
      0x104d23ff12d735f9802ddf0d6ff9dbf9, 0x21820240a121, 0x1736f119f00d6ff9dbf900d6f0db0d6f, 0x1460f0000295f01d9f54af1cff119f, 0x1237f256f237f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x124efcb0ce0103f1011ecf71f70d7240, 0x21821040a521, 0x1088210442121, 0x4a82104529e1, 0x4a82104529e1, 0x114ff154f0204f145ff862a8600ccf1cb,
      0x1088210442121, 0x1088210442121, 0x10edf0d3fd7580154f491e3f490ca0, 0x113cf12af54ff18013ff0b407b40d3f, 0x1d758000000000000b9076076020cf, 0x13cff18013ff0b407b40d3f0edf0d3f,
      0x111ff0135f00100ec0ec020cf233f12af, 0x86600002200000008002000008008000028000433020000004080000000200000040860043000080000000200400000800040004000020010000080020000100020000100228ffb26, 0x10000018000ab0ab0000f500db371fdb0, 0x11e3f0d6f00701abf002a00ec1f0f15, 0x16b0000018000ab0ab2518f4180000d6f, 0x1f934dff9010df019ff00036df1def6b1,
      0x29821044a521, 0x10c40131fab0ab0a12af6b1e4ff500d6f, 0x1550f01111ff6b0e7f6b0acdb173fdb, 0x1088210442121, 0x4a82104529e1, 0x1f410ffd401e6ff9371ff9010df019ff,
      0x1ac0d6f173f0d6f0000abc4ab251ecf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x14e7f1400f737f0f7cb1cb00c5f18bf0, 0x80044002000040002800440020000400028000402020001008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26, 0x121821244a521, 0x10000073bf1173af0000739f00738f, 0x1218212442521, 0x121821244a521,
      0x145af1d3f02f2f2f2f36bf03caf1310f, 0x80604002000800002002040000008000028060403280081000000200000000800040000440028000400000001000080004000280000020200000080800000102000000100029fbb26, 0x100eff02faf2cff18af0000000000366f, 0x121ef0000000438f00000000000eff, 0x111ef3d0f1b4f1ddf73cf40bf01ce2adf, 0x80044002000040002800440020000400028000402020001008080000010200000040000440020000400020004400200004000280000020200000020800000102000000100029faf26,
      0x1035cf267f18af1def035cf001c4f0, 0x102d0f551f0307f27cf551f73ef73df, 0x1552f1e8f054df2c8f45af476f0073ff, 0x1202f1202f002cff00003d0f27cf1ddf, 0x1018210442521, 0x102d0f00307f27cf13cf475f374f0553f,
      0x1160f00c5c50c31cf1cff2e2f740f000, 0x10e70de0de160f04175f04269f10cf0b5, 0x10000c3000134f175f93010d7160f0e40, 0x100014000402204008002100084002000088043a3, 0x1741f0faf109f134f1134f101f0f3d1f0, 0x2010a0240a121,
      0x2010a064131a1, 0x18c101aaf000c95d131b131b00001161f, 0x2010a0a422121, 0x2011000440201008040101004100014008043a3, 0x10b500c91044df13bfd8ce434f05d9c, 0x1014210482521,
      0x10e1fde274fde27df04175f04269f10cf, 0x10e1fc3000134f175f93000000fa00e7, 0x1742f00faf163f255f163f00000102e, 0x80012000480204008080102004100014008043a3, 0x1e4193f00f6f743fc51047cf46cf12b4f, 0x814218482521,
      0x1014210482521, 0x1207fb41bcfb46e00d7001313a311bf, 0x11a3f13744f1c0f2e1c0f128f134f128f, 0x128cf0992faf163f6e011bf000c9a4c9, 0x1d7193f0fa13ef0163f1bcf145f1bcf, 0x100dbf2e0dbf128f0128f0b40b40011bf,
      0x10f6f0d00d02abf12abf09915c6c00000, 0x1014210482521, 0x1014210482521, 0x1ba0554f00b41d0fcc224f160f160f0, 0x1107f1b745ffd288f555f1138f2a138f, 0x40600000040800000404000000401000e050702808001000000500008080001000400070281000040002000000802000002080000020200000080800000102000000100018fbf26,
      0x10175f175f26ef46260f260fb42e4f1b, 0x100288f03d2f138f2a138fba2d6f11fbf, 0x21821240a521, 0x11198f0e4160f00eafe6226f1b107f1b, 0x21820240a121, 0x1342f011ff0298f161f0298f11aaf198f,
      0x121821244a521, 0x1000460291a92df734ff020bf11bf4b1f, 0x121821240a521, 0x1cc202f37af0c6f01c2f1132f2d6f0, 0x21820240a121, 0x1175f1c0f138f0460260fc40cc554f,
      0x10260fc40cc746fcc202f00c6f01314df, 0x100b53d1f013155f175f224f138f046, 0x1c30000c900e70de0de1e0f048c04269f, 0x1b51e8f0c90000128f0128f347f08c930, 0x11be70e1fde0de004004269f163f25df, 0x10000070931c336ffe6461f0fa0ccf,
      0x121821244a521, 0x100009905c10deb0d6c00ccf1b2e0e1f, 0x1218212442521, 0x10eaf14df10cf1caf3e1f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1000000ce267f103f08b0100000052400, 0x420860108860, 0x124000f30de15de1504fd043bc3e6b5f6, 0x1143f143f2800c3f0c3f13fc13a7f4024, 0x10f5175f040ebf040d30c8240530143f, 0x10242400def240def24530133f0133fc8,
      0x10d8240680d8d8d828c39d9d137e13a70, 0x13b66066f600d89dd8d8c3f59d07e00d3, 0x1000e42400c5f000093151d5f15b4fdb4, 0x1d71e8f000462f00ce747f103f08b0100, 0x420860108860, 0x102e0128f0d9f128f0b41b422cfc415bf,
      0x100014000402204008002100084002000088043a3, 0x113f40e4150000000005400a7f4002400, 0x1b40d30c82400fdfafdc90c928135413, 0x1a4e40400133f0133fc800175fb40ebf, 0x1457f0000000fa0c90c90139c133bf4, 0x103bc400150001abf00ce1103f08b27ff,
      0x4040501002090082100084002410020400817a2, 0x1543f103f08b0100248f0000000000670, 0x4209605208e0, 0x1547e7ea7000ddf240b60026ff0263fce, 0x11354131300e4000d8d8d818c31b1f9d, 0x1c309d07e00d30d824000fa0c9c3c928,
      0x1c91abf1301300a4e4000d80e9fd8d8, 0x104160f1a2f0b5160f0008cfa8cc91a5f, 0x10d7160f0e400e70dec4de193f041f4f, 0x1376f0131d0fd3000025c400c3000d4, 0x1130000110df748f5d0d8f9c19c1014cf, 0x2010a0240a121,
      0x2030a064131e1, 0x2050a0a4221a1, 0x107128f0b40b40d40d7193f0c9232f, 0x104319f043d3f1bbf0b500c9002e0128f, 0x1c300000000fa170f0e70e1fde0de304f, 0x1ca58a90cef08d000ccf02e0e1f25000,
      0x1242400124f0146f216f1d1f01d1f2958, 0x12400515f6f6f62809898135713a7150, 0x1a7537653a7a40000001d0d3000e60b5, 0x1749fdc6a36df200f29cf0ecf9e00def, 0x1215f239f179f239f0f7fca188f14ff, 0x128c39d9d137e13a79d1b4f242400def,
      0x19dd37ed874af01b4f0240689dd8d8d8, 0x1b407b4e65a0d7000dd89dd8d8c31d, 0x100c51e170f2e170f128f297f128f186f, 0x1e415015f6f6f600098545757a7150024, 0x106623cffa23cfc90c92813541313d70, 0x107c40e415000000000d3000187f0d724,
      0x10fcf137613a7660fa0c99cc99c13a413, 0x110df3e1fcff90fcf2f2f10170f098054, 0x4211886808e0, 0x1a79d1b4f0ddf240b61144f1cff144f9d, 0xc211886808e0, 0x1e49e09dd8d8d818c31b1f9d547e7e,
      0x123cffa23cfc9c3c928135413132e26bf, 0x1d8c30f2f9dd37ed874bf01b4f024066, 0x1c99c13a413e65a0e4000cefd80e9fd8, 0x1105f5701500f6f49c5668cfa8cc99c, 0x1f9231f1f0f14cfdb0cb014cf03b1f, 0x11def186f1c4f1faf1faf0fff00f9105f,
      0x118af18af27ef1ddf1ddf35cf1cef1def, 0x1010ca00b7a900000000105ff60018af, 0x4221204808e0, 0x1231f129f0e6fdb1cb2a0e6f02bef057, 0x8221084808e0, 0x174cf14af1f92a143f00000492af92af9,
      0x8221084808e0, 0x10cb1ccfcbd407370ff91ca74df8bb7a9, 0x8221084808e0, 0x10edf39bf11159f11112ef3d3f0000, 0x4221044808e0, 0x8221084808e0,
      0x8221084808e0, 0x8221084808e0, 0x8221084808e0, 0x19898135713a7002424000f6f0edf0d1f, 0x10000000000000b5240050f6f6f62815, 0x1de27cfde0faf04fd043bc30b500d3,
      0x10c3f13fc13a7f40242405a0f3164f, 0x108b024053d4143f143f143f283b0c3f, 0x1133fc8133fc81b175f175f040ebf04dc, 0x1b43b000009768970defeb0def9c53d3, 0x1660cef66164f9323df0faf0fafb4fd, 0x1f6f6f60151598545757a7000240018cf,
      0x124000fa0c9d7c9281354131300e4000, 0x18c13013000e4150d30000000000000d7, 0x1541104fa7f400a2400a4fa0c98cc9, 0x424084280860, 0x1f42f2fe4150d44c4f1422fb43bb474ef, 0x424084280860,
      0x108b024058fdfafdc9b4c92813541313, 0x1133fc8133fc81b175f175fb40ebfb4dc, 0x1a4fa04c98cc98c139c133bf40e400d3, 0x110cf0a19cf0a0e7f00e3f01509c58, 0x197b6ebe6134f19cf134f134f25ff134f, 0x10b113f1451f5815822cf0000097fa,
      0x424084280860, 0x424084280860, 0x1008008160f1a2f00160f00795a7938af, 0x1de0dede040804048d0b58d00000000, 0x10000c3000200f08d160f02b01adf1aef, 0x10de0de2504f404ca460b5193f00000,
      0x15d0d8f9c204f9c00000041d0f2b01adf, 0x100000041218f74ff1aaf110df552f, 0x421084280860, 0x421084280860, 0x11297f750f2bbf54ef207f453f207f, 0x8221084808e0,
      0x1ab232fab3d3f00000961751f530f556f, 0x8221084808e0, 0x1009617af144f146f170f0b070d1f556f, 0x1c41d1f304f08319f084f8f170f010ff, 0x10404146f0b59b01bbf8c1caf0e1f1d1f, 0x1000002b437f1adf1aefdec4dede0408,
      0x10e1f1d1fc41d1f3cefc3319f41cf752f, 0x1de2504f404d40cef0b50017af8c146f, 0x12b0e1f1adf1bbfdec4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x120ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1753f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d4f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x119e22af76a6760000013a7d367242400, 0x241084280860, 0x18b01505757572815f6f6130573657198, 0x241084280860, 0x100c5f09857980d4ff61e4fae79079dc0, 0x122bfb40ab4580a0d700a7d3676724,
      0x12a7600000010ef12af10ef181a7f243f, 0x10d700010ef3610ef11a7f122bf4e6f76, 0x241084280860, 0x241084280860, 0x10012af0181cef243f2a1fb40ab4580a, 0x10dc08b015010ef10ef10ef548b8b14af,
      0x1001a7f10ef1a7f0dff14af43ef1cef00, 0x10dbfb40dbf00d7001313d3111fe4160f, 0x1c91a3f13002e13ef128f0128f207fb4, 0x11bcf025ff163f134f171f00000c9108f, 0x1000000000000fa37bf019cf19cf0d4f0, 0x11d1f01d1f079079bc0000000000dff,
      0x1de1504004008bb51500c5c5880880faf, 0x18b000008bd7150e4ae0e1ff30e1fde15, 0x1b40b422cfc40d70000e1f930e1fc38b0, 0x1043b070b500002e28cf128f0128f461f, 0x10000131a7f0e1ff30e1fdedcde3b041b, 0x10e1f930e1fc319cfe627dfb41bb43b0,
      0x158175f58dc08b0150c99cc95d1307, 0x10150fac4138fcc138fcc0dbf1c0f1c0f, 0x1138fcc0dbf1c0f1c0f0a175f0adc08b, 0x10d754fab163fab3d5f00000c4138fcc, 0x10d0f0f6f12dfc5993ddf5c755f0d3cef, 0x1133fcccc048d041d0dcb5f502400f6f,
      0x10f5f004004008bb5150672b1b1b1b16, 0x10458041d07dcb5f50372b1bf31b16f4, 0x16d8b010ef05702b1b1b1b16133fcccc, 0x10dbf0dbf0dbf46260f97138f3f0f0ebf, 0x11b16f40f5fb4049c043b070b500138f, 0x1024018cf1bc8c8c8160ebfcc1b2b1bf3,
      0x11b1b1bd7133fd7cc0153f0670dcd7f5, 0x10dbf1b931b0f400000008bd715067cc, 0x11bb4133fb4ccb4104fb4670dc0f5037, 0x134cf0ebf0e6f8b010ef0570cc1b1b, 0x10000138f0dbf0dbf0dbf46260f97138f, 0x11b0dbf1b931bb4f4b40ab49cb43b0,
      0x1c4111f0160f001bc8c8c8180ebf0dbf, 0x18d04040bcb5b5000000000bd0bd1d0f, 0x10c4111f0160f02b11adfe7de08dede04, 0x8420204408e0, 0x125def4de004004000b50000000000000, 0x1dede0458040407bcb5b50082b881adf,
      0x11ab0dbfab557f000002b11adfe7de08, 0x8420104808e0, 0xc411886808e0, 0x104b4070b500173f270f173f51cf46197, 0xc411886808e0, 0x19cde1de12b881adf25def4deb40413ef,
      0x8420204808e0, 0x8420204808e0, 0x19620bf96] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d4f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1174f756f0000143f99bbbbf608e8e0, 0x100ee0e7fee019bf14ef142f01ebf373f, 0x1ee119bf1142f00dbf557f0dbf0000, 0x41000000101000000110000000410000040001000100100008000010020001000004000200010000800010000080040000280000010200000010800000102000000100069f6326, 0x41000000101000000110000000410000040001000100100080000010000041000004000200010000800010400000040000280000010200000010800000102000000100069f6326, 0x10000192f01c6f00373f0000000ee0e7f,
      0x113a7d3db24240f79a9a9a7e4d4d0c4f0, 0x144130036b9107b9a22af76a67600000, 0x282208482121, 0x1013bff5f500c5168fa3434343282544, 0x10009e08344444410afd606060171d1d, 0x112cf1dcf00fff142f1c1f0129f757f,
      0x1d600601700013bf15f500f0f12cf283f, 0x107b123f188f0a6fcc400000449344c3, 0x10613df171d1d070f5f50eb036b91dcf, 0x117a6186f000f50d58344444410afd606, 0x1758f0000007449344c3d6e60613df, 0x110f1f0f0f0f1f141f148f13ef12ef,
      0x485290a80960, 0x10e6f558f000980d636060e8f257f154f, 0x11bef0c4f120f506f135f123f244f1, 0x481284280860, 0x1244f19cf2a30ff000570947594eb0c4f, 0x16412dfb66363c546092909a91aeff79a,
      0x10c6464] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d6f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10b437afc415bfd71fbf01f0fe48a08e0, 0x1e4240d70d123f12af8d180182f0b4, 0x184058434343a5d744441301313f40ddf, 0x1040d725d7153f182910900000840ddf, 0x84220010860, 0x104358b40e2fb5a5000130131df4a4e4,
      0x19a434343a5d74444130131300ddfe424, 0x1b5a50dff1061301300a4e41600ddf, 0x84220000860, 0x10143f99bbbbf60e463e4630d4f180e2f, 0x1ee019bf1142f1ebf2e6f1ebf3c7f0000, 0x408c001023000408c00f3f307d4c1e7e60f3003cc1e60f30811bcc025f8002046001ed98001e652644,
      0x1142f457f0dbf75af0dbf000000ee759f, 0x101c6f0000000000ee0e7fee119bf1, 0x420000000840000002100000004200000401008381d8008060263008080004000004000200008100cc002000130004000048000000820000008080000008200000010004aedca6, 0x4200000008400000021000000042000004010082008000808026300800008400000400020000810040002040130004000048000000820000008080000008200000010004aedca6, 0x1e4240f79a9a9a7e4d4d0c4f00000192f, 0x11cdf1c6f000186f1c4f364f29cf0fff0,
      0x1d71e8f00f3f142f142f142f218f21df, 0x112af142f180182f0b40b422cfc415bf, 0x1a90c4f44000a7f4136f153f2400da9, 0x1281301313f40effe4150a34343430dff, 0x10b450efd33b0f0240585475bf58a5a90, 0x13bf4a4e404013df43123f43025044b4,
      0x1b4a700024058b40e2f123fa500013013, 0x1128130131300e400a343434300044b40, 0x2080082010200408100104004010800408051a3, 0x143043182509440000d30024005400a50, 0x1180e2f0a5130f1091301300a4e41600, 0x2100082010200408100104004020800808051a3,
      0x1a912cf090003bc413bf294f1500d4f, 0x1b40b4b4c4136fd7193f0c60606061a0f, 0x10272e3f11df2d7f0f5f18a91c7f26ef, 0x1180323f0b40b422cfc415bfd70d3f, 0x1463f75cf1300f0020cf0d3f12af142f, 0x108821040a121,
      0x1246f1559f257f257f272f0272f2fff, 0x1088210422121, 0x141df338f75ef0272f75df246f246f, 0x11246f075ff0257f2d4f055bf55af531f, 0x1088210442121, 0x1255f761f000002fff297f760f246f,
      0x155ef155df55cf763f762f255f2ecf, 0x484284280860, 0x1290f55ff765f55ff00000764f368f, 0x1434f0000022af393f1113f6f766f355f, 0x481284280860, 0x484284280860,
      0x485284280860, 0x155ef768f55df11500f462f767f462f, 0x485280280860, 0x4823886809e0, 0x1272f2fff3f5f769f1300f04bcf39cf, 0x1080a10482121,
      0x1246f246f1559f257f257f272f355f, 0x4833886809e0, 0x12d4f3f6f11041df0001f6f76af246f, 0x4813886809e0, 0x487388e809e0, 0x11f6f76cf246f1246f322f176bf257f,
      0x4823886809e0, 0x487388e809e0, 0x1441301313d70ae42408a0147ef12fff, 0x1088210482121, 0x1088210482121, 0x107c4161fe4f50129f8d434343a5b444,
      0x1840000013b4ceca0e2f04a500013a413, 0x10ae42404313b425b4ab18291094e840a, 0x84204080860, 0x1e4000a9a434343a5b4444413e6131309, 0x10d4f180e2f04a50dff10613a41316180, 0x84200080860,
      0x10601712ef1d013bf0f50013631363, 0x110af0000000f8f00834444440d6257f, 0x100601700013bf105ff50083083000f8f, 0x10f40000000190f0f8f5700449344c3d6, 0x1d6257f06280f1712ef1d0700f500000, 0x1199f0e6fa60e6f0005708344444476df,
      0x12a186f000f5007832a83a626dfa610af, 0x1a6fc0000007449344c3d6e606199f17, 0x107092c5f091b7ff41b7f272f199f1b0f, 0x116af2fcf544f126df76ef00000d6106, 0x3d398007a73001e9ccd613306b9800f4e60f31e60f5e098003ea6000fa98007b66001ed98001e631464, 0x481284280860,
      0x100000940f0f1c6f31af1c6f16af2d3f, 0x11f6f55cf1f6f246f770f1255f76ff, 0x485284280860, 0x11e7f1b0f2afc00000941f9f12c5f771f, 0x485290a80960, 0x10a2400c4b9464f142f148f196f1ccf86,
      0x1104fe4150a3434343b40b444000a7150, 0x10d72408d54206f8da5b40281301313d7, 0x135efe41500a430a43025044d3000187f, 0x100013a7ceca0e2f04a500013a41307c4, 0x10136eb9772f11115f19a4976129f7600, 0x485284280860,
      0x481284280860, 0x484284280860, 0x1434343b4283fb444b49ab4a70900a24, 0x1773fa5b412813e6131300ae4090a3, 0x84210080860, 0x144d3115f20df775f000240774f54206f,
      0x110913a41316180e4000a430a43182509, 0x84200080860, 0x1e6b40aab0d7000d4f180e2f04a5130f, 0x1132713104fab12af58181bef10c4fb4, 0x84210080860, 0x1a509444413d7131302cafe42408a063,
      0x1430f000777f560f0776f008d434343, 0x100e4f50132cf32cf32cf561f778f561f, 0x4402110002420090004800100900024000805a2, 0x1e42402c4f000e2f06a5a400130130, 0x1058434343a509444413b41313f42caf, 0x1061c6f06c429d4090abe0a779f01015,
      0x1281282980960, 0x106a5a420df0413ba131df40e4003a0f, 0x100b626af634463a50c4f444358b40e2f, 0x14343431812ff1844588458a7000dff24, 0x15427bf8da51812813d7131300e400a3, 0x84220040860,
      0x143d325562f440840231f00d72408d, 0x116a5a40013013000e41500dff430dff, 0x112ff1844588458a7f410dff240000e2f, 0x281282180860, 0x11812813b41313f41e4150a343434318, 0x281282180860,
      0x84210080860, 0x1d444b484b4231f010240585427bf58a5, 0x281282180860, 0x1134e133bf40e4000dff430dff43d325, 0x1a518a52514458b40e2f16a5a420df04, 0x84220080860,
      0x166644364a527] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13d6f] (by decide) (by decide +kernel)

private theorem vb11_0 : nb11_0.Valid :=
  SearchNode.cover16 nb11_0 (by decide) rfl
    checkedBranches1.vb11_0_0 checkedBranches1.vb11_0_1 checkedBranches1.vb11_0_2 checkedBranches1.vb11_0_3 checkedBranches1.vb11_0_4 checkedBranches1.vb11_0_5 checkedBranches1.vb11_0_6 checkedBranches1.vb11_0_7 checkedBranches1.vb11_0_8 checkedBranches1.vb11_0_9 checkedBranches1.vb11_0_10 checkedBranches1.vb11_0_11 checkedBranches1.vb11_0_12 checkedBranches1.vb11_0_13 checkedBranches1.vb11_0_14 checkedBranches1.vb11_0_15

private theorem tv_b11_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_0

private theorem vb11_4 : nb11_4.Valid :=
  SearchNode.cover16 nb11_4 (by decide) rfl
    checkedBranches1.vb11_4_0 checkedBranches1.vb11_4_1 checkedBranches1.vb11_4_2 checkedBranches1.vb11_4_3 checkedBranches1.vb11_4_4 checkedBranches1.vb11_4_5 checkedBranches1.vb11_4_6 checkedBranches1.vb11_4_7 checkedBranches1.vb11_4_8 checkedBranches1.vb11_4_9 checkedBranches1.vb11_4_10 checkedBranches1.vb11_4_11 checkedBranches1.vb11_4_12 checkedBranches1.vb11_4_13 checkedBranches1.vb11_4_14 checkedBranches1.vb11_4_15

private theorem tv_b11_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_4

private theorem vb11_8 : nb11_8.Valid :=
  SearchNode.cover16 nb11_8 (by decide) rfl
    checkedBranches1.vb11_8_0 checkedBranches1.vb11_8_1 checkedBranches1.vb11_8_2 checkedBranches1.vb11_8_3 checkedBranches1.vb11_8_4 checkedBranches1.vb11_8_5 checkedBranches1.vb11_8_6 checkedBranches1.vb11_8_7 checkedBranches1.vb11_8_8 checkedBranches1.vb11_8_9 checkedBranches1.vb11_8_10 checkedBranches1.vb11_8_11 checkedBranches1.vb11_8_12 checkedBranches1.vb11_8_13 checkedBranches1.vb11_8_14 checkedBranches1.vb11_8_15

private theorem tv_b11_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_8

private theorem vb11_12_6 : nb11_12_6.Valid :=
  SearchNode.cover16 nb11_12_6 (by decide) rfl
    checkedBranches1.vb11_12_6_0 checkedBranches1.vb11_12_6_1 checkedBranches1.vb11_12_6_2 checkedBranches1.vb11_12_6_3 checkedBranches1.vb11_12_6_4 checkedBranches1.vb11_12_6_5 checkedBranches1.vb11_12_6_6 checkedBranches1.vb11_12_6_7 checkedBranches1.vb11_12_6_8 checkedBranches1.vb11_12_6_9 checkedBranches1.vb11_12_6_10 checkedBranches1.vb11_12_6_11 checkedBranches1.vb11_12_6_12 checkedBranches1.vb11_12_6_13 checkedBranches1.vb11_12_6_14 checkedBranches1.vb11_12_6_15

private theorem vb11_12 : nb11_12.Valid :=
  SearchNode.cover16 nb11_12 (by decide) rfl
    checkedBranches1.vb11_12_0 checkedBranches1.vb11_12_1 checkedBranches1.vb11_12_2 checkedBranches1.vb11_12_3 checkedBranches1.vb11_12_4 checkedBranches1.vb11_12_5 vb11_12_6 checkedBranches1.vb11_12_7 checkedBranches1.vb11_12_8 checkedBranches1.vb11_12_9 checkedBranches1.vb11_12_10 checkedBranches1.vb11_12_11 checkedBranches1.vb11_12_12 checkedBranches1.vb11_12_13 checkedBranches1.vb11_12_14 checkedBranches1.vb11_12_15

private theorem tv_b11_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_12

private theorem vb11_13_2 : nb11_13_2.Valid :=
  SearchNode.cover16 nb11_13_2 (by decide) rfl
    checkedBranches1.vb11_13_2_0 checkedBranches1.vb11_13_2_1 checkedBranches1.vb11_13_2_2 checkedBranches1.vb11_13_2_3 checkedBranches1.vb11_13_2_4 checkedBranches1.vb11_13_2_5 checkedBranches1.vb11_13_2_6 checkedBranches1.vb11_13_2_7 checkedBranches1.vb11_13_2_8 checkedBranches1.vb11_13_2_9 checkedBranches1.vb11_13_2_10 checkedBranches1.vb11_13_2_11 checkedBranches1.vb11_13_2_12 checkedBranches1.vb11_13_2_13 checkedBranches1.vb11_13_2_14 checkedBranches1.vb11_13_2_15

private theorem vb11_13 : nb11_13.Valid :=
  SearchNode.cover16 nb11_13 (by decide) rfl
    checkedBranches1.vb11_13_0 checkedBranches1.vb11_13_1 vb11_13_2 checkedBranches1.vb11_13_3 checkedBranches1.vb11_13_4 checkedBranches1.vb11_13_5 checkedBranches1.vb11_13_6 checkedBranches1.vb11_13_7 checkedBranches1.vb11_13_8 checkedBranches1.vb11_13_9 checkedBranches1.vb11_13_10 checkedBranches1.vb11_13_11 checkedBranches1.vb11_13_12 checkedBranches1.vb11_13_13 checkedBranches1.vb11_13_14 checkedBranches1.vb11_13_15

private theorem tv_b11_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_13

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_new (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left))
    (r : State) (d : Dir) (hthird : M 2 0 = some (some r, Stmt.write 0 d)) : False := by
  let tb := baseTable.set 1 0 ⟨2, 1, true⟩
  have hm : Matches M tb := matches_set hm0 (m := ⟨2, 1, true⟩) hM10
  let h2 : HistItem := ⟨2, 128, h1.c.move ⟨2, 1, true⟩⟩
  have live1 : M.multiStep (Machine.init []) 1 = some h1.c.view := (hv h1 (by simp)).2
  have live2 : M.multiStep (Machine.init []) 2 = some h2.c.view := by
    change M.multiStep (Machine.init []) (1 + 1) = _
    rw [Machine.multiStep_succ, live1]
    exact step_move hm h1.c ⟨2, 1, true⟩ rfl
  have hv2 : HistValid M (h2 :: [h1, h0]) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨by decide, live2⟩
    · exact hv x hx
  fin_cases r <;> cases d
  · exact checkedBranches1.tv_b11_1 M hG (matches_set hm (m := ⟨0, 0, true⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_0 M hG (matches_set hm (m := ⟨0, 0, false⟩) hthird) rfl hv2 (by simp)
  · exact checkedBranches1.tv_b11_5 M hG (matches_set hm (m := ⟨1, 0, true⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_4 M hG (matches_set hm (m := ⟨1, 0, false⟩) hthird) rfl hv2 (by simp)
  · exact checkedBranches1.tv_b11_9 M hG (matches_set hm (m := ⟨2, 0, true⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_8 M hG (matches_set hm (m := ⟨2, 0, false⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_13 M hG (matches_set hm (m := ⟨3, 0, true⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_12 M hG (matches_set hm (m := ⟨3, 0, false⟩) hthird) rfl hv2 (by simp)

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H2 := by
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
  obtain ⟨q', hNew, hM10, r, d, hthird⟩ := second
  rcases hNew with rfl | rfl
  · exact solve_new M hG hm0 hv hM10 r d hthird
  · have h01_base : UsesOnly01 baseTable := by
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      intro q a m' hget
      fin_cases q <;> fin_cases a <;> simp [baseTable, Table.set, Table.empty, Table.get] at hget
      subst hget; exact Or.inr rfl
    have hprev01 : ∀ h ∈ [h1, h0], h.c.state = 0 ∨ h.c.state = 1 := by
      intro h hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl <;> simp [h0, h1, startPos, Position.move]
    have hM10' : (reindex23 M) 1 0 = some (some 2, Stmt.write 1 Dir.left) := by
      simp [reindex23, swap23_1, hM10, swap23_3]
    have hthird' : (reindex23 M) 2 0 = some (some (swap23 r), Stmt.write 0 d) := by
      simp [reindex23, swap23_2, hthird]
    exact solve_new (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01) hM10' (swap23 r) d hthird'

end OMA.BB4H1

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H2 := OMA.BB4H1.h1_proof
