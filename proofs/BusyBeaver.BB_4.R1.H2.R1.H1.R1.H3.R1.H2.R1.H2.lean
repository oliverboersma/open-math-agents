import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1

/-!
Write-0 residual H2: `M 1 0` targets state 2 writing 0 (either dir).
FAR/TNF certificates from @ubuwaits `R2.H1.R1.H1` tv_b8 and `H2` tv_b9
(state-2 trees); checker from @hyprspacecoyote R2.H1.
-/
-- Credit: @pageman

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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580684011931872, 580684011931872, 580684011866336, 580684011931872, 158471546996960, 158471546996960, 
    1461864025806835825412678583131432658718136235426, 72637628284961, 580684011931872, 48526606668273970384418392398631364281246430626, 580684011931872, 48526606668273970384418392398631364281246430626, 
    580617440004320, 191040945127532847629300509356555999372904753959216939898340931399547246124086739196944426639436543684, 191040945127532847629300509356555999372904753959216939898340931399547246124086739196944426639436543684, 16641875742412316784231806828678235166152644401024368103843871060332942088075137478093709091165173444, 291962732323023105017040792183882716068349226897511959278923674891309007423795579466369408460912324, 158471546996960, 
    564085168276513, 567521314084001, 564085168276513, 565219040692321, 1464361709266407596774665301421331909814746903970, 286431641864672, 
    1461864025804172166982813300974795293326077097378, 567631740537312, 2078206948827074159375332889422874939590137389076423151170880409906798680308466164372084064303493988, 145274082689057, 145274082689057, 265783660764111914541556245094158712558996068906704784612334075791772037429517506785635263835129038532, 
    265783407324249547732709478571536249826391226881233229475747986536557712154044511808615161745599775588, 290829688375776, 290829688375776, 2124839861432418469047889324897625585685455500713237997818109983295315661194931613666459051307976388, 81924626647520, 72843721705569, 
    145274183353377, 75327556880864, 286431641864672, 1461864025804172197446119159257036339490260039074, 1461864025804172167022504753779530703569383110050, 567631740537312, 
    74836651540513, 1461864036693207908492535584607518141385965876642, 966163864949330575067660639101841903340483281678925007982733308351952403605275703249339514173968322356365245739748840004236785185550584347072057599281379955134014964848422, 145274183353377, 183045214854273533296870515141649719302077817763, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 
    265783534044183563548419933159424916287270605315382975296643102090471733918175766779926587316802070884, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 564085168047137, 81640091560289, 565425198925921, 
    565184680724577, 565184680724577, 72843990141025, 562985655369761, 564085168047137, 564085168047137, 
    1461864025806835825412678583131432658718136235426, 480481078833541558372121462767058613307873924962920186088194706406010124923268226939886532098741224425175891637053312431695069872734913197141436719131945492178930912715200195697501938512575117016823125087790228818151848229321345239175273267320316075823875138107022760]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580683911268576, 565219911008289, 88031864553505, 580684012325088, 580684012325088, 158471681476832, 
    145277541943520, 71814270682145, 71814270682145, 282851783738401, 282851783738401, 282851783738401, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 286014896081120, 
    145277407725792, 149675722672352, 185544998536624000785095688723326351708275619234, 145277541943520, 730764756684370999216842858312302753416413708707, 145277541943520, 
    145277541943520, 145277541943520, 145277541943520, 145277541943520, 71814270682145, 71814270682145, 
    142251736435809, 282851783738401, 282851783738401, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 143078384470240, 143078384470240, 74908663548128, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 149675454236896, 149675454236896, 141908001687649, 
    286156764219872, 567631606712800, 145419141646816, 145419141646816, 145419141646816, 145419141646816, 
    564326525075489, 149817188157920, 154219798071776, 290554810730976, 154219798071776, 290554810730976, 
    154219798071776, 290554810730976, 149817188157920, 154219798071776, 567631606450656, 567631606450656, 
    1461685619845278754530431049358269582390216660258, 426898681760224, 426898681760224, 145423705049568, 286156764219872, 426898681760224, 
    286156898437600, 154219798071776, 154219798071776, 154219798071776, 154219798071776, 564326525075489, 
    564326525075489, 564326525075489, 564326558663713, 564326525075489, 286156764219872]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [732180859417103219741646552571096028979260872098, 290829688375776, 81922479163872, 290554810730976, 290554810730976, 290554676513248, 
    290554810730976, 290554810730976, 290554810730976, 154215503104480, 290314560735712, 290348652300768, 
    290555079166432, 290555079166432]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [564332967526433, 1461596415859588307719953399713296801748937610658, 564092482946081, 564126842684449, 564092482946081, 564126842684449, 
    564092482946081, 564332967526433, 480481077047106023417608928812220475712048137818800171737751120387406436719275197176533274904672894140098364687896727385014741869774464733091026800344425099455506766902882340132742928865222891890352906868447283992574381794009696294307269548711554727666518016249598761, 265750974941130293871093805119180229696112387423225465719412172432125437306600020704316720672220716421, 265750998701117567785135337399778734287374456057272334838877809611977130463277651675415980239042197253, 73121889781984, 
    265785688283061832415414176102327130081379350843061641403582205801031731801182001067991249762921268932, 265783692444095654529754258157132933653233741495699195484660648685283563346634496493094720695008020164, 265783660764111914541557124390336307247081315727011007187349948896249769008261544033900408960472106692, 265783660764111914541556245094158712558996068903636332651711142391133821283244734069739918465278985924, 265785688283061832415413296806149484211520353100894231679781945032085677093148826436962689672593065668, 73121889781984, 
    37939664980192, 73121889585376, 73121889585376, 564126842684449, 564401720788001, 282858024862753, 
    282858226189345, 81928921614816, 290829688375776, 81928921614816, 265751220461005753993844546341317621682939675694486723364493120751120303530710484590202875928299839941, 565226355820641, 
    362922862184928, 265783660764111914541556245094158712558996068906704784612334075791772037429517506785635263835129038532, 72640786598112, 74908663548128, 74908663548128, 74908663548128, 
    286014896081120, 730842809590322014007978904938306793188778576291, 290554810730976, 154219798071776, 75320912840928, 74839944071392, 
    74839944071392, 286152335034592, 145273514952928, 145273515149536, 145273246976224, 74839876962528, 
    215577432426720, 215577432426720, 215577432426720, 356315054999776, 74839876962528, 145273515411680, 
    145273515411680]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [576290260388320, 576290260388320, 730753606960454507600780929026791259587553564066, 265783407324249547732709478517868270233747802871595241414039453732061746482578784331726944183223731044, 265801654994861121644809591719385693117368448515566517904420884528327316475311152927895313741653362276, 576290260388320, 
    154353076144608, 286157032393184, 265783407324249547732710350944544528245248527191015350476459753188153791862184825727933514881230324580, 265783407324249547732709478517868270233747802871595241414039454375543096160799972335511354263470228324, 154078197975520, 154078197975520, 
    1461864025123623010071203430819158246129893160354, 290829688375776, 567494167366112, 567494167366112, 567494167366112, 732180859417113604374977703483485258768691271074, 
    290829688375776, 145694019291616, 145694019291616, 91522971547888857395043688949275964138152564002, 290829688375776, 290829688375776, 
    290829688375776, 567494167300576, 567494167366112, 1461685634813684030859603079684764069293292295458, 567494167366112, 732178425706991521291988479732015723888100545954, 
    732180864850997610578894585201201794802640262562, 132932253051187826038216600160633821912733318628792445810531936654202295780415130060727081661416539940, 132928197518239160296252839338300567627568738030203427658482599210172780792077480314606629879088825668, 732180864850997610578894585201203483658942977442, 132936307594016172501722152760385591613218619609478603005418557076013995662884815527341765537793459524, 132875514200551213644534064180571755713789664955394532205846980777143850355863748065873559265606137893, 
    145694019291616, 732180854653160467481684471974821248125706474914, 265783407324244827047202888824329598517106474595004228889892674607339666133582215839654971309214148964, 265783660764111914541557124329959829405642254442371872873000396231510036260982346041722933822489898180, 265783660764111914541556245033782234717557007618997198337361589726394088535965536077562443327296777412, 265783660764111914541556245033782234717557007618997198337022897158691404697003462356296596336924699844, 
    145694019291616, 732180854653160467481549072283024409658139383202, 732180855333725201323445342096674434883309311394, 145694019291616, 732180855333725201323445342096674434883309311394, 91522607445766636584894994473903720401723757986, 
    290829688375776, 73126184749536, 265783407324249547732709478517868270233747802871595241371364190209093951593101274134627687044344857444, 24307904844490680048574324743678009382734960034, 37941812464096, 73126184552928, 
    73126184552928, 265783407324249547732709478517868270233747802868776811461856685138289891984819223577938243243707876196, 81922479163872, 571892214270432, 290554810730976, 149679749204448, 
    290554810730976, 290554810730976, 149817188157920, 290554810730976, 16658095707978888284936390092739011560132949983119440263989784339057180843171274592131891862505146052, 16658095707978888284936390092739011560132949983119440263989784339057190394188305009906401566779393732, 
    435484388493792, 154009143347680, 290829688637920, 1461864025804187743912926824097645053462578771362, 567494167497184, 732178425717625385822932270923380545371777832354, 
    435553040861664, 91522966103370986660028273535286467363101775138, 145281971128800, 290554810730976, 732180864861631475109838376392570556951023883682, 568490633333216, 
    154352942057952, 290554810730976, 567494167759328, 290554810730976, 154215503104480, 290554810730976, 
    290554676513248, 290554676513248, 149817188157920, 290554810730976, 1676866272193029428224668747729329813283935139089169660721959467708462956904925217182976993634276637624988923245421837832753016488666279681327020981945238313850569392335469385868558290514247917128265678796435960394703167552783795695057493068667094534243801093991211133478246567138606766983193216521756177038720270235733818648207672939993184210947413055947362204031115085924882731, 290554810730976, 
    290554810730976, 290554810730976, 290554810730976, 145281836911072, 72610988165217, 283717220698209, 
    265783660764111914541556245033782234717557007622065650297984523127032304682238308793457788697146830020, 145281836911072, 294815552506336, 145281836911072, 294815552506336, 145281836911072, 
    145281836911072, 290554810730976, 145281836911072, 154352942057952, 74912958515680, 145281702693344, 
    145281702693344, 154215503104480, 431430006082016, 281758583491040, 281758986144224, 281758986144224, 
    290314560735712, 183045214849122755164619662596591743744591799203, 290348652300768, 154352942057952, 154352942057952, 145419141646816, 
    145419141646816, 290554810730976, 290554810730976, 290554810730976, 435828052593120, 45398345648608, 
    290554676513248, 81716320930272, 290555079166432, 145419543841248, 435827583224288, 508464070134240, 
    145419544300000, 72851508431328, 149679749204448, 145282105084384, 290417237559776, 74912958515680, 
    145281971128800, 145281702693344, 145281702693344, 154353076144608, 154215234669024, 145281971128800]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b8_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [182699551982448538483871585870120436487502181794, 177061641717984, 141979275102432, 564092482946081, 564092449357857, 265783407324249547732710350998212508637607160194970589769867792677302300990370559273977811455718369636, 
    265783407324249547732710350998212508637607160194970589769867792677302300990370559273977811455718369636, 564161202390049, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493221210255610764517877771240757711776100, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 564092449357857, 
    1978658779495010857921506726200232164528366838699012772719397962302619655919008423645291325574162769445726095809830140478843302902742075953910171079142816872601772234632061734, 1978658779495010857921506726200232164528366838699012772719397962302619655919008423775152369066431120893736001765391488026156327108997908966715037020333792788594842191700943654, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 265783407324249547732709478571536250626106435875550480707447493864691605288985705881555650837958273380, 39724693719264, 39724693719264, 
    282858091979041, 71545633899553, 71545633899553, 71545633899553, 71820713133089, 71820713133089, 
    45688651768710295826204242405163238663634551203, 71545633899553, 71545633899553, 71683148358945, 71820713133089, 71820713133089, 
    365387953549772900424076687473194784146648465827, 294819981298144, 730764756684390470404493508777943231771598389667, 3880105118047768846394620327283782093906973322392707030678619764866093703414944052293556817807879468197293099426186646868134473607109491904001994574569304319993241500902182, 286157032393184, 1461529513368780940654873184803806379990997015970, 
    265750982861126169859575712062919439118885473262705519378809920469697500622777743723809452544267944612, 72029021997536, 177061641717984, 141979275102432, 423600280701408, 265750982861126169859575712060836187381901825641925603183642976093626336587611897850977116665022284452, 
    36426158835936, 141979275102432, 141908408076512, 72020230473952, 564126809128993, 564332967755809, 
    564332967755809, 282857991307297, 282857991307297, 2108651412944397531248975787398815768503372911912022126785821771912679366014506495951811615950161604, 288883718757581814639357502268263608443556619061697295821962734157977466187276923088106278310172477124, 365400497777422781968571539224039523926692894498, 
    265751093741551359815597357742025736477031684847739505043953262227883620024068628245151179779112469156, 1461596415859588307715001639556155280649341115810, 564126842684449, 564126842684449, 564333001114657, 564126809096225, 
    564332967526433, 265751093741560801186412709230651528542611869959522053443466751091364939718712477893831119560315273892, 265750998701117921836539515394583362414103864088443582216233754924302842966324483738004218339540350213, 265751093741560801186412709230638937826269143936509197155749002189158621896686769844285999157084979876, 265750998701117685802269164924509481987166814854404721376687276611779660223477377309629506086103545893, 265751093741557024638086212107827582504101473898755778006348080600805244750335079359970926132231701156, 
    564126976976161, 265750998701117685802269164924509481987166814854404721376687276611779650597255631826510417815240570917, 91433229900140350837969651909778910487111015842, 73119742298336, 4152489478245602117955526758703453987170327755107281322127504604204307814394009096889994354017206948, 4152485765747535248354634534461186861078629238806133865958687819838338866034090278208847334775489188, 
    73119742298336, 37935370012896, 73119742101728, 73119742101728, 71545633899553, 45699802183844857002892318197230395972613308835, 
    71545633899553, 282858024862753, 564126809128993, 564332967755809, 564332967755809, 282857991307297, 
    282857991307297, 265751980780607960614139557135854550829071753816617439658305889261277971747595721958358078651001242276, 265751980780609848888302800541157235821504972276301404728686813571001389699192895080688048138804298404, 71545633899553, 282858226189345, 142120603623713, 
    81924626647520, 81924626647520, 1046199806655456814187289393594413257587936909703652206502778551305981597252821962769338994877301412, 81924626647520, 81924626647520, 989329153831664413307367360831762574958688210718350727286345516776997829561037152940185599306628707724280030804318251811574814218121628005406517354647144357090647193510881062, 
    290829688375776, 290829688375776, 143078384470240, 72709640292576, 143078384470240, 143078384470240, 
    143078384470240, 213380556654816, 143078384470240, 564332967526433, 566531992915041, 143078384470240, 
    72709640292576, 143078384470240, 283824462760416, 143078384470240, 283957740964320, 565432514250849, 
    143224681794016, 283957740964320, 213380556654816, 143078384470240, 424699390069216, 213380556654816, 
    143078384470240, 424699390069216, 72709640292576, 143078384470240, 1462216657701427443207918435248570820287176655267, 143078384470240, 
    143078384470240, 143078384470240, 143078384470240, 565501300779361, 2056190593532831424095101229665769924006714840994099866984816984117853030709734507365486021127700995869072132569587419514032725628522790310616124465537295995408585916068904742, 565226355361889, 
    565226355361889, 565432715118689, 61847696334955086639193660342125235548647797212825073714617519020510908910759352988928277499025276705475720542289689917751744724064655541740266170897703757862161917835695910, 213380556654816, 213380556654816, 213380556654816, 
    217783032351200, 37701493983329, 72640920815840, 72640920815840, 217778670274784, 296952365844960, 
    730845771408054078489696041063275168424015169955, 5798215870075658211420407184615404719312994723, 1978658307751508209731300482704683227442739315060202944742355810210052925488133860707147554529465363902491473403150856877441974211778165720607072601573412913097483662964512550, 74908663548128, 74908663548128, 145277407725792, 
    145277407725792, 74908663548128, 145277407725792, 145277407725792, 145277407725792, 286023486015968, 
    294819847473632, 730842809590332398641310055850696022978208991651, 86052291742176, 290554810730976, 86052291742176, 86052291742176, 
    154219798071776, 154219798071776, 154219798071776, 154219798071776, 290554810730976, 39724693719264, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    145277810378976, 145277810378976, 1461864025802879279964657466935371208675916518818, 145277810116832, 145277810116832, 1461864025802214663426512048385318981052773440930, 
    145277541943520, 39724693719264, 145277809985760, 286514784692988995531271664605112892427522164224121171407313906901527830849294242339521686549914240324, 74908663548128, 145277407725792, 
    145277407725792, 74908663548128, 145277407725792, 145277407725792, 145277407725792, 145277810378976, 
    36567487357217, 145419544300000, 426898815846880, 145419544037856, 145419544037856, 426898681760224, 
    149675454236896, 149675454236896, 149675454236896, 149675454236896, 92771453940858257491769166654789332028654884258, 79716811868384, 
    44542070163936, 149675454236896, 149675722672352, 184758223112416, 219977626421472]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

private theorem tv_b9_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581093006804001, 580719347894496, 567624392152225, 564325454480417, 567624392152225, 265783407324725392828938334356413918702589570505240580092137003913060430364252468447195058293360897732, 
    53052547564577, 268378631573369239685731794257359673725133098866138037034041463652942340877849672179051677969763348164, 580577608599648, 25690556475346207874670512835084176336689300898, 1464356230722953767981422770040175273810497897890, 565425335307489, 
    25690556480663140140219779978369828525061965218, 25696131666962772796005163907937990615438460322, 567624358565025, 2108619733444055736041387255672459763647159296912187452323279329495591523570302109936254350383984324, 2108619733444055736040946318305748046402426023840951589531717250155100031539309240135736206435055749, 283125355676705, 
    132877511029518764303025562730626967391514495691560812747115827995374115282195062323066026476250364037, 265783439004225734624146363710623967609188187511895733582098320529620450457624195750531963242042961604, 265751220461002921582585052678911041117164793722668037809534702820203681792926165111020349837155577540, 265783439004708896775665392355877861128863183497789899809980194996863786468660290629165109563100788869, 265783439004708896775666271652055500601000462375108217635260273982831077803816419676835160954037106821, 284225102417121, 
    37934531349729, 45761173065078225069484203645041179491656014755, 1461592234469822369363201861400975379011580730275, 148523311832908097666560981655091297310680030115, 2111201651623782884804442453882779589530527947263467818822007706433021200782081037312404466827819141, 45631112750369, 
    327106089461025, 44531332449313, 1978658307751508196001678975318213461311629267118586113391266038151901087615461667071756707642437925289038499413504697980158517083489887297903092425027280893129717441776670503, 267859582771376891514114293355240242126695240497403767703847273165407105296402001050331616856886030020, 398918407322093383054215344794859828004161662284038492408623394742409745077377297117821088909119008452, 14275275409577789394897237455367834695648150946, 
    36835019719713, 36835019719713, 283125590787105, 283125590787105, 36835019719713, 142388236649505, 
    283125590787105, 22925253537925832852675517834519870505744860578, 2044581912755849578502657307445964262543947881133363500367789867661303290797627774532897232369771272821036222790478313393549200981365065855198051450661500012867862421080874023, 284225102417121, 265752994540085751962201258592594098555013113341775792559779018567964142756149149336371338760031383236, 265752994540085751962201258592594098555013113341775792559779018567964142756149149336371338760031383236, 
    282621948258170769435039093683824267660797578775802827573373488661714073627937904565901902822581997317, 282621948258170769435039093683824267660797578775802827573373488661714073627937904565901902822581997317, 36835019719713, 142388236649505, 580578715961440, 580578715961440, 
    580578715961440, 87997506914400, 368230089831912706516036393544253044181988541858, 265783660764111914541556239077474971753699818838349150004434546592294914429935427928464341037721136836, 265751220461002921582584174242141720904728610158548674549963024254931910758488207246171296124444421828, 580681795176544, 
    228842373646560, 580680791098401, 564327634536544, 265752994540108411252272281240018335430790194086664623538017390049432832720301743718323381370788585156, 567633686694368, 1464361708248215067887250603388447620491794451874, 
    1464361708248215067887250603388447620491794451874, 286149248029857, 564327634536544, 564326558664800, 565426071341152, 565426071341152, 
    565426071341152, 565426071341152, 265751220461002921582584613031549408829008720137533474982836024494046929158912484468393692654750215876, 567625096693984, 286149248029857, 142113359004705, 
    282850713142305, 154207986922913, 290547294545185, 91522967448539455417113466693725738151331500835, 91522303217359225745232786186492031339782738723, 91523348564790406868192545673286061731728331555, 
    145411893892257, 286149248029857, 142113359004705, 580684011931872, 48526606668273970384419034640617149741071345058, 580617442101472, 
    191040945127532847629300509356555999372904753959217528107083240304137531716687339119319421523101507268, 16641875742412316784231806828678235166152644401024945214308121483379192571444038961194523462592388804, 368230612510778101650421373099329180773246043043, 88104952400096, 158471546996960, 567521313035425, 
    535265009258875743553122105331639457575449674705736344746301452315084401860726208787763004985911300, 564085171422241, 36834751054881, 265786306042740395551258923833542319640633054985375422171229960750110719102439102301613133726708430981, 78616327160865, 480782587427450532404815488919616092825910528637996136889167788205389108904255060763094162829867877286294879291136382754360313420838132068894623746020215082654846997781416201990612594611578967733141081788286866791845535729041606744855141555933864377165283338248095560, 
    1984741937021275166721257406612242987235293405082631412421611953025815149369533941603105313156680048848524276041329882453748412624619811051077120937111424165451567254139283238, 2076211109836584743643006813666602705894022748450855757475236467044349003098781849342681706108381220, 2111201651623782884913475179910867452046247974355933709749728879255226990189555084567466038131193989, 565192196950112, 565192196950112, 565192196950112, 
    265783660764111914541556244980219074599402188272702981254962932184620303338385768903057094260920187013, 265751220461005753993843162257540103398796966885230240385066222289660659435507614516313729081362339012, 265751220461005753993843162244123108500636110882457029208402693573726557527147480112388734325306152132, 132875735960437393561945257729544290316199400617296180146062489674384964442074380407561992383733372004, 1461864025804172166982813338753871271471314642338, 265752994540108411252272061361467382189546970026633266357984394373250367223195324709261387785262930788, 
    1978643683645311575188496590646588790616064811147483736863185483200031051732883082320578534694484231954115798533549901580173502081472011362659733470232577338776236591330343974, 731110419564195731373076798820378824998723823010, 265752994540108411252271848460590725947186740043184533195261694608736412718816926991530744815391940292, 1461864025804172166982813338753871271471314642338, 567631740537312, 2078206948827074159375332889422874939590137389076767197795902720528311869811700422715107678737996644, 
    251239652721697, 286424025007137, 145274085835809, 145274085835809, 564600567268385, 564188250407969, 
    567486785393825, 568620656759969, 568483217806497, 567486785393825, 142388102202401, 182710702416187819312595634354649713964514543010, 
    45631079195937, 1461596415838445843446165928985569511505004070306, 36834851816481, 36834851816481, 1461529513368761145097522061466239338860312528802, 1038105570387270466635219360532557730474141494531006707692189950057752106647723891460985526346160164, 
    36834751054881, 989321607749569750738379990335147920483158569472289591737763439250443933398487300940836500965867066978262364981926787685706523822675225587936283995348555787663735885523839782, 564164627105888, 564164627105888, 45631112750369, 1978884747337952134629729879204792949784336375290505937631986258070695446502999381402510266199021063884559568478794520046947675833928593096766328723409919238414155728120964262, 
    36834751054881, 36834851816481, 36834986165281, 1461551814199029293895237237770157240028683044258, 36834751054881, 265751220461002921582585712231441425034812505616828128537106091725726762528973151900012055970606821060, 
    265751220461002921582585052732474200836242977533939340246944485565748864373243502275125179256638877380, 36834851816481, 72019223905313, 72019257492513, 265751220461002921582585052732474200836242977533939340246944485565748864373243502275125179256638877380, 565192196950112, 
    565432715118688, 565226556688480, 74905442321441, 145274186499105, 145274186499105, 154207986922913, 
    37934262682657, 37934262682657, 37934363444257, 37934363444257, 108303241972961, 143075163243553, 
    91433404103568131932107989405854937229602063267, 565192196950112, 565192196950112, 145274186499105, 145274186499105, 1039103489897385333647715559967426470721694953408481929834904565971687462094325748829531855478390436, 
    731110419564195731412768251625114235246324786594, 1461864025804172167022504791558606681714620638626, 567631740537312, 1461551825066880383686554891110541079938916156706, 1461864036693207908492535622386594119531203405218, 145274186499105, 
    145274186499105, 183045214854273533296870477362573741156840252323, 44531332449313, 292216171708600680540126683266424055238778200675284162562738366451503775955294142131871352572948164, 149672233010209, 1461529513352788929998496723580712561679373174178, 
    3880343294172176471769792434163645101475708675294007114254948208222756466024251595705044914795390410677972488433651135771980530398476496839561297658827846942626340321345319, 81914962980321, 290547294545185, 145274320721057, 564085171192865, 564188250506273, 
    564085171192865, 564085171192865, 564085171192865, 1978643683645311575188496590646588790616064811190807196630843264860531480355809822412679126048406708102877152119232321122998374106360189830643375003940467550212200451382689062, 1461864025806835825412678620910508636863373796770, 36834985935905, 
    275742580346025275209528179282281242264944832183647512720891402308691817960880529363972377999912644, 36834985935905]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580578682407008, 580578682407008, 368229959163483808875659170025815986497382778274, 265750998701117921836539516307040573723322637140751136469259050119505247240211944465227087518514051205, 265783439004225734624145485273120907081441486658137271080771675978972215107089454666709908822376872069, 265783439004708896775665392463213821912018517457167757406915753125372513997421822420935438830562474117, 
    580681862285408, 158469397416032, 564429841336416, 567625298151648, 1461529513347805279558919076318739648600095589794, 564429841336416, 
    565426272667744, 565426272667744, 265783439004225734624145485273120907081441486658137271080771675978972215107089454666709908822376872069, 565426272667744, 580613073668192, 565219911010400, 
    580578682374240, 580647401883744, 580647401883744, 580647401883744, 580716121426016, 256629473692336120754385040599383764514766139804504133694386234988788614406406317709385938956569271164103756764774143962370067021973615355146075844369313618274583289943846, 
    158471546998945, 158471546998945, 75479248504339073950171048391661825880178789692262469035702234195840383686552171766340467155723554169710833276663304945997536687306053926938794250283821889991276617160486, 1978658307751508196001678975318213461311629267291875325060185711835874134221411632355604429293295379056704225118545765339916717413116621173675929558888096410582037793608390439, 1877108318434229920971104870761035114202571889840181308321990150220444739798789127269214308375061682116701274991469347955723422280776872494241737301125778726230406457938847769262903292929156014712498820223593411176404490089222257470614510110819624849244198092950760, 158471546998945, 
    158471546998945, 580578682374240, 16641879454910385497850024458770165664584740870729962077226194988769475594157483740845163673971284709, 88031864555616, 580613074061408, 580613074061408, 
    36425756577953, 141978872844449, 141978872844449, 141978872844449, 141978872844449, 282851783739488, 
    39724291461281, 70714758006880, 70714758006880, 281752271063136, 281752271063136, 281752271063136, 
    215987738118368, 286150321768672, 290548372474208, 36354818312288, 36354818312288, 39653353195616, 
    39653353195616, 185542907839763894701950904691730227559917946274, 283744934561888, 71814270683232, 142251736434784, 282851783739488, 
    72913783359584, 72913783359584, 72913783359584, 143351247013984, 283951296415840, 72913783359584, 
    72913783359584, 72913783359584, 143351247013984, 283951296415840, 81709884770656, 81709884770656, 
    70714758006880, 70714758006880, 143351247013984, 281752271063136, 281752271063136, 75112808712416, 
    145550274463968, 286150321768672, 81709884770656, 81709884770656, 154346375875040, 290548372474208, 
    70714758006880, 70714758006880, 8563518823510435908909445239935494456626120098, 14272531372405758373204250773708350635322639778, 14272531372904220773106738678540179320240342434, 79235771795552, 
    730775907099505560393530936465553143467201791906, 283951296415840, 283951296415840, 281752271063136, 286150321768672, 290548372474208, 
    36354784757856, 36354784757856, 141908001687648, 141908001687648, 36355287582816, 36355287582816, 
    16609467118804845791833647426306026642516407484685348973863836475956874854255937867710808652339033381, 142120606769441, 39653319641184, 39653319641184, 145206536570976, 145206536570976, 
    265752994540108411252272061348050387291386114026042089055611872102402986512060962281321351471893850213, 36354784757856, 141907901024352, 36354784757856, 72569982552160, 567631606718881, 
    39653420304480, 145206536570976, 145206536570976, 565426071341152, 1978658779495010857921506726799607886189048659443339760563504402128171071409623755649598519142699761066729546220487374599229886367408112308666248925217645539526399451152230182, 72844862556256, 
    36320929941600, 1978643212360718326897592662703287971240786565707137314887695921102686767736591903790274290808410996536443022555474938406418973323792122902568910189291432414213372578659718950, 36320929941600, 36561447290976, 36561447290976, 36561447290976, 
    142125170177441, 282858229343521, 308182880614109742061387067405084488157637199255304290708859492378642918097288785780397782507043781, 72604310833248, 72604310833248, 72707490711648, 
    308182880614109742061387067405084488157637199255304290708859492378642918097288785780397782507043781, 72845063882848, 72845063882848, 72604310833248, 72638702028896, 72638702028896, 
    72638702028896, 72638702028896, 72707490711648, 72845063882848, 74837725284448, 74837725284448, 
    567631606456737, 567631606456737, 1461685619845278754530431049358269582802549772579, 72638702028896, 143007446206560, 72638702028896, 
    72638702028896, 81709884770656, 81709884770656, 79235771795552, 79235771795552]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [71610128666785, 282713139971105, 565432513792096, 565432513792096, 565432513792096, 282850713142305, 
    36833777975329, 36833777975329, 36833677312033, 36833677312033, 36834986165281, 565432715118688, 
    565432715118688, 565226355329120, 265751220461005753993844546341317621682939675694486723364493120751120303529530818553281907865157833924, 565191962036320, 565260681545824, 565191962036320, 
    565260681545824, 565226355820640, 265751220461005753993844426125054798878990096653554012663640060532278543420564094410304584723453908164, 37460774488160, 143426484439392, 143357697853792, 
    72645146576992, 72645146576992, 283957738866784, 283958007302240, 72645146576992, 72645146576992, 
    72851506333792, 72645146576992, 81716327221600, 72851506333792, 290314567027040, 290555083098464, 
    290555082901856, 290555083098464, 290555083098464, 290555083098464, 290348656494944, 290348656494944, 
    290554814925152, 290554680707424, 290554814925152, 290554814925152, 290554814925152, 290555083360608, 
    290555083360608]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [36842267255073, 256631287657014189269483192926505959467911002723715710844981199713849750818454977478094816777528032130242549200178733961215352577061179482955843373362785080361256631657255, 265783403612227268787808659431459149642327996819893208830666229344550462898858964516783437773049440357, 265783403612227268787808659431459149642327996819893208830666229344550462898858964516783437773049440357, 71607979083872, 71539190401120, 
    16641875742412316777254151964021417623950713855242292983630964005179449700963668201283708157812287589, 16641875742412316777254151964021417623950713855242292983630964005179449700963668201283708157812287589, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 212345400330336, 16641875742412316777254151964021417623950713855242292983630964005179449700963668201283708157812287589, 
    71539190401120, 61848167966877660273688269300874155158971894133002908448549533939933876001744973005056684371788604501289917334793422488965089423106786721696517697808760379554037800786453287, 61848167966877660273688269300874155158972601163774914400664656634570755675325425216127169449339011209482924091514466012175067547955106855238539923218569399126690473670861607, 5731313400432822919761313276378882843890681250, 11440325949328145384056118810151756614840354210, 291929199781153, 
    290829688185121, 290829688185121, 177058418395232, 177058418395232, 141977125521504, 141977125521504, 
    141977125521504, 36561447061600, 177058418395232, 177058418395232, 141977125521504, 141977125521504, 
    423590615976032, 182710702397577907346369928505474813472430097826, 265750994988619797802388814285386488391813846149725795787984382457533678076627053461290398262488806693, 16609467118804845791834306817948756373436563185074879940949117118162664878731757145790668647251653925, 283133106988321, 283133106988321, 
    16609467118804845791834306817948756373247421555584208476173217111262571474281760971538078359309071653, 132875514200551213644534503818597832874809699257546108203319945951832389119124769979601181964010076197, 282858229343521, 1461529513368749706412563928862870940092981068707, 282858229343521, 282858229343521, 
    36842267255073, 318317512631585, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16641875742412316777254151964021417623761572225751621518855063998279356296513672027031117869869705317, 16642889501884443302937788663776494188534713743718286888772381665722885218758738110254010131276376165, 
    72604344387680, 16641875741929390659782189125740798177131772402750003443954080229818868458788699060073646069873718565, 72705274021984, 143074085308512, 143074085308512, 143074085308512, 
    72604310833248, 72636554545248, 143074085308512, 72845063882848, 39619464824928, 39619464824928, 
    180356953278560, 180356953278560, 39619464824928, 145273510955104, 39619464824928, 39619464824928, 
    180356953278560, 180356953278560, 321098740926688, 11774838382263486251612862534281288563900810658, 145273242781792, 145273511217248, 
    145273511217248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [565191995623520, 571892150896992, 571892218071392, 36834851718177, 36834851718177, 36834851718177, 
    281758981490784, 281758981490784, 149817594612064, 281758981687392, 281758981687392, 565191995623520, 
    565226355361888, 565295083227488, 565432513792096, 567494175754720, 567494175754720, 36834851718177, 
    36834851718177, 36834751054881, 732180864850997610578894849654733641819303216546, 732180864850997610578894849654733641819303216546, 11440325949332688660983187555282260284177129891, 132928197518239160296252839338300567627568738030203982572390484604302725882211025864765832604233149764, 
    732180864850997610578894849654735330675605931426, 132936307594016172501722152760385591613218619609479246705550910322496221626871948591694412360839769412, 36842267484449, 318318586373409, 91366501633903549258791849241762937209593283491, 283133106988321, 
    91522607445766636584605418961174153757219919266, 732180854653160467481549638968011160332096013730, 91522608126331370426501688774824178982389847458, 732180855333725201323445908781661185557265941922, 36842368147745, 91522607445766636584895561157881664759149401506, 
    36833912161313, 265750998701117685802270648870982075753059205968440813222327133411682317596057407722768352134093731877, 318318586373409, 70446121224288, 70446121224288, 70446121224288, 
    281758512187488, 37460740933728, 70446121224288, 149817192352096, 281758713514080, 565226321774688, 
    565501300770912, 16609688693064942194413550488509004117522169846150922871886485237695381233705549637544915846991785284, 565226355361888, 565226355361888, 565432715118688, 132875735465436707175583626866669766323324127155409703310851992916263951401008417909863713907123760452, 
    37460740933728, 143288835770464, 1461596415839296730853389699033536807069731524002, 72645146576992, 283957738866784, 1461592234453892017313424744440350107096951819682, 
    72920225810528, 283957738866784, 283957738866784, 283957738866784, 37460774488160, 143426484439392, 
    37426884020320, 730840196221754445833910657133706997674984082850, 37426884020320, 37701762156640, 11512760049210724518026490079853484710388305314, 72645146576992, 
    72645146576992, 354532515645792, 72920225810528, 72645146576992, 72920225810528, 72920225810528, 
    72645146576992, 283958007302240, 72645146576992, 283957738866784, 2127120843387391410897558068663039683119387332195463653408529369482910516506867775193316650516068805, 495132556658784, 
    72645146576992, 72645146576992, 143082685729120, 72645146576992, 72851506333792, 72645146576992, 
    143082685729120, 72645146576992, 1461596415843637510928276701327483584710888659363, 1461596415848954443193825968470770362803463133603, 566531992914016, 566360194254944, 
    37943121292769, 72645146576992, 72645146576992, 72645146576992, 283957537540192, 72645146576992, 
    565432514250848, 72645146576992, 72645146576992, 72645146576992, 290554680707424, 290554680707424, 
    1462216657701427443207918435248570816026561234338, 290554680707424, 290554680707424, 72645146576992, 72645146576992, 72645146576992, 
    290554814925152, 290554814925152, 290554814925152, 81716327221600, 81647607744864, 565191962069088, 
    565191962069088, 281758981556320, 37426884020320, 46360424483168, 37701762156640, 37701762156640, 
    11468158388672479811274186911584855474473272738, 70446121224288, 70446121224288, 70446121224288, 70721200457824, 70721200457824, 
    281758579296352, 70446121224288, 70446121224288, 79379728697696, 70721200457824, 70721200457824, 
    70446121224288, 281758981949536, 281758981949536, 290314567027040, 1461596426387219338222037587658190918608273018274, 1461551824896822276975747262639021718833616913826, 
    183045214849122755164619624817515765599354233763, 290348656494944, 36327373441120, 290555082967392, 36327373441120, 45398352988512, 
    11445857558403357457898035327450540856515757986, 72645146576992, 72645146576992, 290554680707424, 72645146576992, 81716327221600, 
    81716327221600, 72645146576992, 290555083360608, 36361228257376, 145419544300000, 36567889741920, 
    72645146576992, 44531332449313, 275742580346025275209528077816257349133599886173459726917344296642214411439247941244647293790484613, 70446121224288, 70446121224288, 79379728697696, 
    70721200457824, 72645146576992, 81716327221600, 154353084533216, 154352950446560]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b9_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [44538848649505, 44539083530529, 44539083530529, 44538848649505, 44539083530529, 282033461141793, 
    519044880673818367870617757574278685526004337001004603266004933607235501955714699580398231573575877, 2135484335776450652494329980893331141458238489180606585356091983684722958266789725686447189734281797, 234972585769355288166312476553064494542463001528489501505951463158382163333366800715377943245441871456146309400208749059687412947878061344962309656522265238971723853727169040919429009795063430624704614055327738248486054968407744425082779266372995699970112124598761, 141872972466272, 267827178100032633491904496351340897074709294321925239121399051411181546213764597344336388306858225348, 267827178100032633491904496352179459258187263490648057894729026233107818353902506005513338713760935620, 
    267827178100032633491904496352179459258187263493557404898091612112647492788258171096289538766031367876, 268086700524897024081321880116858409418953562033830049716097215573628097675265601503890942243215847108, 267827178100032633491904496351340897074709294324834586124740469005239802908185132827533472922230402756, 141872972466272, 36319856199776, 36560375416928, 
    36319856199776, 282033461141793, 11429175534193259687576444552117471871215601058, 44538848649505, 150092099133729, 571892213784865, 
    571892213883169, 177061644863712, 177061644863712, 141979275102432, 36842267255073, 290829554164001, 
    24263298079706546934003821453176948143197028643, 81922479172065, 81922479172065, 141872972466272, 141872972466272, 36319856199776, 
    36560375416928, 36319856199776, 11440325949327820864264520344175621980939617698, 1461529524151457592853132640770943042876575089571, 1461529524151457592853132640770943042876575089571, 1461518373865247772181260761806842797814764831011, 
    36842502137121, 36842502137121, 291929199781153, 145694019297697, 145694019297697, 91522966783935720501905200462031460505730715939, 
    290829688381729, 290829688381729, 290829688381729, 145694019101089, 290829688185121, 1461685629369166160124587664861066169402376884515, 
    1461685630730295627808341518124268780524406870307, 1461685630730295627808341517681542702279994413347, 36561447094368, 36561447094368, 1461685630730295627808341517681542491172151267619, 290829688185121, 
    11440325938693956333165386317060993159386367394, 177061644863712, 141979275102432, 423600290138592, 1461518373864001611427832901325924648603437007139, 36426158835936, 
    141979275102432, 11440325949337880977804072790535764660636354466, 36842267484449, 36842368147745, 1051177557671194853722871629381885795834744842353054059864042461920527966033122099025587934943193520250000840309361283411962500730715543989780004874412110619178685781630762279, 3462625622495011615410524509355442224181102366558801189892833524043255326986081375073984417543949656312488049011315515065842681724442333411296023662215157098633624372555792166, 
    2071407915806704857173143649619147240638971930522733509157915326812231185138496314899542860742167423633348658059065304635261207143890740980920831739021954403021495363477420839, 1978884747222783456185379191100483388765130552759692159062909161175373963017227322123509295609850297551749768951612288320888437991541760332204659286546943485011581351409725222, 290829688381729, 290829688381729, 2135801135725730665097901476834232933096487679355124185425614317258203524004050609307982889346025157, 81922479172065, 
    81922479172065, 36361731311712, 36567889741920, 290829688381729, 45638595388705, 22847287786815192394392934413734493039693431075, 
    283132872106273, 36842267255073, 283133106988321, 142395484414241, 142395484217633, 1461518362976212030711229932011877520732441313571, 
    36842267484449, 142395484414241, 283133140575521, 283133106988321, 283133106988321, 1461529513358126267079614543866210085576795784099, 
    1461529513347492443113336425808799256917934375843, 1461529513358126267079635095605143798156563088291, 22858351047138830677431803239482183876509471651, 91366501633882704051935777494620274130493146019, 132875514200551213644534503818597832474952094807664371402950375239022837188521007585470128727839602725, 564092586828065, 
    91355699689232245499029236658352545672382677283, 730775907089057361114220664393561139172350133155, 1461518362985516617491241774265124966054404063523, 282858229343521, 564195632881953, 1461529513368760091045895079775260169882419889059, 
    142120875205921, 282858229343521, 1932269682998647193302200343080204111862945463781013818691916463061792872083727143428214206415055549904787776096748983177161836763501659587432020447516010731479313955968807, 282857994461473, 282857994461473, 1978658779495010881948298536857158074196872516290678244898824590925489362907905557380341476143393947333590118338879121779314318307558466137126616356055334390373482386001226534, 
    1978658779495010881948298536857158074196872516290678244898824590925489362907905557380341476143393947333590118338879121779314318307558466137126616356055334390373482386001226534, 142120606769441, 282858229343521, 36567389839649, 142120606769441, 318317512402209, 
    318317646718241, 318317512631585, 1461513484688199852137417721073505378918394265891, 283133106988321, 36842267255073, 431567310758177, 
    267827399859917987289356521017186770752455264120739232986594998351551612591643382695268446951482404548, 16609688693064941272390052738599126436838095433393458492352447711660046201369351479246189891730616004, 267827399859917987289356521017186770752455264120739232986594998351551612591643382695268446951482404548, 150092065808673, 150092065612065, 22880651877387588145923214666291738499149727138, 
    290829688381729, 267827399859917987289355642580417450540019080556619869727023319786279841557205424830419393238771248836, 72604344387680, 72604344387680, 72604344387680, 72707423602784, 
    571892214276385, 267827399859917987289356081369825138464299190535604670159896320025394859957629702052641789769077042884, 72844862556256, 72844862556256, 72844862556256, 213380558751968, 
    143078384470240, 481730391140743824740241801299598365912783096380027679965320244157985495731917954437192782059063065541, 267827399859917987289356521070749930471533447932010535424004781097096795171960719859373276370965704388, 44538848649505, 44538982965537, 44539117314337, 
    143361997015520, 267827399859917987289356521070749930471533447932010535424004781097096795171960719859373276370965704388, 2482762156128, 290829688643873, 1461864025804187743912926824097645057723202576803, 22925253537925832852675517834519852913491707298, 
    22925253537925832852675517834519870505744860578, 22925253537925832852675517834519835321372771746, 22925253537925832852675517834519905690251167138, 5798226440003300162034117761202633712005585187, 22925253537925832852675517834519870505744860578, 72603237091424, 
    3354397805040921975307541445505413680163908101705531687194744670985779913581730925625972379596321466615837397206132682627059306925337791763998522622850921363683515818080008355548389514262378808647554462191898439328640554295046720062879117928476203902439929455778448117400153904977033176155398955193581181491825257351468914442760956063891319517382510040309991974921152113761296426, 22925253519316569923252483092481231833799329186, 284471298975169323160176358146588507288229798313119585918585506156004164475644098520072617930371840453, 72603237091424, 72603237091424, 16641907236287754313950483990952271376546304286484813616414708809475706880560487811102590143760562309, 
    72637596829792, 16642128996173934231361243805386399677662339861701220701512654536587901043479873432270629823798524357, 72603237091424, 72843755260000, 11507228440135187924085906766974158148351821218, 34343191523431195058125799131619681827023226274, 
    34343191523431195058125799131619681844203095458, 241540966556903348016094442032654549733589264338561500865711815612601567742087100944644059073477397293616887570552612857703561783638663427761155671876727754677886774826790, 241540995012533098917532170512120628339099613186500868949024951780709893481829474020919185869017600952092904628266767896467591675973964228671732877578562598383898354931494, 11507228440135187924085906757750786111497045410, 5798215891240189979585117560044506314149725602, 143007446206560, 
    143007446206560, 91522966103370986660028273535286467775434887459, 72844862556256, 22925253537926157372469534161363074867150718370, 72604344387680, 72604344387680, 
    72604344387680, 568490633339297, 72638702028896, 72638702028896, 72707423602784, 567494167765409, 
    72638702028896, 72638702028896, 213380558751968, 495070292216288, 213380558751968, 213380558751968, 
    143078384470240, 424699400554976, 72709640292576, 143078384470240, 5720162964133729974449171324010268872214086051, 91522606786552546612432772217647974779352813987, 
    732180853993946377509376992223476178885988614563, 1983473913172745526191366720185803350047753023151506151178415363009152897733619149470032092507519163912578865526963225488383007605663945532990056900546375377793734121446424358, 72610988165216, 283717220698208, 72610988165216, 265783660764111914541556245033782234717557007622065650297984523127032304683991742362356519136426932677, 
    5720163603409323950946899804545232538429325731, 72645347903584, 283751580436576, 5720162985318301157271268048414693895432077731, 354191199963488, 5720164285303290859211143517115860449058914723, 
    72920225810528, 283957738866784, 283957738866784, 284028404500576, 265783407324242112653080909837740563839032958308366308039525271063801703521198538036705661028040030309, 72610988165216, 
    265751220461003865719681402674602400110055831600649361614411585622286621359592057403431000870672864356, 72645347903584, 72920225810528, 72920225810528, 283957738866784, 72851506333792, 
    72842647963744, 283957738866784, 267829173939000817668971839906450698048026863826429474039859254449712279445935080263393780913385057988, 267829173939000817668971839907289260231504832995152292813189229271638551586072988924570731320287768260, 267829173939000817668971839907289260234628720553191769909096823006188512701221669949166776442893184708, 267829173939000817668971839907289260229161917329534873153994605694871502806798110169302147595551977156, 
    284438609130321815391684397518488748552095016567690933950615596200876238002252585319661116640786449284, 267829173939000817668971839906450698048026863829338821043200672043770536140355615746590865528757235396, 74804441385056, 282751709410638931287782119234815618531498132205269874345240580568509758617992135891233810913956015812, 74802260346976, 74804441385056, 
    74804441385056, 74804474939488, 215548577712608, 74802260346976, 145171507447904, 39618391083104, 
    180360179747040, 267829173939000817668972719202641433656522659049838908135951443193208195060403518445931139959510609604, 268348214836466031797398759630235131412040269713720144900640399586012109480577783882556983682741120708, 39724693719264, 74908663548128, 145277810378976, 
    145277810378976, 145277810116832, 74802260346976, 74804441385056, 74804441385056, 74802260346976, 
    74802260346976, 74804441385056, 145171507447904, 39618391083104, 180360179747040, 321101962152416, 
    11774838382263161731821264068305153930000074146, 74837725284448, 74837725284448, 145206536570976, 145206536570976, 74837725284448, 
    74837725284448, 74837725284448, 145277541943520, 39724693719264, 286514784692988995531271664605112892427522164224121537650494798109390696736737586837345998634282960196, 74908663548128, 
    2077193189339841670887114191044738779733917287119546276100448193532294369603737357516707172844906052, 145277407725792, 145277810378976, 6065825838528597017503210683877967485641188770, 5720162974684517439053241406674226588317417891, 36567389839649, 
    36567490502945, 75052746279392, 75052746279392, 145419544300000, 145419543841248, 145419544037856, 
    286156898437600, 44126632943905, 79235771795552, 79235771795552, 79235771795552, 79235771795552, 
    79519449352544, 519044880673818375073812044849244570435508172421461975002224139687403709722292085544658200214714565, 79235771795552, 2040724893673154581851846193619226953378091237102747148230732600146915048739349312827603048367936237442007504073479398274636042994237156909423722764786724757268002442620959782, 184758226258144, 219977628518624, 
    79235771795552]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 0, true⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 128, ⟨2, [], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_0R (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (hM10 : M 1 0 = some (some 2, Stmt.write 0 Dir.right)) : False := by
  let m : Move := ⟨2, 0, false⟩
  have hm_cmd : M 1 0 = m.command := hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  exact tv_b8 M hG hm1 rfl hv (by simp)

private theorem solve_0L (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (hM10 : M 1 0 = some (some 2, Stmt.write 0 Dir.left)) : False := by
  let m : Move := ⟨2, 0, true⟩
  have hm_cmd : M 1 0 = m.command := hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  exact tv_b9 M hG hm1 rfl hv (by simp)

theorem step_proof : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1.H2 := by
  intro M hFirst ⟨d, hM10⟩ hRun _hUsed hForm hMissing hLoop hHalts
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
  cases d with
  | right => exact solve_0R M hG hm0 hv hM10
  | left => exact solve_0L M hG hm0 hv hM10

end OMA.BB4H1

-- Step BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H2
-- Credit: @pageman (adaptation); certificates from @ubuwaits / @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1.H2 :=
  OMA.BB4H1.step_proof
