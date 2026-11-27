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

private def nb11_2 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_6 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_6_14 : SearchNode := nb11_6.atMove 14

private def nb11_10 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private def nb11_14_6 : SearchNode := SearchNode.mk ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

private structure BranchChecks1 : Prop where
  vb11_2_0 : (nb11_2.atMove 0).Valid
  vb11_2_1 : (nb11_2.atMove 1).Valid
  vb11_2_2 : (nb11_2.atMove 2).Valid
  vb11_2_3 : (nb11_2.atMove 3).Valid
  vb11_2_4 : (nb11_2.atMove 4).Valid
  vb11_2_5 : (nb11_2.atMove 5).Valid
  vb11_2_6 : (nb11_2.atMove 6).Valid
  vb11_2_7 : (nb11_2.atMove 7).Valid
  vb11_2_8 : (nb11_2.atMove 8).Valid
  vb11_2_9 : (nb11_2.atMove 9).Valid
  vb11_2_10 : (nb11_2.atMove 10).Valid
  vb11_2_11 : (nb11_2.atMove 11).Valid
  vb11_2_12 : (nb11_2.atMove 12).Valid
  vb11_2_13 : (nb11_2.atMove 13).Valid
  vb11_2_14 : (nb11_2.atMove 14).Valid
  vb11_2_15 : (nb11_2.atMove 15).Valid
  vb11_6_0 : (nb11_6.atMove 0).Valid
  vb11_6_1 : (nb11_6.atMove 1).Valid
  vb11_6_2 : (nb11_6.atMove 2).Valid
  vb11_6_3 : (nb11_6.atMove 3).Valid
  vb11_6_4 : (nb11_6.atMove 4).Valid
  vb11_6_5 : (nb11_6.atMove 5).Valid
  vb11_6_6 : (nb11_6.atMove 6).Valid
  vb11_6_7 : (nb11_6.atMove 7).Valid
  vb11_6_8 : (nb11_6.atMove 8).Valid
  vb11_6_9 : (nb11_6.atMove 9).Valid
  vb11_6_10 : (nb11_6.atMove 10).Valid
  vb11_6_11 : (nb11_6.atMove 11).Valid
  vb11_6_12 : (nb11_6.atMove 12).Valid
  vb11_6_13 : (nb11_6.atMove 13).Valid
  vb11_6_14_0 : (nb11_6_14.atMove 0).Valid
  vb11_6_14_1 : (nb11_6_14.atMove 1).Valid
  vb11_6_14_2 : (nb11_6_14.atMove 2).Valid
  vb11_6_14_3 : (nb11_6_14.atMove 3).Valid
  vb11_6_14_4 : (nb11_6_14.atMove 4).Valid
  vb11_6_14_5 : (nb11_6_14.atMove 5).Valid
  vb11_6_14_6 : (nb11_6_14.atMove 6).Valid
  vb11_6_14_7 : (nb11_6_14.atMove 7).Valid
  vb11_6_14_8 : (nb11_6_14.atMove 8).Valid
  vb11_6_14_9 : (nb11_6_14.atMove 9).Valid
  vb11_6_14_10 : (nb11_6_14.atMove 10).Valid
  vb11_6_14_11 : (nb11_6_14.atMove 11).Valid
  vb11_6_14_12 : (nb11_6_14.atMove 12).Valid
  vb11_6_14_13 : (nb11_6_14.atMove 13).Valid
  vb11_6_14_14 : (nb11_6_14.atMove 14).Valid
  vb11_6_14_15 : (nb11_6_14.atMove 15).Valid
  vb11_6_15 : (nb11_6.atMove 15).Valid
  vb11_10_0 : (nb11_10.atMove 0).Valid
  vb11_10_1 : (nb11_10.atMove 1).Valid
  vb11_10_2 : (nb11_10.atMove 2).Valid
  vb11_10_3 : (nb11_10.atMove 3).Valid
  vb11_10_4 : (nb11_10.atMove 4).Valid
  vb11_10_5 : (nb11_10.atMove 5).Valid
  vb11_10_6 : (nb11_10.atMove 6).Valid
  vb11_10_7 : (nb11_10.atMove 7).Valid
  vb11_10_8 : (nb11_10.atMove 8).Valid
  vb11_10_9 : (nb11_10.atMove 9).Valid
  vb11_10_10 : (nb11_10.atMove 10).Valid
  vb11_10_11 : (nb11_10.atMove 11).Valid
  vb11_10_12 : (nb11_10.atMove 12).Valid
  vb11_10_13 : (nb11_10.atMove 13).Valid
  vb11_10_14 : (nb11_10.atMove 14).Valid
  vb11_10_15 : (nb11_10.atMove 15).Valid
  tv_b11_14_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  vb11_14_6_0 : (nb11_14_6.atMove 0).Valid
  vb11_14_6_1 : (nb11_14_6.atMove 1).Valid
  vb11_14_6_2 : (nb11_14_6.atMove 2).Valid
  vb11_14_6_3 : (nb11_14_6.atMove 3).Valid
  vb11_14_6_4 : (nb11_14_6.atMove 4).Valid
  vb11_14_6_5 : (nb11_14_6.atMove 5).Valid
  vb11_14_6_6 : (nb11_14_6.atMove 6).Valid
  vb11_14_6_7 : (nb11_14_6.atMove 7).Valid
  vb11_14_6_8 : (nb11_14_6.atMove 8).Valid
  vb11_14_6_9 : (nb11_14_6.atMove 9).Valid
  vb11_14_6_10 : (nb11_14_6.atMove 10).Valid
  vb11_14_6_11 : (nb11_14_6.atMove 11).Valid
  vb11_14_6_12 : (nb11_14_6.atMove 12).Valid
  vb11_14_6_13 : (nb11_14_6.atMove 13).Valid
  vb11_14_6_14 : (nb11_14_6.atMove 14).Valid
  vb11_14_6_15 : (nb11_14_6.atMove 15).Valid
  tv_b11_14_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]
  tv_b11_14_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem checkedBranches1 : BranchChecks1 := by
  constructor
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1149f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x149766d76111ba053a7b614bf05150, 0x2101044210860, 0x2100844210860, 0x2101044210860, 0x110ebf0e6ffcba35cf1570114c2f267f, 0x21020446108e0,
      0x2101044210860, 0x504044210860, 0x504044210860, 0x15edf06a1000ecf000000140bf1267f, 0x10080012004001100040802020100802020080da2, 0x504044210860,
      0x1023000408c001023000f300f33cc0445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x1490ebf971111a8f57000000f7f1014ff, 0x1e6f30079bcc00f3f30001e60f30798445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x304044310860, 0x504044210860, 0x504044210860,
      0x14a0242f496a49111dc000004610267f, 0x9040446108e0, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x88b000222c0004bf000f300f33cc0445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x3db3000f6cc001f53000f300f33cc0445800079bcc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x1132d8f13a7328f30cf242405300001ca,
      0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x110af000001d1d00f5f5028131bf26bf, 0x21020484208e0, 0x10479041d40cf4c3fb5f5074437443, 0x10003700f5074437443162c7f172f27ff, 0x1042a0f930e0fb540df004304300c3084,
      0x13a4f24017407401605eeff4042a0f, 0x2108048408421, 0x10f50161172f26bfd312c7f40ef5432af, 0x21010486308e0, 0x21020484208e0, 0x11d3a4f5effb5f5004304300000001d00,
      0x1000e0ff500000162c7f172f27ff04004, 0x1930e0fb55f0f004304300c3084000, 0x12424065000016f45f1f0041044c4f, 0x8800220020014000420900804020020800827a2, 0x135df35df253f0fcfcc8328f5757030cf, 0x1a60d61e2f00013a76906690614ff40ff,
      0x132bf0410f214f214f013076076000010, 0x1ebc1307983cc001023000f6cda94f300f379809a3f8f303cc0f4e6007980222da942d90000f303cc3a45, 0x1217f0000026cf12bbf2bbf5f2f032bf, 0x10800420020010800440101006030021000837a2, 0x14c6f5f3f0399f38df4c5f4c3f217f, 0x10005f5f311f4c7f311f273f5f4f4c6f,
      0x14b5f4c8f15f9f5f8f5f7f0003a5f5f6f, 0x20800820020010800440101004020021000827a2, 0x101d1d0ebf26bff5f502835ef15faf, 0xf3f3001e9cc00f3f301e60007d4c0011160007d4c1e63cc00f33cc0798f3001e6f301e6f3001e704c64, 0x1f507443744310af251f31ff208f327f, 0x1162c7f172f27ff040041d0ebf31bfb5,
      0x143010208f840fc137198f5074437443, 0x218042408421, 0x218042408421, 0x801020041000140004408010100800210008a7a2, 0x116040ff004004fc930e0fb59807643c3, 0x1e60bfbd76701313a81e4570747974f4,
      0x2018050408421, 0x1fb127f2813001e01815fcf5fbfb40b4, 0x100044001020010800500100804020020800827a2, 0x106063d032cf0b40b43b9a35ff15150a5, 0x19a0600000a00a1fb280ffb15014c406, 0x218050408421,
      0x10bb0994c9f8b3a4f7ef60240140d3f06, 0x139cf1fff05432af10ff0910ff09000, 0x105fdf0411f23df01f9f4caf2a1f40ef, 0x1293f672c7f7e150202f1c6f32bf1c6f, 0x1761100000000000584458440000d40c4, 0x1f53000408c001f53003cc0079f9800f6cc0081183cc0f300f3798081366001e60f31e7e6001e704c64,
      0x3db3000408c001f5305c4fc0fa98000f33cc088b0b8a0730f30798007d5b307980f31e7e6001e612d44, 0x15fef0132bf0410f410f214f0d349760, 0xee6d04d6503b9b4135940ee6d04d6500ee729b59400ee88f5667955d33ed4aef40a0001dcd651dcd662a05f20000ee6b29dcd660c388ff2abadf0f3b735943b9aca0003f5476a07735cf9aca1dcede55d33fbb6b28077394dbb86b280ee6b639aca0ee7a0eb2800ee6f07dbba748, 0x127ff040041d00b5f50000032df102bbf, 0x10800420020010800480102006030022000837a2, 0x14cbf600f5fff3a6f00000162c7f172f,
      0x1004cef0602f04cdf14ccf601f1103a7f, 0x200400000401000004004000004010000002000010004000020040000200040000220001000040002040400020000400008000020001004000001004000010040000010040ad2726, 0x20800820020010800480102004020022000827a2, 0x20800820020010800480102004020022000827a2, 0x1f500f403d1610298f040040930e0fb5, 0x20800820020010800480102004020022000827a2,
      0x119df251f603f208f0001d8b26bf1d5f, 0x1b40b4b412bf172fd715010bf43e943, 0x10071110e0ff50954495441811e5f241f, 0x994d73003cfcc0079f9f98001116000445800088b0f303cc3cc07983d3b69cc1e60f307b66001ef98184, 0x218042408421, 0x218042408421,
      0x218042408421, 0x1b4e61b8ffbd76707643c343010208f84, 0x801020041000140004808020100800220008a7a2, 0x1013a4a826e45409579950718000b40d, 0x1ae0131e00018000b407b4e60bfbd767, 0x10c303d01611298f04004143f930e0fb5,
      0x2012050408421, 0x2010850408421, 0x13a8f145fab0abab1b5f0f2f10ff0daf, 0x1108fb08ae01a6f10df281f2d145f1e5f, 0x2010850408421, 0x10e0fb5ae0a500001811e5f298f66066,
      0x2010850408421, 0x108ae014c3069a061601004c404143f93, 0x818050408421, 0x1141e061c6f06000066c466108fb, 0x218050408421] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1b8051300cdf13af0d0f0c8f149f0c8f0, 0x14813b383030303065237253e853e86d, 0x10028139613138937e437000003522213, 0x100d32028348a3b3040304030140140a5, 0x10cdf140140a500a4130130026e404000, 0x11e1f4a0a16bf0a0a12bfbb0ddff6085,
      0x14d4dab0ab0c3f14af6e10ff9800dff4a, 0x1195f113f10ff10ff03c9a3c9a145f4d, 0x103c9a3c9a145f0229f0dafab0edfabab, 0x109a04deb4d1012bf120f104f6e104f98, 0x100024020080012000404800100000024000805a2, 0x1ab0d3fab12bf0127f10ff104f009a,
      0x1e8858585015ff853c03c0145f0010df, 0x100a80f733c6330a3d5a30c7ec730c5aa, 0x1f600c5f8e0ea2cea2c0cff232323c5, 0x14a0dff6e113f6e0a00a0a12bfbb0ddf, 0x113013540826e4040c5c5f8127f4a1e1f, 0x106d0c3f14af2d189f980c500a80a5000,
      0x12d10ff10ff004d4d4d151ff91f5ff90, 0x101b5f0daf145ff91f5ff9ab0abab183f, 0x1f90f9604f029ff26df0e6f2d0e6f9800, 0x1538553850ea2cea2c118f04d3a9f4d0, 0x1000033412f330a3c6a3e5c7e52a00caa, 0x1023b448b400202d30a3b30403040300,
      0x12702650316ef035383533454230523, 0x10a5065237253e853e80b80513023112f, 0x11414650300353053345423052302ca5, 0x17465037053e853e858b8051302c1427, 0x126e4040c50d0ff80eaf0c5f530144814, 0x1fe540058a0c5a8000a500013a4135408,
      0x15858106fa98d111f0b60006500053053, 0x10130138a00dcfca0290d4f000d4f580, 0x1fe54197f058a0118f0000a5000f80f8, 0x1131acf138a0eab66363636500053053, 0x1eaa86343630000f80f88b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1254f1129f174f0e8f1139f217f00d2f0, 0x2101842310860, 0x2101044210860, 0x101daf174f0605f19e0117f20ef117f1, 0x21030486108e0, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44,
      0x11daf010016ef0000001607f0606f1daf, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0x480012000801020040804400100802020080da2, 0x11000120ef9e00000148f11f0f131f0, 0x2080082000a01020040205400100802020080fa2, 0x3d77a050000165a0bc0003d77a0500007ea8ed400009502f9c1dbe8ef65f3594773595dcd82cd6577536165000ee6c166b2810c388e83b7d255f2940010c388d0003bd664ca3b9acdb9aca01dcd66dcd65ee6b287735cf9acbdcd65ee6b2bb9acaee6b2bb9acaee6b89c80ad28,
      0x3db3000408c001f5304d5c80fa98000f33cc088b09ab9f30f3079800798f307980f31e607981e612d44, 0x10116ef275f000001acf608f1acf10f0f, 0x4004000010010000008040000020100006450000200200000118000001000a000024000322802000010020000c00040000050004000200002000800020000400040001000a9f9c26, 0x28000a000801020040804400100802020080da2, 0x1ba00d2f0000148f1acf1f0f10161f00, 0x1080042000801020040804400100802020080da2,
      0x1117f45413f4511cf0eefe573d3c720ef, 0x10000005533333328dfba0e6f7302220, 0x107302e72000001c5505500e517ef0039, 0x100f4e500107f00000002533033c30eef, 0x1030313ff59a634a4232323000000250, 0x1006306335222054b3b38403030303803,
      0x100630630f7f2732054a6b3003189f03, 0x10750063063942732054d3b384037503, 0x1da87a420d5f20000007307300a6a4075, 0x100d5560c70e2d1f00e4f38129f384ce5, 0x1000a6d5d5660176f001401404b451973, 0x16a011dfd3560c76a414f0140140177f0,
      0x100966de500d5a466fa06a00000e545e5, 0x10b60354034c59e534a4236823014014, 0x10300630633522205454b384030303, 0x17503000000f7f2415f20540b3003189f, 0x175181f750063063942372054d3b38403, 0x1da73a42132f2000006c370370a4000,
      0x10d500c700c7f088274cff19ef4c0eef, 0x100000d50660176fae000000450019ef, 0x14504d1fd30000c74d0f00140140177f, 0x11401400960000d5a466000000001c7f, 0x1250f25ef129f2e9feb282f3aaf98003, 0x1138f360f282fae02eaf2a2f2eaf360f,
      0x12e9f4d2f2a2f609f280f239f280f150f, 0x1129f2e9f0282f139fae000c4f00c4f, 0x13abfae00000154f2a2f32ef360f0280f, 0x125ef4d2f03abf0e8f282f0dbf2a2f, 0x1003abf139f0000c4f00c4f25ef4d3f, 0x10030000154f25ef32ef2a2f011ff129f,
      0x11570885c881277f12afcc412e0fff, 0x2101842310860, 0x2101044210860, 0x21030486108e0, 0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0x1113f000000160af0417fbc0bcfc0416f,
      0xf8c1300f33cc00102303e2c80f6cc000f33cc088b07c5ccc07983cc00798f307980f31e607981e612d44, 0x11154f57000000cef112ff14ff0bc0100, 0x480012000801020040804400100802020080da2, 0x2080082000a01020040205400100802020080fa2, 0x8000400021e0100000080400000401000000804000008010f00040000400040002000100004021e000400040002002000002000080400021e010f0080004000010000100018095727, 0x10001113f167f000005c2e9f5c1461000,
      0x3db3000408c001f5304d5c80fa98000f33cc088b09ab9f30f3079800798f307980f31e607981e612d44, 0x4004000010010000008040000020100006450000200200000118000001000a000024000322802000010020000c00040000050004000200002000800020000400040001000a9f9c26, 0x28000a000801020040804400100802020080da2, 0x1c32220232323000000cef7c12ff10ca, 0x1080042000801020040804400100802020080da2, 0x1059a634000055333333250f370e6f73,
      0x1000254f1129f174f0e8f1139f217f, 0x704042310860, 0x504044210860, 0x1b3003030303803030300f0f01daf154f, 0x1b3003189f030102f63e96335222054b3, 0x10b300375030956395630f7f2e320540,
      0x10e3000007507508463d363942e32054, 0x133331a1f07373c32220095ac95a40e3, 0x105533333300073c322200d5f00005533, 0x15d010af1a1f0e5279fc31aaf39570000, 0x1d9451a6f171f6d8746e39be3000001c, 0x1110f000079a60000f8f00da003a02945,
      0x11a6f381f6d2b7f461146f1fbf0950950, 0x4000212220000000100000000800000000000010020000000000000008800000000000200020000000000000800800000000000010020000000000000008800000004000272a0000001010000000000000040000004000000000090000000000000010000001000000001000000002000000004000004000000000090000000000000001000000202000119500000008000000400000000012000000000000002000004000000000200000008000000000800000010000000012000000000000000200000200000020000000100000000800000004000000001000000080000000200000004000000020000000020000000080000004000000001000000100000000020000000080000013487ffd6bfc7d72e, 0x1250f0129f0eb00980380000cd60bfcd1, 0x40400000021000000404000000410000400062281000188a0200000040200188a0c450020000400010080000200311400200cc5062281000188a0c45062280800000100108f9f27, 0x10450e300d500c70000e4f3800000000, 0x10222f001ed5d500176f0014441444,
      0x1e300000c7105f0014123f1409177f, 0x10000d500fa0001b44d344110f452c4f, 0x1376a73c32f3202368230146614a4096, 0x1e5b3f403189f03034000093330331a6f, 0x1f47520ef75059e50e500f7f20211cf54, 0x12f320030a4028df154f00011cf37e573,
      0x1030b603043361f439333c3330370730, 0x11502ebf6310bf633522205454b300303, 0x1110f3acf258f418f00da6a60181f0f8f, 0x1d363942f420540b30037503095449544, 0x1009579950700b017bf00a60000008463, 0x100003300330331a1f0eefa673c3202,
      0x10017c139f7c021af10e6f0c3f991132f, 0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc0010230b64000f6cc0016c800088b0f5dccc3cc03cc00798f307980f31e607981e612d44, 0x1033025339b331a6f0eef6a73c32e7200, 0x111af001a1f5de5fcc31aaf139f5701a,
      0x145011cf0eefd573f4c70f5f0000007c, 0x1011cf0eefe573f4c7000da0730732945, 0x16d269f4660cf146f00d30eef000450, 0x10000000990106fcd1c7fcd01a6f0faf, 0x10fcc41e2f000740e740e0250f400e5, 0x10277f12afcc412e0027000000000340f,
      0x1ebc1307983cc001023079a5f8f303cc16c800079888dd900b640003cc798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc0f31e6016c800079bdb5d90408c001e60798f307980f31e607981e612d44, 0x178e3e3e3005656033333300001885c88, 0x1ebc1307983cc0010230b64000f6cc0016c800088b0f5dccc3cc03cc00798f307980f31e607981e612d44, 0x10c4f177f00000d5000176f0095449544, 0x1b9e397e3011df0560331a33014311f14,
      0x1146614a40960c300d50000007644c444] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1c7268f100cdfaa0d0f1f8f149fc50, 0x2100844210860, 0x12a73d62220133313f3383946a941aff, 0x2101044210860, 0x15529df0e56b003900000055333333117, 0x504044210860,
      0x10c33303383179373862e72000001c550, 0x100001f4dc01aff83e5833dff86110000, 0x88b000222c0002d907b2940f31e6016e294079bdb652840994a1e608132947980f31e607981e612d44, 0x180006008004a031209102004008948201229a3, 0x1ecb4307983cc00102307b2940f31e6016c800079bdb6528408c001e608132947980f31e607981e612d44, 0x100cff232323c533c5aa285858500cdf,
      0x10476447643803030300343433232323, 0x1476465031a4f035396533460df230523, 0x10064064003b603e8023402302304764, 0x10470470650362f2753253254b80513, 0x127af27cf2ecf135bf0d6f3adf0d6f, 0x2101044210860,
      0x1000169f22bf265f110117ff2c8f131f, 0x2101044210860, 0x100104002100080402010100404008080202011a3, 0x100824000840011000404800100804024100805a2, 0x1129f001f0f40df000001190f19bf190f, 0x100804000840011000404800100804024100805a2,
      0x11acf000000231f19bf019bf4d4f0129f, 0x100000190f1c4f190f103aef169f132ff, 0x1000140005000802030101004040080c0202039a3, 0x100024020880012000404800100804024100805a2, 0x1001a5f3eff000129f060ff1acf60ef00, 0x106523117f230c3303aa538553850000,
      0x105230064064380303030003433232323, 0x1023b8230000065030035305334419f23, 0x1253254b805130064064003b603e80234, 0x173842220858585015ff000065270053, 0x1c7000c5aa7443744355333333119f073, 0x100cff232323c509409403303310d5083,
      0x1ebc1307983cc001023000f7439a0f379807d4e06bf8f303cc0f4e6007980f7439a1023000799e60f6a45, 0x164476438030303115f0343417232323, 0x16447646503003530533417230523047, 0x1b664003003e80733413ef23234f23047, 0x196472765000530537354b8051309464, 0x102ecf135bf0d6f3adf0d6f00c5ff5047,
      0x1088210412121, 0x1c5f8132ff2c8f265f017ff0131f27af, 0x1088210412121, 0x1c500a80a500013013540826e4040c5, 0x1145fab0abab183f010ff292f012df, 0x113cfd713cf0001b5f0145f0f2f1f5f,
      0x1118f004d5f018e6113f3db40b4b4610f, 0x12817ff0fdf131f13013a706142f24240, 0x10131fb40b4126142f26240ead3434343, 0x1088210412121, 0x104030aa538553850ea7a430643017ff, 0x10000c7010046304630202a30d3b30403,
      0x21b37307983cc007a73086ce36507987983cfdb51b28f303cc0f4e6007980f736501023000799e60f6a45, 0x10533402305230230c83940941330330, 0x3db3000408c001f5306bf940fa98000f33cc088b0d7f3730f3079800803f947980f31e7ed981e612d44, 0x1053054b805130230000650316ef0353, 0x103030300034023232300270356520253, 0x1283f13013130a117fe4240e964956438,
      0x10a434b923b823014631463a5191f1a4f, 0x18813548926e40409464b664003003e8, 0x10d0ff80eaf0c5f530149614a4a500013, 0x10c5a8000a500013a413540826e4040c5, 0x10b6028065000530533b5414bf0513, 0x10290d4f000d4f5805858106fa98d111f,
      0x10000a5000f80f80130135800dcfca, 0x106436500053d3533b5414bf05130118f, 0x1430000f8d3f81a7f13fb1300eab643, 0x1eaa84312cf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x153109f53feb6ee058a00c8f149f0c8f0, 0x113013a7940c6f24240652eef2edf0c6f, 0x12edfe424014631463282eef19bf19bf, 0x124014631463a5128df19bf13081313a8, 0x20509504214a1, 0x1630630611f5419bf00d3eed62eef4d6f,
      0x10a51e5f106f5413013a4a826e44d6f00, 0x1044804b399033a8f0300cdf13af14014, 0x143043553333330252573762220d32a32, 0x12000001633321f330425047302b5200, 0x1e7b5e3004304384338333025c37302e7, 0x185bd850cdf0000168308304f40400,
      0x13522213013b3d30303030858585015ff, 0x155333333017737302220c5aa96499648, 0x18e0ea2cea2c0cff232323c50939393, 0x16e113f6e0a00a0a0bb0ddff600c5f, 0x1081313d30e418bf0127f4a1e1f4a0dff, 0x12d189f980c5f8c5c596499648a500013,
      0x14d4d4d151ff91f5ff901abf6d0c3f0, 0x11f5ff9ab183fabab02d10ff10ff014af, 0x102d4d7f9800183f1b5f0daf145ff9, 0x14d3a9f4d612ff929fff901cff026df, 0x1330f15085172f850ea2cea2c118f17df, 0x1880f9f88c8172f012eff0003bc4416f,
      0x100024000880012000404800100804020100805a2, 0x113136503221f035305334a42305230aa, 0x1930d1f93c333833301707302e7201327, 0x12313013065e81e853053b3a4b805200, 0x100024020880012000404800100804020100805a2, 0x1481855d32a320840b30033a8f030230c,
      0x1146503221f0353845334023052302c18, 0x1147465e80e85305300b805202c142714, 0x1104f0104f00172f153f11bf001448, 0x100eaf0c5f00fff00fff1a0f11ff014af, 0x10960960a500108f13013331fd326e40, 0x108a0c5b6013a76500053053fea40058a,
      0x1003aff00d0fc50000f80f80130130460, 0x111bf05e162f5e000005e162f5e195fc3, 0x1a80fbf5a0fbfa5a4054130130026e4, 0x16511ff014af53053fe0197f058a0118f, 0x1f814af000001acf1e4f8a0eab6636363, 0x1eaa8634363f811ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x153153a7b614bf052801f8f149f0cff0, 0x2101044210860, 0x113a6f133713a70613f24240651613a5f, 0x2101044210860, 0x100800120040011000440021000804020100805a2, 0x127bf2813081313a81e45700000284c8f,
      0x20509504214a1, 0x101d3101163aaf16240140140a50dff, 0x504050210860, 0x504050210860, 0x9040504208e0, 0x1106f5413013a4a826e4160000054614f,
      0x12323c5e8c5aa278585850140140a518, 0x164380303030a334349423232300cff23, 0x10320df0353a35334962305230476447, 0x103b3030a3b634023352304764476465, 0x165b30ab3530532796b805350064064e8, 0x1a32353e853aa6585658500cdf470470,
      0x1064380303030a3a3349423232300c23, 0x1000650330af0353a3533402305230064, 0x10064064e80383030a3b634023b82300, 0x10230cdf0000658308353275300b80535, 0x12a3f1cff332f893789a7d32f0f148f24, 0x1615f188f67188f1d84332ff5f50148f,
      0x1181cff18f5004304310af4d8f2a3f, 0x1043043892a4f1c1f2a3f581ccf58188f, 0x14d8f0363fc32f0f262f2a3f262ff50, 0x1f418188f18262f0043043374d9f2a4f, 0x185015ff230000891ccf1c1f2a4f58058, 0x1aa000035222138313b3d303030308585,
      0x1a33434023232300cff232323c5e8c5, 0x15334023052304764476438030303115f, 0x1233523047644764650313cf0353a3, 0x1053509464b664e80333030a303423cf, 0x102424004796472765330335305300b8, 0x1002400c5f3df5f5f528000133713a7d3,
      0x11313d30e4160f000000000893789a7d3, 0x1012dfc5f8c5c59618960a5001a3f1308, 0x10f2f1f5f145fab183fabab0010ff0, 0x13db4bdb4b400d7000183f1b5f0145f, 0x1a70024240118f7a233f0233f18e6113f, 0x10ead34343432817ff0fdf131f133713,
      0x14306431817ff13df131f00002602624, 0x153a35334a42305230aa658565850ea7a, 0x100538353b3a4b805350e800006503003, 0x1a32d320830b316031603023027013650, 0x1035da3a334023232300c23063387f63, 0x1138913130117fe4240e9649564380303,
      0x1b923b823014631463a5191f1a4f283f, 0x10026e41609464b664e803a4030a3034, 0x100eaf0c5f650149614a4a58805413013, 0x10960960a500108f130131d0fd326e416, 0x100c5b601306500053053a7a414bf0528, 0x110100d0fc50000f80f8013013a7a50a5,
      0x1e60079f9800f4e6003cfcc1e60f307981e63cc0f300f33cc03cc0f307987981e61e679803cde61026865, 0x1e60079f9800f4e6003cfcc1e60f307981e63cc0f300f33cc03cde6007987981e61e76c803cde61026865, 0x1130026e41605e05e000005e05e1d0fc3, 0x105280118fa813cf5a13cfa5a4054130, 0x10eab643064365d3022bf530530014bf, 0x14312cf43f8d3f822bf0000a5fba5145f,
      0x1eaa8] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x16ae70d9034b623232300c8f0c8f0c8f0, 0x1840f30f302a02a00e30be306ae5a6, 0x10b4500e500000000000e3d6e308441af, 0x1a65620cf333333059380303030000045, 0x133333300d3fbe0d3f0d3f78e3e3e300, 0x10edf0333fbe676778e3e3e3005656d6,
      0x10edf0caf0290046a60d3f20cf1a137f, 0x17c143f00255ff6073013af0d3fcc0d3f, 0x10fc0b8000255f2f1f617f1616f7c185f, 0x40800108040011000500024008040021000845a2, 0x1f40303030a60a60000000e53bc30e0f, 0x1b3003a6030dae5c3e57335222048d5b3,
      0x100cd0cd0010100c30108fd32252048e5, 0x1f5300798f307b753007987d4c003cc1e607d4c1e60079f9803cde6007983cfcc1e9db3003cc0799327a5, 0x1e6000798f307b660007987d4c003cc1e607d4c1e60079f9803cde6007983cfcc1e60f3003cc0799327a5, 0x16d00000880f9f883bc4001502000100, 0xf300798f30798f3007987d4c003cc1e607d4c1e60079f9803cde6007983cfcc003db3003cc0799327a5, 0x10362f880f9f883b035ff115026d46,
      0x801000040011000500204008040021000845a2, 0x173352227c48d5b3003030300001140af, 0x40801000040011000500204008040021000845a2, 0x40801000040011000500204008040021000845a2, 0x1a6108fd32020480b3003a6030d5e50e5, 0x14b1919190185f03a04545450680d5a60,
      0x1000001919002c9f56c3f30f30680008b, 0x100a3a3a335222048b3b3f403030300, 0x10e5f116af1c7f16af0041bf4daf1e8f, 0x2021848c409e0, 0x1048184fb30037503002c3f010e5f618f, 0x2021050840960,
      0x10011cf011cf00103b0f00a30a3d32252, 0x40020000040020000400200000400208004000200004000280040002000040002800060002000080008000100020000400040000020040000020200000100200000102018faf26, 0x1e3e300f9f056c433333302000364f00, 0x122ff0f9f22ff560333333020006778e3, 0x148b3b30030303001215f6778e3e3e3, 0x1024060840960,
      0x10edf156f0000000a3a3a3352221cff, 0x10b30037503000227f00137f0137f237f, 0x1156f560f37bf300a31e6fa3d32832048, 0x1330daf0eff737302220000000001900, 0x10987c07c0024bf11fff0000ba553333, 0x40801008040011000500204008040021000845a2,
      0x1333333259b9b73022200001bcf1619f, 0x40801008040011000500204008040021000845a2, 0x1c70000000000000e5fcc30000000ba55, 0x1e5730c7000da000007345730c8d573f4, 0x1000cd0cd00001fbf00000d31925190c8, 0x100000088088fcc41e2f000330001bcf0,
      0x1161af014ff88088001e2f10fff03300, 0x40801008040011000500204008040021000845a2, 0x40801008040011000500204008040021000845a2, 0x15b0eef0137f7c0d500c7190e000019cf, 0x133df033df7c07c0003b1f000000fcf, 0x100fcfd300000000c710e00004dbf3b2f,
      0x40801008080012000500204008040021000845a2, 0x100028cf1eb019ef7c07c000161bf000, 0x104004108050a0343001040040a18008142a9a3, 0x200408010805020341001040040a08008140a9a3, 0x1233f39f50230d5f230121f291f858585, 0x19511af95951c23df23df23df00e51dc3,
      0x1958495844ee30e300e500e76e690da34, 0x16c1c2f0001a6f06d000f2f0fdf1f7f0, 0x1129f01ddf1f0f0fff00310bf010bf, 0x11f2f1f2f231f11ef61cf11ef00129f, 0x102120121f142714140e4f031f2f191f, 0x40201008100014000500804008040021000845a2,
      0x11b3f61ef04c0f000e5fcc33a7f61df98, 0x1870450266f0d573f4c7d99509541cf95, 0x1d3000000000e5730c79500da74737473, 0x16c1c2f0001a6f06d000f2f0fdf1f7f0, 0x145330334dcf0d500c70e95010bf010bf, 0x18800000000fcc41e2f03f4f074337433,
      0x1334dcf3361ff3300000ec7951d8f0880, 0x104def00003a2f1aaf4ddf1aaf0d33355, 0x1147614951297f4dff334f14def, 0x1084060840960, 0x1084060840960] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x111ee14cfee0058a00c8f149f0c8f0, 0x218252442521, 0x298252442521, 0x1110bf1a7f211f173f114f135f100e6f, 0x228252442de1, 0x298252442521,
      0x10d600484048400e0fb50053feb610bf, 0x101d3f284f1d7f0c6f10c6f0530003716, 0x16030400d00014000410800400c06020180807a2, 0x10102f284f102f1cef11ecf240f131f0, 0x402000001008000002010000004020080006402a0000000280000000a00001000cd0502002000008008000010000404020040006682900010000080000008200000020001ffc27, 0x1206f0206f206f2c0f2edf1e4f21cf,
      0x1102f1e9f102f223f27bf1ecf240f27bf, 0x1273f335f02f2f335f620f2eef12eef0, 0x26030800d00014000420800800c06020180807a2, 0x124240652ebf4e0f2ebf40df02ddf621f, 0x114631463280114f1abf13013a7940c6f, 0x163a51114f1abf1301313a82edfe4240,
      0x6100084100014000404800080804020080805a2, 0x101abf0a0d311b8f2eefd7240146314, 0x298252442521, 0x1130813a4a826e415010bf635463020bf, 0x17302b52000cdf13af14127f1454a5000, 0x1b500b8057443744316331d5f33042504,
      0x1f403030300003716010040043bc30e0f, 0x775361650003c11ff940077536165000eee25d94000f047fe5ee92459497735b1cd6503b9ae7cd657aef40a0000ee6b9f359412a0fbb42489a0fd2f7359400079126a5ee6b28000ee6b45cd653c895c45957ea6c2ca0003c89352800ee6b287735a2f599328000ee6b2fe8bea88, 0x14804b3003003053000035222134813b3, 0x13bc43e8f29ef150253f40a30d3225204, 0x1652000029ef4bff4bef35bf880f9f88, 0x11437a512bf243f281396131300e400e8,
      0x1140140a500a4130130026e400e8140, 0x10e8f1f7f153f1a2f0bb0ddff60850cdf, 0x10a00001a0f0308f196f104f0104f104f, 0x10c6f20df2a5f20df1dcf00fbf09e00a, 0x14a1e1f4a0a00221f00f0f0c6f1b1f, 0x14d4d4dab1a7fab0c3f06e10ff9800dff,
      0x1abab0113f10ff10ff03c9a3c9a145f, 0x103c9a3c9a145f4b0f229f0dafab0edf, 0x19a16bf4deb4d019cf0120f06e1e4f98, 0x1010dfab0ab00127f10ff1e4f009a12bf, 0x10858585015ff853c0d3f3c12bf145f0, 0x1c5aa960b96483522213013b3d3030303,
      0x12323c50a3a8a303303300d500c70930, 0x1e418bf0bd0c5f8e0ea2cea2c0cff23, 0x19648a527af183f292f1301313d312bf, 0x1622f01a7f130130026e4930c5c5960b, 0x12cea2c118f29ff106f8bc5008a854a5, 0x126efb40b4b4c41d7193f085e4850ea,
      0x1018210442521, 0x1a42305230aa798879219f18172f1e9f, 0x10000c709301327131365030035305334, 0x10053053b3a4b805040c6a30a30330330, 0x1035305334023052302313e813e8650, 0x15305300b80516023027243f2650316ef,
      0x10eaf0c5f240e82c0c2ca5e8a5e865202, 0x196108fa501013013331fd326e4193f0, 0x1018208442121, 0x113a76501053053fea4234f058a09608, 0x1088208442121, 0x10f80000013013101c9f08a0c5b62bcf,
      0x4040101100014000404800100000024000805a2, 0x16510101f53053fe0234f058a0c5f8, 0x8420605088e0, 0x1100000c30183f3aff0b64e1f19df22bf, 0x10482084421a1, 0x1101f0000106f1c9f08a00000106f0,
      0x1f8ea0d0f118ff8256ff83a6fa51183f, 0x8420605088e0, 0x1ea] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1189f03034b623682300c8f228f0c8f0, 0x10f30f30e554e57602020dcf0e5b3ce03, 0x10e573ce75191f7500840840e30e30000, 0x1003189f030030dcfa40dcf000000dcf, 0x100075191f75003054000b2299f2000b3, 0x1056c433333300ba41c550b33335f3300,
      0x199272f105f193f016767be78e3e3e300, 0x218010400421, 0x1ac133f12ff623f365f41df154f02a2a, 0x1154f02a2f3f995c31af395f059ac0f1f, 0x1030853985013afac0dac187f1b5f010, 0x1018208442121,
      0x10daaaa6108fa60020207007b3d303ce, 0x11146f000000033033b9946a94075075, 0x1e60007983cc7b68d9081183cc1e600081183d1b21e679803ccf301e679807d51d08d93cc079a04704c65, 0x1230230e6f10e6f10000cd112fcd046, 0xf3007983cc798f30081183cc1e600081183d1b21e679803ccf301e679807d51d06003cc079a04704c65, 0x8020200900044021008100204008100201029a3,
      0x1d5d50e4f033f9f03025da340230d5f, 0x1d50d500202027da350b8078023d525bf, 0x1230a60a600e30e3025e5870e70d90, 0x1d5a6d5d50e4f03003cd0da34a6230d5f, 0x1d573006d0cd27dae5a6b8132f6a00d0f, 0x177e300f9f184f5603336330680d5108f,
      0x16700019000000c3f30f306806700e6e3, 0x100a3a3a33522204815cfb3f403030300, 0x10067010e5f35165f3501165f0033133, 0x10004400100801020040804201008002200088da2, 0x10004400100801020040804021008002200088da2, 0x2021050840960,
      0x1000a30a3d32252048156fb30037503, 0x10fff0200000a40000f9f165f5600205f, 0x14e4f624f041ef366f4e3f04e2f3b3f, 0x1100009910ae0203b3f0350f4e4f625f, 0x224860940960, 0x826060c409e0,
      0x14815cfb300303030011dbf2c3f0d6c0d, 0x1024060840960, 0x17a3500edf03af400000a3a3a3352220, 0x1d328320480b3f403750300015ef07a35, 0x10067000a4000000f43303300a30d1fa3, 0x10117f20ef117f10e8f1139f217f00d2f,
      0x228042408421, 0x228042408421, 0x100707d3c7cece00d2f262f1262f0000, 0x228042408421, 0x10f34af30da340f1f0eef0f1f0000007, 0x1cd0461146f0000000e34e5fe3d684184,
      0x10004402100801020040804021008002200088da2, 0x1ebb21e607983cc1e60fa983d7826000fa98003cc3ccf300799e601e679faf094241e679807983cd15165, 0x1343323232300fdf10fdf00000cd112f, 0x8040201100044021008100204008100201029a3, 0x1da00330d5f33005900380303030e3e5, 0x1b6e32340236823001000e4f38038025,
      0x100024020080012000404800110080022000885a2, 0x10033033027da00000005900003181f03, 0x1188f038030303000340e8f2323230000, 0x1038cd0da870e8f415f0d5fae0188f59, 0x1b605434a423682306c25bf6c00e4f38, 0x127da183f0e8f2132f206c596c0003003,
      0x1d30300308539850856c0eef6c00000cd, 0x1230d5f230aa0108f2a6f330202000b3, 0x12f3206de5020e4f03129f030e5da34a4, 0x1b3a4b80000370e3c33393330176a730, 0x100c412e15023154f23000002700049da, 0x224860940960,
      0x1230d5f23003012e0f626f88363f88100, 0x836060c409e0, 0x1024060840960, 0x10329f222f20e4f03627f0300da340, 0x141ff3388270000da00b8132f000d0f, 0x1100000e8f1139f217f00d2f0850108f,
      0x294860940960, 0x8c6060c409e0, 0x10000d2f421f1420f1abf117f20ef117f, 0x1084060840960, 0x12323011cf0eef110f78045000000d3c7, 0x1200590f7f3538030303094a634a423,
      0x100e5177f00e4f380380e5da0a420d5f, 0x10000059035b6039303094e5340236823, 0x13aaf9800300177f0027000b9da73a4, 0x12eaf2a2f2eaf360f025ef02e9feb282f, 0x10000c412e0fff003250f25ef420f2e9f, 0x294860940960,
      0x1a63402323230277f1151f103f885c881, 0x8c6060c409e0, 0x1084060840960, 0x1000d5f0013ff590f7f3538030303094, 0x1110f177f4b0e4f38420f380110fda87, 0x1110f35b6035403094034a423682304c,
      0x1177f788827019ef00da002132f204c59, 0x1a4230d5f230aa278539850121f4c0eef, 0x10075075014e514140e4f030034c0da34, 0x1b3a4b81dbf00094e99403347af33000, 0x1da340230d5f23023142714000004c0da, 0x1780231425bf14140e4f033f9f0300,
      0x11495142714350cef20200da00b8231f, 0x12323230270d2f139f0d2f0121f140d0f, 0x120d5f20695969102f3803030300034a4, 0x16823014e514140e4f380384c0da3aa4, 0x11f1f0b659000030030e5f0e534023, 0x123230142714000004c0da73a41a1dbf,
      0x100695969102f3803030300e534023, 0x1014014140e4f3832ef3800da3a000d5f, 0x10b6592196c03181f030003433236823, 0x1140caf0cef3303300da001a270f0d8f, 0x1145914102f1427] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1010040043bc30e0fb511af0b8052700, 0x1218248442521, 0x13522213013b3f403030306615661516, 0x120020204004b396039603053d3737373, 0x13333333522213013b30030303053a30, 0x1960396030000000000003bc400150d3,
      0x14703470365a3332331621f6f2000b3, 0x10f6004150415930e0fb5f4001f8f149f, 0x16d760000053a7b614bf05747974f616, 0x110013013a7002424053000ba11004976, 0x1f5307983cc001f53003cc0079f9800f6cc00799f530003ccf301e681918001e60f31ed98001e704c64, 0x28000a0020010810020100804080012000403a3,
      0x7a7307983cc007a73003cc0079f9800f6cc0079fa73007980f3079879f98001e6f301ed98001e704c64, 0x10655400016000d31000002401000028, 0x3ba2b66baa500077acc99400079126a5ee6b2f73594001deb3265ee6b280007aef40a00004a817c80007aef40a0000fd51da800012a0d673660e06332f7359400079126a5ee6b2f73594001dcd653c895a68bf2ea6c2ca0003c89352800ee6b287735a2f599328000ee6b2fe8bea88, 0xf3f307983cc00f3f30007980798f300f379807a73f3001e60f30f3081918001e60f31ed98001e704c64, 0x114ff2eff336f022bf0fcfcc83a5f5757, 0x19aa500281301313a81e457069066906,
      0x298250442521, 0x118000b415afb4e61b8ffbd707014fb14, 0x154a5000130813a4a826e4c3095799567, 0x194d5940c7000c5aa278585850141e14, 0x12300cff232323c5073073133b933163f, 0x102008440021,
      0x12304764476438030303d903434942323, 0x112304764476465030035305334962305, 0x1218252442521, 0x1b805d30e864b364003003730b634123, 0x1218252442521, 0x108500cdf47b347b36500053a3532796,
      0x185140140a501e9f0139613b5d726e4a4, 0x114fb1454a5046013961307c426e4a40, 0x117017133313f33b9946a940c700053aa, 0x9021084410a1, 0x1650316ef0353255334023052302353b9, 0x18465229ef25327533516b80500230000,
      0x106406438030303000349423232300840, 0x1b823008408416e30e304250400e7b500, 0x18500cdf0ce86406400300300b634023, 0x1aa00003522213013b3d303030308585, 0x1830e30c33393330fdf17a67302020c5, 0x103030ee33434023232300cff232323c5,
      0x1035396533402305230476447643803, 0x1030e303402312304764476465031a4f, 0x8d4060c609e0, 0x1a30275305300b805d30e8642643303b6, 0x1104f294f11bf153f0fff024047247265, 0x1db000001a0f16bf148f135f104f0104f,
      0x100116bf628f135f12f4f135ff101fdb1, 0x2b413d6ec0d800000ad553f602b3fb0159fd800005684c7f6000002b554fd800000ad553f602b413d592102becaec0000002b3fc853d3002b3fb00acfec059335b0000000acfec0acfec00acfec57d95dc0df880567f60acfec057d95d8000000acfec0567f60159fd82b3fb00159fd859335b81bf1acfec00159fd8567f6002b3fbad098fec00002b3fb0002b3fb15aaa7ec00000159fd83919963022a, 0x90118c4418e1, 0x90118c4418e1, 0x9021084410a1, 0x11b8f19dfb40ab4580afbd700a7d300,
      0x14e6f762a7601e2f1f0f00000018347f, 0x10ab4580afbd7000000211f347fd619df, 0x1362f0d6f000067184e7f1b8f26cfb4, 0x1629f131f4ccf251f1422f1d7f0d6f, 0x90118c4418e1, 0x121df2ecf100d6f00d6f00000284f17ff,
      0x9021084410a1, 0x100d6f027af000117ff2c8f131f3eff, 0x9021084410a1, 0x162bf131f1a5f251f19bf62af00d6f, 0x10a0a1a0fbb0ddf135f00000423f17ff, 0x1840f5f5000000dff7e148f103f0a0f0f,
      0x100d3f08df50384f4304310af0000001d, 0x1000000c30000f508943043000058058, 0x1000000058058f40d3f08dc403743043, 0x114367fa5960b5130130026e4a4085089, 0x11454a59600130130026e4a40851462cf, 0x10320df0353045334a42305230aa14fb,
      0x10c3339333114f176a73a92e720000065, 0x1265272c5f13534953b3a4b80500830e3, 0x10383e3e334023232306523117f23020, 0x10e30344523b82300345643364380303, 0x12220232323015ff0ce8642643303b603, 0x100343466ec6617553333336b07373c3,
      0x1030303860932b93f7e30e3ec0000e7ec, 0x101013013a7d3416f2424004764476438, 0x1008208442121, 0x1000a7d32f0f148f2400c5fc4f5f5f528, 0x1188f2a3f1cff332f148f2a3f1cff332f, 0x1a50183f1a3f1301313d3423fe4160f0,
      0x1130130026e400c5c596183f962a5f, 0x10106f12dfc5008a854a562df0284f, 0x1499f359f0004e8f0e8f23af32ef1a2f, 0x106ea43118f0630f4e8f62ff32ef62ef, 0x1020210e5b3a603a6030348323b8230ea, 0x8020200900044021008100204080102001029a3,
      0x10c6930931e30e30000f7e7000a3a42a0, 0x8004200108001200050040401008002400088da2, 0x18394368f94000010e5731fdfc73b4f1, 0x8040201100044021008100a04080142001029a3, 0x8040201100044021008100204080102001029a3, 0x1a3a43b5f3312299f2000b3003003003,
      0x80002000880012000500404010080024000885a2, 0x194133313f3300001affc7268f1003, 0x1080860840960, 0x1084060840960, 0x1e42500eaf0c5fb60e864b664839412ff, 0x1150960896108fa5010130131d0fd326,
      0x1018208442121, 0x10c5b65413fc6501053053a7a414bf05, 0x1088208442121, 0x1150c5f889f80000013013a7a889a815, 0x10b6542829bf65101def530530014bf05, 0x8420604208e0,
      0x11500000106f0100001d0fc30183f1a2f, 0x10482084421a1, 0x1f889f82effa51183f1def0000a889a8, 0x8420604208e0, 0x1eaf8ea0d0f118f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1b5e805e800cdf13af050c8f149f0c8f0, 0x14813b33303030306525962553b85303, 0x12813961313d70e415000003525252513, 0x125b548b5b3e703a3030140140a500d7f, 0x1a4132613b5d70e40e0f00000d3250, 0x1218ffa30cafa300cdf140140a500d7f,
      0x10caf177373e322205b93a893131fc7d5, 0x166e50caf0ecfe339e30000055939393, 0x11733730283207407401c551b9f55151f, 0x118ff26cff71d7ff700000c39309318ff, 0x1e4540740740131f01b9ff43c1f5be5, 0x11d8d0b5f50a593a893132613b5d7144f,
      0x1048d3fefb58d0000016939393041704, 0x1d7008008f507407401601b9f16046604, 0x10c9f04d78d79b50800000c393093d717, 0x1c7392f4a355a307407401601b9ff404, 0x1559393931172a73e322201937a932e7f, 0x2101084220860,
      0x504084220860, 0x1550556a2f0e50caf0ecfe339e300000, 0x100000c3930935b17e77302832000001c, 0x100001f400510f5be518ff1f74f0ff7, 0x28000a0080012010001100044002010080403a3, 0x404000201c100008000400000101000080000008201c000400010002020000002000100020201c100e00040400000100008001000004008000040040000100040000100048a5726,
      0x12288fa3205fa30c5aa03858585015ff, 0x1830c5107f0a80107fe666e6265fc7d5, 0x10780ddd42bd41cbfe7dd33247f830c7f, 0x10d7f016d42bd404e704338d83b583007, 0x1d4acd429cfe71eef33083f78300d7f0, 0x1f600c5f8e0ea2cea2c0cff00001cbf,
      0x14a1e1f4a0dff0000a00a0a153fbb0ddf, 0x1e666e6132613b5d70e4540c5c5e40d3f, 0x1d4040e0f04158d0b5370c50c9f0a80a5, 0x1d4040c9f04d78d0b50800703d016d42b, 0x1d4d70d7000893700d7f00d7f016d42b, 0x1030850c850ea2cea2c118f000018d4ac,
      0x1aa0ddf480ddfe30000b50b5b3d303a3, 0x10500001e67ae62e7fc73920a31aa3005, 0x2021084240860, 0x1ddd4147fd41dffe7133247f830c7f830, 0x20410884408e0, 0x1065d466d453e75334b52305230070780,
      0x1d4187fe74b33083f78300f4f270f4f, 0x153b85303b5e805e80000013dfd40d3f, 0x15305334b523052302ca50a5065d466d4, 0x153b85303b5e805e802c1427141465000, 0x1d7a4e45400c5f0d0f01448147465000, 0x105e4a811bf141f11bfa5000132613b5,
      0x1d466d4530e0f53feb50058a0c50eafc5, 0x12b9d040c9f04d78d0b5080b60103f065, 0x179d4e40e40f80f88a00d7f00d7f0169d, 0x10053053feb510df058a0118f0000a5d4, 0x10e410fff810dff88a0eab6636363650, 0x1eaa86343630000e4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x185858500cdf1f8f0cdf27b685149f850, 0x134c323232300cff939693c5c7c5aad3, 0x1965334c3230523047644764380000034, 0x10f434e8230230476447646500d7f5b53, 0x12753b853f4c3f705f7006406400b60f4, 0x1d813261307c499e45404704706500d7f,
      0x100160930040e0f04ca460b5ae0a5d8a8, 0x107401601b9f16046604044646b546000, 0x1b50800000c3000ca0caca08008ae074, 0x18507407401601b9ff4040c9f04ca4679, 0x1c3232323065936693a4c7a4aa0c855b, 0x15305334c323052300640643800000034,
      0x106400b6000b834e82302300000655b00, 0x1000065270053b853f4c3f705f70064, 0x1c7d507c40205f00c5aad3858585015ff, 0x14600c7f00c5094094107fe666e6265f, 0x1460b500093093ddd42bd41cbfe7ddca, 0x1cacaf700000002516d42bd404e704ca,
      0x1232300cff079378931cbfd4acd4cae7, 0x1052304764476438000115f03434c323, 0x1e823223047644764650005305334c323, 0x1b853f4c3205209464b6640000f40f434, 0x10c5c5d3d30c5fd30479647276500053, 0x10c9f0a80a5d866d813261307c40e454,
      0x102b26ef040c9f04ca460b508012dfc5, 0x103db40b4b49999d79900d7f00d7f016, 0x10013013a7c41c4f24240118f000018e6, 0x10266a3f991c4fd7240ead3434343280, 0x107b3a303d3030850ea7a430643000026, 0x1071a0000a4aa0c85b563b5630000070,
      0x100c7f00a4107f940941e67ae607c707, 0x501084240860, 0x105230093093ddd4147fd41dffe71ca46, 0x9010884408e0, 0x1caf70000000065d466d453e75334c323, 0x105000793789313dfd40d3fd4187fe74b,
      0x1232323002703565d466d453b853f4c30, 0x1c4117fe4240e96495643800000034c3, 0x134e823a423014631463a50001301313, 0x1261307c488e45409464b6640000b90b8, 0x1a4e45400c5f0d0f0149614a4a500013, 0x1a4d3a80fbf460fbfa500013261307c4,
      0x1d466d45314bf53f4c3005150c50eafc5, 0x12b0e9f040c9f04ca460b5080b6028065, 0x1f40f4f4f80f81500d7f00d7f0160e9f, 0x153f4c3d305150118f0000a5d479d4, 0x1f4f8d3f8150eab6430643650005314bf, 0x1eaa84312cf430000f4fbf4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1030303038545454159a6347523232300, 0x2100884210860, 0x10f8f030063063353737377754b3b3f3, 0x10300630630f7f37237e7546db31cbf03, 0x1000a400630639437237f35475b3003d3, 0x1126f0d5f126f0000012159f21a756d75,
      0x20421084410a1, 0x133107f3300e4f3843cf381d4f1da1a1, 0x2101084210860, 0x2101084210860, 0x10176f001401401a111f121c7d5126f1a, 0x2021084240860,
      0x2021084240860, 0x1033d3330140140177f080000d5d50, 0x1d502e00a4000001111f3921ac71126f, 0x2021084240860, 0x2021084240860, 0x175596834123392301401400960390fa,
      0x2100884210860, 0x13537373705454b3f30303030b6540354, 0x1000f7f37237e7546db30030030063063, 0x100630639437237f35475b3003d303000, 0x112248f2000001242af21a756d750a400, 0x9021084410a1,
      0x2101084210860, 0x1d50f5f1a0107f0012711a109fc7dac7, 0x2101084210860, 0x2101084210860, 0x101e2f176f1e2f000001a111f1126f1c7, 0x501084240860,
      0x501084240860, 0x110f5fd30000140140177f01caf000d50, 0x501084240860, 0x10000d50000a4000001111f1126f1ac7, 0x501084240860, 0x501084240860,
      0x12301546654c70d2fe50d2f140140096, 0x2101084280860, 0x1b3f3030303038545454159a634752323, 0x504084280860, 0x10030030102f63e963353737377754b3, 0x10030956395630f7f370d1f37e7546db3,
      0x1000008463d3639437dc37f35475b3003, 0x1ba0095ac95a41dc0d1fdc1a756d75, 0x424084280860, 0x14b1c5f4b35ffac16ff126f18dfba3bcf, 0x11ebf126f0ba0ba00d5fe90ee90e259f, 0x1261f000e2daf0e14b407f4b259f2daf,
      0x221084280860, 0x1265f12ff01c5f00ac2a018df261f105f, 0x179a610d24bf0f8f24bf0da1ae90e9, 0x421084280860, 0x10381d4f9519524bf110f10fef125bf, 0x441084280860,
      0x441084280860, 0x485084280860, 0x10f7f1e7f7a6a2bef0ccf2a2f0ecf4a1f, 0x1000e4f3869112f690d9f0f7f28df238f, 0x114441a111f0fefdd1c7d5126f1a0107f, 0x1021084280860,
      0x10fef1141f1ed5d5ad3def176f101444, 0x411084280860, 0x441084280860, 0x11ac72a126f0000014123f1409177f08, 0x1d512e01001b44d344110f111f180fdd, 0x1014210482521,
      0x421084280860, 0x10339030230146614a41960fef11fa, 0x421084280860, 0x441084280860, 0x421084280860, 0x1392023003900f7f37037e7546db31a8f,
      0x12054755968340a403610001a756d7512, 0x504084210860, 0x504084210860, 0x1188f43188f439367c3673637f373020, 0x13537373714ef5454b3f30303030b654, 0x1a6a60f1f181f0f8f1502ebf6310bf63,
      0x1003095449544110fbc11cf120f181f0d, 0x1101008463d3639437f437f35475b3003, 0x8000a00028040401008010200410000c010081a3, 0x80012000480404010080102004100014010083a3, 0x12107f2009579950710b11cf17bf11a61, 0x424084280860,
      0x424084280860, 0x424084280860, 0x424084280860, 0x1248f367f002021a111f001c7d501a, 0x88b000222c0002d907aafc7981e60812afc3cc3db5d904097641e60812afc7980f31e607981e612d44, 0x12000248f003f7f03f7f110232f1367f,
      0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e60798f307980f31e607981e612d44, 0x180006008004a010009102004008948201229a3, 0x16a4f1fff0d32020111f001ac7001239, 0x88b000222c0004bf000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x1dac70161f00fbf1100383f5d15d14acf,
      0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x80004000201e100000018400000041000000500004201e0004000400020200000020000800040008100f00040400000040009000080010201e0004080000010001200010004895726, 0x3db3000f6cc001f53000f307983cc1ed98003cc3cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x806040002000100000018400000041000080480020000c000100020001020000002000404028000200010002040000004000508050002000020008080000004000a000100028f9c26, 0x11250feff425df1ae51a00000109fc7, 0x821084280860,
      0x16a6f6a14f1f06a5f0074136f74136f, 0x421084280860, 0x13333012769ac695a512fcd238fca511f, 0x1ebc1307983cc00102307aafc7981e608118003cc3db5d90408c001e608118007b66001ed98001e612d44, 0x178171f1c5f11ff0f5f205f565643df33, 0x1d5310f6a7f1e2f176f1e2f095449544,
      0x1140c4f177f43ef0fef513f141f386f, 0x19711ff9b11df1a56033033014311f, 0x1960fefc311d51101007644c444b9171f, 0x1014210482521, 0x1014210482521, 0x421084280860,
      0x421084280860, 0x421084280860, 0x1146614a41, 0x421084280860] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x136222035a3a3a34548b3b3f303030300, 0x1733622200430435583838319257373, 0x102c3200430435583137f836a8f25184f, 0x1f34500ef4004304384833383e325f373, 0x1450320304500004533289f33222ff31, 0x202318c4418e1,
      0x183830252573362220d3a32a3334875b3, 0x1836a9f25184f733622200430435583, 0x1833383e325f37302c32000005583137f, 0x1289f33222ff31f345f40e0004304384, 0x50318c4418e1, 0x10303078a30d3fa34c681687700004533,
      0x21010884808e0, 0x11befd9d90e7f191919048b3b3f303, 0x16aaf9a37ef9a0caf3a2f10ef10ef0fcf, 0x15583838323ff25737336222035a3a3a3, 0x1836abf25184f7336222030bf4310bf43, 0x183fd25f37302020e943e9435583256f,
      0x1f31f30e7f0137f007643c343848386, 0x1824088c809e0, 0x10f30e917dfe9f40caf86256f86222f, 0x1006acf4c1165f4b514f0c7f1b2f0c7f, 0x2014202442121, 0x11c3f6c1c3f0f30e5ff433afdd2bff,
      0x1184fd910105a0181f514f4c781786adf, 0x201428a4129e1, 0x2014202442121, 0x2014202442121, 0x10edf156f1f7f273f46ef3b8f17df0, 0x1259f227f259f273f1c3f147f1c3f0e5f,
      0x15656773333330135180f350e5f273f, 0x20442084821a1, 0x10c7f0c406060678dd6767123f0f9f, 0x16aef3c3c4ce9165f4b102f0c7f1b2f, 0x1679a6aff3656033033095f495952bff, 0x1781783c06c000edf060c4f061dd0c4f,
      0x8850884808e0, 0xc630886808e0, 0x136222003095138f95695a6b0f3c694c, 0x11f303303300300005583083025184f73, 0x9040884108e0, 0x1870e30e304875b30f40770000222ff3,
      0x10330a30fbf064b2f0649864686c82977, 0x136ef4436ef44d4c6c4c6c8b93656033, 0x143558383832e4f252573362220d3a3, 0x1133f1e6f2b3f5603303306b1f431b3f, 0x125f37302020e944e94443ff1cffca67, 0x1403f1d9000007643c343848307830ebf,
      0x1824088c809e0, 0x13300e90edfe907222f1c9fcae6494f, 0x10c30770dd008b182ff31f30e3f330c7f, 0x20442084121a1, 0x1dd4c182f165f0d9f19df3c2f273f3c2f, 0x116cf3300e5ff433af1f7f19dfdd181f,
      0x19d456c45000000008be6f378f3179f33, 0x106b3f05a02bcf200f4c15bf6b2f0f2f, 0x10e3f00000180fa40e5f77dd770f2f, 0x16b4f1fcf182f071f3fe6258f0e3f1c3f, 0x18b182ff31f30e3f00c7f004c0d3f1fcf, 0xc830886808e0,
      0x119df6b5f273f3c0c3069a06ddc41c9f, 0x10095f4959519dfdd3cdd4ce9165f0d9f, 0x10ac06257f066cc417df8be6f378f3000, 0x1cc953c5ac43c694c15bf3c3fe93c06c0, 0x195] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1a30cdfb80cdf13af080c8f149f0c8f0, 0x1133f0a3acb4545450858585015ffa3f8, 0x173bb2220c5aa7c07c115f4bd8d8d80a, 0x133330c51a93939355e6e6e6205f1773, 0x1086d6d6d678d4d4d4119fbe5656cb33, 0x1888688b978d4d4d4b4beb456cb333333,
      0x1d6d678d4d4d43c4fbed956cb3333330, 0x1bb0ddff600c5f8e0ea2cea2c0cff86d6, 0x14a0dff1ddf6b6f273f0a2aaf0a0a440f, 0x1bbd71d5f07d3dc5f8c5c55e04a1e1f, 0x11b8f4d1811bf1dff3db413dfb4b42c9f, 0x10533402305230850ea2cea2c118f7a4d,
      0x153b85300030503085e427e4036500053, 0x10ebf5a330f03f3f0570aa000065e80e8, 0x117e77302020ab15afab7e4697bd975a, 0x15a1000001930d1f93c3e683e6107f, 0x424084280860, 0x424084280860,
      0x1560330330ab1ab515f461bddc5a172f, 0x8c4098c809e0, 0x1084090880960, 0x103300c7ed6b7d6c4d4c6d43c4fbe126f, 0x10155fd61ccfd6c4d4c6d46bbe1a56033, 0x1481855d3d4a3d40cef840cefb3003003,
      0x1141465d4bdd453845334023052302c18, 0x1147465e8bde853b8533a0005002c1427, 0x124650088b531a8f53febc0058a001448, 0x10f88b5e05e0106f0e48a00c5fb62424, 0x10e4007d0d0fc50eafc5085e0000f8, 0x1a80d8f5a0d8fa5a45e54132613bc106f,
      0x16365ca088b531a8f53febc0058a0118f, 0x1f8caf88b5efb5e2e8f0008a0eab66363, 0x1eaa8634363] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x12035a3a3a31eaf4815cfb3f303030300, 0x10202004304355838383192573733622, 0x17302c320043043220f833383e325f373, 0x1f378f3000f4004304384833383e325f3, 0x1184fd91f31b2ff3000001eaf337733e6, 0x21030886308e0,
      0x10e3fe30c7fe306c351b2f350e5f181f, 0x10c7f00000dd8b338f33141ff3141ff3, 0x10182f23af4c141f165f4b00c7f1b2f, 0x18b252f33e6f378f30e3c3e3000002bff, 0x10182fdd4c78216f780f46c000000181f, 0x1a32a3334875b3432f0316cf03000005a,
      0x120043043558383830252573362220d3, 0x1c3200000220f833383e325f3730216cf, 0x1f30f400004304384833383e325f37302, 0x17e333c5f33000001eaf337733e6f378, 0x100c7f00141fa433bf0e3f0e5f77dd77, 0x1000000dd8b32df77272ff31ebff30e3f,
      0x1000000000dd0dd4c0165f0d9f003c5f, 0x100f46c000000179f8b177e6f378f3c3, 0xd030886408e0, 0x17aa3a468356800005a0004c15bf16df, 0x1a3a3a31eaf4815cfb3f303030305aa3, 0x11b3f43558383832baf25737336222035,
      0x183333f836b7f25f37302020441f43, 0x186830eff25f37302020e943e943220f, 0x1333f86e6f378f3000007643c3438483, 0x10c7f1b2f0c7f0f30e90edfe9f41eaf86, 0x10f300002bff6b8f004c0165f4b516f, 0x10f404b5a1004c78216f7811c3f6c1c3f,
      0x28000a0040011008002100084002000080403a3, 0x28000a0040011008002100084002000080403a3, 0x115cf181f2e0f517f3a0f517f0184fd9, 0x110bf6b9f2caf387f326f431f181f0edf, 0x1152f6bbf6baf33af10350e5f10bf442f, 0x8110884808e0,
      0x1444f9516df443f6bcf180f16c7a152f, 0x8410884808e0, 0x195195111180f16c7a152f6c111103595, 0x8110884808e0, 0x814208482121, 0x8110884808e0,
      0x814208482121, 0x8410884808e0, 0x8410884808e0, 0x8410884808e0, 0x8850884808e0, 0x8850884808e0,
      0x1445f18ff141ff316fff30e3f00c7f00, 0x1152f148f6bdf33af10102f06e906dd8b, 0xc130886808e0, 0x195123f443f14df1c5f16c15ef152f, 0xc430886808e0, 0x18b407f18ffe6f378f300000952acf,
      0x16c5a1f6f10ccf00e5f00cc06c3063c6f, 0xc230886808e0, 0x1f3730216cf20030957995074c7a1c5f1, 0xc430886808e0, 0x1179f3316cf330030000220f83083025, 0x10e304875b30f40771eaf000e6f378f3,
      0x1330a3f906a90649864686c82977870e3, 0x1215f44215f44d4c6c4c6c8b936560330, 0x143558383832e4f252573362220d3a3, 0x116ff199f2fbf352ff606bef4330bf, 0x1e909397f13df13ff179f224f0d1f16ff, 0x1c343848307830ebf25f37302020e909,
      0x116ef113f2fbf432f13df0222f007643, 0x10c7f3300e9ace9ce1edf0ccf13ff200f, 0x13c2f0033033dd8b000f30f30e3f33, 0x1439fdd0dd4c0165f0d9f6bff3c2f3c5f, 0x13308b00e6f378f3179f3316cf3300000, 0x1004c15bf16df0f2f9d456c450c33377,
      0x1000000e5f77dd770f400f2f5a200f, 0x11ddf0e5fe6203f07258f0e3f1c3f0e3f, 0x1076c1133bf1dff00e5f003c1ddf1c3f, 0xc220884808e0, 0xc220884808e0, 0x100e5f00a49579950ccf4c1a1f180f,
      0x1956c4c0e5f180f076c5a181f141f182f, 0x16c0f161f5d13bf87877be3e3e309579, 0x16c1f33af2cef03c3f061b3f065bdc, 0x12a6f1c5f11ff6c0e5f152f3c7f446f, 0x1130f77870e30e30956c2f95142f443f, 0x10ccf00e5f00c80646064edcd8161f9c,
      0x1957995074c7a1c5f466c5a1f6f7e] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x12300cffa3a3a3c5e8c5aa3585858500, 0x123047644764388383830a33434552323, 0x10476447646583898353a35334162305, 0x1270064064e88303830a33534023b623, 0x10149f4704706503890353b8533516005, 0x123232300ca323a365e865aa16850585,
      0x1162305230064064388383830a3a33455, 0x1b834023b623000006583898353a35334, 0x1b8533516270500064064e88303830a3, 0x10cdf1f8f0cdf0cff6500006503890353, 0x1a3a3c5e8c5aa35858585015ffa3f8a3, 0x1838383115fa334345523232300cffa3,
      0x1898353a353341623052304764476438, 0x18323cfa335340230230476447646583, 0x18653b8533516005009464b664e88386, 0x1bb0ddf135f00c5f28047964727658689, 0x100dff7e195f103f0a12bf0a0a1a0f, 0x1bbd7103f07d12dfc5f8c5c5a500148f,
      0x10ccf1ddf18e6162f3db4bdb4b40dff, 0x167133713a73d1faf24240118f7a1ddf, 0x1518f01faf0240ead34343432816bf67, 0x10ea7a4306431816bf162f67266c3f26, 0x100006583898353a3533416230523085, 0x102707865089053b8533516030503085,
      0x1c6d3c6168316b30030030a365e865aa, 0x15da3a3345523232300ca3bd63bd63a3, 0x1131318117fe4240e964956438838383, 0x134023023014631463a57c116f671389, 0x116180e4009464b664e883a483b9a3b8, 0x10052400149614a4a588116f54132613,
      0x12400c5fb603d0650088b5314bf532816, 0x10eafc565a50000f80f88ba50a50180e4, 0x1a5a45e5413261316180e4007d0d0fc5, 0x18b5314bf53281600500118fa86e5a6e, 0x1a5fba5145f00000eab643064365d308, 0x1eaa84312cf43f8d3f88b] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1870303030013af0d2f0c8f0c8f0c8f0, 0x1000f60e587e57335252525048d5b3, 0x103012ef012ef00001bef7c185f7c143f, 0x1151500e70108fd325225048a6b300339, 0x16afc3d0130f130f117f0f9fa63b0c3f0, 0x16c4fcd1cd1103e7f00b8da736a0c3f,
      0x22118c4818e1, 0x401090880960, 0x401090880960, 0x111502596250e6f10e6f124df1bbf1c7f, 0x1004090880960, 0x1004090880960,
      0x2221084810a1, 0x106d16d1123df113f130f880f9f883b10, 0x2221084810a1, 0x1004090880960, 0x1004090880960, 0x1004090880960,
      0x1e587e573352525257c48d5b387030303, 0x1108fd3252a25117f48a6b30030030d5, 0x1252525048b3b3f303030300d5a6e7a6, 0x10185f03a0cbf4545450f3a3a3a335, 0x12504875b300320300cbf008b4b001bef, 0x100f9f56567733333300a30a3d3252,
      0x106c5f00681687706767780130f130f, 0x2021090880960, 0x151af2a6f6c6f11cf111cf3b0f519f, 0x421090880960, 0x1330250d3f2551bf437f2a6f364f51bf, 0x123df215f130f22ff0f9f22ff56773333,
      0x1251cff48b3b3f30303030771215f6778, 0x1024090880960, 0x10edf156f110e00e0f3a3a3a3352525, 0x2010088040011008040101004100204000443a3, 0x425090a80960, 0x10447f259f227f111c3f147f6c7f237f,
      0x1025090880960, 0x1025090880960, 0x1a31e6fa3d3258325401f4875b3003003, 0x1130f371f0f9f2c4f567733333300cbf, 0x1d50020200770e1f2cff677811ff6c8f, 0x17c24bf7c448f1aff00000000022520c7,
      0x10c7000239201dbf138f1dbf1bcf00098, 0x1117f1e2fa6186f167f00000000d3202, 0x10d8f22201dbfcc1dbf19cf00130f3bff, 0x1114fba5511ef11ef11ef0daf0eff7373, 0x1107f107f259b9b730d8f2220da114f76, 0x11fdf0380f00114f76114fba55107f,
      0x11bcf409f51cf1c7f6c9fcd1cd269f, 0x421090880960, 0x188186f167f0100979697114f138f114f, 0x2221084810a1, 0x1cc240f19cf123df113f14ff881e2f, 0x1084090880960,
      0x1251b4f7cc7d517ef109f01900240f, 0x13b1f6caf016afc816af0fcf5b0eef, 0x146bf1c7f17c1c7f7c6cbf406f2aff, 0x8410908809e0, 0x117ef0000016af2e4f16af4dbf3b2f, 0x11dff0fcfd31b1f0daf1b1f117fc7117f,
      0x119ef7c207f7c6ccf309f00001dffc8, 0x173362220016af224f16af28cf1eb1c7f, 0x1084090880960, 0x10e7f1919190e38383835593939301773, 0x13320137f6b6b6b0caf000daf0209f0d9, 0x17be3e3e30083083c3933393017f37302,
      0x175d9750e7f8686865b0292901b0f8787, 0x16cdf3bef449f7b2fbf7b14ef01d8f00, 0x19326af9351df2aff0caf10ef18ff170f, 0x151ef2939ff1b0f39ff877be3e3e30, 0x12a3f1773733622200caf8686865b31ff, 0x117f37302020558683838355939393,
      0x1733622200f4a983c683c393c6936cef, 0x1e500039001e6fe3e337559393930172a, 0x1017f373020ecf2000ecf001c5505500, 0x100f40000e500e30e300e3037c3933393, 0x1254f1aa6198f298f0137f00756d75000, 0x193250f1250f198f0caf0daf2fcf279f,
      0x1084090880960, 0x119ff14df24bf14df30ff2e1f0100937a, 0x2421084810a1, 0x1172a73362220211f1211f304f13bef5c, 0x1084090880960, 0x1084090880960,
      0x139326f0159fdc159f375593939313df, 0x11c5551ff55445f1c5fe5d9326f6cff, 0x138ef17f373020201c5f203f1c5f1c5f, 0x1e5876d0f000013ffca13ff37c3934693, 0x19d1c5f326f1f451ff1c5f445f6d1f, 0x1084090880960,
      0x1838383559393930173a7336222001c5f, 0x10f70f7dd5505500000e3f360c7f360e3, 0x10e30083083c3933393017f37302e320, 0x10137f0075777500000f40000000e3, 0x10caf0daf50af279f372f36210f360e7f, 0x17b14ef01d8f0093147f93a9865b86,
      0x110ef18ff3bef33bf0caf31cf7b31cf, 0x1939393363f173a733622201cff10caf, 0x10440908809e0, 0x11c3f1d90e3f360c7f3608683838355, 0x8410908809e0, 0x102020147ff731cff7dd556d2f5539df,
      0x10020bf832a4f83c393c6934d5f17f373, 0x1f4276fa9199f125f1f6f8714ef0488f, 0x10d5f230121f291f147f866d3f8618ff, 0x1844ea979a91e7e5694e06e00da349523, 0x481090880960, 0x11a6f0f2f6d1f7f141f00fdf00958495,
      0x10010bf141f10bf6c1c2f1b4f0edf1b4f, 0x1069d469d4cb971e9723df1aa6e9cb0db, 0x169e61c1f971e97258f2ea6e90d9f000, 0x123df970d3f97db1ae9111f00000697c, 0x1e3219200121f142714140e4fcad45bd4, 0x12a8f520f0742742e30001bffc7d595,
      0x112a8f103c8f03c8f10441f324f1520f, 0x40201008100044001040801008040021000845a2, 0x140005010004c020009102004008548201229a3, 0x40201008100044001040801008040021000845a2, 0x40201008100044001040801008080022000845a2, 0x1247f2000019c7950c7f40af23920521f,
      0x10f2f19b118afba00d8f00da731b3fd32, 0x4a5090a80960, 0x4a1090880960, 0x100fdf00126fc8259fc8ba0f2f26af, 0x136cf0edf36cf1a6f0f2f6d1f7f141f, 0x1d5952d0136f0010bf141f10bf6c1c2f,
      0x10d9f0000749774972d9779972cbfc7, 0x169e61c1f1b1f1e1b1f258f324fa62ebf, 0x12cbf977a97136fc7952aef00000697c, 0x13a2f1aaf4ddf1aaf00000d3975597, 0x17614951297f4dff334f144af6d4f44af, 0x1084090880960,
      0x1084090880960, 0x114] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x111fcf153f9e0e42400c8f149f0c8f0, 0x4010100500044001000800100004020100805a2, 0x14aef14af1a0f000104f172f104f11bf, 0x17e7a7eb4fbb4e60b0d7001313a8111ff, 0x4010100500044001000800100004020100805a2, 0x1581a8f584e135f08d0013100f01e6718,
      0x15a0dcf08d00ce0103fdc0d4fd8124fd8, 0x100fef00fefbc0d4fd8124fd858100f58, 0x1a500bddc0dffd80edfd8000cef4e0000, 0x14813b30030303000cdf13af14631463, 0x1250480b3003b50300500003525252513, 0x10cd3db488b4b41e0d7980e70a30d3252,
      0x116b988b904250473792b52095095dc18, 0x1791e4570e86525962553b85374437443, 0x411084280860, 0x1e814522f1437a512bf0d7f2813961313, 0x1140e0fa5fb0d7fa4132613b4790e400, 0x19393930caf1773730222000cdf14172f,
      0x10c39333930170730233200caf000055, 0x15b28bf5a6a18ff124f0e0ecf0e0e3083, 0x1a6567a333333069f769f70f7f5b0dcf, 0x193131fc7d59544954478d60bd6135fe6, 0x155151f66e50caf7a4539450a35b93a8, 0x118ff7a01d7f00a374c674c61c551b9f,
      0x1f50074f774f7131fa91b9ff43c1f5be5, 0x1d7f50e40000169393930417041d09eb5, 0x10080080c3930e1f930170179f0164f, 0x10d4f00dcf0d4f585a5858124f08d1a2f, 0x10bd6b4e6b4b47a20dfd715069069111f, 0x1054a593a8931326139544954418d6,
      0x11625bf1b9f16046604047a43efb5193f, 0x1ab4eab144f01fcf057074106f7411df, 0x10c9f04587a0b500bc06bc0697b746b7, 0x1172a7302220074797408165e1b9ff404, 0x15501e50caf0039000000559393931, 0x2080082000104004100804400110802020080da2,
      0x2080082000804020100804400100802020080da2, 0x133935b17e773020ecf2000001c55429f, 0x100510f5be500e32a8fe30e30830c393, 0x1d687d64b4fe62a5603303300f70f71f4, 0x1004000008010000040040000040100008000000820180004000100020200000020001000202008100600040400020000008000400004200c00040800000100010000100048a5726, 0x13f3f2aa6a67a10f8f103a44c644151f,
      0x811084280860, 0x811084280860, 0x10f8f0fff0c7956d5f958b110f0b6d6d, 0x1225f6d8f225f6d7f523fa62e7f7a6d6f, 0x1f4a355a31937a93956d9f951cef110f, 0x2080082000804020100804400110002400080da2,
      0x1c7d5930b0205f00c5aa96858585015ff, 0x10c7f00c5107fa3a8a3107fe666e6265f, 0x10007837883ddd42bd41cbfe7ddd64b0, 0x1830d7f8316d42bd404e70488cd0b5, 0x11cbfd4acd41c3fe71b8fd6000000d7f, 0x196bd0c5f8e0ea2cea2c0cff8683f783,
      0x1a854a5e666e6132613930b0e400c5c5, 0x12bd4040e0f04d6103f0b500c50c9f08, 0x1d4040c9f0488cd0b50007673d3716d4, 0x1bd1b8fd6000000d7f5e0d7f0816d42b, 0x12cea2c118f195fbd893718d4acd4195f, 0x127e403650005305334d72305230850ea,
      0x1e879e86500053b853791e030503085e4, 0x11aa31e67ae6523fc72a930000013aa79, 0x1021084280860, 0x1d4147fd41dffe71d64b00c7f0013c6a3, 0x104308c6808e0, 0x166d453e753344c230523007837883dd,
      0x1187fe74bd6000000f4f270f4f8665d4, 0x1531618005008683f78313dfd40d3fd4, 0x18a00e82c0c2ca5e8a5e865d466d453b8, 0x18a00c5fb62424246500053053fe15105, 0x2008080300044001004800100802020080805a2, 0x11396f81e6ff81cef000010183f111e4,
      0x2010080500044001004800100802020080805a2, 0x4010100500044001000800100004020100805a2, 0x4010100500044001000800100004020100805a2, 0x4010100500044001000800100004024000805a2, 0x166d4530e0f53fe1abf0058a0c50eafc5, 0x10c9f0488cd0b500b616bf103fdc65d4,
      0x113ef0008a00d7f5e0d7f08169d2b9d04, 0x1118ff81e6ff8dca5d479d4106f14df5a, 0x1eaf8ea0d0f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1016bf6dafe644bf16bf150850d5f850, 0x1940940e5aa21bf3ebf105f2e5f0000c4, 0x1112f03112f03000000e67ae60756d750, 0x193093016af108f0f8f20000d301d4fb3, 0x1340230d5f23000000d4147fd40f31f30, 0x10004401000804020108040201001002040088da2,
      0x107937893000176f030e4fd466d40e7da, 0x1da78027035000000d40d3fd40f34bf3, 0x1105f230d5f2302300176f00d466d40b8, 0x10d0f0e5f0f8f176f030e4f000460da34, 0x1108f176f2000046b8da11c7f277cae0, 0x4400110100044001080802010080020100885a2,
      0x10e5f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10c8f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10bb39bfe6130f11bf1fff0230d5f230, 0x1000d2fe50d2f18df116ef170f0000c4, 0x80402010100044001080802010080022000885a2, 0x11f6f101f0000d3c71d4f0112fe3112f, 0x1d40d3fd40f3e5347523232300cef0eef, 0x13800da00196f0d5f16bf0059120ff338,
      0x10f36834b6234b230000e5f00e4f3866, 0x10097669700da00270000590f30d47ad4, 0x159120ff33800000034752323230000, 0x1038460da8718df159f0d5f18df00d1f, 0x1a406834b623542305a0dad295f0e4f38, 0x10da7318df277c0fdf00d590f1ff30000,
      0x15a0eef182f1f4f000046] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x113af] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1228f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1a3a33525252504815cfb3f303030300, 0x1f30351b2f3500184f00f31b2ff30f3a3, 0x10a3d32522504875b300316cf0300f30, 0x100068f36800000a400000003303300a3, 0x10eff114f1bef114f6dbfc3f377f300, 0x1349f99116dcf00000257a25ad6723bf,
      0x1425090a80960, 0x425090a80960, 0x1b3f303030301ecf11dbf2c3f0d6c0d, 0x1024090880960, 0x1f30f30f3a3a3a3352525251f9f4815cf, 0x100df315eff37a357a35f40edf184f3a0,
      0x1a30d1fa3d3258325f44875b3003003, 0x1a4444f144ff40f9f107f56000000ccf, 0x10d6716af0e1f1ecf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x15439000001b5f06db31faf0339030230, 0x12c5f3600001b5f756d757e23920235c, 0x10d3fa977f30cbff3000006834191fa4, 0x1364f5f36b704d00b6d684524f841a9, 0x4a5090a80960, 0x1030030200fd40cafd4b79726af976ddf,
      0x15431af0f2f0b977a971b5f366db30, 0x1188f97147f974d360e3f360000031af, 0x10b977a971b5f756d7500000cad45bd4, 0x10e9f1cdfd62c1fd6000000ba41c55, 0x1595c1cdf0c6f2c2f0c6f34ef0e9f0d3f, 0x15c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10e38383835593939301773733622200, 0x16b44cf6b0000dafeb00cbfd9019019, 0x10083083c3933393017f373023320280f, 0x1752d86f786a900cbf2946077870e30e3, 0x121bf2a6f99205f446f100000752a6f, 0x4410908809e0,
      0x193147f932fdf384f396f2e1f21bf6def, 0x1861e6f33bf1e6f2946177870e30e30, 0x445090a809e0, 0x155939393eb17737336222026ff8644df, 0x1c393c6930717f373020205586838383, 0x1f4a983c683] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1000e4f5b0000da340ecf230d5f230850, 0x1aa00000270a90b8daa9003003085039, 0x1112f440fd3107f1d4fb3003003075e5, 0x109366932d3f108f2d3f6dff112f0daf, 0x1116ef4eff8826ff88bbc412e100015, 0x4a5090a80960,
      0x4a5090a80960, 0x1084090880960, 0x197971f9f0ebf0e6f877be3e3e3016ef, 0x134203f230d5f2301e6fdc1e6f4e5b97, 0x10fef0fef0e4f5b238f238f460fefda, 0x10fef46b8da1c5f000000d0f0fef180f,
      0x10fef108f0fef180f8827238f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1e3838383559393930172fef733622200, 0x1200f70f70f1f55055005b0036525f360, 0x10e30083083c3933393017f3730235af, 0x1360000075777500000f4000017bf00e3, 0x18634bf8644ef0daf44ef6e0fc4360e3f, 0x110e8f11b7f6e1f00000930d3f93159f,
      0x445090a809e0, 0x846090c809e0, 0x136222021bf1315f275f0d1f0f1f0d1f, 0x10440908809e0, 0x1036086838383559393932d0f172fef73, 0x1f71ecff70f1f556e2f550715bd9036,
      0x445090a809e0, 0x11ccf83c393c6930717f373020200d3f, 0x1f413ffa9071b0f17bf8700000155f83, 0x10d3f86353f860ccf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10f7f3538939393094a6347523232300, 0x100177f00e4f3803800da0000d5f00059, 0x1020059035b6930393094683402339230, 0x10000d2fe50d2f00177f00270000da002, 0x178112f0daf112f2fcfd3c71d4f100, 0x481090880960,
      0x1c412e526f0000093669311cf0eef110f, 0x4a5090a80960, 0x134752323230277f1151f103f885c881, 0x8c6090c809e0, 0x1084090880960, 0x1013ff590f7f35389393930e8f94a6,
      0x10f7f3846110fda8712ff414f0d5f247f, 0x194683402302304c110f177f4b0e4f38, 0x1b9da73000004c59110f35b6935493a4, 0x14c0eef177f788827117f19ef46] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10e4f000112f0da340ecf230d5f230850, 0x1b8daa911af0314cf0308514391414, 0x1756d7500000e5aa142714a90000112f, 0x1f31f3b704d0027b994e9941e67ae61a, 0x4a5090a80960, 0x8e7090e809e0,
      0x12300daf93102f93b7d4147fd4353f, 0x1140e4fd466d4112fe7da341d6f230d5f, 0x113dfd40d3fd44df34bf300000147c14, 0x1d466d4112fb8da7811af000007937893, 0x1140d0f1495142714350cef] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10695969102f38000000347523232300, 0x138038112f0da3a2e0f1d8f0d5f1d8f, 0x10206834130f2339230141daf14140e4f, 0x11ada0d8f11af214cf20b6590345000, 0x10270d2fe50d2f142714169f0000112f, 0x1102f38d40d3fd42fcff3e53475232323,
      0x138112f205fda3a1d6f00d5f00695969, 0x14df368340230230147c14140e4f3866, 0x1da0d8f11af0000b6594b0e9f6cd47ad4, 0x114102f1427140caf0cef976697112f1a, 0x11459] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1331600004e704f42b88b525085858500, 0x1e6265fc7d50094205f940c5aa743374, 0x1e7dd00930c7f930c50202107fe666, 0x1e70400e3b5250033033ddd42bd41cbf, 0x1d40e70007937893003303316d42bd404, 0x134346623232300cfff7330331cbfd4ac,
      0x153053346623052304764476438000190, 0x1000000e534223b62304764476465000, 0x1036500053b853d366a305270e8640364, 0x1fbb4071e88d7e608505850149f470347, 0x12613a46696e4040aa957c956718000b4, 0x100107f9419401420ef14234fa500013,
      0x28000a000804020100804400100802020080da2, 0x1132613a46696e40401a2021e67ae60c7, 0x28000a000804020100804400100802020080da2, 0x11dffe7100930c7f93014fb1454a5000, 0x4806020004020100880102004020800800825a3, 0x153e7533402305230033033ddd4147fd4,
      0x1d4187fe74b0079378930000065d466d4, 0x153b853002705350f73303313dfd40d3f, 0x10000003486232323000300365d466d4, 0x1640000e30b834223b623023e36426438, 0x1040e0f04143f9313bfb515000ce86403, 0x166233f0b13bfd7150e4c3c49e9e16000,
      0x100132613a4a808c4083a6f00006615af, 0x103d198f16d87ad8040e0f04143f930b5, 0x1124f166f58100f585a0dcf08d00c3, 0x1d8660660000000fef00fefbc0d4f166f, 0x10b1ddfd7f601454a508008198f18d8ac, 0x1030300141e07183f6718000b4fbb4e6,
      0x18803b503005d32223500013013b32503, 0x10303053b8532796a32732000096096b3, 0x100d3d90cafd935977997131a13b32503, 0x10f4f67180e9f1e0e9fb4fbb488cd0d7, 0x116977a97961a96b300300300f4f11ff, 0x100cdf1f8f0cdf47b347b365a3d973d9,
      0x10f3f160cd2504e704f42b0b500858585, 0x1232300cff939693c5c7c5aa740f3f74, 0x1047644764389797971b1fa934346623, 0x1644764655b0d7f5b5396533466230523, 0x197649797b69736cfa9e534023023047, 0x1f765a30d7f2753b853d36600500e864,
      0x1016159315040e0f04000b5150047f747, 0x18d00080080c3000000000d7150e40570, 0x10d69bc0d4f00dcfa958100f58ca124f0, 0x10a95671810b150fb4fbb4077a0d70069, 0x441084280860, 0x16604047a0b50054a5d8a8d813261395,
      0x10000074106f7411df1625bf1b9f1604, 0x1bc0c4fbc1c6f9716df4616dfab7eab99, 0x17408165e1b9ff4040c9f04c47a0b500, 0x15bd744ff53b55334023052308507479, 0x10f765270053b85300030503085000065, 0x1367fa5965804132613a4660e400aa0f7,
      0x1965804132613a4660e400c714132f14, 0x1a9a934023232306593669314fb1454a5, 0x1b83402302305b9d64d8643897979783, 0x12323015ff0ce86497649797b6979da9, 0x1a979a9ece7126f9bec0ec0034346623, 0x11a210fd90f2f0119f0086f7932b93f7,
      0x15a4c0119f00cad65bd66b971e97119f, 0x100000f4fd60f4fd66b971e971a7f1aa6, 0x13886d64dd6119f970d3f97ac1aacd90, 0x13d000b40b43bd46e3f15150047644764, 0x11cff155f2a4f0ddf1500c5fc4575757, 0x10c5c5961ccf363f1ccf4d9f0000fb0fb,
      0x108a854a5d866d8132613fb100f0e40, 0x126ef040c9f0488cd0b50012dfc50c9f, 0x117df527f000000d7f5e0d7f081612b, 0xc620884808e0, 0x1173f127bf21df26af21df17df0f1f, 0x1c4409ce809e0,
      0x110339030230ea06ea43118f195f13df, 0x80002010100044001080802010080022000885a2, 0x12392023a3a4105f20000350f0528fb3, 0x1b83483940edf9400007ac77a0edf15ef, 0x1c6939b931a90d3fa9f7e70f5f9b00000, 0x1024090880960,
      0x16b9726af976e4f1a1d90f2f0119f0083, 0x104709ce809e0, 0x11977a976e5f1a6db30030030cad65bd6, 0x1084090880960, 0x1147f976b1a126fd900000a3a4203f4a, 0x17a971affc7268f10000086d64dd6197,
      0x10440908809e0, 0x1081090880960, 0x13b931052400e864b664839412ff94197, 0x1084090880960, 0x2008080300044001002800080402020080807a2, 0x11e42400c5fb6549857650005314bf53,
      0x2010080500044001002800080402020080807a2, 0x1c5b696f889f8450f0000a889a810b, 0x4010100500044001004800100804020100805a2, 0x165d466d45314bf533b9300500c50eaf, 0x12b0e9f040c9f0488cd0b500b65428f9, 0x1d4a889a81000000d7f5e0d7f08160e9f,
      0x441084280860, 0x1eaf8ea0d0f118ff889f8f9a5d479] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x153b553feb62bcf058a00c8f149f0c8f0, 0x12843434313013a79402424065636363, 0x1a543434313d71313a81e424014631463, 0x2010850408421, 0x1063b543b54300d30005424014631463, 0x1140a526106fb513013a4a808e4540063,
      0x18585015ff2c2c2c0cdf050cdf13af140, 0x14835434343134a2f13b3d3030303085, 0x1129f1bdf0137f119f137f0c5aa96096, 0x1021cf136f12cf0c7f12cf1c1f25ff, 0x10c5f8e0ea2cea2c0cff646464c502c6f, 0x14a0dff9a9a9a0a153f0a0a0bb0ddff60,
      0x1434313d71313d30e418bf00d3f4a1e1f, 0x12c118f646464c5e4c5c596089648a543, 0x1b543000b3d303a3030850c850ea2cea, 0x1636353b55334a42305230aa04800b543, 0x1114f1b0f6d870e386e30132713136563, 0x1f953b3a4e805e8002902bafa9099b09,
      0x12302c0564056413013065b8153f0353, 0x102c142714146563636353b5533402305, 0x101448147465b8153f035305300e805e8, 0x1a5265ab51301300a4e45400c5f0d0f, 0x113fb13331fd30e4108f0a811bf011bf, 0x16353b553fea40058a0960960a5260b5,
      0x1631326130f80f88a0c5b6013a7656363, 0x10ddf5805800ca8dbc005c50000e463e4, 0x10eaf0dcf127f10c4f0d4f100f17af, 0x840120000860, 0x1636563636353b553fe010df058a0118f, 0x1e463e46302600f810dff88a0eab66363,
      0x1eaa8634363] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x11baf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1bd0653153a7b6540515085149f850, 0x2101104210860, 0x12843434313d613a702a1f242406514bf, 0x10a5bd195f28130b1313a81e45700000, 0x2010850408421, 0x1000009343043d30005432af024014014,
      0x10140140a526106f9313013a4a808e454, 0x1232300cff646464c5fdc5aa27858585, 0x10523047644764386363630034349423, 0x12304764476465636363538853349623, 0x1b305b30064064063256300b634e823b3, 0x18500cdf47047065b81a4f25530532796,
      0x19423232301664446453b953aa0c858d, 0x105334023052300640643863636300034, 0x1b86300b634e823023000006563636353, 0x100065b800532753006b0500064064063, 0x135434343131e0f13b3d303030300cdf0, 0x1b5207443744355444444007373842220,
      0x1206207443744316444444048804732b2, 0x1f42b06b5060043043044254400c37383, 0x10ddf1a2f074074016e71c7f2504004, 0x100dff0d9f1e9f21ef0a10a0a9923af, 0x2101104230860, 0x10daf1c6fab0ab2f3f0451f10ff123f,
      0x120cf16ef10ff10ff03c03c0145f52cf, 0x13c03c0145f1e9f2a6f0dafab0d1fabab, 0x11c6f00eb23af12bf172f281f123f0, 0x120cf0ccf10ff281f000000395f0f2f, 0x13c03c0145f127f229f0f2fab0ab10df, 0x10faf13b3d30303030858585015ff1f8f,
      0x119cfa687c40000c5aa00003543434313, 0x1646464c5000b9136f1a5b0c4f188f, 0x16438636363115f03434023232300cff, 0x16465636363530533402305230476447, 0x164b6640630630b7034e8232230476447, 0x124004796472765b80053053002052094,
      0x157f5f5f528434343130faf13a7d3024, 0x1000004343430a0faf0aa7d3002400c5f, 0x19608960a5001a3f1301313d30e4160f0, 0x118fb0142fb40b422cfc40d711df0c5c5, 0x1000127f031df162f010012dfc5000b0, 0x1080042002200088300104004040801008051a3,
      0x1e603db40b4b400d70021ff127f13e07e, 0x40081002002200088100104004040801008051a3, 0x1013a70024240118f100f17bf11a8f18, 0x20100804000104004100804000020020800805a2, 0x1000000d7240ead34343432843434313, 0x1b3a303d3030850ea7a43064326432643,
      0x1a42305230aa0c85b563b563043043000, 0x16d8786e30e300000656363635315334, 0x501104240860, 0x1b3a400500460290a9099b09114f1b0f, 0x1b5f506402701365b82edf0653f953, 0x10b50064000016444444041041dc3234f,
      0xd031046408e0, 0x1230011af03d160e0f172f9a041043bc3, 0x501104240860, 0x1e4240e9649564386363630003402323, 0x123014631463a543434313013130117f, 0x15409464b664b963b8630b7034e823a4,
      0x10149614a4a526112f0130130088e4, 0x1a5265a01301300a4e45400c5f0d0f, 0x1130131d0fd30e4108f0a80fbf00fbf, 0x10653053a7a4005150960960a5260123f, 0x10613013a7f80f8150c5b601306514bf0, 0x10e0f09a040043bc30b5ae0c500001800,
      0x1100f17af05805800ca8dbc09303d016, 0x1d305150118f0eaf0dcf16df112cf0d4f, 0x400810020024000881001040040808020100d1a3, 0x1150eab64306436514bf0cef05305300, 0x1eaa84312cf430fb000000f8d3f8] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1286f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x10cdf530cdf13af0d0f0c8f149f0c8f0, 0x16464c5d5c5aae8858585015ff2c2c2c, 0x1bb0ddff600c5f8e0ea2cea2c0cff64, 0x14a1e1f4a0dff9a9a9a0a104f0a0a12bf, 0x1850ea2cea2c118f646464c513c5c5f80, 0x127e4036563636353045334542305230,
      0x1065b8104f1353e853e80030503085e4, 0x1430443d3eca3b30030030c60caa0089, 0x1345423052302c53645364b448b46a04, 0x1e80005002c1427141465636363530453, 0x10058a001448147465b8104f1353e853, 0x100c5fb624242465636363530453fe54,
      0x10d0ff8000013631363f826f80080e48a, 0x1582aa5265a0413a41354080e400c5, 0x10a58ca58bc106f08d0053c5a80c6f, 0x10eaf0dcf127f10c4f0d4f100f17af, 0x840100080860, 0x1636365636363530453fe540058a0118f,
      0x1436313631363f826f88b0008a0eab663, 0x1eaa863] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1430c4f435c5439b3154f0339030230, 0x14355444444191f370e6f73e322200f7f, 0x1001c4444440dcf0e5730ecf239200430, 0x10439344f344191f37189f7302c32000, 0x100000be7000dcf0e533154ff45c00043, 0x122205c7520ef7507a40707462392023,
      0x139460000055444444191f370e6f7346, 0x1202000001c553c9f550dcf0e5294646, 0x1f45c0000009344f34411ff3711ff73c3, 0x10dcf59e53400000b25000dcf0e5ca46, 0x145454505454b3840303030b6636863, 0x1cc52df0c6f4b9a9a9a7e8b8b3a192f,
      0x1308f67e956033033063354343436e8f, 0x13a0000063e907e910bf220f061c6f06, 0x10e9cce92ebf196fd61eefd621df8be9, 0x100001c4444440dcf189fe57302392003, 0x10b30f4000be7000dcf0e500335c33003, 0x1110f0606065c0e6fa6a67a2bef0f8f15,
      0x1191fa65c7a6e9f0f8f9805495449544, 0x14395191f95154f110f368f258f3d5c, 0x14444191f370e6f73022200f7f430c4f, 0x1a6a6ac299f0f8f15010bf43e9435544, 0x1730202095449544110f0606065c0ccf, 0x11b5f007643c3439344f344191f370e6f,
      0x195070dcf0b16af1faf5c7aa6154fac0, 0x19344f3440371d3f730216cf200309579, 0x1000f30f308408403316cf330030f4033, 0x1d6063606c467d456033033054d3b300, 0x173020206394437543213fbe2d2f9c, 0x1000063e9f4e91b3f9344f34407371d3f,
      0x10e9bee96eaf4af30e7ff30784439f840, 0x100000055444444191f370e6f7302220, 0x12000001c553c9f550dcf191fe5290039, 0x15ce30c303309344f344037073020ecf, 0x12a07000000f4000b25000dcf0e500e3, 0x1003c870daf87191f363b4f36154fe6,
      0x16a0dcf2e2f1f12ef5c2aa6077a01b5f, 0x131af5c154fa6077a01b5f00a4957995, 0x105c7520ef759579951b5f0dcf0b52ef, 0x14410bf44780606064a6756560333333, 0x11115c0ccfa6a6ac335f0f8f1bef01f2f, 0x841104280860,
      0xc61104280860, 0x841104280860, 0x1ba67e656033033095142f950c4f110f, 0x17aa646ac01b5f007644c444d6063606, 0x1957995070dcf0b16af7e5c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1232300cff646464c51c5aa0385858500, 0x2101902310860, 0x123052304764476438636363003434223, 0x1b6230476447646563636353045334f5, 0x10354005270064064063063e800334023, 0x105850149f47047065b8104f13530353,
      0x1003422323230536453640ce323aa5485, 0x15304533402305230064064386363630, 0x1b863e800334023b6230000065636363, 0x1104f135303530354270500064064063, 0x11f8fb4c50cdf830cdfaa0d0f000065b8, 0x144119f29af7373842220858585015ff,
      0x100cff646464c51c5aa74437443554444, 0x1ebc1307983cc001023000f7439a0f379807d4c20bf8f303cc0f4e60079f98443b860f3079801e60f6a45, 0x1476438636363115f21cf343417232323, 0x16465636363530453341723052304764, 0x163234f63e8b773340230230476447, 0x113534fcf537354005009464b66413ef,
      0x100d6f00c5ff504796472765b8104f, 0x106ebf17ff3adf131f27af12ecf100d6f, 0x411104280860, 0x411104280860, 0x101e5f012cf012dfc513c5c5f8002c8f, 0x1127f13eab7eab31df162f127f131df,
      0x840108080860, 0x840108080860, 0x1e631df3db40ab4b400c4fd70c4f021ff, 0x1a706142f24240118f100f17bf11a8f18, 0x840108080860, 0x10240ead34343432843434313299f13,
      0x1ea7a43064326432643b4501fb410142f, 0x485114a80960, 0x10000656363635304533402305230850, 0x10270065b8104f1353053054030503085, 0x163046304430443a3dbd3b30030030aa, 0x115df9a107f9af70d9f993a045045004,
      0x113402323230536453640c1b09115f09, 0x1004110880960, 0x1e4240e9649564386363631fdf325f, 0x123014631463a543434313b413130117f, 0x1e4009464b664b963b863e8b7a4340230, 0x100149614a4a526112f0413881354890,
      0x1b609806514bf013530533b5400524, 0x1f8000013013b4f80f80080e42400c5f, 0x1a5265a0413a41354080e400c50d0f, 0x1ca58bc106f08d0053c5a80eff58251f, 0x10dcf16df112cf0d4f100f17af0a58, 0x840100080860,
      0x10cef1353d3533b5400500118f0eaf, 0x1f8d3f81a7f00000eab64306436514bf, 0x1eaa84312cf4313fb13b4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x12c] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1121f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x115ff] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1333333034b623232300c8f0c8f0c8f0, 0x1333306d06dd9780606060f1fbea6562a, 0x100006767780606062c8fbe5656d633, 0x11a5b2acf0f1f181fa61bdf191f0137f, 0x115ef330330593863636300027df0caf, 0x1840330330ac0ac00e7436f0d3f00e5ac,
      0x1e5ac15efe30e30000d1f00f378f30840, 0x1c43333330030303013afac0ac0000000, 0x148d5b36a466a87780606061d6fb9a656, 0x1061b9a656ca3333330e573354343437c, 0x1004110880960, 0x1c433333300303030e56a076a87780606,
      0x148b3b30c6c6c6780606066ecfb95656, 0x12b3f560330330a3a3a335434343348f, 0x102220026afc626afc6d4063606444fb9, 0x123320191daf0ae0e5544444419457373, 0x11d8f00c30330eefe344137f440450730, 0x127df18ff1a5b2acf1d6f134fa687c40,
      0x155444444d93a73730722201e7f01e7f, 0x1133fa67302020d51daf3a150f17ef, 0x1123f7cc30dbf1b0eef1b441c0f44191f, 0x112ef129f1a5f01c1f000fcf5bc755, 0x113df16af339f1d4f504f29cf2f7f2c6f, 0x19b0d6f13bf18c16ff3a0000013df1b7f,
      0x1084110880960, 0x112ef2fff1a5f01c1f00bac844dfc849, 0x113df16af339f17ff452f16ef2f7f28af, 0x10230d5f230121f291f2c2c2c13df1b7f, 0x195951c444444181f4ee51dc3039f5, 0x1142714140e4f6363636c84da349511af,
      0x12742e3c755951bff0d500219200121f, 0x13c8f441f3c8f06edf0324f002a8f0074, 0x1219c7950c7f0000023920521f12a8f11, 0x1084120840960, 0x1084120840960, 0x1084120840960,
      0x112cf0c4f181f134fe5fcc30000d320, 0x1266f3ad573f40d900950951b3f00c4f, 0x1133fe57300000da7473747387c75595, 0x109446cd3c81c0fc80dbfc795224f1eaf, 0x114761495334f44] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x1f927ef125f1ae0058a00c8f149f0c8f0, 0x304042408421, 0x1feb6010df010ef1197f173f02d0ff96d, 0x804d400020001000000014000000050000804d0200000200800000801002000002000004402680010000200024000000040010804d0020000040080800000040002000100008ffc26, 0x1095dc18003db479b4b41b8fd6d7d6053, 0x14343131e13a794024240656363635395,
      0x14343131e1313a80e4240146314632843, 0x11843064300d3000024014631463a543, 0x154a526006130813a4a80e4000635463, 0x1b40f9fb43bc401515000cdf13af14014, 0x1883bc40330f150e405757573d060606, 0x10d7193f00112eff172f060606880f9f,
      0x411104280860, 0x415110a80960, 0x1079219f18172f281f26efb488b4b4c4, 0x1000001437a515af1e9f281396131379, 0x1358f518f358f355f6eff1453f6eef, 0x485104a80960,
      0x185015ff2c2c2c0cdf142d0f1522f6f0f, 0x485110a80960, 0x14835434343130b13b3d303030308585, 0x10ea2cea2c0cff646464c5a8c5aa96096, 0x143130b1313d312bfe418bf0bd0c5f8e, 0x1118f646464c5a8c5c59609648a54343,
      0x1636353d7533402305230850ea2cea2c, 0x1b8005305300030503085e427e4036563, 0x1636353b45334a42305230aa0e80e865, 0x1114f1b0f6d870e30e30132713136563, 0x1f953b3a400500f7298629afa9099b09, 0x10c2ca564436413e813e865b8206f0453,
      0x124246563636353053fe01058a00e82c, 0x2008080204100104100804000802020080805a2, 0x1063183f630260001e48a00c5fb624, 0x2010080404100104100804000802020080805a2, 0x19a13fb13331fd30e400f81e6ff81cef, 0x1b453fea40058a0960896108fa526106f,
      0x11310008a0c5b62bcf13a76563636353, 0x420104080860, 0x15e43c5f8155ff86f1f796379631326, 0x1eaf8ea0d0f118f0eaf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x100e53bc311af0f60850d5f8500c8f0, 0x134a4230d5f230aa000f8f000e0f0123f, 0x10730293200e5176f030e4f63636300da, 0x1b3a427000114f37105f33c344f344017, 0x17c031c03064446400176f00b80000da, 0x102316af108f0f8f2d3430f7f430840b3,
      0x1176f030e4f636363084da340230d5f23, 0x1142f00da00277cae00d0f0e5f0f8f, 0x10d5f2300c8f0e5f108f176f2c4b8375f, 0x12301e01e0000000e5fcc311af09e023, 0x120ac59ac843863636300034a42323, 0x1066e56600e4f38230f3800da0a420d5f,
      0x127000059084063686300e534b623023, 0x1139f9800d2f660660000000da73a4, 0x1100eb0c4f1acf0c4f00dbf00139f516f, 0x80402020080102004100404010080020800885a2, 0x100d3c7139f123f00007ce31c5500d2f0, 0x105900386363630840340232323000eef,
      0x1000000e4f38230f3800da87000d5f00, 0x17c0005900a4636863084034b6235423, 0x123085013af00eef00c44404400da0027, 0x1d539d5d50e4f63636300da3439230d5f, 0x1d50d500b82b4fca027daf4c303003085, 0x1372ae6c344f344d617937302020daaa,
      0x11461146f0e1fcd112fcd9d000002a, 0x844118c809e0, 0x1004110880960, 0x1437c841cb300300306444640e6f10e6f, 0x1004110880960, 0x1be2a560330330a6108fa6d4d3430f7f,
      0x12302a11df2a15bfc4060e6f061f6f, 0x1a6d5d50e4f636363cd84da34a6230d5f, 0x173c4b8204f6acd27dae5a600000d0fd5, 0x144f3440250730216cf20030d5108fd5, 0x10f3000003316cf330030830d1f83220f, 0x125156f7302020b30f40d1f01c1ff3,
      0x10000482adf830d1f83220f44f34413ff, 0x10d1f6f2f1c1ff37bf313ffb9156f560, 0x1186f00000a30d1fa3d343754321fff4, 0x10d3f6f4f0d1f113f16f3f199f115cf, 0x424104a80960, 0x1c2410ce809e0,
      0x10038636363000342232323000d3f0ccf, 0x10000e4f38230f3800da03920d5f20059, 0x10059000636863b60033417bf23392300, 0x10330330da3400000000027daf4c3202, 0x1001ccf671ccf190fc4063606d6bed456, 0x1216f460c4f146f0c4fcd112fcd9d000,
      0x1139f0dbf139f10009800d2f0fdf10fdf, 0x1084110880960, 0x4e411ca809e0, 0x100d2f215f1215f278feb0c4f1acf0c4f, 0x1084118880960, 0x10f1f101fd3c7139f123f7c1b1c550000,
      0x16363191f841f6f34023232300f1f0eef, 0x1870415f0d5fae0188f59188f13cf3863, 0x16c25bf6c278f0e4f38230f38cd0dbfda, 0x1596c13cfa4636863b68454340230230, 0x11f4fc44452ff44cd27da183f000006c, 0x1930b3003390302302c228f2c6c0eef6c,
      0x1000023920235c5439550f7f430c4f430, 0x193e5b30030030340a4005c7520ef750, 0x10000094e554e5550f7f430c4f430dcf, 0x1a40dcf191f5c7520ef750dcfd6e573, 0x10850121f0dcf59110f35b66368630dcf, 0x13914140e4f636363025da340230d5f23,
      0x114271407cb80000da000314cf0308514, 0x10e4f6363634c25da34a4230d5f230aa, 0x12fdf49df4cb9dab3a400009414e51414, 0x1140d0f1495276444641427141d6f7cb8, 0x13863636325333334023232300121f, 0x1230f38025da3a000d5f00695969102f,
      0x16303303402339230141daf14140e4f38, 0x1132f000da00214cf20b659034526368, 0x1636325565634a4232323014271407c1a, 0x14c25da3aa420d5f20695969102f3863, 0x1e534023023014e514140e4f38230f38, 0x173a40000b659760dbf766368630e5fbe,
      0x10d2f1427141d6f7c1a132f1f1f4cbada, 0x1145914102f270d2f1acf] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 4 [0x13543434313013b3d3030303085858500, 0x174837483000f400e5000000c5aa0000, 0x163631903434023232300cff646464c5, 0x16363530533402305230476447643863, 0x1182f63045034223b6230476447646563, 0x11edfd35305300a305270e8640364163,
      0x294920940960, 0x111afb5f608505850149f4703470365b8, 0x1aa044bf029bf160e0f117f0041043bc3, 0x88b000222c0004bf000f33cc03ccf379801e603cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x1e300000656363635305334a42305230, 0x1860450a9099b09114f1b0f6d8746e329,
      0x106400300365b80053f953b3a42705130, 0x114234fa526127fa4130130096e444, 0x1a526127fa4130130096e4160641420ef, 0x1643863636300a6340232323014fb1454, 0x164e363b863045034223b623023e3642, 0x1434313013a7150eff2424000ce86403,
      0x134ff12eff9930effb52400500002843, 0x16f6f6f5f217f053a7b654000043043d3, 0x10297f036ff11295f0454f236f1236f1, 0x3db3000f6cc001f53000f33cc03ccf379801e603cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x80004000201e100000018400000041000000500040201e0040000400200200000200000800040008100f00040400000040009000080010201e0004080000010001200010004895726, 0x3db3000f6cc001f53000f33cc03ccf379801e603cc1e60f6cc001e61e679801e7e60079bcc01e64f404,
      0x80004000201e100000008400000041000000100040201e0040000400200200000200000800040008100f00040400000040008000080010201e0004080000010001000010004895726, 0x10749a160e0f0f404060406930b50053, 0x118df00a00abb1e1f1ddf0ddfae074, 0x1fcfcc80575706514bf0ce08b0dff15af, 0x1a80e45706906690614ff09090922bfdb, 0x113bfb5150140149aa5002813106f1313,
      0x1a4a80e4000f400160e0f0d004004093, 0x1aa2785858501401454a5260c3130813, 0x125fff4226ffde5fd10cf0226f00c5, 0x12300cff646464c57483748313ef23cf, 0x104764476438636363d93a3434942323, 0x14764476465636363530a533496230523,
      0x1e864b364163182f63733ab6340230230, 0x4a5110a80960, 0x1b347b365b81edfd353a353279600500, 0x16363635305334b523052308500cdf47, 0x1065b800532753f4c3030503085000065, 0x1139613441e5f0e4006453b953aa06b0,
      0x11316180e4006414fb148ba526127fa4, 0x194232323014fb1454a526127fa41396, 0x1000f3f64e9643863636342df1a9fa634, 0x1172f956718fb1e9f07b488b40aac0d7, 0x16415df63b863ba1a9fb634023023095, 0x14313013b30030303000cdf0ce86415df,
      0x1439643000b3003b503005d3222354343, 0x10e0f011af040043bc30b500a3244296, 0x143131e0f13b3f403030306606660616, 0x1125f04b3003003053d3737373354343, 0x1b8112f2753a3142f44123f9643964304, 0x121ef0a00a0a000ddf0004743474365,
      0x1010ff008d99110ff376f0dff0d9f1e9f, 0xa14120d409e0, 0x112a6f359fac1e5fac281f0127f0113f0, 0xa14120d409e0, 0x1200fab1e5fab104feb010ff00162f, 0x100d3f0ccf0d3f281f145f127f229f,
      0x11e9f21ef0a10a0a10df23af0ddf1a2f, 0xc21104280860, 0x123af01a2f0589923afab2f3f0dff0d9f, 0x1257fac1e5fac281fab127fab113f0, 0x1691e9f0d4f100f6f7fca58162f12a6f, 0xc24110e809e0,
      0x17373c32220232323015ff1f8f697a, 0x13a0000034346606617554444446b2ccf, 0x186f7b7eeb77a9b7a123f2a1f119f16ff, 0x113013a7d302424004764476438636363, 0x1d32f0f148f2400c5f0f5f5f528434343, 0x1002a3f1cff332f148f434343000a7,
      0x12a5fa5111a3f13530f1313d30e4160f, 0x1014208482121, 0x1014210482521, 0x179142f5841ff5822cf00000c5c596096, 0x143118f1112dfc55e106f5e127f79106f, 0x840120080860,
      0x840120080860, 0x143528f430860b300339030230ea06ea, 0x1940c700000002392023a3a4105f2350f, 0x12aa643a643186e5b300300303483940, 0x1004110880960, 0x11fdfc73b4f11f7e57300000c6a3a42a,
      0x1084110880960, 0x1084108880960, 0x1052400e864b6648363b8638394368f94, 0x12400c5fb6540576514bfbd0653053001, 0x210920108860, 0x10e400f889f8450fa889a806000001e4,
      0x210920108860, 0x10960896108fa526106f25131131d0fd3, 0x1014210482521, 0x1b65413fc6514bfbd0653153a7a40050, 0x421104280860, 0x1c5f889f84da889a80613113a700000c5,
      0x421104280860, 0x1eaf8ea0d0f118f0eaf5eb6] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 4) (a := [0x11baf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x137053feb62bcf058a00c8f149f0c8f0, 0x137f505300e0f015160000484048411b5, 0x500a04210860, 0x501204210860, 0x1215f08f501d7f4315430c30c30084000, 0x10840000f50d743d7430c30c366066108,
      0x218048408421, 0x1a7941bff24240650430e0f430c30c30, 0x11313a81e42401463146328c30c313013, 0x218050408421, 0x11a8f3faf5424014631463a5c30c3130, 0x108e4540b563b5630c30c30e0f0d3234f,
      0x100cdf13af142614b5a500013d713a4a8, 0x101516000049c043bc39cb5370e805e8, 0x1000035000134813b3f4030303000e0f, 0x1b50b50d30250044804b3f403a303053, 0x144e344d4c476c40b9056033c633053, 0x11d71660e8f66990000034cf8937018af,
      0x84220010860, 0x84220010860, 0x1db441a44d4c476c40b9056033c6330d7, 0x115a5153f0f4f281396131300e4000365, 0x1a5d70f4fa413013000e400b814153f14, 0x1073730222023e82300cdf142614b5,
      0x1d5b3f403030303401700559393930caf, 0x100008378830e5a4e5733594a894103f0, 0x1a30cafa301c3fe70331eefd61b8fd60, 0x10b63c1fc7151f25b0a80131f0d573f4, 0x1a41b9f933594a894103f0d5b30030303, 0x15b93a893131f0d500a30cafa30b61b9f,
      0x129ff980f88a00caf640364131fc71c2, 0x10f914cff904d3a9f4d00026df159f2d, 0x14a1e1f4a0a00a0a0120f0ddff60f8, 0x1a8941301313f40e42400bbab0c3f0dff, 0x11b8fd600000164f8937004a40404a594, 0x1a80130131df40e4540d7bbd71d5f18d6,
      0x1a894130131303ee4240b6042604b5a50, 0x101300144fe4540b61b9fa41b9f93a594, 0x1e8230e464e464162616b5a593a89313, 0x1345b17e701930d1f9300073c32832023, 0x80402020080402010100404010020020800885a2, 0x18303b7fa439009409410e5b3003a3030,
      0x1020040900044001008100204100100201029a3, 0x155a30dde70331d60d1fd60000078378, 0x1024220820960, 0x103a3030b62e7fc7392000010e5730a3, 0x1040041100044001008100204100100201029a3, 0x155a30b63b7fa439931947a94000b3f4,
      0x1004220820960, 0x15564b8642e7fc73921937a930000f4a3, 0x1084220820960, 0x1454513013b3d30303030858585015ff, 0x10d600d500a30a30c5aa96e396483545, 0x1842b84040047302b520b6c50c7a820d6,
      0x18e0ea2cea2c0cffb60d7ff40d7f2516, 0x1390f1301313d3153fe418bf00ddf0c5f, 0x101300d7e4540c5c596089648a50ddf5e, 0x10401e4fb5b50b6c5026a8b5a5d60d613, 0x1118fb60d7ff40d7f2516842b8404004, 0x15334a42305230aab8850c850ea2cea2c,
      0x1d600000a30a301327131365489648530, 0x1096053053b3a4e805e800c73920d60b, 0x19648530533402305230b613b8130365, 0x15305300e805e80b60d7f270d7f256548, 0x10d0f0052c052ca5b8a50365259625, 0x1a505e013013331fd3d7e4108f0e40c5f,
      0x1153f284f53053fea41058a0962696b5, 0x298252442521, 0x1130130ddff81f88a0c5b6113a765335f, 0x298252442521, 0x4040101100404010002800080802020080805a2, 0x1c3c3c353053fe00058a0c5e40e400000,
      0x110ff2b16040040400b500b6c3c3c365, 0x1c30000ddff80f88a00d7ff40d7f2516, 0x1ea0eafea05118fe4c3e4c3a5c3c4]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x11baf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x16d76111ba053a7b6540515085149f850, 0x501204210860, 0x500a04210860, 0x501204210860, 0x113013a702a1f2424053110ba10004976, 0x501204210860,
      0x504204210860, 0x3db3000f6cc001f53000f4e6003d3987980f3003cc1e60f6cc001e61e60f301e63cc07987981e64f404, 0x10c4f000066066108bd08ae0000028000, 0x218048408421, 0x19300016000d30005432af02400bbd0b, 0x114ff99099253f0fcfcc8328f5757065,
      0x19aa5bd0281301313a81e457069066906, 0x218050408421, 0x1a5000130b13a4a808e454014bf14bd14, 0x1fd7334af730c5aa27858585014261493, 0x1a30373030c50c70d61000163f94d594, 0x501204210860,
      0x196b3a30373030063d6630d30d30094b3, 0x10094b3a30373030886388630d30d3960, 0x1034349423232300cff063c7630d30d3, 0x153349623052304764476438d30d3196f, 0x10b634e823b32304764476465d30d3530, 0x188532796b305b301a6425640d30d3c7,
      0x18d84b58408500cdf47b847256500053, 0x1117053aa0c850e70451600004250433, 0x501204210860, 0x10030530fafc70d61000b9946a94b917, 0x501204210860, 0x102305230063d6630d30d30094b3a303,
      0x10094b3a303003000006500053255334, 0x10053275335168405840063c7630d30d3, 0x16438d30d3000349423232300b8078650, 0x146046b40b4b41e330fd715030bf64e9, 0x10d30d3c70b634e82302309544954418, 0x118000b488b4071e15afd76701a64b864,
      0x113b3d3030303085858500cdf95fb95e6, 0x117a673832020c5aa000035000131e0f, 0x10d60b3a30384030c50000c309300fdf, 0x1d300b0b3a3038403006306393d394d3, 0x194d30d60b3a3038403006306396d396, 0x1d3003434023232300cffb763c76393d3,
      0x1d353965334023052304764476438d393, 0x10e7034e823172304764476465d30d7f, 0x12753053003305330064064c7d3b6d3, 0x18901b7ff50f815047b84706500d7f, 0x10101f0101f1827cf1b7f1d7f000104f, 0x1f40e4150d3001d0000000a7f400240f8,
      0x10b4000024004a40404a50a8281301313, 0x10a80130133bf40e45402602600000b4, 0x1c4c4b40b4a700153f24004260477afa5, 0x1a828130131300e400d3c4c4c40dffc4, 0x199c4000000d72401b9fa41b9f93a597, 0x1d8a8d813013000e454026c426c418c4,
      0x1060600909090003bc4001501626160a5, 0x1691800b26efb40b4b4c40d7193f0d406, 0x11817bf13db40b4b400d7006915bf69, 0x404010080402010100004000080022000805a2, 0x10b40b422cfc40d711df0100fe601a8f, 0x104b073832842085069fb691f2f1800b,
      0x12305230aa0c850caf43e7435bc325c3, 0x1176a7383202000006500053045334a4, 0x1534953b3a400500a90e70c30930114f, 0x194d30d60b3a303840300b8006527013, 0x1c30880117f89191f76f5006306393d3, 0x194d30d60b3a3038403004304366c366,
      0x193d3000340232323065b763c76393d3, 0x1000040041dc3234fb5f5006406438d3, 0x164c7d3b6d30e7034e82317230000016, 0x1001611af00041043bc30b5001a64b8, 0x3db3000f6cc001f53000f4e6003d3987980f3003cc1e60f6cc001e61e679801e7e60079bcc01e64f404, 0x1760faf000013b3d3030303015ff00e0f,
      0x156c633453301301a0b9100022af76a6, 0x501204240860, 0x107956c63345330044b9440c40c40076, 0x1007656c63345330884488440c40c479, 0x1c41f1f07373842220350441a440c40c4, 0x1c40c404004732b2b5207443744355c40,
      0x1430c40c41a0c373832e3207443744316, 0x12516000048804f42be3b5e30107f4325, 0x115151513013a7d3101f24240074e774, 0x1000a7d3101f294f2400c5f57f5f5f528, 0x1160f0fb35ff139f267f1a0f533f127ff, 0x218208442121,
      0x196138fa5cb5e1a3f1301313d3101fe4, 0x1a80a59c09c13013000e4540c5c59608, 0x12b21ef040040400b5b5012dfc5026, 0x123af0ddf1a2f00d7ff40d7f25161e5f, 0x100000dff0d9f1e9f21ef0a00a0a99, 0x1063d090909b40b43bc4190f15150118f,
      0x10a00a0a994fbf0ddf1a2f0ead40606, 0x1127f0d9f1e9f52cf0dff395f1e9f21ef, 0x122cfc415bfd711df00c5f0d0f01f8fea, 0x1d4e4108f00bfb13dbf180127f0b40b4, 0x298250442521, 0x105150962696138fa505e0130131d0fd3,
      0x1150c5b614bf13fc6501053053a7a4e6, 0x298248442521, 0x105150c50b15af00000013013a7f826f8, 0x100b500b614bf28065c499c453053000, 0x1f81500d7ff40d7f251602b160400404, 0x1b5ae0118f0000a5c4127fc40000f826,
      0x1930e0f123f9a16012cf0040043bc3e6, 0x1ea0eafea]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x1286f]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x10303000cdf13af0d0f0c8f149f0c8f0, 0x1103b503005000035000134813b38303, 0x500a04210860, 0x11369f3b9f9e0040040d30208348a3b3, 0x501204210860, 0x1e853e80100e6f110df06e77bf9c6d9c,
      0x501204210860, 0x501204240860, 0x1448744d4c476c486b9c656033033053, 0x1660e8f66991cff1c9f8937000001c3f, 0x144d4c476c486b9c6560330330b41b488, 0x84204080860,
      0x128139613138937e43701365db441a, 0x1136d10e400b814104f14b4a5104f0f4f, 0x40101004804020200841020041001140100a3a3, 0x10302300cdf14261404a5b40f4fa4131, 0x421204280860, 0x1135fa43923594a894103f0d5b3830303,
      0x114ff735b0a80131fa3d5a3020caf2023, 0x1d61b8fd61c3f83788300000e8340c7, 0x10caf867373c6222077cfe7152fd91eef, 0x1830303030b61d7f17135fdd55939393, 0x1b61b9fa41b9f933594a894103fc6d5b3, 0x11c735b93a893131fa3d5a3f700caf00,
      0x11301313080e42408a0d564d564131fc7, 0x129ff26df02d0980b5a4b5b5a594a894, 0x10e4f500e6ff90e6ff904d3a9f4d017ff, 0x10ddff605e265e04a50a80130135408, 0x10dff4a1e1f4a0a16bf0a0a12bf120f, 0x1d60ccfa9893700000f812bfbbab0c3f,
      0x113083ee4240b6f8b4bbb4ab18d61b8f, 0x1e400b61b9fa41b9f93a594a894139713, 0x1136416261604a593a89313971354080, 0x1a4e5209409400a3b3003390302301364, 0x1e834e5c7e5000000a355a302392023e5, 0x1dde76b1ebf1d60d1fd60783788300000,
      0x1c27208e809e0, 0x15b17e71ebf1930d1f93c386837302020, 0x1084208880960, 0x1e5a4e5931947a94f4c6a3b30030030b6, 0x1004208880960, 0x164e5c7e52a1937a93f4a355a300000b6,
      0x1084208880960, 0x1a3870ec00c5aae8858585015ff5564b8, 0x1b520b6c55ac7a873f7d6c6d6141fa3d5, 0x10d7ff40d7f2516842b8404860473672, 0x100c5c5f80a0c5f8e0ea2cea2c0cffb6, 0x15826a804a5d6100fd613b41354080e4,
      0x116842b8404ab04045e206fb5b50b6c5, 0x1230850ea2cea2c118fb60d7ff40d7f25, 0x1085e427e403654896485305334542305, 0x1fbb8891365096053e853e80e0f030503, 0x1e5c7e52a1d60bd6f7a3c6a3000000caa, 0x1425210a80960,
      0x1256548964853835334542305230b6b8, 0x12553e853e80e0f00500b60d7f270d7f, 0x1546d058a00532c532ca5b8a513652596, 0x1e48a00c5fb624242465f5f5f553053fe, 0x10d0ff813113001cff019dff80f80a081, 0x4a82904529e1,
      0x4a82904529e1, 0x165c3c3c3535853fe546d058a0c513c5, 0x12b1604ab04045ea9b511df0b6c3c3c3, 0x1c3f8fbf80a0108a00d7ff40d7f2516ab, 0x80600200200000800002000800008002000004200000010800000010800000042000800540300000400400001400000004004080000020200000080800000102000000100028ffb26, 0x1ea0eafea53118f13c313c3a5c3c4]) (b := []) (by decide) ?_
    decide +kernel
  · exact SearchNode.check _ 3 [0x10055000250f370e6f73c322202323230, 0x1174f2b4f0f0f262f1daf059a63400, 0x184200e8f1139f0154f9e09e254f1129f, 0x500a04210860, 0x21b37307983cc007a73086ce36507987983cfcc21b28f303cc0f4e6007980f736501023000799e60f6a45, 0x17302e320043f34393c333c3037073e32,
      0x1037073e328420043f34393c333c30370, 0x1054b3b30030303038043f34393c333c3, 0x1540b30030f8f030063102f6335c3e3c3, 0x10540b3f303d30300633c630f7fc32c30, 0x13c7502020000000a40063756394c32c3, 0x1075] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d5f0000550001a1f223f7373c322200, 0x1570000055000379f223f26df73c32220, 0x1000001c0010af1a1f1e53e2fc377df39, 0x501204210860, 0x109b0290d901a6f171f6d8711ffe33ae3, 0x11254f1129f174f161f11daf217f0da46,
      0x501a02310860, 0x501204210860, 0x3db3000408c001f53009066600799e6003db301e612097980f307980798f307980f31e607981e612d44, 0x10fdf1fbf00e8f1139f0117f28df117f, 0x3db3000408c001f5304d5e6607981e6003db30f309ab9f30f3079800798f307980f31e607981e612d44, 0x10cd0cd11a6f381f6d2b7f11ff2dff,
      0x40400000101000000084000000410000d6d820000004080001080040000020200004006b6c01000002002000040002000010d6d80020000200080000800100024000100008ff926, 0x10010f8f10af00800660660038460146f, 0x3ccf3003ccf301e67a46de6607981e6003db31e60f5e0983cc1e600081e5087980f31e61e601e612d44, 0x11400990ecf200d5003303300e4f38010, 0x3d398003d39801e9ccc6de6607981e6003db31e60f5e0983cc1e600086e0c87980f31e6f3001e612d44, 0x10177f132f0ecf000d5d500176f0014c7,
      0x100c7000993920000033d333014230f14, 0x114fa1400960ecf3900d50000a4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x116a0c3f4617bf1b7f1bff02339230, 0x500a04210860, 0x1e503e5030340000154f130f077ef1f3f, 0x128df059f40000f7f02011cf54e5b3, 0x175075154f20211cf37e5731a5fa41c1f, 0x103043f34393c333c3037073e328420f4,
      0x10b6043f34393c333c3037073e328420, 0x168063f36335c3e3c3775454b30030303, 0x1020063756394c32c30540b3f303d3030, 0x1c30f309303301a6f376a7302] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1248f0e6f0c3f14cf1f0f14cf2a7f020, 0x19e0299248f132f10cf7c1f0f7c021af, 0x173000007c11af001a1f1e5fcc3e616ef, 0x501204210860, 0x10c70ba2900011cf0eefd573f47317ef, 0x100011cf0eefe573d30eef28dfba0da,
      0x16d269f11ff990fdf106f0f4c70ba117f, 0x1c40000460146f0cd1c7fcd01a6f0faf, 0x1669e001a015df0daf00013ff171fa687, 0x10e8f32ff25af10270000000000006688, 0x500a02210860, 0x10f0f2020c412efd885c880277f12afc,
      0x501204210860, 0x504210210860, 0x100176f00c300021cf0001a1f0eefa673, 0x10eef6a731a2020140140177f00000d50, 0x10960000d50000a40c30e702509b01a6f, 0x1140140] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1873784730202013ff59a634a42323230, 0x12b9f37877302020d443f34393c356c3, 0x1c387378473020203a43f34393c356c3, 0x154b3b384030303038d443f34393c356, 0x10030030563f63102f6335c387c314ef, 0x10102f633c630f7fc373c3139f54a6b3,
      0x1008463756394c373c3f354d3b3003003, 0x1c4753c750e8f73eb730e8f07a6a4000] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1129f03b3f0980384ce5da87a420d5f20, 0x1000e4f382a12a366fa61a610af660866, 0x44721ce809e0, 0x485214a80960, 0x1257f4b996a73221f548fd556564f00e, 0x1132fa6d5d5662bef176f197f014c714,
      0x1560000014230f14398f177f132f6a6d, 0x1eb001ac76a414fe599e56a0f5f11dfd3, 0x114fa146a46966ae59907d5a4660] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10000f7f0006c5439b3141f0339030230, 0x10750756c3703707a407074623920230, 0x14393c367c3dc378473020204c59e534, 0x14393c367c3dc3784730202054d443f3, 0x1c3dcc3775454b3840303030b6d443f3, 0x137c3f354d3b30030030687763f36335,
      0x1a48463756394c3] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x19e00c700e3001919ef2d5219219200, 0x119ff113f19ef14cf324f16ef77ff14cf, 0x1d32e32e623920001dbf021af021af, 0x10eefda73a419c74d0f01c7f0780f4d1f, 0x1117f1d6f6688664cff0000019ef4c, 0x133088271d6f465f1d6f465f117f1d6f,
      0x1ae01441447846565f4611156c83333, 0x4a5210a80960, 0x425210a80960, 0x4a5210a80960, 0x4a5210a80960, 0x4a5210a80960,
      0x11d4f1a8f132f139fd5132f661176f, 0x411204280860, 0x1c456033033014375f1420ef177f375f, 0x1660eb0076441a44b946107f469b11df, 0x114c414c446960f0feb9907d5a4] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1e3e378763cff7606756560333333020, 0x1730360360d40d4000c6f00e30e302007, 0x18778763cff762f6f675656ca3333330, 0x1d42f6fdc0c6f87ca000037dd072fef, 0x1f34393c384c3560f3618ff364dd4566f, 0x10e3fb79749972b8fdc3a870e30e3043,
      0x1460ebf77] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1f614ff989898345f00fc46781f575700, 0x1110f11e19ff05aa6a6000f8f000f6f6, 0x840020108040201010004400102002080080da2, 0x1bc0bcfc46782f567f5700070ecf0ecf, 0x10000786f41ef785f567f784f3b3f783f, 0x12e9f0282f098002e000881ee600a6000,
      0x1150f2eaf2a2f2eaf360f250f25ef129f, 0x15aa6a6ca787f0f8f9e0eb282f3aaf, 0x11ca0000086a076a6a110f11e19ff13ff, 0x4e7208e809e0, 0x421204280860, 0x10f0f2e1d4f788f112f881ee613ffbca6,
      0x1bc2a412f0789f098015afd6616610af, 0x446220e809e0, 0x484220280860, 0x14616c78af5a15a14ff1f3f, 0x4e7208e809e0, 0x4a5210a80960] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10736e3d676d47606705603335af33020, 0x10364d36b7d45bd400000e335afe3020, 0x1dcd676d4761f3f67466f56033033073, 0x1d45bd41f3fdc466f870000037ca0736, 0x10e30e3043f34393c384c3ca364d36b7, 0x1460ebf770e3fb797499721ffdc37cf87] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x198000001000bc0fffbcfc98115700, 0x501a02318860, 0x501a02308860, 0x501a02318860, 0x1112ff14ff1d2fbc105f125af1105f, 0x501204208860,
      0x501204210860, 0x1040000008100000040400000041000000400800180c040001000200000100200010000020180c0c0604000080000100008001000004008000040040000100040000100048a5726, 0x1178cf78bf32ff114cf57000113f00cef, 0x501a02308860, 0x501a02310860, 0x110df0e8f1105f98010154f05c05c046,
      0x880022000240021000201008100202400080fa2, 0x501a02308860, 0x101113f167f0cef7c12ff110dfca10df, 0x501204220860, 0x501204240860, 0x178ef78df1bff0885c881277f12afc,
      0x501204280860, 0x3db3000408c001f53009066600799e6003db301e612097980f3079808118007b66001ed98001e612d44, 0x1526f1f9f11f9f78ff2f4f1266f202f, 0x4a5210a80960, 0x4a5210a80960, 0x1c412e190f142f1142f,
      0x4a5210a80960, 0x3db3000408c001f5304d5e6607981e6003db30f309ab9f30f30798008118007b66001ed98001e612d44] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x1283f301f0ae276f389f2a0c3f9900000, 0x10d0c3f9900000f8f024bf0fff214f, 0x100024bf1568f1acf791f0790f0d389f, 0x411204280860, 0x1ac0ac2e4f12ff000276f0d2a0990105f, 0x1117f20ef117f1254f1129f174f00000,
      0x421204280860, 0x4232086809e0, 0x1129f792f0000079a60e8f1139f422f, 0x425210a80960, 0x1139f1daf117f794f117f793f254f1acf, 0x119df0f0f569f112ef795f0009800e8f1,
      0x4a5210a80960, 0x445204280860, 0x1000980180feb0f0f197f0f0f1bef0f0f, 0x1139f0f0f139f0f0f250f1129f56af, 0x445204280860, 0x10e6f796f000980110feb0f0f1acf0f0f,
      0x137bf0c4f37bf123f123f123f21ff389f, 0x1123f250f1129f56af00098095eb0c4f, 0x485204280860, 0x195eb0c4f1acf0c4f139f123f139f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10d2f] (by decide) (by decide +kernel)
  · exact SearchNode.check _ 3 [0x10ecfe339e3000005500000073e322200, 0x120ecf2000001c550551c1f0e517ef, 0x1e30e30e70250450c30eef3373200f, 0x1730107f00025001a5ff4e5ca46e31f0f, 0x107435f219f5bd90000011cf0eefe5, 0x1001a4f00d41a10bf1c6f2fcf0f0f1c5f,
      0x12e9511bf112f88180f07117f79a6413f, 0x10dafeb0fcfeb3e219fccd9019019095, 0x179a6117f1a4f01a4f009d9a0f5f9a, 0x1ba00000957c95e6112f88180f07117f, 0x1123f1b3f123f1115f326fcef9ba3a7f, 0x424210280860,
      0x1ce1acf0d2a20ef0edf0268f0018af, 0x1d3c7e9139fe9bb1d4f7c203f] (by decide) (by decide +kernel)
  · refine guidedTree_sound (holesLeft := 4) (a := [0x10012d528394137f940c5aa0385858500, 0x701a02310860, 0x1d30d3a302b300394030c50c70137f190, 0x104630d30d3a302b39603960300630630, 0x1063c7630d30d3a302b3003940300463, 0x164476438d30d32d03434223232300cff,
      0x164476465d30d35305334f5230523047, 0x164197f640d30d3e800334c723b623047, 0x1b847136500053035303540405270265f, 0x12e328394194023aa548505850149f47, 0x701a02310860, 0x1d3a302b3003940300c797fc7111000e3,
      0x701a02310860, 0x704202310860, 0x4000212220000000100000000800000000000010020000000000000008800000000000200020000000000000800800000000000010020000000000000008800000004000272a1000000010000000040000000000004000080000010000000010000000000001001000000000000002004000000000004000080000010000000001000000000000202000119500000008000000400000000012000000000000002080004244000000200000008000000000800000010000000012000000000000000200000200000020000000100000000800000004000000001000000080000000200000004000000020000000020000000080000004000000001000000100000000020000000080000013487ffd6bfc7d72e, 0x106500053335334023052300630630d30, 0x10063c7630d30d3a302b300394030000, 0x1232300b8013650005303530354270535,
      0x1c723b62305306406438d30d300034223, 0x1aa0d0f531a64b8640d30d3e800334, 0x1194f00000550001172a73d6222000cdf, 0x500a04210860, 0x12000001c5505529df1e56b1194f39, 0x501204210860,
      0x501204210860, 0x1e30860e70c3033083179373120ecf, 0x500a04210860, 0x16a94086011f40861aff83e5831e32a7f, 0x501204210860, 0x501204210860,
      0x501204240860, 0x1069746c846864eb7870e30e308394, 0x12bdf5a0ccf313f0000019af060f3f, 0x1870e30e30799f12fbf798f7a17a14ff, 0x1c46204e809e0, 0x484204280860,
      0x1c7268f116b069b069746c846864eb7, 0x501204280860, 0x504204280860, 0x1c4c607656033033085858500cdf1aff, 0x1870e30e30c5aa29af4419af44f7c4b9, 0x1030030c50eff06ec069746b746864ec8,
      0x103021cf63196f6393d394d3a3d684b30, 0x100300463046396d396d3a30b84b30030, 0x100cffb763c76393d394d3a3d684b3003, 0x164476438d393d32d144f34340232323, 0x1476465d30d7fd3539653340230523047, 0x164c7d3b6d3e8e7173402302304764,
      0x12753479f53565400500265f64197f, 0x115000a7f600240047b8471365040d7f, 0x1a8281301313080e4980d3f5f5f501515, 0x1026000000000bd0d7240b5a4b5b5a50, 0x105e265e04a50a801301354080e415026, 0x12c8f131f27af27cf2ecf10169f0169f,
      0x421204280860, 0x1000f50f835bf0d6f3adf0d6f117ff, 0x421204280860, 0x10d6fb479af189c0ccf9c89a90ccf104f, 0x1c4c4c4b497b4a7991f9f153f240f8b4, 0x1139713130826bfe4980d3c4c4c40dff,
      0x1b4101f9f02401b9fa41b9f93a597a828, 0xc4120c6809e0, 0x11354080e40026c426c418c499c4b497, 0x1b467bd0d70016261604a5d8a8d81397, 0x10130afbab58180c4f1b8f0c4fb47e, 0x11a8f1817bf13db47eb4b400c4fd70c4f,
      0x84210080860, 0x1053b553340230523085013100fe631df, 0x16527005305305403050308500006500, 0x1435bc325c3834b847302020aa0b8013, 0x19746b746864ec8870e30e300caf43e7, 0x1d394d3a3d684b300300300c3e069b06,
      0x18876117f0191f0f50216f6325df6393, 0x1d684b30030030b443b44366c366c389, 0x1340232323065b763c76393d394d3a3, 0x1199f64199f6438d393d31b7f401f1b7f, 0x164b864c7d3b6d3e8e71734023023053, 0x10e400c5c5f8139f0c5ff50c515ff531a,
      0x1c55826a804a59c100f9c13b4135408, 0x12b21ef04ab04045e206fb5b5012df, 0x1eab4ea13118fb40d7ff40d7f25161e5f, 0x19813650f605304533b5410524001f8f, 0x1e6b640f31e61116b6416c80f31e607987980f30004bf62bb15c0003cc3cc0f31e60799e600f31e619824, 0x11300000f826f81081e42400c5fb614bf,
      0x4a82904529e1, 0x4a82904529e1, 0x15304533b5400500c513c50d0ff813b4, 0x1045ea9b511df0b614bf281365c499c4, 0x11000000d7ff40d7f2516ab2b1604ab04, 0x441204280860,
      0x1ea53118f13b41358a5c4127fc4f826f8, 0x1ea0eaf]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x1335501c9f3700073c322202323230850, 0x1d911cf010003caf152f034011af2a9f, 0x20008800204020100900104004004800100825a3, 0x10100840e8402b3fe736bfd91016ff, 0x20008800220100800900104004004800104021a3, 0x20008800204020100900104004100800100825a3,
      0x10000214f02c9ff31f34bc620bfc61a1f, 0x8442204109e0, 0x1e30e8467f318f1c7f4510027df11cf01, 0x20008800204020101100104004008800200825a3, 0x20008800220100801100104004008800204021a3, 0x1346fa9227f227f1f3f0156f870e316cf,
      0x11001002733af0338e8378f0edf352f45, 0x8c6220c609e0, 0x10080402004400110100804002004020100895a2, 0x11a4f16af112e1f536f4f2f467f03a0f, 0x8c22204209e0, 0x8442204409e0,
      0x14a0f33ff8b0003a045454500308516af, 0x1000056c3e6045003442f185f26cf04b, 0x10b3b3f40303030227ff3227ff3001c9f, 0x10019df152f017df4817df7635a3a3a30, 0x1b3d3030030078078135f7807811cf010, 0x20010800404020100900104004004800100825a3,
      0x111cf0100002e5f004875760a30a3000, 0x20010800404020101100104004008800200825a3, 0x1a300b3b30030303009b01bbf100170f, 0x20010800420100801100104004008800204021a3, 0x111f3f0156f00079bf000480035a3a3, 0x10080420010400410100084002080020400895a2,
      0x100b3d3038303000edf00447f1c3f227f, 0x16700056033333300487504ba31e6fa30, 0x109979cf11e8f06800f9f00780e1f2cff, 0x10080402100404010010800402080022000895a2, 0x100187f068ac0dac438f1111cf10016ff, 0x10080402100404010010800402080022000895a2,
      0x10080404100404010020800802080022000895a2, 0x10080402100404010100800402080022000895a2, 0x12323230aaac0ac00011cf00003d3f99, 0x11d3f16ffd911cf156f1152f1000034a4, 0x20020800802010080804100104100104000423a3, 0x8842104809e0,
      0x1c61a1f84184000e001d6fe7152fd91, 0x8822104809e0, 0x8c6204c809e0, 0x132bf182f00002e0ff315cff34bc620bf, 0x1318f152f3a112fdf27df11cf182f1, 0x8842184809e0,
      0x8822084809e0, 0x8822084809e0, 0x10f2f156f87147fe316cfe30e81d6f, 0x10edf16ff16ff346fa9227f227f1f3f, 0x1173a73022200127152fb338e879df, 0x4006800010010000020008000020020008000200020000200080002000200002000860043000080008008000400000800040080000020200000080800000102000000101208fbf26,
      0x1019000caf000939393558383832d1f, 0x101707302e32000005b55055417f2d1f, 0x10f40000000e30e30e393f393c3833383, 0x193935583838379ef173a730722200000, 0x15b5537cf55111107e30cafe30d993, 0x827204e809e0,
      0x82721ce809e0, 0x827204e809e0, 0x82721ce809e0, 0x183e683315f1737cf73020201291566f, 0x825218c809e0, 0x82721ce809e0,
      0x11b0f13ff87070372f004e93f393c3, 0x121ff2f6f2b8f56bff42f6f79ff13ff, 0x1d90000075557518ff831e6f83467f, 0x17b378f19af378f119f3c0f209f465f, 0x135a3a3a300b3b33303030300d87b0caf, 0x14b008b449f026cf3a0e454545004800,
      0x100a30a3d302b3e60320300185f00fcf, 0x17811cf156f1152f1019df00b3a404875, 0x20040801002010080804100104100104000423a3, 0x8c6218c809e0, 0x17617600000442f787a0f78135f78338f, 0x8e7204e809e0,
      0x1182f0000454f365b3644ff8636ef8649, 0x1254f1bbf112fdf170f11cf182f1558f, 0x8c6218c809e0, 0x8422084809e0, 0x8422084809e0, 0x1a3a3a3345f86b3b3c60303030254f9b,
      0x1147f0d9f0147f023ef4823ef15df35, 0x1447f1c3f227f11f3f0f2f156f223f, 0x8422184809e0, 0x1d38683b30030030323f0edf323f22af, 0x14b333333056cf487510cf4ba31e6fa3, 0x156dfba780e1f2cff677a1feb131f56,
      0x11254f17a2f1141f1d6f1006856df0f9f, 0x4416f7f4d6ad0fc5bdfd35ab3fdb4109fd8567f60159fd80ad017554fd80acfec0159fd802b3fb0058a017bfa6b015a540a2fec000ae58bd8000001853d30000000ae58bd8000000b266b6159fd8002b3fb567f6000acfec2b3fb00159fd8567f6002b3fb2b3fb002b3fb02b3fb000ad0173fb0220b7c053aec00000ad29ffb00000ad098fec0882df014ebb0015a085abbec00567f602df9185dd2212b, 0x861218c809e0, 0x861218c809e0, 0x8422104809e0, 0x1141f07a4f00680f1f117f0f1f7a3f111,
      0x8c6218c809e0, 0x8422104809e0, 0x8422104809e0, 0x153cf3bff2fbf374f254f7a5f12c9f, 0x8c6218c809e0, 0x10173c3222023232300c0f1f10f1f22af,
      0x8c42184809e0, 0x20080802002010080404100104100104000423a3, 0x1033013413ff11af13ff67550037182f, 0x20080802004020100900104004100804000825a3, 0x149b93686c4c6d4c639efbe1d3f56033, 0x10303000c0fef270fefa338e80d3fe84c,
      0x1030454548555535a3a3a34584b3b3003, 0x100c7f0033487555d3a32a30840b30032, 0x10303030182ff31f3dd008b182f0156c3, 0x20100804002010080404100104100104000423a3, 0x20100804002010080440101004100104000423a3, 0x1003013a48555535a3a3a33a84b3b3f4,
      0x20100804004020100900104004100804000825a3, 0x149487555d3a3d4a3222f84184fb3003, 0x1030302c0d2f2c4c6816878a30d3fa34c, 0x8442204809e0, 0x17a6f78c6c6c6005656c4333333003, 0x10ebf3a870e30e30b3b31f2fb91f2f,
      0x11a5f0449f00492977fd468697863a1f, 0x156bf161f45ef345f56ff226f56ef2b0f, 0x1483c2ebf35a3a3a31b3f56ff1b3f2b8f, 0x13c]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x1f927ef125f1ae0058a00c8f149f0c8f0, 0x4804020002400090002020080804020100805a2, 0x1053feb60197f00110df010ef2d0ff96d, 0x4804020002400090002000080800020100805a2, 0x1472f134f12ef134f11fdf7a7f1bff, 0x880402000840021000804020100802020080da2,
      0x137c3670840000f505301001161f01fcf, 0x880402000840021000804020100802020080da2, 0x880402000840021000804020108002200080da2, 0x108c308c3660660000f501e431e438bc3, 0x10e0f430c30c300840000f501e431e43, 0x1146328c367c313013a79402424065043,
      0x11463a5c35ec313081313a80e42401463, 0x179631a8fc354c30e0f0d300002401463, 0x11406a505e5413127f13a4a80e4007963, 0x100042504738d2b5200300cdf13af1426, 0x18308304f404ca4633b5330030000160, 0x1c486b976560330330044804b30e70016,
      0x176560330330a318af440f5f44d4c4c6, 0x173762220d3119f441a44d4c4c6c486b9, 0x13b4f0570ac43ac4355c486c41b1f2525, 0x107a067a060cef46bd46ab172fab3a8f0, 0x100205f43e74384c483c41a25c3730202, 0x17a0c4f0cef535fbddcab15afab99000,
      0x1103fc6d5b3003030302300cdf7a330f, 0x10d50020caf2023135fa43923594a894, 0x1b3f40303030340c70935ba3a8a3131f, 0x10caf0083e5a4e5733594a894103fc6d5, 0x1c7151f935ba3a8a3131f86d573f40, 0x112bfe42408a0a864a864a3b6e8b63c1f,
      0x1f5029ffb5a4b5b5a594a894130813130, 0x1240bd026093a508a854130130027afe4, 0x104a40404a594a89413081313f412bfe4, 0x1260493a508a85413bd131df40e40089, 0x10b300339030230a864a864f8b6f8b604, 0x1000239202351afa4189f28394a3940c6,
      0x11c6e5b30030030340c7093c6a355a300, 0x1082218c809e0, 0x1a3186e57300000836da46d868394a394, 0x18c2218c809e0, 0x164b864a3b6e8b67a8fc752ff93c6a355, 0x100013013b3d30303030858585015ff55,
      0x1ea2c0cffb6a3b6c5d6c5aa960964835, 0x1081313d30e418bf0281f0c5f8e0ea2c, 0x1118fb67db6c5f8c5c59609648a500013, 0x1964853e7533402305230850ea2cea2c, 0x196e85305300030503085e427e4036548, 0x14853e75334a42305230aa0b802565e8,
      0x1531a53b3a400500c713271313654896, 0x1962c962cb8b60cb613b8132565e896e8, 0x1b624242465f5f5f553053fe0ee058a00, 0x1f81cfff819df000281f00e48a00c5f, 0x113013331fd30e400100f11e5f0c6f, 0x214220140860,
      0x1109f53fea4ee058a09626960a500108f, 0x108a0c5b6ee13a7652eef2edf0c6f53, 0x1f82aaff81a7f137aaf13281f07a9f, 0x143118f100f7d0d0fc5100f1330f7abf, 0x424210280860, 0x1ea0eafea]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x100000c3f4617bf01bff0231b2f230850, 0x10000165fb3103165f030340000000ccf, 0x1e709c83cc0000f3079f981e61e603cc7980f3213a09c83cfcc000007a54a0079f9801e7e6001ee9de64, 0x1c6000008442cf8400184f2a9f2054, 0x100165f730a400007f378f30ccfc6155f, 0x1570f000b37a037a030e807555750000,
      0x100000a41550e8f40edf2a9f20d5415ef, 0x8c6220c609e0, 0x1237df20276803f47555750d37397f4b, 0x1c311aff333ad37299f1eef0007337df, 0x10000150f4617bf01d5f0031b2f03085, 0x1a3000b3f4030303015ef015ef0000ccf,
      0x10133165f33017df4817df7635a3a3, 0xf409c87983cc0f30007980f31e607987980f32139f30079c2720000f31e6004012800f4e6001ef901a4, 0x1b3d303003000147f7703503500165f, 0x10165f560a400004875760a30a300156f, 0x10035a3a3a3000b300303030000000000, 0x10edf000d3515ef350003a7a07a00048,
      0x17500ccfa30d1fa3000b3d30383030f4, 0x100d6716af0e1f00000a433bf450f448, 0x1ad67000000045000683568f40f9f107f, 0x1001b2fb30031b2f030230aac3f378f3, 0x10707462571f20230252f15cf00540e3, 0x1468f8400000165f340755575000007a4,
      0x10000007f378f30ccfc6155fc64e84, 0x1339f1199f496f11cf0e5f11cf464f, 0x8822084809e0, 0x1570f7ae67ab30030030e8eb11454f, 0x8842184809e0, 0x8842184809e0,
      0x115500000e8f40edf15cf210f0d5415ef, 0x8842084809e0, 0x113a00000f47555750d37397f4b3bbfa4, 0x8842104809e0, 0x12768ca365b360d1fdc1d3f1bdf7acfe6, 0x17bad377aef1eef361f4e7adf7302020,
      0x1838383357f172fef73022200c311aff3, 0x15502e8f017ef00525f00093939355, 0x18333830170730235af2000001550d1f, 0x1e601e61e601e6f301022c52607981e69a03b31e61e58e184d0346003db2c347be80b1e61e601ee24544, 0x118ff7b0f40000000e30e30e393f393c3, 0x19355838383357f172fef7307222007b,
      0x15513ff3c6f572f17ef0e30e30d99393, 0x117466f7302020159f290cbf11550d1f, 0x8242084809e0, 0x825210c809e0, 0x1572f87000004e93f393c383e68321bf, 0x17b18ff7b421ff40ccf3cdf13ff1b0f,
      0x103030300f47555750ccf830d1f83159f, 0x100331b2f3300480035a3a3a3000b333, 0x12b3200f0316cf0300000035035001b2f, 0x1007a40707463303300487500a30a3d30, 0x18649767aff7600000165fb30000000, 0x111cf464f00000ca365b36155f8634bf,
      0x1030eb11553f339f1199f364f11cf0e5f, 0x8422084809e0, 0x8c6218c809e0, 0x8c42184809e0, 0x17b0f10cf35a3a3a32fdf865bb3c60303, 0x13515ef357ae67a3a0670436f02d4f48,
      0x1d38683b30030030f40edf3c9f216f0d, 0x1a413a00000f4487515df0ccfa30d1fa3, 0x8842084809e0, 0x13568f40f9f107fba0d6716af0e1f3bbf, 0x16737df325f23bf9c23bf7b1f0000068, 0x1181f0b30031b2f0302300cc3f378f3ad,
      0x120237b2f252f33ff33ff6c541b2fe30, 0x100300303407555750a400000002571f, 0x1184f2b3f2b3f154165f14c3c6f165fb3, 0x8042084809e0, 0x8042084809e0, 0x1c4c6d4c61dbfbe184f5603303301d3f,
      0x1a44c0e5f4cba165f730000049b93686, 0x1000ca42768a35ae87ae8258f7555754c, 0x15535a3a3a31eaf8415cfb30030303, 0x11b2f350181f0d9001b2f001eaf48220f, 0x10b300316cf0300e5f181f43ffdd6c35, 0x100000333c5f33033487555d3a32a3084,
      0x18415cfb3f403030300e5f77dd770a400, 0x103303301eaf48220f5535a3a3a31eaf, 0x12caf43ffdd135165f354c3c6f165fd9, 0x8442084809e0, 0x1d3a3d4a31edf84156fb300300300e5f, 0x1a44c0e5f4c4e165f560000049487555,
      0x12ca46835685aa37aa30e5f77dd774c, 0x10d1f8302e8f0730216cf200302c0d2f, 0x10000003316cf330031b3f25f33c3f183, 0x8c6220c609e0, 0x1156f7302020b31b3ff378f30f40d1f, 0x1e301b3f25f33c3f1830d1f8313ff4b9f,
      0x8c42084809e0, 0x12977fd468697862fdf0ebf37cf870e30, 0x1f40d1f3cdf13ff9c156f560000049, 0x148757b0ccfa30d1fa31b3ff378f3421f, 0x1d3]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x10035000138313b3d3030303085858500, 0x1a3d32d30830b3330394030c5e8c5aa00, 0x163a3d32d30830b39603960300e635563, 0x1c763a3d32d30830b3330394030166316, 0x1d333d30cafa33434023232300cff4563, 0x1d315d353a35334023052304764476438,
      0x1d303d30a3034c723b62304764476465, 0x10300353053001605270107f643564e8, 0x1c311afb5f608505850149f47b8473565, 0x1230aa00e0f03d1644bf029bf041043b, 0x500a04210860, 0x12705130e800006500053a35334a42305,
      0x13303940300b80356503003538353b3a4, 0x1330394030230e635563a3d32d30830b3, 0x1023232300c4563c763a3d32d30830b3, 0x123065573f641c6438d333d35ba3a334, 0x100651a64b864e8d303d30a3034c723b6, 0x124005000028000133713a7150eff2424,
      0x1b616016054000d34912eff9930effb5, 0x11ca0dc242f496a49153bf2a8f98053a7, 0x501204210860, 0x501204210860, 0x1098b9915df99cb01b0000f60530101, 0x501204240860,
      0x501204240860, 0x10080080e8f660660000002a1f0919ff, 0x103d16f4000400409313bfb515018018, 0x1a505e2813081313a80e4570286500e0f, 0x105e54131813a4a80e40014bf140143d, 0x10030c5e8c5aa27858585014261416a5,
      0x103017ef635563a3d373d3568394b3003, 0x1003016631663a3d373d3968396b30030, 0x100cff3a63c763a3d373d3568394b3003, 0x164476438d356d30cafa3343494232323, 0x1476465d3b4d353a3533496230523047, 0x13564e8d3b3d3c7a3b63402302304764,
      0x13565b3b4b3531653279600500107f64, 0x10053a35334b523052308500cdf47b847, 0x183083532753f4c30305030850000650, 0x1868394b3003003053e853aa0b803565, 0x194b30030030a3119f635563a3d3c6d3, 0x19423232300c6b63c763a3d3c6d38683,
      0x1023065573f641c6438d386d35ba3a334, 0x1651a64b864e8d383d3c7a3b634023, 0x1333355842b846bc67373022200300cdf, 0x178f7932b93ec0dd0033ec33003119ff4, 0x15655842b846bc67373072220b30e70, 0x12b93ec86dd56070ec0083131ff4152f,
      0x1f7635563a3d394d31cefe71abf78f793, 0x100d3f5f5f50151515893789a70002400, 0x1d7240b5a4b5b5a51a8281308131300e4, 0x84220020860, 0x126003abf213f4d3f01e7f0199f02eaf, 0x116a508a8541301300574fe41502625ef,
      0x1332f893789a7f42f0f188f2400260, 0x1e4150d32f0f148f1d148f2a3f1cff, 0x124004a40404a51a82813081313f47b3f, 0x84208080860, 0x120bf0ccf45dfb4155fb41c9f020bf0, 0x11326ff133bf40e400261c9f26670ccf,
      0x10a51a51f899f8c404260416a508a854, 0x84220080860, 0x84220080860, 0x186f4e733838493840c60730216cf2003, 0x1f7e74b78c6937893000003316cf33003, 0x186f4e786838493841c6156f7302020b3,
      0x8822084809e0, 0x1f7e74b78c6937893186156f560000083, 0x8422084809e0, 0x112424000cff15ffc663c763a3d394d3, 0x211202180860, 0x12400c5f0f5f5f528151515133713a7d3,
      0x100dff423f127ff893789a7d311a0f, 0x211202180860, 0x211202180860, 0x101a3f13081313d31e4160f000139f, 0x4000002004000002040000020040000024000600010001000020001000020010000850002000040002008000020000400020080007000200018000800010002000040002001fbf27, 0x1187d12dfc5f8c5c59609621efa50dff,
      0x1f6530530010524001f8fea18ea28118f, 0x210a20108860, 0x1000001e42400c5fb614bf0286516f6, 0x210a20108860, 0x11d0fd30e400a518a50dfff826f82eff, 0x1a7a40050096269616a5180108f13113,
      0x200108004804020200a0102004100414010083a3, 0x100000c5b614bf1328651613a5f53153, 0x421204280860, 0x421204280860, 0x17d0d0fc5a518a50dfff826f8113113a7, 0x421204280860,
      0x8222084809e0, 0x1ea0eafea65118fa5]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x1a66a000034b623232300c8f0c8f0c8f0, 0x141af84000cbf002ae72ad9100016ae5, 0x40801000000401010000200008100024000845a2, 0x40801000040401010000200008100024000845a2, 0x11aff1fdf01aff000f30f377000374f84, 0x1109f406f109f167f0001aff1fdfe5,
      0x1367b0000e7fd40d40e30e7fe30242f, 0x10508f00e6fe6155fe30ecfe300360caf, 0x10000d45bd40e30e30250f36276f36000, 0x1e5ac15ef3325bf33059387b360360, 0x1330ace7ac0d3f1daf07907b4f0edf, 0x103ffff30d1ff37700008408477330cbf,
      0x1ac1ac0edf10790117dfe5ac15efe31e3, 0x218050408421, 0x2010080500044001080102004008010201029a3, 0x2010080500104004080102004020010804021a3, 0x218010400421, 0x1e50e57335000148d5b300303030013af,
      0x40801000001400050100204008100021000845a2, 0x17b5f027ff575f12bef293f003b1f00, 0x40801000040401010100204008008020200845a2, 0x100480b300339030255f0255f255f562f, 0x107a0dbf10e53bc30000870a6108fd302, 0x4000400004000000020004000020000000f0002000040002000e0002000040002000f00078000400080006000100004000400080000020200000020800000102000000102008faf26,
      0x17976148d5b3f40303030a60e0fa6fc0, 0x1001210880960, 0x12576148e5b30030030dae5c3e5733576, 0x1001210880960, 0x1298787cee3e3e30187c3a6108fd376, 0xf300798f30798f3007987d4c003cc1e607d4c1e60079f9803cde60079f983cc1e60f3079800799327a5,
      0x1f6026cfca16ff3a5bc8124fc82b9f, 0x1110f11e3d338f88a6453fca7b6f0f8f, 0x1084208880960, 0x197c87b7f29184f870e30e306a076a6a, 0x1030300d5b8d573117efca9b171f49c8, 0x40801000040401010100204008100024000845a2,
      0x12030770a3a3a3358383837748b3b3003, 0x100cbf00f3a375a3d3832830480b3003, 0x1030300cbff30f377000325f02c9f56c3, 0x1077a3a3a3358383837748b3b3f403, 0x10e5f116af1c7f16af7b8f041bf01e8f, 0x1025208c809e0,
      0x1b30030030374f2c3f4daf10e5f7b9f, 0x1021210880960, 0x1833b0ff3a375a3d3832583325f48184f, 0x1159f459f469f1e6f184f560330330, 0x10000068f38377256f3667159f333f, 0x1117df205f17df507f137bf15cf17ef,
      0x1025210880960, 0x1025210880960, 0x10e7f156f56000006854ff0f5f3cff, 0x120077f37bf3323f773ecf1d9f49af, 0x1c7290f0fcf9c20210cf0d500223cf, 0x113ef0fcfd3202000002392010cf13ef,
      0x107a16df13ef0e5fcc3013ef00fdc7, 0x1c8d573f4023cf00226ffd48bffd10cf, 0x10000da13efc7290f0fcf9c73797310cf, 0x113ef0fcfd30d8f250d8f13efc8e5730, 0x10d8f18afd910df037bf0010cffdc7, 0x1290f107f3d2f1bcf163fd815efd8226f,
      0x15a1ee6226f2a4fa60c3fca0226f00, 0x137cfd900000290f10cf3d2f10cf13ef, 0x1107f101f1bcfcbd80cafd83d2f0d8f, 0x1730239200300c13efba290fbafd13ef, 0x103189f0ecf189f189f1c25105f4501e5, 0x1004220810960,
      0x10723920b30e7000f40000e500330330, 0x1e30e306d6a6d6d1c252a2a2f1f6ae573, 0x11007b4e77dc46b797b7483f0ebf6d870, 0x1008020200400820100108004410004c00121923, 0x1541947a941e7111f41119ce556070, 0x1004210880960,
      0x1004208880960, 0x1004200880960, 0x1004210880960, 0x1004210880960, 0x1004200880960, 0x1004210880960,
      0x1004220880960, 0x195121f14121f291f0c203fa41c5f]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x100d7001313d315afe418bf0fb0c5f8e0, 0x1193f0131e9ffb0b11df18000b476b476, 0x1171f0d4f0124f05897589707baf8d, 0x1058058a90cef1e9f8d193f00576f390f, 0x13c9f0ddf193f0cd100fcdbc0d4f0124f, 0x148a51e9f15afbd292f0000097172f970,
      0x11807a0b476b47615af1acfd722df096, 0x11d0197fb5f500c5c596127ffb0b11df, 0x1139fd7f50e4093939316d6d6d6041704, 0x10d70008930893c3d6172fd6017015af0, 0x1f50106ffb0b11df18000b40b437afc4, 0x1bc93939316d6d6d60417041d07197fb5,
      0x193c3d6e6d6b417b415af0139f0f5013, 0x11e6fab1e5f0268f07bbf0d613089308, 0x1100f256f100f29159f333f159f459fab, 0x1797bcf58127f5810000026a854a5d6, 0x421204280860, 0x10127fb5b50b6c55e100f5e183f79100f,
      0x1130f0d4f00cef4e5805858461e5f8d8d, 0x1ab1e5f01e9f02baf00404cd17bfcd, 0x104106f15df106f115f99cbd8cbab133f, 0x12cea2c118fb60d7ff40d7f2516842b84, 0x1ea]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x1010e53bc311af1f60850d5f8500c8f0, 0x218042408421, 0x2180444094a1, 0x1da34a4230d5f230aa10e0f0f8f9e105a, 0x218048408421, 0x218050408421,
      0x1941940268fe5176f030e4f108fa6a610, 0x4180844118e1, 0x1084220810960, 0x1277bdf001a7514cf751670ccf6700000, 0x1084220810960, 0x10d5f2305916dfb8176f0000010dab3a4,
      0x4180844118e1, 0x179176f030e4f108f1e1e00da34023, 0x110eef110f5b00da0027231f35059268f, 0x1084220840960, 0x12300c8fb80d0f0f8f2316dfb8176f78, 0x11e2f105a010e5fcc311af19e0230d5f,
      0x218042408421, 0x2180444094a1, 0x218048408421, 0x1ac843854545400034a423232301e11e, 0x218042408421, 0x10e4f38a63810da1aa420d5f20ac59,
      0x4180844118e1, 0x18405405410e534b623023066e56642af, 0x8010200500044001008100204008104001029a3, 0x1c766c7000010da73a4277bef00755968, 0x4180844118e1, 0x100059003854545400e5340232323066,
      0x137230079000e4f381e3800da1a000d5f, 0x1277bff1a075596801540d5400034b623, 0x80402020080402010100404010020020800885a2, 0x100d2f0c70c7111df386f205f00da00, 0x80402020080402010100404010080022000885a2, 0x112ff111cf120ef02a1991105f394f,
      0x1018210442521, 0x1018212442521, 0x80402002100404010010800410080022000885a2, 0x80402004100404010020800810080022000885a2, 0x1230d5f23085013afc70d2fac0dac7c0f, 0x139d5d50e4f108f0f8f3325af0da3439,
      0x1d5ca00ca0127daf4c3031f0f03085d5, 0x6280c2410ce1, 0x1751670ccf67b9946a9400000daaad5b8, 0x1084204880960, 0x126af25da347a230d5f2305911a750e6f, 0x4280844818e1,
      0x1da350000059d579d5d50e4f108f1e1e, 0x187174f0000d5b8d57810eef110f5b127, 0x1004210880960, 0x1004210880960, 0x1b80d0fa6a6e7a6d91171f6d17ef125e5, 0x1004210880960,
      0x1004210880960, 0x1a3a3a33583838314815cfb3003030300, 0x8004200100140005010040401010002200088da2, 0x103000000351b2f3501077001b2f000, 0x1024220810960, 0x10330f3a375a3d3832830480b300316cf,
      0x1b3f403030309bf30f30a4000000033, 0x177033033077a3a3a33583838314815cf, 0x1021210880960, 0x10300f5f677c1f10e5f35165f3511165f, 0x1025204a80960, 0x1021210880960,
      0x1021210880960, 0x1000f3a375a3d3832583148156fb30030, 0x1021210880960, 0x19bf3205ff31a4295f110f9f165f5600, 0x1024210880960, 0x1024208880960,
      0x1024210880960, 0x177dc10f9f184f560330330681830d83, 0x1024220880960, 0x1025210880960, 0x100034223232300f368776736201fe6dc, 0x10da1a3920d5f20159329f7738545454,
      0x8040201100044001008100a04080142001029a3, 0x12339230375f1542f00e4f3803825af, 0x228042408421, 0x12248f207559680054054b60033417bf, 0x134167fc7297fc700ca0513f27daf4c3, 0x1177f34af31dc188fdcd68418400000da,
      0x10a5204a80960, 0x10a4204880960, 0x4280844818e1, 0x159329f77385454541dce534672323230, 0x1084208880960, 0x1381e3826af25da1a7a11df0d5f7a01,
      0x1084208880960, 0x1dc37340230230375f79323f207f0e4f, 0x1127da1a00000755968771540d54b6, 0x1084208880960, 0x1084210880960, 0x11acf0d2f167fc71c7111df386f205f,
      0x1084210880960, 0x1084210880960, 0x13301da340230d5f2308500cc70d2f, 0x1004220810960, 0x1030850ecf390ecf0ecf0e4f108f0f8f, 0x10d5f230aa0b8000270000da00031f0f,
      0x106ae56a6a0e4f108fa6a61e5da34a423, 0x1000210880960, 0x100003637f3dcc36793671176a730202, 0x1081210880960, 0x16659577fb8315f11273f1f1149dab3a4, 0x1004210880960,
      0x1004208880960, 0x1004210880960, 0x1004210880960, 0x194a6340232323000cb80d0f0fef54159, 0x1004220880960, 0x101da1a000d5f001590f7f35385454541,
      0x80402010001400050100404010100022000885a2, 0x1080a20840960, 0x1084220810960, 0x1023392301d4f1177f1a0e4f3843cf38, 0x1084220840960, 0x1002248f2075596835b6540354094034,
      0x134a42323230109fc7177fc71270000da, 0xf31a940f33cc07981e6c571e607981e67980f31e61a947983cc1e601e6d4a007b66001e6f3001e9ded44, 0x1a420d5f201590f7f3538545454194a6, 0x1081210880960, 0x1081210880960, 0x12301d4fe5177f1a0e4f38a6381e5da1a,
      0x1084210880960, 0x1000075596835b6549354194e5340230, 0x1081210880960, 0x154109fc7177fc7127512f11b9da73a4, 0x1084210880960, 0x1084208880960,
      0x1084210880960, 0x1121f228f121fc70d2f110f0d2f15466, 0x1084220880960, 0x10d2f]) (b := []) (by decide) ?_
    decide +kernel
  · refine guidedTree_sound (holesLeft := 4) (a := [0x11600fff0040043bc3e6b5f601052400, 0x2008080300404010100804000402020080807a2, 0x1151513013a7f4578f24240930e0f989e, 0x11504004266fd310240533bf5f5f52815, 0x1e600f31e60f31e6016c80f31e607987980f30004bff30222c0003cc3cc7981e63cc1e607981e619824, 0x11513013a701d5f242405354f50f50150,
      0x157150000d3157240f6f6f5f5f5281515, 0xa10a205209e0, 0x10b43bc4579f15150576554f598f51615, 0x12400c5fb614bf985757573df6f6f6b4, 0x11806c0b40b422cfc415bfd71e8f01e4, 0x2010080500404010100804000402020080807a2,
      0x1fb010000a7f4578f15af2400bfb111df, 0x109825040a521, 0x1088208442121, 0x10281301313f47c3fe41501458f17c2f, 0x1088210442121, 0x1088210442121,
      0x10b40b42fffd300240a81127f35dfa5fb, 0x1088210412121, 0x1000130133bf4a4e4040261cff260000, 0x1251fb40b4a707c4f15af240a826154a5, 0x1088210412121, 0x128130131300e40040ff458f07c5ffb11,
      0x12010400496400090100894002410020400897a2, 0x8122204209e0, 0x10000d313aef240a81127f35dfa5fb0, 0x214220108860, 0xa10a205209e0, 0x101300a4e4160261cff2611811e9f251f,
      0x8122204209e0, 0x1814220c209e0, 0x100f826f8450fa826054a510388f13, 0x8122204209e0, 0x11607a0041f4f04160f1a2f1b5160f, 0x1018202442121,
      0x1007c6fd41d7160f0e42557af1a2f3d1f, 0x1018210442521, 0x11b00000131d0fd308fb08111f0000c3, 0x1004000b5001311132f01000ba1b26df, 0x80012000420400820020100804100404010083a3, 0x80012000480404020080102004100014010083a3,
      0x80012000480402020080102004100014010083a3, 0x1a90cef18d1a2f02557af21ef01600004, 0x1018208442121, 0x1000000cd100fcdbc0d4f0124f058058, 0x10962696108fa508fb08018000c3015af, 0x130cf1d1d280301f013013a715124240,
      0x1088210442121, 0x11d0000d30293f4cafe61b52400515, 0x1088210442121, 0x149766d760000053a7a45432af4c9f, 0x113a72a0f02424053111ba114c2f267f, 0x4222046809e0,
      0x421204280860, 0x421204280860, 0x424204280860, 0x421204280860, 0x101328f30cf1d1d28131bf26bf132d8f, 0x8222084809e0,
      0x1088208482121, 0x11d161172f26bfd312c7f40ef00024, 0xc212086809e0, 0x8222084809e0, 0x115af2400c5b614bf13fc655432af3a4f, 0x113d7172fe415015000fb000000a7151,
      0x2040041100404010001800040402020080807a2, 0x155af187f1d7240a8000a5fb02813013, 0x2040081100404010002800080402020080807a2, 0x1a41307c41e41502602600000d307c7f, 0x2040081100404010002800000402020080807a2, 0x176129f760000013a7a826054a500013,
      0x10015af24013112eba10fcf155f0fcf49, 0x421204280860, 0x424204280860, 0x421204280860, 0x130cf2edf5dfbba1c9fbab40fcfb4a7, 0x11795da5fbad2813e6131300e400253f,
      0x424204280860, 0x118ba0ccfbad30fcf3aef7c8f000240a8, 0x1159f9c13a41316180e4002626ff265d, 0x1134f336f9d19ddb0100a8267954a59c, 0x80402000201400070080102004100404010081a3, 0x1021210880960,
      0x12400c5f826f84d197f7c9f2d1134f8c, 0x1024210880960, 0x100515c4c4c428c4c4c4138413a70124, 0x240a20108860, 0x1c30b50054c40c4d3c40c40840001b524, 0x240a20108860,
      0x10930e0f3d1c4f1601c4f0e8f040043b, 0x13bc4c4c428c4c4c4138413a7f402424, 0x1c4bbc4d3c4d4c4048404266f00024053, 0x14608d000b614bf289965c499c45354, 0x17caf0d4f2baf300f193f5805822cf, 0x101000022cf4601e5f00b529576f1e4f,
      0x4020100802400090004800100900024000805a2, 0x158058584608d00a92d1e9f7cbf127f, 0x10404cd17bfcd130f0d4f127f0cef0d4f, 0x12d99239fd8239fab1c0fab3d5f00000, 0x1f40d7f2516100f2b1604106f127f106f, 0x1c4fbc4c4c4588458a70115af24000d7f,
      0x240a20108860, 0x1eba5fb127f2813d7131300e40015c4c4, 0x126c4d3c40c40840001d7240a8eb127f, 0x240a20108860, 0x126100f54a5a40013013001e415026c4, 0x2100084002404010100814000402020080807a2,
      0x1c4c4fbc4c4c4588458a7f4015af240a8, 0x1eba5fb127f2813b41313f40e41501c4, 0x441204280860, 0x1d3c4d4c4b484b42fff000240a8eb127f, 0x1a5a4ab04134e133bf40e40026c426c4, 0x1118ff826f899a5c4127fc4a826100f54,
      0x1ea0eafea0d0f]) (b := []) (by decide) ?_
    decide +kernel

private theorem vb11_2 : nb11_2.Valid :=
  SearchNode.cover16 nb11_2 (by decide) rfl
    checkedBranches1.vb11_2_0 checkedBranches1.vb11_2_1 checkedBranches1.vb11_2_2 checkedBranches1.vb11_2_3 checkedBranches1.vb11_2_4 checkedBranches1.vb11_2_5 checkedBranches1.vb11_2_6 checkedBranches1.vb11_2_7 checkedBranches1.vb11_2_8 checkedBranches1.vb11_2_9 checkedBranches1.vb11_2_10 checkedBranches1.vb11_2_11 checkedBranches1.vb11_2_12 checkedBranches1.vb11_2_13 checkedBranches1.vb11_2_14 checkedBranches1.vb11_2_15

private theorem tv_b11_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_2

private theorem vb11_6_14 : nb11_6_14.Valid :=
  SearchNode.cover16 nb11_6_14 (by decide) rfl
    checkedBranches1.vb11_6_14_0 checkedBranches1.vb11_6_14_1 checkedBranches1.vb11_6_14_2 checkedBranches1.vb11_6_14_3 checkedBranches1.vb11_6_14_4 checkedBranches1.vb11_6_14_5 checkedBranches1.vb11_6_14_6 checkedBranches1.vb11_6_14_7 checkedBranches1.vb11_6_14_8 checkedBranches1.vb11_6_14_9 checkedBranches1.vb11_6_14_10 checkedBranches1.vb11_6_14_11 checkedBranches1.vb11_6_14_12 checkedBranches1.vb11_6_14_13 checkedBranches1.vb11_6_14_14 checkedBranches1.vb11_6_14_15

private theorem vb11_6 : nb11_6.Valid :=
  SearchNode.cover16 nb11_6 (by decide) rfl
    checkedBranches1.vb11_6_0 checkedBranches1.vb11_6_1 checkedBranches1.vb11_6_2 checkedBranches1.vb11_6_3 checkedBranches1.vb11_6_4 checkedBranches1.vb11_6_5 checkedBranches1.vb11_6_6 checkedBranches1.vb11_6_7 checkedBranches1.vb11_6_8 checkedBranches1.vb11_6_9 checkedBranches1.vb11_6_10 checkedBranches1.vb11_6_11 checkedBranches1.vb11_6_12 checkedBranches1.vb11_6_13 vb11_6_14 checkedBranches1.vb11_6_15

private theorem tv_b11_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_6

private theorem vb11_10 : nb11_10.Valid :=
  SearchNode.cover16 nb11_10 (by decide) rfl
    checkedBranches1.vb11_10_0 checkedBranches1.vb11_10_1 checkedBranches1.vb11_10_2 checkedBranches1.vb11_10_3 checkedBranches1.vb11_10_4 checkedBranches1.vb11_10_5 checkedBranches1.vb11_10_6 checkedBranches1.vb11_10_7 checkedBranches1.vb11_10_8 checkedBranches1.vb11_10_9 checkedBranches1.vb11_10_10 checkedBranches1.vb11_10_11 checkedBranches1.vb11_10_12 checkedBranches1.vb11_10_13 checkedBranches1.vb11_10_14 checkedBranches1.vb11_10_15

private theorem tv_b11_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_10

private theorem vb11_14_6 : nb11_14_6.Valid :=
  SearchNode.cover16 nb11_14_6 (by decide) rfl
    checkedBranches1.vb11_14_6_0 checkedBranches1.vb11_14_6_1 checkedBranches1.vb11_14_6_2 checkedBranches1.vb11_14_6_3 checkedBranches1.vb11_14_6_4 checkedBranches1.vb11_14_6_5 checkedBranches1.vb11_14_6_6 checkedBranches1.vb11_14_6_7 checkedBranches1.vb11_14_6_8 checkedBranches1.vb11_14_6_9 checkedBranches1.vb11_14_6_10 checkedBranches1.vb11_14_6_11 checkedBranches1.vb11_14_6_12 checkedBranches1.vb11_14_6_13 checkedBranches1.vb11_14_6_14 checkedBranches1.vb11_14_6_15

private theorem tv_b11_14_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [1], 1, []⟩⟩ [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := vb11_14_6

private theorem tv_b11_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, true⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 128, ⟨2, [], 0, [1]⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [1], 1, []⟩⟩) (prev' := [⟨2, 128, ⟨2, [], 0, [1]⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed, moves12, moves16, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedBranches1.tv_b11_14_0
  · exact checkedBranches1.tv_b11_14_1
  · exact checkedBranches1.tv_b11_14_2
  · exact checkedBranches1.tv_b11_14_3
  · exact checkedBranches1.tv_b11_14_4
  · exact checkedBranches1.tv_b11_14_5
  · exact tv_b11_14_6
  · exact checkedBranches1.tv_b11_14_7
  · exact checkedBranches1.tv_b11_14_8
  · exact checkedBranches1.tv_b11_14_9
  · exact checkedBranches1.tv_b11_14_10
  · exact checkedBranches1.tv_b11_14_11
  · exact checkedBranches1.tv_b11_14_12
  · exact checkedBranches1.tv_b11_14_13
  · exact checkedBranches1.tv_b11_14_14
  · exact checkedBranches1.tv_b11_14_15

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

private theorem solve_new (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1, h0])
    (hM10 : M 1 0 = some (some 2, Stmt.write 1 Dir.left))
    (r : State) (hthird : M 2 0 = some (some r, Stmt.write 1 Dir.right)) : False := by
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
  fin_cases r
  · exact tv_b11_2 M hG (matches_set hm (m := ⟨0, 1, false⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_6 M hG (matches_set hm (m := ⟨1, 1, false⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_10 M hG (matches_set hm (m := ⟨2, 1, false⟩) hthird) rfl hv2 (by simp)
  · exact tv_b11_14 M hG (matches_set hm (m := ⟨3, 1, false⟩) hthird) rfl hv2 (by simp)

theorem h1_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H3 := by
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
  obtain ⟨q', hNew, hM10, r, hthird⟩ := second
  rcases hNew with rfl | rfl
  · exact solve_new M hG hm0 hv hM10 r hthird
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
    have hthird' : (reindex23 M) 2 0 = some (some (swap23 r), Stmt.write 1 Dir.right) := by
      simp [reindex23, swap23_2, hthird]
    exact solve_new (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01) hM10' (swap23 r) hthird'

end OMA.BB4H1

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1_H4_R1.H3 := OMA.BB4H1.h1_proof
