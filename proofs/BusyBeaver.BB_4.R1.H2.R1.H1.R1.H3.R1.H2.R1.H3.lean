import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1

/-!
Write-0 residual H3: `M 1 0 = (2, write 1, right)`.
FAR/TNF certificates from @ubuwaits `R2.H1.R1.H3` tv_b10;
checker from @hyprspacecoyote R2.H1.
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
private theorem tv_b10_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [581096261617888, 580684011931872, 123421324250209, 580615225280736, 580684011931872, 580684011931872, 
    265785434843201353880842708301710276394937755336067049919180384592638538843931464163435007490682543812, 265752994540108411252272281178803296057984686444151809610817283335136992975144300404803289455269011140, 53052645082145, 48526606668268778087869380359900156998879552930, 284230471125216, 1461596415838616540856546788350514238187750565282, 
    1461596415840937506425866057898073110155090208162, 565219047803233, 265751220461005753993844547146442135645670954098644518877582373326416576155445923574026077765462057413, 567521146082465, 81928921614816, 290833983343072, 
    22881261833530618465316119079441416536092845346, 22881523170388413746056058951139924134079243554, 73124238657760, 284230471125216, 22880750048850769373867070164031839156702815522, 75321114429664, 
    286427346897120, 75321114429664, 564085168047137, 564085168047137, 564085168047137, 265785434843201353880842708301710276394937755336067049919180384592638538843931464163435007490682543812, 
    284230471125216, 565184679676001, 564085168047137, 567521146082465, 567383702933665, 580615292389600, 
    368230089832415063153498585148616848099391317410, 268897676423098020835752910825479517298598297845802809793481871978889120089933591501452381999640632644, 16641875556787413440751329480805183564132736223320395355991504034144367568875571796534288907745910084, 580684011931872, 185544998536618808488237191674773799357183960482, 565430503016672, 
    81100758978617535373904881910503923977613046820686057813285086970069487008991665474811725936866565, 53052580105313, 88236951144545, 567627311483104, 265783407324725392828937461936328260973340400881991266715894493267112789134352060642120764567984299716, 580754778327264, 
    565361850648800, 565361850648800, 567490006616288, 580617339242720, 564123826194656, 25690556470698759939224621116054982451802940834, 
    94198707057442629510762287521329256596161176994, 565224411564256, 8563518824012792546311190295065240603055367586, 185542907839767788939450161842023782142647477666, 2108619710240942702853959832755081173570523381991913077911934924213132137528130443309399132578275012, 158471681083616, 
    580684414585056, 265785434843201353880842708301710276394937755334612376417499092218122906834289106570390859848763858628, 11440979275521512288035140278052286485032871842, 1461525331963064205525226858229935928259006441378, 142117788059872, 282855276284128, 
    216964037239183405135560328339111106308754384802, 265785434843669645873327073648629838204349005508353802586205927359079061581895511101450110717389725380, 265785434843669645873327073648629838204349005505444455584198111750350122503388140895737298626607603396, 265752994540108411252272281178803296057984686442697136109135990960621360965501942811759141813350325956, 295320810091988165656855468244036106116063091826798709870977354542344007645183859535045208652668612, 435694908869088, 
    154219932158432, 291962732323023105017040791135679989649532354408371268991381512354674673483403107453901156943683268, 293682064039582975411785877199428464390043004891084410852227756007521543998051188501020887932541624004, 132875736950435933923408548050475631016215565175873823899455986091031676557542072065007679476067229380, 286015298341088, 75046504958176, 
    145415249201376, 286152737425632, 2044581885114101451459901653399317583943996782130056562728223343693773156987326955349290581186039974202034172191033632208753999675660509064045976588879549763035501096086772774, 282855276284128, 92949865336317527948875369299643328907790824866, 284436831098978251208475314375622459112215555607937931057689641337839406770938620288427919700965481796, 
    284436831098978251208475314375622459112215555607937931057689641337839406770938620288427919700965481796, 265751220461002921582585053644934673784160744669036241284558345185255177939855679207713769560759614405, 265751220461002921582585053644934673784160744669036241284558345185255177939855679207713769560759614405, 145415249201376, 286152737425632, 145415249201376, 
    286152737425632, 75046504958176, 145415249201376, 1978658307749821103328700726245097430261063721323732106580323867782391674267840381616484446153487531795437788444297763280177115616218472177760707792089755916768104409721296678, 2108619710240942702854833548511032895102107181873250621115791158614572907936375655843566276398046916, 185544998544594369126496316829367092608271253923, 
    2108619733444055736041001388243589516429034062865380578154437381461040541902170497928180549444198084, 149675856496864, 1464361709266407596754819612798040745790432355746, 567489805420768, 565224210172128, 569622390900960, 
    569622323792096, 565224210172128, 567490275182816, 1462216657701417058555050968566071512898533352866, 74909065939168, 154219932027360, 
    265783439004225734624146363717227644834827963598037524306572463549029042138874130033851282220211265220, 267859836218979294226255815674783841942388957047427489484218720818552133343452438196223011859129720420, 265750998701117921836540835143972706765100933621869457010751998074372214750691537204375353426496010373, 265750998701117921836540945485338749239980700428381720299868463942745198967045342868511798507464898693, 564085041398817, 564085041398817, 
    564085041398817, 248528823847136, 283953714104544, 73121889650912, 73121889650912, 265751220461005753993843987496762408277364857231370812872103017127403081720699000139893555529160516037, 
    1461596415838943819066073970941727094453889403299, 565219046984033, 259775868603384269922685981980179434430755927206987759693095226922730015253089311402545420181626469, 1461596415838943819066073970941727094453889403299, 265751220461005753993844099770124994949621442915462141776210462852709017582620895957302622058042023525, 1978643241384089909978371567717745071160151618234453085241664465541863592652859767840605508452984642363942094498370131804973244465894833148537024805384519695336228977283939367, 
    730842809590311771352134232949743218791929645475, 265786805002488844025069840217880877632797215770499067392776998084215786893529672010514874639504662212, 42920149453024, 1676866372978041557017497393061027105843445470385380739663568675052418331801264143192981609593517544258796263461921360757278370725145168795852463221732816120540476101430975544212107345443192800968841048345278724486807888752902404484144971327563069050998311472182840581359564664457047877172653490657458865772438260920916412873608604246909315671051134089786972587025892567465175082, 256658928972823935696541149439739135789763975987094272938685107359577844533592298052877282779252380507832164278109434674750960622477198231455206493133407960743041725098790, 261549947706041528351420271541310308827302274430020151089243007795207400882473158410533733049264229, 
    145277809985760, 295320810091988165446353336166077431251182526441214344548320542931342777874302723968840848794214084, 290833983343072, 73124037265632, 567489872529632, 567421085944032, 
    567489872529632, 567489872529632, 567489872529632, 1461596415838943819066141803272144828769393199523, 1978659015367662433294633052353903200427384750431432330874466077349645608106486055008437296359838714651382916118710088772739238942904568558307755306452341496953663901427285798, 1461864024610857724873775985238100333297496761762, 
    257263352643302525729737022945778826364094381271882702210819360458598540925794112509855574677389001547274914814042260439077110414069127449374006598311307369336357564432166, 45403714357728, 267861614242116419587613743861396958727759822301872632520087247066536850274072771452237579728012205764, 145277810116832, 145277810116832, 265785434843201353880842275523121229092469351903801437343026951535188924288466498330490553092170342084, 
    265785434843201353880843209775309977829407702669055234425804091789227416667502464186507450595666845380, 39655974176992, 145209090443488, 1461518362932420351363013087393052303439469609379, 145277809985760, 265785434843201353880842708301710276394937755334612376417499092218122906834289106570390859848763858628, 
    39793413261536, 141910555560160, 141910555560160, 141979275102432, 177302160017632, 72022377957600, 
    22858351047123333589456778951371387586667357602, 141979275102432, 564084940735521, 37937517496544, 73121889585376, 73121889585376, 
    564085175616545, 564085041398817, 81928921614816, 73121889585376, 73121889585376, 564085041398817, 
    564085041398817, 73121889585376, 73121889585376, 1461596426727979560536104801770292118926977403299, 1461518373821456092832753774991313427464747876643, 45761303733508096284159240621020199861973691810, 
    1461596415838943819066073970942304681110394636707, 565219046984033, 129887936237173166706074353688465364900655971856288126151343053838152809464376112704171198090409893, 730842809590311791634543836601991229395686164899, 145209090443488, 145209090443488, 
    145209090443488, 145277809985760, 145415249070304, 989322077652117790538083959611194994588071111467567570504911919345987255614225200261537502748066630369552125469674519147853975535637791382874413844591133405453726851066227495, 567521054037153, 567521054037153, 
    1461864025804250213973118148437544750284250685859, 130774975801719715161626530963904245120703490858488323611533823535116133630490216163431720601684901, 145277809985760, 2040476284013587729298224698291850964746590086068788872469018115771499585891023434863815326561290457396534344941658300788362857960798989251549976835007193032168431438519067815, 154219932158432, 79718959352032, 
    267843366571663460705901424538004017820915920012097477904460667412248058233088101508848956129737203396, 149675856496864]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_0 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_1 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580754811848928, 1461551814348214979509821877491715304423888004386, 1461864025804172167022504791558606681714620638626, 1464361718791983170821738214689037735721043502370, 580613077928160, 25690643582647842767884190168480725965092693282, 
    185542907841761638598597329414512522264779957666, 580684011931872, 1461596415839610869507908008526066243831138366882, 564085168047137, 1461518362975205374474752170211638886270992131362, 1464361718794313870680016674589103126779412358562, 
    1464357529240475998515287681920208346389661902242, 46028913675551939272039813989832245869839122851, 48526606668273970523338514994281278278054978978, 365422798756887947987963233058827683959776224546, 731110419545570891672152588845151911328078112162, 519108240874972279057902703935700662297495997703542862312995706724803923918580746595651110266160068, 
    184472472080228336352944560572341073466794485154, 732180864850997610658122785494543799391282046370, 265751980780636284737168116257735330920164708096608374554317276064391512182320033032116443423803919844, 265751030381104730270277535265267887877453154499858059090569746276274794558910753918335672720398959556, 265751030381104730276580330266633483026748946612675747124127560967135661664348753610319218022189056964, 1461685619845247600828798145693906795839743354146, 
    519108240637049734531439429689054076876897614204900754333118984688677940065419950348883150831305668, 183045231193169714890655543870383726965775967650, 1039103489897385337726990325689769028355917716509052114771883537084256224072980776215646099732647396, 184472467996839933301682999011845784285575947682, 53052544417825, 53052544417825, 
    53052544417825, 48526606668273970523067715610687601342920795554, 158605664879649, 732180864850997691787761200101225495180287190434, 33218935722611761806879715280587196168506442965671350897046756944699441404128845767352382038745498564, 365556604253920616209779595357845211593400935714]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_2 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_3 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨0, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580617507113184, 580684011931872, 53052544417825, 581094114134240, 580684011931872, 123421324250209, 
    16641875556787413440751762232560241070303430086482272597205743525148628808405006703318061343264759108, 580617440004320, 580684011931872, 53052544417825, 53052544417825, 1070530033986493666498307113778476560855143382517919700181631686532106076036365620531977957651258020, 
    185542907841761638558905876609777112023621445026, 284232618609120, 286431641864672, 562985656418337, 1461596415840942698722724592725701640651419428258, 565219047803233, 
    22881261833530618524737240965139669731250808098, 354603510335968, 25690643603583261028183229088709178469846099234, 4184799348921628307522312186918547802802313476321754787997918953062793593021960684830508180241818564, 4184799348921569183703602233998564465594832345207647577110675447042144244954776690184685573775467460, 185542907841761638598597329414512522271222408610, 
    185542907841761638598597329414512522271222408610, 185542907841761638598597329414512522271222408610, 290829688375776, 284232618609120, 286431641864672, 564085168047137, 
    564085168047137, 564085168047137, 284232618609120, 565184679676001, 562985656418337, 564085168047137]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_4 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_5 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_6 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580684011866336, 580684011866336, 88236951144545, 16641875556787413440751762232560241070303430086482272597205743525148620911894976909299489706609761604, 16641875556787413440751762232560241070303430086482272597205743525148620911894976909299489706609761604, 290829688179168, 
    268897676423098020835752910825479517298598297101009976932659886816732455231059010924612737781457771844, 290697560111706829943434310619952039434819309853098500487021003570256418949922631231122339952805829956, 290697560111706829943434310619952039434819309853098500487021003570256418949922631231122339952805829956]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_7 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨1, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580615292389600, 580684011931872, 1461529513347638151866091143278951934799995996579, 1461864025804333452665682830778454773252316474275, 3353732544361847878231020834665803982489058087929606401878730169816067366497701070229691740194240691637303559038801513357731868803397831193990798608962225595541852569635828772811288142120818753973022487646036867953119419951246930319619035056582821104176814546102189384240376355320927894864716104796478400526507129844746586220517376553220010072284843497627404779566940802620508970, 3353732645497406852575570240187429523088447220606522246932041415020783112689446234757650657204059444868585354858640826686427512412667218561141511366637644324348272325389668529684223116628364481042983501762644575936761753678197627024989719513183844573575888468332392919985100246034814412803048190657755253111736720559139473400607070914696814626957732720641572440631032276066195755, 
    580684011931872, 580684011931872, 580684011931872, 580684011931872, 1464356840506301691987130105236524754220414936482, 185542907841761638558905876609777112021473961378, 
    16641875556787413440751377567315077708854116308352862244994577874911612905182636642080686877545880900, 185544998536624000844516848388100583048671143330, 185548483028061271254382713344080684355156452770, 290697560111706829943434310619952039434819309853098500487021003570256429403397951128416742863994379588, 1978670256173712906548994319048682252558666979804164767575041440512432838285922798567495837931932105945782480258890570558926948065274983407918852158891199434833153349749046055, 8563540601664184695444461689229515276490909474, 
    1699133317294631717207704971570282511259686404849958357996013558839685805107279310479560100856830304828208569826740228017935843437696261755887330977477153420915224741518812335595304650504137681601200197835399926221746937159340467494943283672286710572769162019769281353959954213967771463253279037487010587881402657021899475437958361695956426006956573066020067802773384923499, 3879633372745541415433854513852050427088000162355834265511830072314937021388789707652579835383916140906327486416891862260687223654857375832392189063237387355003335109222182, 88238027245792, 61847696218876081133648532114023828154670230499747643436587358142346381874713988243688223589855142921675241442322338564721186329059854080971359374437138155951148490346721062, 53052580105313, 123421290728545, 
    123421290728545, 88236951144545, 158608985950432, 16641875556787413440751762232560241070303430086482272597205743525148628808405006703318061343264759108, 16641875556787413440751762259394230866625162946955260243595050059804018643908542115201540465563295044]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_8 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580613077862624, 1947364611433739721585986543006381318093422601235450631885942670187472435924362448260063439904174681551000016816285422614257890954996682853156082660245587431174425650487590, 265785941722929864046919444035801939253827620918186126940031253508166486590564814629632813425046363012, 1461596415859547988820010818270887395390453722530, 265783724124077978312316655652892103834771613113563759921495699479618275471373149843183995695257394052]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_9 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [265783407324725392828938334356413918702589570505240244369220773529445971320415210605458970359238794116, 580613077862624, 580686092372192, 1462220837730012315345500341641065554742826526114, 567633686694368, 368230264061634374609396100839152640411415348131, 
    1461864029895551545285763668507741183320980497826, 94201146211413098998660567317321297328840377251, 580613077862624, 580686092372192, 580613077862624, 1462220837730012315347981057441361517883033150882, 
    567633686694368, 580613077862624, 1462220837730012315382943192402871010647469483426, 1461864025806835825412678620910508636863373796770, 256629444892258282455369622279040981724065160127820438257222776953423691961398625637059718552862824726185903694711619822727707083954250205820544084165581193416601657916710, 1461551815369062037132902816348691757393529808290, 
    1461864025804172166982813338753871271471314642338, 1462220837730012315382711078645505001845925897634, 565503584307680, 1464361708073098996019168764384491385925021492642, 1464361709266407596774665339200407887959984448930, 567427729590752, 
    1461864025804172166982813338753871271471314642338, 567631740537312, 564085171291169, 564188250506273, 568620657808545, 1461596415838617189893654105203967734131315975586, 
    1978643212821386010807107750448100995069496641389945844396047098621518295509966071532867615090972549380150590285298428589463147078028047099625466950076084683134093896312444710, 1461529513352809699263766414278116851394768578466, 265751220461002921582585052732474200836242977533939004524028255182134405329406244433389091322524720836, 565432717216224, 565228706400736, 2108873149626520285567050569496103076377643235347818900853320097012201865650391258038190348626943684, 
    567392296176096, 565192199047648, 567427729590752, 567427729590752, 1461864025804172167022504791558606681714620638626, 567631740537312, 
    1461551825066880383686554919444992178735920227618, 1461864036693207908492535622386594119531203405218, 275742580346025275209528232111699053630928717380749698382842895999242621624513196456138304899177348, 310495522190382098799099326673112421792647339304957819114407699728329681296832142637945022384299716, 564085171291169, 564188250506273, 
    564085171291169, 1978670219318611101651129551064750797595114239298471612128320442342558456895019144375637694179435056644708889036599174610028923443378324172413426112623730177835048216338349862, 1461529513352788929998496794416462006303184136098, 564188250506273, 564085171291169, 568620657808545, 
    1461864025806835825412678620910508636863373796770, 275742580346025275209528185990778691345372833751728675648091375947940958259933753437540556167224196]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_10 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580684011931872, 564085166965793, 580613077862624, 567486785393825, 53052544417825, 268378631573369239685731794257359673725133098866137700617482854614231379639685433184860953753626385284]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_11 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨2, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [580617507113184, 456791912024916798872480452023733297145563109639924032480541442978544057112738797334476516647500799684, 456791908188668796440559530058682954448601687839746180109166998968032555866100214555172664727617691332, 16641875742412316784231806939368443075979706428721588638005444319900202591116964215863710145760485060, 368230612510778101650383934035034838842818692003, 1464356230722953767981422241135381393989366720418, 
    88236919687392, 123423439292640, 265783660764110970404461427929761164671223986946678848704442800608119805202921469802069842577717223108, 580578718058720, 580613077797088, 580613077797088, 
    185542385170700619872826708113157618870472158626, 88238026983648, 53054728669408, 88238026983648, 7560670634479108855437536186797703994533052022643170831690317376582005065704681182018955815859494584937138450825515204245214687558275762215955843814495622008030357126939590153660509119224583016163736492553711884034465981884738275326811481556146100109442122998760, 1978658307750130403652075570996415654783467132576529401807680038276438053742805961390967341204399747908160772128397068669633430268206222213070432490386015123335768713890191142, 
    580617440004320, 456791912024916798872480452023733297145563109635105426465579051991234410655388380475976796466278588100, 191040945127532847629300509356555999372904753959216939898341179465393963644610025836011499193977822916, 16641875742412316784231806828678235166152644401024368103844119126179659608598424117160781645706452676, 368230612510778101650421410878405158918483608483, 2108619732990869929884433882075171882784382928076395184396284483315176274518413878669718759234411364, 
    2076211109836584743643006813666602705894022748450522809128520703816014251230394414829350287129270308, 2078206948827074159375332889422874939590137389076434249449186957297551310063451242713337131082521444, 568620657808545, 568483217806497, 567486785393825, 564085171291169, 
    565253410786785, 2110647228716903754759645893196866741025302504055338355712461860582992749770055514721915068933070532, 2124839861432418469047889324897625585685455500713237997818358049142033181718218252733531605850250948, 2076432846518471456501550628901021036471574699672625445977702499650109024329314490177418088541707972, 2108873149626520285567050569496103076377643235347818900853320097012201865650391258038190348626943684, 400702877438222498284136709685035365591524925667992749875618114367476358196094270915588839036118752964, 
    564085171291169]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_12 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 0, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [158471546996960, 88031868750048, 185542907841761638539330949591003646787056051618, 1464356317851191470097698738169763202800707710370, 158471546996960, 228773719181536, 
    158471546996960, 185542907841761638598597329414513085216880862626, 732180864861631475109838414171643157383656023458, 73119742298336, 2968221476721395911463059958353637030322414197924683716333860813541162146582843238778885679134196903836800593403937881335228534483873777686595898291634437512145902845026084646]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_13 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 0, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [142388974651616, 142388974651616, 265783439004225734624146363710623967609188187511895397859182090146005991413786937908795875307920857988, 564084940735521, 1978658351975829919390076002404130927781666647948487748713508071334730045911427357502438717783473104865813555215951511416271446673385892189629227110065017560267027685143723814, 22881261642454015615778646946920668767703278882, 
    22886139930466194189590857885297243827665904930, 22881261642454015615778646946920668767703278882, 564085041398817, 182733003227852222152585135425329515100939756962, 182733003227852222152585135425329515100939756962, 182733003227852222152585135425329515100939756962, 
    182777604888390466859337438593562115539835823522, 182777604896386634445095478619006967607525420450, 480481306159211361205044992421904139309116810276696193309304011708559916188545629281915133179791458265111617267290289405163740572486879286318082418004927073554939597387653772020712829106139716191208002007470375985659070917427578291145160748223204920710398082123494280, 565253276700129, 565219046984033, 1978658307750102288444220109193682500779982993312867584616715852014250335752425202112433842734881997068014341070780487950412453914826877966989394046386435996628967417235330854, 
    730842809590311933612030032182749300507389495715, 145687509534944, 145687509534944, 567521054037153, 265783724124077978312315775927331316819994843470762741228865708468096027483846600650923028942540529348, 480481310354363302387925279167597941792341734797724518518914413275027457397732829757761795017425767368345521074420046321043453486907287142420365720223321071947994470248899768353961620297583435682701624432029407776324745252049857430410621402168943991647633554373495560, 
    265783724124077978312315775980999296412638273430012510051189705753141943595699750866852919722917256900, 567520919819425, 567521322472609, 44531332745440, 184115654704537808061906533640540128713160271266, 184115654712533975647664573665984980780849866146]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_14 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 1, false⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [183045214851619935099851257602959407029514937762, 158471546996960, 158471546996960, 158471546996960, 228773652072672, 88031868750048, 
    426557545570150979292886852015930290358822704518262636259917213075445889387282365282275333220691123076, 88031868750048, 88238027180256, 366090429719190666718742185201839699486231258530, 290829688375776, 365555209792731730237714547183048494219478463906, 
    368231301258249606540329614156013942190805378466, 368231301258249606540329614156013942190805378466, 182688054477970490102718666277445269396614817058, 73119742298336, 73119742298336, 45761303733508096284091540627548953942715542946, 
    73119742298336, 730842809590311953894439635834997311119735949731, 182866808209466956272842044930029005273930671522, 183045214851619935099851257602959407029514937762, 183045214851619935099851257602959407029514937762, 268898052638370872342010250806000974669552440848297282896829893360040903744949806848861887557992072292]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_3_15 : TreeValid ⟨some ⟨1, 0, false⟩, some ⟨3, 1, true⟩, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 104 ⟨3, 129, ⟨0, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [1461518362932420513622609071879095820151563616675, 480481309846575119507226613771215384544901847850468063456865502520995091900465889430512254432520260318707030660036076409296655255637198698492247333114119276185179218997809019178468368211700220536489498830760370404567033985429735559044021058253840791191425154124763560, 564085175616545, 564084940735521, 265785434843201353880842275516517551866829575814752805008146650787229117267750141009161969722396285828, 564085175616545, 
    564085175616545, 265785434843201353880842275570080711585907759626024107445556433532774299848067478173266799141887532740, 564085175616545, 265785688283069385512264064847160202541508369588684349368086387721852728234269095763960684602564057988, 564085041398817, 6065825835864938706712286055999176633620112802, 
    183045214851619935099851257602957718173212222882, 1978658307751508209731300482704683227442739315228079430128577022410507173145243761448758190635129763049917337560821391970091322759035720949501027215234838278245168272896644902, 1978658307752407999355006782111855050126177310681246586821751509892825522612654146230635958834459782788238687287041827716322829773084220505574813342414469039130701761054725926, 183045214851619935099851257602957718173212222882, 183045214854278401252432894024235328660723737890, 6065847616590020001243667103782705115695687458, 
    91701362521096968864702591979467639932227953954, 356813289622890078333541487308190147813057826, 365735010215529589817526813111199672587000538402, 365733616418933912426532246561161341273727591714, 182710702397583099799208983841213214881491723682, 11429872459070405313140457847376999519571420962, 
    72020230473952, 22858351047118790312374400427201099553791550882, 564084940735521, 37935370012896, 73119742101728, 73119742101728, 
    564085175616545, 81924626647520, 268346444709646768439378511291838382052624662163432396564105065240667503564029006768232166749048445828, 73119742101728, 22881261663389435148375395802283457969568359714, 73119742101728, 
    73119742101728, 73119742101728, 1461596426727979722796000601003298200642437253539, 1461596415838943981325969770175310762825854486947, 565219046984033, 1461596415838445518926103824052967920448199231907, 
    730842809590311953894439635834997311111146015139, 265752994540085751962201342325753595842097161414569570351413697078861626526421931092411586657484053380, 182866808209466956272842044930027316417627956642, 182866808209466956272842044930027316417627956642, 567521054037153, 3353732545142508947553909095694950810962758535436650273245993579966465460556619333454460742907229312561562038762956331846210659920416901908161371334488718803021136908221403688805632427379688726467732736483165572173739002334299360703298530760917788191531350519410861106635560813203324949664485641096964357715212768568001815212900300278254152354337391926376269572933659831028918315, 
    265786448602673480406525912296669777947002613149537103602587745076104799049482320867583952303321374404, 1462934465654592860128672919099945933615096955299, 183045214851619935099851257602957718173212222882, 286514784692988995531271664603435766515803851897168121404500017733107427551015027987564212883152723268, 294819502288649493931623509000377233861919381080784078723120749874211456955734681085036179650172181828, 183045214851619935099851257602957718173212222882, 
    183045214859595333498175158317887885312073934242, 268897672494043231662686758464849299396777228436100830375961495382819709868404119767100095918631034276, 268898052638370872342010250806000974669552440848297282896829893360040908670867930370149519850294363236, 183402028135925892753869682948818521684380755362, 79716811868384, 293665847845670322919496313130563292487986235003303980327981612944240290839735350543779822693260499844]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨0, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 0) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨0, [], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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
private theorem tv_b10_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580679716899040, 567485577562336, 567485577562336, 158467252029664, 158467252029664, 580679717357792, 
    580679717357792, 37454332037217, 37454332037217, 281750127773920, 141012773636320, 141012773636320, 
    281750127773920, 281750127773920, 213587050629344, 283951298513120, 290554810730976, 88238025345121, 
    286010601113824, 75046303828192, 141012773636320, 141012773636320, 281750127773920, 281750127773920, 
    72849428056288, 143213944375520, 283951298513120, 81654111013344, 154219798071776, 154219798071776, 
    290554810730976, 75046303828192, 145415115114720, 145415115114720, 145415115114720, 286152469252320, 
    75046303828192, 145415115114720, 145415115114720, 145415115114720, 286152469252320, 154219798071776, 
    154219798071776, 141012773636320, 141012773636320, 88238024886369, 149671159269600, 281750127773920, 
    283951298513120, 290554810730976, 286152469252320, 286152469252320, 72636625848544, 72636625848544, 
    1461596415838362766379284749877366205707669490083, 259775865702995140774971271277239109653187052792816183811854023041045167764170216211354610863055301, 259775868603384269923235542877360150664453863099591285439722947210842173767332281274261322000916101, 148472930502880, 148472930502880, 16609688878692677949138448138259498589235589870566143166940225714483256586337807105545012614813123781, 
    218841674680544, 565220120988001, 72636625848544, 72636625848544, 41923381823712, 41923381823712, 
    145272978540768, 41992101300448, 265785434843201353880842275523121229092469377225303081087616829291269993545823062066695827171878919876, 265785434843201353880842708301710276394937780656114020162088969974203976091645670306596133928472436420, 1461551819452450441493904901989334927059003647266, 1461864029887560570014345231233403717700681213346, 
    81924626647520, 290829688375776, 81924626647520, 145277541943520, 564086250177569, 265750998701117567785133694248087745524965547099048198757609976303913481982811900240218879303814495173, 
    564086250177569, 564086250177569, 564086250439713, 564086249358369, 564154972900833, 564086249358369, 
    71539400115233, 71814280129889, 282851791078433, 265751980780621178533282367467017635107146556920383709590802443035125017832479327290888581087889479684, 265785434843201353880842708301710276394937780659023367187127880105964815475640414279480262452524900036, 265750998701117567785133028765150623647067652291060578762922045218851002608247267177580874510874983365, 
    265785434843201353880842708301710276394937780659023367187127880105964801637946520670735051901488881348, 265750998701117567785133035634652011505426307044851708241980730793085982376696526980095081908472819397, 265785434843201353880842708301710276394937780659023367187127880105964815475640414279480262452524900036, 143074089502944, 143074089502944, 265751093741071738178133755094820357365099460643187973233610329484671222768775828080102744026028799909, 
    265751093741071738178133751660069663435822702447068898130134914483247626801182887458771200581497092005, 265751093741071738178133751660069663435822702447068898130134914483247626801182886338131498103641831333, 265751093741071738178132872363892017565768461732524021087856305320082128056609573155697694983470282661, 74904368580832, 145273112758496, 145273112758496, 
    145273112758496, 65007330021075508547826595426886163451065368117159109654919917559637237166161574828768699373942693, 154219798071776, 154219798071776, 145208621140192, 145414980896992, 
    145414980896992, 145208621140192, 145273112758496, 145273112758496, 145273112758496, 145273112758496, 
    145414980896992, 149671159269600, 149671159269600]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨1, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580683911268576, 88238024951905, 61847696221575429410295888569122168145685836984712591577978497999059917937636908006816703823891922504669006864521300262951819309857365767927860273784473543542082400450246950, 565219913107553, 567419005569249, 580617507113184, 
    580617507113184, 580613144905952, 580613144905952, 567419005569248, 53053618389025, 53053618389025, 
    53053618389025, 569622390900960, 53053618389025, 53053618389025, 580684011931872, 580684011931872, 
    580684011931872, 567489872529632, 567489872529632, 567489872529632, 567489872529632, 567489872529632, 
    565432582998496, 53053618159649, 53053618159649, 53053618159649, 265751030381104730270277535265267887877453152262575895801430822502022209006975477447280385838110950340, 1461685619845247600947408274674919625300780803362, 
    567631606450656, 567631606450656, 53053618159649, 158400680036577, 158400680036577, 158331960559841, 
    292773767353874293100052443275407498543558248334143297892735441372724203297272833512752037052426510020, 365400497777412721975112170588488459421473056546, 53053618389025, 88031866652769, 25690556470112352675150954066475757337718564770, 158469399513313, 
    158400680036577, 158400680036577, 480481077047106023417608928812220475621679691140121801280980570410987408711367860847130332735108649889724619450414631887351141038045375249632861573336178609816643572164684726376039516701064808713338693634068481260756407526393210582897083434795237521441693696624777161, 565219913107553, 265750974941130293871092047372513272416074009002926972971298991347563632685019577617879114514452587525, 580684011866336, 
    567489872529632, 580582040013024, 88031866652769, 88031866652769, 158471546996960, 580684012325088, 
    37454332037217, 39653355292769, 39653355292769, 290554810730976, 281758717708768, 290554810730976, 
    290554810730976, 281758717708768, 495070617274848, 290554810730976, 283957740964320, 281758717708768, 
    286156764219872, 88238025345121, 286014896081120, 16641875556787413440751762232560241070303430086482272597205743525148620911894976909299489706609761604, 154219798071776, 426898681760224, 
    16641875556787413440751762232560241070303430086482272597205743525148630462912008167553776269275454788, 290554810730976, 283957740964320, 290554810730976, 286156764219872, 88238024886369, 
    290554810730976, 283957740964320, 290554810730976, 286156764219872, 39653424498912, 143078384470240, 
    143078384470240, 143078384470240, 290554676513248, 580754945902816, 565361783343328, 565361783343328, 
    567489872529632, 580790412937440, 256629444890500894254069305822515351835809908151876476823440332491965089880377430949797159924444898666701794732034471471311639890366055479242287959637961664617606166845734, 88173736888544, 580613145364704, 1464361709269071255204259821825881564491939341730, 
    564335252408800, 564332970904032, 567631606712800, 268587543360758126600185884932718958242587867672881719051674529098585866633209637165953666151610169775975569972726392361184783121232589955911974548199060547120248860421926, 79450859899360, 44326349965537, 
    154219798071776, 1464356492059812536821553863652083056186538072483, 283886806894816, 567631606254048, 567631606450656, 564332970904032, 
    86052291742176, 158606838270177, 158606838466785, 284170543172064, 52812264507616, 580577711491296, 
    52812264507616, 158469399513313, 256629444890500894254376186192005615109522102104721823124539985196916557226005740332637908940329307725019451187702459671784281231654926904847295213810889042246455063976998, 36354889615585, 1461524635064786811537953336679228302882469603234, 36354889615585, 
    39653424498913, 39653424498913, 39653424498913, 44326349965537, 44326349965537, 141021095135712, 
    141908005882081, 142120606763488, 141908005882081, 141021095135712, 145419141646816, 145419141646816, 
    149817188157920, 154215234669024, 281758717708768, 290554810730976, 281758717708768, 143220118391264, 
    149817188157920, 158471681018080, 193554047699168, 158471681476832, 145277541943520, 356321497450976, 
    72638773332192, 72638773332192, 213380623763680, 213380623763680, 143078384470240, 143078384470240, 
    143078384470240, 72638773332192, 143078384470240, 72851374213600, 143224681794016, 1461596415838363415418867946809390532569508891043, 
    489288346087263500381072930022711200453851714844168102167696518807840101114483326923186467590564399462691959901939465432320074720177332506654315875106838778692016685054033232326709644591093353408254702890375674340654770670911890676187076495834089106423414930123494280, 489288346087263500381072905188486247434913126647137103894213431983830497981894741068467168704098062787565658758836233066561644304878245960944933992523364451560671184555777913699572464556278336170538278064104767599839231449000875358733533752392540497112989842123494280, 293750358285355512940925011092151264110289031204220046397081134235883323164801266814980656492786507076, 565220120988001, 72638773332192, 145277407725792, 
    3379933736864476015231514933156092806495937325501796113585462294517076061129628601991947039371929338461611200703622099456918457697987263904141567787434054573983986633328371483069791700151971277388192631542022827380986894564873482883055633574350723513091803984681688878860908807369526112813685254486209318214003370650012442512700621345425414052366281948794424671503003860198336554, 86527524943621269157626681606394904430369114783886196580636374249112518495511727563387572950793768464769576223346396097520492952882448429281082923188162541043777570846312010910583865351776175857463915669581992887451468892755667142335557550882295317505798794317074523844253485208295271300278603181916625262947685375687898786851351873293476660604387620000509540405212538117246991818744231303450724203378285218260542912457283134540372749520801126623833892105108825934827257401725097497037830864854716236453791220866562605600768409681785035997589686817741795704276554425399630238523512434573308505230236221223055040833843581972173107597649089795272723126830, 290554810730976, 154219798071776, 290554810730976, 41994248784096, 
    215579647019232, 145277407725792, 145277407725792, 145423705049568, 480481306322647488913651718499145479449750488530043158618303447750326298941259409040351410545079490227744562777638113701161874085521394052995750041520081368007998475509947174813739599026853441693981482038169524640312436199736449961267221770031937846077554834373495560, 567419143852513, 
    41856809830624, 145277407725792, 72851374213600, 79236111534304, 79236111534304, 79236111534304, 
    149675722672352, 149821751560672, 22881261833530618623772444107970091723180746018, 25693256951225794315060628892948682097648215330, 185544998536624000785095726502402329853513180578, 185544998536624000785095726502402329853513180578, 
    25693256951225792963307515024701113713356711330, 145277541943520, 286156764219872, 290554810730976, 132891703662604380753422064223388566223073959142295265575623059825611243540687392233336087490309871620, 366091826238024510448034493935738350967571670306, 
    732180859417113604454051161271914901973110400418, 290554810730976, 730764756684370999216843158183718329944237015459, 145277541943520, 145277541943520, 356321497450976, 
    145277541943520, 145277541943520, 145277541943520, 1461596420943180458699566872517709444153747736995, 564086250177569, 564086250177569, 
    564086249358369, 564086249358369, 564086250177569, 564086249358369, 71539400115233, 71814280129889, 
    142251745873377, 282851791078433, 143078384470240, 74908663548128, 145277407725792, 145277407725792, 
    145277407725792, 145277407725792, 145277407725792, 215575217834208, 145277407725792, 215575217834208, 
    145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 145277407725792, 
    290554810730976, 149675454236896, 219977693530336]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [580615225280736, 88034016233696, 565430569863392, 565430569863392, 565430569863392, 132924142480290222037920648486651301480666804402433759546162282488535761464693859870545329298873327300, 
    212416403605728, 142047659428064, 212416403605728, 265783439004225734624146370586729032692991375379451164617417707716274441800808969765004834706524495556, 282853938562081, 72705278216416, 
    72705278216416, 41992101300448, 41992101300448, 567627244177632, 519108240874972279057902703935700662297508705731253550088117536022733189463697257037479427514254276, 184472472080228336293523438686642820271636522402, 
    732180864850997610578894622980279461797738096034, 565430368405728, 265783439004225734624145924070075653037287621098960778873780339262661415597330059875556864544631462788, 75046303828192, 141012773636320, 281750127773920, 
    281750127773920, 154219798071776, 154219798071776, 290554810730976, 154219798071776, 290555079166432, 
    265750998701117921836540394744438814027433848277094921853098075468974240000335355477374641320628344836, 142116588623009, 282853938562081, 72640853706976, 72640853706976, 72640853706976, 
    213586849302752, 290554810730976, 290554676513248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨2, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [285916514224608, 580683944757472, 265783439004225734624146418676580303346154995467527280634560056780212784326092577756565704117180194500, 580578718058720, 25690643582398609352023897950308518955772814626, 1978643329836335141665315320984264572402854381768892296065643358080522664321490345135915003070899957883193204924684545073626256727066409222348390115310321259623750948770043686, 
    39626983344608, 285916514224608, 290314560735712, 1013759487232776840238303359547232881194427625734600967349270879995776458026907996699883520148420, 285916514224608, 1464356317830006169542883541724226275169542874402, 
    580613077928160, 580613077797088, 580613077797088, 228911091026144, 88031868750048, 1464356840524906333188661418534371817633788470562, 
    94199055528181768369545574767534342002367276322, 88031868750048, 1464356317851190742627181538790974802437815674146, 1947364611236912243079631787170169202981884856844543913862613515838507685354374774698079747061035354694616595427306895871141554285234611130657411622524533456419203404736295, 3879633372942368893938572574384219203083424220396155680469944084513623703902010277458749146906299791390555206167683617409846170101580951702577025923696357244442283114232870, 25690643582315572533281247897478178154213811490, 
    25690643582647879532227476865704129925726348578, 25690643593281703498506803848934586408237540642, 132877509544519530179114695480352936032184208703404860509678107610433328794928327074796224913817777860, 132924142480290222037920648486651301480666804402433759546162282488535761464693859870545329298873327300, 285950605789664, 580617439873248, 
    580613077928160, 39586848313505, 74846520740320, 285950605789664, 39586848313505, 290348652300768, 
    290348652300768, 268897676423098020835752910830301249840124854727006583246943173723451120787758578489967442829975248196, 285950605789664, 25691166256363432140869097239031609866129515810, 1464356840503970992247621354444122707354970498338, 1464356840503970992247621354444122707354970498338, 
    1464356840503970992247621354444122707354970498338, 213376194578656, 212418551089376, 141907938773216, 141907938773216, 212418551089376, 
    286156764219872, 281758717708768, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 
    141907938773216, 141907938773216, 1978658943960902658872645038924875586054885662660143198589553699382062507832600374953322532339156172758169253598564547257824583670708759332349018837580318114114087900011282214, 265783439004225734624146370580963917648486676615215624540147174576578469320026242881927702477725014916, 282853938562081, 72709573183712, 
    72709573183712, 41994248784096, 41994248784096, 185542907849737037016583199106250585019397973410, 145423839005152, 65339969812461898038710211723667840648082120146251416282142617341648534104170827966573309019076, 
    365559391847070412176034521156694531097793946914, 88238026983648, 426898681760224, 154219798071776, 154219798071776, 368231299205921540483310156671128805145410303394, 
    368231301247615742008998966112078880820920083874, 286157032655328, 290555079166432, 732180864850997610578894622980279461797738096034, 290554810730976, 290554810730976, 
    267859836218979294226255376021234537935622776159015050894712493084826497899284778180041958515939624036, 72844864653536, 72844864653536, 495070617274848, 265750998701117921836540394744438813980575534208259484611273849766784074265428294392380389698336479236, 141979275102432, 
    282853938562081, 72638706223328, 213376194578656, 72638706223328, 72638706223328, 143078384470240, 
    143078384470240, 290554810730976, 290554676513248]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [71610061557921, 71745350928481, 732180859417103219741646590350172007124498441634, 265751980780607016487862726761810993489367034875438646582494538141580712049396237933260893873563192420, 3891581796777935685094822000810561401191019847481731136212021999840434662406252339249773317622634873152403769443610297877030598029698974981359183485982174695304166848314150, 290829688375776, 
    81922479163872, 265783407324249547732709526604378087006019092529037106645997147548404654328736400019831610187479035044, 265751980780613625443945055502466486538738431426790169651316157672089032601101335064711840220739488868, 290829688375776, 265750998701117685802270660464677472208905944593431237292009038046571307939260787788742811872361849189, 1461685619160695147386507457658753067081995416994, 
    290829688375776, 569693123447264, 1464357529240476059243674249103823111841099834786, 565226357459424, 290554810730976, 290554810730976, 
    37525201096865, 37525268205729, 72645148674528, 1464357529240475998396445438148815217714098890146, 72645148674528, 81716320930272, 
    292753632659936, 290554810730976, 290554810730976, 290554676513248, 290554810730976, 154215503104480, 
    290554810730976, 154215503104480, 290554810730976, 290554810730976, 290554810730976, 290554810730976, 
    290554676513248, 290314560735712, 290348652300768, 290554810730976, 290554810730976, 290555079166432, 
    290555079166432, 84121300830688, 83640600496608, 149679749204448, 6244232476693876645350435220408889441989981474, 5887419192387918991332047653483326585556202914, 
    39728988686816, 436549607098848, 44264202969377, 7136265696753017691004692269661439026773623203, 435553174948320, 435553174948320, 
    145282105084384, 145282105084384, 145282105084384, 37941812464096, 39728988686816, 39728988686816, 
    44263968079905, 148597187228453110582768391757167285658619921584523359327569801660893296801521061592577783418410096730916428337420138153632373576136057470845941328435870938312705919928687087504796295054639882376047819662229505183701315447319065972225272010145543723041081128160893443768198654172303639748978947007677391107396150679158889662637900268415525184338329647977449273063082565661606554051323990973300551421725840832688321748763935500613327938285309599997245121363200352530998779956604712290649758910907589993869, 290829688375776, 3586318182594794181805264427600586358752501732151023189376291685397171099975880867475098974530252152621198639781564644837310471650041800957412567664727515079340669353442933030, 290829688375776, 981230230509837395243425089791080917627534315748234650717808376557565986365570274027094703720842508863955179343189905519358535331113170726602001266495421284985140196943654, 
    73126184552928, 290700601760904725129766619016589205088817020817726984538159219055062340573316479827615637759502966564, 44263968079905, 9079594942497, 74912958515680, 74912958515680, 
    23562133842359560576016044018561493130168264098, 364496732654048, 290829822462432, 290829822593504, 290829688375776, 435827583224288, 
    435552705317344, 435827583224288, 290417237559776, 290554810730976, 290554810730976, 290417371777504, 
    290348652300768, 290554810730976, 290554810730976, 290554810730976, 290829688637920, 290829688637920, 
    74912958515680, 74912958515680, 86252007721440, 45850507054593596177879281179938270332240557474, 74912958515680, 74912958515680, 
    85908410337760, 282394870282022164641411108182438834331598840835597544049986939406164741523608597554182953959351246628, 145281702693344, 290554810730976, 290554810730976, 146278537365984, 
    147412006472160, 145282105346528]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 0, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [52819542442017, 52853902180385, 53060060610593, 48526606686883162464027522467971594302584792482, 52888297606241, 53060060610593, 
    72024525441248, 73121889585376, 73121889585376, 73121889585376, 79727549286880, 52819578129505, 
    53128815971425, 11507228419542135508628717042249704497755457955, 44264001635361, 52819575997473, 52888297606241, 52888297606241, 
    259775868603384269922696339847830877829637299104836452252464645803405350447172574022969683264043461, 44264068751649, 44264068751649, 37666998985057, 365466006471646154284668350512299160702802210210, 259775868603384269923235595706777758977743463127588876452026517482171393967644916996803709129350789, 
    37460983155041, 1461549026776000540986347740600932292173631071522, 1461549026776000540986347740600932292191884682530, 5753636162973532723427539908632013597891383075, 88003949168737, 2108619733444055736041506236220553303479071560366536819431414106942035445791001589552559653331804613, 
    88003916631137, 88072636140641, 88072636173409, 268897676423098020835752910825479517298598297101009976932659886816732464782076042182867024344123465028, 212418551089376, 143078384470240, 
    143078384470240, 145273112758496, 145273112758496, 145273112758496, 145273112758496, 47099353539030659495171335932542064912078211491, 
    88038309103713, 88038309365857, 212349831612640, 71820722580833, 143078384470240, 145273112758496, 
    145273112758496, 149679749204448, 141976725358816, 212418551089376, 281750127773920, 495061758904544, 
    283955593480416, 283955593480416, 290554810730976, 290554810730976, 286152335034592, 143490633763040, 
    143009664993504, 145273112758496, 145273112758496, 145273112758496, 145273112758496, 154219798071776, 
    154219798071776, 213584701819104, 218843822164192, 4535624403168, 4535624403168, 265750982861125756828414396982106008458777873180850625806372260126224153609647848076520218683503565668, 
    71543489562848, 71543489562848, 265750982861125756828414396982106008458777873183757131650551874730490830463867431101508455687166909284, 1978884747222783456185379191100483388765130552673384691772630548306025393764125279657822328564465695297209909551853673858886016778292115142266915770472055836637857984975712038, 71543489562848, 2040475813996767279036676692917856389751479123634140620313394207462623933389239616034595169684909792480551432596886445302342606951268281871948388225158490955432268461985738534, 
    1978643212821386010807107750444613416610963030056899480255767622787934060633012627096814006321098096391995457171480070831462433597158364202751091025107569723442650542822415398, 212281112135904, 212418551089376, 212418551089376, 1978899843072482742350788208465535590217910939314355370475667720102535332362005618195295064707557388008559149823443752618004976116738360251085607696479233500927795806333808422, 16609467118804845791834747780889983191600596382466694902789538009880429232935384172979083144240904325, 
    142120875205921, 91355699691807614560029158194974572530280456995, 284955875948704198218485432771182189476965516051990780512828290854769669315430374158489936151134101188, 284955875948704198218485432771182189476965516051990780512828290854769674119140711307586617588392681156, 284696353523842641797892259298069207393376191806089318895556981719457244979874412567699975096264318276, 284696353523842641797892259298069207393376191806089318895556981719457244979874412567699975096264318276, 
    267827399859917987289355648597101113023206094497489919610352487705603971361742974890194153226105806532, 248702267033824, 494993106536672, 107827339725024, 354118179227872, 143078787123424, 
    61848169806933395430846284208724093005617278931201403058880967934972992460584414872855522911853516239961263080356841390965099927085657066845292065431958888263019683896076071, 182776995100062786532783822418101806727057384866, 107827339725024, 72640853706976, 72640853706976, 213378409171168, 
    72640853706976, 248702267033824, 494993106536672, 107827339725024, 72640853706976, 143078384470240, 
    16609688878692677949137908935229969316400773306571355212329223839009166021565077768904316336088709573, 2888527492591104447984738066218920660054433177316902026519389009593911020297104037024834979074556211314882353352226474461896545709621690440943549948717318044074984299460550545413514938496724519511807139860244463330784313048501708047016853547004007538079701129759259556680603108635797140923351367564204925374634309702457244270093298052527283369745019426111746307215020766399244928437056233157289023651395062712606451071193768462300164122401274637688576071408662736912614998510793381170649751331142040766377108187238244667974132831896050905010010809101583181517116955513932609751276399178839627906602578016405530378000833125724692797450328256972655200531491265070, 2046288230258875350271964777634457595244189602528683425403302338654554250917964528843847306205446410602565180444523353705122206869768453127094343828197001863691487011157294886, 16609688878692677949138338279066710463816504754277876983814299294819352055719172973109743147960635845, 16609688878692677949137026204288552574168897771999608417219443026929079166217442180477926316381704645, 16609688878692677949137898630964784994782365300888614725482079434985255953055706422670963745390256581, 
    145273112758496, 145273112758496, 431430006213088, 44059960281568, 79246513408480, 44334838188512, 
    9079834020320, 44059960281568, 9080102455776, 286014896081120, 294819847473632, 292773767353874293100052443275407498543558224547322198400233290256346028005355051326540409689372384964, 
    218843822164192, 143009597884640, 143009664993504, 4535624403168, 4535624403168, 286427145373920, 
    285946579060960, 286152737425632, 365422809305641307345055438313253780782538302754, 731110429073477165478236606448207003815974020514, 732180864850997610737350948008808136984825996706, 732180864850997691866989362615489832773831140770, 
    284230269602016, 290829688375776, 365400497777412721816655845559959784234385155874, 281612554602720, 281750127773920, 281750127773920, 
    281750127773920, 286014896081120, 286014896081120, 290554810730976, 290554810730976, 290554676513248, 
    240240771832510474327134544362346117735092369170114308903241134352263946846574067173689483152282982831477572161539729754480256065802099517174707246868972671739025618224232389373349633263406096077897358962170610973947140701867408563012970681868915728768303250373495560, 1676866372978040160745750176076398957697037098257783554157438152996772889515076805764709117628806749711591908571355452620144241800708395740236738668769379923375895013348242530561462543273250099249841061394893608620582906499727406313495027115308962456422320686729467897586441844543747537468265835439433048025624501806239961860972297250114305605862085637784566111436424382523222058, 288147414452448, 294819847473632, 72024525441248, 72024525441248, 
    182699551982443346169681928271572560287822783906, 265750982861125756828414396982106008458777873180850625806372260126224153609647848076518082276576222052, 267827174155503791609610265106048356890496273489495044344773441914639813387057323225769985292649913956, 145273514952928, 293620541632952185633424810848572701148019965629620553186601865447848631365078017462093781962369031492, 490346839950744598838960499198458482868119101080285797142273403494739449058084053232717002276561561270726156952083660183314042778783172472328974258944659464126917639032187402371484073604743211066845837686249783634739285503728121012507780380100169770926604418124598760, 
    1013759487232776840238303359547232881170594255083054663824081867029534849603269365871684139107268, 265751980780621119639965766512248089092003190346959914134773254452388739517160636679915842085065873412, 265751980780621119639965766512248089092003190346959914134773254452388739366750919665462700331446065156, 267861614242116419587613743861396958727759822301872632520087247066536846062600695047550078193977286340, 267861614242116419587613743861396958727759822301872632520087247066536855162388573301323368630722780868, 267861614242116419587613743861396958727759822301872632520087247066536855162388573301323368630722780868, 
    282652075099169, 282858233529377, 282858099320097, 282858233529377, 282652075099169, 145273514952928, 
    730764756684380085771162657736969578509991281059, 286152737294560, 286152737294560, 286152737294560, 286152737425632, 286152737425632, 
    72024525441248, 22858351047123333572125618401376063738079618466, 107208863975648, 72024525441248, 353500777220320, 45694401242704623429275826335243551812037911970, 
    177058420492512, 141977127618784, 423590617024736, 182710702397577907346370004063626769762905236898, 282857998648353, 107208863975648, 
    267859836218979294226255815674783841992371157976059123014675909738731654330664319981473364516694679140, 282858032211233, 282858233529377, 282858233529377, 73121890044128, 143078384470240, 
    72640853706976, 143078384470240, 143078384470240, 45761303733511990506735441748270351814962455970, 73121890044128, 72640853706976, 
    143078384470240, 143078384470240, 143078384470240, 213378409171168, 495061758904544, 213378409171168, 
    213378409171168, 143078384470240, 143078384470240, 730842809579771226543529861293919163208168409507, 66437869465220763316143089532826203076183816469337811173324744278456952072545375273679045457136678821, 72640853706976, 
    72640853706976, 213378409171168, 217845108050144, 72640853706976, 213378409171168, 213378409171168, 
    72640853706976, 145273112758496, 145273246976224, 145273246976224, 145273112758496, 730842809590322014007979188281376629278060349859, 
    81653842577888, 45850507054588401306095793195268362864916178338, 74839876962528, 74839876962528, 145273514952928, 145273515149536, 
    145273045649632, 145273246976224, 74839876962528, 215577432426720, 215577432426720, 215577432426720, 
    356315054999776, 74839876962528, 145273515411680, 145273515411680]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, false⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 5) (a := [1462220837725027692691023284257529965084754339106, 1462934461573717213823874110075857536786866152866, 365735010231459617268013350523274501665040393506, 567906417052128, 576290260388320, 576221540977120, 
    576290260388320, 730753607641019241442657893732616452596327556514, 23192863501175745840095779653551053655664797090, 365733616434895093697784111679921228108804957602, 730753607641019241442348408722795107527602775458, 75325409397216, 
    1461551815368832926123128211632372211198017971618, 1461864025801861586047057333599365914037473289634, 265801654994861121644922141630124364459320159512994962550854097576193227683847684338470048259828735588, 567494167497184, 567494167497184, 1978643329836335140592690686526421833430612537154823769351938224490029921573027795498658007259620032974403815851170687845163022815922939385224941616514041311708185588077975334, 
    567425447823840, 576290260388320, 567425447823840, 567631606450656, 483185126816298234820171351724501363679806337778400351658588127492887094813368914105477460866138203509950085579225274185841126963695137912317470362410844312668365541627686, 123665318701671983413866819025650106695757048883368721278050779362242673695839192960410312099193094027284055744015302392654739690446453136819514226770219446488773512085133094, 
    154353076144608, 1464361709285021973446150602550081826811036591394, 154078197975520, 286157032393184, 83984332032480, 295090564499936, 
    549133572907912476917807655750492275991397295394, 145282105084384, 39660269144544, 145213385411040, 1464356308323294282905195726018535562581583095074, 154078197975520, 
    154078197975520, 145213385411040, 435553174948320, 145419544037856, 154078197975520, 286157032393184, 
    8305731603115938492920571009233281592937514445359178765361604142137423672376025556679918262163820004, 132891703662604395503988265812177299730413842243092909848667136779743517721192021549799693169927084036, 519108241116671371953828409392562191087098537843898660672870875833978280130435413864861852451947460, 519108241116730373346372956322793320320942213263676985642132414049623019096777253089432238477755332, 8305731602636274911227397069121149706749833399645219944371984070122237143096277516602898945847545316, 732538373664486156232808466748909940510525269410, 
    8305731603115896087687664343824449295200507578667502602275450862083353700974380070729893359594458596, 183045224379541785697475676546070231957979571618, 33222925916013647518885782615837792460351229938745275969008544877287232792559873798514047352026699780, 129777054357776070718133912971731955115520846189196740357625803703021495504200890602903288909146757, 132891703662604380758824459938844790636756069145287293468055198095656852389658393923676142199388723204, 1461551815369071773996777212709350514239574926626, 
    1461864025804187743913080395598770415434579092898, 7147416080006916720998194082959912737511613858, 24307904844490680048593705335867891963243570594, 290829688375776, 565707393796576, 567494167366112, 
    567494167366112, 569624471210464, 567494167366112, 732180859417113604374977741262561236913928840610, 81922479163872, 290829688375776, 
    145694019291616, 45638595414496, 81922479163872, 290829688375776, 567494167300576, 567494167300576, 
    567425447823840, 567494167366112, 1461596415859567460007506726231617201245635784098, 184472472082881569544813289498750183585195009442, 91522617634299148217239185473701370208667088290, 732178774156135248332975104006689712163986646434, 
    732180864850997610578894622980277772947877832098, 732180864850997610578894622980279461804180546978, 73126184749536, 145694019291616, 145694019291616, 145694019291616, 
    91522607445766636584895032252979698546961331618, 1978960227047137337937550353967343415532603947628306018436219608623120684340357441179700943772017950447709344586659152250884384758127007497526647879376399765315678000570694694, 732180855333725201323561436754433417429318673826, 365400497777422781967333599184898258839869613858, 732180854653160467481549110062100387803376952738, 732180855333725201323445379875750413028546880930, 
    290829688375776, 73126184749536, 37941812464096, 73126184552928, 73126184552928, 571823494334944, 
    79723590257120, 1982507778792047447813099745238826145080490504249711556737909883741471754512636703052196055499995119954855121625796294150108993923497353534874554900862732293560668894631274279, 265751980781089470530943922150141062749314963993357458917967315101525958649463920281767972972460723684, 150092065802720, 290829688375776, 571892213877216, 
    290829688375776, 571892213811680, 573988191472096, 571892214270432, 149679749204448, 290554810730976, 
    1462930284270039358515993896155942087481690203554, 290554810730976, 290554810730976, 83984264989152, 149817456593376, 149817456593376, 
    149817456593376, 290554810730976, 290554810730976, 290554810730976, 79654870845920, 149817188157920, 
    290554810730976, 83640264952288, 290554810730976, 290554810730976, 83640264952288, 290554810730976, 
    79242553985504, 270472221129415927921911579156950594438578550429103657707254791299989516076583929639303513258759129356635294335097206922302649604203512177390720717714725177785786813103398, 149679749204448, 290554810730976, 92771453940837412314633365073023161840333006242, 149679749204448, 
    149679749204448, 149817456593376, 149679749204448, 508017829743072, 435484388493792, 1461864025804187743912926861876721031607816332706, 
    519108241116671372178928230869904874990520529797123246866659438241363569838654202242598237875946436, 8305731603115896087687664343824449295200507575849072671091620832490372633633906941502580606904782308, 132891703662604380758824459938844790636756069143832619944697580197098093713422138805750173221200812036, 565226424568288, 1978658337233789195929255607019526488043792779762954713959044679902283942670434296828660212279821346688013888397492745555226581813328830571711882571945021641867437027263249446, 480481306159211361205044992421904139309116810276696193309304011708559844123742763904871993587876554234101521370282335971446342873296268559226201403484196634271746517990829774265574312216700297965931268894724361236648758167827448215340857579465691378785198226373494280, 
    567494167497184, 1461551815624449700785402111983664041260455847714, 265751980781089470526216849942372440436434910608999412886021434634381439701790402429365534483858804196, 567494167300576, 567494167759328, 145281702693344, 
    290554810730976, 86252007721440, 154352942057952, 81647668562400, 154215503104480, 290554810730976, 
    290554810730976, 290554676513248, 145281971128800, 145281971128800, 145281971128800, 154215503104480, 
    290554676513248, 290554676513248, 149817188157920, 72645148674528, 290554810730976, 290554810730976, 
    290554810730976, 290554810730976, 145281836911072, 132891703662846066943595453450193440651524550998661831482680274840932285418233723795806143886437603332, 6846376585964146635852517423483800440743159074, 6846376590948770634804955370314099367342531874, 
    6846376585964177059466922900989436361620088098, 789589162433971101954725259937001143280514552194844104488075141645593803005135572043718763759620300308763699522943122408002590564682439471596113594892612396567129484533653700335464229488675716492167044825402460464885244248430197209009722489756401482667663506373494280, 77112250206688, 72645215783392, 147412274907616, 145281836911072, 
    145281836911072, 145281836911072, 217781019085280, 508052155927008, 296945923394016, 789589162433971101954725238201747851064952463496241034993738607821195169472271524499505246570245953376554335627697850238780408735867637334994960547281018430419958739459966767455180783368041274143172931252022302180269885163729666367858571120548455225992683666373494280, 
    508052155927008, 290554810730976, 296945923394016, 294815552506336, 508052155927008, 145281836911072, 
    145281836911072, 145281836911072, 74912958515680, 145281702693344, 154215503104480, 145281702693344, 
    571892146702816, 286514788529236939876521249966844314527623111065295314332003045960315182453498555997011549249396528069, 149955029633504, 567425380714976, 565191964166624, 141021095135712, 
    141021095135712, 281758717708768, 281758717708768, 431430006082016, 37701764254176, 37701764254176, 
    84052917357024, 74844171930080, 281758583491040, 74844171930080, 83777771014624, 75119251163616, 
    74844171930080, 281758986144224, 281758986144224, 290314560735712, 519108240874972279156275694392533670196802110141951485889056845330545911599697703322669849566725060, 154353076144608, 
    295090564499936, 1461864035332094017699212301364224781366791284130, 154353076144608, 1461596426387219338222037653771537851565419834786, 1461596426387717800621932897566220881458079772066, 1461551824896822276975747328752404680587782694306, 
    132932252556490215032027325598086552396264520638510421450137372161824828636941057098893660490864336196, 290348652300768, 41034290039264, 145419141646816, 72851374213600, 81716320930272, 
    154352807840224, 290554810730976, 265751980780847771439849564413872288447942985021105321683443985627022607640947422215195176960042159588, 1461864035330100168099660340515843877338601792930, 290554810730976, 435828052593120, 
    72645148674528, 290554676513248, 72645148674528, 77180701247968, 81716320930272, 72645148674528, 
    290555079166432, 290554810730976, 290554810730976, 435828052593120, 145419544300000, 150091998497248, 
    1013790893067621651452821627234581376713748168999199140399991591803688362280275137618542797737444, 84121300830688, 1978972169482188442710410721212596428335675104344016044271622441051799741202064799170829966027412546478661100605297694992648009345091526460290441697967915593762308546528017446, 281621144537568, 281621144537568, 149679749204448, 
    83640600496608, 3029820533684153960141529059138382891262100527190129406980324166180822762932324685321755637834027023077494799378437253750636746043915620840712063569286873979247073894845117478, 3544291016414190361441758630772792783979870391503066265956795240329787150629867846308316492208637196908557969708524248188825771919409643039540577526514130822874193551770516518, 435690613901792, 145282105084384, 37941812464096, 
    12845278235097714872136777554356777378979512739, 73126184552928, 290417237559776, 8305765022864604554528549968506889025086165026777084293732914850960426063974070226047205080710762884, 519108241116671371953828409392562191087098534940233975676226900835473820935257000218852769661141956, 74912958515680, 
    86252007721440, 145281702693344, 290554810730976, 154353076144608, 183045214851635582899632312352427707683849151906, 154215234669024]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_0 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [5887419192380130516333684469191404243483375010, 39724693719264, 36426158835936, 465453501664267720797795209429916886521042138783559987548995957224517491080502672306412857393191352357, 5753614230702594312420318140803584303657659810, 5798215891240839019172621309036184742553726370, 
    730848384776632031297095723123330080493160925603, 39724693719264, 39724693719264, 39653826693344, 37935370012896]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_1 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 52853902180385, 52853902180385, 52853902180385, 25691166256363432141173746545574496418155472162, 
    52819542442017, 52819542442017, 52819542442017, 52853902213153, 52853937867873, 52853902213153, 
    52853902213153, 52819542442017, 52819542442017, 52819542442017, 231214834006359803346208245375415963971043732898, 52819542442017, 
    231214834006359803346217916597505440267345866146, 1464356840503970992247621354444122707354970498338, 1464356840503970992247621354444122707354970498338, 145206943156448, 8305731486617877442339044042076964185842155957611411085236416249137242974942357004718766996484803684, 1464356840503970992247926003750665593906996454690, 
    8305731386073887209241091207182881895234835296019329943822973658755289299600266351208602024908429796, 1464356840503970992247926003750665593906996454690, 52853902180385, 52853902180385, 52853902180385, 52853937867873, 
    52853902180385, 1464356840503970993515271953528653976281681503522, 1464356840503970993515271953528653976281681503522, 141979275102432, 44264068751649, 6422639122844939304852713745168301801380774307, 
    7136265696773786878438831580175561012090503587, 185542907841761638677980235023983342751391950242, 8563518823446830029792405559545473509992956323, 52819542442017, 52819542442017, 52819542442017, 
    145277809985760, 185542907841761638677980235023983342751391950242, 185542898313855364911510298678060982012368922018, 182733003227852222152585135425329515100939756962, 145277809985760, 145277810116832, 
    145277810116832, 145277810116832, 145277809985760, 149675856496864, 5753614209537413504668113461052719625125626275, 20761861556619841419988321335348821939034818885040434145244181604487793866848005601360605602021328004, 
    519110189698536447370165170891302735150430759346441485194458449221446641370340303729496897655882692, 426898815846880, 145419544037856, 145419544037856]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_2 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 8563540622682844899221214088292641757578405154, 52819575997473, 52819542442017, 52819542442017, 
    88038308907105, 52853902213153, 88038308907105, 39724693719264, 39724693719264, 8563540623679687304198566921318364824436483362, 
    45639534905824]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_3 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨0, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 52853902213153, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52888264051809, 1464356317851190821214091112705485413568987276578, 
    25690643603583261112290615657535837193164563746, 52819578129505, 53060094198817, 48526606668269997706057584976374145528839548322, 1070533978515689484947038003168967104592652373452120565812104042810177802931673445772814486481161316, 1715551911768436610296182157688140210719829796130, 
    551489151990021713864485973180724018285712356224855976990174632590533518393062159921816608934216260, 298483232857638547424267314471374099526436733831483435523444613274900752701970774450017673435935694148, 1601372096331024478892762135605370201907778823458, 52819542442017, 53060060610593, 1532864207102073737914817952229228424280203076898, 
    1464356317830255401686141473557027770695238034722, 1070533963046947539657034285554931905992273121129537942682170538911524362106995149602730463150217700, 1464356317851190821214091112705485413584019662114, 52819578129505, 40003406673313, 44264001635361, 
    52819575997473, 52888297606241, 52888297606241, 52888297606241, 294849918909537079143610232820099897470147181442434694911357181119039023194440440159246677900014935364, 294849918909537079143610232820099897470147181442434694911357181119039023194440440159246677900014935364, 
    2040490908117984763998987327019999519126053333480672013532852457991004951977254914758403485285418981443032860769742947779073537656026481413501370684303911355714876398107622438, 36567487357217, 36567487357217, 11440325949337880977803542714391650557458147234, 35467975729441, 36567487357217, 
    36567487357217, 52819542442017, 52819542442017, 52853902213153, 53060060839969, 53060060839969, 
    44263968079905, 44263968079905, 52819542442017, 52819542442017, 52888331160673, 489288346087263500381072930022711200453851714844168102167696518807840101114483326954844275911938600899755274147157997260455684421097320695695142452121587764103842808404491445392919414239819691539888394365722437461911016498148094744389327841400379515644936338123494280, 
    37460983155041, 25693256951225794466089313685765075635341370658, 185544998536624000923745010902364920642215093666, 185544998536624000923745010902364920642215093666, 465064439786856385438922903408617226965507330293298308673593821066325040407509658290892171739363139268]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_4 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [74908663548128, 81649816046048, 730761990869312137016391977923938253426483397027, 72709640292576, 74908663548128, 74908663548128, 
    74908663548128, 81924626647520, 74908663548128]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_5 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := []) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_6 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [123257008229473, 52819542442017, 52819542442017, 53060060610593, 123257008229473, 123428806921313, 
    88003949168737, 88038308907105, 88038309103713, 74908663548128, 74908663548128, 88038309365857, 
    88244467796065, 74908663548128, 74908663548128, 74908663548128, 45850507054585807702880917995646347990167729570, 74908663548128, 
    22836138690274803194855758005653349975275889954, 519108241116671366551432693936337777404994678301736743761140488753396877440731033818242518924608452, 81924626647520, 81924626647520, 81718468413920]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_7 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨1, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [2061655289281225833874618904457487938326072042592502817932512220643533186752975742597876021849775130457443740324883265785218449796701943915906714460248471939835264817767096102, 266046002711381184379424523688343375107337012571898428582829114572851997698795813095619020666430316324, 1978900314817796389399478764382877701021308138230212120514905411354062441013728170470164995349341902613718897839564142025726922531009995548519268065933546529500798936276791078, 88003949168737, 294849918909537079143610232820099897470147181445344041914719767634489667883388618860262721274210442564, 290697560111706829943434310619952039434819309853098500487021003570256418949922631231122339952805829956, 
    88003915614305, 88038308907105, 266172690962021919697292735851170452031570670506998911488364747222541960292635062053526537193053510980, 77041114810592, 77041114810592, 88003916631137, 
    88072636140641, 68530364305397518190321767670843422602171000226, 72640920815840, 72640920815840, 72640920815840, 79248996436448, 
    79248996436448, 205535602220898081670538502400400015172607419682, 47099359323841281784456365722295680376861886883, 2094595317851095771304483548430715479423313084503385162367402275620346898309409754869224112012809870948264177572128802767364614485127652547518903040339014831685728144798510886, 143078384470240, 143078384470240, 
    46028913688781596734403014864969491939324897699, 149675454236896, 149675454236896, 47099353539041044128502486844931294701508626851, 88038308907105, 2055949058095781387003101637550174258092772887047365449471316915051993713886687537890958022500254443997252848953826280049903039710559079497541438769776584955459947336131672358, 
    88072636107873, 88072636140641, 88072636173409, 88038308972641, 88038309103713, 88072636140641, 
    88038309365857, 294849918909537079143610232820099897470147181445344041914719767634489677434405650118517007836876135748, 205546665480879106932982911363402548978226046370, 143078384470240, 145277407725792, 149675722672352, 
    290697560111706829943434310619952039434819309853098500487021003570256428500939662489376626515471523140, 2136371383162228786594542792296385123352331445452078294165780759759046489946749703306625047958448997, 2112041155725448815469932363044860630960763269127525007077518729194131069846932753309547968323971941, 290554810730976, 290554810730976, 290554810730976, 
    283957740964320, 281758717708768, 290554810730976, 290554810730976, 286156898437600]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_8 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [145277809985760, 730773163054542782734972331078658106105648153507, 143007450400992, 143007450400992, 154219798071776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_9 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [265750982861125756914852728429405599075739489441390583035347204343436207838281403496459041504381409316, 267827178100032633491904496351340897074709294321924903398482821027567087169927339502600300372736121732, 267827178100032633491904496351340897074709294324834250401824238621625343864347874985797384988108299140, 267827178100032633491904496351340897074709294321924903398482821027567087169927339362520337563004214148, 141908408076512, 182699551982448538466540463099196657551389762978, 
    182699551982448538469016343177767488470200624546, 141908408076512, 182699551982448538469016343177767488470200624546, 182699551980117837340611440749838653765571847586, 141908408076512, 182699551982448538466540463099197150132599006626, 
    2061731269759991664846052836663579457891158008231588906808168532526001000591816967998795872890828035730921543526612456082802701383936417609685740054270346868544052105392930086, 1984455585664477028568809030374346478108303835686229062568202306217894670059775830506787279049615971739376194273593796773026813645904403685039925361583291290322969739506203430, 2055949529841084496554073920909042172475589975382329359627253410081576389191794124670587277371312807943559252998395019798331638023967068688474340609513475202503580059488468262, 2055949529841083617859763927192093301712629584714892372184487179095745613156224677602404428316776051888282526109280544383906341135088827637897566365864686625692101957257247526, 145277809985760, 91355351208114354403475324413267069268765213091, 
    145419543841248, 145419544037856, 265750998701117862943223901984317738958324097915146820584408074810103994801838179669143949166488098852, 141908408076512, 177307528530400, 182710702397583099645704418969825638579924641186, 
    141908408076512, 182710702397583099645704418969825638579924641186, 141979275102432, 141979275102432, 274054903178909382097658228604688634568434529698, 1978884747222783456185379191100483388765130552759692159062909161175373963017227322123507368239475599001387279487259153398521750940868570781464215182889323726495553948043161382, 
    177101370296800, 36567892888032, 142120506106145, 142120506106145, 265750974941130352994913394462208287709038552884347990028099816596076612092351486195509153118735603748, 266172738481514013483871839099566530331691939443502937101089678349316317422764283875190163189055445892, 
    2055949087579862832631098460003907426653871721291415115516535196592893381546902092478850002921325882386147011201549551167413145383438508414148098366829192169305976584228814118, 141983335589153, 2055949087579862831343948898729418105095492160187949494169065401623911621819793860273346051292689658797874772330557749958021702110327958749165373232163255472844696070038469926, 141983167815969, 141983167815969, 7507516832302367192652483253244979699790055386976665147800043603409528310921065727677256072511933292263619987216868489598956821832204933392748807857420404339928174482827169814457602913890587914350444222417440471940879423331648569208962534515670342604689408624938761, 
    142120506106145, 142120606769441, 142120606769441, 267827399859917987289356521017186770752455264120738897263678767967937153547806124853532359017360300932, 143007450400992, 213449209022688, 
    143007450400992, 213449209022688, 143007450400992, 143007450400992, 267827399859917987289356521070749930471533447932010199701088550713482336128123462017637188436851547844, 72603239188704, 
    72603239188704, 61847698525019292216490946797538490115393894473320702541477920257723991018837399702550405595137103054667343456125344709446030508543985654392957833217156428537219267577233191, 213377234766048, 213411594504416, 72843757357280, 72843757357280, 
    72603239188704, 143007450400992, 143007450400992, 213449209022688, 143007450400992, 143007450400992, 
    143078384470240, 792306961689388506684453617584087131700937112478872206797726003026398118531135045449497015417409183509011798730569770269769551950173541071002117560537609084280144784040335639428691065734091221444092858515700964714062634176865696775713863198772485135412503174124938760, 213659863747040, 495276574378464, 494932976994784, 495276574378464, 
    494932976994784, 495276574378464, 213384985840096, 72851508431328, 2061745908606541914952150974943445585610870548683565264337434472195226997204009294216098617533775004787195661917929523797012201552314332814577514529394851681947290844438445350, 143007450400992, 
    217778670274784, 143007450400992, 143007450400992, 217783032351200, 217783032351200, 2061745910909984898205864368490382008694135299717469822196240806941287661193336792425361971725779166466454842205510535611105484647799271033404816336134404135870534657792523046, 
    74802262444256, 74802262444256, 23014456837900747337317209065869166747343923106, 215548575615456, 74802262444256, 268348214836466031797398759630235131412040269713719808484087072282594607453891499590257337585869298564, 
    145206943418592, 74802262444256, 2061731240275910219211561607993001517250670233704376903137807578193119270772279968800145127656248359045107191665736498732682649778509968569478218639872264820393408921093520678, 74802262444256, 145206943418592, 145206440102112, 
    145419544300000, 24264000231259053209556543032274940697388787618, 24264000231261649358002735472127415011982718882]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [52819542442017, 52819542442017, 141979275102432, 143078384470240, 145277810378976, 145277810378976, 
    141872974563552, 141872974563552, 141983167815969, 143007450400992, 143007450400992, 154219931896288, 
    184472472080223144155121228887542964962395202978, 154219798071776, 154219529636320, 154219798071776, 154219798071776]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_11 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨2, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [182699573757944794617084688246001841376428828066, 36319858297056, 36560376465632, 36319858297056, 265750982861125756828414396982106008458777873180850625806372260126224144021028388124972502096068762468, 177061641717984, 
    265750982861125756828414396982106008458777873180850625806372260126224153609647704914796093861597829988, 293620581232945847493211593727647236985827085781476059375169064428129716293163798421976042561522917060, 181459688229088, 181459688229088, 142120506106145, 142120606769441, 
    145277809985760, 36319858297056, 36560376465632, 36319858297056, 16644916896610468799500667002392999934239683651223317077601827062003096010959942945736259253586946917, 1978884747222783456185379191100483388765130552673384691782717461892302380442468713923459093698566108550449063898848436970372927397801950722682997536099106467919521425157762854, 
    142120506106145, 266140298178405964661995464641367308297761028640811635586734995548465049601815520976699171409379745476, 1978960226931968659573647587527104413491235024342355099104501753468739598685597348265049992646295083894402286557294304464845045926690584166281956506808100454938914290247118630, 141983167815969, 16609466995054674195244532438047471809325590814198399817917516559413619403642658162805794135925717029, 142120875205921, 
    142120606769441, 149817087500577, 267827399859917987289356521017186770752455264120738897263678767967937143996789093595278068279986396036, 268086922284782377864367516155324933515514546220378553412493992115760363069212496045000632050606185348, 72638706223328, 72844864653536, 
    72638706223328, 213380556654816, 213380623763680, 72638706223328, 72844864653536, 72638706223328, 
    213380556654816, 2060175898774820516892233155551772666500216796965897871287526449776490690232195924813495577515915516601089301561798788542860875643892850465144151339356189684664781156679401254, 2056311361251803258540819578611959834985449549431826431822817976523128155354877815494970937951259838099274546306849413056034945164383895194682292629006012370693679020759826214, 143220017734113, 213380556654816, 217778670274784, 
    145277810116832, 145171509545184, 141020994478369, 145206540765408, 145206540765408, 145171509545184, 
    145419040989601, 145206540765408, 184115676480034064056470313837386905311378941346, 184758223112416, 154215134011809, 219977626421472]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_12 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [290554810730976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_13 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 0, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [33239147552566898678563874142506517370087268623019593213977125988759228976825051697911986692109101701, 480481077044049878458912907417718748290626573045958609004026016343487814498964475572246920704138878351345714889004766477229361986775118360322891423643928200370233848189392646273630503553560544916099481215472632471849438502942329540574338108123095226562642051101894760, 293685469759142831205881779647695335677473993825384518448654942212292009188776358877465152464436108164, 15473246058853430599390408588228780699319226675480632828478765955111084406752071790257495154299415296456242219363195474329066941063883773436010666170862465786745831903942438, 282857998648353, 282857998648353, 
    182733003227852222152585135425329092886864078242, 213517928499424, 22881261642454015615778646946925102013618857250, 213376194578656, 143078384470240, 182733003227852222152585135425333455765646091682, 
    293620597072923317653419513523449053683005999894095278030689724847555044967653697440199218760629902660, 217778670274784, 217778670274784, 503866307643872, 290554810730976, 145277809920224, 
    215575217834208, 215579579910368, 215579647019232, 215579579910368, 497063280773600, 215579647019232, 
    497063280773600, 145277810378976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_14 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, false⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [730753607641019241521576571237059445121146725794, 365556604269871372441303539034119245609224922402, 730753607641019241521576571237059445121146725794, 294819981298144, 294953125284320, 294953125284320, 
    132891703662604380758824459938844790636756098937000607900934604581923060191668923471964677448615024644, 290829688375776, 284234564569568, 290829688375776, 290829688375776, 732180855333725201482017761782962092616406574498, 
    365400497777422781968571539224183639114768738082, 732180855333725201481901704904279088215634781602, 290417237559776, 290554810730976, 290554810730976, 290554810730976, 
    290554810730976, 290829554420192, 290554810730976, 290554810730976, 290554810730976, 132891703662604380758824459938844790636756098935545934377576986683364301515432668354038708470427113476, 
    286023486015968, 290554810730976, 290554810730976, 290554676513248, 296952365844960, 294819847473632, 
    295094859467232, 290554810730976]) (b := []) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b10_15_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, some ⟨3, 1, true⟩⟩ true 104 ⟨3, 129, ⟨3, [], 1, [1]⟩⟩ [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine checkTree_sound (holesLeft := 4) (a := [141979275102432, 72020230473952, 72020230473952, 72020230473952, 182699551982448538483871623649196414632739743138, 141979275102432, 
    45683163715280236269697202798564923492958481826, 183044539728828574733976927207389737759537636642, 181459688229088, 145277809920224, 181459688229088, 282652075099169, 
    282858233529377, 282858099320097, 282858233529377, 282652075099169, 730764756684390470404493808649358808299421696419, 286157032393184, 
    72020230473952, 22858351047118790312374400427201099553791550882, 72020230473952, 72020230473952, 45694401242700729209107805293092914489589247394, 141979275102432, 
    141979275102432, 282857998648353, 109404666038496, 267859836218979294226255815668913906680691357010599455061440022269377831463920149203646336150214427748, 282858032211233, 282857998648353, 
    282858233529377, 282858233529377, 281758487019553, 108305154377952, 73119742560480, 143078384470240, 
    213380556654816, 143078384470240, 213380623763680, 143078384470240, 45761303733508096269236260156124390643926052258, 108305154377952, 
    73119742560480, 72638706223328, 143078384470240, 213380623763680, 495070617274848, 213380556654816, 
    143078384470240, 424699390069216, 143078384470240, 730842809579781611176861012206308392997598824867, 72638706223328, 72638706223328, 
    217778670274784, 217915975010528, 72638706223328, 217778670274784, 213380556654816, 72638706223328, 
    730842809590332398641310339193765859067490765219, 81640957675744, 145277809920224, 45850507054584507088403652231688486092265762210, 74837729478880, 74837729478880, 
    215579647019232, 215579579910368, 215579647019232, 74837729478880, 145277810378976, 145277809920224, 
    145277810116832, 180360176601312, 74837729478880, 145277340616928, 145277541943520, 74837729478880, 
    215579647019232, 215579579910368, 74837729478880, 145277810378976]) (b := []) (by decide) ?_
  decide +kernel

private theorem tv_b10_15 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, some ⟨3, 1, true⟩, none, none, none⟩ true 105 ⟨2, 130, ⟨2, [1], 0, []⟩⟩ [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := ⟨3, 129, ⟨3, [], 1, [1]⟩⟩) (prev' := [⟨2, 130, ⟨2, [1], 0, []⟩⟩, ⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

private theorem tv_b10 : TreeValid ⟨some ⟨1, 0, false⟩, none, some ⟨2, 1, false⟩, none, none, none, none, none⟩ true 106 ⟨1, 129, ⟨1, [], 0, []⟩⟩ [⟨0, 128, ⟨0, [], 0, []⟩⟩] := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := ⟨2, 130, ⟨2, [1], 0, []⟩⟩) (prev' := [⟨1, 129, ⟨1, [], 0, []⟩⟩, ⟨0, 128, ⟨0, [], 0, []⟩⟩]) rfl ?_
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

def baseTable : Table := Table.empty.set 0 0 ⟨1, 0, false⟩
def h0 : HistItem := ⟨0, 128, startPos⟩
def h1 : HistItem := ⟨1, 129, startPos.move ⟨1, 0, false⟩⟩

theorem step_proof : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1.H3 := by
  intro M hFirst hM10 hRun _hUsed hForm hMissing hLoop hHalts
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
  let m : Move := ⟨2, 1, false⟩
  have hm_cmd : M 1 0 = m.command := hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  exact tv_b10 M hG hm1 rfl hv (by simp)

end OMA.BB4H1

-- Step BusyBeaver.BB_4.R1.H2.R1.H1.R1.H3.R1.H2.R1.H3
-- Credit: @pageman (adaptation); certificates from @ubuwaits / @hyprspacecoyote
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1.H3 :=
  OMA.BB4H1.step_proof
