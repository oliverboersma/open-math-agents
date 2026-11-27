import OMAReductions.R_BusyBeaver_BB_4_R2_H1_R1

/-!
# Four-state busy-beaver first-write-zero, write-one/left second move

Assembly, bitset inclusion, compact DFA synthesis, and untrusted guidance generation:
Hanan Beer (@hananzlt).
Guided recurrence checker and soundness proof: Chad Mazzola (@ubuwaits), PRs5662/5666.
The finite-automata verifier,canonical enumeration,and all branch certificates are
by Nick Graham (@hyprspacecoyote),PRs 4446,4593,4739,4798,and 4895.
The R2 reduction is by @henry10101001. It preserves @steveDOTdigital's witness
and finite-alphabet normalization and @Halldon's first-transition symmetry.
The H2 reduction is by @hyprspacecoyote and reuses @marcusbuffett's proofs
of the two exceptional machines; those sweep proofs are also retained here.
No claim of a new mathematical discovery or exclusive priority is made.
-/

/-
A machine running past step 107 determines a partial table: keep exactly the
instructions it reads in the first 107 steps. It suffices to certify that
these partial tables run forever. A leaf with a repeatable segment of at
most 107 steps can be discarded,even when the head drifts and leaves a
different tape behind it. The free tail in the hypotheses describes this
unobserved portion of the tape.

H3 isolates the two published RepWL cases (the BB4 enumeration of Coq-BB5).
Each list gives A0,A1,...,D1,with 16 for an undefined instruction and
4 * nextState + 2 * writtenBit + left for a running instruction.

The witness and finite-alphabet normalization are from @steveDOTdigital.
The first-move symmetry and immediate cases are from @Halldon.
-/
-- Credit: @henry10101001


/-
Split `BusyBeaver.BB_4.R2.H2` (`M 0 0 = 1RB`,excluding the two RepWL machines) into four
sub-cases by the canonicalized second transition `M 1 0`:
- `H1`: `M 1 0` transitions to state `0` or `1`
- `H2`: `M 1 0` transitions to `(2,0,R)` or `(2,0,L)`
- `H3`: `M 1 0 = (2,1,R)`
- `H4`: `M 1 0 = (2,1,L)`

States `2` and `3` are symmetric when `M 0 0 = 1RB`,so any `M` with `M 1 0` targeting state `3`
is normalized via swapping states `2 ↔ 3`. The swapped copies of the two exceptional RepWL
machines are discharged directly using the sweep invariant from `BusyBeaver.BB_4.R2.H3`
(credited to @marcusbuffett).
-/
-- Credit: @hyprspacecoyote

namespace OMA.BB4Common

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

def Table.empty : Table := ⟨none,none,none,none,none,none,none,none⟩

def Table.get (tb : Table) (q : State) (a : Symbol) : Option Move :=
  match q.val,a.val with
  | 0,0 => tb.t00
  | 0,_ => tb.t01
  | 1,0 => tb.t10
  | 1,_ => tb.t11
  | 2,0 => tb.t20
  | 2,_ => tb.t21
  | _,0 => tb.t30
  | _,_ => tb.t31

def Table.set (tb : Table) (q : State) (a : Symbol) (m : Move) : Table :=
  match q.val,a.val with
  | 0,0 => { tb with t00 := some m }
  | 0,_ => { tb with t01 := some m }
  | 1,0 => { tb with t10 := some m }
  | 1,_ => { tb with t11 := some m }
  | 2,0 => { tb with t20 := some m }
  | 2,_ => { tb with t21 := some m }
  | _,0 => { tb with t30 := some m }
  | _,_ => { tb with t31 := some m }

def Move.flip (m : Move) : Move := { m with left := !m.left }

def Table.flip (tb : Table) : Table :=
  ⟨tb.t00.map Move.flip,tb.t01.map Move.flip,
   tb.t10.map Move.flip,tb.t11.map Move.flip,
   tb.t20.map Move.flip,tb.t21.map Move.flip,
   tb.t30.map Move.flip,tb.t31.map Move.flip⟩

theorem Table.get_set_self (tb : Table) (q : State) (a : Symbol) (m : Move) :
    (tb.set q a m).get q a = some m := by
  fin_cases q <;> fin_cases a <;> rfl

theorem Table.get_set_ne (tb : Table) {q q' : State} {a a' : Symbol} (m : Move)
    (h : (q',a') ≠ (q,a)) : (tb.set q a m).get q' a' = tb.get q' a' := by
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

def startPos : Position := ⟨0,[],0,[]⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  match a.val,xs with
  | 0,[] => []
  | _,xs => a :: xs

def symHead : List Symbol → Symbol
  | [] => 0
  | x :: _ => x

theorem symHead_eq_headI (xs : List Symbol) : symHead xs = xs.headI := by
  cases xs <;> rfl

def listEq : List Symbol → List Symbol → Bool
  | [],[] => true
  | x :: xs,y :: ys => Nat.beq x.val y.val && listEq xs ys
  | _,_ => false

theorem listEq_eq_true {xs ys : List Symbol} (h : listEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => rfl | cons _ _ => simp [listEq] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [listEq] at h
    | cons y ys =>
      simp only [listEq,Bool.and_eq_true] at h
      rw [Fin.ext (Nat.eq_of_beq_eq_true h.1),ih h.2]

def Position.move (c : Position) (m : Move) : Position :=
  if m.left then ⟨m.state,c.ls.tail,symHead c.ls,push m.write c.rs⟩
  else ⟨m.state,push m.write c.ls,symHead c.rs,c.rs.tail⟩

def Position.flip (c : Position) : Position := ⟨c.state,c.rs,c.head,c.ls⟩

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
  ⟨some c.state,⟨c.head,ListBlank.mk c.ls,ListBlank.mk c.rs⟩⟩

theorem view_start : startPos.view = Machine.init [] := rfl

def Move.command (m : Move) : Option (Option State × Stmt Symbol) :=
  some (some m.state,Stmt.write m.write (if m.left then Dir.left else Dir.right))

def Matches (M : Machine4) (tb : Table) : Prop :=
  ∀ q a m,tb.get q a = some m → M q a = m.command

theorem matches_set {M : Machine4} {tb : Table} {q : State} {a : Symbol} {m : Move}
    (hm : Matches M tb) (h : M q a = m.command) : Matches M (tb.set q a m) := by
  intro q' a' m' hh
  by_cases e : (q',a') = (q,a)
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩
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
    cases d <;> simp [Position.view,Machine.step,he,Move.command,Position.move,
      Tape.write,Tape.move,mk_push,symHead_eq_headI]

theorem multi_succ_front (M : Machine4) (c : Cfg Symbol State) (k : ℕ) :
    M.multiStep c (k + 1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ,ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

-- ============================================================
-- Guarded repeatable-segment checker
-- ============================================================

def takePad : ℕ → List Symbol → List Symbol
  | 0,_ => []
  | k + 1,[] => 0 :: takePad k []
  | k + 1,x :: xs => x :: takePad k xs

theorem takePad_foldr_drop (k : ℕ) (xs : List Symbol) :
    (takePad k xs).foldr ListBlank.cons (ListBlank.mk (xs.drop k)) = ListBlank.mk xs := by
  induction k generalizing xs with
  | zero => simp [takePad]
  | succ k ih =>
    cases xs with
    | nil =>
      simp only [takePad,List.foldr_cons,List.drop_nil]
      have h0 := ih []
      simp only [List.drop_nil] at h0
      rw [h0]
      exact ListBlank.cons_head_tail (ListBlank.mk [])
    | cons x xs =>
      simp only [takePad,List.foldr_cons,List.drop_succ_cons]
      rw [ih xs,ListBlank.cons_mk]

def runGuardedLeft (tb : Table) : ℕ → State → Symbol → List Symbol → List Symbol →
    Option (State × Symbol × List Symbol × List Symbol)
  | 0,q,a,near,rs => some (q,a,near,rs)
  | k + 1,q,a,near,rs =>
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
  | some (q',a',near',rs') =>
    Nat.beq q'.val q.val && Nat.beq a'.val a.val && listEq rs' rs &&
      listEq (near'.take near.length) near && Nat.ble near.length near'.length

theorem runGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near rs : List Symbol)
    {q' : State} {a' : Symbol} {near' rs' : List Symbol}
    (h : runGuardedLeft tb p q a near rs = some (q',a',near',rs'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q,⟨a,near.foldr ListBlank.cons tail,ListBlank.mk rs⟩⟩ p =
      some ⟨some q',⟨a',near'.foldr ListBlank.cons tail,ListBlank.mk rs'⟩⟩ := by
  induction p generalizing q a near rs with
  | zero =>
    simp only [runGuardedLeft,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
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
        simp only [hd,↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q,⟨a,(x :: xs).foldr ListBlank.cons tail,ListBlank.mk rs⟩⟩ =
              some ⟨some m.state,⟨x,xs.foldr ListBlank.cons tail,ListBlank.mk (push m.write rs)⟩⟩ := by
            simp [Machine.step,hM,Move.command,hd,Tape.write,Tape.move,mk_push]
          rw [hstep,Option.bind_some]
          exact ih m.state x xs (push m.write rs) h
      | false =>
        simp only [hd,Bool.false_eq_true,↓reduceIte] at h
        have hstep : M.step ⟨some q,⟨a,near.foldr ListBlank.cons tail,ListBlank.mk rs⟩⟩ =
            some ⟨some m.state,⟨symHead rs,(m.write :: near).foldr ListBlank.cons tail,ListBlank.mk rs.tail⟩⟩ := by
          simp [Machine.step,hM,Move.command,hd,Tape.write,Tape.move,symHead_eq_headI]
        rw [hstep,Option.bind_some]
        exact ih m.state (symHead rs) (m.write :: near) rs.tail h

theorem runGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (p : ℕ) (q : State) (a : Symbol) (near ls : List Symbol)
    {q' : State} {a' : Symbol} {near' ls' : List Symbol}
    (h : runGuardedLeft tb.flip p q a near ls = some (q',a',near',ls'))
    (tail : ListBlank Symbol) :
    M.multiStep ⟨some q,⟨a,ListBlank.mk ls,near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q',⟨a',ListBlank.mk ls',near'.foldr ListBlank.cons tail⟩⟩ := by
  induction p generalizing q a near ls with
  | zero =>
    simp only [runGuardedLeft,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl,rfl⟩
    rfl
  | succ p ih =>
    simp only [runGuardedLeft] at h
    rw [Table.get_flip] at h
    cases ht : tb.get q a with
    | none => simp [ht] at h
    | some m =>
      simp only [ht,Option.map_some] at h
      have hM := hm q a m ht
      rw [multi_succ_front]
      cases hd : m.left with
      | false =>
        simp only [Move.flip,hd,Bool.not_false,↓reduceIte] at h
        cases near with
        | nil => simp at h
        | cons x xs =>
          simp only at h
          have hstep : M.step ⟨some q,⟨a,ListBlank.mk ls,(x :: xs).foldr ListBlank.cons tail⟩⟩ =
              some ⟨some m.state,⟨x,ListBlank.mk (push m.write ls),xs.foldr ListBlank.cons tail⟩⟩ := by
            simp [Machine.step,hM,Move.command,hd,Tape.write,Tape.move,mk_push]
          rw [hstep,Option.bind_some]
          exact ih m.state x xs (push m.write ls) h
      | true =>
        simp only [Move.flip,hd,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h
        have hstep : M.step ⟨some q,⟨a,ListBlank.mk ls,near.foldr ListBlank.cons tail⟩⟩ =
            some ⟨some m.state,⟨symHead ls,ListBlank.mk ls.tail,(m.write :: near).foldr ListBlank.cons tail⟩⟩ := by
          simp [Machine.step,hM,Move.command,hd,Tape.write,Tape.move,symHead_eq_headI]
        rw [hstep,Option.bind_some]
        exact ih m.state (symHead ls) (m.write :: near) ls.tail h

theorem foldr_append (xs ys : List Symbol) (tail : ListBlank Symbol) :
    (xs ++ ys).foldr ListBlank.cons tail = xs.foldr ListBlank.cons (ys.foldr ListBlank.cons tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem checkGuardedLeft_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near rs : List Symbol}
    (h : checkGuardedLeft tb p q a near rs = true) (tail : ListBlank Symbol) :
    ∃ tail',M.multiStep ⟨some q,⟨a,near.foldr ListBlank.cons tail,ListBlank.mk rs⟩⟩ p =
      some ⟨some q,⟨a,near.foldr ListBlank.cons tail',ListBlank.mk rs⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb p q a near rs with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q',a',near',rs'⟩
    simp only [hr,Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq,ha⟩,hrs⟩,htake⟩,_⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hrs' : rs' = rs := listEq_eq_true hrs
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hrs'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail,?_⟩
    rw [runGuardedLeft_sound hm p q' a' near rs' hr tail]
    congr 3
    rw [← foldr_append]
    congr 1
    conv_lhs => rw [← List.take_append_drop near.length near']
    rw [htake']

theorem checkGuardedRight_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    {p : ℕ} {q : State} {a : Symbol} {near ls : List Symbol}
    (h : checkGuardedLeft tb.flip p q a near ls = true) (tail : ListBlank Symbol) :
    ∃ tail',M.multiStep ⟨some q,⟨a,ListBlank.mk ls,near.foldr ListBlank.cons tail⟩⟩ p =
      some ⟨some q,⟨a,ListBlank.mk ls,near.foldr ListBlank.cons tail'⟩⟩ := by
  unfold checkGuardedLeft at h
  cases hr : runGuardedLeft tb.flip p q a near ls with
  | none => simp [hr] at h
  | some res =>
    rcases res with ⟨q',a',near',ls'⟩
    simp only [hr,Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hq,ha⟩,hls⟩,htake⟩,_⟩ := h
    have hq' : q' = q := Fin.ext (Nat.eq_of_beq_eq_true hq)
    have ha' : a' = a := Fin.ext (Nat.eq_of_beq_eq_true ha)
    have hls' : ls' = ls := listEq_eq_true hls
    have htake' : near'.take near.length = near := listEq_eq_true htake
    subst hq'; subst ha'; subst hls'
    refine ⟨(near'.drop near.length).foldr ListBlank.cons tail,?_⟩
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
  ∀ h ∈ hist,h.step ≤ 107 ∧ M.multiStep (Machine.init []) h.step = some h.c.view

def NoRepeatHyp (M : Machine4) : Prop :=
  ∀ (i p : ℕ) (q : State) (a : Symbol) (side : Bool)
      (near : List Symbol) (fixed : ListBlank Symbol),0 < p → i + p ≤ 107 →
    let cfg := fun tail : ListBlank Symbol =>
      let free := near.foldr ListBlank.cons tail
      (⟨some q,if side then ⟨a,free,fixed⟩ else ⟨a,fixed,free⟩⟩ : Cfg Symbol State)
    (∃ tail,M.multiStep (Machine.init []) i = some (cfg tail)) →
    ¬ ∀ tail,∃ tail',M.multiStep (cfg tail) p = some (cfg tail')

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
    · simp only [hcond,↓reduceIte] at h
      simp only [Bool.and_eq_true,Nat.ble_eq] at hcond
      have ⟨hstep_hi,hrun_hi⟩ := hvalid hi (List.mem_cons_self ..)
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
              ⟨ListBlank.mk (hi.c.ls.drop (hi.pos - minp')),by
                simpa [Position.view,takePad_foldr_drop] using hrun_hi⟩
              (checkGuardedLeft_sound hm hleft)
          · contradiction
        · contradiction
      · simp only [hleft,Bool.false_eq_true,↓reduceIte] at h
        by_cases hright : (if Nat.ble cur.pos hi.pos && listEq hi.c.ls cur.c.ls then
            if listEq (takePad (maxp' - hi.pos) cur.c.rs) (takePad (maxp' - hi.pos) hi.c.rs) then
              checkGuardedLeft tb.flip (cur.step - hi.step) hi.c.state hi.c.head (takePad (maxp' - hi.pos) hi.c.rs) hi.c.ls
            else false else false) = true
        · split at hright
          · split at hright
            · exact hLoop hi.step (cur.step - hi.step) hi.c.state hi.c.head false
                (takePad (maxp' - hi.pos) hi.c.rs) (ListBlank.mk hi.c.ls)
                hp_pos hp_le
                ⟨ListBlank.mk (hi.c.rs.drop (maxp' - hi.pos)),by
                  simpa [Position.view,takePad_foldr_drop] using hrun_hi⟩
                (checkGuardedRight_sound hm hright)
            · contradiction
          · contradiction
        · simp only [hright,Bool.false_eq_true,↓reduceIte] at h
          exact ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
    · simp only [hcond,Bool.false_eq_true,↓reduceIte] at h
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
  | missing h => exact .missing (by simpa [Position.flip,Table.get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get c.state c.head = some m.flip
      simp [Table.get_flip,h]
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
      rw [multi_succ_front,step_move hm c m h,Option.bind_some]
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
  | some (q,l) => q.val * cert.dfa.size + l.val

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
  rcases q with _ | ⟨q,l⟩
  · simp [nodeId]
  · have hq : q.val ≤ 3 := Nat.le_of_lt_succ q.isLt
    have hl : l.val < cert.dfa.size := l.isLt
    have hne : 4 * cert.dfa.size ≠ q.val * cert.dfa.size + l.val := by
      have : q.val * cert.dfa.size ≤ 3 * cert.dfa.size := Nat.mul_le_mul_right _ hq
      omega
    simp [nodeId,hne]

def Certificate.onBlank (cert : Certificate) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (val : ℕ) : Certificate :=
  let extra := val / 2 % 32
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 64 / dfaBase
  let width := 4 * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1,⟨extra,val / 64 % dfaBase⟩,payload / initialBase,payload % initialBase⟩

def nodes (cert : Certificate) : List (Node cert) :=
  none :: (List.finRange 4).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q,l)

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

theorem allNodes {cert : Certificate} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q,l⟩ <;> simp [nodes]

theorem bitSubset_sound {a b k : ℕ} (h : (a &&& b == a) = true)
    (ha : a.testBit k = true) : b.testBit k = true := by
  have hab : a &&& b = a := by simpa only [Nat.beq_eq_true_eq] using h
  have heq := congrArg (fun n : ℕ => n.testBit k) hab
  simpa only [Nat.testBit_and,ha,Bool.true_and] using heq

def checkBlank (cert : Certificate) : Bool :=
  cert.onBlank (some (0,0)) && !cert.onBlank none &&
    (nodes cert).all fun p =>
      if cert.onBlank p then
        let row := cert.edgeRow p 0
        (row &&& cert.blankReach) == row
      else true

def checkAt (tb : Table) (cert : Certificate) (q : State) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q,l)
  let pRow := cert.edgeRow p a
  match tb.get q a with
  | none => pRow.testBit (4 * cert.dfa.size)
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if Nat.beq (cert.dfa.next a' l').val l.val then
          let sRow := cert.edgeRow (some (m.state,l')) a'
          (nodes cert).all fun s =>
            if sRow.testBit (nodeId cert s) then
              let swRow := cert.edgeRow s m.write
              (swRow &&& pRow) == swRow
            else true
        else true
    else pRow.testBit (nodeId cert (some (m.state,cert.dfa.next m.write l)))

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
    (h : Reads cert p (xs.cons a)) : ∃ q,cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none,by simp [edge_none],.done _⟩
  | step he hr => exact ⟨_,by simpa using he,by simpa using hr⟩

theorem no_read_blank {cert : Certificate} (hb : checkBlank cert = true) :
    ¬ Reads cert (some (0,0)) (ListBlank.mk []) := by
  simp only [checkBlank,Bool.and_eq_true_iff,Bool.not_eq_true_eq_eq_false] at hb
  obtain ⟨⟨hstart,hsink⟩,hclosure⟩ := hb
  have each {p : Node cert} {t : ListBlank Symbol} (hr : Reads cert p t) :
      t = ListBlank.mk [] → cert.onBlank p = true → False := by
    induction hr with
    | done _ => intro _ hp; exact Bool.noConfusion (hp.symm.trans hsink)
    | @step p q t he _ ih =>
      rintro rfl hp
      have ht := allNodes hclosure p
      simp only [hp,if_true] at ht
      have he0 : (cert.edgeRow p 0).testBit (nodeId cert q) = true := he
      exact ih rfl (bitSubset_sound ht he0)
  exact fun hr => each hr rfl hstart

theorem reads_of_canStop {tb : Table} {cert : Certificate} (hchk : checkMachine tb cert = true)
    {c : Position} (hs : CanStop tb c) :
    Reads cert (some (c.state,cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt,hh] at h
    exact Reads.push (show cert.edge (some (c.state,cert.dfa.read c.ls)) c.head none = true from h) (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    simp only [checkAt,hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state,cert.dfa.read c.ls)) c.head
          (some (m.state,cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd,Certificate.edge] using h
      refine Reads.push hstep ?_
      simpa [Position.move,hd,TapeDFA.read_push,symHead_eq_headI,← ListBlank.head_mk,← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state,cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move,hd,mk_push,symHead_eq_headI] using ih
      obtain ⟨s,he,hr⟩ := Reads.pop hr
      obtain ⟨t,hf,ht⟩ := Reads.pop hr
      simp only [hd,if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      have hbeq : Nat.beq (cert.dfa.next c.ls.headI (cert.dfa.read c.ls.tail)).val (cert.dfa.read c.ls).val = true := by
        simp [TapeDFA.read_pop]
      simp only [hbeq,if_true] at h'
      have h'' := allNodes h' s
      have he' : (cert.edgeRow (some (m.state,cert.dfa.read c.ls.tail)) c.ls.headI).testBit (nodeId cert s) = true := he
      simp only [he',if_true] at h''
      have hf' : (cert.edgeRow s m.write).testBit (nodeId cert t) = true := hf
      exact Reads.push (bitSubset_sound h'' hf') ht

-- The synthesized relation is untrusted until checkBlank/checkMachine accept it.
-- Hanan Beer (@hananzlt), using Nick Graham's finite-automaton certificate interface.
def farRow (D : TapeDFA) (e p a : ℕ) : ℕ :=
  if p = 4 * D.size then 2 ^ (4 * D.size)
  else (e >>> ((2 * p + a) * (4 * D.size + 1))) &&& (2 ^ (4 * D.size + 1) - 1)

def farAdd (D : TapeDFA) (e p a row : ℕ) : ℕ :=
  e ||| (row <<< ((2 * p + a) * (4 * D.size + 1)))

def farSeed (D : TapeDFA) (tb : Table) : ℕ :=
  (List.finRange 4).foldl (fun e q =>
    (List.finRange 2).foldl (fun e a =>
      (List.finRange D.size).foldl (fun e i =>
        match tb.get q a with
        | none => farAdd D e (q.val * D.size + i.val) a.val (2 ^ (4 * D.size))
        | some m => if m.left then e else
          farAdd D e (q.val * D.size + i.val) a.val
            (2 ^ (m.state.val * D.size + (D.next m.write i).val))) e) e) 0

def farFollow (D : TapeDFA) (e row a : ℕ) : ℕ :=
  (List.range (4 * D.size + 1)).foldl
    (fun r z => if row.testBit z then r ||| farRow D e z a else r) 0

def farPass (D : TapeDFA) (tb : Table) (e : ℕ) : ℕ :=
  (List.finRange 4).foldl (fun e q =>
    (List.finRange 2).foldl (fun e a =>
      match tb.get q a with
      | none => e
      | some m => if m.left then
          (List.finRange D.size).foldl (fun e i =>
            (List.finRange 2).foldl (fun e s =>
              let r := farRow D e (m.state.val * D.size + i.val) s.val
              farAdd D e (q.val * D.size + (D.next s i).val) a.val
                (farFollow D e r m.write.val)) e) e
        else e) e) e

def farSaturate (D : TapeDFA) (tb : Table) : ℕ → ℕ → ℕ
  | 0, e => e
  | k + 1, e =>
    let next := farPass D tb e
    if next = e then e else farSaturate D tb k next

def farReach (D : TapeDFA) (e : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | k + 1, r =>
    let next := r ||| farFollow D e r 0
    if next = r then r else farReach D e k next

def synthCertificate (tb : Table) (tag : ℕ) : Certificate :=
  let base := unpack (tag - 1)
  let D := base.dfa
  let T := if base.mirror then tb.flip else tb
  let width := 4 * D.size + 1
  let e := farSaturate D T (2 * width * width) (farSeed D T)
  ⟨base.mirror, D, e, farReach D e width 1⟩

def checkCertificate (tb : Table) (val : ℕ) : Bool :=
  let C := synthCertificate tb val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

theorem certificate_sound {tb : Table} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb startPos := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb,hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip,startPos,TapeDFA.read,List.foldr_nil,blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [startPos,TapeDFA.read,List.foldr_nil,blank] using (reads_of_canStop hm hs)

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
  fun q a => (M (swap23 q) a).map fun (s,b) => (s.map swap23,b)

def mapCfg23 (c : Cfg Symbol State) : Cfg Symbol State :=
  ⟨c.q.map swap23,c.tape⟩

theorem reindex23_step (M : Machine4) (c : Cfg Symbol State) :
    (reindex23 M).step (mapCfg23 c) = (M.step c).map mapCfg23 := by
  obtain ⟨q,t⟩ := c
  cases q with
  | none => rfl
  | some q =>
    simp only [Machine.step,mapCfg23,Option.map_some,reindex23]
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
    rw [Machine.multiStep_succ,Machine.multiStep_succ,ih]
    cases M.multiStep c k with
    | none => rfl
    | some c' => exact reindex23_step M c'

theorem mapCfg23_init : mapCfg23 (Machine.init []) = Machine.init [] := by
  simp [mapCfg23,Machine.init,swap23_0]


def sp0Table : Table :=
  ⟨some ⟨1,1,false⟩,some ⟨0,1,true⟩,some ⟨0,1,true⟩,some ⟨2,0,false⟩,
   some ⟨3,1,true⟩,some ⟨2,1,false⟩,none,some ⟨0,0,true⟩⟩

def sp1Table : Table :=
  ⟨some ⟨1,1,false⟩,some ⟨1,0,false⟩,some ⟨2,1,true⟩,some ⟨1,1,false⟩,
   none,some ⟨3,0,true⟩,some ⟨0,1,false⟩,some ⟨3,1,true⟩⟩

def m0Table : Table :=
  ⟨some ⟨1,1,false⟩,some ⟨2,0,true⟩,some ⟨2,1,false⟩,some ⟨3,1,false⟩,
   some ⟨0,1,true⟩,some ⟨1,0,false⟩,some ⟨0,1,false⟩,none⟩

def tblOfList (entries : List ℕ) : Machine4 := fun q a =>
  let v := entries[2*q.val+a.val]?.getD 16
  if v = 16 then none else some (some ⟨v / 4 % 4,Nat.mod_lt _ (by decide)⟩,
    Stmt.write ⟨v / 2 % 2,Nat.mod_lt _ (by decide)⟩ (if v % 2 = 0 then Dir.right else Dir.left))

theorem eq_sp0_of_matches {M : Machine4} (hm : Matches M sp0Table) (hMiss : ∃ q a,M q a = none) :
    M = tblOfList [6,3,3,8,15,10,16,1] := by
  obtain ⟨qm,am,hMmiss⟩ := hMiss
  have hqm : qm = 3 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 0 = none at hMmiss; rw [hm 2 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl,rfl⟩
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl,rfl⟩
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

theorem eq_sp1_of_matches {M : Machine4} (hm : Matches M sp1Table) (hMiss : ∃ q a,M q a = none) :
    M = tblOfList [6,4,11,6,16,13,2,15] := by
  obtain ⟨qm,am,hMmiss⟩ := hMiss
  have hqm : qm = 2 ∧ am = 0 := by
    fin_cases qm <;> fin_cases am
    · exfalso; change M 0 0 = none at hMmiss; rw [hm 0 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 0 1 = none at hMmiss; rw [hm 0 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 0 = none at hMmiss; rw [hm 1 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 1 1 = none at hMmiss; rw [hm 1 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exact ⟨rfl,rfl⟩
    · exfalso; change M 2 1 = none at hMmiss; rw [hm 2 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 0 = none at hMmiss; rw [hm 3 0 _ rfl] at hMmiss; simp [Move.command] at hMmiss
    · exfalso; change M 3 1 = none at hMmiss; rw [hm 3 1 _ rfl] at hMmiss; simp [Move.command] at hMmiss
  rcases hqm with ⟨rfl,rfl⟩
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
  | 0,c => some c
  | k + 1,c =>
    match tb.get c.state c.head with
    | none => none
    | some m => runPos tb k (c.move m)

theorem runPos_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (k : ℕ) (c : Position) {c' : Position} (h : runPos tb k c = some c') :
    M.multiStep c.view k = some c'.view := by
  induction k generalizing c with
  | zero =>
    simp only [runPos,Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    simp only [runPos] at h
    cases ht : tb.get c.state c.head with
    | none => simp [ht] at h
    | some m =>
      simp only [ht] at h
      rw [multi_succ_front,step_move hm c m ht,Option.bind_some]
      exact ih (c.move m) h

theorem run_add (M : Machine4) (x : Cfg Symbol State) (m n : ℕ) :
    M.multiStep x (m + n) = (M.multiStep x m).bind (fun y => M.multiStep y n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ,Machine.multiStep_succ,ih]
    cases M.multiStep x m <;> simp

theorem m0_not_halting {M : Machine4} (hm : Matches M m0Table) (hHalts : M.IsHalting) : False := by
  have h85 : ∃ c85,runPos m0Table 85 startPos = some c85 ∧
      checkGuardedLeft m0Table.flip 29 c85.state c85.head [] c85.ls = true := by
    refine ⟨(runPos m0Table 85 startPos).getD startPos,?_,?_⟩ <;> decide +kernel
  obtain ⟨c85,hrun,hcyc⟩ := h85
  have hM85 : M.multiStep (Machine.init []) 85 = some c85.view := runPos_sound hm 85 startPos hrun
  let cfg (tail : ListBlank Symbol) : Cfg Symbol State :=
    ⟨some c85.state,⟨c85.head,ListBlank.mk c85.ls,tail⟩⟩
  have hEnter : ∃ tail,M.multiStep (Machine.init []) 85 = some (cfg tail) :=
    ⟨ListBlank.mk c85.rs,hM85⟩
  have hStep : ∀ tail,∃ tail',M.multiStep (cfg tail) 29 = some (cfg tail') := by
    intro tail
    simpa [cfg] using checkGuardedRight_sound hm hcyc tail
  have hRec (m : ℕ) : ∃ tail,M.multiStep (Machine.init []) (85 + 29 * m) = some (cfg tail) := by
    induction m with
    | zero => simpa using hEnter
    | succ m ih =>
      obtain ⟨t,ht⟩ := ih
      obtain ⟨t',ht'⟩ := hStep t
      refine ⟨t',?_⟩
      rw [Nat.mul_succ,← Nat.add_assoc,run_add M _ (85 + 29 * m) 29,ht]
      exact ht'
  obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
  obtain ⟨t,ht⟩ := hRec (k + 1)
  have hnone := Machine.multiStep_eq_none_mono hk (by omega : k + 1 ≤ 85 + 29 * (k + 1))
  rw [ht] at hnone
  contradiction

def GoodMachine (M : Machine4) : Prop :=
  (∃ q t,M.multiStep (Machine.init []) 107 = some ⟨some q,t⟩) ∧
  (∀ q a,M q a = none ∨ ∃ q' z,M q a = some (some q',z)) ∧
  (∃ q a,M q a = none) ∧
  NoRepeatHyp M ∧
  M.IsHalting ∧
  (M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1]) ∧
  (M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15])

theorem reindex23_invol (M : Machine4) : reindex23 (reindex23 M) = M := by
  funext q a
  have hinv : swap23 (swap23 q) = q := by fin_cases q <;> decide
  simp only [reindex23,hinv]
  cases M q a with
  | none => rfl
  | some p =>
    rcases p with ⟨s,b⟩
    cases s with
    | none => rfl
    | some s =>
      have hs : swap23 (swap23 s) = s := by fin_cases s <;> decide
      simp [hs]

theorem goodMachine_reindex23 {M : Machine4} (hG : GoodMachine M) :
    GoodMachine (reindex23 M) := by
  obtain ⟨⟨q0,t0,hRun⟩,hForm,⟨qm,am,hMiss⟩,hLoop,hHalts,⟨hsp0,hsp0'⟩,⟨hsp1,hsp1'⟩⟩ := hG
  refine ⟨?_,?_,?_,?_,?_,⟨hsp0',by rwa [reindex23_invol]⟩,⟨hsp1',by rwa [reindex23_invol]⟩⟩
  · refine ⟨swap23 q0,t0,?_⟩
    rw [← mapCfg23_init,reindex23_multi,hRun]; rfl
  · intro q a
    rcases hForm (swap23 q) a with h | ⟨q',z,h⟩
    · left; simp [reindex23,h]
    · right; exact ⟨swap23 q',z,by simp [reindex23,h]⟩
  · exact ⟨swap23 qm,am,by
      have : swap23 (swap23 qm) = qm := by fin_cases qm <;> decide
      simp [reindex23,this,hMiss]⟩
  · intro i p q a side near fixed hp hle cfg hEnter hCycle
    let cfgM : ListBlank Symbol → Cfg Symbol State := fun tail =>
      let free := near.foldr ListBlank.cons tail
      ⟨some (swap23 q),if side then ⟨a,free,fixed⟩ else ⟨a,fixed,free⟩⟩
    have hmap : ∀ tail,mapCfg23 (cfgM tail) = cfg tail := by
      intro tail
      have : swap23 (swap23 q) = q := by fin_cases q <;> decide
      simp [mapCfg23,cfgM,cfg,this]
    apply hLoop i p (swap23 q) a side near fixed hp hle
    · obtain ⟨tail,ht⟩ := hEnter
      rw [← mapCfg23_init,reindex23_multi] at ht
      cases hMi : M.multiStep (Machine.init []) i with
      | none => simp [hMi] at ht
      | some c' =>
        simp only [hMi,Option.map_some,Option.some.injEq] at ht
        refine ⟨tail,?_⟩
        congr 1
        obtain ⟨q',t'⟩ := c'
        simp only [mapCfg23,cfg,Cfg.mk.injEq] at ht
        rcases ht with ⟨hq',ht'⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some,Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this,ht']
    · intro tail
      obtain ⟨tail',ht'⟩ := hCycle tail
      rw [← hmap tail,reindex23_multi] at ht'
      cases hMp : M.multiStep (cfgM tail) p with
      | none => simp [hMp] at ht'
      | some c' =>
        simp only [hMp,Option.map_some,Option.some.injEq] at ht'
        refine ⟨tail',?_⟩
        congr 1
        obtain ⟨q',t'⟩ := c'
        simp only [mapCfg23,cfg,Cfg.mk.injEq] at ht'
        rcases ht' with ⟨hq',ht''⟩
        cases q' with
        | none => simp at hq'
        | some q' =>
          simp only [Option.map_some,Option.some.injEq] at hq'
          have : q' = swap23 q := by rw [← hq']; fin_cases q' <;> decide
          simp [this,ht'']
  · obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hHalts
    refine (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨k,?_⟩
    unfold Machine.HaltsAfter
    rw [← mapCfg23_init,reindex23_multi,hk]; rfl

def UsesOnly01 (tb : Table) : Prop :=
  tb.t20 = none ∧ tb.t21 = none ∧ tb.t30 = none ∧ tb.t31 = none ∧
  (∀ q a m,tb.get q a = some m → m.state = 0 ∨ m.state = 1)

theorem matches_reindex23 {M : Machine4} {tb : Table}
    (hm : Matches M tb) (h01 : UsesOnly01 tb) : Matches (reindex23 M) tb := by
  intro q a m hget
  have hms := h01.2.2.2.2 q a m hget
  have hq : q = 0 ∨ q = 1 := by
    fin_cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · fin_cases a <;> simp [Table.get,h01.1,h01.2.1] at hget
    · fin_cases a <;> simp [Table.get,h01.2.2.1,h01.2.2.2.1] at hget
  have hsq : swap23 q = q := by rcases hq with rfl | rfl <;> decide
  have hsm : swap23 m.state = m.state := by rcases hms with h | h <;> rw [h] <;> decide
  simp only [reindex23,hsq,hm q a m hget,Move.command,Option.map_some,hsm]

theorem histValid_reindex23 {M : Machine4} {hist : List HistItem}
    (hv : HistValid M hist)
    (h01 : ∀ h ∈ hist,h.c.state = 0 ∨ h.c.state = 1) :
    HistValid (reindex23 M) hist := by
  intro h hh
  have ⟨hle,hrun⟩ := hv h hh
  refine ⟨hle,?_⟩
  rw [← mapCfg23_init,reindex23_multi,hrun]
  have hs : swap23 h.c.state = h.c.state := by
    rcases h01 h hh with hs | hs <;> rw [hs] <;> decide
  simp [mapCfg23,Position.view,hs]

-- ============================================================
-- Stateful DFS Tree Verifier
-- ============================================================

def holes (tb : Table) : Finset Key :=
  Finset.univ.filter fun k => tb.get k.1 k.2 = none

theorem holes_set (tb : Table) (q : State) (a : Symbol) (m : Move) :
    holes (tb.set q a m) = (holes tb).erase (q,a) := by
  ext ⟨q',a'⟩
  simp only [holes,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
  by_cases e : (q',a') = (q,a)
  · rcases Prod.mk.inj e with ⟨rfl,rfl⟩
    simp [Table.get_set_self]
  · simp [Table.get_set_ne tb m e,e]

def moves12 : List Move :=
  [⟨0,0,false⟩,⟨0,0,true⟩,⟨0,1,false⟩,⟨0,1,true⟩,
   ⟨1,0,false⟩,⟨1,0,true⟩,⟨1,1,false⟩,⟨1,1,true⟩,
   ⟨2,0,false⟩,⟨2,0,true⟩,⟨2,1,false⟩,⟨2,1,true⟩]

def moves16 : List Move :=
  [⟨0,0,false⟩,⟨0,0,true⟩,⟨0,1,false⟩,⟨0,1,true⟩,
   ⟨1,0,false⟩,⟨1,0,true⟩,⟨1,1,false⟩,⟨1,1,true⟩,
   ⟨2,0,false⟩,⟨2,0,true⟩,⟨2,1,false⟩,⟨2,1,true⟩,
   ⟨3,0,false⟩,⟨3,0,true⟩,⟨3,1,false⟩,⟨3,1,true⟩]

def movesAllowed (used2 : Bool) : List Move :=
  if used2 then moves16 else moves12

theorem mem_movesAllowed (used2 : Bool) (m : Move) (h : used2 = false → m.state ≠ 3) :
    m ∈ movesAllowed used2 := by
  obtain ⟨q,a,d⟩ := m
  cases used2
  · have h3 := h rfl
    fin_cases q <;> fin_cases a <;> cases d <;> simp_all [movesAllowed,moves12]
  · fin_cases q <;> fin_cases a <;> cases d <;> simp [movesAllowed,moves16]

inductive StepResult where
  | rep
  | done
  | missing (q : State) (a : Symbol) (rem : ℕ) (cur : HistItem) (prev : List HistItem)

def stepLoop (tb : Table) : ℕ → HistItem → List HistItem → StepResult
  | 0,_,_ => .done
  | rem + 1,cur,prev =>
    match tb.get cur.c.state cur.c.head with
    | none => .missing cur.c.state cur.c.head (rem + 1) cur prev
    | some m =>
      let nc := cur.c.move m
      let nstep := cur.step + 1
      let npos := if m.left then cur.pos - 1 else cur.pos + 1
      let ncur : HistItem := ⟨nstep,npos,nc⟩
      let nprev := cur :: prev
      if (Nat.beq nstep 6 || Nat.beq nstep 12 || Nat.beq nstep 24 || Nat.beq nstep 48 || Nat.beq nstep 107) &&
          findRep tb ncur nprev then
        .rep
      else
        stepLoop tb rem ncur nprev

def checkMoves (f : Move → List ℕ → Option (List ℕ)) : List Move → List ℕ → Option (List ℕ)
  | [],certs => some certs
  | m :: ms,certs =>
    match f m certs with
    | none => none
    | some rest => checkMoves f ms rest

def checkTree : ℕ → Bool → Table → ℕ → HistItem → List HistItem → List ℕ → Option (List ℕ)
  | 0,_,_,_,_,_,_ => none
  | holesLeft + 1,used2,tb,rem,cur,prev,certs =>
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
    ∃ x y,f m x = some y := by
  induction ms generalizing a with
  | nil => simp at hm
  | cons head tail ih =>
    unfold checkMoves at h
    cases hh : f head a with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hm with rfl | ht
      · exact ⟨a,mid,hh⟩
      · exact ih h ht

theorem stepLoop_sound {M : Machine4} {tb : Table} (hm : Matches M tb)
    (hG : GoodMachine M)
    {used2 : Bool} {rem : ℕ} {cur : HistItem} {prev : List HistItem}
    (hsum : cur.step + rem = 107)
    (hv : HistValid M (cur :: prev))
    (h01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev,h.c.state = 0 ∨ h.c.state = 1) :
    match stepLoop tb rem cur prev with
    | .rep => False
    | .done => True
    | .missing q a rem' cur' prev' =>
      tb.get q a = none ∧ cur'.c.state = q ∧ cur'.c.head = a ∧
      cur'.step + rem' = 107 ∧ 0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur' :: prev',h.c.state = 0 ∨ h.c.state = 1) := by
  induction rem generalizing cur prev with
  | zero => simp [stepLoop]
  | succ rem ih =>
    unfold stepLoop
    cases ht : tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht,rfl,rfl,hsum,Nat.succ_pos _,hv,h01⟩
    | some m =>
      simp only
      have ⟨hcur_le,hcur_run⟩ := hv cur (List.mem_cons_self ..)
      let ncur : HistItem := ⟨cur.step + 1,if m.left then cur.pos - 1 else cur.pos + 1,cur.c.move m⟩
      have hncur_run : M.multiStep (Machine.init []) (cur.step + 1) = some ncur.c.view := by
        rw [Machine.multiStep_succ,hcur_run]
        exact step_move hm cur.c m ht
      have hnv : HistValid M (ncur :: cur :: prev) := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega,hncur_run⟩
        · exact hv h hh'
      have hn01 : used2 = false → UsesOnly01 tb ∧ ∀ h ∈ ncur :: cur :: prev,h.c.state = 0 ∨ h.c.state = 1 := by
        intro hu
        have ⟨u,hprev01⟩ := h01 hu
        refine ⟨u,fun h hh => ?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms := u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd : m.left <;> simpa [ncur,Position.move,hd] using hms
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
  refine ⟨?_,?_,?_,?_,?_⟩
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.1
  · rcases hq with rfl | rfl <;> fin_cases a <;> exact h01.2.2.2.1
  · intro q' a' m' hh
    by_cases e : (q',a') = (q,a)
    · rcases Prod.mk.inj e with ⟨rfl,rfl⟩
      rw [Table.get_set_self] at hh
      exact (Option.some.inj hh) ▸ hm
    · rw [Table.get_set_ne tb m e] at hh
      exact h01.2.2.2.2 q' a' m' hh

theorem checkTree_sound {holesLeft : ℕ} {used2 : Bool} {tb : Table}
    {rem : ℕ} {cur : HistItem} {prev : List HistItem} {a b : List ℕ}
    (hCount : (holes tb).card ≤ holesLeft)
    (hCheck : checkTree holesLeft used2 tb rem cur prev a = some b) :
    ∀ M : Machine4,GoodMachine M → Matches M tb →
      cur.step + rem = 107 →
      HistValid M (cur :: prev) →
      (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev,h.c.state = 0 ∨ h.c.state = 1) →
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
        · simp only [hv0,↓reduceIte] at hCheck
          split at hCheck
          · rename_i hsp
            simp only [Bool.or_eq_true,beq_iff_eq] at hsp
            rcases hsp with (rfl | rfl) | rfl
            · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
            · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
            · exact m0_not_halting hm hG.2.2.2.2.1
          · simp at hCheck
        · simp only [hv0,Bool.false_eq_true,↓reduceIte] at hCheck
          split at hCheck
          · rename_i hcert
            have hns := certificate_sound hcert
            obtain ⟨k,hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
            exact cannot_stop_run hm startPos hns (k + 1) hk
          · simp at hCheck
    | missing q a rem' cur' prev' =>
      simp only [hsl] at hCheck hstep
      obtain ⟨hnone,hq_eq,ha_eq,hsum',hrem_pos,hv',hu'⟩ := hstep
      have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
      -- M must define (q,a) as some (some q',z) since cur'.step < 107 and M runs past 107
      have hM_def : ∃ q' z,M q a = some (some q',z) := by
        rcases hG.2.1 q a with hMnone | hMsome
        · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
            rw [Machine.multiStep_succ,hcur'_run]
            simp [Machine.step,Position.view,hq_eq,ha_eq,hMnone]
          have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
          obtain ⟨q0,t0,hrun107⟩ := hG.1
          rw [h107] at hrun107
          contradiction
        · exact hMsome
      obtain ⟨q',⟨w,d⟩,hMqa⟩ := hM_def
      split at hCheck
      · -- holesLeft == 0: (holes tb).card ≤ 1 and (q,a) ∈ holes tb,so M has no none!
        rename_i h0
        have h0' : holesLeft = 0 := Nat.eq_of_beq_eq_true h0
        have hmem : (q,a) ∈ holes tb := by simp [holes,hnone]
        have hcard1 : (holes tb).card = 1 :=
          le_antisymm (by omega) (Finset.card_pos.mpr ⟨_,hmem⟩)
        obtain ⟨qm,am,hMmiss⟩ := hG.2.2.1
        have hqm_mem : (qm,am) ∈ holes tb := by
          simp only [holes,Finset.mem_filter,Finset.mem_univ,true_and]
          cases hget : tb.get qm am with
          | none => rfl
          | some m =>
            have := hm qm am m hget
            rw [hMmiss] at this
            simp [Move.command] at this
        have heq_key : (qm,am) = (q,a) := by
          have hsub : ({(q,a)} : Finset Key) ⊆ holes tb := Finset.singleton_subset_iff.mpr hmem
          have hEq := Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
          rw [← hEq,Finset.mem_singleton] at hqm_mem
          exact hqm_mem
        rcases Prod.mk.inj heq_key with ⟨rfl,rfl⟩
        rw [hMmiss] at hMqa
        contradiction
      · -- Branch on movesAllowed used2
        let m : Move := ⟨q',w,match d with | .left => true | .right => false⟩
        have hm_cmd : M q a = m.command := by
          cases d <;> simpa [m,Move.command] using hMqa
        have hmem_hole : (q,a) ∈ holes tb := by simp [holes,hnone]
        have hcard_next : (holes (tb.set q a m)).card ≤ holesLeft := by
          rw [holes_set,Finset.card_erase_of_mem hmem_hole]
          omega
        by_cases hswap : used2 = false ∧ q' = 3
        · rcases hswap with ⟨hu2,rfl⟩
          have ⟨h01,hprev01⟩ := hu' hu2
          let m2 : Move := ⟨2,w,match d with | .left => true | .right => false⟩
          have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
          obtain ⟨x,y,hxy⟩ := checkMoves_each hCheck hmem_m2
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
          have hM2qa : (reindex23 M) q a = m2.command := by
            cases d <;> simp [reindex23,hsq,hm_cmd,m,m2,Move.command,swap23_3]
          have hcard2 : (holes (tb.set q a m2)).card ≤ holesLeft := by
            rw [holes_set,Finset.card_erase_of_mem hmem_hole]
            omega
          exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
            (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
            (histValid_reindex23 hv' hprev01) (by simp [m2])
        · have hmem_m : m ∈ movesAllowed used2 :=
            mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2,h3⟩)
          obtain ⟨x,y,hxy⟩ := checkMoves_each hCheck hmem_m
          refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
          intro hnext_u2
          simp only [Bool.or_eq_false_iff] at hnext_u2
          have ⟨h01,hprev01⟩ := hu' hnext_u2.1
          have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
          have hm01 : m.state = 0 ∨ m.state = 1 := by
            have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
            have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1,h3⟩
            fin_cases q' <;> simp_all [m]
          exact ⟨usesOnly01_set h01 hq01 hm01,hprev01⟩

def limitedStep (stop:ℕ) (tb:Table):ℕ→HistItem→List HistItem→StepResult
  | 0,_,_ =>.done
  | rem+1,cur,prev =>
    match tb.get cur.c.state cur.c.head with
    | none =>.missing cur.c.state cur.c.head (rem+1) cur prev
    | some m =>
      let nc:=cur.c.move m
      let nstep:=cur.step+1
      let npos:=if m.left then cur.pos - 1 else cur.pos+1
      let ncur:HistItem:=⟨nstep,npos,nc⟩
      let nprev:=cur :: prev
      if Nat.beq nstep stop &&
          findRep tb ncur nprev then
        .rep
      else
        limitedStep stop tb rem ncur nprev
theorem limitedStep_sound (stop:ℕ) {M:Machine4} {tb:Table} (hm:Matches M tb)
    (hG:GoodMachine M)
    {used2:Bool} {rem:ℕ} {cur:HistItem} {prev:List HistItem}
    (hsum:cur.step+rem=107)
    (hv:HistValid M (cur :: prev))
    (h01:used2=false→UsesOnly01 tb∧∀ h ∈ cur :: prev,h.c.state=0 ∨ h.c.state=1) :
    match limitedStep stop tb rem cur prev with
    | .rep =>False
    | .done =>True
    | .missing q a rem' cur' prev' =>
      tb.get q a=none∧cur'.c.state=q∧cur'.c.head=a ∧
      cur'.step+rem'=107∧0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2=false→UsesOnly01 tb∧∀ h ∈ cur' :: prev',h.c.state=0 ∨ h.c.state=1):=by
  induction rem generalizing cur prev with
  | zero =>simp [limitedStep]
  | succ rem ih =>
    unfold limitedStep
    cases ht:tb.get cur.c.state cur.c.head with
    | none =>
      exact ⟨ht,rfl,rfl,hsum,Nat.succ_pos _,hv,h01⟩
    | some m =>
      simp only
      have ⟨hcur_le,hcur_run⟩:=hv cur (List.mem_cons_self ..)
      let ncur:HistItem:=⟨cur.step+1,if m.left then cur.pos - 1 else cur.pos+1,cur.c.move m⟩
      have hncur_run:M.multiStep (Machine.init []) (cur.step+1)=some ncur.c.view:=by
        rw [Machine.multiStep_succ,hcur_run]
        exact step_move hm cur.c m ht
      have hnv:HistValid M (ncur :: cur :: prev):=by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact ⟨by dsimp [ncur]; omega,hncur_run⟩
        · exact hv h hh'
      have hn01:used2=false→UsesOnly01 tb∧∀ h ∈ ncur :: cur :: prev,h.c.state=0 ∨ h.c.state=1:=by
        intro hu
        have ⟨u,bp01⟩:=h01 hu
        refine ⟨u,fun h hh =>?_⟩
        rcases List.mem_cons.mp hh with rfl | hh'
        · have hms:=u.2.2.2.2 cur.c.state cur.c.head m ht
          cases hd:m.left <;> simpa [ncur,Position.move,hd] using hms
        · exact bp01 h hh'
      by_cases hrep:(Nat.beq (cur.step+1) stop && findRep tb ncur (cur :: prev))=true
      · rw [if_pos hrep]
        simp only [Bool.and_eq_true] at hrep
        exact findRepAux_sound hm hG.2.2.2.1 (by dsimp [ncur]; omega) hv hrep.2
      · rw [if_neg hrep]
        exact ih (by dsimp [ncur]; omega) hnv hn01
def stopAt (tag:ℕ):ℕ :=
  match tag with
  | 1 =>6 | 2 =>12 | 3 =>24 | 4 =>48 | 5 =>107 | _ =>0
def advisedStep (tag:ℕ) (tb:Table) (rem:ℕ) (cur:HistItem) (prev:List HistItem):StepResult :=
  if Nat.beq tag 6 then .done else limitedStep (stopAt tag) tb rem cur prev
theorem advisedStep_sound (tag:ℕ) {M:Machine4} {tb:Table} (hm:Matches M tb)
    (hG:GoodMachine M)
    {used2:Bool} {rem:ℕ} {cur:HistItem} {prev:List HistItem}
    (hsum:cur.step+rem=107)
    (hv:HistValid M (cur :: prev))
    (h01:used2=false→UsesOnly01 tb∧∀ h ∈ cur :: prev,h.c.state=0 ∨ h.c.state=1) :
    match advisedStep tag tb rem cur prev with
    | .rep =>False
    | .done =>True
    | .missing q a rem' cur' prev' =>
      tb.get q a=none∧cur'.c.state=q∧cur'.c.head=a ∧
      cur'.step+rem'=107∧0 < rem' ∧
      HistValid M (cur' :: prev') ∧
      (used2=false→UsesOnly01 tb∧∀ h ∈ cur' :: prev',h.c.state=0 ∨ h.c.state=1):=by
  by_cases h:Nat.beq tag 6=true
  · simp [advisedStep,h]
  · simpa only [advisedStep,if_neg h] using limitedStep_sound (stopAt tag) hm hG hsum hv h01
def guidedTree:ℕ→Bool→Table→ℕ→HistItem→List HistItem→List ℕ→Option (List ℕ)
  | 0,_,_,_,_,_,_ =>none
  | _+1,_,_,_,_,_,[] =>none
  | holesLeft+1,used2,tb,rem,cur,prev,code :: certs =>
    match advisedStep (code % 8) tb rem cur prev with
    | .rep =>some ((code >>> 3) :: certs)
    | .done =>
      match certs with
      | [] =>none
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
theorem guidedTree_sound {holesLeft:ℕ} {used2:Bool} {tb:Table}
    {rem:ℕ} {cur:HistItem} {prev:List HistItem} {a b:List ℕ}
    (hCount:(holes tb).card≤holesLeft)
    (hCheck:guidedTree holesLeft used2 tb rem cur prev a=some b) :
    ∀ M:Machine4,GoodMachine M→Matches M tb →
      cur.step+rem=107 →
      HistValid M (cur :: prev) →
      (used2=false→UsesOnly01 tb∧∀ h ∈ cur :: prev,h.c.state=0 ∨ h.c.state=1) →
      False:=by
  induction holesLeft generalizing used2 tb rem cur prev a b with
  | zero =>simp [guidedTree] at hCheck
  | succ holesLeft ih =>
    intro M hG hm hsum hv hu
    cases a with
    | nil =>simp [guidedTree] at hCheck
    | cons code a =>
      unfold guidedTree at hCheck
      have hstep:=advisedStep_sound (code % 8) hm hG hsum hv hu
      cases hsl:advisedStep (code % 8) tb rem cur prev with
      | rep =>rw [hsl] at hstep; exact hstep
      | done =>
        simp only [hsl] at hCheck
        cases a with
        | nil =>simp at hCheck
        | cons v rest =>
          simp only at hCheck
          by_cases hv0:Nat.beq v 0=true
          · simp only [hv0,↓reduceIte] at hCheck
            split at hCheck
            · rename_i hsp
              simp only [Bool.or_eq_true,beq_iff_eq] at hsp
              rcases hsp with (rfl | rfl) | rfl
              · exact hG.2.2.2.2.2.1.1 (eq_sp0_of_matches hm hG.2.2.1)
              · exact hG.2.2.2.2.2.2.1 (eq_sp1_of_matches hm hG.2.2.1)
              · exact m0_not_halting hm hG.2.2.2.2.1
            · simp at hCheck
          · simp only [hv0,Bool.false_eq_true,↓reduceIte] at hCheck
            split at hCheck
            · rename_i hcert
              have hns:=certificate_sound hcert
              obtain ⟨k,hk⟩:=(Machine.isHalting_iff_exists_haltsAt M).mp hG.2.2.2.2.1
              exact cannot_stop_run hm startPos hns (k+1) hk
            · simp at hCheck
      | missing q a rem' cur' prev' =>
        simp only [hsl] at hCheck hstep
        obtain ⟨hnone,hq_eq,ha_eq,hsum',hrem_pos,hv',hu'⟩:=hstep
        have hcur'_run:=(hv' cur' (List.mem_cons_self ..)).2
        have hM_def:∃ q' z,M q a=some (some q',z):=by
          rcases hG.2.1 q a with hMnone | hMsome
          · have hnone_next:M.multiStep (Machine.init []) (cur'.step+1)=none:=by
              rw [Machine.multiStep_succ,hcur'_run]
              simp [Machine.step,Position.view,hq_eq,ha_eq,hMnone]
            have h107:=Machine.multiStep_eq_none_mono hnone_next (by omega:cur'.step+1≤107)
            obtain ⟨q0,t0,hrun107⟩:=hG.1
            rw [h107] at hrun107
            contradiction
          · exact hMsome
        obtain ⟨q',⟨w,d⟩,hMqa⟩:=hM_def
        split at hCheck
        · -- holesLeft == 0: (holes tb).card≤1 and (q,a) ∈ holes tb,so M has no none!
          rename_i h0
          have h0':holesLeft=0:=Nat.eq_of_beq_eq_true h0
          have hmem:(q,a) ∈ holes tb:=by simp [holes,hnone]
          have hcard1:(holes tb).card=1 :=
            le_antisymm (by omega) (Finset.card_pos.mpr ⟨_,hmem⟩)
          obtain ⟨qm,am,hMmiss⟩:=hG.2.2.1
          have hqm_mem:(qm,am) ∈ holes tb:=by
            simp only [holes,Finset.mem_filter,Finset.mem_univ,true_and]
            cases hget:tb.get qm am with
            | none =>rfl
            | some m =>
              have:=hm qm am m hget
              rw [hMmiss] at this
              simp [Move.command] at this
          have heq_key:(qm,am)=(q,a):=by
            have hsub:({(q,a)}:Finset Key) ⊆ holes tb:=Finset.singleton_subset_iff.mpr hmem
            have hEq:=Finset.eq_of_subset_of_card_le hsub (by simp [hcard1])
            rw [← hEq,Finset.mem_singleton] at hqm_mem
            exact hqm_mem
          rcases Prod.mk.inj heq_key with ⟨rfl,rfl⟩
          rw [hMmiss] at hMqa
          contradiction
        · -- Branch on movesAllowed used2
          let m:Move:=⟨q',w,match d with | .left =>true | .right =>false⟩
          have hm_cmd:M q a=m.command:=by
            cases d <;> simpa [m,Move.command] using hMqa
          have hmem_hole:(q,a) ∈ holes tb:=by simp [holes,hnone]
          have hcard_next:(holes (tb.set q a m)).card≤holesLeft:=by
            rw [holes_set,Finset.card_erase_of_mem hmem_hole]
            omega
          by_cases hswap:used2=false∧q'=3
          · rcases hswap with ⟨hu2,rfl⟩
            have ⟨h01,bp01⟩:=hu' hu2
            let m2:Move:=⟨2,w,match d with | .left =>true | .right =>false⟩
            have hmem_m2:m2 ∈ movesAllowed used2:=mem_movesAllowed used2 m2 (by simp [m2])
            obtain ⟨x,y,hxy⟩:=checkMoves_each hCheck hmem_m2
            have hq01:q=0 ∨ q=1:=hq_eq ▸ bp01 cur' (List.mem_cons_self ..)
            have hsq:swap23 q=q:=by rcases hq01 with rfl | rfl <;> decide
            have hM2qa:(reindex23 M) q a=m2.command:=by
              cases d <;> simp [reindex23,hsq,hm_cmd,m,m2,Move.command,swap23_3]
            have hcard2:(holes (tb.set q a m2)).card≤holesLeft:=by
              rw [holes_set,Finset.card_erase_of_mem hmem_hole]
              omega
            exact ih hcard2 hxy (reindex23 M) (goodMachine_reindex23 hG)
              (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
              (histValid_reindex23 hv' bp01) (by simp [m2])
          · have hmem_m:m ∈ movesAllowed used2 :=
              mem_movesAllowed used2 m (fun hu2 h3 =>hswap ⟨hu2,h3⟩)
            obtain ⟨x,y,hxy⟩:=checkMoves_each hCheck hmem_m
            refine ih hcard_next hxy M hG (matches_set hm hm_cmd) hsum' hv' ?_
            intro hnext_u2
            simp only [Bool.or_eq_false_iff] at hnext_u2
            have ⟨h01,bp01⟩:=hu' hnext_u2.1
            have hq01:q=0 ∨ q=1:=hq_eq ▸ bp01 cur' (List.mem_cons_self ..)
            have hm01:m.state=0 ∨ m.state=1:=by
              have hne2:q' ≠ 2:=by intro h2; subst h2; simp [m] at hnext_u2
              have hne3:q' ≠ 3:=fun h3 =>hswap ⟨hnext_u2.1,h3⟩
              fin_cases q' <;> simp_all [m]
            exact ⟨usesOnly01_set h01 hq01 hm01,bp01⟩

def TreeValid (tb : Table) (used2 : Bool) (rem : ℕ) (cur : HistItem) (prev : List HistItem) : Prop :=
  ∀ M : Machine4,GoodMachine M → Matches M tb →
    cur.step + rem = 107 →
    HistValid M (cur :: prev) →
    (used2 = false → UsesOnly01 tb ∧ ∀ h ∈ cur :: prev,h.c.state = 0 ∨ h.c.state = 1) →
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
  obtain ⟨hnone,hq_eq,ha_eq,hsum',hrem_pos,hv',hu'⟩ := hstep
  have hcur'_run := (hv' cur' (List.mem_cons_self ..)).2
  have hM_def : ∃ q' z,M q a = some (some q',z) := by
    rcases hG.2.1 q a with hMnone | hMsome
    · have hnone_next : M.multiStep (Machine.init []) (cur'.step + 1) = none := by
        rw [Machine.multiStep_succ,hcur'_run]
        simp [Machine.step,Position.view,hq_eq,ha_eq,hMnone]
      have h107 := Machine.multiStep_eq_none_mono hnone_next (by omega : cur'.step + 1 ≤ 107)
      obtain ⟨q0,t0,hrun107⟩ := hG.1
      rw [h107] at hrun107
      contradiction
    · exact hMsome
  obtain ⟨q',⟨w,d⟩,hMqa⟩ := hM_def
  let m : Move := ⟨q',w,match d with | .left => true | .right => false⟩
  have hm_cmd : M q a = m.command := by cases d <;> simpa [m,Move.command] using hMqa
  by_cases hswap : used2 = false ∧ q' = 3
  · rcases hswap with ⟨hu2,rfl⟩
    have ⟨h01,hprev01⟩ := hu' hu2
    let m2 : Move := ⟨2,w,match d with | .left => true | .right => false⟩
    have hmem_m2 : m2 ∈ movesAllowed used2 := mem_movesAllowed used2 m2 (by simp [m2])
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hsq : swap23 q = q := by rcases hq01 with rfl | rfl <;> decide
    have hM2qa : (reindex23 M) q a = m2.command := by
      cases d <;> simp [reindex23,hsq,hm_cmd,m,m2,Move.command,swap23_3]
    exact hChildren m2 hmem_m2 (reindex23 M) (goodMachine_reindex23 hG)
      (matches_set (matches_reindex23 hm h01) hM2qa) hsum'
      (histValid_reindex23 hv' hprev01) (by simp [m2])
  · have hmem_m : m ∈ movesAllowed used2 :=
      mem_movesAllowed used2 m (fun hu2 h3 => hswap ⟨hu2,h3⟩)
    refine hChildren m hmem_m M hG (matches_set hm hm_cmd) hsum' hv' ?_
    intro hnext_u2
    simp only [Bool.or_eq_false_iff] at hnext_u2
    have ⟨h01,hprev01⟩ := hu' hnext_u2.1
    have hq01 : q = 0 ∨ q = 1 := hq_eq ▸ hprev01 cur' (List.mem_cons_self ..)
    have hm01 : m.state = 0 ∨ m.state = 1 := by
      have hne2 : q' ≠ 2 := by intro h2; subst h2; simp [m] at hnext_u2
      have hne3 : q' ≠ 3 := fun h3 => hswap ⟨hnext_u2.1,h3⟩
      fin_cases q' <;> simp_all [m]
    exact ⟨usesOnly01_set h01 hq01 hm01,hprev01⟩



def baseTable : Table := Table.empty.set 0 0 ⟨1,1,false⟩
def h0 : HistItem := ⟨0,128,startPos⟩
def h1 : HistItem := ⟨1,129,startPos.move ⟨1,1,false⟩⟩

private theorem mk_good_ne_sp1 (M : Machine4) (h : M 1 0 ≠ some (some 2,Stmt.write 1 Dir.left))
    (h2 : M 1 0 ≠ some (some 3,Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,4,11,6,16,13,2,15] ∧ reindex23 M ≠ tblOfList [6,4,11,6,16,13,2,15] := by
  refine ⟨fun heq => h (by rw [heq]; rfl),fun heq => h2 ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,4,11,6,16,13,2,15] 1 0 = some (some 2,Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23,swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s,z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h10
      rcases h10 with ⟨hs,hz⟩
      have hs3 : s = 3 := by revert hs; fin_cases s <;> decide
      subst hs3; subst hz; rfl

private theorem mk_good_ne_sp0 (M : Machine4) (h : M 1 0 ≠ some (some 0,Stmt.write 1 Dir.left)) :
    M ≠ tblOfList [6,3,3,8,15,10,16,1] ∧ reindex23 M ≠ tblOfList [6,3,3,8,15,10,16,1] := by
  refine ⟨fun heq => h (by rw [heq]; rfl),fun heq => h ?_⟩
  have h10 := congrFun (congrFun heq 1) 0
  have hrhs : tblOfList [6,3,3,8,15,10,16,1] 1 0 = some (some 0,Stmt.write 1 Dir.left) := rfl
  rw [hrhs] at h10
  simp only [reindex23,swap23_1] at h10
  cases hM : M 1 0 with
  | none => simp [hM] at h10
  | some p =>
    rcases p with ⟨s,z⟩
    cases s with
    | none => simp [hM] at h10
    | some s =>
      simp only [hM,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h10
      rcases h10 with ⟨hs,hz⟩
      have hs0 : s = 0 := by revert hs; fin_cases s <;> decide
      subst hs0; subst hz; rfl

private theorem mk_base_hm_hv {M : Machine4}
    (hFirst : M 0 0 = some (some 1,Stmt.write 1 Dir.right)) :
    Matches M baseTable ∧ HistValid M [h1,h0] := by
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable,Table.set,Table.empty,Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1,1,false⟩ rfl
  refine ⟨hm0,?_⟩
  intro h hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · exact ⟨by decide,hrun1⟩
  · exact ⟨by decide,rfl⟩


end OMA.BB4Common

namespace OMA.BB4H1
open Turing Turing.BusyBeaver OMA.BB4Common
private abbrev m0 : Option Move := some ⟨0,0,false⟩
private abbrev m1 : Option Move := some ⟨0,0,true⟩
private abbrev m2 : Option Move := some ⟨0,1,false⟩
private abbrev m3 : Option Move := some ⟨0,1,true⟩
private abbrev m4 : Option Move := some ⟨1,0,false⟩
private abbrev m5 : Option Move := some ⟨1,0,true⟩
private abbrev m6 : Option Move := some ⟨1,1,false⟩
private abbrev m7 : Option Move := some ⟨1,1,true⟩
private abbrev m8 : Option Move := some ⟨2,0,false⟩
private abbrev m9 : Option Move := some ⟨2,0,true⟩
private abbrev m10 : Option Move := some ⟨2,1,false⟩
private abbrev m11 : Option Move := some ⟨2,1,true⟩
private abbrev m12 : Option Move := some ⟨3,0,false⟩
private abbrev m13 : Option Move := some ⟨3,0,true⟩
private abbrev m14 : Option Move := some ⟨3,1,false⟩
private abbrev m15 : Option Move := some ⟨3,1,true⟩
private abbrev hc0 : HistItem := ⟨2,130,⟨2,[1],0,[]⟩⟩
private abbrev hc1 : HistItem := ⟨3,129,⟨0,[],1,[1]⟩⟩
private abbrev hc2 : HistItem := ⟨3,129,⟨3,[],1,[1]⟩⟩
private abbrev hc3 : HistItem := ⟨2,128,⟨2,[],0,[1]⟩⟩
private abbrev hc4 : HistItem := ⟨3,129,⟨3,[1],1,[]⟩⟩
private abbrev hc5 : HistItem := ⟨1,129,⟨1,[],0,[]⟩⟩
private abbrev hc6 : HistItem := ⟨3,129,⟨1,[],1,[]⟩⟩
private abbrev hc7 : HistItem := ⟨2,130,⟨2,[],0,[]⟩⟩
private abbrev hc8 : HistItem := ⟨2,128,⟨2,[],0,[]⟩⟩
private abbrev hp9 : List HistItem := [⟨2,128,⟨0,[],0,[1]⟩⟩,⟨1,129,⟨1,[],0,[]⟩⟩,⟨0,128,⟨0,[],0,[]⟩⟩]
private abbrev hp10 : List HistItem := [⟨2,130,⟨2,[1],0,[]⟩⟩,⟨1,129,⟨1,[],0,[]⟩⟩,⟨0,128,⟨0,[],0,[]⟩⟩]
private abbrev hp11 : List HistItem := [⟨2,128,⟨2,[],0,[1]⟩⟩,⟨1,129,⟨1,[],0,[]⟩⟩,⟨0,128,⟨0,[],0,[]⟩⟩]
private abbrev hp12 : List HistItem := [⟨1,129,⟨1,[],0,[]⟩⟩,⟨0,128,⟨0,[],0,[]⟩⟩]
private abbrev hp13 : List HistItem := [⟨0,128,⟨0,[],0,[]⟩⟩]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_0 : TreeValid ⟨m4,none,m3,m0,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_1 : TreeValid ⟨m4,none,m3,m1,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_2 : TreeValid ⟨m4,none,m3,m2,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_3 : TreeValid ⟨m4,none,m3,m3,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_4 : TreeValid ⟨m4,none,m3,m4,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_5 : TreeValid ⟨m4,none,m3,m5,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_6 : TreeValid ⟨m4,none,m3,m6,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x24a20000104120926904004000820004136d34900904104db4f2c8000611b79e780000c1b6f3ce00800306dbcf3c0000611b79e7004004136d3caa0001848de79d0104924000100020924104004104134d00024904034d24104924900824006d3cb20800800db5964000100224d24800000024924908c6c006f3cf30d65800de7964124124800da49361209a6800000000c249a4180120030804124824104024030c391b79e612000c1b6f3cf00806000236c30c2018c336f3cf30124904004000824904100104104d24d30904920924924124924120020036924104134100120030000001124924231b001bcf3d8041600379e5904860f001bcf3cc0412003696518183c008f3cf30820004806d0c020000904db4904000136c241248000049249249049a6d24920904104804020800024136924104104db69049200001259249241249b4b2c8000060379e1980006006f3d23000018c036c000001883391c78671b79e718000cc06f3c030000c00de79b6000036c66c00000031866db6d8cdb6b2cb20986000c000300000300379e7986180c36180c30000c319e6db633cdacb2c8000660479e0300006006f3d1e0000336336000000306336dc6c66db79e7b04104020100820000800d249a61041009a4134c00020864936d849a692cb200019811e78000001801bcf48c00000d8cd8000000c28cdb71b19b6de79ec10492082d96cb209248209249041348001a592482490003492490002490190c32080010402412482080413496000692c82092492492430cc301bcf36c208041249249009269049348001249a0024924104100820924904020824924924824920920924920924904104924924904124820364b0c0249000249241049200069249209240019249240009241848208208041249249000049209249200009259249241a4924826980034d34104924000d24924100004924104900820924924920104124924924124826924924836d8002492490492490410492d96cb20000921b248001041049a590580002406c96180492d96cb200009049349640209249249248000240249249008209249249209249249241041249b4986004124936924904924126924120924124d249241249a4924800034925130000824924924920104c249249040208249249248349349249049248000209a4b2c8041049249249000008069249201041241249243249249248209268000041048249a4100904120800104da4d04824d34136934120207838db8c36136f04da4d04c24db783cdb6c361001049a4904c36e60eb6e30d84124804004000824904100104104920d30904920924124924924000034e64daa804104d3cd249049201069349209241249249240318061e6db8c04100c3c9a5104904104d36924d048269a0830000020924926c24904820104920924100908e30db6e30d849201800081b0030806f0cde6f0cc04924104024924124924904924904134100120030104124f24924124904934924900c602079b7230934060f279641279b03079bcf30924124d249241e6c0c1e6f3cc20800020184900804104936104d000008201249201049241049241249e6924824104120d269a0104124da49241249249a4924824924904924904926924920c300361b6db60000061b71c6c30c06db6db0c0618818cdb72319bcdb6e361261861b0c06d800001b6de79e61861b6db61b6c30c36de79b6d8cf379bcf309241249208249241049240019249241041048040208200041349600049241269349209a4b2490493492490c3061bcf36db0924924d24924024904134d20c04924000d24924104020824924100820924924920924824824924824924d24924d24924104924104120d269a01049249249241249249a49248249249649249069249209248209241049340208249249248249249049249049249249249209249241041248040008000208249241041041209049200008019249241249a4b26800004144d20c00824924924920000100d24924020824924924824924924904104920120820104924924924124904824924824904964924904926924920820924d349340209249249248249209349249049209249249209249249243249248324e590,1,1,1,1,1,1,2,2,2,2,2,323,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,1,1,1,1,323,2,68,2,2,2,1,2,2,2,1,1,1,1,1,323,1,1,1,324,324,1,1,324,324,324,324,324,323,1,324,1,1,1,2,2,2,2,323,1,6405,1013831,306759,1,324,1,1,1,1,1,1,1,1,1,1,1,437831,1,1,175687,39501513,437831,1,1,1,1,1,1,1,1,1,1,1013831,1013831,1,1,1,120997513,175687,175688,1013831,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,323,306759,1,1,997447,997447,306759,1,1,1,1,1,997447,1,1,44616,997447,997447,1,1,1,175687,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,306759,1,1,1,1,1,14277,1,1,1,2,2,2,324,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_7 : TreeValid ⟨m4,none,m3,m7,none,none,none,none⟩ false 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_8 : TreeValid ⟨m4,none,m3,m8,none,none,none,none⟩ true 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149249a4924924180924d24024104124924904924824924d241249201040001341641249a4100920820924904824924820524924934930904104924934904924824900805904104924814924924924180d34924d34000124924984924834d35904120c059249249340001240001249351641240049269249a0900104924924820524965934934d20c04920c04965924d04924824d84db6100020936d0498490482cdb6db6e00000926930004238d38d20d36d049b49348024a0000920c249a092c3369261a418092c30092cf249a09249049241009208209249048249248241041249249a01040001041041249049249248249241259249209249241249249209209b6c06db6db6c24b0cdb6d88d86024b0c036f3cdb6c24924124904900804104104924904964924824924804924924d261a6180926924824104124924920924904d36d241a61809249201241249209261041241241a6c049049248249249049249005249249349a69860249249b4904924824920804d04104924814d34924db0000924924824104134d35904c208249249309249059249249200009249b6d36184820824100924924924104004924924900524965934904820824920804964124d04924814926984924120820924c30134d04934124920100000030100026820824924804904905834d04920920924920c00134804d300208249a4924804100827984104920926924920c30124904db6104d84104934904c30336d04db6108000186d86d840940001258261b0124104124924066c31864926804904904924900120000924120104124924924124904924924904000d25826db0836c318349268249219249249209a6c049349248205b6c06de6db6c248048008049248249a48349649248249248104925349659848208249249b4924904904804920804904104924812924b349249049048249841249b4936c2480c208e3cdb8c24000800924924804904104924904924924124924104120934924104924824924924184104d349c6c24b0490492492482c1b61b6db6db0812492092534965934d30c04924934904904924804920c04d041049248125249349049049248000061b61e6184930804d34126d84924820104924924900920820924920924924824924800920804d00180820926924920924824924924830806da4136d84db6f361b6db6120904924924904c361b6db6db61024924124a49a4904120820924924904924824db49241241809201801b8f3cf30920824934d249209249249349248049369261a41009249a49049248269b4d04120820900000006186184000134184186120000920c249209a4824934924820924924804104934936c249241249b6db6d86db6c24930805906126d84924824924108136a2c320000da69249041041b5924b2c80006692492490692cf24920924904934000124924124d0080590410630c024d261b0001824d24824120830925920d04106134db61a08048049249241e79819b6f6cc24920924924904300125b261b098602000010418c006decd86c20924020000104124820824924824906904924906924920924920104d24964830100024924924904000924924924124904904104924904134d061009649049249a412492418c1b0e3cd890249041b4d24de6824db6c2492492432c82490080590410492082092492092492412492412492482492482490003c9249249049249000061a69a42301040248249340208069b4928804120934924904da4924920000120164104020824924924800024904924900824920924920d24924924120830925924d00820924924920924924924924124924924924824924924904106125234da000098c1a4904104335924f2c800066904924908d25b26db0b24106124b249a0104024824924124934924924824920924924905924924920986186dbcdb6c06180db6db6d86db6db6db6db0db6db6db6db61b492492482049248,2,1,2,1,1,1,1,2,2,2,2,1,2,323,1,323,13317,13317,15045,2,2,1,1,2,2,2,2,2,2,2,15045,2,2,15045,15045,2,324,324,2,13317,1,1,1,2,2,2,2,2,1,2,2,2,1,1,2,2,2,2,2,15045,2,2,2,1,13317,1,1,1,969287,1,323,13317,1,1,444999,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,323,2,2,323,6789]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_9 : TreeValid ⟨m4,none,m3,m9,none,none,none,none⟩ true 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149249a4924124100924d248261841249249049348241040008208241249a4104124d20db6186006db6124924904934820524924934920986104904900820920904936d861b0db6d84814924924924100d34924d36000124924904904834d35904161805924924924000124000d24920824136db49a69208040049249241201b61b6db6000100104924904820524965934924920804920c34924920904906186db6db0c04814000124920824104104924904830834924920904800924924820124820924924824124c00db6db6c30120494d34104124920db6000006db6136d049049348371b1840de79840041249249201b6000824124100104924904824000c24920c34136db08209249859b6000c36dc6120524904900820924904924930924920904966d80c30db6d84804924924d24124100926924824104124924920924904924124824924124926104824924124924920924900524924934904904024924900820924904924814d34924d30000924924824104134d35904c30c24924920924905924924930000924000124924924124100924924924104004924924900524965934904c00824920804924924904924812100000020100026820820924800804904824900920920924920800134c261000208249a49248241808369a4900920926924920186030db8e360208249a49a6824306030dbcf36124094924104924924124904924924904120004104120104124924924124904924924904924124924924124920524904000904104824924904924924904924810492534965904c00024924904920820926904924812504d049249048049041249a69041249249249a4104120924820104924824924824124920924920904906d861b6db6d848125c6c00186de78249a4906db0c30db6d849248120925349659609000049249049000009041049248124a09808349a49009208209249208249248249248009200009001808209269249209a4124d249241248249a4924836d80c36dbcd8492092692492093cd86db6db6d84f361b6db6db6102492412494934000826924124d00820924904124134924120000824820824120c209249209048268269248241249b6020824924120924020824924124820820924824906924926906920926924920100924924820100024924924904924924904124924904134d001002269049240249249a4104904924904800030920820104924824924824124936d80c36db6d848249008209249049208209249209241249249241248249a49248000249249249049249249041041249249200000268208261041049249348208209a6920984d34924d2000012082492402082482492480000492492490082492092492092492492412082092492490082092092492092492492492412492482492482492492490482082492482402082492492482492092492090492492492492092492492412492049248,1,1,1,2,2,2,2,2,2,2,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_10 : TreeValid ⟨m4,none,m3,m10,none,none,none,none⟩ true 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x24924925925920000924d649048000269bcc209800041059c412082092496490482082482c82c8000049200001209209a0f30b200001249040048208049249a4934920000926924d04820824934900124904906984120820924000134164124b20000920b20926820024824820924924d359361200009a0db08261800248060040208249a79b4120820924124924924924c249241341a6104820804900c04d041049248249a4d36160000924924d34160000924934d858000269b6c20b00004834db41e0000924936d05800024926820b00004120000100120db6db0c3c0001009040040008049249248241041249249001249049249269241809349249b4906065934904100004934904935964120820824924920800020124924820936d24984944c24935924d05830824d34936164d209a6db08260001001a5184d44c2482c9a082c180105800004004830f36c30f06004824900104d201249249249060249349209041049249261249209249240249241249249a4906024924926d24180924924134000100004135934d04924826db6db6180030830c301861b6c36db6db6db0c06db6db6db6c30336336c30c00026830c30f3cdb6c041041a69a6984304d88db6da00001009a69a40001341b69b88024a08201240208209a49a4800924820924936920c00820c36b2cf30826924c2483030c9a680080002cb24826f2cb209041041269249040001009a4924104924100124924124924824924900820804920800800020104924804900004104104100804d24920924101805924920920820804d008208269a6930024920c36db6db6c300000601b6f3cc30db6db0db0c0c336db0030000b0cdb0e3cf3cc240061069a49a6100004026924904124904024820824904004924904924900924920924920124924124904004000824924100d200209248201041041040401349248249248049349249341a0000926934824104124924d048208249a49001249049049b49a00009249040001808209261041241241049200040268249a4904d24900524924924d26800024924924124920924d26104820804d000049059049249000268208249249209249208149249b49a4100924924824104134d27904c20834d24900124905934934f300009249a69241048208200009b4824920100924924924030006134c20804004934124900524da49269040249269241249209e7924d3c800024900024d241641048040209209248209209249249208169b69b69200009a61a69848208000000041061879b4936f300009a40009649059641200008268268208200249a49a4820100000030130026820824924804d041068249049209209a4920000134904100020826924924804100c2c9841049209269a4920000134904db6104d84104924904000336f06d861640909a0000180800124104124924064021804126804904904924900000804820800104134924924024c041248208049049349249000009b48249308268218249248200019b5824820866c6006cdb6c20426800026820020920920124920800020120820020920924924920820827134924824820866d649248248109249349659048208249249241249209a6f30b26000186060187800c24820f3082000412480080482482083cc20800104924920d249201249249249248000249249241249209241a6904820824900004d05904824904024820820924920924920824924924836da09860009241009208209249049249249061b412082012482016410412492092493cd34c000249249a0db682c006004904004000824d36de41600209240a4924926836da0988180124100120020926904924926d06db41000201248201241041249209a49b4906000820924120020020db6db6c36db6136db6db0db0d8c926da41000209b59a09b4f36c20c30c3cf36db01041049a49a420d1b61bcdbcc00004026926904104104004000824124920904920904124824104020804024924904124920924100000100d249241b4030135944c24b0406016492482c1818079b6db0812492124924924b249000049a4d24d440001341b7900000024134f20904106db61811b0030924d3c824104106987906800024900004904d061b61e61b0000924c20134104014924924d26db41000209240201341041249205b6da6d86800034d65904100006db69b69a0000924800000006020804120c04d041069a61809a0820924812400006d80d86c00000004d200000301861b71e0000800134100000100006000c00004da41241000001b78671b0000136d04db6000036d31944c04104da4924d00006186db0000104136924924000066d609308200019b7836c30800104d209041009a0820924920030c30180000124924824924800120804d001808209249249209248249a4924800006db6338d851b6f36db1b661001049269249041861b6c36db6106de61861e0c30d241041249241349249049249061241801a00301041249249241e79e6db6f6cc04904934924900000db4c651309e79e6db6f6cc200219b5924920800c06d86db6c204924249a4936d20000924924934906024d24924d241809269b4d269a0c040049b6d200009269249349060209a49269a0c00004100120920c36db6db6c30104104804820804924926126180924924824104124924984924834964b00124904924924d04820836db6db0d86184924934120820104800935964120824106920820800124824924820924934d868208249249261249209249a4d36824a26004104804020826db69b41249209241249249a49060249249009041049249201249209249240249241248268240009248041208059041049248249224a0824920920d00004d34924820820924924924000124924924824926924900004926924980104920824124000124b04924804104800124904924924920c30db6db6c36030db6d86c36c36db6db6db6d86db6db61b6db0d369a49241041249a49068041248209049049249249249209249248249241249249248029249249848208249249241249209249249249060249a6d349a68301801249a49860248269249a4830020904804824830db6db6db0c049249201249201249249a4800024924926124920925924904820824900004904d05904804124824820820924926924920824924926934da0926900104120120820924904924920186180c30c308209241649341249208a49041040040008000249249241041049209049200009259249241249a4b2c8124920a49249249208049249041208209a49248249241249a6d04924824904da69249060249241008049249208001249249248049349a49a0000924d261048208269b49041208209000000041061840001241041641200009a08208208208261249248209249269a48201249a61048208249249209249049249241249209248209a6124926824924134da6c209860249269b41249209b6124c00924824806006020820820004d04124d001009a08249a09248249041b6db6d86800034db4d20004108db69369a0000d36d348301b6da69a68200069a69acb00000926924904000237904b2c8000349e4d249049a49acb209208249209209000049349248208209249249240001249249248249249249048209248248240209a4104824824924924924904924924124920924924924104920100000820924100124924134c04004000024924c00924900836c04da4d00924d00924100104804000020800034035904004106c04d80c00820d009249241861b01b61e6c20834024904104b27805b2000098cde01ecc00026980800004100924030000104124820824924824934d869249069a4920924920104d34924c00100034d24924104c30d34924904124904d04104924904124804000020034900004904904d36900964100924020164104030db0db6c400241301009000009041b0d24060820800804800004c30d0092410432c8269000049041049208209249209241041249241a6924824924824930dbcdbd9b0004924904100020000800000800124d44104000004000000000c359041049b49a6aa0000100d24d24020824924924800004134924900824920924920934924924104004800020800004804924904100920904100820d26164d341a4924b2c800000d04904900820924924920104134124934020924824924824934924900000984e349b000090c124904000026934f2c8000249b0d249069b4924930920000987b349b0000b003649040000671b4f2c8000648301249079b5b24b20b204a49a0000124920924804004820800020da09a0980004124124120900104904906800030da09a0980026124020820820904904924800020920b20904820100100820000c3682c82810492010010082092410412492412482482492483490490492490080492492400080012492492482410492492482092482482082492482092480080692482492092092492000483682882c120c341a41249a0006c368269ac1208261a41249a09241248040248208249041049249049209209249209241241249241041669649208249041e69649208249248000248269a0d00004000db7020000926926b24000164904b5c826926b249000049049249201041249249240001249249248041049049249049249249209040048248208041049249249049209209249209241241249241249249248000248269a4900004c60d84c20000926926b24000164904b6c826926b2890248002482c92490082012402092000092492492402082482492482c92c924904000d30b249a6020864d60826800034da6924900820930da4920f34b24924102924800804924824920920d24920000c3cc36c36000984904924824926924124920000c38826826030004024820824000c2882c824120804024820800330f20b209041248040248208249209209249208001a49248268249269241249208201a4904824804d041049249048248208249248248249001b0db0db0f049041b0da09a6b049249049200079b61b0db09208061a4120920924124124924124920000db0c36c36030c06180000c00036db6dbcd80c379b003c330dbc9ac9a40a4000d209a492402083410600480003492492c900824120020020d289ac9a411249208,1,2,1,1,15045,15045,15045,324,323,2,2,2,2,15045,2,2,1,1,1221,6405,2,1,1,2,1,323,1,1,1,2,1,1,15045,15045,15045,324,1,1,1,1,2,2,2,2,67,1,1,1,1,5637,2,2,2,1221,1221,67,2,2,2,2,1,1,1,6789,6789,1,1,1,67,67,2,6789,67,2,2,67,2,2,2,67,2,2,324,1,1,1,2,2,324,2,2,1221,1,1,1,323,67,2,324,323,67,1221,2,2,1,1,1,1,1,1,1,1,1,15045,15045,15045,15045,15045,15045,15045,1,323,1,1,1,1,282183,282183,1,1,1,1,1,15045,2,2,2,2,2,323,15237,2,2,2,2,2,2,2,2,2,2,2,2,2,2,323,2,2,2,2,2,323,67,2,2,323,323,6790,2,2,2,1,1,11589,1221,67,11589,1,1,1,1,323,1221,1,1,1,1221,1,1,2,2,1,2,2,2,2,2,2,1221,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,323,2,2,1007175,2,2,2,2,2,2,2,2,2,2,2,2,323,2,2,2,2,2,2,11589,323,1221,437831,2,437831,2,2,323,2,2,306759,2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b3_11 : TreeValid ⟨m4,none,m3,m11,none,none,none,none⟩ true 104 hc6 [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149a49a4934924100924934826004126924904934824924d00130d048009009260001249a4104124d209341000069a4126924904924824924d20936d00524924924d20980104924924824824120024024920804924d040209a69049249248249a4014924924924100924936826004134d24904904834d25980120d05934934d3c0001249269a4d24920804004924924120000800920824100104924904820000124900100524d269209801049249a48248241679a4d34b00004924900020024820904924824924824014800800824000104104924904c20020820920805800934dbc0001349240008009a0824120824926920900494d341041249209b60001069b4136d04904924836da1824926d040041349249200008009208041001049249048200001249001040008369209341269a0c209249059b600000cde61205249001249a69049248249249a4104120024820104924824924824120820da4924904967980000f379848049249269349240001249349049348249a4d24920804904800924820124926000824b241249a0c2092c900924925925924000124d64960904104d65947924000120800000b24824964964900004924000025924124904100964904124924924924124d20904920020926904934824924d359340241041371b0c309b4d008240080269a0924021825944124904924924924100924924904934824924924824104165934904c00034924930904104924820820924924100020024924900926d34c64104124924d34d64000124934d31904104930d36d66000024800000826824934db5900004124000004124104904100104904124934924904024924920904104924924125120924924824924124924920904104924924130c20924924c24104104024124924904924834da4900924904935924d04130c04d34934004924134da71001249009200001a09a0905900001904104124904064924102180c00d26100120820004820804106c00d26d360041801a49208000241309a49000040069249201b6c00db8db60209801a49a6824336c00dbcdbc124094924004124920924920924934824820800924904104000104104800020024924904104800924924124920524900104924824904124924904924824924d20924904924924124904100104904920824104120d24104c2412410412002492490492481052492492c924800026924d2414102092493cd24904004100000006904924f34924101124c00104934834920c24134d20814924924124020024184124d20534d65904c00036da6da0986104db69b6826184124900820820926904924812504104d249048069800209261841a68208249a61000209a48200048208269248261208209a4926984901006186337184812544c00104de7836d861801b6d06db6186826db4126900820c20926984924812124924924920904104924924824924124120824920804924904120924904924924824924024934965964900004924924c24924146de11e798000482000002c820934900000965904d24924c249241049249241248008249241249209249248249001809a68249240a4934f34d00004924900000000004100820000320820124060064104124904924924024000024104124920924924db6c36c36db60248000068208249240a0800800800104824924120924106120034936d801060069248208240200240060001001a49248061b0036db6d808240069269a090c1b0036db6d84306c00db6db610249241492492492410092492502410413496c9049348249249309249049b6db6db6d86024924d249208049249349248201248201049a4924100024920924900926934c24000124924930904104d24924c24104124d30936c24000000020800824824824930904104000104024124104104900904904124924904904024924920904104924924124d20924924824924124904124020924904924824934d00980004924924024924124900000000804100000920020820820134024104124904922000934d26d30000124924920800024d309a4900004926924920934924d240941048249241200009249249041041009249048000249249249049249249205041209249048041249209049049249249241209249248249241249249248105249249209041049249248249241259249249208049249041249209249049249249a4924024924930900004924924c24924124924920904104936c24920904100000820020820900804900904104124924024924104924924820824924924124920924924db6db6c36db60040248008208249240a48a0824d349b0d00004926924820820924d269240001249a4924824934934d02492414934920926000124d24024920804830904924820104104924904c249240008268208241208209a49209009249049248201249041048208249200209269069240000249209248001a682680412082090410082000cb208209a09001a4b24824104820924924100020824924904134d20020a061049248008249a4130024120926904104124924120920820924920904900c361b0db6d848249200249208049240061208209248008249241249001849248249200069a69a00048209249240208041a68208208261069269a0924904000d34dc61000001249a492080003414098410000492c9a4920924d359341041249249048000269ac9a0004104d24924d200009a6924820124924944820834936db0d00004926924820820d24d26d340001249a4924834934d34d049240009049249200209040048248000260209249008240000249209249249241208249249209008241001209209248269249241249000049248249249249004949241841249209241041049241349469049348249249309249048209349a41040001b6d86db6c00024920924904180934924920124924920020924900926000024934124904104924904000104124104104104d00904904000104120000026820820924820804104904104d24104104924124124906104924824904120924904924db4924d20924924924924120006db61b6db0920926d249269049248249000309c5904924904d24924124930db0830934d80924928924920924924d249241249041040249249200009049a49241041009249048000249269249049a4924920904100924924004104920934d04924004124120924924924924126934924822000900c26d300001209a69248000241309a49000049269a4920944924d340945105249041209249049249248249241041249209249049249249a4924120824924920904924d20820924904824900830934d04924924d24924100804904904104924924024924130d841249249009a0820824920934904124924904904924924924920924924db6db6db6db60249249a49248249240a48a0820d349b0d00004826924920820934d269240001249a4924824934934d0249240,2,1,1,1,1,1,1,2,2,2,1,1,15045,15045,15045,2,2,2,323,2,2,2,2,2,2,2,2,323,2,2,2,2,2,1,1,1,1015367,1015367,323,2,2,2,2,2,2,2,2,323,68,2,2,2,2,2,323,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,323,323,2,2,2,2,2,2]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b3 : TreeValid ⟨m4,none,m3,none,none,none,none,none⟩ false 106 hc5 hp13 := by
  refine branch_one (q := 1) (a := 1) (rem' := 104) (cur' := hc6) (prev' := [⟨2,128,⟨0,[],0,[1]⟩⟩,hc5,⟨0,128,⟨0,[],0,[]⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed,moves12,Bool.false_eq_true,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tv_b3_0
  · exact tv_b3_1
  · exact tv_b3_2
  · exact tv_b3_3
  · exact tv_b3_4
  · exact tv_b3_5
  · exact tv_b3_6
  · exact tv_b3_7
  · exact tv_b3_8
  · exact tv_b3_9
  · exact tv_b3_10
  · exact tv_b3_11

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b7 : TreeValid ⟨m4,none,m7,none,none,none,none,none⟩ false 106 hc5 hp13 := by
  refine guidedTree_sound (holesLeft := 6) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_0 : TreeValid ⟨m4,none,m11,none,m0,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149249248241009209249249048248249241041249201041040000241249249049248124904a48a4884904100800102524924904924812414824824100920924924934824824924004924924120104924d241041249249249248124909249248249348249248003249a4800824b3cf30c061bcc240a48a48841249349249025249249049248124140041049249200001641240041001249048248000049059001041049249241209041249249248240019649240241124904a48a48800649349001025124249c0824164d2093492490493482002492496412090492492490482000cb249a0100924e44204d349209049c91a4800946824924924004924100124904904824924920904904904104824924124924920924904b44184124920920484924924824100d20926924004924124924804924824924920904904924184134d30900104c241240a49249209249049241041249a05105148a4924906104934824904100804102524924904924812414d249200051609249241049241249249049049059249200249208249248249248241241200041601049241241240849249049249001001201240205e69248009248105249248049648148a4806924800104804124904904902524924804924812414d00004924d009201048249241340301059340248249209349041008241249201001249241241040249049249059000049059000001049641240a45e6020904924810100100000104026924820924800804d04900000924920920920336904000b04100006d861b6d8400013013480002092482482480432410c8259009249209249201001800009041040249049049041148a4964020904104820804904904102512414924186134da0924924984934864924900124900824824100920820124904824824924104124920104134000104124924904924824920490492492400104d04904004924904124904124924924124120124924924120904124924924904124924924924004126d04904804924924904904812924924804124924804824b24092092492534920c6192090492490492618000690493492490492482480002098090490092492082092082492492482480c9249249049040249241249241009301a000cd0082492092092018c9b6334124024924824924800800d80d241040249b6924124102534924920924904924924924904924800804905904104924812412494934924000024124904100800100004124124160986104020000100186d84906820004134134140000824824824120020920920d041041a6124da0104104c24904000104d86d05804124920924900924104020000124924820824824924904904906924920920920904924904104904100820924934100024924924904000904924924124124924900104d04924924124124120036db61e61b0800905904d04c241049348249241041369a4d34804924924924904924924d2492402490410080410492492082092092492412412412492482482482492082412c9249049000249349249049000048249019201041240249040001249248248041249049249049259249209040348049008041249009249049249209249209249241249241249a4924820004024900d30000d048001b4000166924c0400006492c909904924d251600009049201240209248249248000249249049008249209249209249249240a08049009241008249209249209249241249241249248249248249249249041001201240000009049041241041208241248000249049049049249249a0400130d24064804106d80924100004db49209201049b6124d241249649248104a4920824124920924924904924820824924124920924924904924824004104924920924904920106924da09249249849248201009209200209249248249248269808241249200001041240041279a08241249209209249248041249049248249241249249b6db6d86db6c0080490590010492481491410002010000000090492592410412082412480002496492490c92692db2049248248,1,1,1,1,1,1,323,2,1,323,1,15045,15045,15045,15045,1,323,1,2,2,2,2,323,323,1,13317,1,2,2,15045,2,2,323,323,1,1,1,2,323,14278,2,324,13317,1,15045,1,1,2,2,2,2,2,2,2,2,323,89045513,13317,13317,13317,13317,2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_1 : TreeValid ⟨m4,none,m11,none,m1,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_2 : TreeValid ⟨m4,none,m11,none,m2,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144949359b0004920000860004836124d60d0402481490000412492052490c10492482492182092490250492492ca200069e0926b268008208249a000c1269e0905904000900124020b049248249205144495c8c011b6c22424940d040240129a6834824a241c71c7000946814924304124d20124924904924130004c049349249849248248129249241049241249249249049049a08249a4924900820924d24924000126924924814924804100920534d20904024810800000824c241208000040008241000208309068240000241200009349a4d26000238db7030c30066db6f06180006e38f36db00049a69249200001b4e248260000269a4924804800338f3cdbcc00036db0db6d841249209040248249249041059049249a4920920924924d241240a48a08249349041024001249049248124129041040241240209209240240041249001249008249a4924900800126924824824905944924100114924104924920504106124924810524900124924824904120965904924824124920924924c249240a4884164934904002512424920024924904924004924920926804824b2412493618494482400400580002180016010480482002d8049a0000924924904124924802524924924d0012490000000002402092492482412412080412092490492492482492412490c1049248248049349348201009b0926d340049241049268048040249a49009049049000041249b0900104c241241249209049248249a4900124904590514924920804026824d249a01209209240001049260049051000041049248241249205144149248301009209249241049241249268248040349249049049079a49600059309b71c70311c6c201008009240001049241241240241208241248049249049249069208000048005e6db78001e6c10428920004024010da49a01209208671458001648268000200249200041249049049068249a0924920426820800920814416980004936920d301048249241b61209049b4c34c24900134900000820900000100134924124060120824024804024904924907980004d059000001449641241269800041249205e60001b79e6c101001000009040269248209248008249061200009249209a09203369ac000b061081c9288e0918400010012403002092482482480433490c8059009249209a4920100180000904104024904d04904124806124924814924824124920820104124106104020824820824d249a09209209e78001341640000041249041045240209049248144149263061349b0934936d849348649249001249049249a00009a08201268008268249000041249a0104104000104124820904926824920490512534d66c00130800021800020d04db5834120d20504000105830814d24304124d209248608249240941125249209040248209a49a4120920924900104924824104100004104924824124920524d36904964814412496910924c341009204a4926da09269044824929221241040201040949249241249204904b6db01b0c06d80db6db0c30db0db6db6db61b61b6db6db6c36c24920186db6db0c30900030db0db6d84902504100904024024124da49201009200072449251a092082492490410400092492492400090c1049240249249349241240129a48009249241a4830d0593482492cda09269049241b4124d209b6c38d86dbcc36db6db0db6d86dbcdb01b6f308009041248240249e6db6f07b36c24092124b3af410001b6c24945100034984100000024830924905020134186d80186036c20000000904804924820c24934134e06004938c2c8149249b6db6c06c36c261b6006180db0924904020134124924db0124d20920492400f30d0400d0001a0000005980036c34100180006906820136000f4090402cc20000004124800800c00104000c0002698490400400012412490000000000490000012492490490003d034100b30004924da41240000001809049009a4920820920030186da00000249249a482480cd24934d04904004924104924100180030c0c1808249209a092018ce3cdb0246024924824924800000d80d241040049b610412410482490410412412092492490490006d034920f209a6000124900820060004101860104924124124124924904924904100000124820800ddd1248068205b6d84024da6c349249009249069b4920126920924800024804000000004904d041041009209248309248124149a4930004930524920d04024814d34824100920820000824b0c090004104124100504100104924820820120924902504924824100920924924104924124936d24834824924934904902826924820924820824004924920800120924924814510524936c00104814924db4920120530d26924804006c36db6d80c025129208049248240000001249008149240049241201249209040248249249041349049249a49209209249249241240a48a24001249249248124140009b68249a60209470451c6804126e269a69008252469a5120e38924a341100048249009201049241241240001269248248041249049249029249145105041249049248041249049049049249a49249209249241249240a48a2512420824920924900004c65864d20820934924b2400013cd24844825a2c924902482524934c00036814924c34120d20534d20904024c248000249a0102400104104100814124004124120820804824920090c36c36180db01249209040248149249a492092052492482082682290412c904924804d249041049049249a412492052498cc00936816412496db6db0c30db01b6db6db61b61b6db6c36c36c144a4920024920906924db41209204824929221249241241240949249241249204904a24001209240248041249049049000049a49209201049241249241249249268128209a4824928020834c04d3882492cda4926904924db4124d209b69a49a40920949a00049349005249001249248100040041041209048048249241041001049248140040049249204a2504924004924920924104824924124936d0493482492490010490082482410492080012690482482290590400010c124820904924814510524830d05934814924db4124d20408126904a34c00c36db0db0d82404100104924812b36c30d87a38c14124900104924824904120934d049248241249209249248249240a4884104160824002524924984924812410004804924920104124824124000120904a248041249001249049a29145100001b0030dc0000036f08f360000361c0d80d8000cdb0036f619b6dbd1c61041069249248041049209041049249a49289209249240249240a48a251241000c906928b60000904924924000120984c0400002496492490ca249269e0492484920820100000924924104124134d00004004024924900904900064907925900800000020920026984100800000824d06db4d00900100d24900104124834924c00004806d24da0820924d249240019341e6d64000804134924100924104020000124924820824824926d849069069a4920920920904d24904104904106c00d24934120824134924d04000904d24924124124820004020024924d00004804d241809201009241040201001200000061860308001459b6d64c20820004800804020934d34924000130984d34800024900124904000924c249240249041000041049249208209209249241041341a49248248248249061b003cdbcd84900024934d249049000049608019b0000a2cb003340001648218060000682209079049679259308001b70360460061b8e08e391800071c0dc11b018724adb6e461c71b71c6c24100800124000000d06800130104100004104c00004030804184ab4924920000d04100134020924824924800024d04104d00824920924920924924924104026804920800024904904a04104000924100820934024136126924924800004100904100824920924920104924124134020924824924824934924900000800900800000904904124000120804c04000024934d04906a269249a04001b7830066c00038f3c00cd800079b0c60180001a08c362661b79e6de6c10524800104934814924004124d204001001041048241201209249040040041241205001001249248128941249041249248149248241249205041249248248268249a4924920924020904924800005104924902514412490db0c381b6db0036db6c36db6036db6c06db6c101040041249204a6924db41269204824929220209241241340944904b0c301b6d86d80c30dbc1b6db0db6c36db6db61b6db6d86db6c249269349025041009040248000241249249041040249249200009249249241249249a48124920a49a000496493092690c124924c200059b4164930db6db6c36db610416cd04924c2400400492492092490492400492492092430682db241249671049b4834937180126d00825834104900c30f49b06dc6000136d0480480003c1c1986d84905b00000000124800104d34836d881b0db8d84da6800104d448209a6800105934824924204126d20934804166d04924824b24124908104924c2490c1a0b2cd04924db4124d209249b6c249a413d1bd230048008db71b81b6db0000f36c361b6104100060824004924946d84934834820004a05944940104020800024000136d04a448041000001001059b59c4e21904106934d24c04100820020104924db4926d20924800024024166d349b482000c90692db20000b0692db240001609858040000679e4d2790da349adb2092490248,1,1,1,1,1,1,1,323,1,11589,11589,1,1,1,1,14277,11589,11589,14277,1,2,1,1,323,14278,323,323,5637,2,2,323,2,323,2,5637,14277,124877513,323,675399,323,323,323,11589,2,2,2,323,2,2,2,2,2,2,323,1,1,1,14277,14277,323,323,120997513,14277,997447,323,323,1,1,1,14277,14277,323,323,175688,14277,997447,323,323,1,1,2251445471522383,998984,14277,14277,14277,14277,14277,14277,1,1,1,14277,324,14277,1,1,324,323,323,324,323,14278,2,2,2,14278,14277,2,323,323,1,1,323,2,1,1,1,13318,13318,323,6790,6790,6790,323,323,323,1,1,1007175,1,323,323,323,323,323,324,324,323,1,1,2,2,2,2,323,1046600,323,323,2,121197513,2,2,2,323,1,2,1,2,2,5638,5638,324,323,323,1,1,1,1,2,2,2,323,14854,324,323,1,1,1,1,1,1,1,1,1,2,5637,324,5637,121197513,5637,2,2,2,2,2,1,22950184011,2,2,2,2,2,2,2,324,323,324,324,323,1,1,2,2,1,2,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_3 : TreeValid ⟨m4,none,m11,none,m3,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149a49a4134924100904800900004126904924904c349001a4930104937980046de6d849a4104924d209340008449a4126904904934c24920180126900524924120024000104d24836924c24124924d00020d269049248368249a4014004924924100800800920004100104904904c000000249001040009340059a4124800934936000100037980de6d84104924124d200009b61049a4104124924934c200251a4926900526da0da4c00104db6836924c24100024d00d669049269a4d249a08049000279a4d269049b69369249a4014db7846db6000124904d24904036db0db6db0c048008269a00001269a09a69a08049248300008269a41241208209a6900494db41049249209b61008269b4136d34904934c36da5000136d040049341249200009360069a4136d24904934c30c24da0936d049b60009008001349205249041a09a6906924936824da4104124da09a6904d24936824da41241200248208049248049249208008000001b6d86db6db6c249a01a69a0804924926000a369a4124da0c24926900924925834924000120800120b34824c60d24800104924b06d2480002692000692cf209340009259a41a68001a6b3cc24980120926904124904920024926906db61b6db61b09349211a49208049a4906124934c34da0026926984824934930034936d00826000824e201000000209841000001849000049a00389a4000924037924800144d40c04127106928000826e30da6c30d24db6104924924924100924904924804824d2c904c019a4164104134000034d209268001049248249200041349209248001048209809049a4100024024906900900d00c00180120824000834904000d01124d361041a0100134800020134800800006808120020820d008009a4024820904d30804c00000826800920824134d20c30f01800db61a4124d34964104024920924800104924124920120924824824024104024120826904924124d000009248249a00041349209a4800104924904904000800066004907984834e209061209049359001359200009a0000820c30d34004de48041269a00369a000080000c030c30c04d00c04126100000000db0c301340340049841029269a0de4b0490592692080033686cc30c36c00006db61b6d80030924836920004124904924000824e209b48000049241249000200019041241b400413612083480002410c80080000c80c920e201249249049249040248000041069049241249241209249e0db4900004de5860124de6124904124934846c00034d37984924124124d208249000409e71049a0c34126da09a690782cd24126830d049b686482cc00004d30de600183cc36020830304100036186180c00004936d861b0db6d85904924004924920934d209049448249041209a6d048009008009a4104c00105904c000240209009049241048249841249041209269049209b6c30d86db6c26db6db0036db0188d80c00d461a09b0180134c00060030805900826c06004180d36d80034906c04d64124900104d248249041209a6904924824124d20924904824da4120824020026904920024164130d24004820024104120020824904924800904d3482481052492410cd36800004100004d069069a41b4d00020934d319b4d00004de6001b359a6126c00138934836d80047136d84920034124d20814924124030124984124d24c36d24830124db60011e4dc6120400104d041040069800209a61841a68208269a61000249a09a69840209268269a6100824920926984924812534d049249048269a0da68000049a68269a6820100024d001e6d84d269a0924920984900026da09a69040209248269a40125b8c06286f3ac36d80040db6d86ec78381eadb0db7830006de618033b006f3d800066d801b6d86dc6db81e6db0c319b6036de634b06128ba4b030c061b0f36186f36c141249208200200001049248249a48241271001c59200049269800219269049248248249a40249349619b092000482000482cc20924824c248241249ac034b200009a68061acb3c8349008349279069a0006aaceb0d24824c249a41049241248009249a4124d24806924820124d27800124de61209248249801a0936824924980dac9060249a49801a69b6c240a08008049001048249240209a4130c36030036d84106804004d20824020026806000120184804830db6030036d80924920024da0924924804934826c30f00c00c361049240240001249861241a4006124800124c360011e6dc6120924824800026930c24db6c36db6c361a4980da6906024806000030c30c240a4964934930004aa4824d26824106d80180db01849a4820000f20b240260268001b6d86db6d86c649200249240209249049a4904820104c04824d201b6006036c06000120024834802524904930034126d049a09301b5920c04936db00371b6d848269b0c36db6d06db0c36036db09a7936c26d641b6db6c00db6c081b603d9b6d86826c06004d30c30030366006020830180100035935249249049248102414924824924100924820900004134900934804024920034900904800924104934c20824120820804980100d359a4106134834926d048001009a49a4100024820926900926904800000124920024000104d20820900004000024820834820180a20824c309a6904120000800004d04d06900000100820f200001341241a400000602883cc04004da0926904124920104104024920020000104924004920120924800924024104124824926900024904924d30104d20d249b6128920124900804820924124934800066c04937984824900034900004924800d240241008008049061000009a0824c20c30126124984006026820930c34c04030820000924000820120824800d24024100c04d04126100100180820c30020030124186104000d04d24100000124924d0080002013480080000c9a49243209349259a41861b6db6d86c00036db6db0186186db6db6db0000db6e36c36124924934c000471c5541500006924d34020000c34db8d34000124a3c904844d44d27102000d34d04100000124d24d0080006013600000000c9b69263209349659b41041249049048000249269a0104104924924920000924924824124924934820834d409e11000049a6d34000820936dac9240001a6b34d060669b49359041049241241200009249a6804104124924924800024924920904924924920000d80d80100000026804d000000600368059000069a60341809a6d64d64104124904904804120820000904924934924120924800824024124d249248105249209248001049248249a48241200249249208049249000209209269049248249a49a4024934934920004924824d24824134820924800100000920920f209269a413498002080000002c830800804904926100000180820e301249240249a41049240208249249a4124924021836d24de6120924804024820930824db6c36db6c361a4906da4984824804000026830c240a08000049001000049249340208209340209240001249a49048349349279048a25208000000001000009a0d340008219000201640000269b6d00036db593510241492c9ad96c300924836920004134d071c4e24824920db693090c9b6eb6ed7a8a0269e4d34900006920c3d808f3ceb08001809019a4006060f60f46c04166064827500925937b2d860124904924000824920db69309069a0020924020920800120b36834d209a4800104926f368269acf301058009359a41861b0db6f3cc00830124da6904124b27b2590c034920da4c00004d341e69261609240379268001061e4034967186db61b6dc61b09ac9a0f34b34904187b011e7a56186d860361b6c00060db6c06184db6c36db6db6026960da4d000049241a4900020924c349300041a690482090480c3641b4967180820006a24c20007030d269b416492000ac36db6eb000d9871b79c610c000d04d34100000124d24d00800060136c0618000c9b69263209649359b41a49241008001000200019e69668001041260040248000679e49a180cb2692cda0001980934100020900924004800030124c061008200209240209b49259a41040208241008000608258009041048001201008200059268041289e4f34c00064d24d00100824124900120104c24930c24020904820904864d649271004949240049249209241008369a4134900904a54c24920c30936904800900980184209800209a08c00020026900904d36db0c479b71849249200269a49009260009b6934124904020da6904000000000104026820106d34804000020000900db0006db6c30800000000020846d80036db6d869b0006db49a0d361008369a41b6c001b6d26824124900145924824900020f669049249c412cd20924930824da4120924d209669861b6db61bd1b0c319b6038de61041260268248049e6db6f07b36c269a4de0b64904824931404936d04924930024da4100930c069a4d00924980026d21836930024da4036d86030db6c00000004900004000000004820820000020904136db0c079b6d86db6180f349a0db6c301a693610410432412492000080c96c9a4104126924a050000219a4946904a34d34920000100986d340208241001048000041a0db6d00820900020020d369b69a410410c905925804104b21b679049259e492cd20924b66824da416cd34b648000419c75b7580006036db0db00019b7466de6000186c36db6c36dc79b6d82001931124de6000130d269b4800024160a36980004dbc926da19c6db69641249105249001209a69049248248249a41000209249a09049248249248241249269a0c24924904824900c34924d04924924c249a4100800d049241009a0834134d20d248241248241200000309209209a6c001a6926834d041209a6906db0006db49a0904924924020836924824124920924824926d84934824db6db6c36c36104006c269208249b6d861bcd26824080034c34924d00820934104120000936c249a4020824c00900834d249a69048a0860944935900004824924d20820944d26d240001249a4934834d64924d0252240,1,2,2,872007,1,1,1,2251445471522383,14277,14277,1,2,2,2,2,1,1,1,1,323,15045,2,2,324,323,323,323,323,15045,2,2,2,323,1,1,323,2,1003079,1003079,1003079,2,2,2,2,2,2,2,323,23206535116,2,323,2,2,2,2,1014344,2,2,1,1,324,1,1,324,324,324,1,324,1,1,1,323,1,1,1,1,1,1,1,1,323,1,324,2,1,1,323,324,1,1,1,1,324,6214,11589,120997514,11589,120997513,2,2,2,11589,1013831,324,324,2,2,2,2,2,2,1,1,1,1,1,1,5637,1,324,324,324,2,2,2,14277,175688,14277,14277,14277,11589,11589,11589,175687,11589,175687,324,2,14278,2,2,2,2,2,2,1,15045,1035847,1,2,324,1035847,437831,1,1,306759,306759,1,1,1,2,2,1,1,323,1,11590,1,1,323,1,2,324,124156553,306759,323,1035847,1003079,13317,14278,15045,2,2,1014343,14278,14853,11589,14278,2,323,1014343,2,1003079,2,2,2,2,68,1014344,14853,323,2,2,324,1014343,2,323,2,324,2,2,2,2,2,2,2,2,2,2,2,2,323,2,323,68,2,323,2,2,2,2,2,6405,306759,44615,2,323,15045,2,2,2,15045,15045,2,2,2,2,2,2,2,2,2,14278,1,14277,1,2,2,5637,14278,437831,2,15045,324,324,324,67,67,2,323,323,2,323,323,1007175,2,2,2,2,2,2,2,323,2,2,2,2,2,2,2,2,2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_4 : TreeValid ⟨m4,none,m11,none,m4,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x14924924924924100924924924924822934d249240000949a41049249205249249049248104a48a48a4934d34930c025124149a49249241009269249349248249229c6d349240000940049241249205209249249248104a48a48a69b4d34930c025124149259b6d34000124944d24904034936db4d30c049a69249241041269a49249249049248201048249241200249209249004949a41049249209269249049248240049241249209209249049248220001240241040945104a48a4880804100904102512404924924924d241009269249241041a6d36d349a4824924924924904494924184d249a09241048249241a6d36d049a48249249209249005148a4924965934900002512414d24924d600009249249241041249249249249059249259208209e6926964820824d25124d600004941249241208201049241241241869249048208049249049249005b7934d358008148a49a7134935800822512414936db6db4d30c04924924924100924924924924824935964934000124924104924920924924904924820936d56934000126924924820834965924904104924926924920f36964b64000164d369a6924000124000100000104020924824824804165900805904924920924920094db0004164920924104824924124924920924904120824124920104124124924186c20904926804924904924906db0004d041004959208241249209e6c209049248205b7800d059348148a49a4000904104800804104904102512410492492534d349249048249249249041049249249249241249249249249249049041249249249041249249249240124920924925249249349269e7920804924826d2492492490692492492082092492492492482c924924924904da49b6924d24146936dad930c05920924924924900824920920920c249b6924d24124924824924802492412494934924da400012496593690000cdbcf66f300009b7964d24000336f3d9bcc0002ce3ce36f300019b7964d640001679e593590000c1bcf06f30000000824024124306f3c1bcc00020800100904100925965b2d860124924924820824924934924906924926924920964924924904104924105800d2596410002493492490412492493cd04104924924d24924124b379c6db6dc6c259e79e6f36186124824964d34900004924924920820924924d2492412492492492482496492490cb26496180c000000300019e6de6c00186030d86030c00036de79b0c0cb26b2cf30001934d241000209249248248000249349249008249209249209249259241861b6030186c000679b7986d86186db6d86db0c30db79e6db633cde6f3cc20864d34900d00824924920920924924d2492412492492492482496492490049248,1,2,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,324,324,1,1,1,1,1,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,67,67,67,67,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_5 : TreeValid ⟨m4,none,m11,none,m5,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_6 : TreeValid ⟨m4,none,m11,none,m6,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x144949349249600009249a6924820124d2492490401252493000496592052690012496480492492c9269e0000935934d36000126b24a26820824934d459b0c049259349340001249a0004934920924800186b248205145b79b6db700002492c9249208025249249249040129c7000104db4814924004125120124924d34d24980004926926924180924d24d36c30124924934d30c04924812924924d24104134924924904904924924924924100924d24924904010824804900920400124d24824810924924924820134d34da6800024926924920804924924925934924100924824924820104100000004820804924900120124924924904024924934904104924924924920924924d249240a48a2534d049249040124125249269a4924904104d24d349241009b69249249241249249000209249049248008249240249a4004924d209241349241000008249a6924820104d24924904024924930004934d20926d00124934802924000824924124920000124900824924900920904d34920924000124924824804134d35804d04924004924920905924100964134d00124924814924004924920510524900124924824900000924904924004124920924800c249240a4134904024900824924900920104d24d30134084124934804d02524900124924812404934934926934000926d24d241041249249b49840249a4d349249045149300069349a09240008249241349209849b4c249a00001249005149249249a4900024934d34900004924926926920d34934d64830124964924d000045248001a49268149240061249204149249b4920000924924924104124924924944c349249349249079a4965950000926926db49e0000510100800100820104924124124004120804004004924904924900d34d349240001a6924924820834d3512c9841049249269a4920f36dbcf38000134d34db89340001240001000201040209248248268041341008049049249209a4920124924924c00014924924926920d34924d349241e6d349658008249a71b6d268208244000208248208108048001249204249249249208209249249a4924834d36d2c904104d36db6da6f00004d34920d20904100824920920920dc6006c36186124924824924804936db6db4d000049249269a0000924d34d340001a6d249a6820834d24d35120c049359349340001269a00069a49209240001869a4820936d369240001a6924924820824924926d041049249269a4920f369a6b68000124936db6924000124000100000104020924824824804104900c049049249209a49200949b0004124930934000824924124d20904934834d20000124900000920100800104124124924006124804034c04d24d049249049b00049869805159b00041449b09205a48001259a4c16924004124920804024824820800004d049249001249209209200001341641041a48001069a6800004904d041045a4c00106d36814410512534924934c008249269a4920804d24924926120494934c00307b64814924004125920112524924924904024934d24900004924924924920924d34d648301249649449000045249001249248149240041249204124969249269200009249249248201249249249040149249249241004a4482492924d24d24000124924924904024934934d20c02924924d24830094490524b24934d38e44d44c251249b6925960924d24d24104020b20224028820824924904900004a219301000009259241240249249249208049249269b0c209249a49249a41249249249249249348209209249209841049a0830d208001249248348049269269341809249249a4d24824926924924934924904924926934d30820924104124180024934904900534924924904024d24d24925920924924924924924924104904924904c20824904104904000924924124012924804926804800020924924920804124924926100904924924904024b36d801b6f36c24092124b3af36db6c00024934934980004926d37134000924d24d24c301b6db6db6d86034d26de59a0c049a4d000349c4909a6104c24d240924800d24934014924924d34d240001249a49a4900024924934920c06db6db6db61809249259248301249204b5134d36d30c069a4928920820d34d44de6d34124924a2492483cdb6db4d30c04d249371b4d30c04900004000004100824920920920104d04000d34124924824924806dbc9b6d26000d34924d241041b6d269b4db4c34d249349249079bcd369b63009279b6db69361809a0000800100820104924124124020120804004034924904924900924924a24820824924928924920d249c4d349241351b6dc6d34c30134d24824124924020924824824836db01861b6d849249209249201b6f36d35200034da6db4d80006db6de4d48db0d36926926c301b6f36924d8c0249b6db6d64d88034d24924934904d349b6da4d241b6c04da4d80000024104004906db0034936000000124120104026d27134d249069a49289208211bd9b8dad9861249249a492482cd26d34d24904d46dc6e3cdc1005920920904924900824920920920c04806104d24124924824924804924924d241041249249249249079ecda492c3209279e6db596c180924d24126926120104924124124186000d248008249249049249004924149a4924930000524924924904014d34924924100892520004124104120504104924904804924924924100924924924104124924924934824924934924902924924924820824910824104924920400124924924810524934935030814924d24924d20536d249249248225128061269349a4c141249249249040249249349041049249249249209249249249240a48a25124149124a00049249249001049241241240001249249248041249049249029249145105041249249048041249049049049249249249209249241249240a48a25124049249a69a6180924926d24104144d36db4dc4c34d251b6924904934d269b6180924d349ecd86036db4d36d800069a0834c049b69a0924100924d240001b0d04ac7004134004134d00924db6db6c30124924924820824926db69369089a4926924920934d24924904104d24924924104124104c00924d241000341049049041249279a7986034934da4900004d34de6927160d24d36d24c30165b659a4f6d824d351669295609b6e36db6db9206c20960126b36c20005004128d30826934d24900004924926920820924d351241042269249a4924824934d24904924920004004980980000d64924800000030d04806000034d34d30c069b69a49a0000d24924100020924924824800034924904900824920924920924924d24000106d26826000034d249049000041b4d20d30000d34d34d341a49b6f24800034924900100824924920920104d249241040209249a4924824934d24900524924924c00814924924924120534d24924904022494800104904104814924124924120124924924804014924924920920524924924820834d24934904102924924d341041e7164935800064d249249041069a4924930c20400120924024814924004120920412494d34da4d269309144a0924db4d26920482492924924d34924124924924924824924934924902924924d24924094124924924920490524512892134d26926986024d34d24900004926db49271b0934d34d64c30136db4d36d800049a6986106d26da6800000124934906936db4d271c0820c04d64d34026936937980004924924920820924da49b41042269249a4924824d34924924104134d24924904104904100035904104000904134924104d251a4b26180d359b4ea4104124936d249b4c2492693492490c926db6db6da6dc61bc3041c4b28db09a4d01164a34c209a4d34d64c301249249a4820824924d44d249069a49269249209251b6db6db6db612492412692c900024d35924c00824924920920000935134924020924824924824924924904000934d64834020924924824804124d44d2490082492692492092492492401492c92d96c300924926924104134d34dc4e24824924db693490c924a24ad5a8a0269e4934900006920c3d808f3ceb0904100901924006030f60f36c04124064824900925935b2d860124924924820824924db49369069a4926924920934d24924904104924105800935924100824124d24904124b25b2590c0249249a4980004d24966925160924927926820124d24d269371309ac92cb34b24904904d06024134c06de4d36d841049a6d34d26934024964d24d000049249249208209249349341041a492492492482496492490c9245141008001000200019669668001041060040248000259e49a080cb2692c9a0001934934100020924924824800024924d041008249209249209249259241040208241008000649259849041048001201008209659269241269e4b34c00064d24d00100824924920920104924934d240209249249248249649249004949a00049249205249001249248100049241241208209a6924824104124924904812524d34004924920484924004924920924000824924124900104934824920000124900824924924100924d34924800000124924924804134d35920c04905924924800112524800104924810524800105134814924004124d204001209049248208209249209025041249249048129141249001249248249000209249049240041249209248008249240a4934924920000024924924100104d24d34830084124934920c02512410004804924920104020024904000120104924804120000124904924912510820824924924000100104904c208209249249000041049241309249249241041049249248041008209241049241249249209248000249240a48a2512412522482524800104d34814924004124d204001249041048208269a4920904104924924120494936d00124924812124900124924814924004124920504124924924800034d24904904904924924920820d34d64d341000649349049045248001049248124124900049241001208209249248241041249249048141049249241204a6924004126920482492000d24d34124104124924924820834934d34d02820924d24d34094490400320224f268000241249049000048261349200009259249243249a49248208209249249000048249041208208249249a40001249249048249249269041061269369a0000904d241241041249a4d248000249349249049269269a050410492490480002412492490410412492412000092492492412492492481289208,1,1,324,306759,1,1,1,1,1,2,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,324,324,1,1,1,1,14277,14277,14277,324,11589,11589,175687,11589,997447,1,1,14277,2,2,1,1,1,1,2,2,1,1,2,2,2,2,2,1,1,1,1,2,1,1,1,1,1,1,1,324,324,1,1,1,2,1,2,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,2,2,1,1,1,1,1,1,324,1,1,1,1,2,1,1,1,1,2,1,1,1,1,1,1,323,324,323,323,1,1,1,1,323,323,1,323,323,306759,1,1,323,1,1,323,323,323,323,323,323,323,323,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,323,323,324,1,1,1,323,1,1,1,1,1,1,323,323,323,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_7 : TreeValid ⟨m4,none,m11,none,m7,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_8 : TreeValid ⟨m4,none,m11,none,m8,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x149228a4924924d24100936da4d240001249249249248148041241009205249249248248104a48a48a4924936904102524924904924812414b24924924924924104124924926924904034924124100924924004124124924920904900494934924924100d36d66934000124d24924924827126db4d349028a5947964d24000114104124924920504d249249248104a48a48e79e6dc798000251242400492480002090492493490482403492492410092c23cb069200009200049241b4d209049249349348048249241009209269249248248228a40041241249201041000200001209249249248143041241249205104a48a4884124930924902524924904924812404924514924db4d34100926924d241040a49249249249041201201240009249241041241a6d36d348248249249249049005148a4924934934904022524924804924812414924924924924924100924924924924824904924100920924924924824820494d34d34920000926924924104135134d358300249a4924904904d34924920820515935934920000d369249241040a4100124824924186d24924820804024900924900926de6f36000134924d36d24d24000134924934904104100d040001041049249041049041148a4964924924c00824924924904102512414100000124020100924104924124134804164804024904904900c049208249205100041300041201041240249040a49249009249041001201248208601248209248205b7934c319348148a4984d2482010483492490410490242492480492481241049249249280410492483482492492480c306db6dbcc24092092492534926967920804924924904924924924824824924934904104924924924924924924904902500804904104104924904924924924800924924924904924812412494924924924100924924924104134924924904024924924924904924924924924920c041241a69241808209241041241000249249049009269349340001249a4924904104924d369249241041240001041041041041249049049041249349249040249249349041049249249249209249249249241249249249249a49248248269b4934d30c04924924924d24124936da6da49349049249049249241041249241200009249249041041249249248000249249249049249249209041049249848041249349049049249249249209249249249241249249248204a49249241208209249249349248240049241249209241341249241009208249241249209249249049248049261269200009249249849248261a49241208209269b49241208200001000001041201009209208208249248049248209249249249241249249b6db6db6db6c30926db4924904924814916180c000000300019e6de6c00186036d86030c00036de79b0c0cdb8f3cf3049248248,1,1,1,1,1,1,1,1,1,1,1,2,2,15045,15045,1,323,15045,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_9 : TreeValid ⟨m4,none,m11,none,m9,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_10 : TreeValid ⟨m4,none,m11,none,m10,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1449291493492592000052492496490402492492c9208049349200019205209249040648049249249a69ec920000924924b248208248208000009209249a6820824820514762524d24d44800012826b64a248240471a4800946810924924124120124924924d249b69000049049249b4924824812926924966d34db6c30c24db49a5926d30db6db6db6c30166d34c30c060259b49a41201001249269269a49269041049249249a49241249209049040249249001049049249248241240129249249241041349269249040349249349249049249a4924100924926924984024910c04804924920400124904924810524926924904024964d24904104924924924920924924d249240a48a4936d369b0c02512420924124920800804904104d208268049248241249249b49048241049208249a6104d20924904020c3d988f3d2b09240008251b4d208001249049348029249241049241249249009049049249a4100920934d26904024820824804d24920820924d34924000124904924810c34985924920510524926904024824964d04124904924924120920924924c241240a48a4900100800002400124904924812404934594934934924000926924d241041249269249248249a49249249049049001009a09249241041241349268248040249a4924904900514924924d26d249000249249249249205241200040268149249209209204149249249349a49200009249269248208208049a00009209249268208248204969b49a4930000d369249241041b6d26934834c34da4934d049069b49b49200005e6db6db7800c179b4d34d30000d36924924104120000000924820100124824924000126804124804024900124900db8de8f36000134924d36d24d24000134d34934904104130d04000124104d34904104904124926924900014924924924920924934d241041249249248208249e7964d34c000249249249041045040268249208149249201249204108048201009001009241049240001268048040040249041049008049b00049204601b6c301c6c141000001248001041240249041241268041248249249001249041000001248309205a4926c04024c169249209209209a4924820924824804020004920034924904104900924920124920404020c049208144105124a4535124925800814d24924924120924926924820134c268200648149249241219201125249249269349040249a4934d041049249249249204209201040248149249249209204124949144a092492492690448249292289412492492492049049253ceb8dcd280004926924904d3692490480d9b4924920d04124924924824012824904924820024924804000824924924920904924924924120924904900924924824830f361b6dbcc240921249a49a4d349b4900004924924d24830104c36db4900024134980004909a6d241040200924924c201340149249269249249269241209204925b6db6db6d86024d24de6900006db6db6db6180d24d26924d34904104d36924d24924186da4db4906020924d04104906c36924d24124034d24934d04104924934904924944924904904924925924924124924924924926924920920504000004920800c049041041041009b0124820924800da4db4d860009249349249061b49269249209248124124949a49249300005249249249040129e6924924820114d349249241004a00041241041205061209049048049249a49241009249249241041249249248348249249399049049229249a69241041249249348208108049a4104920400124924824810524924935830814924924d24d2052c926924834c379b4da7986182512806238de7830c14124926944904024934d249041049249249249209249249a49240a48e25249249b49248124128944900049a49249001041248241240001249248248041249001249049229145105041269249048041041209049049249249249209249240249240a48e25124049249a4924180924924924104134d6d934934c34d249249049049a49349b4d24180924926d24906034d34d34900000804804100920820924104124000126934804000024934d049009289349340001249a4924d04104924d36924924104124000104104124104124904d04904124926d24d06024924934d04104924924d24d20d24924d34124126934d36934944c24924924d24d20820120104024820004924d209208269b4d34900004926d34d24104124936da6da4934904924904924920004804124900000924d34904000126904924800024934d249049a49249208001201049a4004124934d04900004924124920104924d349241269249a48205249249248008149249249241204a79a49249208045349249249040128001249241048149249249241201249269248040149249249249205249249249348208224041269248248149249249249204124949144a0924db4d269204824929228944904925124920949a08000049205249241040248129e6920820124104120d04904c100040241241205041209049048208241a0920904c349041009204849249841009209249241049241249249048348249249001049008249b59241008001249649348208249a4d24100820924d3490400012496492481252482080092481052492480000481492492412012052c9209048040379840061a1802404120d04904812920804824824000024934900814924924d241201249201040248249041041249049249241209209249248241240a48801349b6920002400124934924812412c30db6c36db6000036c06db6c30c36db6db6d86186db61b0db0934b249a6104126904924804104900924904924924924920924924024924124934924810004804900d001041240249040001249048248041249001249049249125105041269049248041049009249049249249249209249240249240a48b2512420824920924900004824004c20820934924b2400012492483482492c924902482524924820134814924924920d204a79a4920804904400124924104814124924924120820904924824130d249040248121249269040248149249249209205249041269349248041a4934d049049249249249204201248009248124124949144a4924924920906924db4d20920482492922186db6db61b6094124924d2492049049251282092482492402092480400482492492492c9049249241241209249249a409208,2,1,1,2,1,324,324,323,1,1,1,324,1,1,1,1,1,14278,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1046599,1,1,1,1,323,323,1,323,1,1,1,1,1,1,1,1,1,11589,11589,175687,11589,175687,1,1,1,1,1,2,2,1,1,1,1,1,1,1,2,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_11 : TreeValid ⟨m4,none,m11,none,m11,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_12 : TreeValid ⟨m4,none,m11,none,m12,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x124928a49249a4924924100924924d241041249249249248149a49041009205249249248248104a48a48a4924934904102524924904924812412db4d64d240000a7134945920c04924924924100e34d24d340001649249249a4837134944d30c05b259649240001148241049249205001001049248104a48a48ed9649349000025124249241249a4d0002090492493490482d90cf349a0000924d300041b4d209349249049348028a4824924100920926926904824824b24104124920024104000104126920904924814b241041249205104a48a488010490080410252492490492481240249651cb26f3cf6cdb00009249259241040e49249649249001200301240009249241041241e6f3cde6c0c0649249649049005148a49b6db6f36d860249249649041025249248049248124165969ace3cb200009259349c41041e6f48db8c00c64d2516693490c9259c69640000a49200048249241e6036d86f3cc64d201009249009249a6a6490410596d9b8dccd80004d4593d934800124924b24820834f24d6c92410492492c92492010590000016412492482082480000590c90000092492c9209201148c49659b5900004b24964934900002512414d36106124da052493498596481082c000000b20921800004904104804004900c04020000904906f3000c1bcf009241058249040a492490092490592c10c124b20b205948a49b6d86306db6c34965900805902724924b04924812410492492524d24d34800024925924925940020924924924904104924924924924124906d049040249249041049041249249241240129a49061249348249249a492c9248040249bcf001b6dbcc240920924925249249b6900004924b24924f24104124924926920820dac9b6f34104124924924924834920db0d20c04924920820920824924924824802534920c34124d04924934925935900c04924812414924964d34934da4180da4926d24104124924964d26826da4b34d24904d349040009a09a4926104124124924934c06026da4b34d04900512496d349659b60001a49b6db6db6db6180d249a6d240001c6f66decdecc35924d34920c00000000024000d24904000134186db6db6c06004124d30804d00924926da400013493c92494cd04104e36db6db6c301249249a68208669249269249201040360648001249248208248011b6db6d86d809249269209201a492cb36db6db6d8602492493490410d924924d2492400480cc0c9000209249041049001b6db6db0db1824924d241240161801800368201340301049041a6806020da08249261a69b6db0000104d64d640001a69acdacb00024920490492492564944de48000249e6db6de6c30c259249279208209c79b6db6c00024924934904104d24924d24924184986d849000049249041049061b6db61b0c30124924124124012804800024820824924b04b2c9a4800024924092092492564924d36db0c04934936db6db6d861849349049049248248249269b6d00004924f24924f241041249249269208209a49249a4924834930db0d20c04924920820920c249249a4824802504900c04d24104924904934934924804935934d00c04924812414934934da4104124924926904104d65124d200009249a6d24000124d34d34d300009249a6924000124d26da4920004134d26d240000248260001241341041b6c00020100d8080410053ceb8dccd80004924964965934c00c249249b6b241041049049a4104804924924924904124924d24924014965925b24104134924934924904d34924d34924134d24924924905921824824924920800100124924820934d34db6000124924924004924d24924124164964936de4820824935964db6c0002c92493c904104924924d249241049b4de49000049249001049061b6db79b0c30924924124124024924936db6db6d86184920924934924904904db6db6db8206164924d20c34c24937131030c40a6cdb4000160924de4c0006002c9399009249249248208249249249249209a49249a49248269249249249209241049049249241000200249249040a4924924920c049249249208209249249249241249249a4924826924926924920924924d249241249249249248249249049241269241800019041041e61049249a4d24824004100c20904104984db4d06036db6db6db6d84187904d659e61248208209249240001801b6db6c000200349249008208209241040249248209248209249249209208249249a4824820924920920920104904924936100020024924904004d04f24936124124106180904104d349b6d24d241061b6d861b6d84db6db6db6db61000661bcde7984800900d24db4c2000400492692082490490080010092492082492092492412412412492482482482092492692092092492412412412492482482482082082c9249049000200349249049004a49a41049249209249249241208209249249349248249249208241249209249249049248069a6186d24db09201208209200009249248249248269a61869249a00041041240001249261869249a09a4924984924820924924904924924904024924124924920934935920c049248161b61e61b00009249261b69b6f20000034d24d640001849acdac8000249209249249049a69a49860249241249249b6db6db6db6c30934934d30c04924814100120100000105800d259641049249a412482c104924d24924104b34e64b0c024924934924906920c3cc38f3cf30020820925924000330de6f3cc0002006492490049248248,1,1,1,1,1,1,1,1,1,1,2,2,2,2,323,1,1,1,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,15045,1,1,15045,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,2,2,2,1,1,1,1,1,1,1,15045,2,2,2,2,1003079,15045,15045,1,15045,1,323,15045,15045,1,1,1,2,15045,1,1,1,1,1,1,1,1,1,1,2,2,1,1,1,1,2,15045,2,2,1,1,2,2,1,1,1,2,323,2,2,2,2,324,2,2,2,2,323,323,323,2,2,1,2,1,1,1,323,1,1,67,67,1,1,1,1,1,1,1,1,1,1,1,1,1,1,324,2,2,2,1,1,2,1,1,1,1,1,1,1,1,1,1,323,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,324,2,1,1,1,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_13 : TreeValid ⟨m4,none,m11,none,m13,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x14924924b249249a492410092492492630412692c92496482492492492c90012480410012092493410602412692c9248040249249249009009a4934924926924904044d24924a8c104924924924d20c0492010400486924b2002c1004924924920d208249369279a4930804924b249241009249249380041a6d2c924824824926926920904d4d966934000124924004924d20924104800824126920904934824920900120900936db4d2400013ceb6dbce80004db6db6f38000164934d36d240001249249a4c008249269369801049269a69a40200001000001a40249208200348041009000008049209a09a0c2012492492c9249040269249249249209249a59249000049249001249348349249241249208699b6f37a36f60c00e36f36db6dccc36dbda36d80006f6ce36eb0000dbcdc6db60001b8f31036246dc0e36f36d86dccc06d341841249309a6d26904934824934d00126d04904b2410092010492400080402010c904804024900120900104934004124920d34104828984128920904934824924d00126d04934184124930db6db6006db61209b69b6000186000000036f3cdb8c00006d879b6d8000492412492492c9040248269249241209209249001049248249a5900004904924924124920934906104924c348104a48a48a49269b6980104936db6dbcd80184936f36db6e000049249269300209249249a49048309309b0920000924820800d20db6c36c380061249248248348025249249009609b4900004934826da6d80006180c00000dbcf30db00001b61b61b6c00124902414d35964924924d24100db6b2cdb6000164924924924824924904100100000000000904164924924824800000020924100924934d249249a40001b6d34da68308349249a6904104d241000001241349249861049040a4924d24924d26920806db4d369a0c20924936924924124924c208049049249369241241024929a69a8db6000136db6d34820824db6db4d208209a6934d34d24800026d34924924100026826824820034d20800024826d34924100920094134104120000000800000000130da0c36d000049240268269a60201249201b69b60041041b69260209b6924820034f3ce248000069a6da49208049240869a4da090410492492092cf36920000924900494d349249241009a69269b8000134d24924904836da49a69b0c049a6936db60001671e71b71800059b79c6db6000124104124924120000000800c24104d049249048000000209301009269e6b240001249a6db6da69861069249a69a4820124926d248208269a49249269053349459a41201209a68200241000000000048008249249008009209349200200a49a6da69000049269a49249b4920820924926d249048209a69a6920804000000000120824926d24804802db9b3db360001349379449479a40001269b6de498610c100900000024036db6db6db6c069b6d841869040a29a69a6924820126926d250308269a49249269869249b4926d20b36db6db7830c269248209a69248240000001001048269a09249209049200349240200a69a69a49208049a4934930c209a4926d249b4826db49a6936d30924920000104004120924906d24904804134124924100c268008000001309a09a69b08040209208208241340019c6de78361240009008008241008249269309001a69a6820120026920c201048008249249008009249b49201208061a8821806000000020120100180b209b00000208209a4924020900d241048069a0924920900000004024020020920b24926006028821800024080024d269209009a4930804120824926d24804824920824134904120824906d249048008249269249000009a0860000900496db0004164d30d2600082c9a61349a08209b69840008261a08001008209a6980984db6106838d86136d841a0e36987930004164d40dc6186c3cde6120534900c469a7986d26d34936de69a10049b48141079859300001a68208201a4130db6c26d860049251a69a69a6020124d2049c24ce06db0001826800da00001009a69a69b0805836930dbc18013492000ce36f3c1b0000800da18241008209269b0900496db0006036e411e6030006dc6236c061c0dc9436d86030db718c9a00000300000001861b6000000036c36c3cc0004da000301bd204b20504db00069a69a0db618706cdb6136c20d86936836d861801b79800040061a49001b61060201b4000100186000806d86181806186d34184936d200000000041041b4d06124db4834d04130f3490793410586cd64120db6000c36dc61b6c30d86f36c36db0c361b6db0100186c00c00104d36db0036d849bcf36db0c00026d36000006dc6145108f001bd1841b6c00336f66c36d861b0de6d86db6186c36db6024f36e34d800209a4db8d26d309079e6de6d80007a24c06234db8c289a4db8126d30838d801b0e37986db0c361bcdb11b6c30d86db6c30f00030db0d840301b6c30186130dbce3cc363019b6d80030db6d8523c180c36f36104d30004127960db6186004d24136d861a09349049241a69b6924820124920db60000363241b6c30c06c38c36db0c301b0db0936030db8da60000249a6da4800006936db6980004924134c001869e5836d861801c6d84db6186c36db6124d04924da49b08049a4838d80180006d86db0c301b0db0db6c30c06c36c64d00c671b8db1800dbcdb8f360001b79b6e67000046db8e48db6c35900004104d26120030986924000100826da49208040309379ec1840061b6db6db6c00c36dc6dc7204924000820924824100824124920900000000004024006126d258308201849b6924d2003093cf2db2c006126d25830804d24f3693cb00206e38f36db0d240301871e7806000100124300800c24c00800800004000824120000104134984800c24da49061040309369249a4100c24da4986100186db6db6db0030db6db6db6124900020024820904000800924824012e36004c46d341b6c30d849a6836db0c361269a1934000006000000030c36c00000006986d879800071b0c061b7a30964144c001869e7836d861b0d34d04db6186c34d34124900826da09b0804924810524924924900926904900800180904104935165900b359048248a4924900926904924930db6f36d803009269b69200009249048a0800180900100924924960c20824924b249348609a49b4960c21934930c679c79e198082402490c120db7866f37866124904b249048024a6de59309b5904db4db0024920db6186c36e36136d36d84924865930d86330db0f00c30c300000009b6c30d86de6c2590240,13317,2,1033799,1033799,13317,13317,2,13317,13317,2,2,2,2,2,2,324,2,2,2,2,2,324,1,324,1,1,1033799,1,2,2,13317,13317,2,2,1007175,2,6213,1007175,13509,13509,6214,1,1,1,1,1,1,1,324,1,1,1,1,1,1,1,1007175,1,1,1,1,470348519039860177969558,1,1007175,2,2,323,2,2,2,2,121991113,571463,1,1,13317,2,2,323,1,1,1,1,2,2,2,2,2,470348519039860177969557,1,1,2,2,2,2,2,2,2,1046087,2,2,2,1007175,2,2,2,1013319,1007175,2,324,2,2,2,324,2,324,2,2,2,2,1015367,2,2,2,2,2,2,2,1,1,324,323,1,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,968263,968263,2,1,1,1,1,6213,899399,899399,324,324,2,2,2,1,1,1,1,1,1,2,1,1,1,1,1,2,2,1,1,14853,1,1,1,1,1,1,1,1,1,323,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_0 : TreeValid ⟨m4,none,m11,none,m14,none,none,m0⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_1 : TreeValid ⟨m4,none,m11,none,m14,none,none,m1⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125149249200241209249a4824020124924904804814100004125920564936d049648249208209249044845149249241009209249249048248249241041249201241240001041249249049248144904925249249209069044249209040248129249268249a41120924a492492412092088490410080410252492490492481241492692c9200049209a4b2480092482692000c120920d059340009241a4020b0482482490c9a00249209209249249248201a4124924920906904924820824824124d248000348249249209209009b4924120d20836c36c00db6c241a49a49249840268249249241209209a6904184926834134900004904924924124920820124984824824814924924100100934934924804024d24924104124165934800034834924904104904820820924924100020024924900824004d24d209204a4920024924904920824134d20924904824b2412492090493482092082010002092410482c9a41a482080400482082400492d92092690248,1,1,2,2,1,1,323,324,1,324,1,1,2,2,323]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_2 : TreeValid ⟨m4,none,m11,none,m14,none,none,m2⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_3 : TreeValid ⟨m4,none,m11,none,m14,none,none,m3⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x12526d06104924c100049a000492092482482402012412490400481480000412492052490c1049248249a0820924904b341841249204825a6d36904934c14924924124d20400126904934c24926920900902424130d040048129269248249a4136dbcc00936814924924124d20124900124924824904120924904924824124920924904c24924104904100924904920824124920124104024924104160034930004924810804805924100924924104924000100104934804124900104904924924104924020924820d34804124904124900804824924100820820d249040001001249248125a492482092481092682082482412092c9048040249209209209049209200240209209248200241249248000048249249209008049249241201a0926820824824104000104000824920920920904020000024020830d36c00d068241241049040248041249041249049249249209209249240241240a4924904124900824920824920104924104924080020834924102400100134924812414924004924920924104824904124920904934834924100124900824004924920124104024904000100124824804904100924104d05800924964112420900124924810524900124924824904120924904924824124920924904c24924084904100924904920824124920124104024924084160034934d02512424920024924904926904824b24124920984934824004004004c2092600082c92600010010483482d82c0049adb2092490248,1,1,1,1,1,11589,2,2,1,1,1,323,11589,1,2,2,2]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_4 : TreeValid ⟨m4,none,m11,none,m14,none,none,m4⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_5 : TreeValid ⟨m4,none,m11,none,m14,none,none,m5⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125149249249218209249a49a49241249249249348144a5900c341259205249249049348045149249249241009249249249248249259249240000949241049249205249249049248104925249249269269045249249249040129120924a49249249249208a4924934920c0251241492492c924920000924b2492482082493c9a4920820d37934924000124900000920920924820804824820924924924924820124924924926904924d249a48000269b4924d26d209248208248241b6c36c36c30c249249209209041249a49249a49060249249249249209a6d249a49248449b49349000048249041a482682692492412492081492492593c100934934924924824d249249241041649349b480003492492490410492183cc38dbce3082082092592410002002492490049248,1,1,1,1,1,324,1,1,1,1,1,1,2,2,1046087]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_6 : TreeValid ⟨m4,none,m11,none,m14,none,none,m6⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x249a4d34d26c301b6f269a68000249349349b0c06db6db6db0c30926d24d28030126db69b4c00034904004034924d04104104926920000904c269240001000009248029b6db6de7000c26db6db6dc00309b6db6de7000c26db6db79c0030f36ebadb80001279b6de79b0000826800d2082002d1d1534d000209b6c36d340000ac9bcebcebcdcac24b3c90cda4b34dbc98c184105a479a0030b24d2cf260003001349ec8049349269a08209249249a49269a00009249249a68208209a49200009a0824924820826820b38b24d28286326b24d38d24d2c80012492c9b49289871b71c6dc10301001240200000491c950494680492c984900800924db6025520124d249a4820824924a269a69a69000269a49a69249208208208060208209249a0920920824924da4920c049249249208209a69b49a4b2632c928b6c924824db6db692a0001a49269862b4924920030c36db8e36020100da49a68049249249241041249249249249049249249241041249249249041049208268249249208001001a49a48209249249248301251249a48000269a49a4926984934926d2818092c9ac9249881849249241269a69a48000249249249041069a4926920821134924d249241249249249041049249269208209249249241041a49248208040008001041041069248208208000200201001801a49a082c9a483c936f040000000009260209801a4900020826836db4d048260069249a08209001a492680002403c924d849a69a0db6db61041041069208201249241049241049249249049041249241049241049249041249048268269269b09001041a49248200068479349b092092012402000402002480002482682480090080490092010082090c00c90402080482082cdb6db61e61b79e6de6c241041869a6920000804f269a40001001b6924820004006d249200268208000008049249041249009a49208209201349241241241049249041249009249208209201249241049241e61b0de6db6c248001001a692482480,1,14278,1,1,1,14277,14277,1045063,14277,14277,1,1,1,1,1,1,1,1,1,1,1,1,1,323,1,1,1,1,1,1,1,1,1,1,1,306759,1,1,323,1,1,1,1,14277,1,1,1,14277,1,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_7 : TreeValid ⟨m4,none,m11,none,m14,none,none,m7⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125149249a49600009249a49a49241249249249040144a4900004965920526904124964802514524926926926902524934d24904012994094924924924104134d24938d04904924924924104124924924c30834d24924904102d249249241041a492492482081082480410492040010012482481092692c924834c249a4d34924100924924924820124924925830824924924926984924924924da0935136d26c00828e3cdb6de0c30924820824824104000000104824920920920984920920024020124924944904034d24924904104924924920920924924da41240a4924924904104924924920820d349249241040b4d249249041025a69249048208124169ecd249249241041e7164927000034d2492490410492086c82692c9a08208209259240001209e4f34c0002006492490049492410482492410412410012490082400492492012410482412400010012482480410412090490316d800924964114510524900124924834d04120924904924824124920924904c249240849041209049049208241249201041048241240841b0064924d0251240,1,1,1,1,2251445471522383,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,6789,2,2,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_8 : TreeValid ⟨m4,none,m11,none,m14,none,none,m8⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x34da4936db6db71b0c04934928920820934e249009249049024a5924d249249269a0821924924924924835930131920c049249208209209249249248248029249349249249a6820864d34804c649241240bcdc6e399b1004db7b6cf3cde0134d26d36d249069349a4920820db71bcda6d061a69249a4924834decdb79b00089269a4b20000d44d34d65830120900824124920106804c34d240201248049248049a6db6db00009269a6db69b69a4180924924d3410432cd26b6d926834924934924900000800000820924924104124000120a30c06004924934904901924946924db6934904d25b36de6c001a69269ac8060349e69b59600049240a0800c001a0104927b3c020a66104026d001049009049a00249201811bcc200500201248048248041e01b1800180920820024820104d04c600341a6924804924834d00c00124104d309b4004124102dbd9b6c4c060124936924db0904904d35806c600061ac92698c026834de09b1800d0413483400492412408,324,324,324,1,324,324,1,323,1,1,324,324,324,323,323,323,323,323,324,1,1,1,1,1,1,1015367,1,1,1,1,1,1,324,1,1,1,1,1,1,23214309964,1,1,1,1,1,1,1,1,324,324,324,324,324,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_9 : TreeValid ⟨m4,none,m11,none,m14,none,none,m9⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x125148959c4d35531420534936d349348248201209208059b4d300301205249249048348045148a49249249241009249249249248108249241009205249249248248104925245128248009248241920924a48a25049001049248124149249289a492c9200009a6924b248208208249200009209a69248208248209249249249249248201249249249269041049248201a41a49249249069041249249a69249a4906024924924924920820924984026826924924920920814d351269a0000d249249241041249249b6c30824924934924904d24924924104134d249249041049208048249249208001001249248204a492092692080492492410002092492492482412492490490482092082010002092492482000412492490400082180cc38dbce30920c0cc36db6f3090248,323,323,323,323,323,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_10 : TreeValid ⟨m4,none,m11,none,m14,none,none,m10⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x24934d34934db69000049349269a0820d27934e24104134904c00004904d279341841241024a4924934d249a4900004924926920820db79249a61041a69249a6924834d04000004d04924920820920db6d241860201a69249a6824802924924d249269240001249249a6820836de4b26904104124100000134146db49061049040a4924e36d80004924924db59000049269a49208209b69249241061a6d249a492483da3cdb6d800049269a4a200009000000249241009008241269200001040201240201248009248049269a69a69b6920000924924d341041a7b269b4c20834924934d249009a0800000820924924104134000326830c04004924934d04900924946d441041249269b6b20000924924d64000126da49a4904104f68f38db60001249a6926800024124000924934106c041009049040a4924000004004924824d80004d049069a00249209809240048200201248008248000000009040009208201248200341040219241a6924800924820800c001a4184902924936004d34124924924000164126d249801249041240000241001249a6800026806d0400096490400003000690612408,14853,1,8325,1,1,1,1,1,14277,1,1,1,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_11 : TreeValid ⟨m4,none,m11,none,m14,none,none,m11⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x1251489492496592000052492d16490402492412c920804924930001920520924904064802514522512824904924b2400614cd2496681092492492592009492492492492c920000924924b24820824924920000920924924820824820b2c9249249249a48201349b6d34c3082492c9249289051a71c49251a0104924820224134047030c3482492c9249008049209249200201249249a69249a6906026924926924920820924986026826924926920920814924924924104144924924924902d24924924104134924924904104910824824924920400100124924810524924924904024924924904104924924924920924924d249240a4924924904104924924920820d249249241040a2512424920924920804824824924824120824804104d208208268200001a692490400082186c82692ce309241040049b4d20800100124934804924924104924144924924904902924924104924134924904124900824824924920800100124924810824c35924920510524920904024824924904124904924924920920924924d241240a4924904124904924920824920d249241049240a240010012492481240,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1015368,1,1,324,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_12 : TreeValid ⟨m4,none,m11,none,m14,none,none,m12⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x22892d3592596d96d9a4860124924a26820834da4934924904100100020104134da490c9049040b4d369b49a8db0000dc6d24da68301a8da49b6d860369b4d369200009a6da49a4906036db09b0920c069b4820000920da6da09840268049269b8d200009b79b6f36c000249349b72368208269249251341042399c79b7040c249249249249068240081a41809249241041241049249249049009259a49249a682082492c934a2a906924926924921924924b2482082492492c924920924027824800104904020824830db61bcd80c0412400c9209200ac9e08669259089a40008249a0926c20da4934124820000920820d34001034d240269001a08268371b00369b0c008240089a018092780192480012490248,323,323,2,324,324,2,323,323,1007175,1,1,6790,1,323,1,1,1,1,1,68,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_13 : TreeValid ⟨m4,none,m11,none,m14,none,none,m13⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124949249249249249a6c30c249248248249a41a4114934944d600009249349b71b6c30c249249249241841249249249269049240041241009249341041a41049249249069004a6924104924d209269300009a0d209248208249a402690412483482692400492010092490448,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_14 : TreeValid ⟨m4,none,m11,none,m14,none,none,m14⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124a28e493496536492000492492c920820d24925924924324924b24924834964000804d04924920820920f24934324020324924b248248028a5924d3d93d924800124924b248208249249649249021001000201340a492490c9049020a2cb59651e490000492c924920820d36924d24924326924b2492486492c9a4b20000934d00834924d04900824124920f30904c24924326924800924804924d24b2682082c9249ac9ec9200009249259241041a99a4b64820824924964d24904820800000820924924104124000024860804004924964d049008a493c9bc926000925925924000124924934924905926b269248000229240219249340a49249309249020a2926b3cc2cb2608416518080550490c92002492010092402402002012480482482490006092500492082c12482092692582492412492480092482c9608609259849028a4d25924020134134924900904904d20001824930126b2680002c8349249609249039278218249640a208,2,2,2,2,2,1,1,2,1,2,2,2,2,2,324,2,323,323,2,2,323,323,2,1,2,1,1,1,1,323,1,1,1,1,1,1,1,1,1,1,1,324,2,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,323,1,1,1,14277,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem tv_b11_14_15 : TreeValid ⟨m4,none,m11,none,m14,none,none,m15⟩ true 104 hc4 [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 4) (a := [0x124949249a49249a4924100924924926004136d26924904864924924920904924804101920924904100324136d2692480402492492490c900924924934d34db6c000249249a482482013718c0009060249b4da4124100124924924924924980104924924924824124d06d0490402412410400c904924924924324014936de6db79b1804924db49241009a69349c8004164d24924804036da4d26900905b259b6934000124824004925920820000848b2410012090493482002000012c90052492712cdace0010cda4b369a4c2416d96d1a4d00004926d00020dac9049a4830824b24024924904004100000924820824b2612410010400402d90c0049a0000924920004035920926d041349e48049348258341009209acb36000b44166d2090480404622d9a0908904b240041249209a0000826804166d209049348679a1800126904b24184124931920526924924125120924d2490002c9049249248241a41241041209ac1049249248249a4126d0610492486480,323,6789,1,323,2,2,2,2,2,2,323,1,1,1,1,1,1,2,2,324,324,324,2,2,2,1,1,1,1,1,1,2,1,1,323,323,323,1,1,1,1,324,1,1,1,1,323,1,1,323,1]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11_14 : TreeValid ⟨m4,none,m11,none,m14,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine branch_one (q := 3) (a := 1) (rem' := 104) (cur' := hc4) (prev' := [hc3,hc5,⟨0,128,⟨0,[],0,[]⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed,moves16,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hm
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
private theorem tv_b11_15 : TreeValid ⟨m4,none,m11,none,m15,none,none,none⟩ true 105 hc3 [hc5,⟨0,128,⟨0,[],0,[]⟩⟩] := by
  refine guidedTree_sound (holesLeft := 5) (a := [0x129a25228a29249269240000a4d2c92492080482413412410092498c0001a40a4d24920806900524924934924924000124924da4830834d249249061069249369a49209341000001a4136d34c30826834d249041009020a68a24a6a269a4900002500d24904934834936d80126d029249a48248240249249249249269a0c208a4934d20920d04db4d30c209a08825229249249240000a4d249269b080294d9369340000a49200008009a40a4d20824926900534d24934d00004934924926000135124924906106aa6da692000092cb269268000248000009249a4130c301049a68041040209269020a68a24a4d249a4900802500180000000002824924db6db6e36db6c24d24e24920804daca369200009b49369248200a4db0c341269a08825b6d86d86dc6c26da08209249021009240009000a4c249208009829440008248000a4d20820926904934104124930ca0536db6d801b6d84986936000926135124d80100d06db6db0030db09a60008249200000200000208351041a09269069249300249209368308249261220a68a24a4d249a0800802536d249049448349208001289029248248249a4024924d241241a08009049208201008209049048200240a4935100126d048804a4894924924924924920804924936920c209249249249a41a4924da6924824924820806904db4d30c209a09249249240240829245245249249a4830812924924824824136d34c30826812094924924924c20124924924920804924924924da41249b69ac98602492c9a4920000920020024926904c30c041269a01249008249a4082924524534b2c9a4800012936c30d049a6812124da0c24926906924920da0980104d249369a4c24100d60da4d00004924d00020da69049249368249a4014db6db6006db6126da41a08049041249368240241b6db6d8cc36c26da0c20924900000800000820d249368249a41a4924c00924826da0c209249048829245245248208040208129249248249a41120129224a29249269240000a49249a49208041349241241009049260001240a49249a08049009245249269349240001269a4da4900104926db49a41801009340001a41209b6c00026826a24d841009020a48a24a69a6b3cd80002504d249049048000000001201028008248248240249259248b01a79b4d20d04826db0000820883924935946965924000124924b24c0082493696490010492c9a49243201009040001a412092482003484493d10430080492c9a4920f200a2924924934000134d249349040249249249308024a28a40008248008240a00209249209009249349240001a6926926800024924d249001049a69a49a6000724926926800024926d369a69a0000000934924824036c20800000000020d248209020e6db4db4900004d34924d241009a6d36d24c300a49249269a08024a2506d84f00000002866db5964d000069a4da49a0000924da4d340001269b69ac9860249249249208049ac9a49a6300924924926c201b6e269b6d880248a0db09a00000009a6934824820082924100000934134d241040048249248208049024a00209a49209820008269249240a00209a49209040049359249319b6d00000d040a09249040009061a6930c001268249261840009049a6c340009a07249b0c0012c806d84100000d88db6c30000f30000800924926100020024820900d30820000000800900b24926336da08001a08220e6db4f00034904d349241001209a6d36c201340a49249208069824a25001049249048000000209201028008249a48240269a4820004920924d040000341269a09800268249241208049049a8824180b209249048201261248a0000134d2010cdb88200008209a69048201240804a4914924924d249208049249249249241249b6da4906024824d20806904826db00009a09249249240240829245245129249a49248241209b6c000208120e5924d64db596492000492492c930020db693592c824124b2692490c804034100806d04824920800d20e46b3412c020124b2692483c8028a69a4924920804924924924c2411cf349a49200009249b6da69a4986020824924920900c30820000000924824924824082924534f2c9a498c024512830c20800000012126da0da0d00104db6836924c241208240208209049000659349611849000200240209049b68369248240269a4120804986db8c30180db01869869240241b6e30d8c038c1cc36c30004b201861040200001b6f30d8603cc20820024924904000800924824030c2080400002082002c92490cc36820006820882924534da0984026824512924824924824330da08000208120129359b6d36000124934d24904024936db4db0c029a69249260000a69a49249208024a49340008269240a4120820924900924b26d248000249271a49308049a6a369a41809249369240001249a6d36c00864da6da4d881069a8db89a0000526b36d24800024de6db49000049000008009a41208001801a682080402010c9020b4966db4d80004924924924100924db6d26c300a69a49b6d000024a69a69a4920802504904924904000820030d000029248369a4820026d671b59218049acb34b20000db49c6d6400012c9a6dac9060249269b4f30020db7b679b6c60126a38e2c988024926da49208049a6dbc9241809249e69248200a19311c5920c048200060068208829249b69240001249269a49208039b693493c0000a24a40008009208240a08249249209009249249240001a6924d28c008269a49a698010c9249b8a26120b26926926800036db6db6d80008f36926aa0000736d2692c800026da493490000ae3ce369200000009008008240000040208000000208240009020e6db6db6e00184db6db6db6c360a6da49249208024a2520020c269b08028269a49349b0020db69649a49a61a4926e2498482c9a4d249208049a6a269a4000b369e4924c201248a0000000820000838834924c20083937934964000326934924800824d24936d8618492cdac9a4021b36d2c92680003493400194496582402090092430480413093d06098492002c9a4020092800000824800104104d249048200208209208020008249248000a08209249209824a5800000d36d340a0800000904946000000000020820000020986104000000004820000800800920000000030c20800020020000100000000db0000400000000120840000004126806000000826b20b000001a49a4822080060db4c04904104124924120820c36d26d340a00208249208024a08209a4926982520020c249b6982820000030920920000836d24c34100006c209208200218249209040001808248208008309250261208211a492490400002c9248208208349249240ac000200826a20800860924d240804a49249251a69a0804d269b4db0021b24b669a5b241b6db6e3cd86014b2ce36db00009249a18269a69049a0006db69a1b24938825b240829245349a6d34c008245269b6f249060129268001b6da68120a4924924920806b34d36b2000092492692482412cd249a49200009b6924924c20138e26a2690801cdb49a4b200009a49249248201acb34da498c020824020820900f301008200000248009240240829a8db6dac80002453c9a49a4900024512830c0002c8000120e6d6593490000cd24da49200219a6944f26026138b36b2490086cdb4b249a0000d24900065934960d0002402490c120026844f21826100800b249008024a4921824924986b30006924d20d24860824da4120820020824900d20000c30820024800824024030c0c030c0001000c000004b20de7860124de41acb0c0249ac82cf300069269208829a8c061ac9b6824530806024920824506186b24926812b3cc061ac9a68120149340009359a41b6d861c6dd6c36dc10461b7184824934104100820930800000100124904804000024020800d04000000934024124904134d34866d21004136d04934104d34d209c6100c369a6124d24904964c26da5000136d00524d000271a6906920924c26980004c249369a48241249a6d040309b69849a49368249a4014134924d34100836800130000104d249349040001a79a48309058369349340001400061c61b0185836d34934000104d24934d040001e6d24d318040049041041200008041008261001049248040200001a4900100520020004000004c369b6924c241619a4d209800049618041469a0184d80020104000984836836924c2401c1bc984b20001836800926000106db6236c000001e6de4c2010d836de6db60001b49a000ca34b2c130006806921836000e04268304c001801e4da01005149b4104d3492094600083692616cd049049b4c255a18001b49041841341049201008000008061201049048040240001a0800104186000000d04030f06030dbd836de0c061a59059e6000db6d341205249000209a4984d24836824924104120000820184d248369a48241349679800379b51048029b6d04000934c229a69240009a40a61a49208069028000008249a40a4d20820926904b341041249204a0936db0c00338e049249060001b6134da6c00136866e26d80180d06c38e30000e309200008249b60208000000000268041a0926d049a6200024db05320b6e46180036de0ca69a4980006d824a00209a080480254cd04904934836da6d801249029b69a48249a40355d8c30006e3a124d369b0004da19b0db6e0c036c20120da08049048200001000008048088201a00b6da1800126d048829869b60009a40000001049000261a69a080690398693400093c0a20008269248200a00209249209040049359249204a09869240001241b0d34c001a8826184c0000490cc36e361809a0b30d2680012c8361b6d80036d88c36920006a200009249248000001041a4100800020824820100c30000000820730db0c0012c8261a49800049020e61b6d80036204c34d04100920d86d870001b00a61a49208049024800209a49208025001049449048000000201201028008249a4824026c34d300069a01861800001041b0db6d8c0288261a4d20804904c36a20000a209869e48201241200041269841208a0000126920106c3cc36180b209869348201240829b60008369a0336c00306e3a026da08209b69020008248008240a00209269b090200183693494c0a44a09b60009008001b8c00104da0826d80050dc4100db0000036820000824920924030c000268000000209248309000001a692682080030692692c826db00069a6820430c000001208000209248349020e7180030db6004e3410413a920db6c41046db80a61a08208049024a00209a4964902536de0c061b5b02867580064d35906e30004136a219d6001436d641b6d8018cda88269a0820924904d301808208209a6820826d24030c060000208208200249249041000069260208208009248240a6dbc180824b209a68309249240849b6000826938338c00306f6cc26da08209b69840008268009001200209a69b0984001836935b661249319d8e30c0033ae0790d986000d04134f36c00120804100d80000004c3cdb0000b21950001826d641000003069268649001809b6f049ac180024b2093cde10001b79840904a4924125120804904926a30004d20924b64824324124920020924900820030000920924934824924126986004926814884924924000124184124821866d24c34124db7860c06de41209245249a6c00134824520806c040208129248248249a41120a412492080490492492682412412cb249a0004b20986924820124130e26a0602882082412492080082410690402012480092482402080400402081cf36c30004b209049248201240829245209a48040268244209049a41048129248249a48241b0f36d8002c8120a4120024820804124800824924120820924924900820000920000924824924c241060009ac9a082000c1a4924b209a69801a49a681cf3000000482082082492492408292452480002482082450430c9a49868129b6f0c02092c8121249001a0926904d248368249a4104120020020104d248369a4c24100060da4d6d9049248679e4366200004104d3cdb000482016400602c000130f30c0002c864c000601a590400000c1a49a0d64c4602c9bc126b0800092c824f37840006de610240,2,2,2,2,2,11590,6789,6789,14854,2,14854,6789,323,1,6789,6789,1,1,1,1,6789,323,2,324,2,2,2,2,2,2,2,6789,6789,2,2,2,1,1,1,6789,1,1,806471,1,2,2,2,2,2,15045,15045,67,2,2,2,2,2,324,2,14854,2,14854,2,323,1,1,1,1,1,2,323,324,324,324,324,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,324,2,324,324,324,324,2,2,1,1,1,121988554,323,1,1,1,1,1,324,1,1,2,124877514,1007175,2,2,1,2,2,324,2,2,2,2,2,2,2,2,2,2,2,2,324,2,2,324,2,2,2,2,2,2,324,324,324,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,68,2,2,14278,2,2,2,2,2,2,2,2,2,2,2,437831,14278,15045,2,2,2,324,2,2,324,2,2,2,1,1,2,1,1,1,1,1,1,1,1,1035847,1,1,306759,2,1,1,1,1,1,1,1,1,2,2,2,2,2,1,1,1,323,2,1,1,1,1,13318,323,14278,13318,324,323,323,323,2,2,2,324,2,2,2,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,23215687756,324,1,1,1,324,1,1,1,1,1,1,1,1,1,1,1,324,1,1,1,323,1,1,1,1,1,1,1,13509,1,1,1,1,15045,2,2,2,2,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,13509,1,1,1,323,324,2,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,2,1,1,1,1015367,2,1,1,1,1,1,1,1,1,1,1,1]) (b := [0]) (by decide) ?_
  decide +kernel

private theorem tv_b11 : TreeValid ⟨m4,none,m11,none,none,none,none,none⟩ true 106 hc5 hp13 := by
  refine branch_one (q := 2) (a := 0) (rem' := 105) (cur' := hc3) (prev' := [hc5,⟨0,128,⟨0,[],0,[]⟩⟩]) rfl ?_
  intro m hm
  simp only [movesAllowed,moves16,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hm
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


def baseTable : Table := Table.empty.set 0 0 ⟨1,0,false⟩
def h0 : HistItem := ⟨0,128,startPos⟩
def h1 : HistItem := ⟨1,129,startPos.move ⟨1,0,false⟩⟩

private theorem solve_branch (M : Machine4) (hG : GoodMachine M)
    (hm0 : Matches M baseTable) (hv : HistValid M [h1,h0])
    (q' : State) (hq' : q' ≠ 3)
    (hM10 : M 1 0 = some (some q',Stmt.write 1 Dir.left)) : False := by
  let m : Move := ⟨q',1,true⟩
  have hm_cmd : M 1 0 = m.command := by simpa [m,Move.command] using hM10
  have hm1 : Matches M (baseTable.set 1 0 m) := matches_set hm0 hm_cmd
  have h01_base : UsesOnly01 baseTable := by
    refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro q a m' hget
    fin_cases q <;> fin_cases a <;> simp [baseTable,Table.set,Table.empty,Table.get] at hget
    subst hget; exact Or.inr rfl
  have hprev01 : ∀ h ∈ [h1,h0],h.c.state = 0 ∨ h.c.state = 1 := by
    intro h hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl <;> simp [h0,h1,startPos,Position.move]
  fin_cases q'
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) :=
      usesOnly01_set h01_base (Or.inr rfl) (Or.inl rfl)
    exact tv_b3 M hG hm1 rfl hv (fun _ => ⟨h01_1,hprev01⟩)
  · have h01_1 : UsesOnly01 (baseTable.set 1 0 m) :=
      usesOnly01_set h01_base (Or.inr rfl) (Or.inr rfl)
    exact tv_b7 M hG hm1 rfl hv (fun _ => ⟨h01_1,hprev01⟩)
  · exact tv_b11 M hG hm1 rfl hv (by simp)
  · exact absurd rfl hq'

theorem h4_proof : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := by
  intro M hFirst hSecond hRun _hUsed hForm hMissing hLoop hHalts
  have exclude (xs : List ℕ)
      (hx : tblOfList xs 0 0 = some (some 1,Stmt.write 1 Dir.right)) :
      M ≠ tblOfList xs ∧ reindex23 M ≠ tblOfList xs := by
    constructor
    · intro heq
      have hh := congrFun (congrFun heq 0) 0
      rw [hFirst,hx] at hh
      simp at hh
    · intro heq
      have hh := congrFun (congrFun heq 0) 0
      have hm : reindex23 M 0 0 = some (some 1,Stmt.write 0 Dir.right) := by
        simp [reindex23,swap23_0,swap23_1,hFirst]
      rw [hm,hx] at hh
      simp at hh
  have hG : GoodMachine M := ⟨hRun,hForm,hMissing,hLoop,hHalts,
    exclude [6,3,3,8,15,10,16,1] rfl,exclude [6,4,11,6,16,13,2,15] rfl⟩
  have hm0 : Matches M baseTable := by
    intro q a m hget
    fin_cases q <;> fin_cases a <;> simp [baseTable,Table.set,Table.empty,Table.get] at hget
    subst hget; exact hFirst
  have hrun1 : M.multiStep (Machine.init []) 1 = some h1.c.view := by
    rw [Machine.multiStep_one]
    exact step_move hm0 startPos ⟨1,0,false⟩ rfl
  have hv : HistValid M [h1,h0] := by
    intro h hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl
    · exact ⟨by decide,hrun1⟩
    · exact ⟨by decide,rfl⟩
  obtain ⟨q',hM10⟩ := hSecond
  by_cases h3 : q' = 3
  · subst h3
    have h01_base : UsesOnly01 baseTable := by
      refine ⟨rfl,rfl,rfl,rfl,?_⟩
      intro q a m' hget
      fin_cases q <;> fin_cases a <;> simp [baseTable,Table.set,Table.empty,Table.get] at hget
      subst hget; exact Or.inr rfl
    have hprev01 : ∀ h ∈ [h1,h0],h.c.state = 0 ∨ h.c.state = 1 := by
      intro h hh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl <;> simp [h0,h1,startPos,Position.move]
    have hM10' : (reindex23 M) 1 0 = some (some 2,Stmt.write 1 Dir.left) := by
      simp [reindex23,swap23_1,hM10,swap23_3]
    exact solve_branch (reindex23 M) (goodMachine_reindex23 hG)
      (matches_reindex23 hm0 h01_base) (histValid_reindex23 hv hprev01)
      2 (by decide) hM10'
  · exact solve_branch M hG hm0 hv q' h3 hM10

end OMA.BB4H1

theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R2_H1_R1.H4 := OMA.BB4H1.h4_proof
