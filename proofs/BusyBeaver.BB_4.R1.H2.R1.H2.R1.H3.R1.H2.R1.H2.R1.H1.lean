import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1

/-!

New certificate construction and assembly: Hanan Beer (@hananzlt).
The generic finite-automata verifier is reused from James Halldon (@Halldon),
merged PR1292. The tape-reader soundness lemmas and target reduction are by
@marcusbuffett (PR4876 and PR4509). Their attribution is retained.
The untrusted certificate search follows the direct FAR and n-gram CPS methods
from bbchallenge. Every resulting certificate is checked by Lean.

The following verifier originally established the three-state upper bound.

That original search branches on the first unassigned transition in 21 steps.
The present four-state application uses the first unassigned transition in
106 steps. The new bit-mask tests imply the original verifier checks. Nonhalting leaves use finite-automata reduction: a DFA summarizes
one half of the tape and an NFA recognizes a superset of configurations that
can reach an unassigned transition. The NFA excludes the entirely blank tape.
See Blanchard et al., *Determination of the fifth Busy Beaver value*, for the
finite-automata reduction method. Every certificate is checked by Lean.
-/

namespace BeaverBound

open Turing Turing.BusyBeaver

abbrev Symbol := Fin 2
abbrev Key (n : ℕ) := Fin n × Symbol
abbrev MachineOf (n : ℕ) [NeZero n] := Machine Symbol (Fin n)

structure Move (n : ℕ) where
  state : Fin n
  write : Symbol
  left : Bool
  deriving DecidableEq

structure Position (n : ℕ) where
  state : Fin n
  ls : List Symbol
  head : Symbol
  rs : List Symbol
  deriving DecidableEq

def start (n : ℕ) [NeZero n] : Position n := ⟨0, [], 0, []⟩

def push (a : Symbol) (xs : List Symbol) : List Symbol :=
  if a = 0 ∧ xs = [] then [] else a :: xs

def Position.move (c : Position n) (m : Move n) : Position n :=
  if m.left then ⟨m.state, c.ls.tail, c.ls.headI, push m.write c.rs⟩
  else ⟨m.state, push m.write c.ls, c.rs.headI, c.rs.tail⟩

def Move.flip (m : Move n) : Move n := { m with left := !m.left }

def Position.flip (c : Position n) : Position n := ⟨c.state, c.rs, c.head, c.ls⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem flip_move (c : Position n) (m : Move n) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with
  | mk q a d => cases d <;> rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem mk_push (a : Symbol) (xs : List Symbol) :
    ListBlank.mk (push a xs) = (ListBlank.mk xs).cons a := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact (ListBlank.cons_head_tail (ListBlank.mk ([] : List Symbol))).symm
  · exact (ListBlank.cons_mk a xs).symm

def Position.view [NeZero n] (c : Position n) : Cfg Symbol (Fin n) :=
  ⟨some c.state, ⟨c.head, ListBlank.mk c.ls, ListBlank.mk c.rs⟩⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem view_start (n : ℕ) [NeZero n] : (start n).view = Machine.init [] := rfl

def Move.command (m : Move n) : Option (Option (Fin n) × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def ongoing [NeZero n] (M : MachineOf n) (k : Key n) : Option (Move n) :=
  match M k.1 k.2 with
  | some (some q, ⟨b, .left⟩) => some ⟨q, b, true⟩
  | some (some q, ⟨b, .right⟩) => some ⟨q, b, false⟩
  | _ => none

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem ongoing_command [NeZero n] (M : MachineOf n) (k : Key n) (m : Move n)
    (h : ongoing M k = some m) : M k.1 k.2 = m.command := by
  rcases m with ⟨q, a, d⟩
  unfold ongoing at h
  split at h <;> simp_all [Move.command, Move.mk.injEq]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_move [NeZero n] (M : MachineOf n) (c : Position n) (m : Move n)
    (h : ongoing M (c.state, c.head) = some m) :
    M.step c.view = some (c.move m).view := by
  have he := ongoing_command M (c.state, c.head) m h
  change M c.state c.head = m.command at he
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem step_stop [NeZero n] (M : MachineOf n) (c : Position n)
    (h : ongoing M (c.state, c.head) = none) : M.HaltsAfter c.view 1 := by
  unfold ongoing at h
  split at h
  all_goals try contradiction
  cases hc : M c.state c.head with
  | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
  | some pair =>
    obtain ⟨q, b, d⟩ := pair
    cases q with
    | none => simp [Machine.HaltsAfter, Machine.multiStep_succ, Position.view, Machine.step, hc]
    | some q => cases d <;> simp_all

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem multi_succ_front [NeZero n] (M : MachineOf n) (c : Cfg Symbol (Fin n)) (k : ℕ) :
    M.multiStep c (k+1) = (M.step c).bind (fun c' => M.multiStep c' k) := by
  induction k with
  | zero => rw [Machine.multiStep_one]; cases M.step c <;> rfl
  | succ k ih =>
    rw [Machine.multiStep_succ, ih]
    cases h : M.step c with
    | none => rfl
    | some d => simp [Machine.multiStep_succ]

abbrev Program (n : ℕ) := List (Key n × Move n)

def Program.get : Program n → Key n → Option (Move n)
  | [], _ => none
  | (a, m) :: rest, k => if k = a then some m else Program.get rest k

def Program.flip (tb : Program n) : Program n := tb.map fun (k, m) => (k, m.flip)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem get_flip (tb : Program n) (k : Key n) : tb.flip.get k = (tb.get k).map Move.flip := by
  induction tb with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k', m⟩ := x
    by_cases h : k = k' <;> simp [Program.flip, Program.get, h] at ih ⊢
    exact ih

inductive CanStop (tb : Program n) : Position n → Prop
  | missing {c} : tb.get (c.state, c.head) = none → CanStop tb c
  | move {c m} : tb.get (c.state, c.head) = some m → CanStop tb (c.move m) → CanStop tb c

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem canStop_flip {tb : Program n} {c : Position n} (h : CanStop tb c) :
    CanStop tb.flip c.flip := by
  induction h with
  | missing h => exact .missing (by simpa [Position.flip, get_flip] using h)
  | @move c m h _ ih =>
    refine .move (m := m.flip) ?_ ?_
    · change tb.flip.get (c.state, c.head) = some m.flip
      simp [get_flip, h]
    · rwa [← flip_move]

def Matches [NeZero n] (M : MachineOf n) (tb : Program n) : Prop :=
  ∀ k m, tb.get k = some m → ongoing M k = some m

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem matches_empty [NeZero n] (M : MachineOf n) : Matches M [] := by
  intro k m h
  contradiction

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem matches_add [NeZero n] {M : MachineOf n} {tb : Program n} {k : Key n} {m : Move n}
    (hm : Matches M tb) (h : ongoing M k = some m) : Matches M ((k, m) :: tb) := by
  intro k' m' hh
  by_cases e : k' = k
  · subst k'
    simp [Program.get] at hh
    simpa [← hh] using h
  · apply hm k' m'
    simpa [Program.get, e] using hh

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem cannot_stop_run [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (c : Position n) (hc : ¬ CanStop tb c) (k : ℕ) :
    M.multiStep c.view k ≠ none := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    cases h : tb.get (c.state, c.head) with
    | none => exact (hc (.missing h)).elim
    | some m =>
      rw [multi_succ_front, step_move M c m (hm _ _ h), Option.bind_some]
      exact ih _ (fun hs => hc (.move h hs))

end BeaverBound


namespace BeaverBound

open Turing Turing.BusyBeaver

-- A DFA reads a left half-tape from the far end toward the head. Its initial
-- state is fixed by the blank symbol, so appending blank cells changes nothing.
structure TapeDFA where
  extraStates : ℕ
  code : ℕ

abbrev TapeDFA.size (D : TapeDFA) : ℕ := D.extraStates + 1

def TapeDFA.next (D : TapeDFA) (a : Symbol) (l : Fin D.size) : Fin D.size :=
  ⟨(D.code * D.size / D.size ^ (2 * l.val + a.val)) % D.size,
    Nat.mod_lt _ (Nat.succ_pos _)⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact D.blank.symm
  · rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem TapeDFA.read_pop (D : TapeDFA) (xs : List Symbol) :
    D.next xs.headI (D.read xs.tail) = D.read xs := by
  cases xs
  · exact D.blank
  · rfl

-- Each NFA state records a control state and a left DFA state. The extra state
-- is accepting. The NFA reads the other half of the tape, starting at the head.
structure Certificate (n : ℕ) where
  mirror : Bool
  dfa : TapeDFA
  edges : ℕ
  blankReach : ℕ

abbrev Node (cert : Certificate n) := Option (Fin n × Fin cert.dfa.size)

def nodeId (cert : Certificate n) : Node cert → ℕ
  | none => n * cert.dfa.size
  | some (q, l) => q.val * cert.dfa.size + l.val

def Certificate.edge (cert : Certificate n) (p : Node cert) (a : Symbol)
    (q : Node cert) : Bool :=
  match p with
  | none => q.isNone
  | some _ => cert.edges.testBit ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1) + nodeId cert q)

def Certificate.onBlank (cert : Certificate n) (p : Node cert) : Bool :=
  cert.blankReach.testBit (nodeId cert p)

def unpack (n val : ℕ) : Certificate n :=
  let extra := val / 2 % 8
  let size := extra + 1
  let dfaBase := size ^ (2 * size - 1)
  let payload := val / 16 / dfaBase
  let width := n * size + 1
  let initialBase := 2 ^ width
  ⟨val % 2 == 1, ⟨extra, val / 16 % dfaBase⟩, payload / initialBase, payload % initialBase⟩

def nodes (cert : Certificate n) : List (Node cert) :=
  none :: (List.finRange n).flatMap fun q =>
    (List.finRange cert.dfa.size).map fun l => some (q, l)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem allNodes {cert : Certificate n} {p : Node cert → Bool}
    (h : (nodes cert).all p = true) (a : Node cert) : p a = true := by
  refine (List.all_eq_true.mp h) a ?_
  rcases a with _ | ⟨q, l⟩
  · simp [nodes]
  · simp [nodes]

def checkBlank (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0, 0)) && !cert.onBlank none &&
    (nodes cert).all (fun p => if cert.onBlank p then
      (nodes cert).all fun q => !cert.edge p 0 q || cert.onBlank q
    else true)

def checkAt (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q, l)
  match tb.get (q, a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state, l')) a' s then
            (nodes cert).all fun t => !cert.edge s m.write t || cert.edge p a t
          else true
        else true
    else cert.edge p a (some (m.state, cert.dfa.next m.write l))

def checkMachine (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAt tb cert q a l

inductive Reads (cert : Certificate n) : Node cert → ListBlank Symbol → Prop
  | done (t) : Reads cert none t
  | step {p q t} : cert.edge p t.head q = true → Reads cert q t.tail → Reads cert p t

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem Reads.push {cert : Certificate n} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem Reads.pop {cert : Certificate n} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, rfl, .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem no_read_blank [NeZero n] {cert : Certificate n} (hb : checkBlank cert = true) :
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
      have he0 : cert.edge p 0 q = true := he
      simp [he0] at hn
      exact ih rfl hn
  exact fun hr => each hr rfl hstart

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem reads_of_canStop {tb : Program n} {cert : Certificate n} (hchk : checkMachine tb cert = true)
    {c : Position n} (hs : CanStop tb c) :
    Reads cert (some (c.state, cert.dfa.read c.ls)) ((ListBlank.mk c.rs).cons c.head) := by
  induction hs with
  | @missing c hh =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    rw [checkAt, hh] at h
    exact Reads.push h (.done _)
  | @move c m hh _ ih =>
    have h := allFin (allFin (allFin hchk c.state) c.head) (cert.dfa.read c.ls)
    rw [checkAt, hh] at h
    cases hd : m.left with
    | false =>
      have hstep : cert.edge (some (c.state, cert.dfa.read c.ls)) c.head
          (some (m.state, cert.dfa.next m.write (cert.dfa.read c.ls))) = true := by
        simpa [hd] using h
      refine Reads.push hstep ?_
      simpa [Position.move, hd, TapeDFA.read_push, ← ListBlank.head_mk, ← ListBlank.tail_mk]
        using ih
    | true =>
      have hr : Reads cert (some (m.state, cert.dfa.read c.ls.tail))
          (((ListBlank.mk c.rs).cons m.write).cons c.ls.headI) := by
        simpa [Position.move, hd, mk_push] using ih
      obtain ⟨s, he, hr⟩ := Reads.pop hr
      obtain ⟨t, hf, ht⟩ := Reads.pop hr
      simp only [hd, if_true] at h
      have h' := allFin (allFin h (cert.dfa.read c.ls.tail)) c.ls.headI
      simp only [TapeDFA.read_pop, if_true] at h'
      have h'' := allNodes h' s
      simp only [he, if_true] at h''
      have h''' := allNodes h'' t
      simp [hf] at h'''
      exact Reads.push h''' ht

def checkCertificate [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  let C := unpack n val
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem certificate_sound [NeZero n] {tb : Program n} {val : ℕ}
    (h : checkCertificate tb val = true) : ¬ CanStop tb (start n) := by
  intro hs
  unfold checkCertificate at h
  have ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp h
  apply no_read_blank hb
  have blank : (ListBlank.mk ([] : List Symbol)).cons 0 = ListBlank.mk [] :=
    ListBlank.cons_head_tail (ListBlank.mk [])
  split at hm
  · simpa only [Position.flip, start, TapeDFA.read, List.foldr_nil, blank] using
      (reads_of_canStop hm (canStop_flip hs))
  · simpa only [start, TapeDFA.read, List.foldr_nil, blank] using (reads_of_canStop hm hs)

end BeaverBound

namespace BeaverBound

open Turing Turing.BusyBeaver

def firstMissing (tb : Program n) : ℕ → Position n → Option (Key n)
  | 0, _ => none
  | fuel + 1, c =>
    match tb.get (c.state, c.head) with
    | none => some (c.state, c.head)
    | some m => firstMissing tb fuel (c.move m)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem firstMissing_stops [NeZero n] {M : MachineOf n} {tb : Program n}
    (hm : Matches M tb) (fuel : ℕ) (c : Position n) {k : Key n}
    (h : firstMissing tb fuel c = some k) (halt : ongoing M k = none) : M.HaltsAfter c.view fuel := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases ht : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, ht] at h
      subst k
      exact Machine.multiStep_eq_none_mono (step_stop M c halt) (by omega)
    | some m =>
      have htail : firstMissing tb fuel (c.move m) = some k := by
        simpa [firstMissing, ht] using h
      unfold Machine.HaltsAfter
      rw [multi_succ_front, step_move M c m (hm _ _ ht), Option.bind_some]
      exact ih _ htail

def holes (tb : Program n) : Finset (Key n) :=
  Finset.univ.filter fun k => tb.get k = none

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem missing_is_hole {tb : Program n} {c : Position n} {k : Key n} {fuel : ℕ}
    (h : firstMissing tb fuel c = some k) : k ∈ holes tb := by
  induction fuel generalizing c with
  | zero => simp [firstMissing] at h
  | succ fuel ih =>
    cases he : tb.get (c.state, c.head) with
    | none =>
      simp [firstMissing, he] at h
      subst k
      simp [holes, he]
    | some m =>
      exact ih (by simpa [firstMissing, he] using h)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem holes_add (tb : Program n) (k : Key n) (m : Move n) :
    holes ((k, m) :: tb) = (holes tb).erase k := by
  ext k'
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [Program.get]
  by_cases e : k' = k <;> simp [e]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem no_holes_cannot_stop {tb : Program n} (h : (holes tb).card = 0) {c : Position n} :
    ¬ CanStop tb c := by
  intro hs
  induction hs with
  | @missing c hm =>
    have he : (c.state, c.head) ∈ holes tb := by simp [holes, hm]
    have := Finset.card_pos.mpr ⟨_, he⟩
    omega
  | move _ _ ih => exact ih

def moves (n : ℕ) : List (Move n) := (List.finRange n).flatMap fun q =>
  (List.finRange 2).flatMap fun a => [⟨q, a, false⟩, ⟨q, a, true⟩]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem mem_moves (m : Move n) : m ∈ moves n := by
  obtain ⟨q, a, d⟩ := m
  rw [moves, List.mem_flatMap]
  refine ⟨q, by simp, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, by simp, ?_⟩
  cases d <;> simp

def checkTree [NeZero n] (limit : ℕ) : ℕ → Program n → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | fuel + 1, tb, certs =>
    match firstMissing tb limit (start n) with
    | none => match certs with
      | [] => none
      | v :: rest => if checkCertificate tb v then some rest else none
    | some k => (moves n).foldlM (fun rest m => checkTree limit fuel ((k, m) :: tb) rest) certs

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem succeeds_each {α β : Type*} {items : List α} {f : β → α → Option β}
    {a b : β} (h : items.foldlM f a = some b) {i : α} (hi : i ∈ items) :
    ∃ x y, f x i = some y := by
  induction items generalizing a with
  | nil => simp at hi
  | cons head tail ih =>
    rw [List.foldlM_cons] at h
    cases hh : f a head with
    | none => simp [hh] at h
    | some mid =>
      simp only [hh] at h
      rcases List.mem_cons.mp hi with rfl | ht
      · exact ⟨_, _, hh⟩
      · exact ih h ht

def Upper [NeZero n] (M : MachineOf n) (limit : ℕ) : Prop :=
  M.HaltsAfter (Machine.init []) limit ∨ ¬ M.IsHalting

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem upper_cannot_stop [NeZero n] {M : MachineOf n} {tb : Program n} {limit : ℕ}
    (hm : Matches M tb) (h : ¬ CanStop tb (start n)) : Upper M limit := by
  right
  intro halts
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  apply cannot_stop_run hm (start n) h (k + 1)
  rwa [view_start]

abbrev TreeBound [NeZero n] (limit : ℕ) (tb : Program n) : Prop :=
  ∀ M : MachineOf n, Matches M tb → Upper M limit

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem branch_bound [NeZero n] {limit : ℕ} {tb : Program n} {k : Key n}
    (h : firstMissing tb limit (start n) = some k)
    (children : ∀ m, TreeBound limit ((k, m) :: tb)) : TreeBound limit tb := by
  intro M hm
  cases hs : ongoing M k with
  | none =>
    left
    simpa only [view_start] using firstMissing_stops hm limit (start n) h hs
  | some m => exact children m M (matches_add hm hs)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem subtree_bound [NeZero n] {limit fuel : ℕ} {tb : Program n} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkTree limit fuel tb a = some b) :
    TreeBound limit tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    rw [checkTree.eq_def] at h
    cases hFirst : firstMissing tb limit (start n) with
    | none =>
      simp only [hFirst] at h
      intro M hm
      cases a with
      | nil => contradiction
      | cons v rest =>
        by_cases hc : checkCertificate tb v = true
        · exact upper_cannot_stop hm (certificate_sound hc)
        · simp [hc] at h
    | some k =>
      simp only [hFirst] at h
      apply branch_bound hFirst
      intro m
      obtain ⟨x, y, hy⟩ := succeeds_each h (mem_moves m)
      refine ih ?_ hy
      rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
      omega

end BeaverBound

/- Tape-reader invariant lemmas below are reused from @marcusbuffett's
BusyBeaver.BB_4.R1.H2.R1.H2.R1.H3.R1.H3.R1 reduction. The sparse certificate
adapter is new work credited to Hanan Beer (@hananzlt). -/
namespace BeaverBound.SparseReaders
open Turing Turing.BusyBeaver
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem reader {X : Type} (f : Fin 2 → X → X) (x : X) (blank : f 0 x=x) :
    ∃ g : ListBlank (Fin 2) → X, g (ListBlank.mk [])=x ∧
      ∀ (a : Fin 2) (l : ListBlank (Fin 2)),g (ListBlank.cons a l) = f a (g l) := by
  have zeros (m : ℕ) : (List.replicate m (0 : Fin 2)).foldr f x=x := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ,ih,blank]
  let g (l : ListBlank (Fin 2)) := l.liftOn (fun a => a.foldr f x) (by
    rintro a _ ⟨i,rfl⟩
    simp [List.foldr_append,zeros])
  refine ⟨g,rfl,?_⟩
  intro a l
  induction l using ListBlank.induction_on with | h l => rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem certified (M : Machine (Fin 2) (Fin 4))
    {X Y : Type} (x : X) (y : Y) (L : Fin 2 → X → X) (R : Fin 2 → Y → Y)
    (S : Fin 4 → Fin 2 → X → Y → Bool)
    (hl : L 0 x=x) (hr : R 0 y=y) (start : S 0 0 x y=true)
    (closed : ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, M q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true) : ¬ M.IsHalting := by
  obtain ⟨fl,bl,cl⟩ := reader L x hl
  obtain ⟨fr,br,cr⟩ := reader R y hr
  have decompL (s : ListBlank (Fin 2)) : L s.head (fl s.tail)=fl s :=
    (cl _ _).symm.trans (congrArg fl (ListBlank.cons_head_tail s))
  have decompR (s : ListBlank (Fin 2)) : R s.head (fr s.tail)=fr s :=
    (cr _ _).symm.trans (congrArg fr (ListBlank.cons_head_tail s))
  have run (n : ℕ) : ∃ q t, M.multiStep (Machine.init []) n = some ⟨some q,t⟩ ∧
      S q t.head (fl t.left) (fr t.right)=true := by
    induction n with
    | zero =>
      refine ⟨0,Tape.mk₁ [],rfl,?_⟩
      change S 0 0 (fl (ListBlank.mk [])) (fr (ListBlank.mk []))=true
      simpa only [bl,br] using start
    | succ n ih =>
      obtain ⟨q,t,ht,hs⟩ := ih
      obtain ⟨r,w,d,move,next⟩ := closed q t.head t.left.head t.right.head (fl t.left.tail) (fr t.right.tail) (by
        rwa [decompL,decompR])
      refine ⟨r,(t.write w).move d,?_,?_⟩
      · simp [Machine.multiStep_succ,ht,Machine.step,move]
      · cases d <;> simp only [decompL,decompR] at next <;> simpa [Tape.move,Tape.write,cl,cr] using next
  intro hh
  obtain ⟨n,hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hh
  obtain ⟨_,_,he,_⟩ := run (n+1)
  rw [Machine.HaltsAfter,he] at hn
  contradiction


inductive Tree (α : Type) where
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α

def member [DecidableEq α] (code : α → ℕ) (x : α) : Tree α → Bool
  | .nil => false
  | .node a l r => if x = a then true else
      if code x < code a then member code x l else member code x r

def every (p : α → Bool) : Tree α → Bool
  | .nil => true
  | .node a l r => p a && every p l && every p r

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem every_member [DecidableEq α] {code : α → ℕ} {p : α → Bool}
    (t : Tree α) {x : α} (h : every p t = true) (hx : member code x t = true) :
    p x = true := by
  induction t with
  | nil => simp [member] at hx
  | node a l r ihl ihr =>
    have hh : p a = true ∧ every p l = true ∧ every p r = true := by
      simpa only [every, Bool.and_eq_true, and_assoc] using h
    by_cases ha : x = a
    · simpa only [ha] using hh.1
    · simp only [member, ha, if_false] at hx
      split at hx
      · exact ihl hh.2.1 hx
      · exact ihr hh.2.2 hx

abbrev Context (n m : ℕ) := Fin 4 × Fin 2 × Fin n × Fin m

def code (c : Context n m) : ℕ :=
  ((2 * c.1.val + c.2.1.val) * n + c.2.2.1.val) * m + c.2.2.2.val

def marked (t : Tree (Context n m)) (q : Fin 4) (a : Fin 2) (l : Fin n) (r : Fin m) : Bool :=
  member code (q,a,l,r) t

def checkContext (tb : Program 4)
    (L : Fin 2 → Fin n → Fin n) (R : Fin 2 → Fin m → Fin m)
    (preL : Fin n → List (Fin 2 × Fin n)) (preR : Fin m → List (Fin 2 × Fin m))
    (t : Tree (Context n m)) (c : Context n m) : Bool :=
  match tb.get (c.1,c.2.1) with
  | none => false
  | some cmd => if cmd.left then
      (preL c.2.2.1).all fun (s,l) => marked t cmd.state s l (R cmd.write c.2.2.2)
    else (preR c.2.2.2).all fun (s,r) => marked t cmd.state s (L cmd.write c.2.2.1) r

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sparse_bound {n m : ℕ} [NeZero n] [NeZero m] (tb : Program 4)
    (L : Fin 2 → Fin n → Fin n) (R : Fin 2 → Fin m → Fin m)
    (preL : Fin n → List (Fin 2 × Fin n)) (preR : Fin m → List (Fin 2 × Fin m))
    (t : Tree (Context n m))
    (left_complete : ∀ s l, (s,l) ∈ preL (L s l))
    (right_complete : ∀ s r, (s,r) ∈ preR (R s r))
    (hl : L 0 0 = 0) (hr : R 0 0 = 0) (start : marked t 0 0 0 0 = true)
    (closed : every (checkContext tb L R preL preR t) t = true) : TreeBound 106 tb := by
  intro M hm
  right
  apply certified M (0 : Fin n) (0 : Fin m) L R (marked t) hl hr start
  intro q a s u l r h
  have good := every_member t closed h
  change checkContext tb L R preL preR t (q,a,L s l,R u r) = true at good
  cases hc : tb.get (q,a) with
  | none => simp [checkContext,hc] at good
  | some cmd =>
    have transition := hm (q,a) cmd hc
    have command := ongoing_command M (q,a) cmd transition
    by_cases hd : cmd.left = true
    · refine ⟨cmd.state,cmd.write,.left,?_,?_⟩
      · simpa [Move.command,hd] using command
      · have hgood : (preL (L s l)).all (fun (a,i) => marked t cmd.state a i (R cmd.write (R u r))) = true := by
          simpa [checkContext,hc,hd] using good
        exact List.all_eq_true.mp hgood (s,l) (left_complete s l)
    · have hd' : cmd.left = false := Bool.eq_false_iff.mpr hd
      refine ⟨cmd.state,cmd.write,.right,?_,?_⟩
      · simpa [Move.command,hd'] using command
      · have hgood : (preR (R u r)).all (fun (a,j) => marked t cmd.state a (L cmd.write (L s l)) j) = true := by
          simpa [checkContext,hc,hd'] using good
        exact List.all_eq_true.mp hgood (u,r) (right_complete u r)

end BeaverBound.SparseReaders

namespace BeaverBound.SparseReaders

/-- Read a finite balanced tree from packed node indices. Zero denotes an empty node. -/
def packedTree {n m : ℕ} [NeZero n] [NeZero m] (bits data : ℕ) :
    ℕ → ℕ → Tree (Context n m)
  | 0, _ => .nil
  | fuel + 1, index =>
    match (data >>> (bits * index)) % 2^bits with
    | 0 => .nil
    | v + 1 => .node
        (Fin.ofNat 4 (v / (2*n*m)), Fin.ofNat 2 (v / (n*m)),
          Fin.ofNat n (v/m), Fin.ofNat m v)
        (packedTree bits data fuel (2*index+1))
        (packedTree bits data fuel (2*index+2))

end BeaverBound.SparseReaders

namespace BeaverBound.SparseReaders
private def L10 (a : Fin 2) (x : Fin 29) : Fin 29 :=
  Fin.ofNat 29 (((514241722796073162977491709187420923150639019663389637867561699991898141183579984594976 : ℕ) >>> (5*(2*x.val+a.val))) % 32)
private def preL10 (x : Fin 29) : List (Fin 2 × Fin 29) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,7),(1,7),(0,8),(1,8),(0,11),(1,11),(0,12),(1,12),(0,13),(1,13),(0,14),(1,14),(0,16),(1,16),(0,17),(1,17),(0,21),(1,21),(0,22),(1,22),(0,24),(1,24),(0,25),(1,25),(0,28),(1,28)]
  | 9 => [(0,5)]
  | 10 => [(1,5)]
  | 11 => [(0,6)]
  | 12 => [(1,6)]
  | 13 => [(0,9)]
  | 14 => [(1,9)]
  | 15 => [(0,10)]
  | 16 => [(1,10)]
  | 17 => [(0,15)]
  | 18 => [(1,15)]
  | 19 => [(0,18)]
  | 20 => [(1,18)]
  | 21 => [(0,19),(0,27)]
  | 22 => [(1,19),(1,27)]
  | 23 => [(0,20)]
  | 24 => [(1,20)]
  | 25 => [(0,23)]
  | 26 => [(1,23)]
  | 27 => [(0,26)]
  | 28 => [(1,26)]
  | _ => []
private def R10 (a : Fin 2) (x : Fin 77) : Fin 77 :=
  Fin.ofNat 77 (((1529769007052697573386944566790679914321871972856222302439170113052579465354103354571871575146850681043271256395760083630617913142771749057113958262499710192863773201268799892741502547932775974575417116180456650466730426353147372769784167194719804383078791453080942175732178383174718379066688534946626564140820812590353514624 : ℕ) >>> (7*(2*x.val+a.val))) % 128)
private def preR10 (x : Fin 77) : List (Fin 2 × Fin 77) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,7),(1,7),(0,8),(1,8),(0,11),(1,11),(0,13),(1,13),(0,19),(1,19),(0,20),(1,20),(0,21),(1,21),(0,25),(1,25),(0,26),(1,26),(0,27),(1,27),(0,28),(1,28),(0,31),(1,31),(0,35),(1,35),(0,39),(1,39),(0,40),(1,40),(0,41),(1,41),(0,47),(1,47),(0,52),(1,52),(0,53),(1,53),(0,57),(1,57),(0,58),(1,58),(0,59),(1,59),(0,60),(1,60),(0,63),(1,63),(0,67),(1,67),(0,70),(1,70),(0,71),(1,71)]
  | 9 => [(0,5)]
  | 10 => [(1,5)]
  | 11 => [(0,6)]
  | 12 => [(1,6)]
  | 13 => [(0,9)]
  | 14 => [(1,9)]
  | 15 => [(0,10)]
  | 16 => [(1,10)]
  | 17 => [(0,12)]
  | 18 => [(1,12)]
  | 19 => [(0,14)]
  | 20 => [(1,14)]
  | 21 => [(0,15)]
  | 22 => [(1,15)]
  | 23 => [(0,16)]
  | 24 => [(1,16)]
  | 25 => [(0,17)]
  | 26 => [(1,17)]
  | 27 => [(0,18)]
  | 28 => [(1,18)]
  | 29 => [(0,22)]
  | 30 => [(1,22)]
  | 31 => [(0,23)]
  | 32 => [(1,23)]
  | 33 => [(0,24)]
  | 34 => [(1,24)]
  | 35 => [(0,29),(0,61)]
  | 36 => [(1,29),(1,61)]
  | 37 => [(0,30),(0,62)]
  | 38 => [(1,30),(1,62)]
  | 39 => [(0,32),(0,64)]
  | 40 => [(1,32),(1,64)]
  | 41 => [(0,33),(0,65)]
  | 42 => [(1,33),(1,65)]
  | 43 => [(0,34),(0,66)]
  | 44 => [(1,34),(1,66)]
  | 45 => [(0,36)]
  | 46 => [(1,36)]
  | 47 => [(0,37)]
  | 48 => [(1,37)]
  | 49 => [(0,38)]
  | 50 => [(1,38)]
  | 51 => [(0,42)]
  | 52 => [(1,42)]
  | 53 => [(0,43)]
  | 54 => [(1,43)]
  | 55 => [(0,44)]
  | 56 => [(1,44)]
  | 57 => [(0,45),(0,75)]
  | 58 => [(1,45),(1,75)]
  | 59 => [(0,46),(0,76)]
  | 60 => [(1,46),(1,76)]
  | 61 => [(0,48)]
  | 62 => [(1,48)]
  | 63 => [(0,49)]
  | 64 => [(1,49)]
  | 65 => [(0,50)]
  | 66 => [(1,50)]
  | 67 => [(0,51),(0,69)]
  | 68 => [(1,51),(1,69)]
  | 69 => [(0,54),(0,72)]
  | 70 => [(1,54),(1,72)]
  | 71 => [(0,55),(0,73)]
  | 72 => [(1,55),(1,73)]
  | 73 => [(0,56),(0,74)]
  | 74 => [(1,56),(1,74)]
  | 75 => [(0,68)]
  | 76 => [(1,68)]
  | _ => []
private def contexts10 : Tree (Context 29 77) :=
packedTree 15 0x1d2d80006f420001bc180006c400001afe00006a7e0001a5b0000621000016b200005a780001632800057da00015d38000558c00014d98000530600014790000511a000143d800050da000142c80004eba00013a380004e62000134080004c3c000130200004a00000124e800048ea00011f8000046fe00011b2800046600001125800040000000f7800003da80000f5800003a300000e7f000037f40000d75000035880000c2f000021ee000084680001f54000073d80001c6400006ba80001ac600006a68000175a00005cd800016f2000053d800014b600004ce000012d4000049a800011fc0000376803b0002f0a9ce7b7896eb8d839af334d26516c0d16a92c7d5896aee556e2a6a5310a419448a88150e2a1793b2a74b4e7a9c8131226124be0929d243a410479c8dbd19c22f640407be0f6d1ebe3a3c7430e751b0a35906a2888b90da1f763a3c7240d7f1ad2354c5dc8ba1170e2a0c52f89a212fc254c48608c60036e795bb7b5f86952b57162fab515332a26543a28514e8298c12ff248b47b08d3d0ff1ee63a5473e0d6911c01faa39c86b68d42171a29c44c20919009ede3da782d255572a21d3a9a61848ce8c48f681b1321c6361c5d38a4911bcd8615eca867495e7fb0d530d5f12aec1393959d121512a498757a377 8 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional10 : TreeBound (n := 4) 106 [((3,0),⟨1,0,false⟩),((2,1),⟨3,1,false⟩),((0,1),⟨2,0,true⟩),((1,1),⟨2,1,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨0,1,true⟩)] := by
  apply sparse_bound _ L10 R10 preL10 preR10 contexts10
  all_goals decide +kernel

end BeaverBound.SparseReaders
namespace BeaverBound

def forceNat {α : Type} (v : ℕ) (f : ℕ → α) : α :=
  match v with
  | 0 => f 0
  | k + 1 => f (k + 1)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem forceNat_eq {α : Type} (v : ℕ) (f : ℕ → α) : forceNat v f = f v := by
  cases v <;> rfl

/-- Normalize packed fields once before the kernel checks repeated edge lookups. -/
def checkCertificateFast [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  forceNat (val / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (val / 16 % dfaBase) fun dfaCode =>
  forceNat (val / 16 / dfaBase) fun payload =>
  forceNat (2 ^ (n * size + 1)) fun initialBase =>
  forceNat (payload / initialBase) fun edges =>
  forceNat (payload % initialBase) fun blankReach =>
  let C : Certificate n := ⟨val % 2 == 1, ⟨extra,dfaCode⟩, edges,blankReach⟩
  checkBlank C && checkMachine (if C.mirror then tb.flip else tb) C

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkCertificateFast_eq [NeZero n] (tb : Program n) (val : ℕ) :
    checkCertificateFast tb val = checkCertificate tb val := by
  simp only [checkCertificateFast, forceNat_eq]
  rfl
end BeaverBound
namespace BeaverBound

def Certificate.row (cert : Certificate n) (p : Node cert) (a : Symbol) : ℕ :=
  match p with
  | none => 2 ^ (n * cert.dfa.size)
  | some _ => (cert.edges >>> ((2 * nodeId cert p + a.val) *
      (n * cert.dfa.size + 1))) % 2 ^ (n * cert.dfa.size + 1)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem state_nodeId_lt (cert : Certificate n) (q : Fin n) (l : Fin cert.dfa.size) :
    nodeId cert (some (q,l)) < n * cert.dfa.size := by
  have hh := Nat.mul_le_mul_right cert.dfa.size (Nat.succ_le_of_lt q.isLt)
  simp only [Nat.succ_mul] at hh
  have hl := l.isLt
  simp only [nodeId]
  omega

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem nodeId_lt (cert : Certificate n) (p : Node cert) :
    nodeId cert p < n * cert.dfa.size + 1 := by
  rcases p with _ | ⟨q,l⟩
  · simp [nodeId]
  · exact Nat.lt_succ_of_lt (state_nodeId_lt cert q l)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem row_bit (cert : Certificate n) (p q : Node cert) (a : Symbol) :
    (cert.row p a).testBit (nodeId cert q) = cert.edge p a q := by
  cases p with
  | none =>
    cases q with
    | none => simp [Certificate.row,Certificate.edge,nodeId]
    | some q =>
      have hh := state_nodeId_lt cert q.1 q.2
      simp [Certificate.row,Certificate.edge,ne_of_gt hh]
  | some p =>
    have hq := nodeId_lt cert q
    simp only [Certificate.row,Certificate.edge,Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight,hq,decide_true,Bool.true_and]

def rowsIncluded (a b : ℕ) : Bool := decide (a &&& b = a)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rowsIncluded_bit {a b i : ℕ} (h : rowsIncluded a b = true)
    (ha : a.testBit i = true) : b.testBit i = true := by
  have he : a &&& b = a := of_decide_eq_true h
  have hh := congrArg (fun v => v.testBit i) he
  simpa only [Nat.testBit_and,ha,Bool.true_and] using hh

def checkAtBits (tb : Program n) (cert : Certificate n) (q : Fin n) (a : Symbol)
    (l : Fin cert.dfa.size) : Bool :=
  let p : Node cert := some (q,l)
  match tb.get (q,a) with
  | none => cert.edge p a none
  | some m =>
    if m.left then
      forceNat (cert.row p a) fun target =>
      (List.finRange cert.dfa.size).all fun l' => (List.finRange 2).all fun a' =>
        if cert.dfa.next a' l' = l then
          (nodes cert).all fun s => if cert.edge (some (m.state,l')) a' s then
            rowsIncluded (cert.row s m.write) target
          else true
        else true
    else cert.edge p a (some (m.state,cert.dfa.next m.write l))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkAtBits_sound {tb : Program n} {cert : Certificate n} {q : Fin n}
    {a : Symbol} {l : Fin cert.dfa.size} (h : checkAtBits tb cert q a l = true) :
    checkAt tb cert q a l = true := by
  unfold checkAtBits checkAt at *
  cases hg : tb.get (q,a) with
  | none => simpa [hg] using h
  | some m =>
    simp only [hg] at h ⊢
    cases hd : m.left with
    | false => simpa [hd] using h
    | true =>
      simp only [hd,if_true,forceNat_eq] at h ⊢
      apply List.all_eq_true.mpr
      intro l' _
      apply List.all_eq_true.mpr
      intro a' _
      have hh := allFin (allFin h l') a'
      by_cases he : cert.dfa.next a' l' = l
      · simp only [he,if_true] at hh ⊢
        apply List.all_eq_true.mpr
        intro s _
        have hs := allNodes hh s
        by_cases hed : cert.edge (some (m.state,l')) a' s = true
        · simp only [hed,if_true] at hs ⊢
          apply List.all_eq_true.mpr
          intro t _
          by_cases het : cert.edge s m.write t = true
          · have hrow : (cert.row s m.write).testBit (nodeId cert t) = true := by
              rwa [row_bit]
            have ht := rowsIncluded_bit hs hrow
            rw [row_bit] at ht
            simp only [het,ht,Bool.not_true,Bool.false_or]
          · simp [het]
        · simp [hed]
      · simp [he]

def checkMachineBits (tb : Program n) (cert : Certificate n) : Bool :=
  (List.finRange n).all fun q => (List.finRange 2).all fun a =>
    (List.finRange cert.dfa.size).all fun l => checkAtBits tb cert q a l

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkMachineBits_sound {tb : Program n} {cert : Certificate n}
    (h : checkMachineBits tb cert = true) : checkMachine tb cert = true := by
  unfold checkMachineBits at h
  unfold checkMachine
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro l _
  exact checkAtBits_sound (allFin (allFin (allFin h q) a) l)

end BeaverBound

namespace BeaverBound

def checkBlankBits (cert : Certificate n) [NeZero n] : Bool :=
  cert.onBlank (some (0,0)) && !cert.onBlank none &&
    (nodes cert).all fun p => if cert.onBlank p then
      rowsIncluded (cert.row p 0) cert.blankReach
    else true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkBlankBits_sound {cert : Certificate n} [NeZero n]
    (h : checkBlankBits cert = true) : checkBlank cert = true := by
  simp only [checkBlankBits,Bool.and_eq_true_iff] at h
  unfold checkBlank
  apply Bool.and_eq_true_iff.mpr
  refine ⟨Bool.and_eq_true_iff.mpr h.1,?_⟩
  apply List.all_eq_true.mpr
  intro p _
  have hp := allNodes h.2 p
  by_cases hb : cert.onBlank p = true
  · simp only [hb,if_true] at hp ⊢
    apply List.all_eq_true.mpr
    intro q _
    by_cases he : cert.edge p 0 q = true
    · have hrow : (cert.row p 0).testBit (nodeId cert q) = true := by rwa [row_bit]
      have hq := rowsIncluded_bit hp hrow
      change cert.onBlank q = true at hq
      simp only [he,hq,Bool.not_true,Bool.false_or]
    · simp [he]
  · simp [hb]

def checkCertificateBits [NeZero n] (tb : Program n) (val : ℕ) : Bool :=
  forceNat (val / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (val / 16 % dfaBase) fun dfaCode =>
  forceNat (val / 16 / dfaBase) fun payload =>
  forceNat (2 ^ (n * size + 1)) fun initialBase =>
  forceNat (payload / initialBase) fun edges =>
  forceNat (payload % initialBase) fun blankReach =>
  let C : Certificate n := ⟨val % 2 == 1, ⟨extra,dfaCode⟩, edges,blankReach⟩
  checkBlankBits C && checkMachineBits (if C.mirror then tb.flip else tb) C

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checkCertificateBits_sound [NeZero n] {tb : Program n} {val : ℕ}
    (h : checkCertificateBits tb val = true) : ¬ CanStop tb (start n) := by
  apply certificate_sound (val := val)
  rw [← checkCertificateFast_eq]
  unfold checkCertificateBits at h
  unfold checkCertificateFast
  simp only [forceNat_eq] at h ⊢
  exact Bool.and_eq_true_iff.mpr ⟨checkBlankBits_sound (Bool.and_eq_true_iff.mp h).1,
    checkMachineBits_sound (Bool.and_eq_true_iff.mp h).2⟩

end BeaverBound

namespace BeaverBound

/- The constructor is an untrusted finite calculation following direct FAR
saturation from bbchallenge. Its output must pass `checkCertificateFast`, whose
soundness is inherited from James Halldon's verifier. -/

def nfaRow (size edges p : ℕ) (a : Fin 2) : ℕ :=
  let width := 4 * size + 1
  if p = 4 * size then 1 <<< (4 * size)
  else (edges >>> ((2 * p + a.val) * width)) % (2 ^ width)

def nfaInsert (size edges p : ℕ) (a : Fin 2) (row : ℕ) : ℕ :=
  edges ||| (row <<< ((2 * p + a.val) * (4 * size + 1)))

def nfaInitial (tb : Program 4) (D : TapeDFA) : ℕ :=
  (List.finRange 4).foldl (fun e q =>
    (List.finRange 2).foldl (fun e a =>
      (List.finRange D.size).foldl (fun e l =>
        match tb.get (q,a) with
        | none => nfaInsert D.size e (q.val * D.size + l.val) a (1 <<< (4 * D.size))
        | some cmd => if cmd.left then e else
            nfaInsert D.size e (q.val * D.size + l.val) a
              (1 <<< (cmd.state.val * D.size + (D.next cmd.write l).val))) e) e) 0

def nfaCompose (size edges mask : ℕ) (a : Fin 2) : ℕ :=
  forceNat mask fun mask =>
  (List.range (4 * size + 1)).foldl (fun out p =>
    if mask.testBit p then out ||| nfaRow size edges p a else out) 0

def nfaIteration (tb : Program 4) (D : TapeDFA) (edges : ℕ) : ℕ :=
  (List.finRange 4).foldl (fun out q =>
    (List.finRange 2).foldl (fun out a =>
      match tb.get (q,a) with
      | none => out
      | some cmd => if cmd.left then
          (List.finRange D.size).foldl (fun out l =>
            (List.finRange 2).foldl (fun out b =>
              nfaInsert D.size out (q.val * D.size + (D.next b l).val) a
                (nfaCompose D.size edges (nfaRow D.size edges
                  (cmd.state.val * D.size + l.val) b) cmd.write)) out) out
        else out) out) edges

def nfaSaturate (tb : Program 4) (D : TapeDFA) : ℕ → ℕ → ℕ
  | 0, edges => edges
  | fuel + 1, edges => forceNat (nfaIteration tb D edges) fun next =>
      if next = edges then next else nfaSaturate tb D fuel next

def nfaBlankStep (size edges reach : ℕ) : ℕ :=
  reach ||| nfaCompose size edges reach 0

def nfaBlankReach (size edges : ℕ) : ℕ → ℕ → ℕ
  | 0, reach => reach
  | fuel + 1, reach => forceNat (nfaBlankStep size edges reach) fun next =>
      if next = reach then next else nfaBlankReach size edges fuel next

def constructCertificate (tb : Program 4) (choice : ℕ) : ℕ :=
  forceNat (choice / 2 % 8) fun extra =>
  let size := extra + 1
  forceNat (size ^ (2 * size - 1)) fun dfaBase =>
  forceNat (choice / 16 % dfaBase) fun code =>
  let D : TapeDFA := ⟨extra,code⟩
  let oriented := if choice % 2 == 1 then tb.flip else tb
  forceNat (nfaInitial oriented D) fun initial =>
  forceNat (nfaSaturate oriented D (2 * (4 * size + 1) ^ 2) initial) fun edges =>
  forceNat (nfaBlankReach size edges (4 * size + 1) 1) fun reach =>
  choice % 2 + 2 * extra + 16 * (code + dfaBase * (reach + 2^(4 * size + 1) * edges))

def checkChoice (tb : Program 4) (choice : ℕ) : Bool :=
  forceNat (constructCertificate tb choice) fun cert => checkCertificateBits tb cert

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem choice_sound {tb : Program 4} {choice : ℕ}
    (h : checkChoice tb choice = true) : ¬ CanStop tb (start 4) := by
  apply checkCertificateBits_sound (val := constructCertificate tb choice)
  simpa only [checkChoice, forceNat_eq] using h

end BeaverBound
namespace BeaverBound

def chunkBytes : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, data => forceNat (data / 256) fun next =>
      data % 256 :: chunkBytes fuel next

def varints : List ℕ → ℕ → ℕ → List ℕ
  | [], _, _ => []
  | b :: rest, acc, shift =>
    let next := acc + (b % 128) * 2^shift
    if b < 128 then next :: varints rest 0 0 else varints rest next (shift+7)

def decodeTokens (chunks : List (ℕ × ℕ)) : List ℕ :=
  varints (chunks.flatMap fun (count,data) => chunkBytes count data) 0 0

def checkGenerated (special : ℕ → Program 4 → Bool) :
    ℕ → Program 4 → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | _ + 1, _, [] => none
  | fuel + 1, tb, v :: rest =>
    if v = 0 then
      match firstMissing tb 106 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkGenerated special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkChoice tb (v-17) then some rest else none

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem generated_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 106 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkGenerated special fuel tb a = some b) :
    TreeBound 106 tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    cases a with
    | nil => simp [checkGenerated] at h
    | cons v rest =>
      by_cases hv : v = 0
      · simp only [checkGenerated, hv, if_true] at h
        cases hFirst : firstMissing tb 106 (start 4) with
        | none => simp [hFirst] at h
        | some k =>
          simp only [hFirst] at h
          apply branch_bound hFirst
          intro m
          obtain ⟨x,y,hy⟩ := succeeds_each h (mem_moves m)
          refine ih ?_ hy
          rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
          omega
      · simp only [checkGenerated, hv, if_false] at h
        by_cases small : v < 17
        · simp only [small,if_true] at h
          by_cases hs : special v tb = true
          · exact hspecial v tb hs
          · simp [hs] at h
        · simp only [small,if_false] at h
          by_cases hc : checkChoice tb (v-17) = true
          · intro M hm
            exact upper_cannot_stop hm (choice_sound hc)
          · simp [hc] at h
end BeaverBound

namespace BeaverBound

private def exceptionalCheck (v : ℕ) (tb : Program 4) : Bool :=
  match v with
  | 11 => decide (tb = [((3,0),⟨1,0,false⟩),((2,1),⟨3,1,false⟩),((0,1),⟨2,0,true⟩),((1,1),⟨2,1,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨0,1,true⟩)])
  | _ => false

set_option maxHeartbeats 0 in
private theorem exceptionalCheck_sound (v : ℕ) (tb : Program 4)
    (h : exceptionalCheck v tb = true) : TreeBound 106 tb := by
  unfold exceptionalCheck at h
  split at h
  next =>
    have ht : tb = [((3,0),⟨1,0,false⟩),((2,1),⟨3,1,false⟩),((0,1),⟨2,0,true⟩),((1,1),⟨2,1,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨0,1,true⟩)] := of_decide_eq_true h
    rw [ht]
    exact SparseReaders.exceptional10
  next => contradiction
end BeaverBound
namespace BeaverBound

/- This is only a data preparation pass. The result is checked again by
`checkPrepared`, including every branch and every certificate. No correctness
assumption about this pass is used by the soundness theorem. -/
def prepareCertificates : ℕ → Program 4 → List ℕ → List ℕ →
    Option (List ℕ × List ℕ)
  | 0, _, rest, acc => some (rest, acc)
  | _ + 1, _, [], _ => none
  | fuel + 1, tb, v :: rest, acc =>
    if v = 0 then
      match firstMissing tb 106 (start 4) with
      | none => none
      | some k => (moves 4).foldlM
          (fun st m => prepareCertificates fuel ((k,m)::tb) st.1 st.2)
          (rest, 0 :: acc)
    else if v < 17 then some (rest, v :: acc)
    else forceNat (constructCertificate tb (v-17)) fun cert =>
      some (rest, (cert+17) :: acc)

def preparedTokens (fuel : ℕ) (tb : Program 4) (xs : List ℕ) : List ℕ :=
  match prepareCertificates fuel tb xs [] with
  | some ([], acc) => acc.reverse
  | _ => []

def checkPrepared (special : ℕ → Program 4 → Bool) :
    ℕ → Program 4 → List ℕ → Option (List ℕ)
  | 0, _, certs => some certs
  | _ + 1, _, [] => none
  | fuel + 1, tb, v :: rest =>
    if v = 0 then
      match firstMissing tb 106 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkPrepared special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkCertificateBits tb (v-17) then some rest else none

theorem prepared_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 106 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkPrepared special fuel tb a = some b) :
    TreeBound 106 tb := by
  induction fuel generalizing tb a b with
  | zero =>
    intro M hm
    exact upper_cannot_stop hm (no_holes_cannot_stop (by omega))
  | succ fuel ih =>
    cases a with
    | nil => simp [checkPrepared] at h
    | cons v rest =>
      by_cases hv : v = 0
      · simp only [checkPrepared, hv, if_true] at h
        cases hFirst : firstMissing tb 106 (start 4) with
        | none => simp [hFirst] at h
        | some k =>
          simp only [hFirst] at h
          apply branch_bound hFirst
          intro m
          obtain ⟨x,y,hy⟩ := succeeds_each h (mem_moves m)
          refine ih ?_ hy
          rw [holes_add, Finset.card_erase_of_mem (missing_is_hole hFirst)]
          omega
      · simp only [checkPrepared, hv, if_false] at h
        by_cases small : v < 17
        · simp only [small,if_true] at h
          by_cases hs : special v tb = true
          · exact hspecial v tb hs
          · simp [hs] at h
        · simp only [small,if_false] at h
          by_cases hc : checkCertificateBits tb (v-17) = true
          · intro M hm
            exact upper_cannot_stop hm (checkCertificateBits_sound hc)
          · simp [hc] at h
end BeaverBound

namespace BeaverBound

/-- This decoder supplies data only; every decoded program is checked by the proof. -/
private def decodeProgram : ℕ → ℕ → Program 4
  | 0, _ => []
  | fuel+1, data => if data = 0 then [] else
      let v := data % 256 - 1
      ((⟨v/32%4, Nat.mod_lt _ (by decide)⟩, ⟨v/16%2, Nat.mod_lt _ (by decide)⟩),
        ⟨⟨v/4%4, Nat.mod_lt _ (by decide)⟩,
          ⟨v/2%2, Nat.mod_lt _ (by decide)⟩, v%2 == 1⟩) ::
        decodeProgram fuel (data/256)

private def programCode (data : ℕ) : Program 4 := decodeProgram 8 data

private theorem branchFour {tb : Program 4} {k : Key 4}
    (h : firstMissing tb 106 (start 4) = some k)
    (p0 : TreeBound (n := 4) 106 ((k,⟨0,0,false⟩)::tb))
    (p1 : TreeBound (n := 4) 106 ((k,⟨0,0,true⟩)::tb))
    (p2 : TreeBound (n := 4) 106 ((k,⟨0,1,false⟩)::tb))
    (p3 : TreeBound (n := 4) 106 ((k,⟨0,1,true⟩)::tb))
    (p4 : TreeBound (n := 4) 106 ((k,⟨1,0,false⟩)::tb))
    (p5 : TreeBound (n := 4) 106 ((k,⟨1,0,true⟩)::tb))
    (p6 : TreeBound (n := 4) 106 ((k,⟨1,1,false⟩)::tb))
    (p7 : TreeBound (n := 4) 106 ((k,⟨1,1,true⟩)::tb))
    (p8 : TreeBound (n := 4) 106 ((k,⟨2,0,false⟩)::tb))
    (p9 : TreeBound (n := 4) 106 ((k,⟨2,0,true⟩)::tb))
    (p10 : TreeBound (n := 4) 106 ((k,⟨2,1,false⟩)::tb))
    (p11 : TreeBound (n := 4) 106 ((k,⟨2,1,true⟩)::tb))
    (p12 : TreeBound (n := 4) 106 ((k,⟨3,0,false⟩)::tb))
    (p13 : TreeBound (n := 4) 106 ((k,⟨3,0,true⟩)::tb))
    (p14 : TreeBound (n := 4) 106 ((k,⟨3,1,false⟩)::tb))
    (p15 : TreeBound (n := 4) 106 ((k,⟨3,1,true⟩)::tb))
    : TreeBound (n := 4) 106 tb := by
  apply branch_bound h
  rintro ⟨q,a,b⟩
  fin_cases q <;> fin_cases a <;> cases b
  · exact p0
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact p7
  · exact p8
  · exact p9
  · exact p10
  · exact p11
  · exact p12
  · exact p13
  · exact p14
  · exact p15

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1 : TreeBound (n := 4) 106 (programCode 0x44290731) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8040201008040200010084002108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3 : TreeBound (n := 4) 106 (programCode 0x4429073211) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10840e6204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4 : TreeBound (n := 4) 106 (programCode 0x4429073212) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201008040200000004020100002020080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5 : TreeBound (n := 4) 106 (programCode 0x4429073213) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10840e6204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6 : TreeBound (n := 4) 106 (programCode 0x4429073214) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201008000200000004020100002000080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7 : TreeBound (n := 4) 106 (programCode 0x4429073215) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084084208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8 : TreeBound (n := 4) 106 (programCode 0x4429073216) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201008000200000004020100002000080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9 : TreeBound (n := 4) 106 (programCode 0x4429073217) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084084208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10 : TreeBound (n := 4) 106 (programCode 0x4429073218) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804e721c481,0x1081084210481,0x10804e721c481,0x1081084210481,0x1080884208481,0x1081084210481,0x1080884208481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x8000600012040080010084020102002080080ce3,0x8004200102040080100804020102002080080ce3,0x8000a00022040080020104020102002080080de3,0x8040200002040080000004020102002080080ce3,0x8001200042050080040204020102802080080ee3,0x8000200002040080000004020102002080080ce3,0x8002200082056080180c04020102c02080080ce3,0x400000101000000404000001010000001040220001100880004400000010000000010002201100008804400010000000010010002020110008000000020000400020000200017ffa8,0x8004200102040080100804020102002080080ce3,0xf307983cc1e60f30000079800079879807980000f301e60001e60f301e679801e7e60079f9801e703855,0x0,0xf307983cc1e60f30000079800079879807980000f301e60001e60f301e679801e7e60079f9801e703855,0x400010001000040004000020010000080020003100080008000040020000100048006200010009000040004000020009000080600000101000000402400000801000001024487fe27,0x0,0x40001000100004000400008001000010002000310008000800004002000010005000620001000a000040008000020009000080600000101000000402400000801000001038487fe27,0x0,0x0,0x101a021188642],
[0x100a021188642,0x101a021188642,0x100a021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x8004200102000880020084002080402010412de4,0x8008200208000000000004020100002000080ce3,0x80082002020008800200880020804020104135e4,0x400020001000080004000200010000000020000001080000004100000010100000010002201100008804400010000000010010002020110008000000020000400020000200017ffa8,0x0,0x400020001000080004000200010000000020000001080000004100000010100000010002201100008804400010000000010010002020110008000000020000400020000200017ffa8,0x0,0x0,0x8000600014040100010084020104002100080ce3,0x8000200104040100000004020104002100080ce3,0x8000a00024040100020104020104002100080de3,0x0,0x8001200044060100040204020104802100080ee3,0x8000200004040100000004020104002100080ce3,0x8002200084066100180c04020104c02100080ce3,0x400000101000000404000001010000001040020001000080004400000010000400010002201100008804400010000000010010002020110008000000020000400020000200017ffa8,0x8004200104040100100804020104002100080ce3,0x8000201004040100000004020104002100080ce3,0x0,0x0,0x400010001000040004000020010000080020003100080008000100020000200048006200010009000040004000020009000080600000101000000402800000802000001024487fe27,0x0,0x40001000100004000400008001000010002000310008000800010002000020006000620001000c000040010000020009000080600000101000000402800000802000001030487fe27,0x0],
[0x0,0x101a021188642,0x100a021188642,0x101a021188642,0x100a021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x8004200104000900020084002080402010814de4,0x0,0x80082002040009000200880020804020108155e4,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_91 : TreeBound (n := 4) 106 (programCode 0x4429073219) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201008040200000004020100802020080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_92 : TreeBound (n := 4) 106 (programCode 0x442907321a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804e721c481,0x1081084210481,0x10804e721c481,0x1081084210481,0x10808c6218481,0x1081084210481,0x10808c6218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x8000600012016480190c84030100081032080ca3,0x8000200102010080000004020100802020080ce3,0x8000600022015880160b0402810010102c080fa3,0x8000200002000080000004020100002000080ce3,0x8001200042014080100804020100201028080ca3,0x8000200002000080000004020100002000080ce3,0x8001200082014080100804020100401030080ca3,0xf3000f6cc003db30007d89b3088b0001e600003cc44d3660f300000f4e63ce04da7301e60f3000001e56,0x8004200102010080000004020100802020080ce3,0x8000200002000080000004020100002000080ce3,0x8008200202010080402004020101002040083ce3,0x8040200002000080000004020100002000080ce3,0xf300f33cc0f30f300f307985b279888b079a41203cc1ea8241e62d901ea45801e7e6004142401e8e97c5,0xf300f33cc0f30f300f30798004bf0000fa98003cc0f4e601152c000f4e60f4e600f301e60f33cc1e7556,0xf301e63cc03ccf301e607985b279888b079abaa03cc1eb7541e62d901eabf001e9cc004235401ecb57c5,0xf301e63cc0798f301e60f30004bf00010230003cc0f4e60118f8000f4e60f4e600f301e60f37983cd556,0x0,0x8000a000220008800200808021008040205029e4],
[0x80006000120008800200804021008040205029e4,0x0,0x8000a000220008800200808021008040205029e4,0x80142001220008800200848021008040205029e4,0x8001200042000880020081002100804020412be4,0xf307983cc007a7300f30798004458000fa98003cc0f4e601152c000f4e60f4e600f301e60f33cc1e7556,0x80022000820008800200820021008040204124e4,0x80042001020008800200840021008040204029e4,0x80042001020008800200840021008040204029e4,0x80402001020008800200840021008040204029e4,0x80082002020008800200880021008040204039e4,0xf307983cc1e60f300001e60008118001ed98003cc489d800f300000f4e63cef760f301e60f33cc1e7e56,0xf300f33cc0f30f300f30798004458000fa98003cc0f4e600f6cc000f4e60f4e600f301e60f33cc1e7556,0xf307983cc1e60f300001e60008118001ed98003cc489d800f300000f4e63cef760f301e60f33cc1e7e56,0xf301e63cc0798f301e60798004458000fa98003cc0f4e600fa98000f4e60f4e600f301e60f33cc5b3556,0x0,0x8000600012026500190c84030100081032080ca3,0x8000200104000100000004020100002000080ce3,0x8000600022027d001f0f8403010008103e080fa3,0x8000200004000100000004020100002000080ce3,0x8001200042024100100804020100201028080ca3,0x8000200004000100000004020100002000080ce3,0x8001200082024100100804020100201038080ca3,0x400000101000000404000001010000001040020001000080004400000010000400010002210100008840400010000000010080020021010080000000100002000100000200017ffa8,0x8004200104020100000004020100802020080ce3,0x8000200102020100100804020100001020080ca3,0x8008200204020100804004020101002040085ce3,0x0,0xf300f33cc0f30f300f30f305b21e697e0f3241203cc1ea8241e62d901ebb2001ed98004142401e8e97c5,0x0,0xf301e63cc03ccf301e60f3097e1e697e0f32baa03cc1eb7541e64bf01ea45801e7e6004235401ecb57c5,0x0],
[0x0,0x8000a000240009000200808021008040209049e4,0x80006000140009000200804021008040209049e4,0xf301e63cc0798f307980f3000408c0010230003cc0f4e600fa98000f4e60f4e600f301e60f37983cd556,0x8000a000240009000200808021008040209049e4,0xf30dc5a2c0798f300011160008118001f530003cc4a85660fa98000f4e63cef760f301e60f37983cde56,0x8001200044000900020081002100804020814be4,0x80042008040009000200840021008040208049e4,0x80022000840009000200820021008040208144e4,0x80002001040009000200800021008040208040e4,0x80042001040009000200840021008040208049e4,0x0,0x80082002040009000200880021008040208059e4,0x0,0xf300f33cc0f30f300f30f3000408c0010230003cc0f4e6010230000f4e60f4e600f301e60f3798d4b556,0x0,0xf301e63cc0798f301e60f3000408c0010230003cc0f4e600fa98000f4e60f4e600f301e60f37983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_173 : TreeBound (n := 4) 106 (programCode 0x442907321b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a5210481,0x1081084210481,0x10804a5210481,0x1081084210481,0x10808c6210481,0x1081084210481,0x10808c6210481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x100a18c210501,0x106218c210501,0x100a18c210501,0x106218c210501,0x101218c210501,0x106218c210501,0x101218c210501,0x8050200402010080402004020101002040082ce3,0x102218c210501,0x106218c210501,0x102218c210501,0x0,0x104218c210501,0x0,0x104218c210501,0x0,0x0,0xc0003000402200080404020101002040080ce3],
[0x40021000000200000004020101002040080ce3,0x140005000402200080404020101002040080ce3,0x40001000000200000004020101002040080ce3,0x240009000804200100804020101002040080ce3,0x40001000000200000004020101002040080ce3,0x440011000804200100804020101002040080ce3,0x0,0x840021000000200000004020101002040080ce3,0x0,0x1040041000000200000004020101002040080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x100a18c210501,0x106218c210501,0x100a18c210501,0x106218c210501,0x101218c210501,0x106218c210501,0x101218c210501,0x0,0x102218c210501,0x106218c210501,0x102218c210501,0x0,0x104218c210501,0x0,0x104218c210501,0x0],
[0x0,0xc0003001008200201004020101002040081ce3,0x0,0x140005001008200201004020101002040081ce3,0x40001000000200000004020101002040080ce3,0x240009000804200100804020101002040080ce3,0x40001000000200000004020101002040080ce3,0x440011000000200000004020101002040080ce3,0x0,0x0,0x0,0x1040041000000200000004020101002040080ce3,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_254 : TreeBound (n := 4) 106 (programCode 0x442907321c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804e721c481,0x1081084210481,0x10804e721c481,0x1081084210481,0x10808c6218481,0x1081084210481,0x10808c6218481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x16c80005b200016c807980001e6000079801e60f31e600007983cc1e6003cfcc00f3f300001e64d995,0x40021002010080000004020100802020080ce3,0xf307980001e600007983cc000798000222c0003cc44d18011160000f6cc3ce0460f303cc1e6000001e56,0x40001002000080000004020100002000080ce3,0x420220001080880000200200000008800042020001100000004020000011000000010001210100004040000012000000010100020001000080084040200004000200040002027bba8,0x40001002000080000004020100002000080ce3,0xfa98002046000fa9807981e679890c1f9a04603cc1ea08c1e60f301ea860c1e60f3041094c1e7037c5,0x0,0x840021002010080000004020100802020080ce3,0x8040001002000080000004020100002000080ce3,0x20020000080080000100200000200800020003300080000800040000000100000006600010000000040000000020009000080628000100020000400080000800000001000487fe27,0x40001002000080000004020100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x8000a000220008800200808022010080406031e4],
[0x80006000120008800200804022010080406031e4,0xf303cc3cc0f30f307980798004458000fa98003cc0f6cc012090000f6cc1e7e6007983cc1e6f30799556,0x8000a000220008800200808022010080406031e4,0x80182002220008800200888022010080406031e4,0x80012000420008800200810022010080404133e4,0x0,0x80022000820008800200820022010080404124e4,0x80082002020008800200880022010080404031e4,0x80042001020008800200840022010080404039e4,0x80402002020008800200880022010080404031e4,0x80082002020008800200880022010080404031e4,0x0,0xf300f33cc0f30f300f30798004458000fa98003cc0f6cc00f6cc000f6cc1e7e6007983cc1e6f3097f556,0x0,0xf301e63cc0798f301e60798004458000fa98003cc0f6cc00fa98000f6cc1e7e6007983cc1e6f30b65556,0x0,0x16c80005b200016c81e600007980000f3001e60f31e600007983cc1e6003cfcc00f3f300001e64d995,0x40021004000100000004020100002000080ce3,0x25f80005b200025f80f302047e6a22bfb288ac5cc1eb115a2610231eb11585e600f341d1585e7037c5,0x40001004000100000004020100002000080ce3,0x420020001080880000200200000004800042000001108000004020000009000000010001200100004840400012000000010100020001000080084000100004000200040002027baa8,0x40001004000100000004020100002000080ce3,0x102379801e7e600007983cc000798000222c0003cc44d18011160000f6cc3ce0460f303cc1e6000001e56,0x0,0x840021004020100000004020100802020080ce3,0x0,0x0,0x40001004000100000004020100002000080ce3,0x0,0x0,0x0,0x0],
[0x0,0x8000a00024000900020080802201008040a051e4,0x8000600014000900020080402201008040a051e4,0xf301e63cc0798f307980f3000408c0010230003cc0f6cc00fa98000f6cc1e7e6007983cc1e67983cd556,0x8000a00024000900020080802201008040a051e4,0x0,0x80012000440009000200810022010080408153e4,0x80082008040009000200880022010080408051e4,0x80022000840009000200820022010080408144e4,0x80002002040009000200800022010080408040e4,0x80042001040009000200840022010080408059e4,0x0,0x80082002040009000200880022010080408051e4,0x0,0xf300f33cc0f30f300f30f3000408c0010230003cc0f6cc010230000f6cc1e7e6007983cc1e6798d4b556,0x0,0xf301e63cc0798f301e60f3000408c0010230003cc0f6cc00fa98000f6cc1e7e6007983cc1e67983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_335 : TreeBound (n := 4) 106 (programCode 0x442907321d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040200010084020102002080080ce3,0x8004200108040200100804020102002080080ce3,0x8000a00028040200020104020102002080080de3,0x8040200008040200000004020102002080080ce3,0x8001200048040200040204020102002080080ee3,0x8000200008040200000004020102002080080ce3,0x8002200088040200080404020102002080080ce3,0x0,0x80106000100c0002010084020102002080080ce3,0x8004200100840020100804020102002080080ce3,0x8010a00020140004020104020102002080080de3,0x8000200008040000000004020102002080080ce3,0x8005200040240008040204020102002080080ee3,0x8000200000040000000004020102002080080ce3,0x8002200080440010080404020102002080080ce3,0x8000200000040000000004020102002080080ce3,0x8004200100840020100804020102002080080ce3,0x0,0x0,0x0,0x8050200402040080402004020102002080082ce3,0x8000200008040000000004020102002080080ce3,0xf307983cc0798f301e61e61e607987980f307983cc01e6f3007983cc1e679803cde600f379801ea19995,0x8000200008040000000004020102002080080ce3,0x8004200108040200100804020102002080080ce3,0x0,0xc0002188000600180c04020102002080080ce3,0x40020008004200000004020102002080080ce3,0x140004188000a00180c04020102002080080ce3,0x40000008000200000004020102002080080ce3,0x240008108001200100804020102002080080ce3],
[0x40000008000200000004020102002080080ce3,0x440010108002200100804020102002080080ce3,0x0,0x840020008004200000004020102002080080ce3,0x8040000008000200000004020102002080080ce3,0x1040040208008200201004020102002080081ce3,0x8040000008000200000004020102002080080ce3,0x2040080008010200000004020102002080080ce3,0x1e601e7e601e61e601e9cc0004bf00012fc0003cc0f30f311160000f30f3097e003cc00f3079f983ffb6,0x0,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003cc0f30f311160000f30f3097e00f3000f307b660f63b6,0x0,0x1240a4220481,0x424084220481,0x1240a4220481,0x424084220481,0x2240c4220481,0x424084220481,0x2240c4220481,0x0,0x424084220481,0x8008000208000200201004020102002080081ce3,0x424084220481,0x0,0x824184220501,0x424084220481,0x824184220501,0x0,0x0,0xc0002418000600412084020102002080082ce3,0x0,0x140004428000a00422104020102002080082de3],
[0x40000008000200000004020102002080080ce3,0x79f9807b660008191bcc01e6f3000408c205533cc1ea08c1e60f301e679801ed98003d39801e7037c5,0x40000008000200000004020102002080080ce3,0x440010008002200000004020102002080080ce3,0x0,0x0,0x8040000008000200000004020102002080080ce3,0x0,0x8040000008000200000004020102002080080ce3,0x2040080408010200402004020102002080082ce3,0x1e603cde600f31e603cfcc0004bf00012fc0003cc0f30f311160000f30f3097e0079800f307a7307cbb6,0x0,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003cc0f30f311160000f30f3097e0079800f307a7307cbb6,0x8010200408040200402004020102002080082ce3,0x0,0x13c0e7220481,0x424084220481,0x13c0e7220481,0x424084220481,0x2340c6220481,0x424084220481,0x2340c6220481,0x0,0x424084220481,0x3ccf303ccf3003ccf33cc0004bf00012fc0003cc102300111600010230799e60001f530798079a25fb6,0x424084220481,0x798f301e6f300798f33cc0004bf00012fc0003cc102300111600010230799e60001f5307980f3262bb6,0x804184220501,0x4084220481,0x804184220501,0x4084220481,0x8020200808040200804004020102002080084ce3],
[0x0,0x14c1ad220501,0x0,0x14c1ad220501,0x8000200000004020102002080080ce3,0x0,0x8000200000004020102002080080ce3,0x400010008002200000004020102002080080ce3,0x0,0x0,0x3cde603cc79803cde63cc0004bf00012fc0003cc111600111600011160f31e600020460f301e64c23b6,0x0,0x799e601e67980799e63cc0004bf00012fc0003cc111600111600011160f31e600020460f300f3448bb6,0x84418c220501,0x4084220481,0x84418c220501,0x4084220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_448 : TreeBound (n := 4) 106 (programCode 0x442907321e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c83cc01e6f30811bcc204603cc1ea08c1e60f301e9cc001e60f30408fcc1e7037c5,0x16c800111600016c83cc0004bf00012fc0003cc102300111600010230799e607980f30798001e61556,0xf307980001e600007983cc00088b000222c0003cc482400111600010231e62d907980f30798000001e56,0x0,0x4918e60f6cc001f533cc00088b000222c0003cc4825e6111600010231e62d981180f30798003ea9cb6,0x108000200000004020100002000080ce3,0x40000000200000000808000001400000001000000004000000010000040002000020000000400020000200090000800010000400000002000000008000400010024852e27,0x8000200000004020100002000080ce3,0x25f800097e3cc1e603cc0004bf00012fc0003cc102300111600010230799e607980f30798003ea93b6,0x8000200000004020100002000080ce3,0x25f80007d4c001e612fc0004bf00012fc0003cc102300111600010230799e607980f30798003ea93b6,0x0,0x4000108000200000004020100002000080ce3,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc102300111600010230799e607980f30798003ee5fb6,0x8000208000200000004020100002000080ce3,0x1e9cc007a73001e9cfcc0004bf00012fc0003cc102300111600010230799e607980f30798003f22bb6,0x2010080408010200402004020102002080082ce3,0x8000200000004020100002000080ce3,0x20100808000200804004020104002100084ce3,0x8000200000004020100002000080ce3,0x0,0x200408018044200100804020100802010080ce3,0x200008108040200000004020100802000080ce3,0x200808028044200100804020100802010080ce3,0xf300012fc7983cc1e612fc0004bf00012fc0003cc102300111600010230799e607980f30798003ea93b6,0x201008048040200000004020100802020080ce3,0x200008008040200000004020100802000080ce3,0x202008088040200000004020100802020080ce3,0x0,0x204008108040200000004020100802000080ce3,0xf3001e9db31e603cc1e9cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6],
[0xf303cc5b21e607983cc3cc0004bf00012fc0003cc102300111600010230799e607980f30798f30799556,0xf3003cfea60f307983cfcc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x210008408041200402004020100802080082ce3,0x204008008040200000004020100802000080ce3,0x220008808041200804004020100802100084ce3,0xf301e64bf07983cc1e63cc0004bf00012fc0003cc102300111600010230799e607980f307987983cd556,0x0,0x800420018044200100804020100802010080ce3,0x108000200000004020100002000080ce3,0x800820028044200100804020100802010080ce3,0x8000200000004020100002000080ce3,0x1000048040200000004020100002020080ce3,0x8000200000004020100002000080ce3,0x2000088040200000004020100002020080ce3,0x0,0x4000108000200000004020100002000080ce3,0x799e60799e600799e9cc0004bf00012fc0003cc102300111600010230799e607980f3079800f52d936,0x8000208000200000004020100002000080ce3,0x79bcc0798f30079bcfcc0004bf00012fc0003cc102300111600010230799e607980f3079800f56a536,0x2010080408010200402004020102002080082ce3,0x8000200000004020100002000080ce3,0x4020100808020200804004020104002100084ce3,0x8000200000004020100002000080ce3,0xfa98002046000fa983cc01e6f307983cc1e6003cc1e9cc01e60f301e9cc001e6f300409b301e7037c5,0x0,0x1ed98007b66000fa985ba8b088b0001e600003cc4835160f3000010231e62dd4d180f3079801e611156,0x1ed98007b66000fa98000f307983cc1e603cc3cc409d160f31e6010231e60f74d180f3079801e611156,0xfa98003ea6000fa98003cc03ccf300f30f303cc1023000f30000102307980007980f3079801e610856,0x0,0x0,0x0,0x1ed98007b66000fa985ba8b07b66001e63cc03cc4835160f3000010231e62dd4d180f3079801e611156],
[0x4400110004008100200800024020100800804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800420018044200100804020100802010080ce3,0x800020108000200000004020100002000080ce3,0x800820028044200100804020100802010080ce3,0x800020008000200000004020100002000080ce3,0x801020048040200000004020100002020080ce3,0x800020008000200000004020100002000080ce3,0x802020088040200000004020100002020080ce3,0x0,0x804020108000200000004020100002000080ce3,0x1e601e9cc01e61e601e9cc0004bf00012fc0003cc102300111600010230799e607980f307983cc225fb6,0x808020208000200000004020100002000080ce3,0x1e603cfcc00f31e603cfcc0004bf00012fc0003cc102300111600010230799e607980f307983cc262bb6,0x810020408004200402004020102002080082ce3,0x800020008000200000004020100002000080ce3,0x820020808004200804004020104002100084ce3,0x1e61e63cc07981e61e63cc0004bf00012fc0003cc102300111600010230799e607980f307983cc5b3556,0x0,0xf379adccc003cfcc012fc00088b000222c0003cc489d80111600010231e62f767980f30798079a268b6,0x3cc007d4c0079bcc00b640004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0x0,0x3cc00f6cc003cfcc012fc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0x3d39803cded983cc003cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6],
[0x3cc03cfcc03cc3cc0408c0004bf00012fc0003cc102300111600010230799e607980f30798079a2d936,0x3d39803cc3cc03cc1e9cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0x0,0x3ccf303cde6003ccf33cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0x3cfcc03cde6003cfcc3cc0004bf00012fc0003cc102300111600010230799e607980f3079807a1bdfb6,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc102300111600010230799e607980f30798079a9f7b6,0x3ccf303cc003cfcc003cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0x3ccf303ccf3003ccf33cc0004bf00012fc0003cc102300111600010230799e607980f30798079a25fb6,0xf379803cde6003cc003cc00088b000222c0003cc489d80111600010231e62f767980f30798079a268b6,0x3cde603cc79803cde63cc0004bf00012fc0003cc102300111600010230799e607980f30798079df1fb6,0x0,0x200000100800000401000000202000000c0002100100008000400000201000000804200010000100040000400020009000080422000101000000400040000800020001000487fe27,0x1000040108000200000004020100002000080ce3,0xf3001e9cc0079f98012fc0000f300003cc007980001e60f307983cc1e600003cc0000f307981e64d995,0x1000040008000200000004020100002000080ce3,0x0,0x1000040008000200000004020100002000080ce3,0x0,0x0,0x1004040108000200000004020100002000080ce3,0x79801e9cc01e679801e9cc0004bf00012fc0003cc102300111600010230799e607980f30798f309bdfb6,0x1008040208000200000004020100002000080ce3,0x79803cfcc00f379803cfcc0004bf00012fc0003cc102300111600010230799e607980f30798f309fabb6,0x20010000080040000100020000200080040003100100008000400000401000009006200010000200040004000020009000080620000101000000400080000801000001004c87fe27,0x1000040008000200000004020100002000080ce3,0x0,0x7981e63cc07987981e63cc0004bf00012fc0003cc102300111600010230799e607980f30798f30b65556,0x0,0x0,0x798007b660079f9800b640004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x0],
[0x79800f4e6003d398012fc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x79f9801e7f530798003cc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x79803cde603cc7980408c0004bf00012fc0003cc102300111600010230799e607980f307980f326a536,0x79f9801e63cc07983cfcc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x0,0x798f301e7e600798f33cc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x7981e61e61e607981e9cc0004bf00012fc0003cc102300111600010230799e607980f307980f329f7b6,0x79bcc01e7e60079bcc3cc0004bf00012fc0003cc102300111600010230799e607980f307980f39fabb6,0x7983cc1e60f307983cfcc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x798f301e6003d398003cc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x798f301e6f300798f33cc0004bf00012fc0003cc102300111600010230799e607980f307980f3262bb6,0x0,0x799e601e67980799e63cc0004bf00012fc0003cc102300111600010230799e607980f307980f362ebb6,0x0,0x80c0e620c481,0x2000080108040200000004020100802000080ce3,0x80c0e620c481,0x2000080008000200000004020100002000080ce3,0x2001080048044200100804020100201028080ca3,0x2000080008000200000004020100002000080ce3,0x2001080088044200100804020100401030080ca3,0x0,0x2004080108040200000004020100802000080ce3,0x1e7e6892b66001e7e9cc0004bf00012fc0003cc102300111600010230799e607980f30798003ee5fb6,0xf303cc5b21e607983cc3cc0004bf00012fc0003cc102300111600010230799e607980f30798f30799556,0x1e9cc985a73001e9cfcc0004bf00012fc0003cc102300111600010230799e607980f30798003f22bb6,0x84418c220501,0x804084200481,0x84418c220501,0x84418c220501,0x0,0x800410018044200100804020100802010080ce3],
[0x108000200000004020100002000080ce3,0x800810028044200100804020100802010080ce3,0x8000200000004020100002000080ce3,0x1020048040200000004020100002020080ce3,0x8000200000004020100002000080ce3,0x2020088040200000004020100002020080ce3,0x0,0x4000108000200000004020100002000080ce3,0x1e601e7e601e61e601e9cc0004bf00012fc0003cc102300111600010230799e607980f307983cc225fb6,0x8000208000200000004020100002000080ce3,0x1e603cde600f31e603cfcc0004bf00012fc0003cc102300111600010230799e607980f307983cc262bb6,0x84418c220501,0x4084200481,0x84418c220501,0x4084200481,0x0,0x80c0e620c481,0x4000100108000200000004020100002000080ce3,0x80c0e620c481,0x4000100008000200000004020100002000080ce3,0x2001100048044200100804020100201028080ca3,0x4000100008000200000004020100002000080ce3,0x2001100088044200100804020100201030080ca3,0x0,0x4004100108040200000004020100802000080ce3,0x0,0x0,0x0,0x84418c220501,0x804084200481,0x84418c220501,0x84418c220501],
[0x0,0x7987981e600003cc0003cc00088b000222c0003cc482400111600010231e62d907980f307987983cde56,0x0,0x800028004200100804020100002010080ce3,0x8000200000004020100002000080ce3,0x798b641e607983cc0003cc00088b000222c0003cc482400111600010231e62d907980f307987983cde56,0x8000200000004020100002000080ce3,0x2000088040200000004020100002020080ce3,0x0,0x0,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003cc102300111600010230799e607980f307987986e4fb6,0x0,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003cc102300111600010230799e607980f3079879862ebb6,0x4418c220501,0x4084200481,0x4418c220501,0x4084200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_657 : TreeBound (n := 4) 106 (programCode 0x442907321f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040200010084020104002100080ce3,0x8000200108040200000004020104002100080ce3,0x8000a00028040200020104020104002100080de3,0x0,0x12c0a5220481,0x424084220481,0x12c0a5220481,0x424084220481,0x2340c6220481,0x424084220481,0x2340c6220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x86418c220501,0x424084220481,0x86418c220501,0x8000200000004020104002100080ce3,0x8001200048040200040204020104002100080ee3,0x8000200008040200000004020104002100080ce3,0x8002200088040200080404020104002100080ce3,0x0,0x1dcd650000165a0bff54b7d14cf0ee6b9f359400041314cf00000ee6b33778b51c788ce718471de75476a00002cb417800007aef7ffbe9f943ba2d264247d3f45cd651dcd65007ea9dbab6b0e237b9b41359400eee25d9400ee88f565003b9e83aca00773d0759400ee89760f77c39,0x8004200100840020100804020104002100080ce3,0x1dcd65ee6b2f73594ee6b45cd6500002540be400009502f900001dcd6caef40a0001ebbd0280000fd51da8000fd51da800012a05fb502f9003b9ca6d6500ee6b2f73597b9aca00eea6c2cc540be7b9e83aca0077447ab2801dcddc359400eee25d9400ee729b59400eee4421445159,0x8000200008040000000004020104002100080ce3,0x8005200040240008140a04020104002100080ee3,0x8000200000040000000004020104002100080ce3,0x8002200080440010080404020104002100080ce3],
[0x8000200000040000000004020104002100080ce3,0x8004200100840020100804020104002100080ce3,0x0,0x0,0x0,0x0,0x8000200008040000000004020104002100080ce3,0x0,0x8000200008040000000004020104002100080ce3,0x8004200108040200100804020104002100080ce3,0x0,0x80022011000c0002080404020104002100080ce3,0x8000201000040020000004020104002100080ce3,0x8002201100140004080404020104002100080ce3,0x0,0x8004201100240008100804020104002100080ce3,0x8000201000040000000004020104002100080ce3,0x8004201100440010100804020104002100080ce3,0x8000201000040000000004020104002100080ce3,0x8000201000840020000004020104002100080ce3,0xf3001e9cc01e6f3001e60f3003db3000f3f3003cc0f4e600f303cc0f4e60f4e60f3001e60f307983ffb6,0x0,0xf3001e9cc01e6f3001e61e6003d39800f4e6003cc0f6cc00f303cc0f6cc1e7e60f3003cc1e60f307cbb6,0x0,0x0,0x8000201004040100000004020104002100080ce3,0x0,0x0,0x1240a4220481,0x424084220481,0x1240a4220481,0x424084220481],
[0x2240c4220481,0x424084220481,0x2240c4220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x824184220501,0x424084220481,0x824184220501,0x0,0x0,0x80202010000c0002804004020104002100084ce3,0x8004201100840020100804020104002100080ce3,0x8020201000140004804004020104002100084ce3,0x0,0x8004201040240008100804020104002100080ce3,0x8000201000040000000004020104002100080ce3,0x8000201000440010000004020104002100080ce3,0x8000201000040000000004020104002100080ce3,0x8004201100840020100804020104002100080ce3,0xf3003cfcc00f3f3003cc0f3003db3000f3f3003cc0fa9800f303cc0fa983cde60f3007983cc079932fb6,0x0,0xf3003cfcc00f3f3003cc1e6003d39800f4e6003cc0f6cc00f303cc0f6cc1e7e60f3003cc1e60f307cbb6,0x0,0x0,0x0,0x0,0x8010200408040200402004020104002100082ce3,0x0,0x13c0e7220481],
[0x424084220481,0x13c0e7220481,0x424084220481,0x2340c6220481,0x424084220481,0x2340c6220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x804184220501,0x4084220481,0x804184220501,0x4084220481,0x8020200808040200804004020104002100084ce3,0x0,0x14c1ad220501,0x0,0x14c1ad220501,0x8000200000004020104002100080ce3,0x204009008001200100804020104002100080ce3,0x8000200000004020104002100080ce3,0x400010008002200000004020104002100080ce3,0x0,0x0,0x0,0x0,0x0,0x84418c220501,0x4084220481,0x84418c220501],
[0x4084220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_786 : TreeBound (n := 4) 106 (programCode 0x4429073220) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c084200481,0x0,0x10c084200481,0x80002008000200000004020100002000080ce3,0x81002048040200000004020100802020080ce3,0x80002008000200000004020100002000080ce3,0x82002088000200000004020100002000080ce3,0x0,0x0,0xf301e63cc1e6f31e7e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x0,0x7983cc1e60f3f31e9cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x1440e6204481,0x7980f31e60f311160f33cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30f3097f556,0x1440e6204481,0x104084200481,0x0,0x220000000880000001200000001800060020001100000004400000010000000010002300100008c00400010000000011000200030010800000002000040002000000200017ffa8,0x0,0x0,0xc00030001008040200a00028040201000100e4,0x0,0xc00030002008080200a00028040201000100e4,0x3d3983cc1e600f3798003cde6008118003ea6003cc1e9cc01e60f301e9cc001e60f30408c001e7037c5,0xc00030004008100200800028040201000100e4,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x25f80005b200025f83cc01e6f307983cc1e6003cc1e9cc01e60f301e9cc001e60000408c001e7037c5,0x0,0x400018000200000004020100002000080ce3,0x0,0x800028000200000004020100002000080ce3,0x8000200000004020100002000080ce3,0x22000000028000000200010000200044000000110000000140000001100000001000120000000110000001200000001100020000400020008000200004000200000040802793a8,0x8000200000004020100002000080ce3,0x2000088000200000004020100002000080ce3,0x0,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300041823b6,0x0,0x1e9cc007a73001e9cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30004108bb6,0x10000408000200000004020100002000080ce3,0x8000200000004020100002000080ce3,0x20000808000200000004020100002000080ce3,0x8000200000004020100002000080ce3,0x8118007b6600081183cc01e6f307983cc1e6003cc1e9cc01e60f301e9cc001e6f300409b301e7037c5,0x0,0x400018000200000004020100002000080ce3,0x0,0x800028000200000004020100002000080ce3,0x8000200000004020100002000080ce3,0x1000048040200000004020100002020080ce3,0x8000200000004020100002000080ce3,0x2000088000200000004020100002000080ce3,0x0,0x0],
[0x799e60799e600799e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f3003d0e09b6,0x0,0x79bcc0798f30079bcfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f3003d0671b6,0x10000408000200000004020100002000080ce3,0x8000200000004020100002000080ce3,0x20000808000200000004020100002000080ce3,0x8000200000004020100002000080ce3,0x0,0x400410018000200000004020100002000080ce3,0x0,0x400810028000200000004020100002000080ce3,0x400010008000200000004020100002000080ce3,0x401010048040200000004020100002020080ce3,0x400010008000200000004020100002000080ce3,0x402010088000200000004020100002000080ce3,0x0,0x0,0xf3001e6f301e63cc01e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f307984c23b6,0x0,0xf3003ccf300f33cc03cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30798448bb6,0x410010408044200100804020100802010080ce3,0xf300f30f30f303cc0f33cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30798d4b556,0x420010808044200100804020100802010080ce3,0x400010008000200000004020100002000080ce3,0x0,0x0,0x0,0x1ed98007b66000fa98007980799e601e681183cc1e6000053880014e21e616c87981e60f3003cc20246,0x0,0x40002000000108000000420000001080000010000200010020000102000000108008010000800050000804000008000400008001000002100000010010000101000000100108493a7,0x0,0x0],
[0x4400110004008100200800028040201000804e4,0x0,0x0,0x40002000002008000008020000020080000100008000200020002002000002008280010000200050000804000008000500008002000008100000010020000101000000100108613a7,0x0,0x0,0x0,0x0,0x0,0x0,0x3d39803cde6003d3980003ec46044587985b4049cc1e9cfcde610231e9cc001e600f3408c3cde7037c5,0x401010000808020200800028040201000000e4,0x401010000008000200800028040201000000e4,0x0,0x0,0x0,0x3d39803cde6003d398003cde6008191803ec4603cc1ea08c1e60f301e9cc001e60f30408fcc1e7037c5,0x401010004008100200800028040201000000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3cc0003cc00003d3992fc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x0,0x3cc7983cc1e603d3983cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x3cc00f6cc003cfcc012fc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x1002000001008000010000800010002004000000110000000140000001100000001000120000000110000001200000001100020000400020008000200004000200002000900f93a8],
[0x3cc03cfcc03cc3cc0408c0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64e09b6,0x3d39803cc79803cc79bcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x0,0x0,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x0,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e653bbb6,0x3cde603cc003cfcde72fc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x3ccf303ccf3003ccf33cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e6e403b6,0x0,0x3cde603cc79803cde63cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f301e64c23b6,0x0,0x79f9800f4e60079f980003ec46044587985b3e63cc1e9cfcde610231e9cc001e603cc408c3cde7037c5,0x0,0x401010000008000200800028040201000000e4,0x0,0x0,0xc01010002008080200a00028040201000100e4,0x16c87980001e607987985b20007d4c001e600003cc4824000f3000011161e62d907981e60f30000001e56,0xc01010004008100200800028040201000100e4,0x79f9800f4e60079f9800f31e60f37b660f4ed983cc1e9db31e60f301e9cc001e6f300409b301e7037c5,0x0,0x3cc7980001e603cc7980f30003cc00010230003cc111600111600011160f31e603cc1e60f30000001556,0x0,0x0,0x0,0x0,0x79f9800f4e60079f983cc01e60007983cc1e6003cc1e9cc01e60f301e9cc001e60000408c001e7037c5,0x0,0x7980001e6000079f992fc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x0,0x7983cc1e60f3079f983cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6],
[0x79800f4e6003d398012fc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x2002000002008000020001000020004004000000110000000140000001100000001000120000000110000001200000001100020000400020008000200004000200004000a02793a8,0x79803cde603cc7980408c0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f34671b6,0x79f9801e679807983cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x0,0x0,0x7981e61e61e607981e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f353bbb6,0x0,0x7983cc1e60f307983cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x799e601e6003d399e72fc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x798f301e6f300798f33cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3dc6bb6,0x0,0x799e601e67980799e63cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f300f3448bb6,0x0,0x80c1a5220501,0x1e601e7e620461e6079bcc01e6f3088b3cc241203cc1ea08c1e60f301e9cc001e7e6004105801e7037c5,0x80c1a5220501,0x2010080008010200000004020102002080080ce3,0x2001080048055200542a040281020010a8082ea3,0x2000080008010200000004020102002000080ce3,0x2001080088056200582c040301020010b0082ca3,0x0,0x0,0x1e7e7303b66001e7e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f309821823b6,0x0,0x1e9cd11da73001e9cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f3088f108bb6,0x84418c220501,0x804184220501,0x84418c220501,0x84418c220501,0x0,0x1e60001e600001e67983cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30f30799556],
[0x1e600097e0007b66000b640004bf00012fc0003cc111600111600011160f31e603cc1e60f30f30799556,0x1e63cc1e60f301e688b3cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30f30799556,0x8000200000004020100002000080ce3,0x0,0x8000200000004020100002000080ce3,0x0,0x0,0x0,0x1e601e7e601e61e601e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30f30c96fb6,0x0,0x1e603cde600f31e603cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30f30be0bb6,0x84418c220501,0x4084200481,0x84418c220501,0x4084200481,0x0,0x80c1a5220501,0x3cc01e6799e603cc079bcc01e6f3088b3cc25f803cc1e9cc01e60f301e9cc001e7e600417f001e7037c5,0x80c1a5220501,0x4020100808020200804004020104002100084ce3,0x2001100048055200944a04028102001128084ea3,0x4000100008020200000004020104002000080ce3,0x20011000880772009c4e04030102001138084ea3,0x0,0xf30b640001e600001e63cc00088b000222c0003cc482400111600011161e62d907981e60f30000001e56,0x0,0x20000100010000080200001000200001004000100010000040040003000100008680020000200010000804200008010500008020000010100000008200000101200000102308703a7,0x0,0x84418c220501,0x804184220501,0x84418c220501,0x84418c220501],
[0x0,0xc084200481,0x0,0xc084200481,0x8000200000004020100002000080ce3,0x0,0x8000200000004020100002000080ce3,0x2000088000200000004020100002000080ce3,0x0,0x0,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003cc111600111600011160f31e603cc1e60f307984c23b6,0x0,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003cc111600111600011160f31e603cc1e60f30798448bb6,0x44084200481,0x4084200481,0x44084200481,0x4084200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2 : TreeBound (n := 4) 106 (programCode 0x44290732) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part010_3 part010_4 part010_5 part010_6 part010_7 part010_8 part010_9 part010_10 part010_91 part010_92 part010_173 part010_254 part010_335 part010_448 part010_657 part010_786

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1027 : TreeBound (n := 4) 106 (programCode 0x44290733) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8040201008040200020104004108002200080de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1029 : TreeBound (n := 4) 106 (programCode 0x4429073411) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084021204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1030 : TreeBound (n := 4) 106 (programCode 0x4429073412) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc0004bf00012fc0003cc1e61e6097e0001e61e605b20003cc1e603cc1e61556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1031 : TreeBound (n := 4) 106 (programCode 0x4429073413) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084021204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1032 : TreeBound (n := 4) 106 (programCode 0x4429073414) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1033 : TreeBound (n := 4) 106 (programCode 0x4429073415) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1034 : TreeBound (n := 4) 106 (programCode 0x4429073416) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1035 : TreeBound (n := 4) 106 (programCode 0x4429073417) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1036 : TreeBound (n := 4) 106 (programCode 0x4429073418) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1081084210481,0x1080421204481,0x1080000200481,0x1080800208481,0x1080000200481,0x1080800208481,0x1080000200481,0x1081084210481,0x1080000200481,0x1081084210481,0x1080000200481,0x0,0x182021220481,0x8040021002004080100804020102002080080ce3,0x182021220481,0x82000220481,0x282042228481,0x82000220481,0x282042228481,0x0,0x482084220481,0x8040001002000080000004000100002080080ce3,0x482084220481,0x82000220481,0x0,0x0,0x0,0x0,0x0,0x101a021188642],
[0x100a021188642,0x101a021188642,0x100a021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x8004200102000880020104004080402010422de4,0x8008200208000000000004000100002000080ce3,0x80082002020008800201080040804020104235e4,0x0,0xf300f33cc0f30f300f30798004458000fa98003cc1e679807d4c001e67983ea6000f307983cc03eb86b6,0x0,0xf301e63cc0798f301e60798004458000fa98003cc1e679808118001e67983ea6000f307983cc0409e6b6,0x0,0x182021220481,0x0,0x182021220481,0x82000220481,0x282042228481,0x82000220481,0x282042228481,0x40101002000100000004000100001100080ca3,0x482084220481,0x0,0x482084220481,0x82000220481,0x0,0x0,0x0,0x0],
[0x0,0x101a021188642,0x100a021188642,0x101a021188642,0x100a021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x1012021188642,0x101a021188642,0x8004200104000900020104004080402010824de4,0x0,0x80082002040009000201080040804020108255e4,0x0,0xf300f33cc0f30f300f30f3000408c0010230003cc1e6798088b0001e67983ea6000f307983cc046506b6,0x0,0xf301e63cc0798f301e60f3000408c0010230003cc1e679808118001e67983ea6000f307983cc0409e6b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1117 : TreeBound (n := 4) 106 (programCode 0x4429073419) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421210481,0x1081084210481,0x1080421210481,0x1080000210481,0x1080842210481,0x1080000210481,0x1080842210481,0x1080000210481,0x1081084210481,0x1080000210481,0x1081084210481,0x1080000210481,0x0,0x100a108210501,0x1062108210501,0x100a108210501,0x1042108210501,0x1012108210501,0x1042108210501,0x1012108210501,0x8040200402010080402004080100802020082ce3,0x1022108210501,0x1002108210501,0x1022108210501,0x0,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x1002021000022],
[0x100a021084222,0x1002021000022,0x100a021084222,0x1002021000022,0x101202118c642,0x1002021000022,0x101202118c642,0x1002021000022,0x80042001020008800201040041008040204029e4,0x8008200208000000000004000100802020080ce3,0x80082002020008800201080042010080404031e4,0x8010200408010080402004080100802020082ce3,0x0,0x8020200808020100804004100100802020084ce3,0x0,0x0,0x100a108210501,0x1062108210501,0x100a108210501,0x1042108210501,0x1012108210501,0x1042108210501,0x1012108210501,0x0,0x1022108210501,0x1002108210501,0x1022108210501,0x0,0x1042108210501,0x0,0x1042108210501,0x0],
[0x0,0x1002021000022,0x100a021084222,0x1002021000022,0x100a021084222,0x1002021000022,0x101202118c642,0x1002021000022,0x101202118c642,0x1002021000022,0x80042001040009000201040041008040208049e4,0x0,0x80082002040009000201080042010080408051e4,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1198 : TreeBound (n := 4) 106 (programCode 0x442907341a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080400208481,0x1081000200481,0x1080400208481,0x1080000200481,0x1080842210481,0x1080000200481,0x1080842210481,0x1080000200481,0x1081000200481,0x1080000200481,0x1081000200481,0x1080000200481,0x0,0x8000600012000080000004000100082000080ce3,0x8010200102010080402004080100802020082ce3,0x800060002200088002010400410010100c080fa3,0x1002000200481,0x1012000208481,0x1002000200481,0x1012000208481,0x0,0x1022108210501,0x1002000200481,0x1022108210501,0x8040200002000080000004000100002000080ce3,0x0,0xf300f33cc0f30f300f30798004bf0000fa98003cc1ed98009bac001ed980f4e600f307980f33cc1e7556,0x0,0xf301e63cc0798f301e60f30004bf00010230003cc1ed98009f78001ed980f4e600f307980f37983cd556,0x0,0x8000a000220008800201008041008040205029e4],
[0x80006000120008800201004041008040205029e4,0x0,0x8000a000220008800201008041008040205029e4,0x80042001220008800201048041008040205029e4,0x8001200042000880020101004100804020422be4,0xf307983cc01e6f300f30798004458000fa98003cc1ed98009bac001ed980f4e600f307980f33cc1e7556,0x8002200082000880020102004100804020422de4,0x80042001020008800201040041008040204029e4,0x80042001020008800201040041008040204029e4,0x80402001020008800201040041008040204029e4,0x80082002020008800201080041008040204039e4,0x0,0xf300f33cc0f30f300f30798004458000fa98003cc1ed98007d4c001ed980f4e600f307980f33cc1e7556,0x0,0xf301e63cc0798f301e60798004458000fa98003cc1ed98008118001ed980f4e600f307980f33cc5b3556,0x0,0x8000600014000100000004000100082000080ce3,0x8000200104000100000004000100002000080ce3,0x8000a00024000900020104004100102010080de3,0x1002000200481,0x1012000208481,0x1002000200481,0x1012000208481,0x8000200804000100000004000100002000080ce3,0x1022108210501,0x1002000200481,0x1022108210501,0x0,0x0,0x0,0x0,0x0],
[0x0,0x8000a000240009000201008041008040209049e4,0x80006000140009000201004041008040209049e4,0xf301e63cc0798f307980f3000408c0010230003cc1ed98008118001ed980f4e600f307980f37983cd556,0x8000a000240009000201008041008040209049e4,0x80042000240009000201040041008040208049e4,0x8001200044000900020101004100804020824be4,0x80042008040009000201040041008040208049e4,0x8002200084000900020102004100804020824de4,0x80002001040009000201000041008040208040e4,0x80042001040009000201040041008040208049e4,0x0,0x80082002040009000201080041008040208059e4,0x0,0xf300f33cc0f30f300f30f3000408c0010230003cc1ed980088b0001ed980f4e600f307980f3798d4b556,0x0,0xf301e63cc0798f301e60f3000408c0010230003cc1ed98008118001ed980f4e600f307980f37983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1279 : TreeBound (n := 4) 106 (programCode 0x442907341b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421210481,0x1081084210481,0x1080421210481,0x1080000210481,0x1080842210481,0x1080000210481,0x1080842210481,0x1080000210481,0x1081084210481,0x1080000210481,0x1081084210481,0x1080000210481,0x0,0x100a108210501,0x1062108210501,0x100a108210501,0x1042108210501,0x1012108210501,0x1042108210501,0x1012108210501,0x8040200402010080402004080101002040082ce3,0x1022108210501,0x1002108210501,0x1022108210501,0x0,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0xc0003000402200080404010101002040080ce3],
[0x40021000000200000004000101002040080ce3,0x140005000402200080404010101002040080ce3,0x40001000000200000004000101002040080ce3,0x240009000804200100804020101002040080ce3,0x40001000000200000004000101002040080ce3,0x440011000804200100804020101002040080ce3,0x0,0x840021000000200000004000101002040080ce3,0x0,0x1040041000000200000004000101002040080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x100a108210501,0x1062108210501,0x100a108210501,0x1042108210501,0x1012108210501,0x1042108210501,0x1012108210501,0x0,0x1022108210501,0x1002108210501,0x1022108210501,0x0,0x1042108210501,0x0,0x1042108210501,0x0],
[0x0,0xc0003001008200201004040101002040081ce3,0x0,0x140005001008200201004040101002040081ce3,0x40001000000200000004000101002040080ce3,0x240009000000200000004000101002040080ce3,0x40001000000200000004000101002040080ce3,0x440011000000200000004000101002040080ce3,0x0,0x0,0x0,0x1040041000000200000004000101002040080ce3,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1360 : TreeBound (n := 4) 106 (programCode 0x442907341c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080400200481,0x1081084210481,0x1080400200481,0x1080000200481,0x1080800200481,0x1080000200481,0x1080800200481,0x1080000200481,0x1081084210481,0x1080000200481,0x1081084210481,0x1080000200481,0x0,0x182021204481,0x0,0x182021204481,0x82000200481,0x282000208481,0x82000200481,0x282000208481,0x0,0x0,0x8040001002000080000004000100002000080ce3,0x0,0x82000200481,0x0,0x0,0x0,0x0,0x0,0x8000a000220008800201008042010080406031e4],
[0x80006000120008800201004042010080406031e4,0xf303cc3cc0f30f307980798004458000fa98003cc1e9cc00a710001e9cc1e7e6007983cc1e6f30799556,0x8000a000220008800201008042010080406031e4,0x80082002220008800201088042010080406031e4,0x80012000420008800201010042010080404233e4,0x0,0x80022000820008800201020042010080404235e4,0x80082002020008800201080042010080404031e4,0x80042001020008800201040042010080404039e4,0x80402002020008800201080042010080404031e4,0x80082002020008800201080042010080404031e4,0x0,0xf300f33cc0f30f300f30798004458000fa98003cc1e9cc007d4c001e9cc1e7e6007983cc1e6f3097f556,0x0,0xf301e63cc0798f301e60798004458000fa98003cc1e9cc008118001e9cc1e7e6007983cc1e6f30b65556,0x0,0x182021204481,0x40021004000100000004000100002000080ce3,0x182021204481,0x82000200481,0x282000208481,0x82000200481,0x282000208481,0x40101002000100000004000100001100080ca3,0x0,0x0,0x0,0x82000200481,0x0,0x0,0x0,0x0],
[0x0,0x8000a00024000900020100804201008040a051e4,0x8000600014000900020100404201008040a051e4,0xf301e63cc0798f307980f3000408c0010230003cc1e9cc008118001e9cc1e7e6007983cc1e67983cd556,0x8000a00024000900020100804201008040a051e4,0x80082000240009000201080042010080408051e4,0x80012000440009000201010042010080408253e4,0x80082008040009000201080042010080408051e4,0x80022000840009000201020042010080408255e4,0x80002002040009000201000042010080408040e4,0x80042001040009000201040042010080408059e4,0x0,0x80082002040009000201080042010080408051e4,0x0,0xf300f33cc0f30f300f30f3000408c0010230003cc1e9cc0088b0001e9cc1e7e6007983cc1e6798d4b556,0x0,0xf301e63cc0798f301e60f3000408c0010230003cc1e9cc008118001e9cc1e7e6007983cc1e67983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1441 : TreeBound (n := 4) 106 (programCode 0x442907341d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x184021220481,0x8040021008004200100804020102002080080ce3,0x184021220481,0x84000220481,0x284042220481,0x84000220481,0x284042220481,0x0,0x2040003000080402010084002102002080080ce3,0x840021008004020100804020102002080080ce3,0x2040005000100804020104004102002080080de3,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x484084220481,0x8040001008000200000004000102002080080ce3,0x484084220481,0x8040001008000200000004000102002080080ce3,0x0,0x80c108220501,0x824108220501],
[0x80c108220501,0x844108220501,0x814108220501,0x844108220501,0x814108220501,0x0,0x824108220501,0x2040080008010200402004080102002080082ce3,0x824108220501,0x2040080408010200402004080102002080082ce3,0x844108220501,0x804108220501,0x844108220501,0x844108220501,0x0,0x60c0c6220481,0x24000220481,0x60c0c6220481,0x4000220481,0x414084220481,0x4000220481,0x414084220481,0x0,0x24000220481,0x0,0x24000220481,0x0,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x0],
[0x80c108220501,0x824108220501,0x80c108220501,0x844108220501,0x814108220501,0x844108220501,0x814108220501,0x4020101008020200804004100102002080084ce3,0x824108220501,0x0,0x824108220501,0x0,0x844108220501,0x804108220501,0x844108220501,0x844108220501,0x0,0x80c108220501,0x0,0x80c108220501,0x4000220481,0x14000220481,0x4000220481,0x14000220481,0x0,0x0,0x0,0x0,0x0,0x44000220481,0x4000220481,0x44000220481],
[0x4000220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1538 : TreeBound (n := 4) 106 (programCode 0x442907341e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c000208481,0x124000208481,0x10c000208481,0x104000208481,0x0,0x104000208481,0x0,0x0,0x124000208481,0x3cc1e60f31e6f31e7e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x124000208481,0x7983cc1e60f3f31e9cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x144021228481,0x1e60f30798f311160f33cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07983cc1e7556,0x144021228481,0x80002008000200000004000100402000080ce3,0x16c800111600016c83cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798001e61556,0x16c800111600025f83cc0000f307983cc1e6000001e9cc01e6f3001e9cde60f31e60f6cfcc1e7033d5,0x0,0xc000208481,0x24000200481,0xc000208481,0x4000200481,0x0,0x4000200481,0x0,0x0,0x24000200481,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798004497fb6,0x24000200481],
[0x1e9cc007a73001e9cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980044d4bb6,0x44000220481,0x4000200481,0x44000220481,0x4000200481,0x0,0x8118007b6600081180003cc1e644587985b21e60f4e9cc3ea6f30f4e9db300f33cc0f6db301e7033d5,0x8118007b660008118417f1e702381183ce0460f301ea08c1e702301e9db301e63cc0f6cc001e7038e5,0x102000000108000001020000001080000001000040001000100022000400028001000080800000200804000808010002008000400008101000008004000101010000100128e83a7,0x0,0x0,0x0,0x8118007b660008118001e61e61ed9f983ea7e60f31e9cfcde6f3f31e9db300f33cc0f6db301e7033d5,0x8118007b6600081183cc0000f307980001e6000001e9cc01e6f3001e9db300f33cc0f6db301e7033d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc000208481,0x24000200481,0xc000208481,0x4000200481,0x0,0x4000200481,0x0,0x0,0x24000200481],
[0x799e60799e600799e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc079800fadf936,0x24000200481,0x79bcc0798f30079bcfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc079800fb1c536,0x44000220481,0x4000200481,0x44000220481,0x4000200481,0x0,0x8118007b66000fa980003cc1e644587985b21e60f4e9cc3ea6f30f4e9db300f3f300f6db301e7033d5,0x20400010000808020201000044020100800000e4,0x20400010000008000201000044020100800000e4,0x20400010001008040201100044020100800000e4,0x0,0x20400010002008080201100044020100800000e4,0xfa98007b66000fa98003cc1e61ed9f983ea7e60f31e9cfcde6f3f31e9db301e6f300f6cc001e7038e5,0x20400010004008100201000044020100800000e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x420020001080080004000200000400800042002000008000000400020000040080004000010000000040040000080100000080400000101000000400000000810000001001087fea7,0xf316c83cc1e600025f80003cc000445800097e000001e9cc01e6f3001e9cc000f31e60f6cfcc1e7033d5,0x0,0x0,0x0,0x20200000020800000202000000208000602a0001000000001100000010002000010002381500002c05400020000000022000200030150800000001000080001000001000087dfa8],
[0x4400110004008100201000044020100800804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40c000208481,0x424000200481,0x40c000208481,0x404000200481,0x0,0x404000200481,0x0,0x0,0x424000200481,0x79801e9cc01e679801e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798f307d7fb6,0x424000200481,0x79803cfcc00f379803cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798f30814bb6,0x0,0x404000200481,0x0,0x7981e63cc07987981e63cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798f30b65556,0x0,0x3cc0003cde63cfd3992fc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3cc007d4c0079bcc00b640004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3cc1e63cc07983d3983cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3cc00f6cc003cfcc012fc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x0],
[0x3cc03cfcc03cc3cc0408c0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fdf936,0x0,0x0,0x3cfcc03cde6003cfcc3cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3cfcc03cde6003cfcc3cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc079807a0517b6,0x3cfcc03cc003cfcfcc3cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x3ccf303ccf3003ccf33cc0004bf00012fc0003cc222c00097e000222c0799e607983cc079807a1bdfb6,0x0,0x3cde603cc79803cde63cc0004bf00012fc0003cc222c00097e000222c0799e607983cc079807a3a3fb6,0x0,0x40c000208481,0x424000200481,0x40c000208481,0x404000200481,0x0,0x404000200481,0x0,0x0,0x424000200481,0x79801e9cc01e679801e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798f307d7fb6,0x424000200481,0x79803cfcc00f379803cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798f30814bb6,0x0,0x404000200481,0x0,0x7981e63cc07987981e63cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798f30b65556,0x0,0x7980001e7e63d39f992fc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x798007b660079f9800b640004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x7983cc1e60f3079f983cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6],
[0x79800f4e6003d398012fc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x0,0x79803cde603cc7980408c0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f381c536,0x0,0x0,0x79bcc01e7e60079bcc3cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x7981e61e61e607981e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f38517b6,0x79bcc01e7e60079bcc3cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x7983cc1e60f307983cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x79bcc01e6003d39bcc3cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x798f301e6f300798f33cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f39fabb6,0x0,0x799e601e67980799e63cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3be0bb6,0x0,0x80c06320c481,0x0,0x80c06320c481,0x804000200481,0x0,0x804000200481,0x0,0x0,0x0,0x1e7e7f5ab66001e7e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798004497fb6,0x0,0x1e9ce04da73001e9cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980044d4bb6,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x0,0x0],
[0x24000200481,0x0,0x4000200481,0x0,0x4000200481,0x1e67981e60f301e60f33cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07983cc1e7556,0x0,0x24000200481,0x1e601e7e601e61e601e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07983cc9bdfb6,0x24000200481,0x1e603cde600f31e603cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc07983cc9fabb6,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x0,0x80c06320c481,0x4000100108000200000004000100002000080ce3,0x80c06320c481,0x804000200481,0x1e6003ea6003cfcc00408c0000f307983cc1e6000001e9cc01e6f3001e611160f31e60f311161e7033d5,0x804000200481,0x1e6003ea6003cfcc007d4c0000f307983cc1e6000001e9cc01e6f3001e611160f31e60f34fbc1e7033d5,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x804000200481,0x844108220501,0x844108220501],
[0x0,0x0,0x0,0x800028000200000004000100002010080ce3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x0,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798798c96fb6,0x0,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798798be0bb6,0x44000220481,0x4000200481,0x44000220481,0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1779 : TreeBound (n := 4) 106 (programCode 0x442907341f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x184021220481,0x0,0x50c0a5220481,0x424084220481,0x50c0a5220481,0x424084220481,0x6140c6220481,0x424084220481,0x6140c6220481,0x21008000200000004000104002100080ce3,0x424084220481,0x0,0x424084220481,0x0,0xc4418c220501,0x424084220481,0xc4418c220501,0x0,0x184021220481,0x84000220481,0x284042220481,0x84000220481,0x284042220481,0x40201008000200000004000104002100080ce3,0x484084220481,0x0,0x6804c6220481,0x0,0x6804c6220481,0x80000220481,0x480884220481],
[0x80000220481,0x480884220481,0x80000220481,0x81000220481,0x80000220481,0x81000220481,0x80000220481,0x0,0x0,0x0,0x0,0x484084220481,0x0,0x0,0x0,0x0,0x80000220481,0x80800220481,0x80000220481,0x80800220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x82000220481,0x0,0x82000220481,0x0,0x0,0x80c108220501,0x824108220501],
[0x80c108220501,0x844108220501,0x814108220501,0x844108220501,0x814108220501,0x0,0x824108220501,0x2040080008010200402004080104002100082ce3,0x824108220501,0x2040080408010200402004080104002100082ce3,0x844108220501,0x804108220501,0x844108220501,0x844108220501,0x0,0x60c0c6220481,0x24000220481,0x60c0c6220481,0x4000220481,0x414084220481,0x4000220481,0x414084220481,0x0,0x24000220481,0x1e601e7e601e61e601e9cc0004bf00012fc0003cc1f5300097e0001f533cc1e601e60f33cc03cc225fb6,0x24000220481,0x1e603cde600f31e603cfcc0004bf00012fc0003cc1f5300097e0001f533cc1e601e60f33cc03cc262bb6,0x844108220501,0x4000220481,0x844108220501,0x4000220481,0x0],
[0x80c108220501,0x824108220501,0x80c108220501,0x844108220501,0x814108220501,0x844108220501,0x814108220501,0x4020101008020200804004100104002100084ce3,0x824108220501,0x0,0x824108220501,0x0,0x844108220501,0x804108220501,0x844108220501,0x844108220501,0x0,0x80c108220501,0x0,0x80c108220501,0x4000220481,0x14000220481,0x4000220481,0x14000220481,0x0,0x0,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003cc204600097e00020463cc1e603cc1e63cc07984c23b6,0x0,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003cc204600097e00020463cc1e603cc1e63cc0798448bb6,0x44000220481,0x4000220481,0x44000220481],
[0x4000220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1908 : TreeBound (n := 4) 106 (programCode 0x4429073420) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c000200481,0x0,0x10c000200481,0x104000200481,0x114000200481,0x104000200481,0x114000200481,0x0,0x0,0xf301e63cc1e6f31e7e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x0,0x7983cc1e60f3f31e9cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x144021204481,0x7980f31e60f311160f33cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30f3097f556,0x144021204481,0x104000200481,0x0,0x0,0x0,0x0,0xc00030001008040201200048040201000100e4,0x0,0xc00030002008080201200048040201000100e4,0x0,0xc00030004008100201000048040201000100e4,0x0,0x0,0x1dcd65ee6b2f73597b9aca0077447ab2f73597b9aca02541acab281dcda09aca0773595dcd653b9ad173597b9bb86b2803b9e83acbdcd65003b9ad8e6b28ee6b639aca3ba23d59403b9ca6d65003ba23d5940077536165001dd4d8594000ee6c166b28eee25d94000ee70c62ce5159,0x0,0x2cb41780007aef40a0000861c468000218711a00002cb417f73594000098bcad1359662f2b44d65ee6b45cd657ea8ed40000773597f5476a0000ee6b28000088e78bb1acdfcbad226b2bf5476a77359400001dcd65ee6b36e6b6b0e329de817b9aca773594003b9acc010da6a],
[0x0,0x0,0x0,0x16c800111600025f83cc0000f307983cc1e6000001e9cc01e6f3001e9cc000f30000f6cc001e7033d5,0x0,0xc000200481,0x0,0xc000200481,0x4000200481,0x14000200481,0x4000200481,0x14000200481,0x0,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300041823b6,0x0,0x1e9cc007a73001e9cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30004108bb6,0x44000200481,0x4000200481,0x44000200481,0x4000200481,0x0,0x20c000200481,0x0,0x20c000200481,0x204000200481,0x214000200481,0x204000200481,0x214000200481,0x0,0x0,0xf3001e6f301e60f301e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f307984c23b6],
[0x0,0xf3003ccf300f307983cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30798448bb6,0x244000208481,0xf300f30f30f307980f33cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30798d4b556,0x244000208481,0x204000200481,0x0,0xc000200481,0x0,0xc000200481,0x4000200481,0x14000200481,0x4000200481,0x14000200481,0x0,0x0,0x799e60799e600799e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f3003d0e09b6,0x0,0x79bcc0798f30079bcfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f3003d0671b6,0x44000200481,0x4000200481,0x44000200481,0x4000200481,0x0,0x20c000200481,0x0,0x20c000200481,0x204000200481,0x214000200481,0x204000200481,0x214000200481,0x0],
[0x0,0xf3001e6f301e63cc01e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f307984c23b6,0x0,0xf3003ccf300f33cc03cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30798448bb6,0x244000208481,0xf300f30f30f303cc0f33cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30798d4b556,0x244000208481,0x204000200481,0x0,0x0,0x0,0xf316c83cc1e600025f80003cc000445800097e000001e9cc01e6f3001e9cc000f30000f6cc001e7033d5,0x0,0x0,0x0,0x0,0x4400110004008100201000048040201000804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401010000808020201000048040201000000e4,0x401010000008000201000048040201000000e4,0x0,0x0,0x0],
[0x0,0x401010004008100201000048040201000000e4,0x0,0x0,0x3d39803cde6003d39800f31e60f381181e81390f301ea08c1e709c81e9db300f37980f6ea601e7033d5,0x0,0x0,0x0,0x3d39803cde6003d39807981e67988118f320bf8f301ea08c1e705fc1ea45800f6cc00f7bf001e7033d5,0x0,0x0,0x3cc0003cc00003d3992fc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x0,0x3cc7983cc1e603d3983cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x3cc00f6cc003cfcc012fc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x3d39803cc79803cde63cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x3cc03cfcc03cc3cc0408c0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64e09b6,0x3d39803cc79803cc79bcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x0,0x0,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x0,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e653bbb6,0x3cde603cc003cfcde72fc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x3ccf303ccf3003ccf33cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e6e403b6,0x0,0x3cde603cc79803cde63cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x0,0x0,0x0,0x401010000008000201000048040201000000e4,0x0],
[0x3d39803cde60079f98001e60001ed98002046000001e9cc01e6f3001e9cde60f31e60f6cde61e7033d5,0x0,0x3d39803cde60079f98001e60001ed98003ea6000001e9cc01e6f3001e9cde60f31e60f6cfcc1e7033d5,0x0,0x0,0x0,0x3cc7980001e603cc7980f30003cc00010230003cc204600097e00020460f31e603cc1e60f30000001556,0x0,0x0,0x0,0x2002000001008000020020000020080002000010001000040020002100020008400020000200080000804200008010800008020000010100000008200000101200000100308703a7,0x3d39803cde60079f983cc00000007983cc1e6000001e9cc01e6f3001e9cc000f30000f6cc001e7033d5,0x0,0x7980001e6000079f992fc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x0,0x7983cc1e60f3079f983cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x79800f4e6003d398012fc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x79f9801e67980799e63cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x79803cde603cc7980408c0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f34671b6,0x79f9801e679807983cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x0,0x0,0x7981e61e61e607981e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f353bbb6,0x0,0x7983cc1e60f307983cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x799e601e6003d399e72fc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x798f301e6f300798f33cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3dc6bb6,0x0,0x799e601e67980799e63cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x0,0x80c108220501,0x1e6097fe620461e6079bcc03ccf3088b3cc222c1e601ea4581e711601ea45801e7e600f6cc001e8e98e5],
[0x80c108220501,0x844108220501,0x814108220501,0x844108220501,0x814108220501,0x0,0x0,0x1e7e7303b66001e7e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f309821823b6,0x0,0x1e9cd11da73001e9cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f3088f108bb6,0x844108220501,0x804108220501,0x844108220501,0x844108220501,0x0,0x1e60001e600001e67983cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30f30799556,0x1e600097e0007b66000b640004bf00012fc0003cc204600097e00020460f31e603cc1e60f30f30799556,0x1e63cc1e60f301e688b3cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30f30799556,0x4000200481,0x0,0x4000200481,0x0,0x0,0x0,0x1e601e7e601e61e601e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30f30c96fb6,0x0,0x1e603cde600f31e603cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30f30be0bb6,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x0],
[0x80c108220501,0x3cc0007980007d4c000b640004bf00012fc0003cc204600097e00020460f31e603cc1e60f30000001556,0x80c108220501,0x844108220501,0x814108220501,0x844108220501,0x814108220501,0x10000080010200000100000800104000000110000000140000001100000001000220000000240000002200000002400020001000020008000200010000200000000000793a8,0x3cc01e7e601e63cc01e9cc0798f30b643cc2d903cc01ebb201e76c801eabf001ed9800f6cc001eacf8e5,0x0,0x3cc03cde601e63cc03cfcc0798f30b643cc2d903cc01ebb201e76c801eabf001ed9800f6cc001eacf8e5,0x0,0x844108220501,0x804108220501,0x844108220501,0x844108220501,0x0,0xc000200481,0x0,0xc000200481,0x4000200481,0x14000200481,0x4000200481,0x14000200481,0x0,0x0,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f307984c23b6,0x0,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f30798448bb6,0x44000200481,0x4000200481,0x44000200481],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_1028 : TreeBound (n := 4) 106 (programCode 0x44290734) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part010_1029 part010_1030 part010_1031 part010_1032 part010_1033 part010_1034 part010_1035 part010_1036 part010_1117 part010_1198 part010_1279 part010_1360 part010_1441 part010_1538 part010_1779 part010_1908

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2165 : TreeBound (n := 4) 106 (programCode 0x44290735) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8040201008040200040204008108002200080ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2166 : TreeBound (n := 4) 106 (programCode 0x44290736) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8040201008040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2167 : TreeBound (n := 4) 106 (programCode 0x44290737) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8040201008040200080404010108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2169 : TreeBound (n := 4) 106 (programCode 0x4429073851) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080421204481,0x1080463208481,0x10804e721c481,0x1080463208481,0x1080421204481,0x10804a5210481,0x10804e721c481,0x10804a5210481,0x1080421200481,0x0,0x16c800111600016c80003cc1e63cc0798408de60f4e67981e6000f4e679801ed98003d39801e7037c5,0x1dcd65ee6b2f73597b9aca02541acab2f73597b9aca01dce536b2800007780157c807748345f20077713283ad17447ab280079126a50001dd11ead173597b9aca001dd11eb059aca3b9aca001dd11eb059aca00eea6c2ca01dcda09aca00eea6c2ca00ee6ee1aca00ee6d0c6e7bdc9,0x0,0x0,0x0,0x0,0xfa98002046000fa980003ce0463cc798040aa600f4e67981e601024e679801ed98003d39801e7037c5,0x16c80799e600016c80003cc1e63cc0798408de60f4e67981e6000f4e679801ed98003d39801e7037c5,0x0,0x0,0x2002000008008000010020000020080000000404000001050080010040000010902048100200020100800400008000001008004000010010000040100000080100000100388732a7,0x4002000000008000040020000000080000000400000001000000010000000010800000000200000100800400008000001008004000004010000010100000100100000100108513a7,0x0,0x0,0x0,0x0,0x0,0x1010822120442],
[0x1008c22120442,0x8000a000200c2002080404002108002010080ce3,0x1008c22120442,0x1010822120442,0x1010822120442,0x1010822120442,0x1010822120442,0x1010822120442,0x8004200100800834020402810082002080482de4,0x400020001000020004000200010000200010000000540000004100000004400000010008280000080001000080800000200010100000040400080101000000401000001010085b9a8,0x80082002010008540204028100820020804835e4,0x0,0xf303cc3cc0f30f300f3636e4082fe00118f8003cdf26dc83defc00f307b661ebb9980079f9801ef8f0c6,0x0,0xf303cc3cc0798f301e66b064084e40012090003cdf360c83e2c800f307b661ebb9980079f9801f1750c6,0x0,0x16c800111600016c80003cc97e3cc1e604459e60f4e6f301e6004c0e6f3001e7e6003db3001e707485,0x0,0x25f80005b200025f80003cc1e63cc0798445bcc0f4e6f301e6000f4e6f3001e7e6003db3001e7037c5,0x16c80001e603cc7980003cc1e63cc00004458000f4e6f301e6000f4e6f3001e7e6003db3001e7037c5,0x0,0x1dce536b2f73597b9aca0007823ff28001e08ffca1dd4e73ff28000077712eca002cb417800007736826b287735cf9aca07af02f28f56503b9aca1dcd73e6b2801dd11eb4135943b9aca001dd11eca6d65003ba9b0b2801dcddc359400eee25d9400ee729b59400ee6d0c7a4f349,0x202000000108000002020000002080000001001000001004000010010000011050802000800000100800820008002001008020000010010000008200000100200000100128783a7,0x0,0x402000001008000010020000010080000000402000001020080010080000011280810040200000100800900008002001008004000002010000008200000100200000100108403a7,0xf3798003ea610339c80003ce0463cc798064be460f4e6f301e601024e6f3001e7e6003db3001e7037c5,0x802000008008000010020000020080000000404000001060080010080000011200880040200040100800900008000001008008000004080000040100000080200000100388532a7,0x0,0x0,0x0,0x0,0x0],
[0x0,0x1010822120442,0x1008c22120442,0x0,0x1008c22120442,0x1010822120442,0x1010822120442,0x1010822120442,0x1010822120442,0x1010822120442,0x8004200100800834020402810084002100884de4,0x80082002000c0402010084002108002002080ce3,0x80082002010008540204028100840021008855e4,0x0,0xf303cc3cc0f30f300f35bd64081180011160003cdf17ac83db3000f307b661ebb5cc007a73001eda90c6,0x0,0xf303cc3cc0798f301e66b06407d4c0010230003cdf360c83d39800f307b661ebb5cc007a73001e9dd0c6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2250 : TreeBound (n := 4) 106 (programCode 0x4429073852) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080422140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2251 : TreeBound (n := 4) 106 (programCode 0x4429073853) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080421204481,0x1080463208481,0x10804e721c481,0x1080463208481,0x1080421204481,0x10804a5210481,0x10804e721c481,0x10804a5210481,0x1080421200481,0x0,0x6000000018000000120000000180000000800020002000080020000200022800000040200000200801400008000002008004000004010000010100000100100000100108513a7,0x77447ab2f73597b9aca07736826b2f73597b9acbdeb33536b280000ee6b2f73595e08ffca000ef59932800fd60c132800f5ed67f2803b9e83ae7cd65ee6b28003b9e83bb86b283b9aca003b9e83b059aca00ef599328001dd11eaca00eea6c2ca00ee6ee1aca00ee749dcfdfec9,0x0,0x400a00000008800010002000040008000000082004000800040001080000002200004008020000080400100000800000200800400000408000004010000008010000010010a53ea7,0x0,0x40002000000008000002020000400280000000400000002000000020800400022001000000200000200801000008000002008004000002010000010100000100100000100108413a7,0x82000000208000002020000002080000000800400002001000020004000022000000800200000200801000008000002008004000004010000010100000100100000100108513a7,0x0,0x0,0x0,0x40200000200800002002000002008000000040400000201000002004000002290500800020000020080140000800000a008004000002010000010100000100100000100188413a7,0x4002000000008000100020000000080000000800000002000000020000000022000000000200000200801000008000002008004000004010000010100000100100000100108513a7,0x0,0x0,0x0,0x0,0x0,0xc00030000c20040a0404014100401210080fa3],
[0x180c22120442,0x280822120442,0x180c22120442,0x280822120442,0x280822120442,0x280822120442,0x280822120442,0x280822120442,0x3d39803cde6003d398003cc03cfcc00f42fc03ccf307983cc03ccf3079f98f307980079f9801e6126b6,0x0,0xf379803cde60079f9803cc007b0ae01ea45803cde601e67984458f4f53f3003cfcc1f53798222d16f36,0x0,0x0,0x0,0x0,0x0,0x6000000018000000120000000180000000800020002000280020000800025000000140200000200802800008000002008008000004020000010200000100200000100109513a7,0x0,0x0,0x16c80001e60b665f80003cc1e63cc0000904bcc0f4e7e601e63cde7e679800fa9800f3f3001e7033d5,0x0,0x0,0x82000000108000002020000002080000000800400001001000020010000025051000800200000100802020008002002008008000004010000008200000100200000100108503a7,0x16c81e61e603ce5f80003cc1e6408c000904bcc0f4e7e601e63cde7e679800fa9800f3f3001e7033d5,0x1002000001008000010020000010080000000408000002020100020080000024080010000800000200802000008000002008004000002020000010200000100200000100128c93a7,0x82000001008000002020001a5a28000000080040000100100002001000002d2d1000800200000100802020008002002008008000004010000008200000100200000100108503a7,0x80200000800800001002000002008000000080400000804040001008000002320108008020008080080110000800000200800800000408000004010000008020000010038a532a7,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x180c22120442,0x280822120442,0x180c22120442,0x280822120442,0x280822120442,0x280822120442,0x280822120442,0x280822120442,0x79f9801e7e6003d39801e6007a17e01e85f803cde601e67984458f6db4e6003d3983db3f3012fc9d736,0x1040041000140804020104004100102200080de3,0xf379803cde60079f9803cc007a91601ea45803cde601e67984458f6db4e6003d3983db3f30222d16f36,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2332 : TreeBound (n := 4) 106 (programCode 0x4429073854) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080422140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2333 : TreeBound (n := 4) 106 (programCode 0x4429073855) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080822140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2334 : TreeBound (n := 4) 106 (programCode 0x4429073856) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080822140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2335 : TreeBound (n := 4) 106 (programCode 0x4429073857) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080822140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2336 : TreeBound (n := 4) 106 (programCode 0x4429073858) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080822140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2337 : TreeBound (n := 4) 106 (programCode 0x4429073859) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080822140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2338 : TreeBound (n := 4) 106 (programCode 0x442907385a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079800f3003db3000f3f3003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2339 : TreeBound (n := 4) 106 (programCode 0x442907385b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10810a4204481,0x1081084210481,0x10810a4204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x1810a4220481,0x8040021001004040201004040102002080081ce3,0x1810a4220481,0x481084220481,0x2810c4220481,0x481084220481,0x2810c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x16c80005b200016c803cc1e60f379801e61e60f301e63cc07987981e603cc3cc0f30f6cc001e740995],
[0x0,0x445800111600025f803cc1e60f379801e61e60f301e63cc07987981e607983cc1e60f6cc001e740995,0x0,0x0,0x0,0x0,0x0,0x3d39800f4e6003d39803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x0,0x0,0x200200000200800002002000002008000008000010400000010080000104000000100200001000200040002020000002000401000001001000a000100000100100000400022793a8,0x0,0x0,0x0,0x0,0x0,0x1810a4220481,0x0,0x1810a4220481,0x481084220481,0x2810c4220481,0x481084220481,0x2810c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x445800111600025f803cc0000f379801e61e60f301e63cc07987981e600003cc0000f6cc001e740995,0x0,0x8118002046000811803cc1e60f379801e61e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0,0x1ed98007b66000fa9803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0xf379803cde60079f9803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x3d39800f4e6003d39803cc1e60f379801e61e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0,0xf379803cde60079f9803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x200200000200800002002000002008000000000010800000010200000108000000100200001000200040002020000002000402000001002000c000200000100200000400022793a8,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2420 : TreeBound (n := 4) 106 (programCode 0x442907385c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079801e6003d39800f4e6003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2421 : TreeBound (n := 4) 106 (programCode 0x442907385d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xc0003002000480010084080100082002080ce3,0x861c4680000b2d05e00002cb4178000218711a00002cb4178ee6b65b33ee29361eccfb8a4d4a3b9ebf47796ccfb8a4d4bdcda1893528ee6b2f73594ee6c166b283b9aca0077712ed8e6b283ba244eadddb8449e2b77881d6e502f90f058c969f7936b9f35940ee6d0c70c5cc9,0xc0003002000880030184080100102004080de3,0xc0003002000480010084080100082002080ce3,0x600000008800000006000000018000040002000800008000400020001000000884000020000100400000040200100000800004000400080004000040008000100010004c53e27,0xc0003002040480010084080108402002080ce3,0xc0003002002480090484080100402010080ce3,0x0,0x600000008800000006000000018000040002000800008000400020001000008084000020001000400000040200100000800040000400800004000400008001000010004853e27,0x1ebbd0280007aef40a00002cb4178000218711a00002cb417bb9acfc77ad4949d6e6b283b9aca3c8970c2d95de90624d4a00069d6a03128fca79127936b36e6b283b9aca0077712ed8e6b283ba658f58b634936165001dd4d8770d65f047fe5000ee6ba1126a5ee6d0c853a9d9,0x0,0xc0003002000080010084080100082000080ce3,0x0,0x0,0x0,0x0,0x0,0x8000420012040080502804080108002200082ce3,0x108822140442,0x8000820022040080502804080108002200082de3,0x108822140442,0x110822140442,0x110822140442,0x110822140442,0x110822140442,0x110822140442,0x120c22140442,0x0,0x120c22140442,0x110822140442],
[0x102300102300010230798003cd0230fa98003ccf307983cfea60f307d4c0021390007d4c001e7f6856,0x8020020802040080502804080108002200086ce3,0x440000008200000004800000011000100000004004800020012000084000000100080008000400000001008000002000204000000010000002040000008100000024001252e28,0x0,0x140005002000480030184080100082002080de3,0x445800111600025f807983cfea60f30798003cc1e7e60079f99e601e61741bcc01e6f30f301e66ddf5,0x140005002000880020104080100102004080de3,0x140005002000080020104080100002004080de3,0x0,0x0,0x1400050020028800a0504080100402010080de3,0x140005002000880020104080100102080080de3,0x6000000028000000220000000280000400020001000020010000200010000801010000200100000800000808001000008000400002001000010010000100010000100108413a7,0x0,0x0,0x140005002000880020104080100102004080de3,0x0,0x1400050020428800a0504080100402200080de3,0x0,0x140005002040080020104080100002200080de3,0x8040001002040080000004080108002200080ce3,0x0,0x200408012040080442204080108002200082ee3,0x208822140442,0x200808022040080442204080108002200082fe3,0x208822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x220c22140442],
[0x0,0x220c22140442,0x210822140442,0xa428225414c2,0x210822140442,0xa428225414c2,0x8040001002040080000004080108002200080ce3,0x440011002040080080404080108002200080ce3,0x0,0x2000480012040080402004080108002200082ce3,0x208822140442,0x2000880022040080402004080108002200082de3,0x208822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x220c22140442,0x0,0x220c22140442,0x210822140442,0x2428225404c2,0x210822140442,0x2428225404c2,0x0,0x800420012040080502804080108002200082ce3,0x208822140442,0x800820022040080502804080108002200082de3,0x208822140442,0x210822140442,0x210822140442],
[0x210822140442,0x210822140442,0x210822140442,0x220c22140442,0x0,0x220c22140442,0x210822140442,0xa428225414c2,0x210822140442,0xa428225414c2,0xf307983cc1e60000798079800079879807980001e601e60001e61e601e9cc001f530007d4c001e703855,0x0,0x798007a730079f980081192fc7987980799f531e601e61e61e697e01e9cc001f53000408c001f0817c5,0x0,0x0,0x802000002002000020020000020001000400200001000200010002000010000100100000200100000800080008001000008040000004100000010400000101000000101108513a7,0x0,0x802000002002000020008400020001000400200001000200010002000010000100100000200100000800080008001000008040000004100000010400000101000000101108513a7,0x7980798f300f3798079f992fc7987980799f531e601e61e61e697e01e9cc001f53000408c001f0817c5,0x798f300f30f3079cbf07992fc7987980799f531e601e61e61e697e01e9cc001f53000408c001f0817c5,0x0,0x0,0x0,0x0,0x798f300f3f300798f307992fc7987980799f531e601e61e61e697e01e9cc001f53000408c001f0817c5,0x0,0x799e600f33cc0799e607992fc7987980799f531e601e61e61e697e01e9cc001f53000408c001f44d7c5,0x0,0xf307983cc1e60000798079800079879807980001e601e60001e61e601e9cc001f530007d4c001e703855,0x0,0x2000480012040080402004080108002200082ce3,0x208822140442],
[0x2000880022040080402004080108002200082de3,0x208822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x320c22140442,0x0,0x320c22140442,0x22140442,0x8420225414c2,0x22140442,0x8420225414c2,0x0,0xc00410012040080080404080108002200080ce3,0x808c22140442,0xc00810022040080080404080108002200080ce3,0x808c22140442,0x810822140442,0x810822140442,0x810822140442,0x810822140442,0x810822140442,0x1e601e7e601e61e601e6003cc1e9cc00f3fa983cc7987983cc222cf307d4c1e7f530007d4c001e6121a6,0x0,0x1e601e7e600f31e603cc007981f16400f4ed983cc7987983cc222cf307d4c1e7f530007d4c001e6121a6,0x800022140442,0x8420225414c2,0x8420225414c2,0x8420225414c2,0x0],
[0x4000500012040080804004080108002200084ce3,0x0,0x4000900022040080804004080108002200084de3,0x0,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x0,0x0,0x4020101802040080804004080108002200084ce3,0x22140442,0x420225404c2,0x22140442,0x420225404c2,0x0,0x0,0x808c22140442,0x0,0x808c22140442,0x810822140442,0x810822140442,0x810822140442,0x810822140442,0x810822140442,0x1e601e6f301e63cc01e6003cc1f53000f3fa983cc7987983cc2412f307d4c1e7f530007d4c001e6121a6,0x0,0x1e601e6f300f33cc03cc007981ed9800f4ed983cc7987983cc222cf307d4c1e7f530007d4c001e6121a6,0x800022140442,0x8420225414c2,0x8420225414c2],
[0x8420225414c2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2614 : TreeBound (n := 4) 106 (programCode 0x442907385e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600018040010000004010108002200080ce3,0xf30000b6400088b00008118004458000fa98003ccf307983cc01e6f307d4c1e60f30007d4c001e610856,0x8000a00028040010000004010108002200080ce3,0xf300012fc0004bf0000fa98004458000fa98003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6,0x1012022140442,0x1012022140442,0x1012022140442,0x1012022140442,0x1012022140442,0x8004200102000880020404010088002200482de4,0x0,0x8008200208000402010084002100082002080ce3,0x8008200208000000000004000100002020080ce3,0x8008200208000804020104004100102004080de3,0x8008200208000000000004000100002000080ce3,0x8008200208000000000004000100202008080ce3,0x8008200208000000000004000100002000080ce3,0x8008200208000000000004000100402010080ce3,0x8008200208000000000004000100002000080ce3,0x8008200208000000000004000100802020080ce3,0x8040200102000880020404010080802020482de4,0x0,0x80402002020008800204080100810020404835e4,0x0,0xf303cc3cc1e60f303cc0798004458000fa98003ccf307983db3000f3079f99e607980079f9801eda8856,0x0,0x0,0x80082002020008800204080100880022004835e4,0x0,0x0,0x112022140442],
[0x0,0x112022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x8008200820008800204020100880022000804e4,0x0,0x10008400820008800204020100880022000804e4,0x2022140442,0x802022140442,0x2022140442,0x802022140442,0xf300f33cc0f30f300f30798004458000fa98003ccf307983cfcc00f307d4c1e60f30007d4c001e7f6856,0x0,0x0,0x0,0x0,0x0,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x462022741d02,0x0,0x462022741d02,0x2022140442,0x8420225414c2,0x2022140442,0x8420225414c2],
[0xf301e63cc0798f301e60798004458000fa98003ccf307983d39800f307d4c1e60f30007d4c001e9dc856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2679 : TreeBound (n := 4) 106 (programCode 0x442907385f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xc0003004000500010084100100082002080ce3,0x0,0xc0003004000900030184100100102004080de3,0xc0003004000500010084100100082002080ce3,0x600000008800000006000000018000080004000800010001000040002000000888000020000100400000040200200000800004000400080004000040008000100010004c53e27,0xc0003004040500010084100108402002080ce3,0xc0003004002500090484100100402010080ce3,0x0,0x600000008800000006000000018000080004000800010001000040002000008088000020001000400000040200200000800040000400800004000400008001000010004853e27,0x1ebbd0280007aef40a0001ebbd028000218711a00002cb417bb9acfe548e4f1a22e6b2877359400fdc910140003c11ff940011d956eefabeca01fab29bb45cd653b9aca001dd11eae7cd6503ba69491bb040536165000ee6b29dcd65f047fe5000ee6b29dcd65ee6d0cfc351c9,0x0,0xc0003004000100010084100100082000080ce3,0x0,0x0,0x0,0x0,0x0,0x440021004000500080404100100082002080ce3,0x40021004020100000004100100002020080ce3,0x440021004000900080404100100102004080ce3,0x40021004000100000004100100002000080ce3,0x0,0xf307980001e6003d3980f31e607980000f3000000001e6000079bcc01e600001f53000f300001e64d485,0x0,0x0,0x40021004020100000004100100802020080ce3,0x620020001000080000000200000900800020003100040008000100000000200000006200010000000040000000020020000080620000101000000204000000800000001000487ee27,0x0,0x40021004000100000004100100002000080ce3,0x0],
[0x0,0x0,0x0,0x0,0x140005004000500030184100100082002080de3,0x22000000028000000220000000280002000000002000000020000400020000004000000800200000800002008002000008000000010004000010000000100040000100108793a7,0x140005004000900020104100100102004080de3,0x140005004000100020104100100002004080de3,0xa00000008800000012000000028000080004000800010001000040002000004208000020000800400000100200200000800004000400080004000040008000100010006953e27,0x25f800111600025f80f325f87980098d30025f8f31e600f379bcc01e603cc1f56cc0f304bf1e651145,0x1400050040029000a0504100100402010080de3,0x140005004000900020104100100102100080de3,0x0,0x0,0x0,0x140005004000900020104100100102004080de3,0x0,0x1400050040429000a0504100100402200080de3,0x0,0x140005004040100020104100100002200080de3,0x0,0xc0003004000500010084100100082002080ce3,0x0,0x140005004000900020104100100102004080de3,0x40001004000100000004100100002000080ce3,0x0,0xf307980001e600007980f31e607980000f3000000001e6000079bcc01e600001f53000f300001e64d485,0x40001004000100000004100100402010080ce3,0x40001004000100000004100100002100080ce3,0x0,0x600020001000080000000200000000800020003000040008000100000000200000006000010000000040000000020020000080400000101000000204000000800000001000487ee27,0x0],
[0x40001004000100000004100100002000080ce3,0x40001004000100000004100102002080080ce3,0x0,0x40001004000100000004100104002100080ce3,0x0,0x0,0x200408014040100844204100108002200084ee3,0x0,0x200808024040100844204100108002200084fe3,0x0,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x220822140442,0x0,0x220822140442,0x210822140442,0x240822140442,0x210822140442,0x240822140442,0x0,0x0,0x0,0x0,0x0,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442],
[0x220822140442,0x0,0x220822140442,0x210822140442,0x240822140442,0x210822140442,0x240822140442,0x440011004040100080404100108002200080ce3,0x40101004040100000004100108002200080ce3,0x0,0x800420014040100904804100108002200084ce3,0x0,0x800820024040100904804100108002200084de3,0x0,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x220822140442,0x0,0x220822140442,0x210822140442,0x240822140442,0x210822140442,0x240822140442,0x0,0x0,0x0,0x0,0x0,0x410822140442],
[0x410822140442,0x410822140442,0x410822140442,0x410822140442,0x420022140442,0x0,0x420022140442,0x0,0x3ccf303ccf3003ccf300f3003cfcc00f3f3003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6,0x400022140442,0x3cde603cc79803cde603cc003db3000f6cc003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6,0x0,0x798007a730079f980088b07981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001ead3485,0x0,0x79800f3f3001ed980102307981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001eacf7c5,0x0,0x0,0x799e600f3000079fb66f307981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001eacf7c5,0x0,0x0,0x7981e60f31e607981e6f307981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001eacf7c5,0x79f9800f3000079fb66f307981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001eacf7c5,0x0,0x0,0x798f300f3f300798f30f307981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001f44d7c5,0x0,0x799e600f33cc0799e60f307981e67980f31ed9bcc01e60f31e63cc01e9cc001f53000408c001ecb57c5,0x800400002000100020010000020055000800200002000100020002000020000400080000200200000800200008002000008040000004100000010400000101000000102908513a7,0x40201004040100000004100108002200080ce3,0x0,0x2000480014040100402004100108002200082ce3,0x2040080104040100402004100108002200082ce3],
[0x2000880024040100402004100108002200082de3,0x2040080404040100402004100108002200082ce3,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0xee6b2800003b9aca00007735a2e6b28ee6b2800000ee6c166b2bb9acdb9acaee6b38c388d7735c0b417f735a2e6b2877359d502f9ee6b283ba06082f00ee6d04d651dcd73e6b283b9ae7cd6503ba23d5940077536165001dd4d8594000f047fe5000eee25d94000efd2ad3c468c9,0x0,0x10000800010008000100008000100008002000200002000080020002000020002000040000800200000801000008002000008040000010100000010400000101000000100508793a7,0x22140442,0x8420225414c2,0x22140442,0x8420225414c2,0x0,0x418e307a73001e6f30097e1e607987980f30811c08c1e60f3079bcc01e9cc003db3000f6cc001ea19995,0x620021001000002000000200000000020020003100080000000080020000200000006200010008000040000000080020000080400000101000000404000000410000001001087fda7,0x42aec1e6f300799e6011161e607987980f30811c08c1e60f3079bcc01e9cc003db3000f6cc001ea3bc55,0x600030001000000000000200000000000020003000080000000080020000200000006000010008000040000000080020000080400000101000000404000000410000001001087fda7,0x812822140442,0x812822140442,0x812822140442,0x812822140442,0x812822140442,0x822022741502,0x0,0x822022741502,0x802022140442,0x8420225414c2,0x8420225414c2,0x8420225414c2,0x0],
[0x4000500014040100804004100108002200084ce3,0x0,0x4000900024040100804004100108002200084de3,0x0,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x210822140442,0x20022140442,0x0,0x20022140442,0x22140442,0x40022140442,0x22140442,0x40022140442,0x0,0x0,0x0,0x0,0x400030001000000000000200000000000020003000080000000080020000200000006000010008000040000000080020000080400000101000000404000000410000001001087fda7,0x812822140442,0x812822140442,0x812822140442,0x812822140442,0x812822140442,0x822022741502,0x8100204040100000004100108002200080ce3,0x822022741502,0x802022140442,0x8420225414c2,0x8420225414c2],
[0x8420225414c2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2904 : TreeBound (n := 4) 106 (programCode 0x4429073860) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1012022108442,0x1012022104442,0x1012022108442,0x1012022104442,0x1012022108442,0x1012022108442,0x1012022108442,0x1012022108442,0x1012022108442,0x8000a00024000900020400810080802020180de4,0x0,0x8000a000240009000204008100810020402815e4,0x0,0x1012022120442,0x0,0x1012022120442,0x0,0x100a02218c642,0x100a022184642,0x100a022188442,0x100a022184642,0x100a02218c642,0x100a022188442,0x100a022188442,0x100a022188442,0x100a02218c642,0x8000600014000900020400410080802020180de4,0x0,0x80006000140009000204004100810020402815e4,0x8004200108040000000004000102002080080ce3],
[0x80006000140009000204004100820020804824e4,0x8000200108040000000004000104002100080ce3,0x80006000140009000204004100840021008844e4,0x0,0x1012022108442,0x101a022184642,0x1012022108442,0x101a022184642,0x1012022108442,0x1012022108442,0x1012022108442,0x1012022108442,0x1012022108442,0xf30007d4c0798f3079fa73000408c0010230003ccf307983d39800f30798f4e600f300798f301e9dc856,0x0,0xf30007d4c0798f3079fa73000408c0010230003ccf307983d39800f30799e7e6007980799e601e9dc856,0x0,0x0,0x0,0x0,0xf300012fc0004bf0001023000408c0010230003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6,0x1012022140442,0x1012022140442,0x1012022140442,0x1012022140442,0x1012022140442,0x8004200104000900020404010088002200884de4,0x0,0x0,0x0,0x0,0x25f80007983cc25f80f3000408c0010230003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6],
[0x208008200040000000004000108002200080ce3,0x8000200040000000004000108002200080ce3,0x408010200040000000004000108002200080ce3,0x8000200040000000004000108002200080ce3,0x808020200040000000004000108002200080ce3,0x804021004000900020404010088002200884de4,0x1008040200040000000004000108002200080ce3,0x10080410040009000204080100880022008855e4,0x0,0x0,0x0,0x8000200040000000004000108002200080ce3,0x80082002040009000204080100880022008855e4,0x0,0x0,0x112022140442,0x0,0x112022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x3cc079bcc003cfcc089a3000408c0010230003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6,0x1010040400040040000004040108002200080ce3,0x7980799e6003d398089a3000408c0010230003ccf307983cc03ccf307d4c1e60f30007d4c001e6126b6,0x2022140442,0x802022140442,0x2022140442,0x802022140442,0xf300f33cc0f30f300f30f3000408c0010230003ccf307983db3000f307d4c1e60f30007d4c001ef8e856,0x0],
[0x0,0x0,0x0,0x0,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x462022741d02,0x1020040800040040000004040108002200080ce3,0x462022741d02,0x2022140442,0x8420225414c2,0x2022140442,0x8420225414c2,0xf301e63cc0798f301e60f3000408c0010230003ccf307983d39800f307d4c1e60f30007d4c001e9dc856]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_2168 : TreeBound (n := 4) 106 (programCode 0x44290738) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part010_2169 part010_2250 part010_2251 part010_2332 part010_2333 part010_2334 part010_2335 part010_2336 part010_2337 part010_2338 part010_2339 part010_2420 part010_2421 part010_2614 part010_2679 part010_2904

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3017 : TreeBound (n := 4) 106 (programCode 0x44290739) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x8040201008040200100804020108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3019 : TreeBound (n := 4) 106 (programCode 0x4429073a51) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80402010000c0002080404220108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3020 : TreeBound (n := 4) 106 (programCode 0x4429073a52) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10818e7204481,0x1081084210481,0x10818e7204481,0x1081000200481,0x1081000208481,0x1081000200481,0x1081000208481,0x1081084210481,0x1081084210481,0x1081000200481,0x1081084210481,0x1081084210481,0x0,0x80006000100c0020080404220102002080080ce3,0x8004200100840020000004200102002080080ce3,0x8000a00020140020080404220102002080080ce3,0x8040200000040020000004200102002080080ce3,0x8001200040240020100804220102002080080ce3,0x8040200000040020000004200102002080080ce3,0x8002200080440020100804220102002080080ce3,0x8040200100840020000004200102002080080ce3,0x8004200100840020000004200102002080080ce3,0xf3001e9cc01e6f3001e6003cc3cc3cc0f303cc3cfcc007d4de63cfcc0079897e0f300007987983cc33b6,0x0,0xf3003cfcc00f3f3003cc003cc3cc3cc0f303cc3cfcc007d4de63cfcc0079897e0f300007987983cc33b6,0x8010200402040020402004280102002080082ce3,0xf300f33cc0f30f300f30003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e60f3000081183cc1e7556,0x8020200804040020804004300102002080084ce3,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e60f3000088b07983cd556,0x0,0xf30c5922c0000f30000000f307983cc1e603cc3db3b65e9cc3cc03cc0097e2d9811800081183cc1e7e56],
[0xf30000b6400088b00007983cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1e7556,0x0,0xf300012fc0004bf0000f303cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1e93b6,0xf3088b3cc0004bf00f30003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1e7556,0xf3000408c003db30003cc03cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1eeed6,0xf307983cc0002d900f30003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1e7556,0xf3000f6cc003db30007980f307983cc1e603cc3db3b65e9cc3cc03cc0097e2d9811800081183cc1f7156,0xf30000b64222cf300007983cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1e7556,0xf3001e9cc01e6f3001e6003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc225fb6,0xf303cc3cc03ccf303cc0003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc97f556,0xf3003cfcc00f3f3003cc003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc262bb6,0xf307983cc1e60f30000000f307983cc1e603cc3db3b65e9cc3cc03cc0097e2d9811800081183cc1e7e56,0xf300f33cc0f30f300f30003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc1e7556,0xf307983cc1e60f30000000f307983cc1e603cc3db3b65e9cc3cc03cc0097e2d9811800081183cc1e7e56,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3cfcc007d4e22c03cc008119e6079800081183cc5b3556,0x0,0x80006000100c0020080404220104002100080ce3,0x8000200100040020000004200104002100080ce3,0x8000a00020140020080404220104002100080ce3,0x0,0x8001200040240020100804220104002100080ce3,0x80012000400808020208044200180004201109e4,0x8002200080440020100804220104002100080ce3,0x80022000800808020208044200180004201109e4,0x8004200100840020000004200104002100080ce3,0x8000201000040020000004200104002100080ce3,0x0,0x8004201000840020000004200104002100080ce3,0x8010200402040020402004280104002100082ce3,0x0,0x8020200804040020804004300104002100084ce3,0x0],
[0x0,0xf301e63cc0000f307980003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983cd556,0x0,0x0,0xf300012fc0004bf0000f303cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983cf3b6,0xf307992fc0004bf01e60003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983cf3b6,0xf3000408c003db30003cc03cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983ebb56,0xf307983cc0002d901e60003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983cd556,0x0,0xf30b6622c0798f30000798f307983cc1e603cc3db3b65e9cc79803cc0097e2d9811800088b07983cde56,0xf3001e9cc01e6f3001e6003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07984c23b6,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983cd556,0xf3003cfcc00f3f3003cc003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b0798448bb6,0x0,0xf300f33cc0f30f300f30003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b0798d4b556,0x0,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3cfcc007d4e5f803cc0088b1e603cc00088b07983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3101 : TreeBound (n := 4) 106 (programCode 0x4429073a53) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000140004080404220108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3102 : TreeBound (n := 4) 106 (programCode 0x4429073a54) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce7204481,0x1080000210481,0x1081ce7204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x181ce7220481,0x8040021000804000000004000102002080080ce3,0x181ce7220481,0x80000220481,0x2818c6220481,0x80000220481,0x2818c6220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x8000a000201008040208008200220008804021e4],
[0x80006000101008040208008200220008804020e4,0xf303cc3cc1e60f307980007983cc1e60f307983cfcc00f6cc003cfcc00fa98f30798000fa98f30799556,0x8000a000201008040208008200220008804021e4,0x8000a000201008040208008200220008804021e4,0x80012000401008040208008200220008804023e4,0x8000a004001008040208008200220008804020e4,0x80022000801008040208008200220008804025e4,0x8000a000201008040208008200220008804021e4,0x80042001001008040208008200220008804029e4,0x80102004001008040208008200220008804020e4,0x80082002001008040208008200220008804031e4,0x0,0x80102004001008040208008200220008804020e4,0x0,0x80202008001008040208008200220008804060e4,0x0,0x181ce7220481,0x0,0x181ce7220481,0x80000220481,0x2818c6220481,0x80000220481,0x2818c6220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x80002000201008040208008200240009008040e4,0x80006000101008040208008200240009008040e4,0x0,0x8000a000201008040208008200240009008041e4,0x8000a000201008040208008200240009008041e4,0x80012000401008040208008200240009008043e4,0x8000a008001008040208008200240009008041e4,0x80022000801008040208008200240009008045e4,0x8000a000201008040208008200240009008041e4,0x80042001001008040208008200240009008049e4,0x80202008001008040208008200240009008040e4,0x80082002001008040208008200240009008051e4,0x0,0x80102004001008040208008200240009008060e4,0x0,0x80202008001008040208008200240009008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3183 : TreeBound (n := 4) 106 (programCode 0x4429073a55) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000240008100804220108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3184 : TreeBound (n := 4) 106 (programCode 0x4429073a56) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080824340c82]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3185 : TreeBound (n := 4) 106 (programCode 0x4429073a57) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080024040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3186 : TreeBound (n := 4) 106 (programCode 0x4429073a58) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080824340c82]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3187 : TreeBound (n := 4) 106 (programCode 0x4429073a59) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080024040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3188 : TreeBound (n := 4) 106 (programCode 0x4429073a5a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079800f3003db3000f3f3003cfcc1e63cc003cfcc1e9cc1e60f3001e9cc007983ffb6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3189 : TreeBound (n := 4) 106 (programCode 0x4429073a5b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10810e7204481,0x1081084210481,0x10810e7204481,0x1081000200481,0x1081000208481,0x1081000200481,0x1081000208481,0x1081084210481,0x1081084210481,0x1081000200481,0x1081084210481,0x1081084210481,0x0,0x1810e7220481,0x8040021001004040100804020102002080080ce3,0x1810e7220481,0x81000220481,0x2810c6220481,0x81000220481,0x2810c6220481,0x481084220481,0x481084220481,0x81000220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x0],
[0x16c800111600016c81e60003ea6f311160003cfcfcc03cde61e9cfcc079a22c7983cc0798001e61556,0x7983cc1e60f307981e60003cc00011160003cfcfcc03cde6003cfcc0799e607983cc0798000001556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1810e7220481,0x0,0x1810e7220481,0x81000220481,0x2810c6220481,0x81000220481,0x2810c6220481,0x481084220481,0x481084220481,0x81000220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x1dcd65ee6b2f73597b9aca0077447ab2f73597b9aca02541acab281dcda09aca0773595dcd653b9ad173597b9bb86b2803b9e83acbdcd65003b9ad8e6b28ee88f565003ba23d59403b9caa8ffca3ba23d5940077536165001dd4d8594000ee6c166b28eee25d94000ee70c62ce5159,0x7980001e60f307980f30003cc00010230003cfcde603cde6003cde60f31e603cc1e60f30000001556,0x0,0x0,0x0,0x0,0x0,0x402000001008000010020000010080000040010000100040002002100002008500020000201080000804200008010a00008000400002100000008008000101020000100308403a7,0x0,0x3cc7980001e603cc7980f30003cc00010230003cfcde603cde6003cde60f31e603cc1e60f30000001556,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3270 : TreeBound (n := 4) 106 (programCode 0x4429073a5c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079801e6003d39800f4e6003cfcc3cc3cc003cfcc3cfcc1e60f3003cfcc00f307cbb6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3271 : TreeBound (n := 4) 106 (programCode 0x4429073a5d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600012040080010084210108002200080ce3,0x8040200102040080100804220108002200080ce3,0x8000a00022040080020104210108002200080de3,0x8040200002040080000004200108002200080ce3,0x8001200042040080040204220108002200080ee3,0x8040200002040080000004200108002200080ce3,0x8002200082040080080404220108002200080ce3,0x8040200402040080402004280108002200082ce3,0x8004200102040080100804220108002200080ce3,0x0,0x103a0e7204481,0x8000200002010080000004000100001020080ca3,0x103a0e7204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481,0x0,0x1002100210501,0x1002000200481,0x1002100210501,0xf3001e9cc01e6f3001e6007984bf0000f307983cfcc00f6cde63cfcc00f4e7f53079800f4e60f307cbb6,0x0,0xf3001e9cc01e6f3001e6007984bf0000f307983cfcc00f6cde63cfcc00fa9ad90798000fa98f307d7fb6,0x0,0xf3001e9cc01e6f3001e6007984bf0000f307983cfcc00f6cde63cfcc0102325f83cc00102307984c23b6,0x0,0x10220e7204481,0xf30079bcc01e6f3003cc79a22c1e60f307980f307981e61e607a98f81e697e03cc7980f30f301e8ad195,0x10220e7204481,0xf30079bcc01e6f3003cc799e601e60f307980f307981e61e607a98f81e9cc003cde600f31e601e8ad195],
[0x1022084208481,0xf30079bcc01e6f3003cc79a22c1e60f307980f307981e61e607a98f81e679803dd8f80f31e601e8ad195,0x1022084208481,0x0,0x102218c210501,0x400001001000004004000008010000010020003340080000800040000000100001006680010000200040000800020000000080668000100020000400080000800000001000c87fe27,0x102218c210501,0x0,0x0,0x0,0x0,0x0,0x0,0x8040200012000480010084010100082002080ce3,0x0,0x8040200022000880020104010100102004080de3,0x8040200002000080000004000100002000080ce3,0x8040200002000080000004000100202008080ce3,0x8040200002000080000004000100002000080ce3,0x8040200002000080000004000100402010080ce3,0x0,0x0,0x8040200002000080000004000100002000080ce3,0x0,0xf3003cfcc00f3f3003cc007984bf0000f307983cfcc00f6cde63cfcc00f4e7f53079800f4e60f307cbb6,0x0,0xf3003cfcc00f3f3003cc007984bf0000f307983cfcc00f6cde63cfcc00fa9ad90798000fa98f30814bb6,0x0,0xf3003cfcc00f3f3003cc007984bf0000f307983cfcc00f6cde63cfcc0102325f83cc0010230798448bb6,0x8010200402040080402004280108002200082ce3,0x0,0x82002102040080100804220108002200080ce3],
[0x102300102300010230798004bf0f30fa98003cfccf303ce22de9ccf33cc1e62d900f33cc0001e61556,0x102004102040080100804220108002200080ce3,0x1100044020008800208100204080102000221e4,0x204008002040080000004200108002200080ce3,0x2100084020008800208100204080102000422e4,0x8420244410a2,0x4100104020008800208100204080102000824e4,0x8420244410a2,0x8100204001008800208100204080102001029e4,0x0,0x10100404001008800208100204080102002031e4,0x8420244410a2,0x8420244410a2,0x420244410a2,0x8420244410a2,0x8020200802040080804004300108002200084ce3,0x0,0x0,0x440000008200000004800000011000100000004000800020002000084000000100400800008000000004008000010020004000000010000200040000800100000004000252e28,0x0,0x1200048040009000208200208080202000241e4,0x1201008040009000208200208080202000241e4,0x2200088040009000208200208080202000442e4,0x8420244410a2,0x4200108040009000208200208080202000844e4,0x8420244410a2,0x8200208001009000208200208080202001049e4,0x0,0x10200408001009000208200208080202002051e4,0x8420244410a2,0x8420244410a2,0x420244410a2],
[0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3368 : TreeBound (n := 4) 106 (programCode 0x4429073a5e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc1e600007981e60008118001ed98003db3b6403cde6003ccf33cc2d90f300f33cc0000001e56,0x16c800111600016c80798004458000fa98003cfccf303cde6003ccf33cc1e60f300f33cc0001e61556,0xf307983cc1e600007981e60008118001ed98003db3b6403cde6003ccf33cc2d90f300f33cc0000001e56,0x0,0x1400044020008800208100204080102000221e4,0x1e607987987981e608118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc0003ea93b6,0x0,0x1e60f307983cc1e60fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x1008040020008800208000204080102000221e4,0x101004042000880020801020408010200122be4,0x25f80007d4c001e60fa98004458000fa98003cfccf303cde63cfccf33cc1e60f300f33cc0003ea93b6,0x102004082000880020802020408010200122de4,0x1100044020008800208100204080102000221e4,0x1040041020008800208040204080102004229e4,0x0,0x1080042020008800208080204080102004231e4,0x1100040020008800208000204080102000221e4,0x1100044020008800208100204080102000221e4,0x44580011160001e601e60008118001ed98003db3b65e9cc00003ccf33cc2d988b00f33cc0003ea9cb6,0x1200048020008800208200204080102000261e4,0x0,0x200408010840010100804220108002200080ce3,0xf307987987980f308118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc0001e61556,0x200808020840010100804220108002200080ce3,0x1e6000f307983cc1e60fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc0003ea93b6,0x201008040840020000004200108002200080ce3,0x101088042000880020801020408010200542be4,0x202008080840020000004200108002200080ce3,0x102010082000880020802020408010200182de4,0x204008100840000000004200108002200080ce3,0x1040241020008800208040204080102005229e4],
[0x0,0x1080442020008800208080204080102006231e4,0x210008400840080402004280108002200082ce3,0x204008000840000000004200108002200080ce3,0x220008800840100804004300108002200084ce3,0x1201008020008800208200204080102008261e4,0x0,0x2400084020008800208100204080102000422e4,0x798079f98079879808118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc000f4eeed6,0x240008542000880020815020408010200542be4,0x7980f379803cc7980fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc000f4f0d36,0x2008080020008800208000204080102000422e4,0x212024741d02,0x272024741d02,0x212024741d02,0x272024741d02,0x222024741d02,0x0,0x222024741d02,0x2100080020008800208000204080102000422e4,0x242024741d02,0x272024741d02,0x242024741d02,0xf307980799e600007980798004458000fa98003cfccf303cde6003ccf33cc1e60f300f33cc0000001556,0x0,0x4400100020008800208000204080102000804e4,0xf30079bcc0798f3008118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc001e610856,0x440010582000880020816020408010200582de4,0xf300f33cc03ccf300fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc001e7f86b6,0x4008100020008800208000204080102000804e4,0x212024741d02,0x272024741d02],
[0x212024741d02,0x272024741d02,0x222024741d02,0x0,0x222024741d02,0x4000100020008800208000204080102000804e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x800420010840010100804220108002200080ce3,0x1e60007983cc7b660008118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc03cc1e7556,0x800820020840010100804220108002200080ce3,0x1e6000f307983ea6000fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc03cc1e93b6,0x801020040040020000004200108002200080ce3,0xe12024741d02,0x8420244410a2,0xe12024741d02,0x8420244410a2,0xc220246418e2,0x0,0xc220246418e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0xf379adccde6003cc011160008118001ed98003db3be05ccc003cfccf33cc2f76f300f33cc0079a268b6,0x3cc007d4c0079bcc008118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc0079a25fb6,0x8400205020008800208140204080102005029e4,0x3cc00f6cc003cfcc00fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc0079a25fb6,0x8008200020008800208000204080102001029e4],
[0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x0,0x4220246418e2,0x8008204020008800208100204080102001029e4,0x4420246418e2,0x4620246418e2,0x4420246418e2,0x0,0x3d39803cde60079f983d008e0460f30ba4e92646f31ea0ccaa703324e6003ccf303ccf3003cde7033d5,0x0,0xf307980001e600007981e60008118001ed98003db3b6403cde6003ccf33cc2d900000f30000000001e56,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7980001e600007980798004458000fa98003cfccf303cde6003ccf30001e600000f30000000001556,0x0,0x79f9803cde60079f983ea60f307983cfcc1f5307981e9ea61e6fa981e679801ed9800f379801e77d0e5,0x0,0x79f9803cde60079f983ea60f30f3079bcc204607981ea08c1e709c81e6f3001ed9800f3f3001e77d0e5,0x0,0x0,0x0,0x798007b660079f98008118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc00f3262bb6,0x10400406020008800208180204080102006031e4],
[0x79800f4e6003d39800fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc00f3262bb6,0x10008400020008800208000204080102002031e4,0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x0,0x4220246418e2,0x10008404020008800208100204080102002031e4,0x4420246418e2,0x4620246418e2,0x4420246418e2,0x0,0x20004800100c0010180c04230108002200080ce3,0xf30000b6400079800008118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc0000001556,0x2000880020140010180c04230108002200080ce3,0x1e6000fa9f983ea6000fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc03cc1e93b6,0x2001080040240020100804220108002200080ce3,0x2201080042000880020801020408010200502be4,0x8420244410a2,0x5010b0082000480020802020588010200582da4,0x8420244410a2,0x29040041020008800208040204080102004229e4,0x0,0x31080042020008800208080204080102004231e4,0x20244410a2,0x8420244410a2,0x20244410a2,0x8420244410a2,0x0,0x800410010840010100804220108002200080ce3],
[0x1e600097e0007b660008118004458000fa98003cfccf303cc001e9ccf33cc1e60f300f33cc03cc1e7556,0x800810020840010100804220108002200080ce3,0x1e60011160003ea6000fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc03cc1e93b6,0x1020040040020000004200108002200080ce3,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x40005000100c0010180c04230108002200080ce3,0x0,0x4000900020140010180c04230108002200080ce3,0x0,0x4001100040240020100804220108002200080ce3,0xc12024741902,0x420244410a2,0xc12024741902,0x420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x20244410a2,0x420244410a2,0x20244410a2,0x420244410a2],
[0x0,0x0,0x0,0x0,0x3cc001023000408c000fa98004458000fa98003cfccf303cc003cfccf33cc1e60f300f33cc07985b53b6,0x40009000020008800208000204080102008061e4,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x3cc7980f307983cc7980798004458000fa98003cfccf303cde6003ccf33cc1e60f300f33cc07983cd556,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3577 : TreeBound (n := 4) 106 (programCode 0x4429073a5f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600014040100010084210108002200080ce3,0x0,0x10320e7204481,0x8000200104020100000004000100002020080ce3,0x10320e7204481,0x8000200104000100000004000100002000080ce3,0x1022084208481,0x8000200104000100000004000100002000080ce3,0x1022084208481,0x400021001000002004000000010000020020002100080000000080020000200000004200010010000040000000080000000080600000100800000400000000402000001001087fda7,0x106218c210501,0x8000200104000100000004000100002000080ce3,0x106218c210501,0x0,0x8004200104040100100804220102002080080ce3,0x0,0x8000200104040100000004200104002100080ce3,0x0,0x8000a00024040100020104210108002200080de3,0x0,0x103a0e7204481,0xf300012fc0004bf0000f30f304bf0000f30f303cfcc01e9cde6003cc01e605b20003cc1e603cc1e61556,0x103a0e7204481,0x1002000200481,0x1002000208481,0x1002000200481,0x1002000208481,0x0,0x1042108210501,0x1002000200481,0x1042108210501],
[0x0,0x0,0x0,0x0,0x0,0x8001200044040100040204220108002200080ee3,0xf3000408c003db30003ccf3004bf0000f3f3003cfcc1e63cde63cfcc1e9cc1e60f3001e9cc007983ffb6,0x8002200084040100080404220108002200080ce3,0xf30007d4c001f5300079bcc004bf0000f6cc003cfcc7983cde63cfcc79bcc1e60f30079bcc01e60f63b6,0x8004200104040100100804220108002200080ce3,0x8000201004040100000004200108002200080ce3,0x0,0x10220e7204481,0x1dcd6503b9b4135940ee6d04d6500773d075940773770d650077394daca00000ee6b2f73594773594ee6b9f3594ee6b2f7359477359b73594ee6b45cd653b9ad52d05e3b9ad8e6b2bb9bb86b2803b9aca0000077359400001dcd6c735940ee729b5940ee6b9f35940ee747fdbffd99,0x10220e7204481,0x0,0x1022084208481,0xf30079bcc01e6f3003cde600007983cc0f301e60f301e63cc0798f301e600003cc0000f33cc01e740995,0x1022084208481,0x0,0x102218c210501,0xf30079bcc01e6f3003cde60f30798b640f301e60f301e63cc07afbb01e63cc03ccf300f8eec01eed8995,0x102218c210501,0x0,0x0,0x0,0x0,0x0,0x0,0x80403004040100010084210108002200080ce3,0x0,0x100805004040100020104210108002200080de3],
[0x0,0x201009104040100040204220108002200080ee3,0x79bcc0798f30079bcc0f3003cfcc00f3f3003cfcc1e63cc003cfcc1e9cc1e60f3001e9cc007983ffb6,0x20024040022,0xf33cc03ccf300f33cc3cc003db3000f6cc003cfcc7983cc003cfcc79bcc1e60f30079bcc01e60f63b6,0x20024040022,0x420024040022,0x0,0x420024040022,0x0,0x8220246410e2,0x20024040022,0x8220246410e2,0x8010200404040100402004280108002200082ce3,0x0,0x82002184040100080404220108002200080ce3,0x0,0x102004184040100080404220108002200080ce3,0x0,0x204008104040100100804220108002200080ce3,0x7a73007a730007a73001e601e9cc00f411603cfcc222fcc08c7fcc2268c1ee9a3002268c0088b47426,0x40024040022,0x7a73003db3000f3f3001e601f53000f42fc03cfcc29c7cc005b5cca380c1e60f3002a00c028d249726,0x40024040022,0x3ccf303ccf3003ccf300f3003cfcc00f3f3003cfcc1e63cc003cfcc1e9cc1e60f3001e9cc007983ffb6,0x0,0x798f300f3f300798f301e6003cc00007b66003cfcc3cc3cc001e9cc3cfcc1e60f3003cfcc00f307acc6,0x8420244410a2,0x8420244410a2,0x40024040022,0x8420244410a2,0x8020200804040100804004300108002200084ce3],
[0x0,0x0,0x0,0x0,0x0,0x0,0x7a730079f98007b660079801e9cc00f48ae03cfcc315fcc0c93fcc3198c1f2663003198c00c5765a26,0x40024040022,0xf4e6003d39800f4e6003cc03db3000f33cc03cfcc079bcc003cfcc07d4c1e60f30007d4c01e61056b6,0x40024040022,0x3cde603cc79803cde603cc003db3000f6cc003cfcc7983cc003cfcc79bcc1e60f30079bcc01e60f63b6,0x1020040a04040100804004300108002200084ce3,0x799e600f33cc0799e601e6003cc00007a73003cfcc5b23cc005b5cc1e9cc1e60f3001e9cc016c8b9726,0x8420244410a2,0x8420244410a2,0x40024040022,0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3690 : TreeBound (n := 4) 106 (programCode 0x4429073a60) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x16c800111600016c83cc3ce0460f30b645d2646f31e9cfcde703324e6003ccf303ccf3003cde7033d5,0x16c87980001e600007981e60008118001f530003db3b6403cde6003cde60012090003ea60003cc0001e56,0xf307980001e600007981e60008118001f530003db3b6403cde6003cde63cc2d900001e60000000001e56,0x0,0x0,0x0,0xf307980001e600007981e60008118001f530003db3b6403cde6003cde65b22d903cc1e60000000001e56,0x0,0x0,0x0,0xf307980001e60f307980f3000408c0010230003cfcde603cde6003cde60001e600001e60000000001556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81002044000900020801020808020200114be4,0xa00020140009000208200208080202000100e4,0x82002084000900020802020808020200114de4,0x800028040009000208000208080202000100e4,0x840021040009000208040208080202008149e4,0x0,0x880022040009000208080208080202008151e4,0x0],
[0x900024040009000208100208080202000100e4,0x0,0xa00028040009000208200208080202000100e4,0x0,0x25f800111600025f83cc3ce0463cc0b641e7e60f31e9cfcde703231e6003cde603ccf3003cde7038e5,0x16c80005b20f316c80f3000408c0010230003cfcde603cde6003cde60005b20003ea60003cc1e61556,0xf307980001e600007981e60008118001f530003db3b6403cde6003cde63cc2d900001e60000000001e56,0x0,0x0,0x0,0xf307980001e600007981e60008118001f530003db3b6403cde6003cde65b22d903cc1e60000000001e56,0x0,0xf307980001e600007981e60008118001f530003db3b6403cde6003cde65b22d90f301e60f30000001e56,0x0,0x7980001e60f307980f3000408c0010230003cfcde603cde6003cde60001e600001e60000000001556,0x0,0x0,0xf307980001e600007981e60008118001f530003db3b6403cde6003cde61e62d907981e60798000001e56,0x0,0x7980001e60f307980f3000408c0010230003cfcde603cde6003cde60f31e603cc1e60f30000001556,0x0,0x0,0x0,0x0,0x1e60f307983cc1e61023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x20460007983cc1e61023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x101004044000900020801020808020200124be4,0x1200040240009000208200208080202000241e4,0x102004084000900020802020808020200124de4,0x1000048040009000208000208080202000241e4,0x1040041040009000208040208080202008249e4,0x25f80007983cc25f80f3000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6],
[0x1080042040009000208080208080202008251e4,0x1200048040009000208200208080202000241e4,0x1100044040009000208100208080202000261e4,0x0,0x1200048040009000208200208080202000241e4,0x0,0x0,0x0,0x0,0x3cc000f307983cc1e61023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x3cc1e60007983cc1e61023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x101108044000900020801020808020200124be4,0x1201000240009000208200208080202000241e4,0x102010084000900020802020808020200124de4,0x1000008040009000208000208080202000241e4,0x1040241040009000208040208080202008249e4,0x3cc7980007983cc25f80f3000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x1080442040009000208080208080202008251e4,0x1201008040009000208200208080202000241e4,0x1100804040009000208100208080202004261e4,0x16cc825e6079800000001e60008118001f530003db3b65e9cc00003cde63cc2d988b01e63cc000408fcb6,0x1201008040009000208200208080202000241e4,0x0,0x0,0x0,0x0,0x7980f379803cc7981023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc003cfed9b6,0x7b660079803cc7981023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc003cfed9b6,0x212024741d02,0x272024741d02,0x212024741d02,0x272024741d02],
[0x222024741d02,0x201009004000900020801020808020200144be4,0x222024741d02,0x2200088040009000208200208080202000442e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x0,0x0,0x0,0xf30001023000408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc07983cf3b6,0xf301e60f3000408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc07983cf3b6,0xc12024741902,0x8420244410a2,0xc12024741902,0x8420244410a2,0x8220246410e2,0x408010200040000000004200108002200080ce3,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x0,0x0,0x0,0xf300f33cc03ccf301023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc001e9de6b6,0xf4e6003cc03ccf301023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc001e9de6b6,0x212024741d02,0x272024741d02],
[0x212024741d02,0x272024741d02,0x222024741d02,0x402011004000900020802020808020200184de4,0x222024741d02,0x4000100040009000208000208080202000804e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x0,0x0,0x0,0x3cc000f30798408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0x3cc1e6000798408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc000408f3b6,0xe12024741d02,0x8420244410a2,0xe12024741d02,0x8420244410a2,0xc220246418e2,0x808020200040000000004200108002200080ce3,0xc220246418e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x0,0x0,0x0,0x3cc00f6cc003cfcc01023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc01e64c23b6,0x3cde603cc003cfcc01023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc01e64c23b6],
[0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x8040210040009000208040208080202009049e4,0x4220246418e2,0x3cde603cc003cfcde7023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc01e64c23b6,0x4420246418e2,0x4620246418e2,0x4420246418e2,0xf307980001e60f307980f3000408c0010230003cfcde603cde6003cde63cc1e60f301e63cc0000001556,0x0,0x0,0x0,0x0,0x79800f4e6003d39801023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc00f3448bb6,0x799e601e6003d39801023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc00f3448bb6,0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x1008041004000900020808020808020200a051e4,0x4220246418e2,0x799e601e6003d399e7023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc00f3448bb6,0x4420246418e2,0x4620246418e2,0x4420246418e2,0x0,0xf307980001e600000001e60008118001f530003db3b6403cde6003cde63cc2d90f301e63cc0000001e56,0x16cbcc1e60000798000097e0008118001f530003db3b65e9cc0079bcde63cc2d988b01e63cc0000001e56],
[0xf307980001e600000001e60008118001f530003db3b6403cde6003cde63cc2d90f301e63cc0000001e56,0x3cc001023798408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc079c08f3b6,0x3cc1e60f3798408de61023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc079c08f3b6,0x4201100044000900020801020808020200944be4,0x8420244410a2,0x402010084000900020802020808020200184de4,0x8420244410a2,0x49040041040009000208040208080202009249e4,0x0,0x5108004204000900020808020808020200a251e4,0x20244410a2,0x8420244410a2,0x20244410a2,0x8420244410a2,0x0,0x0,0x1e600097e0007b6600088b000408c0010230003cfcde603cc0079bcde63cc1e60f301e63cc0f30799556,0x1e63cc1e61e601e688b0f3000408c0010230003cfcde603cde6003cde63cc1e60f301e63cc0f30799556,0x1e60011160003ea6001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc0f30b673b6,0x1e61e61e60003ea6001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc0f30b673b6,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0],
[0xf307980001e600000001e60008118001f530003db3b6403cde6003cde63cc2d90f301e63cc0000001e56,0x0,0xf307980001e600000001e60008118001f530003db3b6403cde6003cde63cc2d90f301e63cc0000001e56,0x0,0x0,0xc12024741902,0x420244410a2,0xc12024741902,0x420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x20244410a2,0x420244410a2,0x20244410a2,0x420244410a2,0x0,0x0,0x0,0x0,0x3cc001023000408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc07983cf3b6,0x3cc1e60f3000408c001023000408c0010230003cfcde603cc003cfcde63cc1e60f301e63cc07983cf3b6,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x8000200040000000004200108002200080ce3,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2],
[0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3018 : TreeBound (n := 4) 106 (programCode 0x4429073a) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part010_3019 part010_3020 part010_3101 part010_3102 part010_3183 part010_3184 part010_3185 part010_3186 part010_3187 part010_3188 part010_3189 part010_3270 part010_3271 part010_3368 part010_3577 part010_3690

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3948 : TreeBound (n := 4) 106 (programCode 0x4429073b11) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10840a4204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3949 : TreeBound (n := 4) 106 (programCode 0x4429073b12) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1dcd65ee6b2f73597b9acbdcd65ee6b2f73597b9acbdcd65ee6b2f7359400001dcd65ee6b2f735940ee6d04d65ee6b2f73594077359b73594ee6b45cd653b9acaee6b2bb9ad8e6b2bb9acaee6b2bb9aca0000077359400001dcd6c735940ee729b5940ee6b9f35940ee747fdbffd99]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3950 : TreeBound (n := 4) 106 (programCode 0x4429073b13) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10840a4204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3951 : TreeBound (n := 4) 106 (programCode 0x4429073b14) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a4214481,0x1081084210481,0x10804a4214481,0x1081084210481,0x10808c4218481,0x1081084210481,0x10808c4218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x600000008800000006000000018000040000400800000008400120001000028000800020001000400010000200020000800080000400001000824000008005000010014850e27,0x0,0x0,0x0,0x0,0x0,0x8200000010800000102000000208000040000400800000100400120001000028000800020001000400010000200020000800080000400020000824000008005000010014850e27,0x0,0x0,0x200010000800040002000100008000040000800800000000400100001000020000800020004000400010000200020000800100000400000002020000008004000010014852e27,0x0,0x200008000800020002000080008000040000800800000000400100001000020000800020004000400010000200020000800100000400000002020000008004000010014852e27,0x0,0x0,0x0,0x0,0x0,0xc000300040a200201004040101402040081ce3],
[0x1040021001008200201004040101002040081ce3,0x14000500040a200201004040101402040081ce3,0x40041000000200201004040100002040081ce3,0x0,0x40041000000200201004040100002040081ce3,0x0,0x0,0x840021001008200201004040101002040081ce3,0x0,0x1040041000000200201004040100002040081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x220000000880000000600000001800020001941010000000900006000200002800200010000100040001000020002000080328200100000100080c00000800500001001487ce27,0x20001000080000000200000100800020000000080000000100010000200006000200002000800008001000020002000080000000100000000402000000800c000010034873227,0x445800111600025f81e600081183cc0f301e60f301e63cc07987981e600f33d39800f33cc01e762c55,0x7981e61e600f37981e600007983cc0f301e60f301e63cc07987981e600003d39800f33cc01e740995,0x0,0x7981e61e600f37981e600007983cc0f301e60f301e63cc07987981e600003d39800f33cc01e740995,0x400020001000f800000006000000028000000080003000f000200020001100000001000060001000f8007c000200000008000080006000000048007800200002000200010000caba8,0x0,0x0,0x0,0x0,0x7980001e607987981e600007983cc0f301e60f301e63cc07987981e600003d39800f33cc01e740995,0x0,0x0,0x0,0x0],
[0x0,0xc0003001008200201004040101002040081ce3,0x7980001e6003d3980000000f300003cc01e60f301e63cc07987981e600003cc0000f33cc01e740995,0x140005000000200201004040100002040081ce3,0x40041000000200201004040100002040081ce3,0x240009001008200201004040101002040081ce3,0x40041000000200201004040100002040081ce3,0x440011001008200201004040101002040081ce3,0x0,0x0,0x0,0x1040041000000200201004040100002040081ce3,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4032 : TreeBound (n := 4) 106 (programCode 0x4429073b15) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084084208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4033 : TreeBound (n := 4) 106 (programCode 0x4429073b16) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a4214481,0x1081084210481,0x10804a4214481,0x1081084210481,0x10808c4218481,0x1081084210481,0x10808c4218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x600000008800000006000000018000040000400800000008400120001000028000800020001000400010000200020000800080000400001000824000008005000010014850e27,0x0,0x0,0x0,0x0,0x0,0x8200000010800000102000000208000040000400800000100400120001000028000800020001000400010000200020000800080000400020000824000008005000010014850e27,0x0,0x0,0x200010000800040002000100008000040000800800000000400100001000020000800020004000400010000200020000800100000400000002020000008004000010014852e27,0x0,0x200008000800020002000080008000040000800800000000400100001000020000800020004000400010000200020000800100000400000002020000008004000010014852e27,0x0,0x0,0x0,0x0,0x0,0xc000300040a200201004040101402040081ce3],
[0x1040021001008200201004040101002040081ce3,0x14000500040a200201004040101402040081ce3,0x40041000000200201004040100002040081ce3,0x0,0x40041000000200201004040100002040081ce3,0x0,0x0,0x840021001008200201004040101002040081ce3,0x0,0x1040041000000200201004040100002040081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x220000000880000000600000001800020001941010000000900006000200002800200010000100040001000020002000080328200100000100080c00000800500001001487ce27,0x20001000080000000200000100800020000000080000000100010000200006000200002000800008001000020002000080000000100000000402000000800c000010034873227,0x445800111600025f81e600081183cc0f301e60f301e63cc07987981e600f33d39800f33cc01e762c55,0x7981e61e600f37981e600007983cc0f301e60f301e63cc07987981e600003d39800f33cc01e740995,0x0,0x7981e61e600f37981e600007983cc0f301e60f301e63cc07987981e600003d39800f33cc01e740995,0x3ba9b0b28000f224d4a003ba9b0b280077712eca0007823ff2bb9acd19487a9dab2803bd664ca00ee729b59477359b7359477359b73597b9aca1dcd73e6b2f73597b9acaee6b2bb9acaee6b2bba0fc90f365f3594773595dcd82cd657736826b280ee6c166b280ee713d6683c09,0x0,0x0,0x0,0x0,0x7980001e607987981e600007983cc0f301e60f301e63cc07987981e600003d39800f33cc01e740995,0x0,0x0,0x0,0x0],
[0x0,0xc0003001008200201004040101002040081ce3,0x7980001e6003d3980000000f300003cc01e60f301e63cc07987981e600003cc0000f33cc01e740995,0x140005000000200201004040100002040081ce3,0x40041000000200201004040100002040081ce3,0x240009001008200201004040101002040081ce3,0x40041000000200201004040100002040081ce3,0x440011001008200201004040101002040081ce3,0x0,0x0,0x0,0x1040041000000200201004040100002040081ce3,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4114 : TreeBound (n := 4) 106 (programCode 0x4429073b17) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1084084208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4115 : TreeBound (n := 4) 106 (programCode 0x4429073b18) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a4204481,0x1081084210481,0x10804a4204481,0x1081084210481,0x1080884208481,0x1081084210481,0x1080884208481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x1820a4220481,0x8040021002004080201004040102002080081ce3,0x1820a4220481,0x482084220481,0x2820c4220481,0x482084220481,0x2820c4220481,0x0,0x482084220481,0x8040001002000080201004040102002080081ce3,0x482084220481,0x2000000008000100020000400080001000000001000040010000800010002500020000800010000800200008000200008010000010010000008100000100100000100308783a7,0x0,0x0,0x0,0x0,0x0,0x16c80005b200016c8003cde600fa983cc01e60f301e63cc07987981e603cc3cc0f30f6cc001e740995],
[0x0,0x445800111600025f800799e601ed983cc01e60f301e63cc07987981e607983cc1e60f6cc001e740995,0x0,0x0,0x0,0x0,0x0,0x3d39800f4e6003d39803cc1e60f37983cc01e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1820a4220481,0x0,0x1820a4220481,0x482084220481,0x2820c4220481,0x482084220481,0x2820c4220481,0x0,0x482084220481,0x0,0x482084220481,0x40101004000100201004040104002100081ce3,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x445800111600025f800000000007983cc01e60f301e63cc07987981e600003cc0000f6cc001e740995,0x0,0x0,0x0,0x1ed98007b66000fa9803cc1e60f37983cc01e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x0,0x0,0x0,0xf379803cde60079f9800000000007983cc01e60f301e63cc07987981e600003cc0000f6cc001e740995,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4196 : TreeBound (n := 4) 106 (programCode 0x4429073b19) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a4210481,0x1081084210481,0x10804a4210481,0x1081084210481,0x10808c4210481,0x1081084210481,0x10808c4210481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x100a184210501,0x1062184210501,0x100a184210501,0x1062184210501,0x1012184210501,0x1062184210501,0x1012184210501,0x1042184210501,0x1022184210501,0x1062184210501,0x1022184210501,0x0,0x1042184210501,0x0,0x1042184210501,0x0,0x0,0x8000600018002010201004040100802020081ce3],
[0x8008200108008040201004040100802020081ce3,0x8000a00028002010201004040100802020081ce3,0x8000200208000000201004040100802020081ce3,0x8001200048004020201004040100802020081ce3,0x8000200208000000201004040100802020081ce3,0x8002200088004020201004040100802020081ce3,0x0,0x8004200108008040201004040100802020081ce3,0x0,0x8008200208000000201004040100802020081ce3,0x0,0x8010200408010080201004040100802020083ce3,0x0,0x8020200808020100201004040100802020085ce3,0x0,0x0,0x100a184210501,0x1062184210501,0x100a184210501,0x1062184210501,0x1012184210501,0x1062184210501,0x1012184210501,0x1042184210501,0x1022184210501,0x1062184210501,0x1022184210501,0x0,0x1042184210501,0x0,0x1042184210501,0x0],
[0x0,0x8000600018004020201004040100802020081ce3,0x0,0x8000a00028004020201004040100802020081ce3,0x0,0x8001200048008040201004040100802020081ce3,0x0,0x8002200088008040201004040100802020081ce3,0x0,0x8004200108000000201004040100802020081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4277 : TreeBound (n := 4) 106 (programCode 0x4429073b1a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804e421c481,0x1081084210481,0x10804e421c481,0x1081084210481,0x10808c4218481,0x1081084210481,0x10808c4218481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x8000600012000080201004040100082000081ce3,0xf30079bcc20c073001e67983cc1e688b07981e60f301e63cc07987981e60f303cc3cc0f754b01e926995,0xf3000222c00088b0000fa98003ea607a7a981e60f301e63cc07987981e60079bcc01e6f308119e760df5,0xf300f33cc222cf3007987983cc1e688b07981e60f301e63cc07987981e63cc03ccf300f782401e926995,0x1dcd6500077acc994001deb32650001e449a94001deb32650001ddc4bb63b897a09aca07735cf9aca7735cf9acbdcd653b9aca773597b9acaee6b36e6b2bb9ad1735943b9ad8e6b2bb9acaee6b2bb9aca0ee6b639aca3b9ad8ef14534eb9f35943b9ad8e6b639aca0eeadca4d9ce29,0xf300f33cc222cf3007987983cc1e688b07981e60f301e63cc07987981e63cc03ccf300f782401e926995,0xf3000f6cc003db300079f981e61e616c87981e60f301e63cc07987981e603cc3cc0f30f3408c1e740995,0x0,0xf3001e9cc007a73001e67983cc1e688b07981e60f301e63cc07987981e60f303cc3cc0f754b01e926995,0x8000200002000080201004040100002000081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x2cb4178000218711a0001ebbd028000218711a00002cb41783b9aca0007aef40a0007aef40a00007aef40a00077712eca000775361dc35940007aef40a01dcd653b9aca00b2d05e01dcddc359401dcd82cd651dcd653b9ae7cda09aca01dcddc359401dcd65003b9acc49787a,0x0,0x0,0x0,0x0,0x1ddc4bb2800eea6c2ca0003c8935280077712eca0007823ff280773597b9aca77448d535655940ee6b29dce549535673652ca4e7939acaee6b45cd650ee6b2f73597b9ad8e6b2bb9acaee6b2bba25949ceb3b9b4135941dd5121733b079196673aceee5f9733b0ee747fd5ef1d9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000600014000100201004040100082000081ce3,0x8000200104000100201004040100002000081ce3,0xf3000222c00088b0001116000811807b75301e60f301e63cc07987981e600f33cc03ccf3088b1e762c55,0x8000200204000100201004040100002000081ce3,0xb,0x8000200204000100201004040100002000081ce3,0xf3000f6cc003db30007b6601e67984458f301e60f301e63cc07987981e607983cc1e60f344581e740995,0x0,0xf3001e9cc007a73001e7e6079879897e0f301e60f301e63cc07987981e60f303cc3cc0f7ce301eb0c995,0x8000200004000100201004040100002000081ce3,0xf30079bcc01e6f3003cde60f30798b640f301e60f301e63cc07987981e63cc03ccf300f8eec01eed8995,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf37980001e600f37980f3000408c0010230003db31e60001e600f31e600f4e600f31e600f3000001556,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4358 : TreeBound (n := 4) 106 (programCode 0x4429073b1b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a4210481,0x1081084210481,0x10804a4210481,0x1081084210481,0x10808c4210481,0x1081084210481,0x10808c4210481,0x1080084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084210481,0x0,0x100a184210501,0x1062184210501,0x100a184210501,0x1062184210501,0x1012184210501,0x1062184210501,0x1012184210501,0x1042184210501,0x1022184210501,0x1062184210501,0x1022184210501,0x0,0x1042184210501,0x0,0x1042184210501,0x0,0x0,0xc0003000402200201004040101002040081ce3],
[0x1040021001008200201004040101002040081ce3,0x140005000402200201004040101002040081ce3,0x40041000000200201004040101002040081ce3,0x240009000804200201004040101002040081ce3,0x40041000000200201004040101002040081ce3,0x440011000804200201004040101002040081ce3,0x0,0x840021001008200201004040101002040081ce3,0x0,0x1040041000000200201004040101002040081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x100a184210501,0x1062184210501,0x100a184210501,0x1062184210501,0x1012184210501,0x1062184210501,0x1012184210501,0x1042184210501,0x1022184210501,0x1062184210501,0x1022184210501,0x0,0x1042184210501,0x0,0x1042184210501,0x0],
[0x0,0xc0003001008200201004040101002040081ce3,0x0,0x140005001008200201004040101002040081ce3,0x40041000000200201004040101002040081ce3,0x240009001008200201004040101002040081ce3,0x40041000000200201004040101002040081ce3,0x440011001008200201004040101002040081ce3,0x0,0x0,0x0,0x1040041000000200201004040101002040081ce3,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4439 : TreeBound (n := 4) 106 (programCode 0x4429073b1c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804a4204481,0x1081084210481,0x10804a4204481,0x1081084210481,0x10808c4218481,0x1081084210481,0x10808c4218481,0x1080084200481,0x1081084210481,0x1081084210481,0x1081084210481,0x1080084200481,0x0,0x0,0x0,0xc0005002000880320804040100101084081fa3,0x0,0x1020000001080000010200000010800010000842010000100100000420100001800040008000800008000400080002000080000400020421000400004000205010001001cc4b0a7,0x0,0x1ed98007b66000fa9807981e61e61741f981e60f301e63cc07987981e603cc3cc0f30f3ba0c1e740995,0x0,0x0,0x8040001002000080201004040100002080081ce3,0x0,0x7981e61e6079879807980f379800007980f303cc1e61e61e607981e600000fa98007b66001e77cb45,0x0,0x0,0x0,0x0,0x0,0x6000000018000000120000000180000008200410020021000082104100000500010000200020000800200008000200008002000008108200010420000101082000100108613a7],
[0x0,0x600020000000080001000200000000800020000001080000004100000004100000016200380000200200000002000002002000020038000080080000080080000200000000007fda8,0x0,0x0,0x0,0x0,0x0,0x40002000000008000400020000400080001000000101000000110000001010000001000020000080000001000200000800200002000000002008000020008000020000000000793a8,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c80f300f33cc001f5300f307981e61e61e607981e600001e603cc7a73001e780d15,0x0,0x140005004000900201004040100102104081de3,0x40041004000100201004040100002100081ce3,0x0,0x40041004000100201004040100002100081ce3,0x1ed98007b66000fa981e601e6798454bf301e60f301e63cc07987981e607983cc1e60f52a581e740995,0x0,0x0,0x0,0x0,0x40101004000100201004040100002100081ce3,0x0,0x0,0x0,0x0],
[0x0,0x2200010808800000022000008008000200000010200000012000000102000000100022000008004400000220000080040000200010000200c00402001000002000004020279ba8,0x0,0x0,0x2200000002800000022000000028000200000010200000012000000102000000100022000008004400000220000080040000200010000200c00402001000002000004020279ba8,0xee6b2800003b9acbdcd83bbd0280007aef40bdcd65ee6b2bb9aca0003c893528000eee25d940007ea8ed400077acc994000773594ee6b2800003b9aca0b2d0d8ef40a007aef40a03b9b4135941dcd6500000773597b9aca3ba06082f03b9b41359403b9aca0000000391793a,0x1e449b826b2f73597b9aca01dce536b2800003b9aca03b9bb86b2f73597c893528000ee6b2f7359403b9aca00000000773594077359b73597b9aca7735a2e6b2f73597b9acaee6b2bb9acaee6b2bba23d5940077359400000773594000077536165000ee6b2800000ee6d0c84c9d29,0x2000100008000200020000000080002000000102000000120000001020000001000020000080000002000200000800400002000000002008000020010000020000000000793a8,0x0,0x0,0x0,0x79f980001e60079f980f3000408c0010230003d399e60001e600799e601e7e600799e601e6000001556,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4520 : TreeBound (n := 4) 106 (programCode 0x4429073b1d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1840a4220481,0x8040021008004200201004040102002080081ce3,0x1840a4220481,0x484084220481,0x2840c4220481,0x484084220481,0x2840c4220481,0x0,0x1804a4220481,0x8040021008004020201004040102002080081ce3,0x1804a4220481,0x481084220481,0x2808c4220481,0x481084220481,0x2808c4220481,0x80084220481,0x481084220481,0x481084220481,0x481084220481,0x80084220481,0x0,0x0,0x0,0x0,0x484084220481,0x8040001008000200201004040102002080081ce3,0x484084220481,0x0,0x4002000010008000040020000000580000000420000001010000010000a00010400008000200020000800200008000200008004000004010000010100000100100000100189513a7,0x0,0x567f60acfec00000002b3fb00567f60acfec0159fd82b3fb00159fd8acfec000000daf26b0000000acfec00000000ad6adf380002b6aefb0000000ad553f600000acfec1b07ce00ad145fd80acfec0acfec00acfec02b3fb2b3fb00acfec00acfec02b3fb0acfec02b3fb00acfec02b40067f60000159fed9fd800015a53ff60000567f759fd800015a131fd8000159fed9fd800015a008b298e08b4ab],
[0x481084220481,0x6808c4220481,0x481084220481,0x6808c4220481,0x80084220481,0x481084220481,0x481084220481,0x481084220481,0x80084220481,0x2000000008000100020000400080001000000001000040010000800010002500020000800010000800200008000200008010000010010000008100000100100000100308783a7,0x0,0x2000000008000000020000800080002000000001000040020001000020004500020000800010000800200008000200008010000010010000008100000100100000100308783a7,0x0,0x0,0x80c184220501,0x824184220501,0x80c184220501,0x864184220501,0x814184220501,0x864184220501,0x814184220501,0x0,0x824184220501,0x2040080408010200201004040102002080083ce3,0x824184220501,0x0,0x844184220501,0x804184220501,0x844184220501,0x844184220501,0x0,0x60c0c4220481],
[0x424084220481,0x60c0c4220481,0x424084220481,0x414084220481,0x424084220481,0x414084220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0x844184220501,0x4084220481,0x844184220501,0x4084220481,0x0,0x80c184220501,0x824184220501,0x80c184220501,0x864184220501,0x814184220501,0x864184220501,0x814184220501,0x0,0x824184220501,0x0,0x824184220501,0x0,0x844184220501,0x804184220501,0x844184220501,0x844184220501],
[0x0,0x80c184220501,0x0,0x80c184220501,0x0,0x8001040048008200201004040102002080081ce3,0x0,0x8002040088008200201004040102002080081ce3,0x0,0x0,0x0,0x0,0x0,0x44084220481,0x4084220481,0x44084220481,0x4084220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4633 : TreeBound (n := 4) 106 (programCode 0x4429073b1e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b200016c83cc01e6f307983cc01e60f301e63cc07987981e603cc3cc0f30f6cc001e740995,0x0,0x0,0x1dcd65ee6b280000000001dcd65ee729b59400001dcd65ee6b2f735940ee6d04d65ee6b2f73594077359b73594ee6b45cd653b9acaee6b2bb9ad8e6b2bb9acaee6b2bb9aca0000077359400001dcd65000000ee729b5940ee6d04d6500ee747fdbffd99,0x0,0x0,0x0,0x0,0x1dcd65000007735b1cd6503b9ca6d6503b9ae7cd6503c11ff9400001dcd65ee6b2f735940ee6d04d65ee6b2f73594077359b73594ee6b45cd653b9acaee6b2bb9ad8e6b2bb9acaee6b2bb9aca0000077359400001dcd6c735940ee729b5940ee6b9f35940ee747fdbffd99,0x0,0x0,0x0,0x424001000010004000000002000400010040002100100000100400000001000080800200010000800040000400080002000080424000101010000400080000200000001001887fca7,0x0,0x624010000010040000400080000400080040003120100000100400000801000080800200010000800040000400080002000080624000100800000400080000201000001001887fca7,0x408c00102300010233cc00088b000222c0005388b6622c1e607980020462d98118001ed98f30799e56,0x6fc0100000100400008000200004001000400037e01000001004000008010000808002000100008000400004000800020000806fc000100200000400080000201000001001887fca7,0x408c00102300011163cc00088b000222c0005388b6622c1e607980020462d98118001ed98f30799e56,0x445800111600025f83cc01e6f307983cc01e60f301e63cc07987981e607983cc1e60f6cc001e740995,0x0,0x7d4c001f53000b640000f30079bcc01e60f301e63cc07987981e600003cc0000f303cc1e740995,0x0,0x1e9cc007a730012fc0000f30079bcc01e60f301e63cc07987981e600003cc0000f307981e740995,0x40208000200201004040100002000081ce3,0x0,0x40208000200201004040100002000081ce3,0x0,0x0,0x0,0x420021000020000000000200000200000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x8040208000200201004040100002000081ce3],
[0x0,0xf303cc3cc0f30f33cc0000f30079bcc01e60f301e63cc07987981e600003cc0000f379801e740995,0x40008000200201004040100002000081ce3,0x20040808000200201004040100002100081ce3,0x408c00102300020463cc00088b000222c0005388b6622c1e607980020462d98118001ed98f30799e56,0x0,0x811800204600081180003cc1e616c80003ea60f301e63cc07987981e60f303cc3cc0f6cc001e740995,0x80400010000808020220000800020000800000e4,0x80400010000004000200000800020000800000a4,0x80400010001008040220000800020000800000e4,0x81180020460008118001e60f308118001e7e60f301e63cc07987981e60f303cc3cc0f6cc001e748315,0x80400010002008080220000800020000800000e4,0x80400010000004000200000800020000800000a4,0x80400010002004100200000800020000800000a4,0x80400010000004000200000800020000800000a4,0x3d3983cc97e00025f800f3003db3000f3f300445801e60f300445801e6798f3079801e679807983ffb6,0x0,0x79f983cc97e00025f801e6003d39800f4e600445803cc1e600445803cc798f3079803cc7980f307cbb6,0x0,0x0,0x0,0x0,0x0,0x7d4c001f53000b640000f30079bcc01e60f301e63cc07987981e600003cc0000f303cc1e740995,0x0,0x1e9cc007a730012fc0000f30079bcc01e60f301e63cc07987981e600003cc0000f307981e740995,0x40208000200201004040100002000081ce3,0x0,0x40208000200201004040100002000081ce3,0x0,0x0,0x0],
[0x420021000020000000000200000200000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x8040208000200201004040100002000081ce3,0x0,0xf303cc3cc0f30f33cc0000f30079bcc01e60f301e63cc07987981e600003cc0000f379801e740995,0x40008000200201004040100002000081ce3,0x20040808000200201004040100002100081ce3,0x420020000020080000000200010100000040002100100000100400000001000080800200010000800040000400080002000080420000101000000404040000200000001001887fca7,0x0,0x1ed98007b66000fa980003cc1e616c80003ea60f301e63cc07987981e60f303cc3cc0f6cc001e740995,0x80428020022,0x80028020022,0x80428020022,0x1ed98007b66000fa98001e60f308118001e7e60f301e63cc07987981e60f303cc3cc0f6cc001e748315,0x80828020022,0x80028020022,0x80828020022,0x80028020022,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16c80005b200016c80003ea60016c80003ea60f301e63cc07987981e603cc3cc0f30f6cc001e740995,0x0,0x2400110004004100200000800820020800000a4,0x0,0x81180020460008118001e60f308118001e7e60f301e63cc07987981e60f303cc3cc0f6cc001e748315,0x0,0x2400110004004000200000800820020800000a4],
[0x2400110002004100200000800820020800000a4,0x2400110000004100200000800820020800000a4,0xfa98003ea6000fa9800f3003db3000f3f3004458025f8f3004458025ff98f30798025ff9807984f2b6,0x0,0x1ed98007b66000fa9803cc007a73001e7e6003db3001f8fc22a94c26ebf30222fcc26eb798222d16f36,0x0,0x0,0x0,0x0,0x0,0x3d39800f4e6003d3980003cc1e616c80003ea60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x80428020022,0x80028020022,0x80428020022,0x3d39800f4e6003d398001e60f308118001e7e60f301e63cc07987981e63cc03ccf300f6cc001e748315,0x80828020022,0x80028020022,0x80828020022,0x80028020022,0x3d39800097e003d39800f3003db3000f3f300445801e60f300445801e6798f3079801e679807983ffb6,0x3d39800f4e6003d39803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x79f9800097e0079f9801e6003d39800f4e600445803cc1e600445803cc798f3079803cc7980f307cbb6,0x0,0x3d39800f4e6003d39803cc1e60f37983cc01e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x0,0x0,0x0,0x420001002080000008200010f358000000061e0a000102008001200020001858081000020001000080020000800020000800100000810100000843cd40101040000100108603a7,0x3d39803cde6003d3980003cc3cc3cc0f303cc445801e6798447df801e6798447df801e6798001e61556,0x3d39803cde6003d39800f3003cfcc00f3f300445801e60f300445801e6798f3079801e679807983ffb6,0x8400210001008040220040801020040800209e4,0x2b3fbacfec000acfeeb3fb000159fe2cfec00015a0033fb000056800cfec0000568213fb015cb185cfec05bf226173fb02c99ad8000000acfec02b3fb016f9d58000000567f602b3fb0066b7420d998738001e9aa611cd5308e67e44c2fd95d800567f6567f600159fd8567f6000acff6cfec0d998731335b036661cbf657600159fd8567f62b9630bb577d8002b3fb159fd8000015a28c080eea55ac],
[0x840021000200808022004080102004080040be4,0x77447ab2801dd11eacbdd4d947ab28077394dacbdf8effff928001dcd65ee6b63a9b3d729a7ee7a0eb281ddc4e7dc179e0994ccf9ee6b2bb9ae7cd650ee6b2f73597b9ad8e6b2bb9acaee6b2bba24ff99f20ee729b5941dd4d85940007920d9cceceee38799f20ee747fc7a1019,0x8400210002004100200000801820040800804a4,0x3d39803cde6003d39800f3003cc1e607a73003ea601e60f300445801e6798f3079801e679807983ff26,0x3d39803cde6003d39800f3003db3000f3f300445801e60f300445801e6798f3079801e679807983ffb6,0x0,0x79f9801e7e6003d39803cc007a73001e7e6003db3001f8fc2e0d4c29c4f302d93cc29c47982d9172136,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1000040208000200201004040100002000081ce3,0x0,0x1000040208000200201004040100002000081ce3,0x0,0x0,0x0,0x20021000080000000080200000200000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x1008040208000200201004040100002000081ce3,0x0,0x0,0x1000040008000200201004040100002000081ce3,0x0,0x20020000080080000080200000200000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x0,0x0,0x0,0xf379803cde60079f9803cc007aec801ebb2003e2c801fae22e0d4c29c4f302d93cc29c47982d9172136],
[0x10400410001008040220080802020080800211e4,0x0,0x10400410002008080220080802020080800413e4,0x1e85cccf5b280ee6ee1acbdcd65ee6b280ee6ee1aca03d788ebb2800eea834862d25cd83f76b00e6b9f35941ddc4bb28001dcddc359b73597b9acaee6b28ee6b9f3597b9acaee6b2bb9acaee6b2bba26d6d9bf8735d1eed5f2ee25d94007735d9622f32ee25d94000ee715b346f079,0x10400410004008100200000802020080800804e4,0x77447ab2801dd11eacbdd4d947ab2801dd11eaca02541acab2801dcd68b9acbdce54952df3dcd77a05f3dce54599329dcd6e502fadcd653b9ae7cd653b9acaee6b2bb9ad8e6b2bb9acaee6b2bb9adca05f21dcdaf817c9dd4eaf99f20f055f69758eee25d94000ee747fcdb1bd9,0x79f9801e7e60079f9800f3003db3000f3f300445805b20f300445805b2798f3079805b279825f9ac7b6,0x79f9801e7e60079f981e60003d39801116000445803cc1e7e6445803cc79ad9079803cc7980f307cbb6,0xf379803cde60079f9803cc007a73001e7e6003db3001f8fc1edd4c25f8f301e63cc25f87981e60f8936,0x0,0x0,0x79f9803cde60079f983cc0003cc000222c00044587d4fcc1e6079803cde61e6079803cc798000001946,0x0,0x0,0x80c0e420c481,0x0,0x80c0e420c481,0x0,0x0,0x0,0x1e600f379803cde6007d4c01e6f307983cc01e60f301e63cc07987981e603cc3cc0f30f30f301e740995,0x0,0x0,0x200021000800000001000200001000000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x0,0x0,0x844184220501,0x804084200481,0x844184220501,0x844184220501,0x0,0x0],
[0xf301e9cc0000f307983cc01e60f301e63cc07987981e600003cc0000f33cc01e740995,0x0,0x208000200201004040100002000081ce3,0x0,0x208000200201004040100002000081ce3,0x1dcd65000007735b1cd6503b9ca6d6503b9ae7cd6503c11ff9400001dcd65ee6b2f735940ee6d04d65ee6b2f73594077359b73594ee6b45cd653b9acaee6b2bb9ad8e6b2bb9acaee6b2bb9aca0000077359400001dcd6c735940ee729b5940ee6b9f35940ee747fdbffd99,0x0,0x1e60000798f301e9cc0000f307983cc01e60f301e63cc07987981e600003cc0000f33cc01e740995,0x420021001000000000000200000000000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x8000208000200201004040100002000081ce3,0x0,0x844184220501,0x4084200481,0x844184220501,0x4084200481,0x0,0x80c0e420c481,0x7980001e600003cc01e9cc0000f307983cc01e60f301e63cc07987981e600003cc0000f33cc01e740995,0x80c0e420c481,0x4000100208000200201004040100002000081ce3,0x0,0x4000100208000200201004040100002000081ce3,0x79800f4e6003cfcc007d4c01e6f307983cc01e60f301e63cc07987981e607983cc1e60f30f301e740995,0x0,0x0,0x0,0x0,0x0,0x844184220501,0x804084200481,0x844184220501,0x844184220501],
[0x0,0x0,0x0,0x800028008200201004040100002010081ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x400021001000000000000200000000000040002100100000100400000001000001000200010000800040000800080002000080420000101000000400000000400000001001887fda7,0x0,0x0,0x44084220481,0x4084200481,0x44084220481,0x4084200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_4874 : TreeBound (n := 4) 106 (programCode 0x4429073b1f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1840a4220481,0x0,0x50c0a4220481,0x424084220481,0x50c0a4220481,0x424084220481,0x6140c4220481,0x424084220481,0x6140c4220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0xc44184220501,0x424084220481,0xc44184220501,0x0,0x1840a4220481,0x484084220481,0x2840c4220481,0x484084220481,0x2840c4220481,0x0,0x1804a4220481,0x0,0x1804a4220481,0x481084220481,0x2808c4220481,0x481084220481,0x2808c4220481],
[0x80084220481,0x481084220481,0x481084220481,0x481084220481,0x80084220481,0x0,0x0,0x0,0x0,0x484084220481,0x0,0x6804c4220481,0x0,0x6804c4220481,0x481084220481,0x480884220481,0x481084220481,0x480884220481,0x480084220481,0x481084220481,0x481084220481,0x481084220481,0x480084220481,0x0,0x0,0x0,0x0,0x484084220481,0x0,0x0,0x0,0x0],
[0x481084220481,0x6808c4220481,0x481084220481,0x6808c4220481,0x80084220481,0x481084220481,0x481084220481,0x481084220481,0x80084220481,0x2000000008000100020000400080001000000001000040010000800010002500020000800010000800200008000200008020000010010000008200000100200000100308783a7,0x0,0x40101004000100201004040104002100081ce3,0x0,0x0,0x80c184220501,0x824184220501,0x80c184220501,0x864184220501,0x814184220501,0x864184220501,0x814184220501,0x0,0x824184220501,0x2040080408010200201004040104002100083ce3,0x824184220501,0x0,0x844184220501,0x804184220501,0x844184220501,0x844184220501,0x0,0x60c0c4220481],
[0x424084220481,0x60c0c4220481,0x424084220481,0x414084220481,0x424084220481,0x414084220481,0x0,0x424084220481,0x7980799e601e61e601e9cc00088b000222c0005388b643cc1e601e60f35b22d901e60f33cc03cc2268b6,0x424084220481,0x0,0x844184220501,0x4084220481,0x844184220501,0x4084220481,0x0,0x80c184220501,0x824184220501,0x80c184220501,0x864184220501,0x814184220501,0x864184220501,0x814184220501,0x0,0x824184220501,0x0,0x824184220501,0x0,0x844184220501,0x804184220501,0x844184220501,0x844184220501],
[0x0,0x80c184220501,0x0,0x80c184220501,0x0,0x0,0x0,0x0,0x0,0x0,0x400021001000000000000200000000000040002100100000100400000001000001000200010000800040000800080002000080200000100800000400800000402000001001887fda7,0x0,0x0,0x44084220481,0x4084220481,0x44084220481,0x4084220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5019 : TreeBound (n := 4) 106 (programCode 0x4429073b20) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c084200481,0x0,0x10c084200481,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1440a4204481,0x0,0x1440a4204481,0x104084200481,0x0,0x3cc0079800089a3000b6400f3f300003cc1ed987981e60f31e607981e600001f530003cc0001e77cfc5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x408c00102300010233cc00088b000222c0005388b6622c1e607980020462d98118001f530f30799e56,0x428010000010040000000020010400100040002100100000100400000001000080800200010000800040000400080002000080428000101040000404000000200000001001887fca7,0x408c00102300011163cc00088b000222c0005388b6622c1e607980020462d98118001f530f30799e56,0x445800111600025f83cc0000f307983cc01e60f301e63cc07987981e600003cc0000f6cc001e740995,0x0,0x7980079800088ecc00b6400f3f300003cc1ed987981e60f31e607981e600001f530003cc0001e77cfc5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x408c0010230001f533cc00088b000222c0005388b6622c1e607980020462d98118001f530f30799e56,0x420010000020040000000020010100100040002100100000100400000001000080800200010000800040000400080002000080420000101010000404000000200000001001887fca7,0x408c00102300020463cc00088b000222c0005388b6622c1e607980020462d98118001f530f30799e56,0x0,0x811800204600081180003cc1e616c80003ea60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0,0x81180020460008118000f3079844580007b660f301e63cc07987981e61e603cc7980f6cc001e762c55,0x0,0x81180020460008118001e60f308118001e7e60f301e63cc07987981e61e603cc7980f6cc001e748315,0x0,0x81180020460008118007983cc1ed98003cde60f301e63cc07987981e61e603cc7980f6cc001e75ef95,0x81180020460008118000000000079800001e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x8118002046000811800f307983d39800f31e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0],
[0x8118002046000811803cc1e60f379801e61e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0,0x0,0x8118002046000811800f307983d3983cc01e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0,0x0,0x0,0x7980079800088ecc00b6400f3f300003cc1ed987981e60f31e607981e600001f530003cc0001e77cfc5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x420021200020080800000202010100000040002100100000100400000001000080800200010000800040000400080002000080400000101000000404000000200000001001887fca7,0x420010000020040000000020010100100040002100100000100400000001000080800200010000800040000400080002000080420000101010000404000000200000001001887fca7,0x420020000020080000000200010100000040002100100000100400000001000080800200010000800040000400080002000080400000101000000404000000200000001001887fca7,0x0,0x1ed98007b66000fa980003cc1e616c80003ea60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x80428020022,0x80028020022,0x80428020022,0x1ed98007b66000fa98001e60f308118001e7e60f301e63cc07987981e63cc03ccf300f6cc001e748315,0x80828020022,0x80028020022,0x80828020022],
[0x80028020022,0x3cc79800f4e6003d39800f3003db3000f3f300408c01e60f300408c01e6f307983cc01e6f3007983ffb6,0x1ed98007b66000fa9803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0xf3798222de600f379803cc007a73001e7e6003db3002082c1ee1184459e601e67984458f301e60f8936,0x0,0x1ed98007b66000fa9800f307983d3983cc01e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x0,0x1ed98007b66000fa9803cc1e60f37983cc01e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x0,0x0,0x0,0x4400110004008000200001000840021000000e4,0x0,0x81180020460008118001e60f308118001e7e60f301e63cc07987981e61e603cc7980f6cc001e748315,0x0,0x4400110004008000200001000840021000000e4,0x4400110004008100200001000840021000000e4,0x4400110000008100200001000840021000000e4,0xfa98003ea6000fa9800f3003db3000f3f300408c025f8f300408c02607307983cc026073007984f2b6,0xf379803cde60079f9803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0x1ed98007b66000fa9803cc007a73001e7e6003db3002082c22ad18454ce60223398454bf30222d16f36,0x0,0x0,0x0,0x0,0x0,0x0,0x80428020022,0x80028020022,0x80428020022,0x0,0x80828020022],
[0x80028020022,0x80828020022,0x80028020022,0x0,0x3d39800f4e6003d39803cc1e60f379801e61e60f301e63cc07987981e61e603cc7980f6cc001e740995,0x0,0x3d39800f4e6003d39807980799e679807981e60f301e63cc07987981e679803cde600f6cc001e740995,0x0,0x3d39800f4e6003d3981e60079f987980f301e60f301e63cc07987981e6f3003cfcc00f6cc001e740995,0x0,0x0,0x420001002080000008200010f35800000006140a0001020080012000200018582010000200010000800200008000200008002000008102000008428140101080000100108603a7,0x3d39803cde6003d3980003cc3cc3cc0f303cc408c0798f3098022c0798f3098022c0798f30001e61556,0x79f9801e7e6003d39801e6003d39801e7e6003d398021576893118222cf300f3798222cf300f307ec26,0x8400210001008040240041001040041000209e4,0x0,0x840021000200808024004100104004100040be4,0x0,0x8400210002004100200001801820041000804a4,0x3d39803cde6003d39804bf003cc1e607e3f00408c097e4bf003ea6097ef303cc1e6097ef3025f932f26,0x3d39803cde6003d39800f3003db3000f3f300408c097e0f300408c097ef307983cc097ef30079932fb6,0x0,0x79f9801e7e6003d39803cc007a73001e7e6003db3002082c2e11184825e602d97984824f302d9172136,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401010000008000200001000040001000000e4,0x0],
[0x0,0x0,0x401010000008000200001000040001000000e4,0x401010004008100200001000040001000000e4,0x401010000008000200001000040001000000e4,0x3cc79800f4e603cc79800f3003db3000f3f300408c01e60f300408c01e6f307983cc01e6f3007983ffb6,0xf379803cde60079f9803cc1e60f379801e61e60f301e63cc07987981e63cc03ccf300f6cc001e740995,0xf3798222de6079879803cc007a73001e7e6003db3002082c1ee1184459e601e67984458f301e60f8936,0x0,0x0,0xf379803cde60079f981e601e67987980f301e60f301e63cc07987981e7e6003d39800f6cc001e740995,0xf379803cde60079f9800000000007983cc01e60f301e63cc07987981e600003cc0000f6cc001e740995,0x0,0x0,0xacff6cfec000acfeeb3fb000159fe2cfec0002b3fdb3fb0000acff6cfec0000ad0173fb0000000567f60567f60acfec0567f6002b3fb0acfec0159fd8159fd80567f60567f600567f6059335b000ad146aa7ec059335b2b3fb0159ff1c3705800975ef37ceac00ad146aa7ec059335b2b3fb000ad148b17b0002b3fb567f60025d7baacfec0567fc6e281b0164cd6c2b3fb002b45180ba2ae36d93ac,0xf379803cde60079f9803cc007a73001e9cc003db3002082c1ee1184459e601e67984458f301e60f8936,0x10400410001008040240081002040081000211e4,0x0,0x10400410002008080240081002040081000413e4,0xf379801e7e60079f9870020079f9800f4e60058c16031ae600408c03cde638013cc03ccf300f307d426,0x10400410004008100200001002040081000804e4,0x77447ab281dcda09aca01dce536b280ee6ee1aca00ee7a0eb280000000003b9aca0000fd500c192cfae6b29dcd6c75361650007735940000007735940003b93924150339cd314000430e2343b9acdb9aca7736826b281dcd73e6b9f2721409cf43b9ad17359400000000201153a,0x79f9801e7e60079f9800f3003db3000f3f300408c05b20f300408c05b2f307983cc05b2f3025f9ac7b6,0x79f9801e7e60079f980f30003d39801023000408c03cc1e7e6408c03ccf325f83cc03ccf300f307cbb6,0xf379803cde60079f9803cc007a73001e7e6003db3002082c1ee1184459e601e67984458f301e60f8936,0x7736826b281dcda09aca00ee7a0eb280ee6ee1aca00ee7a0eb28000773597b9acbdcd65f5de81400007735a2e6b2fea8ed40000861c4683b9b059acdb9acb65a0cb224dc13597b9acb65a0bc3b9b059aca0ee6c166b36e6b287735cf9b0611ff943b9ad173594003ba23f6ccb89a,0x0,0x2000100008000000020001f000800010003e00010000200200020000200085800100002000100008002000080002000080000000081000000087c0000101000000100108603a7,0x0,0x0,0x80c184220501,0x1e601e6799e601e601e9cc03ccf307983cc01e60f301e63cc07987981e679803cde600f6cc001e926995],
[0x80c184220501,0x1e60f3079a22c1e6079bcc03ccf3088b3cc01e60f301e63cc07987981e679803cde600f745801e926995,0x1e6003d39800f4e600408c03ccf307983cc01e60f301e63cc07987981e679803cde600f31e601e92e315,0x1e60f3079a22c1e6079bcc03ccf3088b3cc01e60f301e63cc07987981e679803cde600f745801e926995,0x1e600f379803cde6007d4c03ccf307983cc01e60f301e63cc07987981e679803cde600f33cc01e926995,0x0,0x1e601e67980799e601e9cc03ccf307983cc01e60f301e63cc07987981e679803cde600f6cc001e926995,0x4002000010008800100020000100008004000020010000040040002200100000400020000200020000800200008000200008004000010100000010040000101100000100708713a7,0x0,0x0,0x844184220501,0x804184220501,0x844184220501,0x844184220501,0x0,0x0,0xee6b280012a05f20003c11ff940007823ff28000ef59932800165a0bc00009502f900002540be400010c388d0000430e23400007aef40db9acaee6b72817e98712ca05f973597b9aca3b9acdb9aca7735ed682f1dcd7b5a0bcee6b72817cbb9acdb9aca7735b1cd65ee6b4c37baa,0x0,0x200000004800000021000000081000000140000000500000002400000009000000011000300014000c000400020000400040000800300004000c000100010000200040002000deea8,0x0,0x1e449b8624d4a000000001dcd6501dcd650003b9aca0000001dcddc3597c893704d65000007735940773770d65ee6b2f73594077359b73597b9acaee6b28ee6b9f3597b9acaee6b2bb9acaee6b2bba23d5940077359400000eee25d940077359400000eee25d94000ee70c63176079,0x0,0x0,0x0,0x420021001000000000000200000000000040002100100000100400000001000001000200010000800040000800080002000080400000101000000400000000400000001001887fda7,0x0,0x0,0x844184220501,0x4084200481,0x844184220501,0x4084200481,0x0],
[0x80c184220501,0x7980001e61e603cc01e9cc0f30f307983cc01e60f301e63cc07987981e7e6003d39800f6cc001eed8995,0x80c184220501,0x7983cc1e62d903cc079bcc0f30f30b643cc01e60f301e63cc07987981e7e6003d39800f8b2001eed8995,0x798003ea6000f6cc00408c0f30f307983cc01e60f301e63cc07987981e7e6003d39800f31e601eee0315,0x7983cc1e62d903cc079bcc0f30f30b643cc01e60f301e63cc07987981e7e6003d39800f8b2001eed8995,0x79800f4e6003cfcc007d4c0f30f307983cc01e60f301e63cc07987981e7e6003d39800f33cc01eef6f95,0x0,0x79801e7e60079bcc01e9cc0f30f307983cc01e60f301e63cc07987981e7e6003d39800f6cc001eed8995,0x0,0x7980799e601e63cc03cfcc0f30f307983cc01e60f301e63cc07987981e7e6003d39800f6cc001eed8995,0x0,0x844184220501,0x804184220501,0x844184220501,0x844184220501,0x0,0xc084200481,0x0,0xc084200481,0x0,0x0,0x0,0x0,0x0,0x0,0x400021001000000000000200000000000040002100100000100400000001000001000200010000800040000800080002000080400000101000000400000000400000001001887fda7,0x0,0x0,0x44084200481,0x4084200481,0x44084200481],
[0x4084200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_3947 : TreeBound (n := 4) 106 (programCode 0x4429073b) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part010_3948 part010_3949 part010_3950 part010_3951 part010_4032 part010_4033 part010_4114 part010_4115 part010_4196 part010_4277 part010_4358 part010_4439 part010_4520 part010_4633 part010_4874 part010_5019

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5277 : TreeBound (n := 4) 106 (programCode 0x4429073c51) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080400200481,0x1080442208481,0x1080400200481,0x1080442208481,0x1080421204481,0x10804a5210481,0x10804e721c481,0x10804a5210481,0x1080400200481,0x0,0x80006000100c0002402004200102002080082ce3,0x80042001000c0002402004200102002080082ce3,0x8000a000200c0002402004200102002080082de3,0x80402004000c0002402004200102002080082ce3,0x80012000400c0002402004200102002080082ee3,0x80502004000c0002402004200102002080082ce3,0x80022000800c0002402004200102002080082ce3,0x80402000100c0002402004200102002080082ce3,0x80042001000c0002402004200102002080082ce3,0xf307983cc001f530000000408c004458000408cf3001e67981e6f3001e679801ed980079f9801e8e9855,0x0,0x0,0x80102004000c0002402004200102002080082ce3,0x0,0x80202008000c0002402004200102002080086ce3,0x0,0x0,0x1000024020022],
[0xf30000b6400088b00008118003cc0f312fc3cc3d398007b6822ded9800811a22c79800081183cc1e7556,0x8000a000200c2002080404210108002010080ce3,0x8000a000201008040210008400220008804021e4,0x80012000400c0402100804222108002020080ce3,0x800120004020080c0210010400420010802013e4,0x1000024020022,0x80022000804008140210020400820020802015e4,0x1000024020022,0x80042001008008240210048401020040805229e4,0x0,0x80082002010008440210088402020080806031e4,0x80102004000c0002402004200108002080082ce3,0x0,0x80202008000c0002804004200108002100084ce3,0x0,0x0,0x80006000100c0002804004200104002100084ce3,0x80002001000c0002804004200104002100084ce3,0x8000a000200c0002804004200104002100084de3,0x0,0x80012000400c0002804004200104002100084ee3,0x0,0x80022000800c0002804004200104002100084ce3,0x0,0x80042001000c0002804004200104002100084ce3,0x80022010800c0002804004200104002100084ce3,0x0,0x80202010000c0002804004200104002100084ce3,0x80102004000c0002804004200104002100086ce3,0x0,0x80202008000c0002804004200104002100084ce3,0x0],
[0x0,0x1000024020022,0xf30000b6400088b00007980003cc3cc0f30f303d39801e7e6000079801f5300003cc001f5307983d1216,0x0,0x8000a000201008040210008400240009008041e4,0x8000a000201008040210008400240009008041e4,0x800120004020080c0210010400440011002013e4,0x1000024020022,0x80022000804008140210020400840021002015e4,0x1000024020022,0x80042001008008240210048401040041009249e4,0x80082002000c0402010084202108002002080ce3,0x8008200201000844021008840204008100a051e4,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5358 : TreeBound (n := 4) 106 (programCode 0x4429073c52) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10818e7204481,0x1081084210481,0x10818e7204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x80006000100c0020502804220102002080082ce3,0x8004200100840020100804220102002080080ce3,0x8000a00020140020502804220102002080082de3,0x8040200100840020100804220102002080080ce3,0x8000a000100808020210004400180004020100e4,0x8044200100840020100804220102002080080ce3,0x8002200080440020100804220102002080080ce3,0x8044200100840020100804220102002080080ce3,0x8004200100840020100804220102002080080ce3,0x0,0x0,0x0,0x0,0xf300f33cc0f30f300f30003cc3cc3cc0f303cc3d39801e7e822c079801ed99e60f30001ed983cc1e7556,0x0,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3d39801e7e85f8079801f531e60f30001f5307983cd556,0x0,0x0],
[0xf30000b6400088b00007983cc3cc3cc0f303cc3d39801e7e822c079801ed99e60798001ed983cc1e7556,0x0,0x0,0x0,0x0,0xf307983cc00088b00f30003cc3cc3cc0f303cc3d39801e7e822c079801ed99e60798001ed983cc1e7556,0x40000010100000010400000101000000100001000100001000100010001000010001020020000020000020200020000200000210000000810008000100000008100008000408793a8,0x0,0x0,0xf303cc3cc03ccf303cc0003cc3cc3cc0f303cc3d39801e7e822c079801ed99e60798001ed983cc97f556,0x0,0x0,0xf300f33cc0f30f300f30003cc3cc3cc0f303cc3d39801e7e822c079801ed99e60798001ed983cc1e7556,0x0,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3d39801e7e822c079801ed99e60798001ed983cc5b3556,0x0,0x80006000100c0020904804220104002100084ce3,0x8000200100040020100804220104002100080ce3,0x8000a00020140020904804220104002100084de3,0x0,0x0,0x80012000400808020210084400180004402111e4,0x8002200080440020100804220104002100080ce3,0x80022000800808020210084400180004402111e4,0x8004200100840020100804220104002100080ce3,0x8004201100840020100804220104002100080ce3,0x0,0x8004201100840020100804220104002100080ce3,0x0,0x0,0x0,0x0],
[0x0,0xf307983cc0000f307980003cc3cc3cc0f303cc3d39801e7e85f8079801f531e603cc001f5307983cd556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400010001000000024000300010000000200010000400010004000100004000100010080100000800000200803000002000002080000008800080000800000082000400020005b1a8,0x0,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3d39801e7e85f8079801f531e603cc001f5307983cd556,0x0,0x0,0xf300f33cc0f30f300f30003cc3cc3cc0f303cc3d39801e7e85f8079801f531e603cc001f530798d4b556,0x0,0xf301e63cc0798f301e60003cc3cc3cc0f303cc3d39801e7e85f8079801f531e603cc001f5307983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5439 : TreeBound (n := 4) 106 (programCode 0x4429073c53) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080400200481,0x1080442208481,0x1080400200481,0x1080442208481,0x1080421204481,0x10804a5210481,0x10804e721c481,0x10804a5210481,0x1080400200481,0x0,0x8000600010140004402004200102002080082ce3,0x8004200100140004402004200102002080082ce3,0x8000a00020140004402004200102002080082de3,0x8040200400140004402004200102002080082ce3,0x8001200040140004402004200102002080082ee3,0x8050200400140004402004200102002080082ce3,0x8002200080140004402004200102002080082ce3,0x8040200020140004402004200102002080082de3,0x8004200100140004402004200102002080082ce3,0x0,0x0,0x0,0x8010200400140004402004200102002080082ce3,0x0,0x8020200800140004402004200102002080086ce3,0x0,0x0,0xc0003000142004080404210100402200080ce3],
[0x0,0x80024020022,0x0,0x240009000140804100804224100802200080ce3,0x8118007b66000811801e6003cc79807b84603d398408cf30111d9803d3984bf798003d398102382646,0x80024020022,0x1ed98007b66000fa980079807aa0901ea45803db301119cc0445f9a76573003cfcc2764f98222d16f36,0x80024020022,0x3d39803cde6003d39800f3003cfcc00f3f3003d3981e61e6003d3981e6798f3079801e679807983ffb6,0x0,0xf379803cde60079f9803cc007aec801ebb2003db3001e9cc1ed9f9a9c4f301e63cc29c47982d9172136,0x0,0x0,0x0,0x0,0x0,0x8000600010140004804004200104002100084ce3,0x8000200100140004804004200104002100084ce3,0x8000a00020140004804004200104002100084de3,0x0,0x8001200040140004804004200104002100084ee3,0xf300003cc1e60f303cc001116000445800088b079801e7e6007a73001e7e6003d39800f3f3001ede5995,0x8002200080140004804004200104002100084ce3,0x0,0x8004200100140004804004200104002100084ce3,0x8002201080140004804004200104002100084ce3,0x0,0x8020201000140004804004200104002100084ce3,0x8010200400140004804004200104002100086ce3,0x0,0x8020200800140004804004200104002100084ce3,0x0],
[0x0,0x0,0x0,0x80024020022,0x0,0x0,0xfa98003ea60008118003cc07a82301ea08c03db300981cc025ff9c4d366001ed9844d2730204707c36,0x80024020022,0x1ed98007b66000fa980079807a91601ea45803db3001e9cc0445f9c54ce6003d398454bf30222d16f36,0x80024020022,0x79f9801e7e6003d39801e6003d39801e7e6003d39801e9cc8929f9a22cf300f3798222cf300f307ec26,0x1040041000140804020104204100102200080de3,0xf379803cde60079f9803cc007a73001e9cc003db3001e9cc1ed9f9c459e601e67984458f301e60f8936,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5520 : TreeBound (n := 4) 106 (programCode 0x4429073c54) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080000210481,0x1080421204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x0,0x8040021000804000000004000102002080080ce3,0x0,0x80000220481,0x280840220481,0x80000220481,0x280840220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0x8000a000201008040210008400220008804021e4],
[0x80006000101008040210008400220008804020e4,0xf303cc3cc1e60f307980007983cc1e60f307983d39800f4e6003d39800fa98f30798000fa98f30799556,0x8000a000201008040210008400220008804021e4,0x8000a000201008040210008400220008804021e4,0x80012000401008040210008400220008804023e4,0x8000a004001008040210008400220008804020e4,0x80022000801008040210008400220008804025e4,0x8000a000201008040210008400220008804021e4,0x80042001001008040210008400220008804029e4,0x80102004001008040210008400220008804020e4,0x80082002001008040210008400220008804031e4,0x0,0x80102004001008040210008400220008804020e4,0x0,0x80202008001008040210008400220008804060e4,0x0,0x0,0x0,0x0,0x80000220481,0x280840220481,0x80000220481,0x280840220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0x80002000201008040210008400240009008040e4,0x80006000101008040210008400240009008040e4,0x0,0x8000a000201008040210008400240009008041e4,0x8000a000201008040210008400240009008041e4,0x80012000401008040210008400240009008043e4,0x8000a008001008040210008400240009008041e4,0x80022000801008040210008400240009008045e4,0x8000a000201008040210008400240009008041e4,0x80042001001008040210008400240009008049e4,0x80202008001008040210008400240009008040e4,0x80082002001008040210008400240009008051e4,0x0,0x80102004001008040210008400240009008060e4,0x0,0x80202008001008040210008400240009008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5601 : TreeBound (n := 4) 106 (programCode 0x4429073c55) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x1080840218481,0x1080821204481,0x1080800200481,0x1080800208481,0x1080800200481,0x1080800208481,0x1080800208481,0x1080840210481,0x1080840210481,0x1080840210481,0x1080800200481,0x0,0x0,0x8040021000204008040204008102002080080ee3,0x0,0x80800220481,0x280840220481,0x80800220481,0x280840220481,0x280840220481,0x4808c2220481,0x6808c2220481,0x4808c2220481,0x80800220481,0x0,0x0,0x0,0x0,0x0,0x8000a000201008040210008400220008804021e4],
[0x80006000101008040210008400220008804020e4,0xf303cc3cc1e60f307980007983cc1e60f307983d39800f4e6003d39800fa98f30798000fa98f30799556,0x8000a000201008040210008400220008804021e4,0x8000a000201008040210008400220008804021e4,0x80012000401008040210008400220008804023e4,0x8000a004001008040210008400220008804020e4,0x80022000801008040210008400220008804025e4,0x8000a000201008040210008400220008804021e4,0x80042001001008040210008400220008804029e4,0x80102004001008040210008400220008804020e4,0x80082002001008040210008400220008804031e4,0x0,0x80102004001008040210008400220008804020e4,0x0,0x80202008001008040210008400220008804060e4,0x0,0x0,0x0,0x0,0x80800220481,0x280840220481,0x80800220481,0x280840220481,0x280840220481,0x4808c2220481,0x6808c2220481,0x4808c2220481,0x80800220481,0x0,0x0,0x0,0x0],
[0x0,0x80002000201008040210008400240009008040e4,0x80006000101008040210008400240009008040e4,0x0,0x8000a000201008040210008400240009008041e4,0x8000a000201008040210008400240009008041e4,0x80012000401008040210008400240009008043e4,0x8000a008001008040210008400240009008041e4,0x80022000801008040210008400240009008045e4,0x8000a000201008040210008400240009008041e4,0x80042001001008040210008400240009008049e4,0x80202008001008040210008400240009008040e4,0x80082002001008040210008400240009008051e4,0x0,0x80102004001008040210008400240009008060e4,0x0,0x80202008001008040210008400240009008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5682 : TreeBound (n := 4) 106 (programCode 0x4429073c56) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080824340c82]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5683 : TreeBound (n := 4) 106 (programCode 0x4429073c57) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080024040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5684 : TreeBound (n := 4) 106 (programCode 0x4429073c58) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080824340c82]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5685 : TreeBound (n := 4) 106 (programCode 0x4429073c59) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080024040022]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5686 : TreeBound (n := 4) 106 (programCode 0x4429073c5a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079800f3003db3000f3f3003d3987981e6003d39879bcc1e60f30079bcc0079932fb6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5687 : TreeBound (n := 4) 106 (programCode 0x4429073c5b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10810a5204481,0x1081084210481,0x10810a5204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0xc00030010004402010040c0102002080081ce3,0x8040021001004040201004040102002080081ce3,0x1400050010008402010040c0102002080081de3,0x481084220481,0x2810c4220481,0x481084220481,0x2810c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x16c80005b200016c803cc1e60f379801e61e60f301e63cc07a82301e603cc3cc0f30f6cc001e740995],
[0x0,0x445800111600025f803cc1e60f379801e61e60f301e63cc07a82301e607983cc1e60f6cc001e740995,0x0,0x0,0x8118007b6600081181e60003d411811160003d398408de7f66039840939ae92a980409398102384536,0x0,0x20200000020800000202000000208000020000010400000010008000104000000102002001002000400020020000020000101000010001000a000100000040100004000202793a8,0x3d39800f4e6003d39803cc1e60f379801e61e60f301e63cc07a82301e63cc03ccf300f6cc001e740995,0x0,0x0,0x79f9801e7e60079f981e60003d398011160003d3983cc1e7e63d3983cc79ad9079803cc7980f307cbb6,0x0,0x0,0x0,0x0,0x0,0xc0003001000440201004140104002100081ce3,0x0,0x140005001000840201004140104002100081de3,0x481084220481,0x2810c4220481,0x481084220481,0x2810c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x445800111600025f803cc0000f379801e61e60f301e63cc07a82301e600003cc0000f6cc001e740995,0x0,0x0,0x8118007b6600081180f30003d57e010230003d3984bf1e7f9393984bff32727fcc04bff3012fc9b1b6,0x1ed98007b66000fa9803cc1e60f379801e61e60f301e63cc07a82301e63cc03ccf300f6cc001e740995,0x20200000020800000202000000208000020000010800000010020000108000000102000001002000400020020000020000402000010002000c000200000100200004000202793a8,0x3d39800f4e6003d39803cc1e60f379801e61e60f301e63cc07a82301e61e603cc7980f6cc001e740995,0x0,0xf379803cde60079f9803cc1e60f379801e61e60f301e63cc07a82301e63cc03ccf300f6cc001e740995,0x79f9801e7e60079f980f30003d398010230003d3983cc1e7e63d3983ccf325f83cc03ccf300f307cbb6,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5768 : TreeBound (n := 4) 106 (programCode 0x4429073c5c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f3079801e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5769 : TreeBound (n := 4) 106 (programCode 0x4429073c5d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0003002040080010084200108002200080ce3,0x8040021002040080100804280108002200080ce3,0x140005002040080020104200108002200080de3,0x8040001002040080000004200108002200080ce3,0x240009002040080040204200108002200080ee3,0x8040001002040080000004200108002200080ce3,0x440011002040080080404210108002200080ce3,0x0,0xa000480012040080402004280108002200082ce3,0x208024040022,0xa000880022040080402004280108002200082de3,0x208024040022,0x208024040022,0x210024040022,0x200024040022,0x210024040022,0x200024040022,0x4040101000008040210000400080002000000e4,0x0,0x4080102000008040210000400080002000000e4,0x200024040022,0x4100104020008800210100404080102000824e4,0xa020080802040080402004280108002200086ce3,0x4200108040009000210200408080202000844e4,0x840021002040080100804280108002200080ce3,0x0,0x8040031002000480180c040b2100082002080ce3,0x0,0x8040031002000880180c040b4100102004080ce3,0x8040001002000080000004000100002000080ce3,0x8040001002000080000004000100202008080ce3],
[0x8040001002000080000004000100002000080ce3,0x8040001002000080000004000100402010080ce3,0x8040001002000080000004000100002080080ce3,0x0,0x3d39803cde6003d3983cc0003cc1e612fc0003d39800f4e7e63d39800f3f50460f3000f3f31e60f63b6,0x0,0x8040001002000080000004000100002000080ce3,0x8040001002000080000004000102002080080ce3,0x0,0x0,0x0,0x0,0x1040041002000480201004082100082002081ce3,0x0,0x1040041002000880201004084100102004081de3,0x0,0x0,0x0,0x1040041002008080201004080100402010081ce3,0x79f9803cde60079f9807984bf1e603cc7980f307981e61e6079a5f81e679801e85f80f379801e6c6c85,0x0,0xf37983cc1e600f37983cc0003cc1e6222c0003d3a01276cde60079800f6ce0460f3000f3f31e60f67a6,0x0,0x20020000080080000100200000200800020001340080000800040000400100001002680010000200040000800020010000080268000100020000400080000801000001000c87fe27,0x1040041002008080201004080102002080081ce3,0x0,0x1040041002008080201004080104002100081ce3,0x0,0x0,0x182021204481,0x40001002010080000004000100001020080ca3,0x182021204481],
[0x82000200481,0x82000208481,0x82000200481,0x82000208481,0x82000220481,0x40001002010080000004000100802020080ce3,0x79f9801e7e60079f983cc0003cc1e612fc0003d39800f4e7e63d39800f3f50460f3000f3f31e60f63b6,0x40001002010080000004000101002040080ce3,0x82000200481,0x82000220481,0x0,0x82000220481,0x0,0x0,0x2000480012040080402004280108002200082ce3,0x8024040022,0x2000880022040080402004280108002200082de3,0x8024040022,0x8024040022,0x10024040022,0x24040022,0x10024040022,0x24040022,0x40041000008040210000400080002000000e4,0x0,0x80042000008040210000400080002000000e4,0x24040022,0x8420244410a2,0x24040022,0x8420244410a2,0x0,0xc00410012040080080404210108002200080ce3],
[0x0,0xc00810022040080080404210108002200080ce3,0x0,0x801020042040080100804280108002200080ce3,0x20010800402008080210010400480012002013e4,0x800024040022,0x20020800804008000210000400880022002015e4,0x800024040022,0x1e601e7e601e61e601e6007983cfcc00f307983d3981e61e607d53981e9cc1e64bf001e9cc0003cfffb6,0x0,0x1e603cde600f31e603cc007983d39800f307983d3983cc1e60f6d3983cfcc1f53f3003cfcc00f307cbb6,0x800024040022,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x4000500012040080804004300108002200084ce3,0x0,0x4000900022040080804004300108002200084de3,0x0,0x4001100042040080804004300108002200084ee3,0x0,0x24040022,0x0,0x24040022,0xf33d39bcc01e6001e7e9ccf307980001e607983db3799e9cc0000798003cc1e688b00003cc0000001e56,0x0,0x4020101802040080804004300108002200084ce3,0x24040022,0x420244410a2,0x24040022,0x420244410a2],
[0x0,0x0,0x0,0x0,0x0,0x0,0x40011000402008080210010400480012002013e4,0x800024040022,0x40021000804008000210000400880022002015e4,0x800024040022,0x3cc01e6f301e63cc01e6007983db3000f307983d3987981e61e9d39879bcc1e64bf0079bcc0003db63b6,0x0,0x3cc03ccf300f33cc03cc007983d39800f307983d3983cc1e60f6d3983cfcc1f53f3003cfcc00f307cbb6,0x800024040022,0x8420244410a2,0x8420244410a2,0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5914 : TreeBound (n := 4) 106 (programCode 0x4429073c5e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80402010440010000004200108002200080ce3,0xf30b6400088b0f308118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc0001e61556,0x80802020440010000004200108002200080ce3,0x1e612fc0005388000fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc000445b3b6,0x81002040440020100804220108002200080ce3,0x800108c0420008800210010404080102006633e4,0x82002080440020100804220108002200080ce3,0x80020940820008800210020404080102006a35e4,0x84002100440000000004200108002200080ce3,0x80040a41020008800210040404080102005229e4,0x0,0x80080c42020008800210080404080102006231e4,0x90002400440080010084200108002200080ce3,0x82002100440020100804220108002200080ce3,0xa0002800440100010084200108002200080ce3,0x3cc1e63cc07992fc1e60798004458000fa98003d39bcc01e6798079bcc3cc1e60f303cc3cc07983cd556,0x16c800111600016c80798004458000fa98003d39bcc01e7e60079bcc3cc1e60f303cc3cc0001e61556,0x7983cc1e60f307980798004458000fa98003d39bcc01e7e60079bcc3cc1e60f303cc3cc0000001556,0x0,0x1400044020008800210100404080102000221e4,0x1e607987987981e608118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc000445b3b6,0x1e60f3097e00025f80798004458000fa98003d39bcc01e7e63d39bcc3cc1e60f303cc3cc000445b3b6,0x1e60f307983cc1e60fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc000445b3b6,0x1008040020008800210000404080102000221e4,0x1010040420008800210010404080102002233e4,0x0,0x1020040820008800210020404080102002235e4,0x1100044020008800210100404080102000221e4,0x1040041020008800210040404080102004229e4,0x0],
[0x1080042020008800210080404080102004231e4,0x1100040020008800210000404080102000221e4,0x1100044020008800210100404080102000221e4,0x0,0x1200048020008800210200404080102000261e4,0x0,0x200408010840010080404210108002200080ce3,0x7987987980f308118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc0000001556,0x200808020840010080404210108002200080ce3,0x798000f307983cc1e60fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc0f3079b3b6,0x201008040840020100804220108002200080ce3,0x1010880420008800210010404080102006433e4,0x202008080840020100804220108002200080ce3,0x1020100820008800210020404080102002835e4,0x204008100840000000004200108002200080ce3,0x1040241020008800210040404080102005229e4,0x0,0x1080442020008800210080404080102006231e4,0x210008400840080442204208108002200082ee3,0x204008000840000000004200108002200080ce3,0x220008800840100844204208108002200084ee3,0x1201008020008800210200404080102008261e4,0x0,0x2400084020008800210100404080102000422e4,0x798079f98079879808118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc000faa0ed6,0x2400086420008800210190404080102006433e4,0x7980f379803cc7980fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc000faa2d36,0x2008080020008800210000404080102000422e4,0x212024741d02,0x272024741d02,0x212024741d02,0x272024741d02],
[0x222024741d02,0x0,0x222024741d02,0x2100080020008800210000404080102000422e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x400410010840010080404210108002200080ce3,0x0,0x400810020840010080404210108002200080ce3,0x0,0x401010040840020100804220108002200080ce3,0xc12024741902,0x8420244410a2,0xc12024741902,0x8420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x4400100020008800210000404080102000804e4,0xf30079bcc0798f3008118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc001e610856,0x44001068200088002101a0404080102006835e4,0xf300f33cc03ccf300fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc001edaa6b6,0x4008100020008800210000404080102000804e4,0x212024741d02,0x272024741d02],
[0x212024741d02,0x272024741d02,0x222024741d02,0x0,0x222024741d02,0x4000100020008800210000404080102000804e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x800420010040010000004200108002200080ce3,0x7980007983cc81180008118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc0f30799556,0x800820020040010000004200108002200080ce3,0x798000f307984458000fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc0f3079b3b6,0x801020040840020100804220108002200080ce3,0xe12024741d02,0x8420244410a2,0xe12024741d02,0x8420244410a2,0xc220246418e2,0x0,0xc220246418e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x3cc0003cde6003d398fa98004458000fa98003d39bcc01e7e63d39bcc3cc1e60f303cc3cc0079fd7fb6,0x3cc007d4c0079bcc008118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc0079fd7fb6,0x8400205020008800210140404080102005029e4,0x3cc00f6cc003cfcc00fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc0079fd7fb6,0x8008200020008800210000404080102001029e4],
[0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x0,0x4220246418e2,0x8008204020008800210100404080102001029e4,0x4420246418e2,0x4620246418e2,0x4420246418e2,0x0,0x3d39803cde60079f983cc3cc1e60f30b645b21e60f4e9cc3ea6f30f4e6003ccf303ccf3003cde7033d5,0x0,0x3d39803cde60079f983cc3cc1e63cc222dc7ad4a0f4e9cdab26f36a6e6003ccf303ccf300799e7033d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7980001e600007980798004458000fa98003d39bcc01e7e60079bcc0001e600003cc0000000001556,0x0,0x79f9803cde60079f983ea60f307983cfcc1f5307981e9ea61e6fa981e679801ed9800f379801e77d0e5,0x0,0x7980001e600007980798004458000fa98003d39bcc01e7e60079bcc3cc1e600003cc3cc0000001556,0x0,0x0,0x7980001e7e60079f98fa98004458000fa98003d39bcc01e7e63d39bcc3cc1e60f303cc3cc00f3814bb6,0x798007b660079f98008118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc00f3814bb6,0x10400406020008800210180404080102006031e4],
[0x79800f4e6003d39800fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc00f3814bb6,0x10008400020008800210000404080102002031e4,0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x0,0x4220246418e2,0x10008404020008800210100404080102002031e4,0x4420246418e2,0x4620246418e2,0x4420246418e2,0x0,0x0,0x0,0x0,0x7980011167984458000fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc0f3079b3b6,0x8800020008800210000404080102004020e4,0x22010800420008800210010404080102006033e4,0x8420244410a2,0x5010b0082000480020802040588010200582da4,0x8420244410a2,0x29040041020008800210040404080102004229e4,0x0,0x31080042020008800210080404080102004231e4,0x20244410a2,0x8420244410a2,0x20244410a2,0x8420244410a2,0x0,0xc00410010c40010080404210108002200080ce3],
[0x1e600097e0007b660008118004458000fa98003d39bcc01e6001ed9bcc3cc1e60f303cc3cc03cc1e7556,0xc00810020c40010080404210108002200080ce3,0x1e60011160003ea6000fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc03cc9813b6,0x801020040840020100804220108002200080ce3,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x0,0x0,0x0,0x0,0x0,0xc12024741902,0x420244410a2,0xc12024741902,0x420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x20244410a2,0x420244410a2,0x20244410a2,0x420244410a2],
[0x0,0x0,0x0,0x0,0x3cc001023000408c000fa98004458000fa98003d39bcc01e6003d39bcc3cc1e60f303cc3cc0798b673b6,0x40009000020008800210000404080102008061e4,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x3cc7980f307983cc7980798004458000fa98003d39bcc01e7e60079bcc3cc1e60f303cc3cc07983cd556,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6155 : TreeBound (n := 4) 106 (programCode 0x4429073c5f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0003004040100010084200108002200080ce3,0x0,0x440021004000500080404012100082002080ce3,0x40021004020100000004000100002020080ce3,0x440021004000900080404014100102004080ce3,0x40021004000100000004000100002000080ce3,0x840021004024100100804120100202008080ce3,0x40021004000100000004000100002000080ce3,0x840021004004100100804100100402010080ce3,0x0,0x40021004020100000004000100802020080ce3,0x0,0x0,0x40021004000100000004000100002000080ce3,0x0,0x16c800111600016c83cc0003ea60012fc0003d398f301e7e600798f30799e607980f30798001e61556,0x0,0x0,0x140005004040100020104200108002200080de3,0x0,0x182021204481,0x25f800097e00025f83cc0003cc3cc12fc0003d39801e7e7e60079801e605b20003cc1e603cc1e61556,0x182021204481,0x82000200481,0x82000208481,0x82000200481,0x82000208481,0x82000220481,0x0,0x0,0x0],
[0x82000200481,0x82000220481,0x0,0x82000220481,0x0,0x240009004040100040204200108002200080ee3,0x8118007b6600081183cc0003d398012fc0003d3983cc1e7e63d3983cfcc1e60f3003cfcc00f307cbb6,0x440011004040100080404210108002200080ce3,0xfa98003ea6000fa983cc0003d398012fc0003d3983cc1e7e63d3983cfcc1e60f3003cfcc00f307cbb6,0x840021004040100100804300108002200080ce3,0x0,0x80610014040100010084200108002200080ce3,0x0,0x100a10024040100020104200108002200080de3,0x0,0x201220044040100040204200108002200080ee3,0x3cc03cfcc03cc3cc03cde6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x400024040022,0x3cc079bcc01e63cc0799e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x400024040022,0x420024040022,0x0,0x420024040022,0x2010280404040100402004280108002200082ce3,0x3ccf303ccf3003ccf300f3003cfcc00f3f3003d3981e61e6003d3981e9cc1e60f3001e9cc007983ffb6,0x400024040022,0x3cde603cc79803cde603cc003db3000f6cc003d3987981e6003d39879bcc1e60f30079bcc01e60f63b6,0x0,0x1040041004000500201004102100082002081ce3,0x1200000009800040002000000048000400000005000000010002400090000000100800001202008000810020000020000048000600020008800000010001200010000800051ea8,0x1040041004000900201004104100102004081de3,0x0],
[0x0,0x0,0x1040041004008100201004100100402010081ce3,0x7736826b281dcda09aca0077447ab280ee6ee1aca00ee7a0eb2bb9aca0ee6c166b2faef40db9acaee6b9f359bccc176735c23785a8735943b9ae7cd650ee7a85e8143b9ad8e6b2bb9c3802806bb9e83aca0077447ab2801dcda09aca0078a2a81540eeb012f9900ee747fd982a49,0x0,0x0,0x0,0x0,0x1040041004008100201004100102002080081ce3,0x0,0x1040041004008100201004100104002100081ce3,0xf379803cde60079f981e601e67987980f301e60f301e63cc07aec801e7e6003d39800f6cc001e740995,0x40201004040100000004200108002200080ce3,0x0,0x2000480014040100402004280108002200082ce3,0x2040080104040100402004280108002200082ce3,0x2000880024040100402004280108002200082de3,0x2040080404040100402004280108002200082ce3,0x2001080044040100402004280108002200082ee3,0x2050080404040100402004280108002200082ce3,0x24040022,0x0,0x24040022,0x0,0x0,0x0,0x24040022,0x8420244410a2,0x24040022,0x8420244410a2,0x0,0x800410014040100100804300108002200080ce3],
[0x1e600097e0007b66000b640003ea60012fc0003d398f301e7e61ed98f33cc1e60f300f33cc03cc1e7556,0x800810024040100100804300108002200080ce3,0x1e60011160003ea60012fc0003ea60012fc0003d398f301e7e63d398f33cc1e60f300f33cc03cc1e93b6,0x1020044040100000004200108002200080ce3,0x1e6003ea6003cde6003cde6003ea600082fe003d3992fc0f30111d98f708c1f53f300f33cc04bf268646,0x8420244410a2,0x1e6007b66000f4e600799e6003ea6000820b003d3991160f30241998fad4c1eda7300f33cc0445a35226,0x8420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x4000500014040100804004300108002200084ce3,0x0,0x4000900024040100804004300108002200084de3,0x0,0x4001100044040100804004300108002200084ee3,0x7980001e61e603cc3cc1e61e607987980f30f3079801e7e6007aec801e9cc003db3000f6cc001ede5995,0x24040022,0x7983cc1e62d903cc1e61e61e607987980f30f3079801e7e6007aec801e9cc003db3000f6cc001ede5995,0x24040022,0x20024040022,0x0,0x20024040022,0x24040022,0x40024040022,0x24040022,0x40024040022],
[0x0,0x0,0x0,0x0,0x3cc001023000408c0012fc000408c0012fc0003d399e601e7e63d399e63cc1e60f301e63cc07983cf3b6,0x3cc97e0f3000408c0012fc000408c0013ef0003d399e601e7e63d399e63cc1e60f301e63cc07983cf3b6,0x3cc003d39803cfcc003cde6003ea60008a96003d39b15c0f303ead98f708c1f53f300f33cc0c57652c46,0x8420244410a2,0x3cc0079f9800f6cc00799e6003ea600089a3003d39af760f3014e998fad4c1f53f300f33cc0bdde08ba6,0x8420244410a2,0x8220246410e2,0x8100204040100000004200108002200080ce3,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6300 : TreeBound (n := 4) 106 (programCode 0x4429073c60) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x16c800111600016c83cc3cc1e60f30b645b21e60f4e9cc3ea6f30f4e6003ccf303ccf3003cde7033d5,0x0,0xf307980001e600007981e60007d4c0010230003db3d4a01e7e600799e63cc2d900001e60000000001dc6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf307980001e60f307980f3000408c0010230003d399e601e7e600799e60001e600001e60000000001556,0x0,0x6000000018000000120000000180000400000030000000084000000310008800800040200100000804000408011001008004000002010000008100000100100000100108403a7,0x0,0x6000000018000000120000000180000800000030000000208000000920009002800100200200000804001008012004008004000002020000010200000100200000100109413a7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x810020440009000210010408080202002153e4,0xa00020140009000210200408080202000100e4,0x820020840009000210020408080202002155e4,0x800028040009000210000408080202000100e4,0x840021040009000210040408080202008149e4,0x0,0x880022040009000210080408080202008151e4,0x0],
[0x900024040009000210100408080202000100e4,0x0,0xa00028040009000210200408080202000100e4,0x0,0x16c800111600025f83cc3cc1e63cc0b645b21e60f4e9cc3ea6f30f4e6003ccf303ccf3003cde7033d5,0x16c80005b20f316c80f3000408c0010230003d399e601e7e600799e60005b20003ea60003cc1e61556,0x16c800111600025f83cc3cc1e63cc222c97ed4a0f4e9ccf4e6f36a6e6003ccf303ccf300799e7033d5,0x0,0x0,0x0,0xf307980001e600007981e60007d4c0010230003db3d4a01e7e600799e65b22d903cc1e60000000001dc6,0x0,0x0,0x0,0x7980001e60f307980f3000408c0010230003d399e601e7e600799e60001e600001e60000000001556,0x0,0x600000001800000022000000028000040000003000000009000000051000a801800040200400000804000808015003008004000002010000008100000100100000100108403a7,0x6000000018000000220000000280000004000010000000000202000100208000000000201000000804000008010000008000040002100000008002000101002000100108403a7,0x60000000180000002200000002800004000000300000000a000000112000d80580004020010000080400200801b00b008004000002010000008200000100200000100108403a7,0x7980001e60f307980f3000408c0010230003d399e601e7e600799e60f31e603cc1e60f30000001556,0x0,0x0,0x0,0x0,0x1e60f307983cc1e61023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0x20460007983cc1e61023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0x1010040440009000210010408080202002253e4,0x1200040240009000210200408080202000241e4,0x1020040840009000210020408080202002255e4,0x1000048040009000210000408080202000241e4,0x1040041040009000210040408080202008249e4,0x25f80007983cc25f80f3000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6],
[0x1080042040009000210080408080202008251e4,0x1200048040009000210200408080202000241e4,0x1100044040009000210100408080202000261e4,0x0,0x1200048040009000210200408080202000241e4,0x0,0x0,0x0,0x0,0x3cc000f307983cc1e61023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0x3cc1e60007983cc1e61023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0x1011080440009000210010408080202002253e4,0x1201000240009000210200408080202000241e4,0x1020100840009000210020408080202002255e4,0x1000008040009000210000408080202000241e4,0x1040241040009000210040408080202008249e4,0x3cc7980007983cc25f80f3000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0x1080442040009000210080408080202008251e4,0x1201008040009000210200408080202000241e4,0x1100804040009000210100408080202004261e4,0x0,0x1201008040009000210200408080202000241e4,0x0,0x0,0x0,0x0,0x7980f379803cc7981023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc003cfed9b6,0x7b660079803cc7981023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc003cfed9b6,0x212024741d02,0x272024741d02,0x212024741d02,0x272024741d02],
[0x222024741d02,0x2010090040009000210010408080202002453e4,0x222024741d02,0x2200088040009000210200408080202000442e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x0,0x0,0x0,0xf30001023000408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc07983cf3b6,0xf301e60f3000408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc07983cf3b6,0xc12024741902,0x8420244410a2,0xc12024741902,0x8420244410a2,0x8220246410e2,0x408010200040000000004200108002200080ce3,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x0,0x0,0x0,0xf300f33cc03ccf301023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc001e9de6b6,0xf4e6003cc03ccf301023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc001e9de6b6,0x212024741d02,0x272024741d02],
[0x212024741d02,0x272024741d02,0x222024741d02,0x4020110040009000210020408080202002855e4,0x222024741d02,0x4000100040009000210000408080202000804e4,0x242024741d02,0x272024741d02,0x242024741d02,0x0,0x0,0x0,0x0,0x3cc000f30798408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0x3cc1e6000798408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc000408f3b6,0xe12024741d02,0x8420244410a2,0xe12024741d02,0x8420244410a2,0xc220246418e2,0x808020200040000000004200108002200080ce3,0xc220246418e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0,0x0,0x0,0x0,0x3cc00f6cc003cfcc01023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc01e64c23b6,0x3cde603cc003cfcc01023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc01e64c23b6],
[0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x8040210040009000210040408080202009049e4,0x4220246418e2,0x3cde603cc003cfcde7023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc01e64c23b6,0x4420246418e2,0x4620246418e2,0x4420246418e2,0xf307980001e60f307980f3000408c0010230003d399e601e7e600799e63cc1e60f301e63cc0000001556,0x0,0x0,0x0,0x0,0x79800f4e6003d39801023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc00f3448bb6,0x799e601e6003d39801023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc00f3448bb6,0x412024741902,0x4620246418e2,0x412024741902,0x4620246418e2,0x4220246418e2,0x1008041004000900021008040808020200a051e4,0x4220246418e2,0x799e601e6003d399e7023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc00f3448bb6,0x4420246418e2,0x4620246418e2,0x4420246418e2,0x0,0xf307980001e600000001e60007d4c0010230003db3d4a01e7e600799e63cc2d90f301e63cc0000001dc6,0x16cbcc1e60000798000097e0007d4c0010230003db3d4be7e60079f99e63cc2d988b01e63cc0000001dc6],
[0xf307980001e600000001e60007d4c0010230003db3d4a01e7e600799e63cc2d90f301e63cc0000001dc6,0x3cc001023798408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc079c08f3b6,0x3cc1e60f3798408de61023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc079c08f3b6,0x4201100044000900021001040808020200a453e4,0x8420244410a2,0x4020100840009000210020408080202002855e4,0x8420244410a2,0x49040041040009000210040408080202009249e4,0x0,0x5108004204000900021008040808020200a251e4,0x20244410a2,0x8420244410a2,0x20244410a2,0x8420244410a2,0x0,0x0,0x1e600097e0007b6600088b000408c0010230003d399e601e60079f99e63cc1e60f301e63cc0f30799556,0x1e63cc1e61e601e688b0f3000408c0010230003d399e601e7e600799e63cc1e60f301e63cc0f30799556,0x1e60011160003ea6001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc0f30b673b6,0x1e61e61e60003ea6001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc0f30b673b6,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2,0x8420244410a2,0x0],
[0xf307980001e600000001e60007d4c0010230003db3d4a01e7e600799e63cc2d90f301e63cc0000001dc6,0x0,0xf307980001e600000001e60007d4c0010230003db3d4a01e7e600799e63cc2d90f301e63cc0000001dc6,0x0,0x0,0xc12024741902,0x420244410a2,0xc12024741902,0x420244410a2,0x8220246410e2,0x0,0x8220246410e2,0x20244410a2,0x420244410a2,0x20244410a2,0x420244410a2,0x0,0x0,0x0,0x0,0x3cc001023000408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc07983cf3b6,0x3cc1e60f3000408c001023000408c0010230003d399e601e6003d399e63cc1e60f301e63cc07983cf3b6,0x812024741902,0x8420244410a2,0x812024741902,0x8420244410a2,0x8220246410e2,0x8000200040000000004200108002200080ce3,0x8220246410e2,0x8020244410a2,0x8420244410a2,0x8420244410a2],
[0x8420244410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_5276 : TreeBound (n := 4) 106 (programCode 0x4429073c) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part010_5277 part010_5358 part010_5439 part010_5520 part010_5601 part010_5682 part010_5683 part010_5684 part010_5685 part010_5686 part010_5687 part010_5768 part010_5769 part010_5914 part010_6155 part010_6300

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6558 : TreeBound (n := 4) 106 (programCode 0x4429073d61) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000600018040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6559 : TreeBound (n := 4) 106 (programCode 0x4429073d62) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040200108040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6560 : TreeBound (n := 4) 106 (programCode 0x4429073d63) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000a00028040200402004080108002200082de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6561 : TreeBound (n := 4) 106 (programCode 0x4429073d64) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040200408040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6562 : TreeBound (n := 4) 106 (programCode 0x4429073d65) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8001200048040200402004080108002200082ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6563 : TreeBound (n := 4) 106 (programCode 0x4429073d66) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8010200408040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6564 : TreeBound (n := 4) 106 (programCode 0x4429073d67) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8002200088040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6565 : TreeBound (n := 4) 106 (programCode 0x4429073d68) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80402000100c0002402004080108002200082ce3,0x8040200108040020402004080108002200082ce3,0x8040200020140004402004080108002200082de3,0x8040200408040080402004080108002200082ce3,0x8040200040240008402004080108002200082ee3,0x8040200402040080402004080108002200082ce3,0x8040200080440010402004080108002200082ce3,0x8040200008040000402004080108002200082ce3,0x8040200100840020402004080108002200082ce3,0x0,0x8040200082c00410402004080100082002082ce3,0x0,0x8040200082c00810402004080100102004082ce3,0x0,0x8040200000010000402004080100202008082ce3,0x0,0x8040200000010000402004080100402010082ce3,0x0,0x8040200000000000402004080100802020082ce3,0x8040200000000000402004080100002000082ce3,0x8040200000000000402004080101002040082ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x8040200201000440402004080100082002083ce3,0xf307983cc1e60f3003cc3ce0460f303cc1e63cc1e601e67980799e601e61e603cde600f30f301e8ad195,0x8040200201000840402004080100102004083de3,0x0],
[0x8040200201010040402004080100202008083ce3,0x0,0x8040200201010040402004080100402010083ce3,0x0,0x8040200201008040402004080100802020083ce3,0x8040200201008040402004080101002040083ce3,0x8040200201008040402004080101002040083ce3,0x400000101000000404000000810000001000000001008000004020000008040000014000000110808840440000001000080400020021000080084000100010000200000000007baa8,0x0,0x0,0x0,0x0,0x0,0xf30000b641e60f307987984bf0f30f30b644fbe04601e7e601e61e601e6003ccf303cc79803cdee9b345,0x0,0xf300012fc1e60f30798f3088b0f31e612fc8c7fea601e7e601e61e601e6003ccf301e67980799ee9d1a5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8040200402040080402004080108002200082ce3,0x0,0x804025804400b0402004080108002200082ce3],
[0x112022140442,0x1008045804400b0402004080108002200082ce3,0x112022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x0,0x0,0x0,0x212022140442,0x812022140442,0x212022140442,0x812022140442,0x0,0x80402804040100402004080108002200086ce3,0x8004020804040100402004080108002200086ce3,0x100804804040100402004080108002200086de3,0x8010080804040100402004080108002200086ce3,0x10020040022,0x210020040022,0x10020040022,0x210020040022,0x10020040022,0xf300f33cc03cc3cc07d4cf307981e61e607984bf445800079800000003cc1e60f300003cc0000001e56,0x0,0x0,0x10020040022,0x812822140442,0x10020040022,0x812822140442],
[0x0,0x0,0x112022140442,0x0,0x112022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x212022140442,0x0,0x1008040000040000402004080108002200082ce3,0x0,0x212022140442,0x812022140442,0x212022140442,0x812022140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6678 : TreeBound (n := 4) 106 (programCode 0x4429073d69) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8004200108040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6679 : TreeBound (n := 4) 106 (programCode 0x4429073d6a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8040200088000600402004080100082002082ce3,0x0,0x1dcd82d11eb4135940ee6d04d6501dcd65003b9e83aca000003ba23d5940003d77a050000f5de8140003d77a0500007ea8ed40000950317bbd1166b2faef4459acbdcd650000003b9aca00003b9acdb9ad1aef4459acbdcd65000003f5476a0000773597b9aca7735b1cd662a054fa,0x77360b3597b9acdb9aca07736826b2bb9acdb9aca01dcecaa0c373595dcd66dcd6503b9b413595dcd66dcd65ee6b2f73594773594ee6b283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283b9ae7cd6500ef59932800ee6d04d6500ef59932800ee6b9f35940ef5b7796573d9,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc1e625f94e20001e625f85b20003cc25f83cc1e61556,0x0,0x799e60799e600799e9cc0004bf00012fc0003cc1e625f94e20001e625f85b20003cc25f83cc1e61556,0x1dcd82d11eaca00000ee6d04d6501dcd65001dd11eaca00ee6ee223d5940003d77a050000f5de8140003d77a0500007ea8ed40000950317bbd11dde88eef4459acbdcd650000003b9aca00003b9acdb9ad1aef4459acbdcd65000003f5476a0000773597b9aca7735b1cd662a054fa,0x0,0x0,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc1e61e6097e0001e61e605b20003cc1e603cc1e61556,0x0,0x7981e61e61e607981e9cc0004bf00012fc0003cc1e61e6097e0001e61e605b20003cc1e603cc1e61556,0x1dcd82d11eb4135940ee6b28003b9e83aca01dd11eaca003b9e8423d5940003d77a050000f5de81400009502f900007ea8ed40000950317bbd11dde817b9aca00003b9acaee6b498711a00003b9acdb9ad1aef4459acbdcd650ee6b332d05e0000773597b9aca773597b9acdb915da,0x0,0x0,0x0,0x8040200088000a00402004080100102004082ce3,0x0,0xc0002088010600402004080102082080082ce3,0x0,0x140004088000a00402004080100102080082ce3,0x2040080008010200402004080102002080082ce3,0x240008108011200402004080102202080082ce3,0x40080008010200402004080102002080082ce3,0x440010108012200402004080102402080082ce3,0x0,0x0,0x8040000008000200402004080100002080082ce3,0x0],
[0x8040000008000200402004080100002080082ce3,0x2040080008010200402004080102002080082ce3,0x0,0x0,0x0,0x8040200008010200402004080100202008082ce3,0x0,0xc0002088010600402004080100402080082ce3,0x2040020408004200402004080102002080082ce3,0x140004088010a00402004080100402080082ce3,0x2040080008010200402004080100002080082ce3,0x0,0x40080008010200402004080100002080082ce3,0x0,0x0,0x840020408004200402004080102002080082ce3,0x8040000008000200402004080100002080082ce3,0x0,0x8040000008000200402004080100002080082ce3,0x2040080008010200402004080100002080082ce3,0x0,0x0,0x0,0x8040200008010200402004080100402010082ce3,0x0,0x0,0x0,0xf6163980001e600001e9cc00088b00012fc0004c21d70ae01e60001e67987b6c2b8f307983cc00001dc6,0x1000000008000800050002000040008000400008001000040004000280010000200004000020080000400100000800100000804000000418000001010000008100000010210851ea7,0x0,0x100080000100080001000800001000804000000110000000140000001100000001000020000000200000020200000002004000200000000208000002000100002000000000793a8,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1010528210501,0x1063188210501,0x1010528210501,0x1002108210501,0x1020948210501,0x1002108210501,0x1020948210501,0x8040200008000000402004080100802020082ce3,0x1061188210501,0x1000108210501,0x1061188210501,0x0,0x1002108210501,0xf30079bcc01e6f3001e7e60008118001ed98004bf4990bcc0079801e7ec68734203cc1e60f33cc2268b6,0x1002108210501,0x40000080100000200400000801000000802000000102000000120000001020000001400000800000282004000008000002020001002000104009000010000800040010000900f9ba8,0x0,0x1010508208501,0x0,0x1010508208501,0x1002108200501,0x1020948210501],
[0x1002108200501,0x1020948210501,0x40002000100008000400000001000080004000200010000100040002200000002800040000200200001001000008001000008040000010100000040000000081000000100908736a7,0x0,0x1000108200501,0x8000200001000040402004080100002000082ce3,0x0,0x1002108200501,0x4000008010000020040000080100000080100000010400000011000000101000000140000080000028200400000a00000202000100200000400a800010000800010020001100f9ba8,0x1002108200501,0x40000080100000200400000801000000802000000102000000120000001020000001400000800000282004000008000002020001002000004009000010000800010010000900f9ba8,0x0,0x1010528210501,0x1063188210501,0x1010528210501,0x1002108210501,0x1020948210501,0x1002108210501,0x1020948210501,0x0,0x1061188210501,0x1000108210501,0x1061188210501,0x0,0x1002108210501,0x0,0x1002108210501,0x0,0x0,0x0,0x0,0x4000000010000800840000008100008018000042000000140000001200000002a80004000020080000400100000800100000804000000210000000800000008100000010210840ea7],
[0x0,0x0,0x0,0x0,0x4000004010000020040000080100000080001000008008000040010000080020000140000000100088664400121990000202000100208000800866401000080002000040002067aa8,0x0,0x0,0x4000004010000020040000080100000080000000010080000010200000100800000140000001000028400400221010000204000200210000200840002000100002000000000075ba8,0x0,0x0,0x0,0x0,0x0,0x0,0xc0002088000600402004080102002080082ce3,0x2040020408004200402004080102002080082ce3,0x140004088000a00402004080102002080082ce3,0x2040080008010200402004080102002080082ce3,0x240008108001200402004080102002080082ce3,0x40080008010200402004080102002080082ce3,0x440010108002200402004080102002080082ce3,0x0,0x840020408004200402004080102002080082ce3,0x8040000008000200402004080102002080082ce3,0x1040040208008200402004080102002080083ce3,0x8040000008000200402004080102002080082ce3,0x2040080008010200402004080102002080082ce3,0x0,0x0,0x0,0x0,0x420080200080004000040008010002008040000000500000001400000009000000010000880000002a4005000a0000000220000400210008000a400100008000100004001200d1ea8],
[0x730039800040020001000200000400200040003980100002000400000801000020002000010008000040010000080010000080730000101000000401000000404000001011087fda7,0x220000000800000000a00000002000040003000100002000400008001000020002000010008000040010000080010000080402000101000000400008000400000001011087fda7,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc222d11697e000222cfa99e607983ccfa98f34497fb6,0x0,0x799e60799e600799e9cc0004bf00012fc0003cc2230dd87de0002230c699e607983d0c698f4379f936,0x0,0x0,0x0,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc0798079fd7fb6,0x20031000080000000080200000200000040003100100002000400000001000020002000010008000040010000080010000080620000101000000400000000400000001011087fda7,0x7981e61e61e607981e9cc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f38517b6,0x200020000800000001000200001000000040003000100002000400000001000020002000010008000040010000080010000080400000101000000400000000400000001011087fda7,0x400020001000000000000200000000000040003000100002000400000001000020002000010008000040010000080010000080400000101000000400000000400000001011087fda7,0x0,0x400020001000000000000200000000000040003000100002000400000001000020002000010008000040010000080010000080400000101000000400000000400000001011087fda7,0x0,0xc0002088000600402004080104002100082ce3,0x0,0x140004088000a00402004080104002100082ce3,0x40080008000200402004080104002100082ce3,0x240008108001200402004080104002100082ce3,0x40080008000200402004080104002100082ce3,0x440010108002200402004080104002100082ce3,0x0,0x840020408004200402004080104002100082ce3,0x0,0x1040040208008200402004080104002100083ce3,0x0,0x2040080008010200402004080104002100082ce3,0x7980799e601e61e601e9cc00088b000222c0003db782400f4e60001f535b22d901e60f33cc03cc2268b6,0x0,0x400020001000000000000200000000000040003000100002000400000001000020002000010008000040010000080010000080200000100800000400800000402000001011087fda7],
[0x0,0x420080200080004000100008010002008040000000500000001400000009000000010000880000002a4005000a0000000220000800210002000a400100008000200004001200d1ea8,0x0,0xf3007980001e600001e9cc00088b00012fc0004bf4a0a0001e600020461e62d903cc1e60f30000001dc6,0x1e7e6007b66001e7e9cc0004bf00012fc0003cc204702397e00020470231e603cc1e7023079c1823b6,0x2cd1f3cca0eee1aca03b9d971f3cca0ed04d6503b9acbdcd653ba23d5940003d77a050000f5de8140001faa3b500007ea8ed40000a40788ba1db3347d2e876a000104d421e5d97f5476a00003f5476db9acf9a3e885d02f73595dcd6a9a3e80e9a97b9aca7735b1cd65f04925d79da,0x799e60799e600799e9cc0004bf00012fc0003cc205632b2fe00020563231e603cc1f632307d8da09b6,0x4008000020828000102000000208280400008001000040104000200610000a80004000020080000400100000800100000804000000218000001010000008110000010210841ea7,0x0,0x0,0x3cc1e63cc1e603cc1e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e64c23b6,0x0,0x7981e61e61e607981e9cc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f353bbb6,0x10000800000202002000008000002008040000000900000001400000011000000010100200000002c2002000200000002400010000080020008200200010000200002002100e9ba8,0x400020001000000000000200000000000040003000100002000400000001000020002000010008000040010000080010000080400000101000000400000000400000001011087fda7,0x0,0x400020001000000000000200000000000040003000100002000400000001000020002000010008000040010000080010000080400000101000000400000000400000001011087fda7]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6888 : TreeBound (n := 4) 106 (programCode 0x4429073d6b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1024128204501,0x0,0xf30079bcc01e6f3003cc005f67660f30798408c1e601e67980799e601e6ab18fcde600f30f301e8ad195,0xf3001e9cc01e6f3003cc1e7e601e601e60f33cc1e601e67980799e601e61e600f4e600f30f301e8ac775,0xf30079bcc01e6f3003cc011537643cc0f307d4c1e601e67980799e601e6af21bcde600f30f301e8cd5f5,0xf3003cfcc01e6f3003cfcc1e601e60f307983cc1e601e67980799e601e61e601e7e600f30f301e8acc85,0xf3003cfcc01e6f3003cc02082c007983cc1e9cc1e601e67980799e601e62d901e7ed98f30f301e8b4605,0xf30079bcc01e6f3003cc1e7f530798f307983cc1e601e67980799e601e697e03cde600f30f301e8ad195,0xf3003cfcc01e6f3003cc03ee2c01e616c83cfcc1e601e67980799e601e62d901e81390f30f301e8cb285,0xf30079bcc01e6f3003cfcc1e60f3000000003cc1e601e67980799e601e61e603cde600f30f301e8ad195,0xf30079bcc01e6f3003cc0f4ed983cc1e60f33cc1e601e67980799e601e6a7103cde600f30f301e8ad195,0x0,0xf30079bcc01e6f3003cc3ce0460f303cc1e63cc1e601e67980799e601e61e603cde600f30f301e8ad195,0x0,0xf3003cfcc01e6f3003cc799e601e60f307983cc1e601e67980799e601e61e601e7e600f30f301e8acc85,0x159fd800000030a7a60000000c29e980acfec0567f60000000c29e980acfec0567f60000000ad553f6000001853d3000000057d95d80000057d95d80000015b577d8000005694ffd800000567f6159fd8159fd8059335b0159fd800000030a7a602b3fb0159fd80000002b3fb0567f60567f600206fc4000000afb2bb0000000614f4c000000567f602b3fb00567f6159fd800567f602b3fb0196beb0ac,0x0,0x0,0x1024128204501,0x0,0x124128224501,0x111607981e61e603cc3cfcc1e60f3001e9cc03cc1e601e67980799e601e9cc003cc3cc0f379801e8ad195,0x124128224501,0x824108220501,0x224148228501,0x1008080208010200402004080102002080083ce3,0x224148228501,0x0,0x3cc7980f31e603cc3cfcc1e60f3001e9cc03cc1e601e67980799e601e9cc003cc3cc0f379801e8ad195,0x3cfcc00f307983cfcc0f30f300003cc0f301e601e7e601e61e601e7e6001e600007b66001ef15055,0xf307983cc1e607983cfcc1e60f3003cfcc03cc1e601e67980799e601e9cc003cc7980f379801e8ad195],
[0x8008000208000200402004080100002080083ce3,0x824108220501,0x1004080208010200402004080102001080083ca3,0x824108220501,0x0,0x1024108208501,0x0,0xfa98003ea6000f6cfcc1e60f30000b6403cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x3cc7981e61e603cc3cfcc1e60f3001e9cc03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x3d39800f4e6001e9cfcc1e60f300012fc03cc1e601e67980799e601e61e603cc7980f379801e8cd5f5,0xf3007987981e61e603cfcc1e60f300f33cc03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x79f9801e7e60079bcfcc1e60f3000408c03cc1e601e67980799e601e61e603cc7980f379801e8b4b15,0x7987981e61e61e603cfcc1e60f300f33cc03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x1e67980799e600f33cfcc1e60f30007d4c03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x0,0x3cc7980f31e603cc3cfcc1e60f3001e9cc03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x0,0xf307983cc1e607983cfcc1e60f3003cfcc03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x0,0x1e607987981e61e603cfcc1e60f300f33cc03cc1e601e67980799e601e61e603cc7980f379801e8ad195,0x0,0x0,0x0,0x1024108208501,0x0,0xf30079bcc01e6f3003cc005b20000f30798408c1e601e67980799e601e9cc003db3000f3003cde8ad195,0xf30079bcc01e6f3003cfcc1e601e601e60f33cc1e601e67980799e601e9cc003db3000f30f301e8ad195,0x0,0x0,0xf30079bcc01e6f3003cc020460007a73001e9cc1e601e67980799e601e9cc003db3000f301e61e8ad195,0x0,0xf30079bcc01e6f3003cc07b66001e6f3003cfcc1e601e67980799e601e9cc003db3000f303cc1e8ad195],
[0xf30079bcc01e6f3003cfcc1e60f3000000003cc1e601e67980799e601e9cc003db3000f300001e8ad195,0xf30079bcc01e6f3003cc0f4e6003cc1e60f33cc1e601e67980799e601e9cc003db3000f30f301e8ad195,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1020528210501,0x1023188210501,0x1020528210501,0x1022108210501,0x1020948210501,0x1023188210501,0x1020948210501,0x8008200208000000402004080100802020083ce3,0x1021188210501,0x1023188210501,0x1021188210501,0x0,0x1022108210501,0x8008200208000000402004080100802020083ce3,0x1022108210501,0x0,0x0,0x1020528218501,0x0,0x1020528218501,0x1022108210501,0x1020948210501],
[0x80042002010080c0602004080101001040083ca3,0x1020948210501,0x400020001000082444000200010000020000100000800800004001000008002000014000000010488824040000000000080200010020900040080400100008000100004000206baa8,0x0,0x8004200200000040402004080100001040083ca3,0x8008200201008040402004080101002040083ce3,0x0,0x1022108210501,0x0,0x1022108210501,0x0,0x0,0x1020528210501,0x1023188210501,0x1020528210501,0x1022108210501,0x1020948210501,0x1023188210501,0x1020948210501,0x0,0x1021188210501,0x1023188210501,0x1021188210501,0x0,0x1022108210501,0x0,0x1022108210501,0x0,0x0,0x0,0x0,0x4000002010000008040000100100000100000040000000110000002220000002a800080000400100000801000008001000008000000002100000008000000101000000100b08443a7],
[0x0,0x0,0x0,0x0,0x400020001000086664000210010000020000100000800800004001000008002000014000000010ccc8666400021998000802000100219980800866601000080002000040002067aa8,0x0,0x0,0x4000010010000008040000100100000100020001000010010000200250000200ac000800004001000008010000080010000080020000101080000080200001010a0000100b08743a7,0x0,0x0,0x0,0x0,0x0,0x0,0x124128220501,0x424188220501,0x124128220501,0x824108220501,0x224148220501,0xc24188220501,0x224148220501,0x0,0x424188220501,0x8008040208008200402004080102002080083ce3,0x424188220501,0x8008000208000200402004080102002080083ce3,0x824108220501,0xc24188220501,0x824108220501,0x0,0x0,0x12416822c501],
[0x77c001000010004000000002000600010040003be010000080040000000100002300200001000800004001000008001000008077c000100460000400400000200000001005887fca7,0x12416822c501,0x740001000100004000000002014000010040003a001000008004000000010000a0002000010008000040010000080010000080768000101400000404200000200000001005887fca7,0x0,0x76000100010000400008000201d800010040003b001000008004000000010000ec002000010008000040010000080010000080768000101d80000407680000200000001005887fca7,0x0,0x0,0x0,0x0,0x1008040208000200402004080100002000083ce3,0x0,0x0,0x8000208000200402004080100002000083ce3,0x0,0x0,0x0,0x124128220501,0x424188220501,0x124128220501,0x824108220501,0x224148220501,0xc24188220501,0x224148220501,0x0,0x424188220501,0x0,0x424188220501,0x0,0x824108220501,0xc24188220501,0x824108220501,0x0],
[0x0,0xf30079bcc01e6f3003cc005b20000f30798408c1e601e67980799e601e9cc003db3000f3003cde8ad195,0x0,0x0,0x0,0xf30079bcc01e6f3003cc020460007a73001e9cc1e601e67980799e601e9cc003db3000f301e61e8ad195,0xf30079bcc01e6f3003cc1e7e6007983cc7983cc1e601e67980799e601e9cc003db3000f31e601e8ad195,0xf30079bcc01e6f3003cc07b66001e6f3003cfcc1e601e67980799e601e9cc003db3000f307981e8ad195,0x0,0xf30079bcc01e6f3003cc0f4e6003cc1e60f33cc1e601e67980799e601e9cc003db3000f30f301e8ad195,0x1dcd6501dcddc35940773770d6503b9b41359401dcf41d6500773f8bd2e820027df4cdf7a66fbd2ef9359400013efa5d21cd6c73595dcd650773770d65077360b35941dcd73e6b283b9ad8e6b283ba23d594003bc2a94ba08ee6b280000775d734ba083b9aca00000eeb01a9eb08f9,0x0,0x0,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7097 : TreeBound (n := 4) 106 (programCode 0x4429073d6c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf30000b641e60f30798b640f30f30000b6412fe04601e7e601e61e601e6003ccf303cc79803cdee9b345,0x0,0x15a28bfb00005b6904419d2b2becaec00000059335b0000000614f4c0000000567f62c99ad800acfec567f604e9a442f72880000001037e20159fd8159fd80acfec0567f6002b3fb00567f6000ad0019fd8002b3fbacfec00159fd959fd8002b3fb159fd8002b3fb159fd8002b3fb0567f6000571c948833a60cfec567f600056800cfec000ad098fec0000159fd959fd80015aaad5edf9f7c3ab,0x0,0x430e2340003f5476a00004a817c80003f5476a00003b9acc540be5dcd66dcd6500002540be5dcd66dcd65ee6b2f73594773594ee6b283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283b9ae7cd6500ef59932800ee6d04d6500ef59932800ee6b9f35940ef5b7796573d9,0x1e9cc007a73001e9cfcc0004bf00012fc0003cc1e625f94e20001e625f85b20003cc25f83cc1e61556,0x0,0x79bcc0798f30079bcfcc0004bf00012fc0003cc1e625f94e20001e625f85b20003cc25f83cc1e61556,0x0,0x0,0x0,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc1e61e6097e0001e61e605b20003cc1e603cc1e61556,0x0,0x7983cc1e60f307983cfcc0004bf00012fc0003cc1e61e6097e0001e61e605b20003cc1e603cc1e61556,0x100000080100000001000000801004000000110000000140000001100000001000020000000800000000200000008000200010000000018000000100008000100008000793a8,0x0,0x0,0x0,0xf300012fc1e60f307992fc0f30f300012fc12ffea601e7e601e61e601e6003ccf301e67980799ee9d1a5,0x0,0xc0002418010600402004080102082080082ce3,0x0,0x140004028000a00402004080100102080082de3,0x2040080408010200402004080102002080082ce3,0x240008448011200402004080102202080082ee3,0x2040080408010200402004080102002080082ce3,0x440010488012200402004080102402080082ce3,0x0,0x0,0x8040000008000200402004080100002080082ce3,0x0],
[0x8040000008000200402004080100002080082ce3,0x2040080408010200402004080102002080082ce3,0x0,0x0,0x0,0x0,0xc0002018010200402004080100202008082ce3,0x840020108010200402004080100202008082ce3,0x140004028010200402004080100202008082de3,0x2040080408010200402004080100202008082ce3,0x240008048010200402004080100202008082ee3,0x2040080408010200402004080100202008082ce3,0x440010088010200402004080100202008082ce3,0x0,0x840020108010200402004080100202008082ce3,0x8040000008010200402004080100202008082ce3,0x1040040208010200402004080100202008083ce3,0x8040000008010200402004080100202008082ce3,0x2040080408010200402004080100202008082ce3,0x0,0x0,0x0,0x0,0xc0002418010600402004080102082080082ce3,0x0,0x140004028000a00402004080100102080082de3,0x2040080408010200402004080102002080082ce3,0x240008448011200402004080102202080082ee3,0x2040080408010200402004080102002080082ce3,0x440010488012200402004080102402080082ce3,0x0,0x0],
[0x8040000008000200402004080100002080082ce3,0x0,0x8040000008000200402004080100002080082ce3,0x2040080408010200402004080102002080082ce3,0x0,0x0,0x0,0x0,0xc0002018010200402004080100402010082ce3,0x840020108010200402004080100402010082ce3,0x140004028010200402004080100402010082de3,0x2040080408010200402004080100402010082ce3,0x240008048010200402004080100402010082ee3,0x2040080408010200402004080100402010082ce3,0x440010088010200402004080100402010082ce3,0x0,0x840020108010200402004080100402010082ce3,0x8040000008010200402004080100402010082ce3,0x1040040208010200402004080100402010083ce3,0x8040000008010200402004080100402010082ce3,0x2040080408010200402004080100402010082ce3,0x0,0x0,0x0,0x0,0x0,0x0,0xf6349980000f300003cfcc00088b00012fc0004c23bd1a101e60001e67987b6c684f307983cc00001dc6,0x20100000020100000201000000201004000000110000000140000001100000001000020000000800000020200000008004000200000000208000002000100002000000000793a8,0x0,0x100100000100100001001000001001004000000110000000140000001100000001000020000000800000020200000008004000200000000208000002000100002000000000793a8,0x82000000208010002020000002000104000080010000080040002800100002000040000200100000801000008001000008000080004100000010000800101000000100508513a7],
[0x0,0x0,0x0,0x0,0x0,0x1e688b1e61e601e60f33cc03ccf3088b3cc0f301e601e7e601e61e601ea45801e7e600f6cc001e8e98e5,0x0,0x0,0x0,0x0,0xf3001e9cc007a7307980004bf0003cc07984bf01e601e7e601e61e601e60f301e6f300798f301eed8455,0xf30079bcc2046f3079803ccf3079807983ccf301e601e7e601e61e601e60f301e6f300798f301ee9b855,0xf30079bcc01e6f3079800088b0001e60f3088b01e601e7e601e61e601e60f301e6f300798f301ee9b855,0x0,0x0,0x0,0xf303cc3cc0f30f30798003db3000f307983db301e601e7e601e61e601e60f301e6f300798f301ee9b855,0xf300003cc1e60f307980000f30f300000000f301e601e7e601e61e601e60f301e6f300798f301ee9b855,0xf3001e9cc007a73079800f3f300f301e60f3f301e601e7e601e61e601e60f301e6f300798f301eed8455,0xf300003cc0000f307980000f300000000000f301e601e7e601e61e601e60f301e6f300798f301ee9b855,0xf3003cfcc00f3f3079801e6f3007983cc1e6f301e601e7e601e61e601e60f301e6f300798f301ef15055,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf300003cc1e60f307981e60f300000001e60f301e601e7e601e61e601e600001e600007980001ee9b855,0x0],
[0x1dcd6500773d0759401dcf41d6500ee729b59403b9ca6d65007735940ee6b2877394daca01dcddc35940ee6c166b283b9ad8e6b2877359b753616500218efc4ca16d63bf1328594077359400775361651dd11f24c4765e8289310eb0ee9972ef1cd66dcd651dcd657735d35a73c84a,0x159fd80614f4c567f60360f9c159fd80567f60567f60000000159fd800acfec567f602b3fb000002b4517f6000015a4be41bfec02b3fb01b07ce02b554fd800002b3fb000000002b4263fb0567f6000acfed59fd8002b3fbacfec00159fd959fd8002b3fb159fd8002b3fb159fd8002b3fb30a7a60015a9a9d5d6000acfeeb3fb000159fd80000000159fdd67f600159fd8000000015ac075c693d398ab,0x40000080100000400400000801000001000010000080080000400100000800200001400000001000c8366400220d9800040200008020c000400836601000080001000040002067aa8,0x0,0xf300003cc0000f307980000f300000000000f301e601e7e601e61e601e600001e600007980001ee9b855,0xf300003cc00f3f3079801e6f3007980001e6f301e601e7e601e61e601e600001e600007980001ee9b855,0x0,0x0,0x0,0x0,0x0,0x0,0xf3003cfcc00f3f307980004bf0003cc1e604bf01e601e7e601e61e601e61e601e67980799e601ef18d15,0xf300003cc33bc730ceee3ccf300000002ab855b9e601e7e601e61e601e60f300f37980799e601ee9b345,0xf3003cfcc00f3f307d4c004bf0001e60f308c7fea601e7e601e61e601e60f300f37980799e601ef169a5,0xf300003cc1e60f307981e60f3000000025f92fc1e601e7e601e61e601e60f300f37980799e601ee9b345,0x0,0x0,0xf303cc3cc0f30f30c57001f53000f307983df1a7e601e7e601e61e601e60f300f37980799e601ee9b345,0x0,0xf3001e9cc007a73079800f3f300f307980f3f301e601e7e601e61e601e61e601e67980799e601eed8455,0xf300003cc0000f307980000f300000000000f301e601e7e601e61e601e61e601e67980799e601ee9b855,0xf3003cfcc00f3f307d4c0f3f3007983cc1e73ef1e601e7e601e61e601e60f300f37980799e601ef14b45,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000000010000800040000000100008000000040000000110000002220000002a800080000400100000801000008001000008000000002100000008000000101000000100908443a7],
[0x0,0x0,0x0,0x0,0x4000010010000040040000080100000100002000010008000040010000080020000140000000100088440400221000000404000200210000800844001000100002000040002077aa8,0x0,0x0,0x4000010010000840040000100100008500020001000010010000200250000200ac000800004001000008010000080010000080020000101080000080200001010a0000100b08743a7,0x0,0x0,0x0,0x0,0x0,0x0,0xc0002418000600402004080102002080082ce3,0x0,0x140004428000a00402004080102002080082de3,0x2040080408010200402004080102002080082ce3,0x240008448001200402004080102002080082ee3,0x2040080408010200402004080102002080082ce3,0x440010488002200402004080102002080082ce3,0x0,0x0,0x8040000008000200402004080102002080082ce3,0x0,0x8040000008000200402004080102002080082ce3,0x2040080408010200402004080102002080082ce3,0x0,0x0,0x0,0x0,0x600000001800080012000000010000c000080010000080040002800100002000040000200100000801000008001000008000080004100000010000800101002000100508513a7],
[0x0,0x400020001800080012000000028001c00002001000040004000380010000a80004000020080000400100000800100000804008000210010000800100008100600010210840ea7,0x1e9cc007a73001e9cfcc0004bf00012fc0003cc222d11697e000222cfa99e607983ccfa98f344d4bb6,0x0,0x79bcc0798f30079bcfcc0004bf00012fc0003cc2230dd87de0002230c699e607983d0c698f437dc536,0x0,0x0,0x0,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc079807a0517b6,0x0,0x7983cc1e60f307983cfcc0004bf00012fc0003cc222c00097e000222c0799e607983cc07980f3814bb6,0x1e688b1e61e601e60f33cc03ccf3088b3cc0f301e601e7e601e61e601ea45801e7e600f745801e8e98e5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40080408000200402004080104002100082ce3,0x240008448001200402004080104002100082ee3,0x2040080408010200402004080104002100082ce3,0x440010488002200402004080104002100082ce3,0x0,0x0,0x0,0x0,0x0,0x2040080408010200402004080104002100082ce3,0x0,0x0,0x0],
[0x0,0x773597b9b41360b3770d6c73597b9aca773597b9ca6d82cddc3d075940003d77a0500002540be40003d77a050000430e23400007735b2bbd02800079126a50001f36bf73cd061b9aca00007ea8ed7b9acbdcd651dcd74224d859acdc8935639ad173594773594ee6c1de0966615a,0x0,0xf3007980000f300003cfcc00088b00012fc0004bf686a0001e600020461e635283cc1e60f30000001dc6,0x1e9cc007a73001e9cfcc0004bf00012fc0003cc204702397e00020470231e603cc1e7023079c108bb6,0x159fd80000ad0427f600000000acff47e9b0c1f44ff6cfec000567f60acfec005680b9fd80000015f657600000057d95d8000000b266b60000000c29e980000005be7560000000567f600acfec00000002b3fb0002b3fbacfec087e9b66dd45860f4c2becaec0000002becaec0acfec00000002b3fb02b3fb00567f60567f600567f643f4d863a8bb02b3fb002b3fb00000567f602dd5f6a0ac,0x79bcc0798f30079bcfcc0004bf00012fc0003cc205632b2fe00020563231e603cc1f632307d8d271b6,0x0,0x0,0x0,0x3cc3cc3cc0f303cc3cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f301e653bbb6,0x0,0x7983cc1e60f307983cfcc0004bf00012fc0003cc204600097e00020460f31e603cc1e60f300f3448bb6,0x1e688b1e61e601e60f33cc03ccf3088b3cc0f301e601e7e601e61e601ea45801e7e600f745801e8e98e5,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7338 : TreeBound (n := 4) 106 (programCode 0x4429073d6d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8010200408040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7339 : TreeBound (n := 4) 106 (programCode 0x4429073d6e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x82002508040200402004080108002200082ce3,0x0,0x67c128204501,0x2010020008044200402004080102002020082ce3,0x67c128204501,0x408c00102300010233cc00088b000222c000538c459e6097e01e60007991167983cc07987983cc3cb6,0x444108208501,0x10020008004200402004080100001080082ca3,0x444108208501,0x0,0x2010020008040200402004080100802020082ce3,0x408c00102300010233cc00088b000222c000547f4d366f4e601e60007d4e04da730007a730798408b6,0x0,0x0,0xc64188220501,0x10020008004200402004080102002000082ce3,0xc64188220501,0x408c00102300010233cc00088b000222c000538c825f531e601e600097e2d9811800088b0798b65e56,0x102004508040200402004080108002200082ce3,0x0,0x97c128204501,0x0,0x97c128204501,0x804108220501,0x804108208501,0x804108220501,0x804108208501,0x0,0x0,0x60002000180000000000000000500000004000300010000c000400000001000028002000010004000020004000020010000080400000101000000404000000800000001014487fa27,0x0],
[0x0,0x804108220501,0x804108200501,0x804108220501,0x804108220501,0x204008408040200402004080108002200082ce3,0x80008040200402004080108002200082ce3,0x404010408040200402004080108002200082ce3,0x0,0x820025000c0002402004080108002200082ce3,0x24042a5414c2,0x102004500140004402004080108002200082ce3,0x24042a5414c2,0x24282a5414c2,0x24082a5414c2,0x24282a5414c2,0x24082a5414c2,0x24282a5414c2,0x1e9cc007a73000f3f303cc007a73001e6f30053aae351607983ea6007d4c2dd54b0007d4c0003cd2fb6,0x0,0x0,0x24282a5414c2,0x24202a5414c2,0x24282a5414c2,0x24202a5414c2,0x810020008040200402004080108002200082ce3,0x0,0xf33cc03ccf3003ccf34195c888b0001e60000445c4f2b9079801e601e9cc20cbd7001e9cc0000001e56,0xf33cc03ccf3003ccf3000f307983cc1e603cc445c4d3660798204601e9cc204e8b001e9cc0001e61e56,0xf33cc03ccf3003ccf33cc00088b0001e60000445c4d180079801e601e9cc2046f3001e9cc0000001e56,0xf33cc03ccf3003ccf3000f307983cc1e60798445c4d459079f99e601e9cc205257001e9cc0003d008b6,0xf33cc03ccf3003ccf3678dc87b66001e60798445c9b1b9079f99e601e9cc33c7d7001e9cc0003d008b6],
[0xf33cc03ccf3003ccf3007980799e601e61e60445c9c3c2079f99e601e9cc340ffb001e9cc000f348236,0xf307980b66d90f6ccf3003cfcc0084e4003f9903cc03cde601e61e601e9cc001f53000408c001e8e9975,0xf33cc03ccf3003ccf3007980799e601e63cc0445c8ae96079801e601e9cc2fbb4b001e9cc001e611156,0xf33cc03ccf3003ccf34195c87981e61e6f300445c4f2b907983ea601e9cc20cbd7001e9cc00798408b6,0xf33cc03ccf3003ccf303cc007a73001e6f300445c4d36607983ea601e9cc2046f3001e9cc00798408b6,0x0,0x0,0xf33cc03ccf3003ccf31e6f307981e61ed9800445c9b0c607d4c1e601e9cc33c40b001e9cc03cc1e7e56,0xf33cc03ccf3003ccf31e60008118001ed9800445c9aee007d4c1e601e9cc33bc73001e9cc03cc1e7e56,0xf33cc03ccf3003ccf303cc0079bcc01e6f300445c4d45907983ea601e9cc2046f3001e9cc00798408b6,0xf33cc03ccf3003ccf31e60008118001f53000445c89d80088b01e601e9cc2f76f3001e9cc0798b65e56,0x0,0x47c128204501,0x0,0x47c128204501,0x0,0x444108208501,0x400008000004020004000080000040080040000001100000001400000011000000014000200004000a020501020000100000200010280800040a02000100008000102000100079ba8,0x444108208501,0x0,0x0,0x0,0x0,0x0,0x464188220501,0x1000040008000200402004080100002000082ce3,0x464188220501,0x0,0x0,0x0,0x0,0x0],
[0x0,0xf33cc03ccf300798f36879307b66001e60f30445c9cf261273cb6603cfcc343d8b003cfcc03cc1e7e56,0x0,0x0,0x200040000200200002000800002000800002000010002000010020000100020000100020000040008100100220400100001004000204010000804040000040100000040002075ba8,0x0,0x0,0x0,0x0,0x0,0xf33cc03ccf300798f31e60008118001ed9800445c8da400f6cc1e603cfcc3069f3003cfcc0f30799e56,0xf33cc03ccf300798f303cc007980001e7e600445c4d3660f307b6603cfcc2046f3003cfcc0000001e56,0xf33cc03ccf300798f31e60008118001f53000445c89d80102301e603cfcc2f76f3003cfcc0f30799e56,0x2000080008040200402004080108002200082ce3,0x8040200402004080108002200082ce3,0x4000100008040200402004080108002200082ce3,0x8040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7452 : TreeBound (n := 4) 106 (programCode 0x4429073d6f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8020200808040200402004080108002200086ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7453 : TreeBound (n := 4) 106 (programCode 0x4429073d70) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c128204501,0x0,0x10c128204501,0x14c128224501,0x15c108208501,0x14c128224501,0x15c108208501,0x0,0x0,0x22000000040000000040000000100004000300010000c000400000001000028002000010004000020004000020010000080400000101000000404000000800000001014487fa27,0x0,0x2100010c0c2000000210000000810004000000110000000240000001100000001000020001cc0c860600002000080000004020000000040086060200000100200040002027aba8,0x14c128220501,0x80002008010200402004080100402000082ce3,0x14c128220501,0x104108200501,0x0,0x773597b9aca01dd4d85947736826b28001e08ffca01dce536b2f73595dcd66dcd650000165a0bddcd66dcd650000165a0bc773594ee6b283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283b9aca007736826b29dcd73e6b2807736826b287736826b28077368362eaef973d9,0x0,0x1dcd65ee6b281deb3265077368624d4a07778a223425b8e23f2f735947735b1cd6500002540be5dcd66dcd6500007ea8ed495037123ff283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283b9aca0077360b35943b9b059aca077360b3594ee6c166b280ee6c175b778fe4d99,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x420020000010080000000200010400000040003100100000800400020801000020802000010008000040010000080010000080200000100800000401000000201000001005087fca7],
[0x408c00102300011163cc00088b000222c000538c8260461e607980020462d98118001ed98f30799e56,0x0,0x408c00102300011163cc00088b000222c000538c8260461e607980020462d98118001f530f30799e56,0x0,0x10c128204501,0x4000440000009100000004800100011000400000005000000014000000090000000110000001220018000c00060000400000048000600020008800080010001200010000800051ea8,0x10c128204501,0x14c128224501,0x15c108208501,0x14c128224501,0x15c108208501,0x100804028040a00402004080100102200082de3,0x0,0x0,0x0,0x0,0x14c128220501,0x1020044a8052a004020040801004020b4082de3,0x14c128220501,0x104108200501,0x0,0x94c128204501,0x0,0x94c128204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x0,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x210008448040200402004080108002200082ee3,0x2010080408040200402004080108002200082ce3,0x410010488040200402004080108002200082ce3,0x0,0x0,0x24042a5414c2,0x0,0x24042a5414c2,0x24282a5414c2,0x24082a5414c2,0x24282a5414c2,0x24082a5414c2,0x24282a5414c2,0x201000000201000002010000002010000100000100400000101000001001000001000080004800080400000800048000004040002000100008001400000101000000010020f9ba8,0x0,0x0,0x24282a5414c2,0x24202a5414c2,0x24282a5414c2,0x24202a5414c2,0x0,0x0,0x40428040022,0x0,0x40428040022,0x8420284410a2,0x40828040022],
[0x40028040022,0x40828040022,0x40028040022,0x0,0x0,0x0,0x8420284410a2,0x8420284410a2,0x40028040022,0x8420284410a2,0x0,0x0,0x0,0x0,0x1000400008002000010008000010010000000800040004000200010000800020001100021004400684010001810004000040040002000500008401400001001000000010200daea8,0x31085f2432eef7f12ac38be085ddefe2350c39995dd6200468000000eec4902f000eee25d9400773d0759400ef599328000eee25da2e6b283b9ad8e6b283b9b4135941dcd73e6b283b9ad8e6b283ba23d59400775361650003c11ff9400775361650003c11ff94000ef2ec394f3b09,0x400020001000000000000000000000000060003000040002000000020000400020002000010008000040010000080010000080400000101000000404000000410000001011087fda7,0x0,0x800800004004000010008000010010000010000080080000400100000800200001000200000c00ce3662000b8d9840000200400020c010000e36640000080100000040002067aa8,0x0,0x400020001000000000000000000000000040003000100002000000030000000020002000010002000010010000080010000080400000101000000404000000410000001011087f5a7,0x0,0x0,0x4000200010000800000002000100000000200030000200008001000300001000a0002000010002000010010000080010000080400000101000000404000000210000001005087f4a7,0xf33cc03ccf3003cde61e60008118001ed9800445c89d8008118798079bcc2f76f30079bcc0f30799e56,0x400020001000000000000000000000000020003000080002000080030000200020002000010002000010010000080010000080400000101000000404000000410000001011087f5a7,0xf33cc03ccf3003cde61e60008118001f53000445c89d80088b0798079bcc2f76f30079bcc0f30799e56,0x0,0x0,0x0,0x0,0x0],
[0x0,0x1000040000040080402004080108002200082ce3,0x3cfcc01e601e679bf1f81f53000fa98003fd5c1e601e7e601e61e601e9cc0010230007d4c001ee9b345,0x0,0x1004040100840020402004080108002200082ce3,0x20020000080000000080000000200000040003000100002000000030000000020002000010002000010010000080010000080400000101000000404000000410000001011087f5a7,0x0,0x0,0x0,0x0,0x0,0x1000040000040000402004080108002200082ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200100000800400001000800002001000002000010008000040010000080020000100020000080088444200121000400004004000210010000844440000100100000040002077aa8,0x0,0x0,0x0,0x0,0x0,0xf33cc03ccf300799e61e60008118001ed9800445c89d800fa98798079bcc2f76f30079bcc0f30799e56,0x4000200010000800000002000100000000080008000200008000400200002000a0002000010008000040010000080010000080400000041000000104000000210000001005085dca7,0xf33cc03ccf300799e61e60008118001f53000445c89d8010230798079bcc2f76f30079bcc0f30799e56,0x2010080408040200402004080108002200082ce3,0x8040200402004080108002200082ce3,0x4020100808040200402004080108002200086ce3],
[0x8040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_6557 : TreeBound (n := 4) 106 (programCode 0x4429073d) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part010_6558 part010_6559 part010_6560 part010_6561 part010_6562 part010_6563 part010_6564 part010_6565 part010_6678 part010_6679 part010_6888 part010_7097 part010_7338 part010_7339 part010_7452 part010_7453

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7615 : TreeBound (n := 4) 106 (programCode 0x4429073e71) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xc0003008040200080404200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7616 : TreeBound (n := 4) 106 (programCode 0x4429073e72) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x440021008000600100804200100082002080ce3,0x40021008040200000004200100002020080ce3,0x440021008000a00100804200100102004080ce3,0x40021008000200000004200100002000080ce3,0x840021008040200000004200100202008080ce3,0x16c800111600016c83cc0004bf00012fc0003ea600097e1e601e600079a046001e600799e60f308ed6,0x840021008000200000004200100402010080ce3,0x0,0xc00030000008100220000800104004100804e4,0x445800111600016c8000f307983cc1e603cc44583dd346001e7e600079fa77459e60079bcc1e611156,0x0,0xc00030001008040220004800104004100804e4,0x445800111600016c85ba8b088b0001e63cc04458b7534600001e600079fc5d459e60079bcc1e611156,0xc00030002008080220004800104004100804e4,0x445800111600016c85ba8b07980f31e63cc04458b7ccc600001e600079fc5d459e60079bcc1e611156,0xc00030004008100220000800104004100804e4,0x16c800111600016c80003cc3ccf300f303cc3ea600097e001e7e600079bdb3000f30079bcc1e610856,0xc00030008008200220008800104004100805e4,0x0,0xc00030010008400220008800104004100805e4,0x0,0x0,0x0,0x0,0x40021008040200000004200100802020080ce3,0x16c800111600016c83cc0004bf00012fc0003ea600097e1e601e60007a74e600f30007a7307983ffb6,0x0,0x180428080222,0x180428080222,0x180028080222,0x180428080222],
[0x240021000201008100804200101002040080ce3,0x0,0x180428080222,0x0,0x180428080222,0x181028290a62,0x180028080222,0x181028290a62,0x0,0x40021000000200000004200101002040080ce3,0x0,0x0,0x16c800111600016c83cc0004bf00012fc0003ea600097e1e601e60007b67e600798007b660f307cbb6,0x0,0x50c0e7220481,0x424084220481,0x50c0e7220481,0x424084220481,0x6140c6220481,0x424084220481,0x6140c6220481,0x0,0x424084220481,0x40020008004200000004200102002080080ce3,0x424084220481,0xf6cc00f3f3000f6cfcc0004bf00012fc0003ea600097e1e601e600079897e0f31e607987983cc33b6,0xc4418c220501,0x424084220481,0xc4418c220501,0x1116000fa980011163cc0004bf00012fc0003ea600097e1e601e600088b1e612fc00088b07983cd556,0x0,0x40c042208481],
[0x424000200481,0x40c042208481,0x404000200481,0x1020048040200000004020100002020080ce3,0x404000200481,0x2020088040200000004020100002020080ce3,0x0,0x424000200481,0xf4e600f4e6000f4e9cc0004bf00012fc0003ea600097e1e601e60008119e6079800081183cc225fb6,0x424000200481,0xf6cc00f3f3000f6cfcc0004bf00012fc0003ea600097e1e601e60008119e6079800081183cc262bb6,0x2010020408004200402004080102002080082ce3,0x404000200481,0x4020020808020200804004100104002100084ce3,0x1116000fa980011163cc0004bf00012fc0003ea600097e1e601e60008119e6079800081183cc5b3556,0x0,0x50c0e7220481,0x424084220481,0x50c0e7220481,0x424084220481,0x6140c6220481,0x424084220481,0x6140c6220481,0x0,0x424084220481,0x0,0x424084220481,0x0,0xc4418c220501,0x424084220481,0xc4418c220501,0x0],
[0x0,0x3cc0079800089a3000b64001f5300003cc1e7e60f31e9cfcde600f31e600001f530003cc0001e7037c5,0x0,0x0,0xf30f30f303cc0f312fc0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b07983cf3b6,0x4825e60fa980011163cc00088b000222c0004458b660461e601e600097e2d9811800088b07983cde56,0xf33cc0f33cc00f3408c0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b07983ebb56,0x16c8000f301e611163cc0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b07983cd556,0x0,0x0,0xf4e600f4e6000f4e9cc0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b07984c23b6,0x0,0xf6cc00f3f3000f6cfcc0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b0798448bb6,0x4a0be60fa98000f303cc00088b000222c0004458b660461e601e600097e2d9811800088b07983cde56,0x102300102300010233cc0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b0798d4b556,0xf31e60fa9800111822c0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b07983cd556,0x1116000fa980011163cc0004bf00012fc0003ea600097e1e601e600088b1e603cc00088b07983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7729 : TreeBound (n := 4) 106 (programCode 0x4429073e73) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x140005008040200080404200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7730 : TreeBound (n := 4) 106 (programCode 0x4429073e74) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0031008000600180c04200100082002080ce3,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x240021000201008100804200100802020080ce3,0x180828084222,0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x0,0x0,0x0,0x0,0x140031008000a00180c04200100102004080ce3,0x40001008000200000004200100002000080ce3,0x0,0x60c0c6208481,0x24000208481,0x60c0c6208481,0x4000208481,0x414084208481,0x4000208481,0x414084208481,0x0,0x24000208481,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e60012fc1e6003cc00f3079f983ffb6],
[0x24000208481,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e60012fc1e60079800f307a7307cbb6,0x844108208501,0x4000208481,0x844108208501,0x4000208481,0x25f800097e00025f83cc0004bf00012fc0003ea60011161e601e6000f32046001e600f31e63cc219b6,0x40001008000200000004200100402010080ce3,0x0,0x1400050001008040220008800204008100805e4,0x0,0x0,0x1400050001008040220008800204008100805e4,0x0,0x1400050002008080220008800204008100805e4,0x1400050001008100220008800204008100805e4,0x1400050004008100220000800204008100804e4,0x1400050001008040220008800204008100805e4,0x1400050008008200220008800204008100805e4,0x0,0x1400050010008400220008800204008100805e4,0x25f80005b200025f83cc0003cc1e60b665f84458004dd61e63ea6000f33ee3b307980f33cc12fcb006,0x0,0xf307980001e60f307980799e607980000f31e6000001e9cc00f3f3001e9cc00109c800f3f3001e689ba5,0x0,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x240021000201008100804200100802020080ce3,0x180828084222],
[0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x0,0x0,0x0,0x0,0x25f800097e00025f83cc0004bf00012fc0003ea60011161e601e6000f3f4e600f3000f3f31e60f63b6,0x0,0x180428080222,0x180428080222,0x180028080222,0x180428080222,0x240021000201008100804200101002040080ce3,0x0,0x180428080222,0x0,0x180428080222,0x181028290a62,0x180028080222,0x181028290a62,0x0,0x40001000000200000004200101002040080ce3,0x0,0x40001000000200000004200101002040080ce3,0x25f800097e00025f83cc0004bf00012fc0003ea60011161e601e6000f4e7e60079800f4e60f307cbb6,0x40001008000200000004200102002080080ce3,0x0,0x400018000200000004010100002010080ce3],
[0x24000200481,0x800028000200000004010100002010080ce3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x24000200481,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e6000fa99e60798000fa98f307d7fb6,0x24000200481,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e6000fa99e60798000fa98f30814bb6,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x40001008000200000004200104002100080ce3,0x0,0x400018000200000004010100002000080ce3,0x0,0x800028000200000004010100002000080ce3,0x4000200481,0x0,0x4000200481,0x2000088000200000004020100002000080ce3,0x0,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e60010231e603cc00102307984c23b6,0x0,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e60010231e603cc0010230798448bb6,0x844108220501,0x4000200481,0x844108220501],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7859 : TreeBound (n := 4) 106 (programCode 0x4429073e75) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x240009008040200100804200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7860 : TreeBound (n := 4) 106 (programCode 0x4429073e76) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x800400018040200000004010108002200080ce3,0x798079f9807987980b640004bf00012fc0003ea6003ea61e601e600408c1e60f3000408c03cc1e7556,0x800800028040200000004010108002200080ce3,0x7980f379803cc79812fc0004bf00012fc0003ea6003ea61e601e600408c1e60f3000408c03cc1f0d36,0x1000048040200000004020108002200080ce3,0x8040200000004000108002200080ce3,0x2000088040200000004020108002200080ce3,0x0,0x8000000100c0002000004010108002200080ce3,0x2104285414c2,0x800000020140004000004010108002200080ce3,0x2104285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0x7987987981e60798798f3003db3000f3f3003ea6003ea60003ea600408c1e60f3000408c03cc200036,0x0,0x7987987981e60798799e6003d39800f4e6003ea6003ea60003ea600408c1e60f3000408c03cc200036,0x2128285414c2,0x2120285414c2,0x2120285414c2,0x2120285414c2,0x4000108040200000004000108002200080ce3,0x799e60799e600799e9cc0004bf00012fc0003ea6003ea61e601e600408c1e60f3000408c03cc22d936,0x0,0x7240e7204481,0x0,0x7240e7204481,0x24000200481],
[0x24000208481,0x24000200481,0x24000208481,0x0,0x0,0x79f9807b6600079f9bcc0004bf00012fc0003ea6003ea61e601e6003ccf4e600f3003ccf33cc2e3d36,0x0,0x79bcc07b6600079bcfcc0004bf00012fc0003ea6003ea61e601e6003cde7e60079803cde63cc26a536,0x24000220481,0x24000200481,0x24000220481,0x0,0x79bcc0798f30079bcfcc0004bf00012fc0003ea6003ea61e601e600408c1e60f3000408c03cc26a536,0x2010080408040200402004080108002200082ce3,0x8040200000004000108002200080ce3,0x4020100808040200804004100108002200084ce3,0x8040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7909 : TreeBound (n := 4) 106 (programCode 0x4429073e77) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x440011008040200100804200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7910 : TreeBound (n := 4) 106 (programCode 0x4429073e78) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xc804020100c0002180c04010108002200080ce3,0x420018040020000004010108002200080ce3,0xd00404010140004180c04010108002200080ce3,0x400018040000000004010108002200080ce3,0xa00408010240008100804010108002200080ce3,0x400010840000000004010108002200080ce3,0xc00410010440010100804010108002200080ce3,0x400010040000000004010108002200080ce3,0x420010840020000004010108002200080ce3,0xf300f33ea6000fa98f3f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf300f33ea6000fa98f4e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x666a400110000000400004000210000000a000213528000800004002000010000010c26a410000020040000004020000200080400000101000000404000000810000001000487fe27,0xc00410010840010100804010108002200080ce3,0x6a6a400110000000400004000220000000a000213528000800010002000020000010c26a410000020040000004020000200080400000101000000404000000810000001000487fe27,0x0,0xf30079bcc0798f300b640004bf00012fc0003ea6007b661e601e6007d4c1e60f30007d4c0f30799556,0xf6cc003ea6000fa9fd4c0004bf00012fc0003ea6007b661e601e6007d4c1e60f30007d4c0f30799556,0x0,0x20000100080000400100000800200001642a800110000000440000000800220001200032154800080000400000401000001040003214100000010400000041000008000408ffe28,0x2084285414c2,0x0,0x2084285414c2,0x2004100201004140220020804880022004825a4,0x2088285414c2,0x1dd11f9ec4d4a0eea7b135283b9aca00000003b9aca0007736826b28eea7b135283ba9ec4d4a0ee6b2800001ddc4bb28001dcda09cae49a97b9aca00000ee6d04d6501dcd65773597b9aca000003ba23d5940077536165001dd4d85940077536165000eee25d94000ee6d0c8543679,0x2088285414c2,0x4008100200008100220000800880022004025e4,0xf300f33cc03ccf300f3f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0],
[0xf300f33cc03ccf300f4e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x4008100200008100220000800880022004025e4,0xf300f33cc03ccf300fa98004458000fa98003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf300f33cc03ccf301023000408c0010230003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xc810020400c0002180c04020108002200080ce3,0x2504285414c2,0xd01004040140004180c04020108002200080ce3,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0xf307983cc222cf300f3f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf307983cc222cf300f4e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0x0,0xc860021800c0002180c04030108002200080ce3,0x2104285414c2,0xd06004180140004180c04030108002200080ce3,0x2104285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2],
[0xf303cc3cc3cc0f303ccf3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307b2036,0x0,0xf303cc3cc3cc0f303cde6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307b2036,0x2128285414c2,0x2120285414c2,0x2120285414c2,0x2120285414c2,0x0,0xc820020800c0002180c04020108002200080ce3,0x2504285414c2,0xd02004080140004180c04020108002200080ce3,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x0,0x0,0x0,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0x0,0xc864020100c0002180c04030108002200080ce3,0x2104285414c2,0xd06804020140004180c04030108002200080ce3,0x2104285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2],
[0x2108285414c2,0x2128285414c2,0xf307983cc1e60f30798f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf307983cc1e60f30799e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x2128285414c2,0x2120285414c2,0x2120285414c2,0x2120285414c2,0x0,0xc840021000c0002180c04030108002200080ce3,0x2504285414c2,0xd04004100140004180c04030108002200080ce3,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0xf307983cc03ccf30798f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf307983cc03ccf30799e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0x0,0x1e664066360d2d1dcd6c735941ebbd02800000000ee6b281ddc4bb2807b025834b41ebbd02800077359400000861c4680000773684518a1a959aca00000ee6b29dcd68b9aca01dcda09aca000003ba23d5940077536165001dd4d85940077536165000eee25d94000ee6d0c8543e49,0x220428541502,0x432aa19400002800001088004000020210000221940000202100000a0000000202104328010000400040001080080004200080400000101000000104000000410000001001087dda7,0x220428541502,0xf31e603cde600f31e6044583cfcc00f344583ea6007b6600224a6007d4c2d90f30007d4c0f307e72b6],
[0x220828541502,0x222828741502,0x220828541502,0x404010100000810022000080088002200402de4,0xf31e603cde600f31e60f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307e72b6,0x0,0xf31e603cde600f31e61e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307e72b6,0x404010100400804022002080088002200402de4,0x222028741502,0x222028741502,0x222028741502,0x0,0x400041001000004000000408010000010040000000300000010c0000000300008010400800200002100804000008000001008000004010000010040000100080000100100108732a7,0x0,0x0,0x0,0xf30079800007a73003cfcc0000f300003cc1e60f3001e9cc01e600001e601e63cc1e603cc1e61e703cd5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf6cc003ea6000f6cc3cc0004bf00012fc0003ea6007b661e601e60079f99e607980079f98f30799556,0xf6cc003ea6000f6cc3cc0004bf00012fc0003ea6007b661e601e6007d4c1e60798007983db30799556,0x0,0x0,0x0,0x220428541502,0x20010000020010000200100000200100400800010402000014000000100020000110002054080002010100000400100000504000080410000a00040000014100002000108a79fa8],
[0x220428541502,0xf33cc03ccf300f33cc044583d39800f344583ea6007b6600224a6007d4c2d90f30007d4c0f30823eb6,0x220828541502,0x222828741502,0x220828541502,0x4080102000008100220000800880022004035e4,0xf33cc03ccf300f33cc0f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f30823eb6,0x0,0xf33cc03ccf300f33cc1e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f30823eb6,0x4080102004008040220020800880022004035e4,0x222028741502,0x222028741502,0x222028741502,0x0,0xc900024000c0002180c04080108002200080ce3,0x2504285414c2,0xd10004400140004180c04080108002200080ce3,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0xf307983cc03ccf3088bf3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf307983cc03ccf3088ce6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0xf3f3003db3000f3f33cc0004bf00012fc0003ea6007b661e601e6007d4c1e60f30007d4c0f3097f556,0x0],
[0xca00028000c0002180c04100108002200080ce3,0x2504285414c2,0xd20004800140004180c04100108002200080ce3,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0xf307983db3000f6d398f3003db3000f3f3003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x0,0xf307983db3000f6d399e6003d39800f4e6003ea6007b660003ea6007d4c1e60f30007d4c0f307aa6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0xf4e6003d39800f4e63cc0004bf00012fc0003ea6007b661e601e6007d4c1e60f30007d4c0f30b65556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8119 : TreeBound (n := 4) 106 (programCode 0x4429073e79) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x840021008040200000004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8120 : TreeBound (n := 4) 106 (programCode 0x4429073e7a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf379803cde6003d3984195c888b0001e600004458832d7600001e601e9cc20cbd7001e9cc0000001e56,0x3d39803cde6003d3980003cc3cc3cc0f303cc3ea601e7e61e6204601e9cc1e60f3001e9cc0001e61556,0xf379803cde6003d3983cc00088b0001e6000044588119e600001e601e9cc2046f3001e9cc0000001e56,0x8400210001008040220040801080042000209e4,0x3d39803cde6003d3983cc7984bf0000f307983ea601e7e61ed99e601e9cc1e64bf001e9cc0003cfffb6,0x840021000200808022004080108004200040be4,0x3d39803cde6003d3983cc0003cfcc00f300003ea601e7e61e63ea601e9cc1e60f3001e9cc0000001556,0x8400210004008100220000801080042000804e4,0x3d39803cde6003d39800f3003cc1e607a73003ea601e7e60003ea601e9cc1e60f3001e9cc007983ff26,0x3d39803cde6003d39800f3003db3000f3f3003ea601e7e60003ea601e9cc1e60f3001e9cc007983ffb6,0x0,0x481428294a62,0x480428284a62,0x480028200862,0x480428284a62,0x0,0x3d39803cde6003d3980079803f01200f379803ea601e7e61edd6a601e602049cc1e61e601e63cc5e5b6,0x481028290862,0x0,0x481428294a62,0x481028290862,0x480028200862,0x481028290862,0x40001001000040000004200102002080080ce3,0x0,0x40001001000040000004200104002100080ce3,0x0,0x3d39803cde6003d39801e6003d39800f4e6003ea601e7e60003ea601e9cc1e60f3001e9cc00f30b97b6,0x0,0xf300007983cc89a3f30811801ed987980799e7e60f31e9cfcde600f31e9cc001f53000408c001e7037c5,0x8004200101008000220040801080042000000e4],
[0xf381369cde6003cc00409b307981e61e600004458831e4600001e601e9cc204e8b001e9cc0000001e56,0xf3000f6cc001e9cc00f7c6983cc1e607e46984458098f1602636a60981cc20c43f00981cc02635f3286,0xf3098d6cc2634fcc98d7c6983cc1e607e46984458098f1602636a60981cc20c43f00981cc02635f3286,0xf300f33cc03cc3cc03d0c6983cc1e607e46984458098f1602636a60981cc20c43f00981cc02635f3286,0xf30007983cc103323079f981e6798798079a04603cc1ea08c1e60f301e9cc001f53000408c001e7037c5,0xf30079bcc00f33cc079cc6983cc1e607e46984458098f1602636a60981cc20c43f00981cc02635f3286,0x8040201001008040220040801080042000209e4,0x8040201001008040220040801080042000209e4,0x0,0x8080202001008040220040801080042000209e4,0xf300f30798f311160f307983cc798798079a22c1e601ea4581e61e601e9cc001f53000408c001e8e97c5,0x8100204001008800220140801080042005029e4,0x8000200001008000220040801080042000000e4,0x8200208001009000220240801080042009049e4,0x0,0xf300007d4c0089a300079bcc1f53fa98003ea7e60f31e9cfcde600f31e9cc001f53000408c001e7037c5,0x3cc007d4c0079bcc008118004458000fa98003ea601e7e6000204601e9cc1e60f3001e9cc03cc1e7556,0x8400205020008800220140801080042005029e4,0x3cc00f6cc003cfcc00fa98004458000fa98003ea601e7e60003ea601e9cc1e60f3001e9cc03cc225fb6,0x3cc1f56cc07d4fcc00fa98004458000fa98003ea601e7e6007d6a601e9cc222cf3001e9cc03cc225fb6,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x0,0x4220286418e2,0xf300f30798f311160f307983cd116798079a22c1e601ea4581e61e601e9cc001f53000408c001e8e97c5,0x4420286418e2,0x4620286418e2,0x4420286418e2,0x0],
[0xf30000798f3089a3f3088b001e7e67980f31e7e60f31e9cfcde600f31e9cc001f53000408c001e7037c5,0x0,0xf379803cde6003cc003cc0007980001e6000044588119e600001e601e9cc2046f3001e9cc0000001e56,0x0,0x0,0x412028741902,0x420028240862,0x412028741902,0x420028240862,0x420028240862,0x0,0x420028240862,0xf300f31e60f311160f30f303cc1e67980f3222c1e601ea4581e61e601e9cc001f53000408c001e8e97c5,0x3ccf303ccf3003ccf300f3003cfcc00f3f3003ea601e7e60003ea601e9cc1e60f3001e9cc007983ffb6,0x400028240862,0x3cde603cc79803cde603cc003db3000f6cc003ea601e7e60003ea601e9cc1e60f3001e9cc01e6132fb6,0x0,0x0,0x0,0x0,0x3cc00f6cc003cfcc01023000408c0010230003ea601e7e60003ea601e9cc1e60f3001e9cc079840bfb6,0x3cc1f56cc07d4fcc01023000408c0010230003ea601e7e6007d6a601e9cc25f8f3001e9cc079840bfb6,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x8040210040009000220040801080042008049e4,0x4220286418e2,0x3cc1e63cc003cfcc1f623000408c0010230003ea601e7e60003ea601e9cc1e60f3001e9cc079840bfb6,0x4420286418e2,0x4620286418e2],
[0x4420286418e2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8217 : TreeBound (n := 4) 106 (programCode 0x4429073e7b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1040041008000600010084200100082002080ce3,0x44583cc1e600044583cc0004bf00012fc0003ea60020461e601e6001e605b20003cc1e603cc1e61556,0x1040041008000a00020104200100102004080de3,0x1040041008000200000004200100002000080ce3,0x0,0x40c042208481,0x424000208481,0x40c042208481,0x404000208481,0x414084208481,0x404000208481,0x414084208481,0x0,0x424000208481,0x0,0x424000208481,0x0,0x444108208501,0x404000208481,0x444108208501,0x0,0x0,0x0,0x424000200481,0x0,0x404000200481,0x1001040048000200000004020100002000080ce3,0x404000200481,0x1002040088000200000004020100002000080ce3,0x0,0x424000200481],
[0x1e61e9cc01e601e61e9cc0004bf00012fc0003ea600f4e61e601e600f302046001e60f301e9cc2445b6,0x424000200481,0x1e63cfcc00f301e63cfcc0004bf00012fc0003ea600f4e61e601e600f302046001e60f301e9cc2811b6,0x20010000080040000100080000200080040003100100004100400000001000000006200010008200040000000080010000080620000100820000400400000800000001021887fea7,0x404000200481,0x77360b359401dcd82cd6577360b35940ee6c166b280ee6c166b9f3599adcb84b56500773d07594f0481c1d650000077359400002d6e5b3af9aca3b9acdb9af6b417bb9aca000003b9b41359403ba87d5c5e7773594000001deb6dffca7736826b280ee6b2800000ef11e49adf569,0x1e7e63cc079801e7e63cc0004bf00012fc0003ea600f4e61e601e600f302046001e60f301e9cc5b3556,0x1040041008000200000004200100402010080ce3,0x0,0x0,0xf300b64000798f300b640004bf00012fc0003ea6007b661e601e6007983ea6000f307983db30799556,0xf6cc3cc0f3000fa9fd4c0004bf00012fc0003ea6007b661e601e6007983ea6000f307983db30799556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf3f33cc0f3000f3f33cc0004bf00012fc0003ea6007b661e601e6007983ea6000f307983db3097f556,0x0,0xf4e63cc079800f4e63cc0004bf00012fc0003ea6007b661e601e6007983ea6000f307983db30b65556,0x0,0x80028000022,0x80428000022,0x80028000022,0x80428000022,0x1040041000201008040204200100802020080ee3,0x1040041008000000000004200100802020080ce3],
[0x80028000022,0x1040041008000000000004200100802020080ce3,0x80028000022,0x581028294a62,0x80028000022,0x581028294a62,0x0,0x0,0x0,0x0,0x0,0x581428290a62,0x480428290a62,0x480028210862,0x480428290a62,0x1040041000201008040204200100802020080ee3,0x2040021000200808022004080100804020040be4,0x481028290862,0x20400210004008100220000801008040200804e4,0x581428290a62,0x481028290862,0x481028290862,0x481028290862,0x0,0x0,0x0,0x0,0x0,0x80028000022,0x80428000022,0x80028000022,0x80428000022],
[0x1040041000201008040204200101002040080ee3,0x0,0x80028000022,0x0,0x80028000022,0x481028290862,0x80028000022,0x481028290862,0x0,0x1040041000000200000004200101002040080ce3,0x0,0x1040041000000200000004200101002040080ce3,0x0,0x581428290a62,0x480428290a62,0x480028210862,0x480428290a62,0x0,0x20400410002008080220080802010080400413e4,0x481028290862,0x20400410004008100220000802010080400804e4,0x581428290a62,0x481028290862,0x481028290862,0x481028290862,0x0,0x0,0x0,0x0,0x1040041008008200201004200102002080081ce3,0x0,0x40c042208481],
[0x424000200481,0x40c042208481,0x404000200481,0x0,0x404000200481,0x0,0x0,0x424000200481,0x79801e9cc01e679801e9cc0004bf00012fc0003ea63cc1e61e601e63cc0799e607983cc0798f307d7fb6,0x424000200481,0x79803cfcc00f379803cfcc0004bf00012fc0003ea63cc1e61e601e63cc0799e607983cc0798f30814bb6,0x0,0x404000200481,0x0,0x7981e63cc07987981e63cc0004bf00012fc0003ea63cc1e61e601e63cc0799e607983cc0798f30b65556,0x1040041008008200201004200104002100081ce3,0x0,0x0,0x0,0x401010000008000220000808040201000000e4,0x0,0x0,0x0,0x402000001008000020020000020080000004000000010000000202000000208000000000201000000804000008010000008000040002100000008002000101002000100108403a7,0x0,0x0,0x0,0x3cc7980001e603cc7980f30003cc00010230003ea61e61e61e601e61e60f31e603cc1e60f30000001556,0x0,0x0,0x0,0x2002000001008000020020000020080002000010001000040020002100020008400020000201000000804200008010800008020000010100000008200000101200000100308703a7],
[0x3cc7980001e603cc7980f3000408c0010230003ea61e61e61e601e61e60f31e603cc1e60f30000001556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8378 : TreeBound (n := 4) 106 (programCode 0x4429073e7c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x481428294a62,0x481428284a62,0x481428294a62,0x481428284a62,0x20020000080080000100200000200800042830001100000004008000008000400012000214188000000204000040010000100428321419000001004000004000004010000817fe28,0x10400410010008440220088802002080082413e4,0x481428294a62,0x10400410011008440220088802004080102a15e4,0x481428294a62,0x481428290a62,0x481428294a62,0x481428290a62,0x0,0x0,0x0,0x0,0x0,0x480428294a62,0x480428284a62,0x480428284a62,0x480428284a62,0x79f9801e7e60079f980003cc3cc3cc0f303cc3ea603cde60007b6603cc000000f3003cc007987985216,0x8020000020080000100200000200800000004000400080001000100008000100010400004008000014010000200810000100000402008008001400010004000010000200a151ea8,0x480428294a62,0xee7a0eb280ee6ee1aca00ee7a0eb280ee6ee1aca00ee7a0eb28000077359b735b1cd6577359477359b7359b7359b7359477359b823ff2877394daca7922405c13287736826b28000ef5993287735941dd4f723f6f84d6c735941dcd65ee6b45cd6c735941dcd650ee6ba8f3cd1a,0x480428294a62,0x480428290a62,0x480428280a62,0x480428290a62,0x0],
[0x0,0x0,0x0,0x0,0x481428294a62,0x480428284a62,0x480028200862,0x480428284a62,0x0,0x0,0x480028210862,0x0,0x480028210862,0x480028210862,0x480028200862,0x480028210862,0x0,0xf379803cde60079f9803cc007aec801ebb200408c001f5301edb6629c4f301e63cc29c47982d9172136,0x0,0xf379803cde60079f9803cc007a73001e9cc00408c001f5301edb664825e601e67984824f301e60f8936,0x10400410001008040220080802080082000211e4,0x0,0xf300007d88c089f6880799e80461ed9800206dde0f31ea1bbde610231e9cc001f53000408c001e7037c5,0x798007b660079f9800798b643cc0f30f307983ea603cde600f504603cfcc1e62d9003cfcc0001e61556,0x10400400000008040220080802080082000000e4,0x10008400201008040220080802080082000211e4,0x10008400201008040220080802080082000211e4,0x10010400402008040220080802080082000413e4,0x10080400000008040220080802080082000000e4,0x10020400804008040220080802080082000815e4,0x7983cc1e60f6d3983cc1ed983d39800f307983ea603cde600f6ea603cfcc1f53f3003cfcc00f307cbb6,0x7981e61e61e607981e61ed983cfcc00f307983ea603cde600f6ea603cfcc1eda73003cfcc00798b97b6],
[0x0,0x7983cc1e60f307983cc1ed983d39800f307983ea603cde600f6ea603cfcc1f53f3003cfcc00f307cbb6,0xf300f30798f311160f3001e9cc01ed98002082c1e601ea4581e61e601e9cc001f53000408c001e8e97c5,0x8100404020004820220180806080082006030a4,0x10000400000008040220080802080082000000e4,0x1020040804000904022028080208008200a051e4,0x10400410002008080220080802080082000413e4,0x79f9801e7e60079f983cc0003d39800f4e6003ea603cde61e63ea603cfcc1e60f3003cfcc00f307cbb6,0x10400410004008100220000802080082000804e4,0x79f9801e7e60079f9801e6003d3b660f4e6003ea603cde600f6ea603cfcc1f57bf003cfcc00f6d3cbb6,0x79f9801e7e60079f9800f3003db3000f3f3003ea603cde60003ea603cfcc1e60f3003cfcc01e616fbb6,0x0,0x481428294a62,0x480428284a62,0x480028200862,0x480428284a62,0x0,0x0,0x481028290862,0x0,0x481428294a62,0x481028290862,0x480028200862,0x481028290862,0x1040001001000040000004200102002080080ce3,0x79f9801e7e60079f981e60003d398011160003ea603cde61e63ea603cc79ad9079803cc7980f307cbb6,0x1040041001008040201004200104002100081ce3,0x79f9801e7e60079f980f30003d398010230003ea603cde61e63ea603ccf325f83cc03ccf300f307cbb6,0x79f9801e7e60079f9801e6003d39800f4e6003ea603cde60003ea603cfcc1e60f3003cfcc00f307cbb6,0x79f9801e7e60079f983cc0003cc1e612fc0003ea603cde61f531e603cfcc1e64bf003cfcc0003d3cbb6,0x0,0x79800f4e7e60079f98fa98004458000fa98003ea603cde61e63ea603cfcc1e60f3003cfcc0f30814bb6],
[0x798007b660079f98008118004458000fa98003ea603cde6000204603cfcc1e60f3003cfcc0f30799556,0x10400406020008800220180802080082006031e4,0x79800f4e6003d39800fa98004458000fa98003ea603cde60003ea603cfcc1e60f3003cfcc0f30814bb6,0x7983db4e60f6d39800fa98004458000fa98003ea603cde600f6ea603cfcc2d90f3003cfcc0f30814bb6,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x0,0x4220286418e2,0x79c08c0f3001ed9c0a34180044580008118003ea6408de61028d06408fcc2e83f3003cfcc1023812cc6,0x4420286418e2,0x4620286418e2,0x4420286418e2,0x79f9800f4e60079f983cc0003cc0000b640003ea603cde61e601e603cfcc1e60f3003cfcc00f307acc6,0x0,0x0,0x0,0x0,0x79800f4e6003d39801023000408c0010230003ea603cde60003ea603cfcc1e60f3003cfcc0798448bb6,0x7983db4e60f6d39801023000408c0010230003ea603cde600f6ea603cfcc25f8f3003cfcc0798448bb6,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x10080410040009000220080802080082008051e4,0x4220286418e2,0x7983cc1e6003d3983dc23000408c0010230003ea603cde60003ea603cfcc1e60f3003cfcc0798448bb6,0x4420286418e2,0x4620286418e2],
[0x4420286418e2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8507 : TreeBound (n := 4) 106 (programCode 0x4429073e7d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x2000480018040200010084010108002200080ce3,0x2040080108040200100804220108002200080ce3,0x2000880028040200020104010108002200080de3,0x2040080008040200000004200108002200080ce3,0x2001080048040200040204020108002200080ee3,0x2000080008040200000004000108002200080ce3,0x2002080088040200080404020108002200080ce3,0x0,0x20404800100c0002010084210108002200080ce3,0x10428040022,0x2040880020140004020104210108002200080de3,0x10428040022,0x10828040022,0x10828040022,0x10028040022,0x10828040022,0x10028040022,0x0,0x0,0x0,0x10028040022,0xa120285414c2,0xa128285414c2,0xa120285414c2,0x2004080108040200100804020108002200080ce3,0x0,0x2040080188000600180c04230100082002080ce3,0x0,0x2040080188000a00180c04230100102004080ce3,0x2040080008000200000004200100002000080ce3,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e60012fc1e6003cc00f3079f983ffb6],
[0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e6000f32046001e600f31e63cc219b6,0x2040080008000200000004200100402010080ce3,0x0,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e6000f3f4e600f3000f3f31e60f63b6,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e6000f4e7e60079800f4e60f307cbb6,0x2040080008010200000004200102002080080ce3,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e6000fa99e60798000fa98f307d7fb6,0x2040080008010200000004200104002100080ce3,0x1e7e6007b66001e7e9cc0004bf00012fc0003ea60011161e601e60010231e603cc00102307984c23b6,0x0,0x8240a5204481,0x0,0x8240a5204481,0x0,0x824084208481,0x0,0x824084208481,0x0,0x0,0x200001000800004000400008001000010040002100100008000400000001000001004200010000200040000800020100000080420000101000000404000000800000001000c87fe27,0x0,0x0,0x82418c220501,0x0,0x82418c220501,0x0,0x0,0x2040080018000600010084210100082002080ce3,0x0,0x2040080028000a00020104210100102004080de3],
[0x2040080008000200000004200100002000080ce3,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e60012fc1e60079800f307a7307cbb6,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e6000f32046001e600f31e63cc219b6,0x2040080008000200000004200100402010080ce3,0x0,0x0,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e6000f3f4e600f3000f3f31e60f63b6,0x0,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e6000f4e7e60079800f4e60f307cbb6,0x2040080408010200402004280102002080082ce3,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e6000fa99e60798000fa98f30814bb6,0x2040080408010200402004280104002100082ce3,0x1e9cc007a73001e9cfcc0004bf00012fc0003ea60011161e601e60010231e603cc0010230798448bb6,0x2010080408040200402004080108002200082ce3,0x2000080008040200000004000108002200080ce3,0x2020080808040200804004100108002200084ce3,0x2010080408040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8588 : TreeBound (n := 4) 106 (programCode 0x4429073e7e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x800410018040200100804010108002200080ce3,0x1e600097e0007b66000b640004bf00012fc0003ea60f31e61e601e60f33cc1e60f300f33cc03cc1e7556,0x800810028040200100804010108002200080ce3,0x1e60011160003ea60012fc0004bf00012fc0003ea60f31e61e601e60f33cc1e60f300f33cc03cc1e93b6,0x1020048040200000004020108002200080ce3,0x8040200000004000108002200080ce3,0x2020088040200000004020108002200080ce3,0x0,0x8044300100c0002100804030108002200080ce3,0x8104284410c2,0x804830020140004100804030108002200080ce3,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2,0x8108284410c2,0x8128285410c2,0x1e6007b66001e7e600798f3003db3000f3f3003ea60f31e60003ea60f33cc1e60f300f33cc03cc1f86b6,0x0,0x1e6007b66001e7e600799e6003d39800f4e6003ea60f31e60003ea60f33cc1e60f300f33cc03cc1f86b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2,0x4000108040200000004000108002200080ce3,0x1e601e7e601e61e601e9cc0004bf00012fc0003ea60f31e61e601e60f33cc1e60f300f33cc03cc225fb6,0x0,0x7240e7204481,0x0,0x7240e7204481,0x24000200481],
[0x24000208481,0x24000200481,0x24000208481,0x0,0x0,0x1e60799e61e601e6079bcc0004bf00012fc0003ea60f31e61e601e60f300f4e600f30f300f33cc2dc3b6,0x0,0x1e603cde61e601e603cfcc0004bf00012fc0003ea60f31e61e601e60f301e7e600798f301e63cc262bb6,0x24000220481,0x24000200481,0x24000220481,0x0,0x1e603cde600f31e603cfcc0004bf00012fc0003ea60f31e61e601e60f33cc1e60f300f33cc03cc262bb6,0x2010080408040200402004080108002200082ce3,0x8040200000004000108002200080ce3,0x4020100808040200804004100108002200084ce3,0x8040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8637 : TreeBound (n := 4) 106 (programCode 0x4429073e7f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x4000500018040200010084010108002200080ce3,0x0,0x8340e7204481,0x4000100108040200000004000100002020080ce3,0x8340e7204481,0x4000100108000200000004000100002000080ce3,0x824084208481,0x4000100108000200000004000100002000080ce3,0x824084208481,0xf300981cc0798f300b640004bf00012fc0003ea6007b661e601e6007983ea6000f307983db30799556,0x4000100108040200000004000100802020080ce3,0x0,0x0,0x0,0x82418c220501,0x4000100108000200000004000100002000080ce3,0x82418c220501,0x3cc0007980007d4c000b640004bf00012fc0003ea61e61e61e601e61e60f31e603cc1e60f30000001556,0x4000900028040200020104010108002200080de3,0x0,0x83c0e7204481,0x3cc0f303cc3cc3cc12fc0004bf00012fc0003ea60020461e601e6001e605b20003cc1e603cc1e61556,0x83c0e7204481,0x804000200481,0x804000208481,0x804000200481,0x804000208481,0x0,0x0,0x0,0x0],
[0x0,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x4001100048040200040204020108002200080ee3,0x4000100008040200000004000108002200080ce3,0x4002100088040200080404020108002200080ce3,0x0,0x40001000100c0002000004010108002200080ce3,0x8104284410c2,0x4000100020140004000004010108002200080ce3,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2,0x8108284410c2,0x8128285410c2,0x798007b66001ed9800798f3003db3000f3f3003ea63cc1e60003ea63cc3cc1e60f303cc3cc0f307aa6b6,0x0,0x798007b66001ed9800799e6003d39800f4e6003ea63cc1e60003ea63cc3cc1e60f303cc3cc0f307aa6b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2,0x4004100108040200100804020108002200080ce3,0x0,0x40021011000c0002080404230108002200080ce3,0x0,0x4002101100140004080404230108002200080ce3,0x0,0x4004101100240008100804220108002200080ce3],
[0xa20828541502,0x20028040022,0xa20828541502,0x20028040022,0x3cc1e60f31e603cc1e60f3003db3000f3f3003ea601e7e60003ea601e9cc1e60f3001e9cc007983ffb6,0x0,0x7981e61e61e607981e61e6003d39800f4e6003ea603cde60003ea603cfcc1e60f3003cfcc00f307cbb6,0x0,0x8220286410e2,0x20028040022,0x8220286410e2,0x0,0x8240a5204481,0xee6b283b9b059aca0ee6b45cd650773770d6507735b1cd650773d0759400001dcd65ee6b2f735940ee6d04d65ee6b2f73594077359b73594ee6b45cd653b9ca6d65003b9ad8e6b2bb9ca6d65003b9aca0000077359400001dcd6c735940ee729b5940ee6b9f35940ee747fdbffd99,0x8240a5204481,0x0,0x824084208481,0x0,0x824084208481,0x0,0x0,0x0,0x0,0x0,0x82418c220501,0x0,0x82418c220501,0x7980799e601e63cc03cfcc0f30f307983cc01e60f301e63cc07aec801e7e6003d39800f6cc001eed8995,0x0,0x0,0x0,0x0],
[0x0,0x7983cc1e60f307983cc1ed983d39800f307983ea603cde600f6ea603cfcc1f53f3003cfcc00f307cbb6,0xa20828541502,0x20028040022,0xa20828541502,0x20028040022,0xf303cc0f30f30f303cc0f3003db3000f3f3003ea60799e60003ea6079bcc1e60f30079bcc0079932fb6,0x0,0x7983cc1e60f307983cc1e6003d39800f4e6003ea603cde60003ea603cfcc1e60f3003cfcc00f307cbb6,0x4020101802040080804004300108002200084ce3,0x8220286410e2,0x20028040022,0x8220286410e2,0x4010100408040200402004080108002200082ce3,0x4000100008040200000004000108002200080ce3,0x4020100808040200804004100108002200084ce3,0x4020100808040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8750 : TreeBound (n := 4) 106 (programCode 0x4429073e80) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c062204481,0x0,0x10c062204481,0x400018000200000004010100002000080ce3,0x4260000100100000400080000200100000c0002130100000010400000041000000804260010000100040000400020000200080002000100008000400004000800010001000487fe27,0x400018040200000004010100802000080ce3,0x4220000110000000400400000200200000c0002110100000080400000201000000804220010000100040000400020000200080002000100008000400010000800020001000487fe27,0x0,0x0,0x3cc001023000408c7992fc0004bf00012fc0003ea61e61e61e601e61e600f4e600f31e600f37983cf3b6,0x0,0x3cc001023000408c7992fc0004bf00012fc0003ea61e61e61e601e61e601e7e600799e601e67983cf3b6,0x80c163220501,0x4220000110000000400400000200200000c0002110100008000400000201000000804220010000100040000400020000200080422000100010000400040000800020001000487fe27,0x80c163220501,0xc042200481,0x0,0x0,0x8084284410a2,0x0,0x8084284410a2,0x8084284410a2,0x8088284410a2,0x0,0x8088284410a2,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x10c062204481,0x800028040200000004010100002020080ce3,0x10c062204481,0x800028000200000004010100002000080ce3,0xee6b2800003b9ad8e6b281dce536b281dcd73e6b282540be40077536165001dd4d859403b9ca6d65000eee25d9400ee6b280000ee6b2f73597b9aca3b9acdb9acbdcd68b9aca1dcd68b9aca3b9ad173594ee6b45cd650ee6b36e6b36e6b36e6b28ee6b36e6d0c82bfd99,0x0,0x1e60000799e6012fc0000f3001e9cc007980001e60f307981e61e607983cc1e60f303cc1e64d995,0x800028040200000004010100002200080ce3,0x0,0x0,0x0,0x0,0x80c163220501,0x800028000200000004010100002010080ce3,0x80c163220501,0xc042200481,0x3cc001023000408c0012fc0004bf00012fc0003ea61e61e61e601e61e63cc1e60f301e63cc07983cf3b6,0x0,0x40484004101210010004840020010000080000a0000000280000000602400001009040480040001200100004800200010000804000001010000004040000008100000010004877627,0x8004284410a2,0x0,0x8004284410a2,0x8000284410a2,0x8008284410a2,0x8020284410a2,0x8008284410a2,0x8020284410a2,0x3cc03cc0003cc3cc0408c0000f30798000000003cc1e60001e603cc1e9cc001f530007d4c001e703855],
[0x0,0x3cc03cc0003cc3cc0408c0000f30798000000003cc1e60001e603cc1e9cc001f530007d4c001e703855,0x8000284410a2,0x8020284410a2,0x8020284410a2,0x8020284410a2,0x8040200000004000108002200080ce3,0x2000088040200000004020108002200080ce3,0x0,0x0,0x8104284410c2,0x0,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2,0x8108284410c2,0x8128285410c2,0x3cc007a73001e9cc00798f3003db3000f3f3003ea61e61e60003ea61e63cc1e60f301e63cc07983de6b6,0x0,0x3cc007a73001e9cc00799e6003d39800f4e6003ea61e61e60003ea61e63cc1e60f301e63cc07983de6b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2,0x0,0x0,0x8404284410a2,0x0,0x8404284410a2,0x8420284410a2,0x8408284410a2],
[0x8420284410a2,0x8408284410a2,0x8420284410a2,0x3cc1e60f3000408c1e600f3003db3000f3f3003ea61e61e60003ea61e63cc1e60f301e63cc07983cf3b6,0x0,0x3cc1e60f3000408c1e601e6003d39800f4e6003ea61e61e60003ea61e63cc1e60f301e63cc07983cf3b6,0x8420284410a2,0x8420284410a2,0x8420284410a2,0x8420284410a2,0x3cc01e6f301e63cc01e9cc0004bf00012fc0003ea61e61e61e601e61e63cc1e60f301e63cc07984c23b6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc08010200440010100804200108002200080ce3,0x0,0x808020200840020000004200108002200080ce3,0x3cc7980f30079bcc79800f3003db3000f3f3003ea61e61e60003ea61e63cc1e60f301e63cc079840bfb6,0x0,0x3cc7980f300f33cc79801e6003d39800f4e6003ea61e61e60003ea61e63cc1e60f301e63cc0798448bb6,0x0,0x8000200040200000004200108002200080ce3,0x20010000080000001000a00001000400200001000000020002000020008580000000201000000800240008010b00008040000002100000008400000101000000100108403a7,0x8000200040000000004200108002200080ce3,0x3cc03ccf300f33cc03cfcc0004bf00012fc0003ea61e61e61e601e61e63cc1e60f301e63cc0798448bb6,0x10000408040200000004080108002200080ce3,0x8040200000004000108002200080ce3,0x20000808040200000004100108002200080ce3],
[0x8040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_7614 : TreeBound (n := 4) 106 (programCode 0x4429073e) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part010_7615 part010_7616 part010_7729 part010_7730 part010_7859 part010_7860 part010_7909 part010_7910 part010_8119 part010_8120 part010_8217 part010_8378 part010_8507 part010_8588 part010_8637 part010_8750

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8880 : TreeBound (n := 4) 106 (programCode 0x4429073f61) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000600018040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8881 : TreeBound (n := 4) 106 (programCode 0x4429073f62) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1034128204501,0x8020200108040200804004100104002020084ce3,0x1034128204501,0x0,0x134128224501,0x20108000200804004100100002100084ce3,0x134128224501,0x824108220501,0x224148228501,0x100108000200804004100100002100084ce3,0x224148228501,0x200108000200804004100100002100084ce3,0x0,0x0,0x0,0x0,0x824108220501,0x100108000200804004100100002100084ce3,0x824108220501,0x0,0x1024108208501,0x8000200108040200804004100100002100084ce3,0x1024108208501,0x0,0xf379805b20000f4e9cc1e60f307983cc0f3079801e7e60079bcc01e6003cfcc00f3f6cc001ede5995,0x0,0x3ccf3011160001e7e9cc00088b07983cc0f3079801e7e60079bcc01e600f33cc03ccf6cc001ee03f95,0x0,0x799e602046000799e9cc0798f307983cc0f3079801e7e60079bcc01e601e63cc0798f6cc001ede5995,0x0,0x1e61e607b66000f31e9cc0f30f307983cc0f3079801e7e60079bcc01e607983cc1e60f6cc001ede5995],
[0x1e60f3001e9cc0000f307983cc0f3079801e7e60079bcc01e600003cc0000f6cc001ede5995,0x3cfcc00f4e6003cc1e9cc1e60f307983cc0f3079801e7e60079bcc01e60f303cc3cc0f6cc001ede5995,0x0,0x0,0x0,0x1e601e6799e601e601e9cc03ccf307983cc0f3079801e7e60079bcc01e679803cde600f6cc001ede5995,0x1e600097e0007b66000b640004bf00012fc0003ccf3f30799e6000f3f3003ea6000f3f3003cfcc1e7556,0x7980001e61e603cc01e9cc0f30f307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001ede5995,0x0,0x8020200108040200804004100100802020084ce3,0x0,0xf3001e9cc0faa73001e6004bf00012fc7984bf079801e7e60079bcc01e603cc3cc0f30f312fc1ede5995,0xf3000222c00088b0000798f307983cc1e603cc4ce38327c4007983cc007d4e0c90d30007a730798408b6,0xf3001e9cc0faa73001e601023000408cf3088b079801e7e60079bcc01e607983cc1e60f316c81ede5995,0x8000200100000100804004100100002000084ce3,0xf303cc3cc2d90f3001e601e60f30811bcc1f53079801e7e60079bcc01e60f303cc3cc0f8c1301ede5995,0x8000200100000100804004100100002000084ce3,0xf303cc3cc2d90f3001e607981e61ed9f983db3079801e7e60079bcc01e60f303cc3cc0f8c1301ede5995,0x0,0xf300003cc1e60f3001e60f4e6003d39800f3f3079801e7e60079bcc01e7e6003d39800f6cc001ede5995,0x8000200100000000804004100100002000084ce3,0x8000200101000040804004100100002000084ce3,0x0,0xf303cc3cc2d90f3001e67983cc1e688b0798f3079801e7e60079bcc01e60f303cc3cc0f8c1301ede5995,0x0,0x8000200104000100804004100100002000084ce3,0x0,0x0,0x1068528210501,0x1063188210501,0x1068528210501,0x1062108210501],
[0x1070948210501,0x1063188210501,0x1070948210501,0x0,0x1061188210501,0x1063188210501,0x1061188210501,0x0,0x1062108210501,0x0,0x1062108210501,0x0,0x0,0x0,0x0,0xf300003cc1e60f3001e600f30000445800088b079801e7e60079bcc01e600003cc0000f6cc001ede5995,0x0,0x0,0x0,0xf300003cc1e60f3001e607b66001ed98003db3079801e7e60079bcc01e7e6003d39800f6cc001ede5995,0x0,0xf303cc3cc2d90f3001e60f307983d3b660f3f3079801e7e60079bcc01e60f303cc3cc0f6db301ede5995,0x40000000900000002400000009000000008100000100400000101000001001000001400000004020082004000000040200020002002000002008600020000800020002000100f9ba8,0xf30079bcc2046f3001e63cc1e60f381181e6f3079801e7e60079bcc01e63cc03ccf300f708c01eed8995,0x0,0x0,0x0,0x0,0x0,0x8004200108040200804004100102002080084ce3,0x0,0x84002108010600c02004100100401190086ca3],
[0x20108000200804004100104002100084ce3,0x84004108010e00c02004100100201190086ca3,0x100108000200804004100100002100084ce3,0x220008108041200804004100100802100084ce3,0x100108000200804004100100002100084ce3,0x420010108042200804004100100802100084ce3,0xf30079bcc0798f300b640004bf00012fc0003ea60079801e601e60079f99e607980079f98000001556,0x800020108004200804004100104002100084ce3,0x0,0x0,0x0,0x2020080108050200804004100100802100084ce3,0x100108000200804004100100002100084ce3,0x4000100108020200804004100100002100084ce3,0x0,0x8000200108040200804004100104002100084ce3,0x0,0x0,0x0,0x3cc00011160001e7e9cc0000f307983cc0f3079801e7e60079bcc01e600003cc0000f6cc001ede5995,0x0,0x0,0x0,0x1e600007b66000f31e9cc003db307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001ede5995,0xf30079bcc0798f300b640004bf00012fc000408c0079801e603cc007a731e603cc007a730000001556,0x0,0x0,0x0,0x0,0x1e601e6799e601e601e9cc03ccf307983cc0f3079801e7e60079bcc01e679803cde600f6cc001ede5995,0x1e600097e0007b66000b640004bf00012fc000408c4bf0799e603cc4bf0f31e603cc4bf0f303cc1e7556,0x7980001e61e603cc01e9cc0f30f307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001ede5995],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9010 : TreeBound (n := 4) 106 (programCode 0x4429073f63) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000a00028040200804004100108002200084de3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9011 : TreeBound (n := 4) 106 (programCode 0x4429073f64) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x104c128204501,0x1dcd6500000773597b9acbdcd6577359b73597b9acbdcd653b9ad17359400001dcd65ee6b2f73595dcd66dcd65ee6b2f73594ee6b36e6b280ee6ee1aca03b9ae7cd6503b9ca6d6503b9ae7cd6503b9aca0000077359400001dcd6c735940ef59932800ee6b9f35940ef5b77aabfd99,0x104c128204501,0x0,0x14c128224501,0x20808000200804004100100002100084ce3,0x14c128224501,0x844108220501,0x254148228501,0x844108220501,0x254148228501,0x200808000200804004100100002100084ce3,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x1044108208501,0x0,0x14c128224501,0x20808000200804004100100002100084ce3,0x14c128224501,0x844108220501,0x254148228501,0x844108220501,0x254148228501,0x200808000200804004100100002100084ce3,0x0],
[0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x1044108208501,0x0,0x0,0x0,0x3cc1e61116000222c3cc00088b07983cc0f3079801e7e60079bcc01e600f33cc03ccf6cc001ee07c55,0x0,0x0,0x0,0x1e9cc007b66000f6cc3cc0f30f307983cc0f3079801e7e60079bcc01e607983cc1e60f6cc001ede5995,0x1e60f303cc3cc0000f307983cc0f3079801e7e60079bcc01e600003cc0000f6cc001ede5995,0x0,0x0,0x0,0x0,0x1e60f30799e601e63cc3cc03ccf307983cc0f3079801e7e60079bcc01e679803cde600f6cc001efcb995,0x1e60011160003ea60012fc0004bf00012fc0003ccf3f30799e6000f3f3003ea6000f3f3003cfcc1e93b6,0x7983cc1e61e603cc3cc3cc0f30f307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001ede5995,0x3cc001023000408c0012fc0004bf00012fc0003ccf4e60f31e6000f4e6003ea6000f4e6003d3983cf3b6,0x0,0x1048528210501,0x1063188210501,0x1048528210501,0x1042108210501,0x1050948210501,0x1042108210501],
[0x1050948210501,0x8000200808000000804004100100802020084ce3,0x1061188210501,0x1042108210501,0x1061188210501,0x0,0x1042108210501,0x8000200808000000804004100100802020084ce3,0x1042108210501,0x0,0x0,0xf303cc3cc1e60f303cc0004bf00016c80004bf079801e7e60079bcc01e603cc3cc0f30f8b2001ede5995,0x0,0xf303cc3cc1e60f303cc001023000445800088b079801e7e60079bcc01e607983cc1e60f8b2001ede5995,0x8000200800000100804004100100002000084ce3,0xf3000408c26082303cc001e60f308301cc1f53079801e7e60079bcc01e60f303cc3cc0f7d0161eded315,0x8000200800000100804004100100002000084ce3,0xf30007d4c0f4f5303cc007981e61e9d3983db3079801e7e60079bcc01e60f303cc3cc0f312fc1ede5995,0x0,0x0,0x8000200800000000804004100100002000084ce3,0x8000200801000040804004100100002000084ce3,0x0,0x0,0x0,0x8000200804000100804004100100002000084ce3,0x0,0x0,0x1048528210501,0x1063188210501,0x1048528210501,0x1042108210501],
[0x1050948210501,0x1042108210501,0x1050948210501,0x0,0x1061188210501,0x1042108210501,0x1061188210501,0x0,0x1042108210501,0x0,0x1042108210501,0x0,0x0,0x0,0x0,0xf300003cc1e60f303cc000f30000445800088b079801e7e60079bcc01e600003cc0000f6cc001ede5995,0x0,0x0,0x0,0x0,0x0,0xf3001e9cc1eda7303cc00f307983d3b660f3f3079801e7e60079bcc01e60f303cc3cc0f6db301ede5995,0x40000000500000002400000009000000010200000040800000201000000801000001010021801040086034000000040400040000802180004008600010001000020004000200deea8,0xf30079bcc2046f303cc03cc1e60f381181e6f3079801e7e60079bcc01e63cc03ccf300f708c01eed8995,0x0,0x0,0x0,0x0,0x0,0x0,0x14c128220501,0xc64188220501],
[0x14c128220501,0x844108220501,0x254148220501,0x844108220501,0x254148220501,0x0,0x464188220501,0x8000000808000200804004100102002080084ce3,0x464188220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x12fc0004bf1e612fc3cc0f30f303ccb640f3079801e7e60079bcc01e603cc3cc0f30f4e9cc1ede5995,0x20808000200804004100104002000084ce3,0x408c001023798222c3cc0f30f303ce22c0f3079801e7e60079bcc01e607983cc1e60f4ed981ede5995,0x844108220501,0x0,0x844108220501,0x0,0xf300f33cc03ccf3012fc0004bf00012fc00044580079801e607980079f99e607980079f98000001556,0x3cc1e60f4ed983cfcc3cc007a7307b69cc0f3079801e7e60079bcc01e7e6003d39800f8c1301ede5995,0x0,0x1000040808000200804004100100002000084ce3,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0],
[0x14c128220501,0xc64188220501,0x14c128220501,0x844108220501,0x254148220501,0x844108220501,0x254148220501,0x200808000200804004100104002100084ce3,0x464188220501,0x0,0x464188220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x44108220501,0x0,0x14c128204501,0x0,0x14c128204501,0x844108220501,0x254148228501,0x844108220501,0x254148228501,0xf300f33cc03ccf3012fc0004bf00012fc000408c0079801e603cc007a731e603cc007a730000001556,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501],
[0x44108200501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9204 : TreeBound (n := 4) 106 (programCode 0x4429073f65) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8001200048040200804004100108002200084ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9205 : TreeBound (n := 4) 106 (programCode 0x4429073f66) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8000200808040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9206 : TreeBound (n := 4) 106 (programCode 0x4429073f67) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8002200088040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9207 : TreeBound (n := 4) 106 (programCode 0x4429073f68) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80403008040200804004100108002200084ce3,0x0,0x402021008000600804004100100082002084ce3,0x4020021008060200804004100104002020084ce3,0x402021008000a00804004100100102004084ce3,0x21008000200804004100100002100084ce3,0x804021008020200804004100100202008084ce3,0x21008000200804004100100002100084ce3,0x804021008020200804004100100402010084ce3,0x0,0x4020021008040200804004100100802020084ce3,0x0,0x0,0x0,0x0,0x0,0x21008000200804004100104002100084ce3,0x0,0x100805008040200804004100108002200084de3,0x0,0x80501008000600804004100100082002084ce3,0x3cc1e607987983cc0000f307983cc0f3079801e7e60079bcc01e600003d39800f30f301ede5995,0x100901008000a00804004100100102004084de3,0x101008000200804004100100002100084ce3,0x4020101008020200804004100100202008084ce3,0x101008000200804004100100002100084ce3,0x4020101008020200804004100100402010084ce3,0x0,0x0,0x0,0x0],
[0x0,0x4020101008020200804004100102002080084ce3,0x0,0x101008000200804004100104002100084ce3,0x0,0x201009008040200804004100108002200084ee3,0x101008040200804004100108002200084ce3,0x402011008040200804004100108002200084ce3,0x201008040200804004100108002200084ce3,0x804021008040200804004100108002200084ce3,0x0,0x4022100100c0002804004100108002200084ce3,0x0,0x402210020140004804004100108002200084ce3,0x0,0x410020040022,0x410822140442,0x410020040022,0x410822140442,0x410020040022,0x3cc079bcc01e63cc0798f3003db3000f3f3003cfcc1e60f3003cfcc1e9cc1e60f3001e9cc007983ffb6,0x0,0x3cc079bcc01e63cc0799e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x2010280402040080804004100108002200086ce3,0x412028741902,0x410020040022,0x412028741902,0x0,0x1008041008000600804004100100082002085ce3,0x2b3fb0159fd80acfec0567f60159fd80acfec00ad0173fb0000acfec0567f600ad0173fb0159fd80000000567f602b3fb0159fd800159fdd67f60206fc4159fd80acfec0567f600567f60acfec0002b3fdb3fb0000acff167f60002b3fb2b3fb0002b3fdb3fb0002b3fb2b3fb0002b3fb00000000567f60000000159fdab3fb0002b3fb159fd80015b00fe20000159fd959fd80015b040949f50634ab,0x1008041008000a00804004100100102004085de3,0x0],
[0x1008041008020200804004100100202008085ce3,0x0,0x1008041008020200804004100100402010085ce3,0x0,0x0,0x0,0x0,0x0,0x1008041008008200804004100102002080085ce3,0x0,0x1008041008008200804004100104002100085ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x410020040022,0x410822140442,0x410020040022,0x410822140442,0x410020040022,0x7980799e601e67980798f3003db3000f3f3003db301e63cc003db301e9cc1e60f3001e9cc007983ffb6,0x0,0x7980799e601e67980799e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x412028741902,0x410020040022,0x412028741902,0x0,0x20100800100c0002804004100108002200086ce3,0x10420040022],
[0x2010080020140004804004100108002200086de3,0x10420040022,0x10020040022,0x10820040022,0x10020040022,0x10820040022,0x10020040022,0x0,0x0,0x0,0x10020040022,0x212020140022,0x10020040022,0x212020140022,0x0,0x48241300100c0002804004100108002200084ce3,0x8104284410c2,0x4824130020140004804004100108002200084ce3,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2,0x8108284410c2,0x8128285410c2,0x1e6007b66001e7e600798f3003db3000f3f3003ea60f30798003ea60f33cc1e60f300f33cc03cc1f86b6,0x0,0x1e6007b66001e7e600799e6003d39800f4e6003ea60f30798003ea60f33cc1e60f300f33cc03cc1f86b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2,0x4020101008040200804004100108002200084ce3],
[0x0,0x0,0x8104284410c2,0x0,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2,0x8108284410c2,0x8128285410c2,0x3cc007a73001e9cc00798f3003db3000f3f300408c1e60f3000408c1e63cc1e60f301e63cc07983de6b6,0x0,0x3cc007a73001e9cc00799e6003d39800f4e600408c1e60f3000408c1e63cc1e60f301e63cc07983de6b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9352 : TreeBound (n := 4) 106 (programCode 0x4429073f69) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8004200108040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9353 : TreeBound (n := 4) 106 (programCode 0x4429073f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80022010800c0002804004100108002200084ce3,0x0,0x1079928204501,0x8020201804044020804004100104002020084ce3,0x1079928204501,0x0,0x1041108208501,0x8020201804040020804004100104002100084ce3,0x1041108208501,0x0,0x1063188210501,0xf30079bcc01e6f3001e600f307983cc1e603cc4bf44f27c40001e60f4e63ce0c90d301e60f3001e61e56,0x1063188210501,0x0,0x0,0x0,0x8020201804040020804004100104002100084ce3,0x0,0x8002201080140004804004100108002200084ce3,0x0,0x1012528204501,0x0,0x1012528204501,0x0,0x1002108208501,0x0,0x1002108208501,0x0,0x1002108210501,0x1002108200501,0x1002108210501],
[0x0,0x0,0x0,0x0,0x0,0x8004201100240008804004100108002200084ce3,0x8000201000040100804004100108002200084ce3,0x8004201100440010804004100108002200084ce3,0x0,0x820030800c0000804004100108002200084ce3,0x0,0x102005080140000804004100108002200084ce3,0x0,0x220822140442,0x220822140442,0x220822140442,0x220822140442,0x220822140442,0x420822140442,0x0,0x420822140442,0x0,0x82082a541502,0x220822140442,0x82082a541502,0x8020201800840020804004100108002200084ce3,0xf30079bcc01e6f3001e63cc007a73001e6f3004ce3813a2c0003cfcc1e9cc2046f3001e9cc00798408b6,0x0,0x1059128204501,0x1dcd6500000773597b9acbdcd65eee2650759401dcf41d65ee6b281dcd65000007736826b2803b9ca6d6503b9aca773597b9bb86b36e6b280ee6ee1aca03b9ae7cd6503b9ca6d6503b9ae7cd6503b9aca0000077359400001dcd6c735940ef59932800ee6b9f35940ef5b77aabfd99,0x1059128204501,0x0],
[0x1041108208501,0x0,0x1041108208501,0x0,0x1061188210501,0x8000200001000040804004100100002000084ce3,0x1061188210501,0xf30079bcc2046f3081183cc1e60f381181e6f3079801e7e60079bcc01e63cc03ccf300f708c01eed8995,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x799e60799e600799e61e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x109c87981e61e607981e63cc0079f9800f4e6004d5d05027e6003d3983cfcc2139f3003cfcc00f307d426,0xf31e603cde600f31e61e6003d39800f4e6003d3983cc000003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x3cc1e63cc1e603cc1e61e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x7736f9a0bc0ee6b2800007736826b280ee6ee1aca00ee6b28007a00db0e82f00000ee6b2f73594ee6b280000ee6b280ee6c166b36e6b283b9ae7cd6503b9bb86b283b9ae7cd6503b9ae7cd6503ba23d5940077536165000eee25d940077536165000eee25d94000eee44218ee719,0x7981e61e61e607981e61e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x1e601e7e601e61e601e61e6003d39800f4e6003d3992fc798003d3992ffcc1e60f3012ffcc04bf29f7b6,0x7981e61e61e607981e61e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x3cc01e6f301e63cc01e61e6003d39800f4e6003d39a22cf30003d39a22fcc1e60f30222fcc088b53bbb6,0x0,0x1012128204501,0x0],
[0x1012128204501,0x0,0x1002108208501,0x0,0x1002108208501,0x0,0x1002108210501,0x1002108200501,0x1002108210501,0x0,0x0,0x0,0x0,0x0,0x0,0xf4e6005b998016e6603ea6000fa985b20f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x3cde60111d9802616607b66001ed985b20f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x7d4c00213900084e400f4e6003d3985b20f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x222028741502,0x8220286410e2,0x222028741502,0xc2202c6418e2,0x4220286418e2,0x0,0x4220286418e2,0x0,0x8220286410e2,0x8220286410e2,0x8220286410e2,0x8000201004040100804004100108002200084ce3],
[0x0,0x0,0x0,0x0,0x0,0x1024ed983cc1e6001e7e6f30004458001f53000408c9f7cbf01e63cc079bcc27def30079bcc07984c27a6,0x222028741502,0x8220286410e2,0x222028741502,0xc2202c6418e2,0x4220286418e2,0xf300003cde60079f980001e600007983cc0f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x4220286418e2,0x1ed980001e6001e7e6f30004458001f53000408c9f7bcc01e63cc0003cc25f8f300003cc0000001946,0x8220286410e2,0x8220286410e2,0x8220286410e2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9498 : TreeBound (n := 4) 106 (programCode 0x4429073f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1024128204501,0x159fd800159fdd67f6000567f759fd8000acff167f600005680b9fd8000567fb67f600005680b9fd80000000567f602b3fb0159fd80acfec0567f60206fc4159fd80acfec0567f600567f60acfec0002b3fdb3fb0000acff167f60002b3fb2b3fb0002b3fdb3fb0002b3fb2b3fb0002b3fb00000000567f60000000159fdab3fb0002b3fb159fd80015b00fe20000159fd959fd80015b040949f50634ab,0x1024128204501,0x0,0x124128224501,0x7983cc1e603cc3cfcc0000f300003cc0f3079801e7e60079bcc01e600003cc0000f4e6001eed8995,0x124128224501,0x824108220501,0x224148228501,0x0,0x224148228501,0x8200208000200804004100100002100085ce3,0x0,0x0,0x0,0x0,0x824108220501,0x8000208000200804004100100002100085ce3,0x824108220501,0x0,0x1024108208501,0x0,0xf30079bcc01e6f3003cc003cc1e616c80004bf079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0xf30079bcc01e6f3003cc0000000f379800f3f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0xf30079bcc01e6f3003cc00f30798445800088b079801e7e60079bcc01e63cc03ccf300f4e6001eefac55,0xf30079bcc01e6f3003cc000000f307981e60f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0xf30079bcc01e6f3003cc01e60f308118001f53079801e7e60079bcc01e63cc03ccf300f4e6001eee0315,0xf30079bcc01e6f3003cc3cc1e60f37981e60f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0xf30079bcc01e6f3003cc07983cc1ed98003db3079801e7e60079bcc01e63cc03ccf300f4e6001eef6f95,0x0,0xf30079bcc01e6f3003cc0f307983d39800f3f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995],
[0x40000080100000020400000a010000002001000001004000001010000010010000014000000040500828040000000405000280001020000004082a0001000a00001002800140f9ba8,0xf30079bcc01e6f3003cc3cc1e60f379801e6f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0x0,0x0,0x0,0xf30079bcc01e6f3003cde60f307987980f30f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0x0,0x1024108208501,0x0,0x0,0x0,0x3d39800f4e6001e9cfcc00088b07983cc0f3079801e7e60079bcc01e600f33cc03ccf6cc001eefac55,0x0,0x79f9801e7e60079bcfcc0798f307983cc0f3079801e7e60079bcc01e601e63cc0798f6cc001f2a4995,0x0,0x1e67980799e600f33cfcc0f30f307983cc0f3079801e7e60079bcc01e607983cc1e60f6cc001eed8995,0x7980001e6f3003cfcc0000f307983cc0f3079801e7e60079bcc01e600003cc0000f6cc001eed8995,0x0,0x0,0x0,0x0,0x0,0x0,0x7980799e601e63cc03cfcc0f30f307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001eed8995,0x0,0x0,0x1020528210501,0x1023188210501,0x1020528210501,0x1022108210501,0x1020948210501,0x1023188210501],
[0x1020948210501,0x8008200208000000804004100100802020085ce3,0x1021188210501,0x1023188210501,0x1021188210501,0x0,0x1022108210501,0x8008200208000000804004100100802020085ce3,0x1022108210501,0x0,0x0,0x1020528218501,0x1dcd6500ee729b5940773770d6505968a6359400ee88f56500ee6b280077359b735b1cd651dcd68b9acaee6b2f73597b9aca77359b735b1d15a476a082638868f567cb7d29240bfb9acdb9ad8eaa7c76bdd11eacdc120082a6d1bf996e29b0b45cd68f5476bdcd65003b9acc437baa,0x1020528218501,0x1022108210501,0x1020948210501,0x8008200201008100804004100101002040085ce3,0x1020948210501,0x0,0x0,0x8008200200000040804004100100002040085ce3,0x8008200201008040804004100101002040085ce3,0x0,0x1022108210501,0x0,0x1022108210501,0x0,0x0,0x1020528210501,0x1023188210501,0x1020528210501,0x1022108210501],
[0x1020948210501,0x1023188210501,0x1020948210501,0x0,0x1021188210501,0x1023188210501,0x1021188210501,0x0,0x1022108210501,0x0,0x1022108210501,0x0,0x0,0x0,0x0,0xf30079bcc01e6f3003cc00f30000445800088b079801e7e60079bcc01e600003cc0000f6cc001eed8995,0x0,0x0,0x400001001000004004000008010000010002000100008008000010021000c000600020000020080000080100000200200000800200001000800004040000008108000010324873227,0x0,0x0,0xf30079bcc01e6f3003cc0f307983d3b660f3f3079801e7e60079bcc01e60f303cc3cc0f6db301eed8995,0x40000080100000600400001201000002000200000040800000201000000801000001020021a010900868340000000408000400008021a0004008680010001000020004000200deea8,0xf30079bcc01e6f3003cc3cc1e60f381181e6f3079801e7e60079bcc01e63cc03ccf300f708c01eed8995,0x0,0x0,0x0,0x0,0x0,0x0,0x124128220501,0x424188220501],
[0x124128220501,0x824108220501,0x224148220501,0xc24188220501,0x224148220501,0x0,0x424188220501,0x8008040208008200804004100102002080085ce3,0x424188220501,0x0,0x824108220501,0xc24188220501,0x824108220501,0x0,0x0,0x12416822c501,0x3b9acbdcd65ee6b29dcd657735940000773595dcd65773d0759400001dcd6500000773595dcd66dcd6500000773594ee6b36e6b280ee6ee1aca03b9ae7cd6503b9ca6d6503b9ae7cd6503b9aca0000077359400001dcd65000000ef59932800ee6b2800000ef62eb03ffd99,0x12416822c501,0x0,0x0,0x0,0x0,0x10000000040000000080100000100400000001000080004000200010000600020000020080000080100000200200000800000001000000004040000008100000010324873227,0x3cc7980f31e603cc3cfcc007a7307983cc0f3079801e7e60079bcc01e7e6003d39800f6db301eed8995,0x0,0x1008040208000200804004100100002000085ce3,0x0,0x0,0x8000208000200804004100100002000085ce3,0x0,0x0,0x0],
[0x124128220501,0x424188220501,0x124128220501,0x824108220501,0x224148220501,0xc24188220501,0x224148220501,0x8200208000200804004100104002100085ce3,0x424188220501,0x0,0x424188220501,0x0,0x824108220501,0xc24188220501,0x824108220501,0x0,0x0,0x0,0x0,0x3d39800f4e6001e9cfcc0000f307983cc0f3079801e7e60079bcc01e600003cc0000f6cc001eed8995,0x2200000004e000000220000000240004000000110000000240000001100000001200020001400ce006200020000000840002000000104000e0062000100002000000400027aba8,0x79f9801e7e60079bcfcc00102307983cc0f3079801e7e60079bcc01e6f3003cfcc00f6cc001eee0315,0x0,0x1e67980799e600f33cfcc003db307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001eef6f95,0x1f34a003ea6000f4e63cc00088b00012fc0004c1e0aec801e6000f3001e61ebb5cc0000f30000001dc6,0x0,0x0,0x0,0x0,0x0,0x0,0x7980799e601e63cc03cfcc0f30f307983cc0f3079801e7e60079bcc01e7e6003d39800f6cc001eed8995],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9691 : TreeBound (n := 4) 106 (programCode 0x4429073f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x8000601010080402804004100100082002084ce3,0x80042011000c0402804004100104802020084ce3,0x8000a01020080802804004100100102004084de3,0x80202010000c0002804004100108002100084ce3,0x80012010000a0002804004100100202008084ee3,0x80202010000c0002804004100104002100084ce3,0x80022010000a0002804004100100402010084ce3,0x80006010100c0402804004100108002002084ce3,0x8004201100080402804004100100802020084ce3,0x80002010000a0002804004100100402000084ce3,0x8008201200080402804004100101002040085ce3,0x0,0x0,0x0,0x80202010000c0002804004100104002100084ce3,0x0,0x0,0x8024201010400420804004100100082002084ce3,0x1dcd6500000773597b9acbdcd65ef599a9b59403b9ca6d65ee6b28000000000000000ee6b280773770d65ee6b280ee6b2f736826b36e6b280ee6ee1aca03b9ae7cd6503b9ca6d6503b9ae7cd6503b9aca0000077359400001dcd6c735940ef59932800ee6b9f35940ef5b77aabfd99,0x8024201020400820804004100100102004084ce3,0x0,0x8004201000820020804004100100202008084ce3,0x0,0x8004201000820020804004100100402010084ce3,0x0,0x0,0x1dcd668904ab63597b9acbdcd65000007735940861e23565ee6b34482581c128ffb9ae7cd6500003b9aca0000000000010c390435a2e6b283b9b059aca0ee6b639aca1dcd73e6b280ee6d04d6503ba712251f877536165001dcd65000001dd11eaca0077359400000eea741ae82629,0x8004201000000020804004100101002040084ce3,0x0,0x0],
[0x0,0x8004201000840020804004100104002100084ce3,0x0,0x0,0x8000601010100404804004100100082002084ce3,0x8020201800140804804004100104002020084ce3,0x8000a01020100804804004100100102004084de3,0x0,0x8001201000120004804004100100202008084ee3,0x8000201000140004804004100100002100084ce3,0x8002201000120004804004100100402010084ce3,0x0,0x8004201100100804804004100100802020084ce3,0x8002201000120004804004100100402010084ce3,0x8008201200100804804004100101002040085de3,0x8000201000140004804004100100002200084ce3,0x0,0x0,0x8020201000140004804004100104002100084ce3,0x0,0x0,0xf30000b641e60f307987983cc1e60f3097e0f3079801e7e60079bcc01e6003cfcc00f3f3003cdede5995,0x0,0xf3000222c1e60f30799e60f307983cc20460f3079801e7e60079bcc01e600f33cc03ccf300799ee07c55,0x0,0x0,0x0,0x0,0x0,0x0,0xf300003cc1e60f3079800000000000001e60f3079801e7e60079bcc01e600003cc0000f300001ede5995,0xf300003cc1e60f3079800000000000001e60f3079801e7e60079bcc01e63cc03ccf300f31e601ede5995],
[0x0,0x0,0x0,0x0,0x0,0x8020201000240008804004100108002200084ce3,0x0,0x0,0x0,0x0,0x0,0x220822140442,0x220822140442,0x220822140442,0x220822140442,0x220822140442,0x420822140442,0xf300003cc1e607a0118001e600f37981e60f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x420822140442,0x0,0x82082a541502,0x220822140442,0x82082a541502,0x8020201000440010804004100108002200084ce3,0x0,0x0,0x0,0x0,0x0,0x220822140442,0x220822140442,0x220822140442],
[0x220822140442,0x220822140442,0x420822140442,0x0,0x420822140442,0x0,0x82082a541502,0x220822140442,0x82082a541502,0x8004201000840020804004100108002200084ce3,0x400020001000080004000000010000800040003000100001000000020000000010002000010008000040008000080020000080400000101000000404000000410000001009087fda7,0x0,0x8008201011000440804004100100082002085ce3,0x4000010010000040040000080100008600020001000080080000100004000200600020000020080000080100000200200000800200001000800004030000008001000010324873227,0x8008201021000840804004100100102004085de3,0x0,0x8008201001020040804004100100202008085ce3,0xf30079bcc01e6f3081183cc1e60f379801e6f3079801e7e60079bcc01e63cc03ccf300f4e6001eed8995,0x8008201001020040804004100100402010085ce3,0x0,0x8008201201008040804004100100802020085ce3,0x8008201201008040804004100101002040085ce3,0x8008201201008040804004100101002040085ce3,0xf30079bcc01e6f3081183cc1e60f381181e6f3079801e7e60079bcc01e63cc03ccf300f708c01eed8995,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x79bcc0798f30079bcc1e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x109c87981e60f307983cc3cc0079f9800f4e6004d5d05027e6003d3983cfcc2139f3003cfcc00f307d426,0xf33cc03ccf300f33cc1e6003d39800f4e6003d3983cc000003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x3cc3cc3cc0f303cc3cc1e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x20021400080080000080000000200010042803000100001000000020000020010002000010008000040008000080020000080400000101000000404000000410000001009087fda7,0x7983cc1e60f307983cc1e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x1e603cde600f31e603cc1e6003d39800f4e6003d3992fc798003d3992ffcc1e60f3012ffcc04bf262bb6,0x7983cc1e60f307983cc1e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x3cc03ccf300f33cc03cc1e6003d39800f4e6003d39a22cf30003d39a22fcc1e60f30222fcc088b448bb6,0x0,0x80403012040080804004100108002200084ce3,0x8004021002040080804004100108002200084ce3,0x100805022040080804004100108002200084de3,0x8020101002040080804004100108002200084ce3,0x201009042040080804004100108002200084ee3,0x4020101802040080804004100108002200084ce3,0x402011082040080804004100108002200084ce3,0x4080102000008040200000000080002000000e4,0x804021102040080804004100108002200084ce3,0x0,0x0,0x0,0x0,0x1e603cde600f31e603cc007983d39800f307983d3992fc7984c2d3992ffcc231ff3012ffcc04bf262bb6,0x4020101802040080804004100108002200084ce3,0x3cc03ccf300f33cc03cc007983d39800f307983d39a22cf3088ed39a22fcc26ebf30222fcc088b448bb6,0x0,0x12fc0006a51e616c879bea6000fa985b5db3079801e7e60079bcc01e9cc003db3000f6cc001ede5995],
[0x0,0x408c00120979825f9e67b66001ed985b9a73079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x0,0x222028741502,0x8220286410e2,0x222028741502,0xc2202c6418e2,0x4220286418e2,0x0,0x4220286418e2,0x0,0x8220286410e2,0x8220286410e2,0x8220286410e2,0x0,0x80403014040100804004100108002200084ce3,0x0,0x100805024040100804004100108002200084de3,0x0,0x20020040022,0x220020040022,0x20020040022,0x220020040022,0x20020040022,0x420020040022,0x0,0x420020040022,0x0,0x8220286410e2,0x20020040022,0x8220286410e2],
[0x0,0x0,0x0,0x0,0x0,0x7983cc2046f30811bdb31e603cc7984bf0f3079801e7e60079bcc01e9cc003db3000f6cc001eded315,0x222028741502,0x8220286410e2,0x222028741502,0xc2202c6418e2,0x4220286418e2,0xf300003cde6007a0118001e600007983cc0f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x4220286418e2,0x0,0x8220286410e2,0x8220286410e2,0x8220286410e2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9900 : TreeBound (n := 4) 106 (programCode 0x4429073f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8010200408040200804004100108002200086ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9901 : TreeBound (n := 4) 106 (programCode 0x4429073f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x82002988040200804004100108002200084ce3,0x0,0x67c128204501,0x4020020808060200804004100104002020084ce3,0x67c128204501,0x4020020808020200804004100104002100084ce3,0x444108208501,0x4020020808020200804004100104002100084ce3,0x444108208501,0x0,0x4020020808040200804004100100802020084ce3,0x0,0x0,0x0,0xc64188220501,0x4020020808020200804004100104002100084ce3,0xc64188220501,0x0,0x102004988040200804004100108002200084ce3,0x0,0x97c128204501,0x1f5300088b0001f533cc0004bf00012fc0003cc1e625f91160001e625f85b20003cc25f83cc1e61556,0x97c128204501,0x804108220501,0x804108208501,0x804108220501,0x804108208501,0x0,0x0,0x0,0x0],
[0x0,0x804108220501,0x804108200501,0x804108220501,0x804108220501,0x204008908040200804004100108002200084ce3,0x100008040200804004100108002200084ce3,0x404010908040200804004100108002200084ce3,0x1e60f307983cc1e60f307983cc0f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x820020808040200804004100108002200084ce3,0x0,0xf31e603f990f6d7826005b200016c80004bf079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x1e61e607c590f6d782601116000445800088b079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x8100204001004000200000200080002000000a4,0x440826340c82,0x440024040022,0x440826340c82,0x440024040022,0x3ccf303ccf3003ccf300f3003db3000f3f3003cfcc1e60f3003cfcc1e9cc1e60f3001e9cc007983ffb6,0x0,0x3ccf303ccf3003ccf301e6003d39800f4e6003cfcc3cc1e6003cfcc3cfcc1e60f3003cfcc00f307cbb6,0x8100204001008800220140205080142005029e4,0x44202c6418e2,0x3ccf303ccf3003ccf300f3003cfcc00f3f3003cfcc1e60f3003cfcc1e9cc1e60f3001e9cc007983ffb6,0x44202c6418e2,0x0,0x47c128204501,0x77359400001dcd65ee6b28ee7a0eb280ee6ee1aca00ee7a0eb2f7359400001dcd6503b9b413595dcd66dcd65ee6b2f73594ee6b36e6b280ee6ee1aca03b9ae7cd6503b9ca6d6503b9ae7cd6503b9aca0000077359400001dcd6c735940ef59932800ee6b9f35940ef5b77aabfd99,0x47c128204501,0x0],
[0x444108208501,0x0,0x444108208501,0x0,0x0,0x0,0x0,0x0,0x464188220501,0x1000040008000200804004100100002000084ce3,0x464188220501,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x440826340c82,0x440024040022,0x440826340c82,0x440024040022,0x798f301e6f300798f300f3003db3000f3f3003d39897e3cc003d398981cc1e60f300981cc0079932fb6,0x0,0x798f301e6f300798f301e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x44202c6418e2,0x1e60f307981e61e607987980f30f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x44202c6418e2,0x2000080008040200804004100108002200084ce3,0x8040200804004100108002200084ce3,0x4000100008040200804004100108002200084ce3],
[0x8040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9998 : TreeBound (n := 4) 106 (programCode 0x4429073f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8020200808040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_9999 : TreeBound (n := 4) 106 (programCode 0x4429073f70) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c128204501,0x84003008040600804004100104802020084ce3,0x10c128204501,0x14c128224501,0x15c108208501,0x14c128224501,0x15c108208501,0x0,0x84003008040200804004100100802020084ce3,0x0,0x0,0x0,0x14c128220501,0x80002008020200804004100100402000084ce3,0x14c128220501,0x104108200501,0x0,0xf6cc003ea6003d76bd4c0002d90000b640f3079801e7e60079bcc01e6003cfcc00f3f3003cdede5995,0x1e61e6003d3983cc0000f307983cc0f3079801e7e60079bcc01e600003d39800f30f301ede5995,0x1e9cc007b66003d7736cc00088b000222c0f3079801e7e60079bcc01e600f33cc03ccf300799ede5995,0x1e6003d3983cc0000f300003cc0f3079801e7e60079bcc01e600003cc0000f4e6001ede5995,0x0,0x0,0x0,0x0,0x7983cc1e61e6003d7643cc1e60f307983cc0f3079801e7e60079bcc01e60f303cc3cc0f30f301ede5995,0x0,0x0,0x0,0x0],
[0x1116000fa980011163cc0004bf00012fc0003cc3db38119e60003db38119e607980f381183ce413556,0x0,0x0,0x0,0x10c128204501,0x120004828040a00804004100104002020084ce3,0x10c128204501,0x14c128224501,0x15c108208501,0x14c128224501,0x15c108208501,0x100804028040a00804004100100102200084de3,0x104005008040200804004100100802020084ce3,0x0,0x0,0x0,0x14c128220501,0x1020048a8060200804004100100402030084ce3,0x14c128220501,0x104108200501,0x0,0x94c128204501,0x204600081180020463cc0004bf00012fc0003cc1e625f91160001e625f85b20003cc25f83cc1e61556,0x94c128204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x0,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x220008848040200804004100108002200084ce3,0x100008040200804004100108002200084ce3,0x420010888040200804004100108002200084ce3,0x1e60f307983cc1e60f307983cc0f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x8004210000c0002804004100108002200084ce3,0x40420040022,0x800821000140004804004100108002200084de3,0x40420040022,0x40020040022,0x40820040022,0x40020040022,0x40820040022,0x40020040022,0x0,0x0,0x0,0x8420284410a2,0x8420284410a2,0x40020040022,0x8420284410a2,0x0,0xf6cc003ea7fcc8b6b9805b200016c80004bf079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x1e9cc007b69e2c8b73301116000445800088b079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x0,0x8100208001004000200000200080002000000a4],
[0x440826340c82,0x440024040022,0x440826340c82,0x440024040022,0x3cde603cc79803cde600f3003db3000f3f3003db301e60f3003db301e9cc1e60f3001e9cc007983ffb6,0x0,0x3cde603cc79803cde601e6003d39800f4e6003db303cc1e6003db303cfcc1e60f3003cfcc00f307cbb6,0x8200208001009000240240209080242009049e4,0x44202c6418e2,0x3cde603cc79803cde603cc003db3000f6cc003db307983cc003db3079bcc1e60f30079bcc01e60f63b6,0x44202c6418e2,0x0,0x10004410000c0002804004100108002200084ce3,0x0,0x1000841000140004804004100108002200084de3,0x0,0x1001040a40240008804004100108002200084ee3,0x1000040000040100804004100108002200084ce3,0x1002040a80440010804004100108002200084ce3,0x0,0x1004040100840020804004100108002200084ce3,0x10233cc00f3f30f301e603cc007a73001e6f3004d2043202c0003cfcc1e9cc20c073001e9cc00798408b6,0x0,0x20021400080000000080000000200000042803000100001000000020000020010002000010008000040008000080020000080400000101000000404000000410000001009087fda7,0x0,0x0,0x1020040a04040100804004100108002200084ce3,0x1000040000040000804004100108002200084ce3,0x0,0x0,0x0,0x0],
[0x0,0x80040000400200002001000002001000000000005000e000200008001000000001000000001060e8007000080000080000004000200010000800740000000100000000000052ba8,0x440826340c82,0x440024040022,0x440826340c82,0x440024040022,0x799e601e67980799e600f3003db3000f3f3003d39897e3cc003d398981cc1e60f300981cc0079932fb6,0x0,0x799e601e67980799e601e6003d39800f4e6003d3983cc1e6003d3983cfcc1e60f3003cfcc00f307cbb6,0x0,0x44202c6418e2,0x1e60f307981e61e607987980f30f3079801e7e60079bcc01e9cc003db3000f6cc001ede5995,0x44202c6418e2,0x2010080408040200804004100108002200086ce3,0x8040200804004100108002200084ce3,0x4020100808040200804004100108002200084ce3,0x8040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_8879 : TreeBound (n := 4) 106 (programCode 0x4429073f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part010_8880 part010_8881 part010_9010 part010_9011 part010_9204 part010_9205 part010_9206 part010_9207 part010_9352 part010_9353 part010_9498 part010_9691 part010_9900 part010_9901 part010_9998 part010_9999

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10145 : TreeBound (n := 4) 106 (programCode 0x4429074071) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0003008000600010084200100082002080ce3,0xc0003008040200100804200100802020080ce3,0xc0003008000a00020104200100102004080de3,0xc0003008000200000004200100002000080ce3,0xc0003008040200040204200100202008080ee3,0xc0003008040200000004200108002000080ce3,0xc0003008002200080404200100402010080ce3,0x0,0x80028008022,0x80428008022,0xc0003000140004020104200108002004080de3,0x80428008022,0xc0003000240008040204200108002008080ee3,0x80828008022,0x80028008022,0x80828008022,0x80028008022,0x1400050008008200240009000204008100805e4,0x0,0x1400050010008400240009000204008100805e4,0x0,0x0,0x0,0x0,0xc0003008040200100804200100802020080ce3,0x25f800097e0f325f83cc0004bf00012fc000408c0010231e603cc000f3f4e600f3000f3f31e60f63b6,0x0,0x80028000022,0x80428000022,0x80028000022,0x80428000022],
[0xc0003000201008201004200101002040081ee3,0x0,0x80028000022,0x0,0x80028000022,0x581028290a62,0x80028000022,0x581028290a62,0x0,0xc0003000402200201004200101002040081ce3,0x0,0xc0003001008200201004200101002040081ce3,0x25f800097e0f325f83cc0004bf00012fc000408c0010231e603cc000f4e7e60079800f4e60f307cbb6,0x0,0x10c128220501,0x84002108000600402004200102002080082ce3,0x10c128220501,0x14c129220501,0x114128220501,0x15c129220501,0x114128220501,0x0,0x84002108000600402004200102002080082ce3,0xc0002088000600402004280102002080082ce3,0x88002208000600402004200102002080083ce3,0xc0002418000600402004282102002080082ce3,0x144129220501,0x82002508000600402004282102002080082ce3,0x144129220501,0x14c129220501,0x0,0x10c042208481],
[0x84002108000200000004200100402000080ce3,0x10c042208481,0x80002008000200000004000100402000080ce3,0x81002048046200180c04030100401030080ca3,0x80002008000200000004000100402000080ce3,0x81002088046200180c04030100401030080ca3,0x0,0x84002108000200000004200100402000080ce3,0x0,0x88002208000200000004200100402000080ce3,0x0,0x14416b228501,0x82002108044200100804220100402020080ce3,0x14416b228501,0x80002008000200000004000100402000080ce3,0x0,0x10c128220501,0x80002108000600804004200104002100084ce3,0x10c128220501,0x14c129220501,0x114128220501,0x15c129220501,0x114128220501,0x0,0x84002108000600804004200104002100084ce3,0x0,0x88002208000600804004200104002100085ce3,0x0,0x144129220501,0x82002988000600804004302104002100084ce3,0x144129220501,0x14c129220501],
[0x0,0x10c000200481,0x0,0x10c000200481,0x104000200481,0x114000200481,0x104000200481,0x114000200481,0x0,0x0,0x0,0x0,0x0,0x144021204481,0x1e60f31e60f311160f33cc0004bf00012fc000408c3cc0f31e603cc3cc0f31e603cc3cc0f303cc1e7556,0x144021204481,0x104000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10258 : TreeBound (n := 4) 106 (programCode 0x4429074072) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x440021000200408040204200100082002080ee3,0x180828084222,0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x0,0x0,0x0,0x0,0x16c800111600016c83cc0004bf00012fc000408c001f531e603cc001e605b20003cc1e603cc1e61556,0x16c800111600016c83cc0004bf00012fc000408c001f531e603cc001e601e60f3000222c0000001556,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x2200000008800000012000000018000400380010000000014000000100000000120002001c200080052000000002000000200022001400020000000200008000200010001fdfa8,0x180828084222,0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222],
[0x181028084222,0x0,0x0,0x0,0x0,0x0,0x8400210000c0002010084200100202008080ce3,0x840021000840020100804200100202008080ce3,0x840021000140004020104200100202008080de3,0x840021008040000000004200100202008080ce3,0x840021000240008040204200100202008080ee3,0x840021008040000000004200100202008080ce3,0x840021000440010080404200100202008080ce3,0x840021008040000000004200100202008080ce3,0x840021000840020100804200100202008080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c80000003cc3cc0f30f30408c001f5300003cc001e61e60001e601e61e60f30cb96,0x0,0xacfec056ed865f7fb0159fd80acfec000567f8b3fb000002b4a7fec00015a0033fb0000000acfec000000059336bb9a110164cd6c000000acfec00000000b7ceac0000000acfec567f6015a00340067f70380d3fb00000000acff167f60002b3fb00002b3fdb40067f600002b4109fd8000015a5401773422acfec081bf102b3fb000000015a131fd80000159fd800acfec159fdd72e80a59aab,0xc00030001008040240005000102004080402e4,0x7736826b2f940108c54bdd4d947ab2801dd11eaca0430f11ab28000f224dc135cfa9b0d04d6c7712eca0003c893528000ee6ba6c6baa5003ba23d6827a0eb2803b9ca6d650fd51e9688f565003ba23d6826b45eb3a13f418ee27b61653bb897650007735a3d51db6e6be6280df49,0xc00030002008080240005000102004080402e4,0x861c4680003f5476a0001ebbd028000218711a00002cb418150aa7f40c0218f9fd02f736826b28077359b7359b736826b2807ea8ed40003d77a09a8cc7711277a1551c4ea50000f047fe50003b9b05e54f53fa22e00654fe9026b2f73594ee6b283b9ad8e6b9f3597c44f16ca,0xc00030004008100240001000102004080402e4,0x16c800111600016c8000f303cc0000f30f30408c001f5300003cc001e61e60001e601e61e60f30cb96],
[0xc00030008008200240009000102004080402e4,0x1200000008800000012000000018000000400004004000008c2540004104000010800001021000000208002412a200000020010001000080904a00100000800100040802058da8,0xc00030010008400240009000102004080402e4,0x0,0x0,0x0,0x0,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x840021000201008040204200100402010080ee3,0x180828084222,0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x0,0x0,0x0,0x0,0x0,0xc00030000008100240001000104004100804e4,0x120000000180000001200000001800000010000400010004000100004000100010800001008000000208000410820000002000800008008010420008000080020004000205b1a8,0x40002000001008000002020001050080000000600000002000000022000000028001000000201000000804000808010000008040000002000020010400000100000200100108413a7,0xc00030001008040240005000104004100804e4,0x2200000008800000012000000018000602b0001000000001400000010000000012000301582000c05420000000020000002002030150002000000020000080020001000087dfa8,0xc00030002008080240005000104004100804e4,0x16c800111600016c80000003cc3cc0f33cc0408c001f5300003cc001e63cc0000f301e63cc1e610856],
[0xc00030004008100240001000104004100804e4,0x16c800111600016c8000f303cc0000f30f30408c001f5300003cc001e63cc0000f301e63cc1e610856,0xc00030008008200240009000104004100805e4,0x15cb17bacfec0567f602b3fb0159fd80acfec0000568213fb0000acff6cfec0001b07f93fb0002b3fbae58bd80acfec02b3fb0159fe2cfec0000acfec2b3fb00acfec0567f600ad0179b976bcb17b000ad0427f600002b3fb159fd800ad0427f600002b3fb02b3fb02b40067f600002b410cb17b000567f6acfec00159fd8acfec002b3fb0acfec0015b577d80000159fd8acfec00159ff312c6140f8ab,0xc00030010008400240009000104004100805e4,0x0,0x0,0x0,0x0,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x180828084222,0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x1002000001008000040020000040080000400020001000020010000200010000800010000201000000800400008010000008000400004001000010010000100010000100108513a7,0x0,0x0,0x0,0x0,0x181428290a62,0x180428290a62,0x181028290a62,0x180428290a62,0x0],
[0xc00030002008080240005000108004201009e4,0x181428290a62,0xc00030004008100240001000108004201009e4,0x181428290a62,0x181028290a62,0x181028290a62,0x181028290a62,0x0,0x0,0x0,0x0,0x0,0x180428080222,0x180428080222,0x180028080222,0x180428080222,0x0,0x0,0x180428080222,0x0,0x180428080222,0x181028290a62,0x180028080222,0x181028290a62,0x10002000004008000100020001150080001000080001000020010000800010008a80010000801000000804540008011000008002000010001000008020000100020000100108783a7,0x16c800111600016c80798004458000fa9800408c001f531e603cc001e605b20000f31e603cc1e61556,0x0,0x0,0x0,0x181428290a62,0x180428290a62,0x181028290a62],
[0x180428290a62,0x0,0xc00030002008080240005000110004402011e4,0x181428290a62,0xc00030004008100240001000110004402011e4,0x181428290a62,0x181028290a62,0x181028290a62,0x181028290a62,0x16c800111600016c83cc0003d3a730b64000408c03d4119e603cc03f2167e6003cc01e7e60f4edacc6,0x0,0x16c800111600016c83cc0003d39800b82600408c03d4119e6222c0026167f5303cc01e7e60f4edacc6,0x0,0x0,0x3cc007983cc7a73f30b6403ccf3007a36422a59e601ea4581e61e601e679801ed98003d39801e8e97c5,0x0,0x40800040100000400008000204080001400022205000020004000008110000a88044000020010000400540000800400000800400000408000004010000002010000010110a53ca7,0x0,0x3cc03cc1e63ccfa98408c0000f3007d88c1ed980001e9cc01e600001e679801ed98003d39801e7037c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3ccf30798f302d90f33cc05b2f3016cbcc248b83cc1ea8241e62d901e679801ed98003d39801e8e97c5,0x102300102300010233cc0004bf00012fc000408c001f531e603cc001ed99e61116001ed983cc1e7556,0x3cde60f303cc4bf1e63cc0798f3025fbcc2671cbf01eabf01e63cc01e679801ed98003d39801ecb57c5,0x1116000fa980011163cc0004bf00012fc000408c001f531e603cc001f531e612fc001f5307983cd556,0x0,0x0],
[0xf30798f307980f30b640004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc1e7556,0x0,0x0,0x0,0x0,0x16c8000f3079810233cc0004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc1e7556,0x0,0x0,0x0,0x12fc00111600012fc3cc0004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc97f556,0x0,0x620010000010040000400080000400080040003100100000200400000801000080006200010000100040040000080004000080620000100800000400100000201000001001087fca7,0x102300102300010233cc0004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc1e7556,0xf30798f6cc001023b640004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc1e7556,0x1116000fa980011163cc0004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc5b3556,0x0,0x3cc00798f307a73f30b640798f3000222c27e022c01eabf01e63cc01e6f3001e7e6003db3001ead3485,0xf30798f307980f30b640004bf00012fc000408c001f531e603cc001e601e60000001e600000001556,0x800040100000080020001005020001400000005000010004000000110000d28108000020020000080600000801a00000800800000401000000820000010020000010090a503a7,0xf30f30f303cc0f312fc0004bf00012fc000408c001f531e603cc001e601e60000001e600000001556,0x3cc03cc7983ccfa98408c0000f3000f6cc205530001e9cc01e600001e6f3001e7e6003db3001e7037c5,0x0,0x16c8000f307980f303cc0004bf00012fc000408c001f531e603cc001e601e60f3000222c0000001556,0x0,0x0,0x0,0x0,0x0,0x10000800004000800100008000150008004000080010000020040000800100008a80010000800040000804540008011500008020000010010000008200000100200000100108783a7,0x102300102300010233cc0004bf00012fc000408c001f531e603cc001e605b20000f31e603cc1e61556,0x3cde607983cc4bf1e63cc0d4af300f33cc2baa4bf01ea4581e66a501e6f3001e7e6003db3001ecb57c5,0x0],
[0x0,0x3cc0079800089a3000b640000f300003cc1e6000001e9cc01e600001e600001f530003cc0001e7037c5,0x0,0x0,0x0,0x3cc03cc0003dc2300408c0000f300003cc1e6000001e9cc01e600001e600001f530003cc0001e7037c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1100000001c0000001300000001c00040000000500000004400000005000000010800200008000000208002000020000002080000008800080000800000082000400020005b1a8,0x102300102300010233cc0004bf00012fc000408c001f531e603cc001f531e603cc001f530798d4b556,0xf31e60fa9800111822c0004bf00012fc000408c001f531e603cc001f531e603cc001f5307983cd556,0x1116000fa980011163cc0004bf00012fc000408c001f531e603cc001f531e603cc001f5307983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10499 : TreeBound (n := 4) 106 (programCode 0x4429074073) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x140005008000600010084200100082002080ce3,0x140005008040200000004200100002020080ce3,0x140005008000a00020104200100102004080de3,0x140005008000200000004200100002000080ce3,0x140005008040200040204200100202008080ee3,0x0,0x10c000200481,0x0,0x10c000200481,0x104000200481,0x114000200481,0x104000200481,0x114000200481,0x0,0x0,0x3cc01e6f301e72fc01e9cc0004bf00012fc000408c1e60f31e603cc1e6002046001e7e6001ed984c23b6,0x0,0x3cc03ccf300f42fc03cfcc0004bf00012fc000408c1e60f31e603cc1e6002046001e7e6001ed98448bb6,0x110004408046200180c04004100c02030080ce3,0x3cc0f30f30f312fc0f33cc0004bf00012fc000408c1e60f31e603cc1e6002046001e7e6001ed98d4b556,0x120004808046200180c04004100c02030080ce3,0x104000200481,0x140005008002200080404200100402010080ce3,0x0,0x0,0x0,0x100804028040200000004000100002200080ce3,0x3cc0010230004fbc0012fc0004bf00012fc000408c1e60f31e603cc1e6003ea6000f4e6003d3983cf3b6,0x101004048040200000004000100002200080ce3,0x100004008040200000004000100002200080ce3,0x102004088040200000004000100002200080ce3],
[0x0,0x0,0x3cc01e6f301e72fc01e9cc0004bf00012fc000408c1e60f31e603cc1e6003ea6000f4e6003d3984c23b6,0x0,0x3cc03ccf300f42fc03cfcc0004bf00012fc000408c1e60f31e603cc1e6003ea6000f4e6003d398448bb6,0x110004408040200000004004100002200080ce3,0x3cc0f30f30f312fc0f33cc0004bf00012fc000408c1e60f31e603cc1e6003ea6000f4e6003d398d4b556,0x120004808040200000004004100002200080ce3,0x100004008040200000004000100002200080ce3,0x140005008040200100804200100802020080ce3,0x0,0x581428290a62,0x580428290a62,0x80028010022,0x580428290a62,0x140005000201008100804200100802020080ce3,0x0,0x80028010022,0x0,0x80028010022,0x481028290862,0x481028290862,0x481028290862,0x0,0x16c87980799e600007981e60008118001ed98004458b641e61e603cc0f303ced900f30f300f3000001e56,0x0,0x0,0x0,0x80028000022,0x80428000022,0x80028000022,0x80428000022],
[0x140005000201008201004200101002040081ee3,0x80828020022,0x80028000022,0x80828020022,0x80028000022,0x481028290862,0x80028000022,0x481028290862,0x0,0x140005000402200201004200101002040081ce3,0x0,0x140005001008200201004200101002040081ce3,0x0,0x581428290a62,0x580428290a62,0x80028010022,0x580428290a62,0x0,0x0,0x80028010022,0x0,0x80028010022,0x481028290862,0x481028290862,0x481028290862,0x140005002000880020104200100102004080de3,0x7981e61e60f307980798004458000fa9800408c3cc0f31e603cc3cc01e7e60079bcc01e6000001556,0x140005004000900020104200100102004080de3,0x0,0x0,0x10c128220501,0x104004108000a00402004200102002080082ce3],
[0x10c128220501,0x14c129220501,0x114128220501,0x15c129220501,0x114128220501,0x0,0x104004108000a00402004200102002080082ce3,0x140004088000a00402004280102002080082ce3,0x108004208000a00402004200102002080083de3,0x140004428000a00402004284102002080082de3,0x144129220501,0x102004508000a00402004284102002080082ce3,0x144129220501,0x14c129220501,0x140005008042200080404200100402200080ce3,0x0,0x10c128220501,0x100004108000a00804004200104002100084ce3,0x10c128220501,0x14c129220501,0x114128220501,0x15c129220501,0x114128220501,0x3cc1e6111679825f83cc00088b000222c0f3079801e7e6007aec801e7e6003d39800f3f3001ee07c55,0x104004108000a00804004200104002100084ce3,0x0,0x108004208000a00804004200104002100085de3,0x0,0x144129220501,0x102004988000a00804004304104002100084ce3,0x144129220501,0x14c129220501],
[0x140005008040200000004200100002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10628 : TreeBound (n := 4) 106 (programCode 0x4429074074) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0003008000600010084200100082002080ce3,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x180828084222,0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x2040001002010080000004200100002020080ce3,0x0,0x0,0x0,0x140005008000a00020104200100102004080de3,0x40001008000200000004200100002000080ce3,0x0,0x20c042208481,0x0,0x20c042208481,0x4000208481,0x14000208481,0x4000208481,0x14000208481,0x0,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc000408c0010231e603cc0012fc1e600f3000f307b660f63b6],
[0x0,0x1e9cc007a73001e9cfcc0004bf00012fc000408c0010231e603cc0012fc1e60079800f307a7307cbb6,0x44000208481,0x4000208481,0x44000208481,0x4000208481,0x25f800097e00025f83cc0004bf00012fc000408c0010231e603cc000f32046001e600f31e63cc219b6,0x40001008000200000004200100402010080ce3,0x0,0x1400050001008040240009000204008100805e4,0x159fd80acfec0579de6193fb0159fd80acfec0001b07f93fb0002b3fbacfec00000002b3fb000015a084fec0579de619cef30c9fd80acfec000acfec00d83e706c1f3959fd80159fd80000159fd8000acff179de5ee2b3fb00159fd959fdd67f60002b3fb000000002b40067f600002b3fb0159fd800ad565de5ee00acfec000000002b96dc5ec000ad145fd80000159fd959fd800159fdecce32081fab,0x0,0x1400050001008040240009000204008100805e4,0x0,0x1400050002008080240009000204008100805e4,0x1400050001008100240009000204008100805e4,0x1400050004008100240001000204008100804e4,0x1400050001008040240009000204008100805e4,0x1400050008008200240009000204008100805e4,0x600000004800000022000000028000000080002e07d0002040000010008000010400200004000f87fa00020000200000040004000020040f87f802000010002000090006caba8,0x1400050010008400240009000204008100805e4,0x400020001000080000000200000000800020002000080008000040000000100000004000010000000040000000020100000080600000100000000084000000801000001000487ce27,0x0,0xf307980001e60f307980799e607980000f31e6000001e9cc00f3f3001e9cc00109c800f3f3001e689ba5,0x0,0x0,0x180428084222,0x180428084222,0x180428084222,0x180428084222,0x0,0x180828084222],
[0x180428084222,0x180828084222,0x180428084222,0x181028084222,0x180428084222,0x181028084222,0x2040001002010080000004200100802020080ce3,0x0,0x0,0x0,0x25f800097e00025f83cc0004bf00012fc000408c0010231e603cc000f3f4e600f3000f3f31e60f63b6,0x0,0x180428080222,0x180428080222,0x180028080222,0x180428080222,0x0,0x0,0x180428080222,0x0,0x180428080222,0x181028290a62,0x180028080222,0x181028290a62,0x2040001002010080000004200101002040080ce3,0x40001000000200000004200101002040080ce3,0x0,0x40001000000200000004200101002040080ce3,0x25f800097e00025f83cc0004bf00012fc000408c0010231e603cc000f4e7e60079800f4e60f307cbb6,0x40001008000200000004200102002080080ce3,0x0,0x400018000200000004010100002010080ce3],
[0x108000200000004200100002000080ce3,0x800028000200000004000100002010080ce3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x4000108000200000004200100002000080ce3,0x1e7e6007b66001e7e9cc0004bf00012fc000408c0010231e603cc000fa99e60798000fa98f307d7fb6,0x8000208000200000004200100002000080ce3,0x1e9cc007a73001e9cfcc0004bf00012fc000408c0010231e603cc000fa99e60798000fa98f30814bb6,0x44000220481,0x4000200481,0x44000220481,0x4000200481,0x40001008000200000004200104002100080ce3,0x0,0xc000200481,0x0,0xc000200481,0x4000200481,0x14000200481,0x4000200481,0x14000200481,0x0,0x0,0x1e7e6007b66001e7e9cc0004bf00012fc000408c0010231e603cc0010231e603cc00102307984c23b6,0x0,0x1e9cc007a73001e9cfcc0004bf00012fc000408c0010231e603cc0010231e603cc0010230798448bb6,0x44000200481,0x4000200481,0x44000200481],
[0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10757 : TreeBound (n := 4) 106 (programCode 0x4429074075) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x20c021204481,0x200408018040200100804020100802020080ce3,0x20c021204481,0x20c000200481,0x20c042208481,0x20c000200481,0x20c042208481,0x0,0x200408018040200100804020100802020080ce3,0xf30000f307983cc25f92fc0004bf00012fc000408c0010231e603cc000f3f4e600f3000f3f31e60f63b6,0x0,0xf30000f307983cc25f92fc0004bf00012fc000408c0010231e603cc000f4e7e60079800f4e60f307cbb6,0x20c148220501,0x200408018042200080404010100802010080ce3,0x20c148220501,0x20c000200481,0x0,0x0,0xf30000798f3088b0000b640004bf00012fc000408c001f531e603cc001e605b20003cc1e603cc1e61556,0x79a22c7983cc07a1fb4c0002d9000222c1e63cc001e9cc01e6f3001e6003ccf303ccf300799e7033d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0xf30000798f3088b0000b640004bf00012fc000408c001f531e603cc001ed99e60798001ed983cc1e7556,0xf30000798f3088b0000b640004bf00012fc000408c001f531e603cc001e601e60f30001e600000001556,0x0,0x0,0x20c021204481,0x200808028040200000004000100002020080ce3,0x20c021204481,0x20c000200481,0x20c042208481,0x20c000200481,0x20c042208481,0x200808028040200000004000100002200080ce3,0x200808028040200100804020100802020080ce3,0x0,0x0,0x0,0x20c148220501,0x200808028044200100804020100802010080ce3,0x20c148220501,0x20c000200481,0x0,0x20c021204481,0x0,0x20c021204481,0x204000200481,0x204000208481,0x204000200481,0x204000208481,0x0,0x0,0xf30000f307983cc1e612fc0004bf00012fc000408c0010231e603cc000f3f4e600f3000f3f31e60f63b6,0x0],
[0xf30000f307983cc1e612fc0004bf00012fc000408c0010231e603cc000f4e7e60079800f4e60f307cbb6,0x214040220481,0xf30000f307983cc1e612fc0004bf00012fc000408c0010231e603cc000fa99e60798000fa98f3079b3b6,0x214040220481,0x204000200481,0x201008048040200000004000108002200080ce3,0x200008008040200000004000108002200080ce3,0x202008088040200000004000108002200080ce3,0x0,0x0,0xa104285414c2,0x0,0xa104285414c2,0xa128285414c2,0xa108285414c2,0xa128285414c2,0xa108285414c2,0xa128285414c2,0xf307983cc1e601e6798f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x0,0xf307983cc1e601e6799e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983de6b6,0xa128285414c2,0xa120285414c2,0xa128285414c2,0xa120285414c2,0x0,0x2040081000c0002010084002108002200080ce3,0x428040022,0x204008100140004020104004108002200080de3,0x428040022,0x28040022,0x828040022],
[0x28040022,0x828040022,0x28040022,0x0,0x0,0x0,0x28040022,0x2028040022,0x28040022,0x2028040022,0x0,0x1024e7e63cc1e6001e7e6007984bf0001338c00408c0798f3204a08c079bcc1e64bf0079bcc0003db63b6,0xf30f4e63cc1e6001e7e6003cc3cc3cc0f303cc408c0798f31e6222c079bcc1e60f30079bcc0001e61556,0xf3001e63cc1e6001e7e6000004bf00012fc000408c0798f31e603cc079bcc1e60f30079bcc0000001556,0x8040041001008040240041001080042000209e4,0xf4e7e63cc1e6001e7e63d3983db3000f30798408c0798f301ea08c079bcc204abf0079bcc01e9db63b6,0x804004100200808024004100108004200040be4,0x1000800008080000010008000010020000082000000800040000820000002000404000008000080040000200080000800080400000041000000404000000410000001001285bda7,0x8040041004008100240001001080042000804e4,0xf4e7e63cc1e6001e7e63cc003db4e60f6cc00408c0798f301ea08c079bcc2046f30079bcc01e60f63b6,0xf301e63cc1e6001e7e60f3003db3000f3f300408c0798f3000408c079bcc1e60f30079bcc0079932fb6,0x0,0xf301e63cc1e6001e7e61e6003d39800f4e600408c0798f3000408c079bcc1e60f30079bcc00f316fbb6,0xf4e7e63cc1e6001e7e6007983db4e60f30798408c0798f301ea08c079bcc1e64bf0079bcc0003db63b6,0x8040041020008800240041001080042004029e4,0xf3001e63cc1e6001e7e6000004bf0000f30000408c0798f31e603cc079bcc1e60f30079bcc0000001556,0x8040041040009000240041001080042008049e4,0x0,0x2080082000c0002010084002108002200080ce3,0x0,0x208008200140004020104004108002200080de3,0x0],
[0x208008200240008040204008108002200080ee3,0x208008200040000000004000108002200080ce3,0x208008200440010080404010108002200080ce3,0x208008200040000000004000108002200080ce3,0x208008200840020100804020108002200080ce3,0x3d39800f30798025f800f3003db3000f3f300408c01e6f3000408c01e9cc1e60f3001e9cc007983ffb6,0x0,0x79f9801e60f30025f801e6003d39800f4e600408c03ccf3000408c03cfcc1e60f3003cfcc00f307cbb6,0x0,0x208008200840200100804020108002200080ce3,0x0,0x208008200040000000004000108002200080ce3,0x0,0x0,0x0,0x0,0x10080042001008040240081002080082000211e4,0x7b69cc1e60f3001e9cc1ed983d39800f30798408c03ccf300f708c03cfcc1f53f3003cfcc00f307cbb6,0x10080042002008080240081002080082000413e4,0xfa983cc1e60f3001e9cfcc0003d39800f4e600408c03ccf31e6408c03cfcc1e60f3003cfcc00f307cbb6,0x10080042004008100240001002080082000804e4,0x10dfec980f307987b69d037f947981e607a7300445886ffa1800408c01e9cc21c0bd001e9cc0170579f96,0x7983cc1e60f3001e9cc0f3003db3000f3f300408c03ccf3000408c03cfcc1e60f3003cfcc01e616fbb6,0x0,0x7983cc1e60f3001e9cc1e6003d39800f4e600408c03ccf3000408c03cfcc1e60f3003cfcc00f307cbb6,0x7b69cc1e60f3001e9cc007983d3b660f30798408c03ccf300f708c03cfcc1f57bf003cfcc00f6d3cbb6,0x10080042020008800240081002080082004031e4,0x1000080008080000010000800010000008002000080000000080020000200000004000008000000040000000080000000080400000041000000404000000410000001001085bda7,0x10080042040009000240081002080082008051e4,0x210008408040200040204008108002200080ee3,0x0,0x40020000108000801000200001082908000600000001000080012000000018000800040200000100804000408010001008040000002100000008400000101000000100108403a7],
[0x8404284410a2,0x100020000108001801000200001082d18002200000001000100022000000028001800080800000200804000c08010003008040000010100000008400000101000000100128f83a7,0x8404284410a2,0x8420284410a2,0x8408284410a2,0x8420284410a2,0x8408284410a2,0x8420284410a2,0x798000798798079803cc0000f30798000000000001e60001e600001e9cc001f530007d4c001e703855,0x0,0x798000798798079803cc0000f30798000000000001e60001e600001e9cc001f530007d4c001e703855,0x8420284410a2,0x8420284410a2,0x8420284410a2,0x8420284410a2,0x220008808040200040204008108002200080ee3,0x200008008040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10934 : TreeBound (n := 4) 106 (programCode 0x4429074076) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x30c021204481,0x400018040200000004020100002020080ce3,0x30c021204481,0xc000200481,0x0,0xc000200481,0x0,0x0,0x400018040200000004020100802020080ce3,0x798f3079803cc81192fc0004bf00012fc000408c00f3f31e603cc00f30f4e600f300f30f37983ed9b6,0x0,0x798f3079803cc81192fc0004bf00012fc000408c00f3f31e603cc00f31e7e6007980f31e67983ed9b6,0x80480018010200402004080102002080082ce3,0x0,0x80512018000600894084100102001100084ca3,0xc000200481,0x0,0x20000100080000400100000800100000c0114000400400000c00000005004100010800020a0100000200800260a020000020400006021000098284000000810000080804145cda8,0x2084285414c2,0x0,0x2084285414c2,0x20040801008080a0240211000480012008442e4,0x2088285414c2,0x0,0x2088285414c2,0x2004080102008080240011000480012008040e4,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x30c021204481,0x800028040200000004000100002020080ce3,0x30c021204481,0xc000200481,0x0,0xc000200481,0x0,0x800028040200000004000100002200080ce3,0x800028040200000004020100802020080ce3,0x0,0x0,0x0,0x100880028010200402004080102002080082de3,0x800028000200000004000100002010080ce3,0x2000100088000400020000880080001400000011000000444000000110000400420000020080000080200200200c00000802000001008000004010000008020000010206a73227,0xc000200481,0x7980f379803cc79812fc0004bf00012fc000408c00f3f31e603cc00f6cc1e60f3000f6cc07983ed9b6,0x1000048040200000004000108002200080ce3,0x8040200000004000108002200080ce3,0x2000088040200000004000108002200080ce3,0x0,0x0,0x2104285414c2,0x0,0x2104285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2],
[0x2108285414c2,0x2128285414c2,0x7987987981e60798798f3003db3000f3f300408c00f3f3000408c00f6cc1e60f3000f6cc07983fccb6,0x0,0x7987987981e60798799e6003d39800f4e600408c00f3f3000408c00f6cc1e60f3000f6cc07983fccb6,0x2128285414c2,0x2120285414c2,0x2120285414c2,0x2120285414c2,0x0,0x4040001000c0002000004002108002200080ce3,0x2504285414c2,0x404000100140004000004004108002200080ce3,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x798f3079803cc798f30f3003db3000f3f300408c00f3f3000408c00f6cc1e60f3000f6cc07983ed9b6,0x0,0x798f3079803cc798f31e6003d39800f4e600408c00f3f3000408c00f6cc1e60f3000f6cc07983ed9b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0x799e60799e600799e9cc0004bf00012fc000408c00f3f31e603cc00f6cc1e60f3000f6cc07984e09b6,0x0,0x4080002000c0002000004002108002200080ce3,0x0,0x408000200140004000004004108002200080ce3,0x0],
[0x808008200240008040204008108002200080ee3,0x8000200040000000004000108002200080ce3,0x808010200440010080404010108002200080ce3,0x8000200040000000004000108002200080ce3,0x8000200840020000004020108002200080ce3,0x8118007987980811800f3003db3000f3f300408c00f3f3000408c00f6cc1e60f3000f6cc079842a5b6,0x0,0x811800798f300811801e6003d39800f4e600408c00f3f3000408c00f6cc1e60f3000f6cc07984671b6,0x0,0x8000200040200000004000108002200080ce3,0x0,0x8000200040000000004000108002200080ce3,0x79bcc0798f30079bcfcc0004bf00012fc000408c00f3f31e603cc00f6cc1e60f3000f6cc07984671b6,0x10000408040200000004000108002200080ce3,0x8040200000004000108002200080ce3,0x20000808040200000004000108002200080ce3,0x8040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11047 : TreeBound (n := 4) 106 (programCode 0x4429074077) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x440011008040200000004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11048 : TreeBound (n := 4) 106 (programCode 0x4429074078) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf300007983cc88b0000b640002d90000b641e61e60f4e9cc01e6000f4e6003cde603cc3cc03cde7037c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf3000079800088b0000b640798f300003cc1e603cc01e9cc01e63cc01e6f3001e7e6003db3001ead3485,0xf3000079800088b0000b640000f300003cc1e6000001e9cc01e600001e600001f530003cc0001e7037c5,0x0,0x0,0x2084285414c2,0x0,0x2084285414c2,0xf30079bcc0798f3007980003cc3cc0f30000408c007a7300003cc007d4c0000f30007d4c07983d1216,0x2088285414c2,0x40002000000800100002020800002003000008200000080000000202000000208000000000401008000804000008000080008040000004100000040400000101000000100108573a7,0x2088285414c2,0x4004100100008100240001000880022008040e4,0x0,0x0,0x0,0x3b9aca07736826b2803b9bb86b283b9b4135940ee6b9f35940ee6b280003b9b059aca0fa87c8a474fee6b36e6b2faef40a0000861c46800003b9aca0077394dae2394166b7450001deb326502cbb8ad940077536165001dd4d859a0e4da4c665000eee25d95dcd65eea7eb67efa],
[0x0,0x0,0x0,0x0,0xf30000f303cc2d900012fc000a710000b641e61e60f4e9cc01e6004c0e6003cde603cc3cc03cde707485,0xf4e6003cc01e6fa9fd4c0004bf00012fc000408c007a731e603cc0079805b20003cc798044583cd556,0x400240011000000040000800030000000140002001500000000c00000003000080014002810000002040040000080000010080000200100000800400000400200002001001087fca7,0x0,0x0,0xf4e6003d39800fa9fd4c0004bf00012fc000408c007a731e603cc007982046001e607981ed983cd556,0x201000000204000002020100002080404000000110000000140000001100000001200020000200000402000200002000004000200010100008000002000100800040002000793a8,0xf4e6003d39800fa9fd4c0004bf00012fc000408c007a731e603cc007983ea6000f307983d3983cd556,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2084285414c2,0x0,0x2084285414c2,0x4008100201008100240021000880022008045e4,0x2088285414c2,0x1e601e61e601e6f30165bca0798798088ecc04458e5aee1800222c00408c395f43000408c07b69dd036,0x2088285414c2,0x4008100200008100240001000880022008045e4,0xf300f33cc03ccf300f3f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x0],
[0xf300f33cc03ccf300f4e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x4008100200008100240001000880022008045e4,0xf300f33cc03ccf300fa98004458000fa9800408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x600030000800000000000200002000000020003000080000000080020000200000006000010010000040000000080000000080400000101000000404000000410000001001087fda7,0xf300f33cc03ccf301023000408c001023000408c007a73000408c007d4c1e60f30007d4c07983de6b6,0xf30003cc0003db3000408c0000f307983cc1e6000001e9cc01e600001e9cc001f53000408c001e7037c5,0x0,0x0,0x2104285414c2,0x0,0x2104285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0xf303cc3cc3cc0f303ccf3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983fccb6,0x0,0xf303cc3cc3cc0f303cde6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983fccb6,0x2128285414c2,0x2120285414c2,0x2120285414c2,0x2120285414c2,0x0,0x0,0x2504285414c2,0x0,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2],
[0x2528285414c2,0xfa98003cc1e60f4e600f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x0,0xfa98003cc1e60f4e601e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0x0,0x0,0x2104285414c2,0x0,0x2104285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0x2108285414c2,0x2128285414c2,0xf307983cc1e60f30798f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x0,0xf307983cc1e60f30799e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x2128285414c2,0x2120285414c2,0x2120285414c2,0x2120285414c2,0x0,0x0,0x2504285414c2,0x0,0x2504285414c2,0x2528285414c2,0x2508285414c2],
[0x2528285414c2,0x2508285414c2,0x2528285414c2,0xf307983cc03ccf30798f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x0,0xf307983cc03ccf30799e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0x0,0x0,0x220428541502,0x0,0x220428541502,0xf31e603cde600f31e6044583db3000f34458408c007a73002268c007d4c25f8f30007d4c07984d16b6,0x220828541502,0x222828741502,0x220828541502,0x404010100000810024000100088002200804de4,0xf31e603cde600f31e60f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07984d16b6,0x0,0xf31e603cde600f31e61e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07984d16b6,0x404010100400804024002100088002200804de4,0x222028741502,0x222028741502,0x222028741502,0x0,0x0,0x0,0x0,0x0],
[0x208008200240008040204008108002200080ee3,0x8000200040000000004000108002200080ce3,0x8010200440010000004010108002200080ce3,0x8000200040000000004000108002200080ce3,0x808020200840020100804020108002200080ce3,0xfa98003cc7980fa9800f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c079841b2b6,0x0,0xfa98003ccf300fa9801e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c0798457eb6,0x0,0x0,0x8100204040100000004100108002200080ce3,0x8000200040000000004000108002200080ce3,0x0,0x0,0x220428541502,0x0,0x220428541502,0xf33cc03ccf300f33cc044583d39800f34458408c007a73002268c007d4c25f8f30007d4c0798457eb6,0x220828541502,0x222828741502,0x220828541502,0x4080102000008100240001000880022008055e4,0xf33cc03ccf300f33cc0f3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c0798457eb6,0x0,0xf33cc03ccf300f33cc1e6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c0798457eb6,0x4080102004008040240021000880022008055e4,0x222028741502,0x222028741502,0x222028741502,0x0,0x0,0x2504285414c2],
[0x0,0x2504285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0x2508285414c2,0x2528285414c2,0xf307983cc03ccf3088bf3003db3000f3f300408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x0,0xf307983cc03ccf3088ce6003d39800f4e600408c007a73000408c007d4c1e60f30007d4c07983de6b6,0x2528285414c2,0x2520285414c2,0x2528285414c2,0x2520285414c2,0xf3f3003db3000f3f33cc0004bf00012fc000408c007a731e603cc007d4c1e60f30007d4c0798d4b556,0xf307983d39800f4edd4c0004bf00012fc000408c007a731e603cc007d4c1e60f30007d4c07983cd556,0xf4e6003d39800f4e63cc0004bf00012fc000408c007a731e603cc007d4c1e60f30007d4c07983cd556]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11257 : TreeBound (n := 4) 106 (programCode 0x4429074079) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8400210000c0002010084200108002200080ce3,0x80428040022,0x840021000140004020104200108002200080de3,0x80428040022,0x840021000240008040204200108002200080ee3,0x80828040022,0x80028040022,0x80828040022,0x80028040022,0x0,0x181028084222,0x181028084222,0x181028080222,0x181028084222,0x0,0x1400050008008200240009000202008080403e4,0x181028084222,0x1400050008008200240009000204008100805e4,0x181028084222,0x581028290a62,0x581028290a62,0x581028290a62,0x840021000004000000004200102002080080ce3,0x0,0x840021000004000000004200104002100080ce3,0x0,0x0,0x80028000022,0x80428004022,0x80028000022,0x80428004022],
[0x0,0x0,0x80028000022,0x0,0x80028000022,0x581028290a62,0x80028000022,0x581028290a62,0x840021001004040201004200102002080081ce3,0x0,0x840021001004040201004200104002100081ce3,0x0,0x0,0x181028084222,0x181028084222,0x181028080222,0x181028084222,0x0,0x1400050010008400240009000202008080403e4,0x181028084222,0x1400050010008400240009000204008100805e4,0x181028084222,0x581028290a62,0x581028290a62,0x581028290a62,0x840021000004000000004200102002080080ce3,0x0,0x840021000004000000004200104002100080ce3,0x0,0x0,0x800420012040080402004200108002200082ce3,0x8028040022],
[0x800820022040080402004200108002200082de3,0x8028040022,0x28040022,0x10028040022,0x28040022,0x10028040022,0x28040022,0x20428040022,0x0,0x20428040022,0x28040022,0x8420284410a2,0x28040022,0x8420284410a2,0x0,0x800420010440010080404200108002200080ce3,0x0,0x800820020440010080404200108002200080ce3,0x0,0x2028040022,0xa120285414c2,0x2028040022,0xa120285414c2,0x2028040022,0xc220286418e2,0x0,0xc220286418e2,0x2028040022,0x8420284410a2,0x2028040022,0x8420284410a2,0x0],
[0x800420014040100804004200108002200084ce3,0x0,0x800820024040100804004200108002200084de3,0x0,0x28040022,0xa128285414c2,0x28040022,0xa128285414c2,0x28040022,0x20028040022,0x0,0x20028040022,0x28040022,0x40028040022,0x28040022,0x40028040022,0x0,0x0,0x0,0x0,0x0,0x2028040022,0xa120285414c2,0x2028040022,0xa120285414c2,0x2028040022,0xc220286418e2,0x808020200040000000004000108002200080ce3,0xc220286418e2,0x2028040022,0x8420284410a2,0x2028040022],
[0x8420284410a2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11386 : TreeBound (n := 4) 106 (programCode 0x442907407a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x3d39803cde6003d3980007984bf0001338c00408c0798f3204a08c079bcc1e64bf0079bcc0003db63b6,0x3d39803cde6003d3980003cc3cc3cc0f303cc408c0798f31e6222c079bcc1e60f30079bcc0001e61556,0x3d39803cde6003d3980000004bf00012fc000408c0798f31e603cc079bcc1e60f30079bcc0000001556,0x8400210001008040240041001080042000209e4,0x2002000008008000010020000010080004302800100002000140000001000020001200021814200086052000008002000020040002181500000001400000801000000010100fdfa8,0x840021000200808024004100108004200040be4,0x10020001000080000100200000400800000082000000800040000820000002000404000008010000040000200080100000080400000041000000404000000410000001001285bda7,0x8400210004008100240001001080042000804e4,0x3d39803cde6003d39804bf003cc1e607d4c00408c097e79800408c079bcc1e60f30079bcc025f932f26,0x3d39803cde6003d39800f3003db3000f3f300408c0798f3000408c079bcc1e60f30079bcc0079932fb6,0x0,0x481428294a62,0x480428284a62,0x480028200862,0x480428284a62,0x0,0x3d39803cde6003d398007980419d600f37980408c0798f3204a08c079802049cc1e679801e63cd149b6,0x481028290862,0x1e449b826b2f73597b9acbdcd65ee6b280ee6ee1aca00000ee6b281dcda189352877447ab281dcd650ee6b639acbdcd653b9aca001e449a97b9aca1dcd73e6d04d6503b9aca000003b9ca6d65003ba25b26a50773594000001dcf41d65077536165000ee6b639aca0ee6d83b9e3c09,0x481428294a62,0x481028290862,0x480028200862,0x481028290862,0x40001001000040000004200102002080080ce3,0x0,0x40001001000040000004200104002100080ce3,0x0,0x3d39803cde6003d39801e6003d39800f4e600408c0798f3000408c079bcc1e60f30079bcc00f316fbb6,0x0,0x0,0x8004200101008000240041001080042000000e4],
[0x0,0xf3000f6cc001e9cc00f7bf003cc1e607d5398408c097e7981ea08c079bcc20c43f0079bcc025f933286,0xf30003cc1e63db37983d3980007987980799e6000001e9cc01e600001e9cc001f53000408c001e7037c5,0xf300f33cc03cc3cc03d0bf003cc1e607d5398408c097e7981ea08c079bcc20c43f0079bcc025f933286,0x3d398f6cc1e603cc00f307983cc1e61338c00408c0798f3204a08c079bcc1e64bf0079bcc0003db63b6,0xf30079bcc00f33cc079bd3983cc1e607d5398408c098da981ea08c079bcc204abf0079bcc02635f3286,0x8040201001008040240041001080042000209e4,0x8040201001008040240041001080042000209e4,0x0,0x8080202001008040240041001080042000209e4,0xf307a76cc003cfcc7a76d3983cc1e607d5398408c098da981ea08c079bcc204abf0079bcc02635f3286,0x8100204001008800240141001080042005029e4,0x8000200001008000240041001080042000000e4,0x8200208001009000240241001080042009049e4,0x0,0x41000000300000000810000009040000008008200000020001040082000000208010000800201000000804008008010000008040000004100000010400000101000000100108513a7,0x3cc007d4c0079bcc008118004458000fa9800408c0798f3000222c079bcc1e60f30079bcc03cc1e7556,0x8400205020008800240141001080042005029e4,0x3cc00f6cc003cfcc00fa98004458000fa9800408c0798f3000408c079bcc1e60f30079bcc03cc2dc3b6,0x3cc7983cc00003cc00fa98004458000811800408c111679800408c079bcc1e60f30079bcc0445b18f26,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x0,0x4220286418e2,0x3cc7983cc003cfcc7a7a98004458000811800408c11167981ea08c079bcc222cf30079bcc0445b18f26,0x4420286418e2,0x4620286418e2,0x4420286418e2,0x0],
[0x0,0x0,0x0,0x0,0xf30003cc7983db37983db300001e67980f31e6000001e9cc01e600001e9cc001f53000408c001e7037c5,0x412028741902,0x420028240862,0x412028741902,0x420028240862,0x420028240862,0x0,0x420028240862,0x0,0x3ccf303ccf3003ccf300f3003cfcc00f3f300408c0798f3000408c079bcc1e60f30079bcc0079932fb6,0x400028240862,0x3cde603cc79803cde603cc003db3000f6cc00408c0798f3000408c079bcc1e60f30079bcc01e60f63b6,0x0,0x0,0x0,0x0,0x3cc00f6cc003cfcc01023000408c001023000408c0798f3000408c079bcc1e60f30079bcc07984c23b6,0x8000200240009000240001001080042008040e4,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x8040210040009000240041001080042008049e4,0x4220286418e2,0x3cc7983cc003cfcc7a823000408c001023000408c0798f3000408c079bcc1e60f30079bcc07984c23b6,0x4420286418e2,0x4620286418e2],
[0x4420286418e2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11483 : TreeBound (n := 4) 106 (programCode 0x442907407b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10400410000c0002010084200108002200080ce3,0x0,0x80428000022,0x180428084222,0x80428000022,0x180428084222,0x1040041000840020100804200100202008080ce3,0x0,0x80428000022,0x0,0x80428000022,0x480428290a62,0x80428000022,0x480428290a62,0x0,0x0,0x0,0x0,0x1040041000140004020104200108002200080de3,0x0,0x80428000022,0x180428084222,0x80428000022,0x180428084222,0x0,0x0,0x80428000022,0x0,0x80428000022,0x480428290a62,0x80428000022],
[0x480428290a62,0x1040041001008040201004200102002080081ce3,0x0,0x1040041001008040201004200104002100081ce3,0x0,0x1040041000240008040204200108002200080ee3,0x0,0x0,0x40006000102008080240201008080202008040e4,0x0,0x4000a000202008080240201008080202008041e4,0x1001040040040000000004000108002200080ce3,0x1000040000040000000004000108002200080ce3,0x1002040080040000000004000108002200080ce3,0x1000040000040000000004000108002200080ce3,0x1004040100040000000004000108002200080ce3,0x40042001002008080240201008080202008049e4,0x1008040200040000000004000108002200080ce3,0x40082002002008080240201008080202008051e4,0x0,0x40102004002008080240201008080202008060e4,0x0,0x1000040000040000000004000108002200080ce3,0x1040041000440010080404200108002200080ce3,0x0,0x0,0x40006000104008100240001008080202008040e4,0x0,0x4000a000204008100240001008080202008041e4,0x1001040040040000000004000108002200080ce3,0x1000040000040000000004000108002200080ce3,0x1002040080040000000004000108002200080ce3],
[0x1000040000040000000004000108002200080ce3,0x1004040100040000000004000108002200080ce3,0x40042001004008100240001008080202008049e4,0x1008040200040000000004000108002200080ce3,0x40082002004008100240001008080202008051e4,0x1010040400040000000004040108002200080ce3,0x40102004004008100240001008080202008060e4,0x1020040800040000000004040108002200080ce3,0x1000040000040000000004000108002200080ce3,0x1040041000840020100804200108002200080ce3,0xf3079800f4e60f3079800f3003db3000f3f300408c01e6f3000408c01e9cc1e60f3001e9cc007983ffb6,0x0,0x80028000022,0x180428084222,0x80028000022,0x180428084222,0x0,0x0,0x80028000022,0x2000000808000200020000008080000000000100080000120000001000800001200020000200000002000200002000400000200000000208000002010000002000000000793a8,0x80028000022,0x481028290862,0x80028000022,0x481028290862,0x1040041001008040201004200102002080081ce3,0x0,0x1040041001008040201004200104002100081ce3,0xf379803cde60079f9803cc1e60f379801e61e60f301e63cc07a73001e63cc03ccf300f6cc001e740995,0xf3079801e7e60f3079801e6003d39800f4e600408c03ccf3000408c03cfcc1e60f3003cfcc00f307cbb6,0x0,0x1000440012040080402004200108002200082ce3,0x1040040102040080402004280108002200082ce3],
[0x1000840022040080402004200108002200082de3,0x1040040402040080402004240108002200082ce3,0x1001040042040080402004000108002200082ee3,0x1050040402040080402004240108002200082ce3,0x1002040082040080402004080108002200082ce3,0x10180404020400804020040c0108002200082ce3,0x1004040102040080402004080108002200082ce3,0x0,0x0,0x0,0x1010040402040080402004040108002200082ce3,0x0,0x1020040802040080402004040108002200086ce3,0x0,0x0,0x1040041000080600010084200100082002080ce3,0x445800111600044580798004458000fa9800408c001f531e603cc001e605b20003cc1e603cc1e61556,0x1040041000100a00020104200100102004080de3,0x1040041000000200000004200100002000080ce3,0x0,0x0,0x1040041000000200000004200100402010080ce3,0x0,0x0,0x0,0x1040041000000200000004200101002040080ce3,0x0,0x1040041001008200201004200102002080081ce3,0x0,0x1040041001008200201004200104002100081ce3,0x0,0x0],
[0x1000440014040100804004200108002200084ce3,0x0,0x1000840024040100804004200108002200084de3,0x0,0x1001040044040100804004000108002200084ee3,0xf300003cde60079bcc1e61e607987980f30f3079801e7e6007a82301e9cc003db3000f6cc001ede5995,0x1002040084040100804004100108002200084ce3,0x0,0x1004040104040100804004100108002200084ce3,0x1000041004040100804004200108002200084ce3,0x0,0x0,0x1010040404040100804004040108002200086ce3,0x0,0x1020040804040100804004040108002200084ce3,0x1020040a04040100804004140108002200084ce3,0x1040041000040200000004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11628 : TreeBound (n := 4) 106 (programCode 0x442907407c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x481428294a62,0x481428284a62,0x481428294a62,0x481428284a62,0x0,0x10400410010008440240089002002080082413e4,0x481428294a62,0x10400410011008440240089002004080102a15e4,0x481428294a62,0x481428290a62,0x481428294a62,0x481428290a62,0x2040001000080002000004200102002080080ce3,0x0,0x0,0x0,0x0,0x480428294a62,0x480428284a62,0x480428284a62,0x480428284a62,0x79f9801e7e60079f980003cc3cc3cc0f303cc408c03ccf30007d4c03cc000000f3003cc007987985216,0x0,0x480428294a62,0x0,0x480428294a62,0x480428290a62,0x480428280a62,0x480428290a62,0x0],
[0x2b405cfec0000ad0173fb0002b3fbacfec0000ad0173fb0000acff6cfec0000ad0173fb000000159fd80159fd80567f60567f62b3fb0159fd80567f600567f60567f60567f600567f60572c5ec00159fdab3fb00159fe2cfec02df3ab02b3fb00567f62b3fb00000232672fb00159fdd67f6000159fd959fd8000036bc9ac00159fd959fd80b7ceac159fd800567f6159fd800005682ec73ef8d50ac,0x0,0x2b405cfec0000ad0173fb0002b3fbacfec0000ad0173fb0000acff6cfec0000ad0173fb000000159fd80159fd80567f60567f62b3fb0159fd80567f600567f60567f60567f600567f60572c5ec006c1f3ab3fb00159fe2cfec00567f602b3fb00567f62b3fb00000232672fb00159fd8acfec006c1f3ab3fb000008d3bfac00159fd82b3fb0159fd82b3fb000567f62b3fb000005682ec73ef8d50ac,0x0,0x481428294a62,0x480428284a62,0x480028200862,0x480428284a62,0x0,0x0,0x480028210862,0x0,0x480028210862,0x480028210862,0x480028200862,0x480028210862,0x2040001000100004000004200102002080080ce3,0xf379803cde60079f9803cc007aec801e9cc00445800204601edd4c25f8f301e63cc25f87981e60f8936,0x0,0xf379803cde60079f9803cc007a73001e9cc00445800204601edd4c4459e601e67984458f301e60f8936,0x10400410001008040240081002080082000211e4,0x0,0x0,0x0,0x0,0x10008400201008040240081002080082000211e4,0x10000400200008040240081002080082000000e4,0x10010400402008040240081002080082000413e4,0x79fd4c1e60f307983cc1ed983d39800f30798408c03ccf300f708c03cfcc1f53f3003cfcc00f307cbb6,0x10020400804008040240081002080082000815e4,0x7983cc1e60f6d3983cc1ed983d3b660f30798408c03ccf300f708c03cfcc1f57bf003cfcc00f6d3cbb6,0x7981e61e61e607981e61ed983db3000f30798408c03ccf300f708c03cfcc2046f3003cfcc01e616fbb6],
[0x0,0x7983cc1e60f307983cc1ed983d39800f30798408c03ccf300f708c03cfcc1f53f3003cfcc00f307cbb6,0x10008402201008040240081002080082000211e4,0x10100404020008840240181002080082006031e4,0x10000400000008040240081002080082000000e4,0x1020040804000904024028100208008200a051e4,0x10400410002008080240081002080082000413e4,0x79f9801e7e60079f983cc0003d39800f4e600408c03ccf31e6408c03cfcc1e60f3003cfcc00f307cbb6,0x10400410004008100240001002080082000804e4,0xf379800f4e60079f98437f947981e607a7300445886ffa1800408c01e9cc21c0bd001e9cc016c8b9f96,0x79f9801e7e60079f9800f3003db3000f3f300408c03ccf3000408c03cfcc1e60f3003cfcc01e616fbb6,0x0,0x481428294a62,0x480428284a62,0x480028200862,0x480428284a62,0x0,0x80200000400800001002000002008000002000004040000020800000080090000108000080040008002100000800200002000004201000080020000040080000100200010152e28,0x481028290862,0x2002000002008000020020000020080000200000100080000120000001000800001200020010200004002000200102000040000200100000208040002001000002004000202793a8,0x481428294a62,0x481028290862,0x480028200862,0x481028290862,0x1040041001008040201004200102002080081ce3,0x79f9801e7e60079f981e60003d39801116000408c03ccf31e6408c03cc79ad9079803cc7980f307cbb6,0x1040041001008040201004200104002100081ce3,0x79f9801e7e60079f980f30003d39801023000408c03ccf31e6408c03ccf325f83cc03ccf300f307cbb6,0x79f9801e7e60079f9801e6003d39800f4e600408c03ccf3000408c03cfcc1e60f3003cfcc00f307cbb6,0x79f9801e7e60079f983cc0003cc1e612fc000408c03ccf31f533cc03cfcc1e64bf003cfcc0003d3cbb6,0x0,0x79800f4e7e60079f98fa98004458000fa9800408c03ccf31e6408c03cfcc1e60f3003cfcc0f30814bb6],
[0x798007b660079f98008118004458000fa9800408c03ccf3000222c03cfcc1e60f3003cfcc0f30799556,0x10400406020008800240181002080082006031e4,0x79800f4e6003d39800fa98004458000fa9800408c03ccf3000408c03cfcc1e60f3003cfcc0f30814bb6,0x7983db4e6000079800fa98004458000fa9800408c03ccf300f708c03cfcc2d90f3003cfcc0f30814bb6,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x0,0x4220286418e2,0x79cfbc0f3001ed9d1b9418004458000811800408c4fbc79946e6ec51a5cc324ff3001e9cc13efa37726,0x4420286418e2,0x4620286418e2,0x4420286418e2,0x79f9801e7e60079f983cc0003cc00012fc000408c03ccf31e603cc03cfcc1e60f3003cfcc0000001556,0x0,0x0,0x0,0x0,0x79800f4e6003d39801023000408c001023000408c03ccf3000408c03cfcc1e60f3003cfcc0798448bb6,0x10000400240009000240001002080082008040e4,0x412028741902,0x4620286418e2,0x412028741902,0x4620286418e2,0x4220286418e2,0x10080410040009000240081002080082008051e4,0x4220286418e2,0x7983cc1e6003d3983dc23000408c001023000408c03ccf3000408c03cfcc1e60f3003cfcc0798448bb6,0x4420286418e2,0x4620286418e2],
[0x4420286418e2]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11757 : TreeBound (n := 4) 106 (programCode 0x442907407d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x2000480018040200402004200108002200082ce3,0x2040080108040200402004200108002200082ce3,0x2000880028040200402004200108002200082de3,0x2040080408040200402004280108002200082ce3,0x2001080048040200402004000108002200082ee3,0x2010080408040200402004080108002200082ce3,0x2002080088040200402004080108002200082ce3,0x0,0x20500800100c0002402004280108002200082ce3,0x10428040022,0x2050080020140004402004280108002200082de3,0x10428040022,0x10828040022,0x10828040022,0x10028040022,0x10828040022,0x10028040022,0x1e67981e6222c1e60003cc03ccf3079800003cd11601e67981e6f3001e9cc001f530007d4c001e8e9855,0x0,0x1e67981e6222c1e60f33cc03cd11679807983cd11601e67981e711601e9cc001f530007d4c001e8e9855,0x10028040022,0xa120285414c2,0xa128285414c2,0xa120285414c2,0x2004080108040200402004200108002200082ce3,0x1e67981e61e601e60003cc03ccf307983cc03ccf3001e67981e6f3001e9cc001f530007d4c001e8e9855,0x0,0x2008080208000600402004200100082002083ce3,0x0,0x2008080208000a00402004200100102004083de3,0x2008080208010200402004200102002080083ce3],
[0x0,0x1e607987981e61e603cfcc1e60f300f33cc03cc1e601e679807a73001e61e603db3000f379801e8ad195,0x2008080208010200402004200100402010083ce3,0x0,0x0,0x0,0x0,0x10a2b6e4001e60001e9cfcc00088b00012fc00044588512831e603cc00003ce1446b980001e6000001dc6,0x2008080208010200402004200102002080083ce3,0x0,0x2008080208010200402004200104002100083ce3,0x0,0x1e67981e61e601e60f33cc03ccf307983cc03ccf3001e67981e711601e9cc001f530007d4c001e8e9855,0x2010080408040200402004080108002200082ce3,0x2000080008040200402004000108002200082ce3,0x2020080808040200402004080108002200086ce3,0x2010080408040200402004080108002200082ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11806 : TreeBound (n := 4) 106 (programCode 0x442907407e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80000200010004004000002002000008000600000008800000006000000010000c0000020000010400000000201000000804000000410000004040000008100000010004853e27,0x800410018040020100804200108002200080ce3,0x0,0x800410018040000000004200108002200080ce3,0x4264000100010000400400000200200000802020120008080000004200000010000840240100000100400000000201000000804000001010000004040000008100000010004c7fe27,0x800410018040000000004200108002200080ce3,0xc00410010440010080404200108002200080ce3,0x800410018040000000004200108002200080ce3,0x800410010840020100804200108002200080ce3,0x0,0x0,0x0,0x666a400101000000400400000200200000a000333528000800004002000010000800666a410001000040000000020100000080400000101000000404000000810000001004487fe27,0xc00410010c40010080404200108002200080ce3,0x6a6a400102000000400400000200200000a0003535280008000100020000200010006a6a410002000040000000020100000080400000101000000404000000810000001008487fe27,0x0,0x1e600097e0007b66000b640004bf00012fc000408c3cc0f31e603cc3cc3cc1e60f303cc3cc03cc1e7556,0x0,0xee6c166b2807735940000ee7a0eb2800ee6fd017c81dcd68f5476a00001dcd6500003f5476a00002cb41780000773597b9aca01dcddc359400ee6b2801deb326500077447c8f565003ba23d59400775361650003c11ff94007753616500077acc994000ee6ba6e26e289,0x800810028040020100804200108002200080ce3,0xee6c166b2807735940000ee7a0eb2800ee6fd017c81dcd6caef40a00003b9aca00007aef40a0000861c4680000ee6b2f7359401dcddc359400ee6b2803bb89765000ee7a108f565003ba23d59400775361650003c11ff94007753616500077acc994000ee6f6fb15b729,0x800810028040000000004200108002200080ce3,0xee6c166b2807735940000ee7a0eb2800ee6fd017c81dcddc712eca0003b9aca000077712eca0003c893528000ee6b2f73594001dcddc359400ee6b283b9ca6d6500ee6c1688f565003ba23d59400775361650003c11ff94007753616500077acc994000ee6baa9c1ac89,0x800810028040000000004200108002200080ce3,0xc00810020440010080404200108002200080ce3,0x800810028040000000004200108002200080ce3,0x800810020840020100804200108002200080ce3,0x0,0x0,0x0],
[0xee6c166b2807735940000ee7a0eb2800ee6fd017c81faa3b8b9aca0ee6b280001dcd68b9aca0ee6c166b283b9acbdcd65000001dcddc359400ee6c166b29dcd68b9aca0ee88f565003ba23d59400775361650003c11ff94007753616500077acc994000ee7e5663db729,0xc00810020c40010080404200108002200080ce3,0xee6c166b2807735940000ee7a0eb2800ee6fd017c8218711db9aca1dcd6500003b9acdb9aca3b9ad8e6b28773597b9aca000001dcddc359400ee6d04d651dcd6c735940ee88f565003ba23d59400775361650003c11ff94007753616500077acc994000ee8d6a060dbc9,0x0,0x1e60011160003ea60012fc0004bf00012fc000408c3cc0f31e603cc3cc3cc1e60f303cc3cc03cc9813b6,0x0,0x0,0x8004284410a2,0x0,0x8004284410a2,0x8000284410a2,0x8008284410a2,0x8020284410a2,0x8008284410a2,0x8020284410a2,0x3cc03cc0003cc3cc0408c0000f30798000000000001e60001e600001e9cc001f530007d4c001e703855,0x0,0x3cc03cc0003cc3cc0408c0000f30798000000000001e60001e600001e9cc001f530007d4c001e703855,0x8000284410a2,0x8020284410a2,0x8020284410a2,0x8020284410a2,0x8040200000004000108002200080ce3,0x1e67981e60f301e60f33cc0004bf00012fc000408c3cc0f31e603cc3cc3cc1e60f303cc3cc03cc1e7556,0x0,0x1e66b973db666b28773595dcd6500000eee2614daca0007735940ee6ba2ef4495476ccb41780000773597b9ad261c4680000b2d09f314eeadf4fca00077447c8f565003b9aca00003b9ca6d65003ba23d5940077536165001dd4d85940077536165000eee25d94000ee6d0c85111c9,0x8104284410c2,0x0,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2],
[0x8108284410c2,0x8128285410c2,0x1e6007b66001e7e600798f3003db3000f3f300408c3cc0f3000408c3cc3cc1e60f303cc3cc03cc9906b6,0x0,0x1e6007b66001e7e600799e6003d39800f4e600408c3cc0f3000408c3cc3cc1e60f303cc3cc03cc9906b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2,0x4000108040200000004200108002200080ce3,0x1e601e7e601e61e601e9cc0004bf00012fc000408c3cc0f31e603cc3cc3cc1e60f303cc3cc03cc9bdfb6,0x0,0x40400010000800008008000001010040002000100000000c0000000300000000c0000020000010400000040201000000800000400400008000800004008000010010004850e27,0x0,0x0,0x8000208000200000004200100002000080ce3,0x0,0x1e600f4e61e601e600f6cc0004bf00012fc000408c3cc0f31e603cc3cc002046001e9cc001e9cc99db56,0x8000208000200000004200100402010080ce3,0x0,0x0,0x1e60799e61e601e6079bcc0004bf00012fc000408c3cc0f31e603cc3cc00f4e600f33cc00f33cca743b6,0x0,0x1e603cde61e601e603cfcc0004bf00012fc000408c3cc0f31e603cc3cc01e7e60079bcc01e63cc9fabb6,0x8000208000200000004200102002080080ce3,0x8000208000200000004200100002000080ce3,0x8000208000200000004200104002100080ce3,0x0,0x1e603cde600f31e603cfcc0004bf00012fc000408c3cc0f31e603cc3cc3cc1e60f303cc3cc03cc9fabb6,0x2010080408040200402004080108002200082ce3,0x8040200000004000108002200080ce3,0x4020100808040200804004100108002200084ce3],
[0x8040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_11903 : TreeBound (n := 4) 106 (programCode 0x442907407f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x4000500018040200804004200108002200084ce3,0x0,0x4002100108000600804004300100082002084ce3,0x4020100108060200804004300104002020084ce3,0x4002100108000a00804004300100102004084ce3,0x4000100108020200804004200104002100084ce3,0x4004100108040200804004200100202008084ce3,0x0,0x4004100108020200804004200100402010084ce3,0x800200000a0000000800200000c000000050000000140000001100000001080020000200040002000200002000400000080000000208000002010000002000000000593a8,0x4020100108040200804004300100802020084ce3,0x0,0x0,0x0,0x4004100108020200804004200102002080084ce3,0x4000100108020200804004200100002100084ce3,0x4000100108020200804004200104002100084ce3,0x7980001e61e603cc01e9cc0f30f307983cc0f3079801e7e6007a73001e7e6003d39800f6cc001ede5995,0x4000900028040200804004200108002200084de3,0x0,0x84c129204501,0x7983cc1e61e603cc3cc3cc0f30f307983cc0f3079801e7e6007aec801e7e6003d39800f30f301ede5995,0x84c129204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0xf3010230003ccf3012fc0004bf00012fc000408c1e60f31e603cc1e6003ea6000f4e6003d3983cf3b6,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x4001100048040200804004000108002200084ee3,0x4000100808040200804004100108002200084ce3,0x4002100088040200804004100108002200084ce3,0x7983cc1e62d903cc7983cc1e60f307983cc0f3079801e7e6007aec801e9cc003db3000f6cc001ede5995,0x4004100108040200804004200108002200084ce3,0x0,0x40021010800c0002804004300108002200084ce3,0x0,0x4002101080140004804004300108002200084ce3,0x0,0x4004101100240008804004208108002200084ce3,0xa20828541502,0x20028040022,0xa20828541502,0x20028040022,0x3cc1e60f31e603cc1e60f3003db3000f3f300408c01e6f3000408c01e9cc1e60f3001e9cc007983ffb6,0x0,0x7981e61e61e607981e61e6003d39800f4e600408c03ccf3000408c03cfcc1e60f3003cfcc00f307cbb6,0x0,0x8220286410e2,0x20028040022,0x8220286410e2,0x0,0x4008100208000600804004200100082002085ce3,0xacfec00159fdab3fb000567f6567f6000acfec2b3fb000567f8b3fb000567f62b3fb0005680b9fd80000000567f602b3fb0159fd80567f60567f60206fc4159fd80acfec0567f600567f60acfec0002b3fdb3fb0000acff167f60002b40067f600002b3fdb3fb0002b40067f600002b3fb00000000567f60000000159fdab3fb0002b3fb159fd80015b00fe20000159fd959fd80015b040949f50634ab,0x4008100208000a00804004200100102004085de3,0x4008100208020200804004200104002100085ce3],
[0x0,0x0,0x4008100208020200804004200100402010085ce3,0x1a947aec801e603cc007d4c00088b00012fc0004458d4a0f31e603cc000007cd2800f300003cc00001dc6,0x0,0x0,0x0,0x0,0x4008100208020200804004200102002080085ce3,0x0,0x4008100208020200804004200104002100085ce3,0x7980799e601e63cc03cfcc0f30f307983cc0f3079801e7e6007a73001e7e6003d39800f6cc001eed8995,0x0,0x0,0x0,0x0,0x0,0x7983cc1e60f307983cc1ed983d39800f30798408c03ccf300f708c03cfcc1f53f3003cfcc00f307cbb6,0xa20828541502,0x20028040022,0xa20828541502,0x20028040022,0xf303cc0f30f30f303cc0f3003db3000f3f300408c01e6f3000408c01e9cc1e60f3001e9cc007983ffb6,0x0,0x7983cc1e60f307983cc1e6003d39800f4e600408c03ccf3000408c03cfcc1e60f3003cfcc00f307cbb6,0x4020101802040080804004300108002200084ce3,0x8220286410e2,0x20028040022,0x8220286410e2,0x4010100408040200804004100108002200086ce3,0x4000100008040200804004000108002200084ce3,0x4020100808040200804004100108002200084ce3],
[0x4020100808040200804004100108002200084ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_12000 : TreeBound (n := 4) 106 (programCode 0x4429074080) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c021204481,0x0,0x10c021204481,0xc000200481,0x20c042208481,0xc000200481,0x20c042208481,0x0,0x0,0x3cc001023000408c7992fc0004bf00012fc000408c1e60f31e603cc1e600f4e600f31e600f37983cf3b6,0x0,0x3cc001023000408c7992fc0004bf00012fc000408c1e60f31e603cc1e601e7e600799e601e67983cf3b6,0x80c108220501,0x410018040200000004010100802010080ce3,0x80c108220501,0xc000200481,0x0,0x0,0x8084284410a2,0x0,0x8084284410a2,0x8084284410a2,0x8088284410a2,0x0,0x8088284410a2,0x1dcd6500010c388d0003bb8976500010c388d0000f047fe500010c388d0000773594000079126a500007735b1cd6579126a5000079126a8b9acbdcd65000001dcd68b9acbdcd650003bb89768b9ad17359400001dcd653b9ad173597b9acbdcd653b9ad173594ee6b2f73795844da,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x10c021204481,0x800028040200000004000100002020080ce3,0x10c021204481,0xc000200481,0x20c042208481,0xc000200481,0x20c042208481,0x800028040200000004000100002200080ce3,0x0,0x0,0x0,0x0,0x80c108220501,0x800028000200000004000100002010080ce3,0x80c108220501,0xc000200481,0x3cc001023000408c0012fc0004bf00012fc000408c1e60f31e603cc1e63cc1e60f301e63cc07983cf3b6,0x1000048040200000004000108002200080ce3,0x8040200000004000108002200080ce3,0x2000088040200000004000108002200080ce3,0x0,0x0,0x8104284410c2,0x0,0x8104284410c2,0x8108284410c2,0x8108284410c2,0x8120285410c2],
[0x8108284410c2,0x8128285410c2,0x3cc007a73001e9cc00798f3003db3000f3f300408c1e60f3000408c1e63cc1e60f301e63cc07983de6b6,0x0,0x3cc007a73001e9cc00799e6003d39800f4e600408c1e60f3000408c1e63cc1e60f301e63cc07983de6b6,0x8128285410c2,0x8120285410c2,0x8120285410c2,0x8120285410c2,0x0,0x0,0x8404284410a2,0x0,0x8404284410a2,0x8420284410a2,0x8408284410a2,0x8420284410a2,0x8408284410a2,0x8420284410a2,0x3cc1e60f3000408c1e600f3003db3000f3f300408c1e60f3000408c1e63cc1e60f301e63cc07983cf3b6,0x0,0x3cc1e60f3000408c1e601e6003d39800f4e600408c1e60f3000408c1e63cc1e60f301e63cc07983cf3b6,0x8420284410a2,0x8420284410a2,0x8420284410a2,0x8420284410a2,0x3cc01e6f301e63cc01e9cc0004bf00012fc000408c1e60f31e603cc1e63cc1e60f301e63cc07984c23b6,0x0,0x0,0x0,0x0,0x0],
[0x208008200240008040204008108002200080ee3,0x8000200040000000004000108002200080ce3,0x8010200440010000004010108002200080ce3,0x8000200040000000004000108002200080ce3,0x808020200840020100804020108002200080ce3,0x3cc7980f30079bcc79800f3003db3000f3f300408c1e60f3000408c1e63cc1e60f301e63cc079840bfb6,0x0,0x3cc7980f300f33cc79801e6003d39800f4e600408c1e60f3000408c1e63cc1e60f301e63cc0798448bb6,0x0,0x8000200040200000004000108002200080ce3,0x8100204040100000004100108002200080ce3,0x8000200040000000004000108002200080ce3,0x3cc03ccf300f33cc03cfcc0004bf00012fc000408c1e60f31e603cc1e63cc1e60f301e63cc0798448bb6,0x10000408040200000004000108002200080ce3,0x8040200000004000108002200080ce3,0x20000808040200000004000108002200080ce3,0x8040200000004000108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_10144 : TreeBound (n := 4) 106 (programCode 0x44290740) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part010_10145 part010_10258 part010_10499 part010_10628 part010_10757 part010_10934 part010_11047 part010_11048 part010_11257 part010_11386 part010_11483 part010_11628 part010_11757 part010_11806 part010_11903 part010_12000

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part010_0 : TreeBound (n := 4) 106 (programCode 0x442907) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part010_1 part010_2 part010_1027 part010_1028 part010_2165 part010_2166 part010_2167 part010_2168 part010_3017 part010_3018 part010_3947 part010_5276 part010_6557 part010_7614 part010_8879 part010_10144

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned010 : TreeBound (n := 4) 106 [((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨0,1,true⟩)] := part010_0
open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem zero_one_return_0_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 0, Stmt.write 1 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 106 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,0,false⟩),((2,0), ⟨0,1,true⟩)] := by
    intro k m h
    simp only [Program.get] at h
    split at h
    next hk =>
      subst k
      cases Option.some.inj h
      simp [ongoing,h0]
    next =>
      split at h
      next hk =>
        subst k
        cases Option.some.inj h
        simp [ongoing,h1]
      next =>
        split at h
        next hk =>
          subst k
          cases Option.some.inj h
          simp [ongoing,h2]
        next => contradiction
  rcases partitioned010 M hm with h | h
  · exact h
  · exact (h halts).elim

end BeaverBound


/- Exact residual adapter: Hanan Beer (@hananzlt).
Residual specification and freeze reduction: @pageman, PR6963, adapting
@henry10101001. All existing verifier and certificate attribution above is retained.
This proves only the named auxiliary return-state branch. -/
open Turing Turing.BusyBeaver
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1.H1 := by
  intro M h0 h1 h2 hRun _hUsed _hForm _hMissing _hLoop hHalts
  have stopped := BeaverBound.zero_one_return_0_machine M h0 h1 h2 hHalts
  change M.multiStep (Machine.init []) 107 = none at stopped
  obtain ⟨q,t,live⟩ := hRun
  rw [live] at stopped
  contradiction
