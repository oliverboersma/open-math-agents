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
private def L5 (a : Fin 2) (x : Fin 47) : Fin 47 :=
  Fin.ofNat 47 (((30655717824374062551910937084627588235288321424589970181169231565455271897174522602467740418449112009141951846301109653048702175456516071540101566342562755140281908863040 : ℕ) >>> (6*(2*x.val+a.val))) % 64)
private def preL5 (x : Fin 47) : List (Fin 2 × Fin 47) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,5),(1,5),(0,8),(1,8),(0,10),(1,10),(0,16),(1,16),(0,19),(1,19),(0,20),(1,20),(0,23),(1,23),(0,24),(1,24),(0,26),(1,26),(0,29),(1,29),(0,30),(1,30),(0,36),(1,36),(0,39),(1,39),(0,40),(1,40),(0,43),(1,43),(0,44),(1,44)]
  | 9 => [(0,6)]
  | 10 => [(1,6)]
  | 11 => [(0,7)]
  | 12 => [(1,7)]
  | 13 => [(0,9)]
  | 14 => [(1,9)]
  | 15 => [(0,11),(0,41)]
  | 16 => [(1,11),(1,41)]
  | 17 => [(0,12),(0,42)]
  | 18 => [(1,12),(1,42)]
  | 19 => [(0,13)]
  | 20 => [(1,13)]
  | 21 => [(0,14)]
  | 22 => [(1,14)]
  | 23 => [(0,15)]
  | 24 => [(1,15)]
  | 25 => [(0,17)]
  | 26 => [(1,17)]
  | 27 => [(0,18)]
  | 28 => [(1,18)]
  | 29 => [(0,21),(0,45)]
  | 30 => [(1,21),(1,45)]
  | 31 => [(0,22),(0,46)]
  | 32 => [(1,22),(1,46)]
  | 33 => [(0,25),(0,35)]
  | 34 => [(1,25),(1,35)]
  | 35 => [(0,27),(0,37)]
  | 36 => [(1,27),(1,37)]
  | 37 => [(0,28),(0,38)]
  | 38 => [(1,28),(1,38)]
  | 39 => [(0,31)]
  | 40 => [(1,31)]
  | 41 => [(0,32)]
  | 42 => [(1,32)]
  | 43 => [(0,33)]
  | 44 => [(1,33)]
  | 45 => [(0,34)]
  | 46 => [(1,34)]
  | _ => []
private def R5 (a : Fin 2) (x : Fin 17) : Fin 17 :=
  Fin.ofNat 17 (((193107347534193383863513766012999607066827692279840 : ℕ) >>> (5*(2*x.val+a.val))) % 32)
private def preR5 (x : Fin 17) : List (Fin 2 × Fin 17) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2),(1,2),(0,4),(1,4),(0,5),(1,5),(0,7),(1,7),(0,10),(1,10),(0,11),(1,11),(0,13),(1,13),(0,15),(1,15),(0,16),(1,16)]
  | 5 => [(0,3)]
  | 6 => [(1,3)]
  | 7 => [(0,6)]
  | 8 => [(1,6)]
  | 9 => [(0,8)]
  | 10 => [(1,8)]
  | 11 => [(0,9)]
  | 12 => [(1,9)]
  | 13 => [(0,12)]
  | 14 => [(1,12)]
  | 15 => [(0,14)]
  | 16 => [(1,14)]
  | _ => []
private def contexts5 : Tree (Context 47 17) :=
packedTree 13 0x991000000000000000000000000000000000000000000000000088d000000000000000000000000000000000000000000000000079c8000000000000000000000065b00000000000000000000000589800000000000000000000000000000000000000000000000044d000000000000000000000003998000000000000000000000032f00000000000000000000000000000000000000000000000000f60000000000000000000000004280000000000000000000000000d746b0153ca65d24a84739e997cba65bd2c995f4a7243b1d38b9c31a0c700b8013f29f7efa57cfb811ab4d17673323d7eabba5a629993ee9ab4d125a92be915468a18104e7b839f1b80d8867e339994cc9656b19d0c4452c25b11706c42840f405080d802e01000356ee9e54399c14b825832558d641fe006fc17d135f59f4c3c5b9a80d346961469a0a4efe6d833a994082e2da12405e41b801f00454fa7d52d490d415df6ad3b5dea7292a07f035b991c52814000a5252564fd764fa618e2e329021cbd9d468870f54410cacaa4 8 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional5 : TreeBound (n := 4) 106 [((0,1),⟨1,1,true⟩),((3,0),⟨0,0,true⟩),((1,1),⟨3,1,true⟩),((2,1),⟨1,0,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := by
  apply sparse_bound _ L5 R5 preL5 preR5 contexts5
  all_goals decide +kernel


private def L6 (a : Fin 2) (x : Fin 17) : Fin 17 :=
  Fin.ofNat 17 (((193107347534193384196580295642691884648162165622816 : ℕ) >>> (5*(2*x.val+a.val))) % 32)
private def preL6 (x : Fin 17) : List (Fin 2 × Fin 17) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2),(1,2),(0,4),(1,4),(0,5),(1,5),(0,7),(1,7),(0,9),(1,9),(0,11),(1,11),(0,13),(1,13),(0,15),(1,15),(0,16),(1,16)]
  | 5 => [(0,3)]
  | 6 => [(1,3)]
  | 7 => [(0,6)]
  | 8 => [(1,6)]
  | 9 => [(0,8)]
  | 10 => [(1,8)]
  | 11 => [(0,10)]
  | 12 => [(1,10)]
  | 13 => [(0,12)]
  | 14 => [(1,12)]
  | 15 => [(0,14)]
  | 16 => [(1,14)]
  | _ => []
private def R6 (a : Fin 2) (x : Fin 45) : Fin 45 :=
  Fin.ofNat 45 (((228906565552802019579166636341413465007638499216745572074942411268900706924832666754066782603629904640864008949182232497163216252401305773901836004524885675876416 : ℕ) >>> (6*(2*x.val+a.val))) % 64)
private def preR6 (x : Fin 45) : List (Fin 2 × Fin 45) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2),(1,2),(0,4),(1,4),(0,8),(1,8),(0,9),(1,9),(0,12),(1,12),(0,16),(1,16),(0,18),(1,18),(0,19),(1,19),(0,24),(1,24),(0,28),(1,28),(0,29),(1,29),(0,32),(1,32),(0,34),(1,34),(0,37),(1,37),(0,38),(1,38),(0,44),(1,44)]
  | 5 => [(0,3)]
  | 6 => [(1,3)]
  | 7 => [(0,5),(0,39)]
  | 8 => [(1,5),(1,39)]
  | 9 => [(0,6),(0,40)]
  | 10 => [(1,6),(1,40)]
  | 11 => [(0,7)]
  | 12 => [(1,7)]
  | 13 => [(0,10)]
  | 14 => [(1,10)]
  | 15 => [(0,11)]
  | 16 => [(1,11)]
  | 17 => [(0,13)]
  | 18 => [(1,13)]
  | 19 => [(0,14)]
  | 20 => [(1,14)]
  | 21 => [(0,15)]
  | 22 => [(1,15)]
  | 23 => [(0,17)]
  | 24 => [(1,17)]
  | 25 => [(0,20)]
  | 26 => [(1,20)]
  | 27 => [(0,21),(0,41)]
  | 28 => [(1,21),(1,41)]
  | 29 => [(0,22),(0,42)]
  | 30 => [(1,22),(1,42)]
  | 31 => [(0,23),(0,43)]
  | 32 => [(1,23),(1,43)]
  | 33 => [(0,25),(0,35)]
  | 34 => [(1,25),(1,35)]
  | 35 => [(0,26),(0,36)]
  | 36 => [(1,26),(1,36)]
  | 37 => [(0,27)]
  | 38 => [(1,27)]
  | 39 => [(0,30)]
  | 40 => [(1,30)]
  | 41 => [(0,31)]
  | 42 => [(1,31)]
  | 43 => [(0,33)]
  | 44 => [(1,33)]
  | _ => []
private def contexts6 : Tree (Context 17 45) :=
packedTree 13 0xb598002cb6000b028002b04000a970002a0e0009ee000000000093c00023e80008910001ffa00079e8001d7800075600000000007478001ce2000672800192400061180014c000044a00000000003558000d0a00011f000043a0000880000066000000db46d77665b08d64aa85513a764ef25271f68994445fa8ef57593a6dd26e7967ab29989ea6f44c21f90e2697314089024a0490175b1ec4b573a78cec63defe975b3a61cd8c7d4c021d8d04139018d9d6a332147913a154fe6a002ad7ea230cd61174f21114ea2 7 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional6 : TreeBound (n := 4) 106 [((3,1),⟨3,0,true⟩),((1,1),⟨3,1,false⟩),((3,0),⟨0,1,false⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := by
  apply sparse_bound _ L6 R6 preL6 preR6 contexts6
  all_goals decide +kernel


private def L7 (a : Fin 2) (x : Fin 15) : Fin 15 :=
  Fin.ofNat 15 (((708921629009941129008363181152940560 : ℕ) >>> (4*(2*x.val+a.val))) % 16)
private def preL7 (x : Fin 15) : List (Fin 2 × Fin 15) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,5),(1,5),(0,8),(1,8),(0,9),(1,9),(0,10),(1,10),(0,12),(1,12),(0,13),(1,13),(0,14),(1,14)]
  | 9 => [(0,6)]
  | 10 => [(1,6)]
  | 11 => [(0,7)]
  | 12 => [(1,7)]
  | 13 => [(0,11)]
  | 14 => [(1,11)]
  | _ => []
private def R7 (a : Fin 2) (x : Fin 15) : Fin 15 :=
  Fin.ofNat 15 (((708921629009941129008363181152940560 : ℕ) >>> (4*(2*x.val+a.val))) % 16)
private def preR7 (x : Fin 15) : List (Fin 2 × Fin 15) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,5),(1,5),(0,8),(1,8),(0,9),(1,9),(0,10),(1,10),(0,12),(1,12),(0,13),(1,13),(0,14),(1,14)]
  | 9 => [(0,6)]
  | 10 => [(1,6)]
  | 11 => [(0,7)]
  | 12 => [(1,7)]
  | 13 => [(0,11)]
  | 14 => [(1,11)]
  | _ => []
private def contexts7 : Tree (Context 15 15) :=
packedTree 11 0x2d0d4d946002243f172a0015caaf43c000e501500390a76c69746b4d341d201759e15ab205f268f230d 5 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional7 : TreeBound (n := 4) 106 [((3,1),⟨1,1,true⟩),((1,1),⟨1,0,false⟩),((3,0),⟨0,1,true⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := by
  apply sparse_bound _ L7 R7 preL7 preR7 contexts7
  all_goals decide +kernel


private def L8 (a : Fin 2) (x : Fin 39) : Fin 39 :=
  Fin.ofNat 39 (((459514853384110293777775906085846185494215760233999436586893949873831964406528569062574821959105985566907751557542330739827139381626808311872 : ℕ) >>> (6*(2*x.val+a.val))) % 64)
private def preL8 (x : Fin 39) : List (Fin 2 × Fin 39) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4)]
  | 9 => [(1,4)]
  | 10 => [(0,5),(1,5),(0,10),(1,10),(0,12),(1,12),(0,15),(1,15),(0,16),(1,16),(0,22),(1,22),(0,25),(1,25),(0,26),(1,26),(0,29),(1,29),(0,30),(1,30),(0,36),(1,36)]
  | 11 => [(0,6),(0,27)]
  | 12 => [(1,6),(1,27)]
  | 13 => [(0,7),(0,28)]
  | 14 => [(1,7),(1,28)]
  | 15 => [(0,8)]
  | 16 => [(1,8)]
  | 17 => [(0,9)]
  | 18 => [(1,9)]
  | 19 => [(0,11)]
  | 20 => [(1,11)]
  | 21 => [(0,13)]
  | 22 => [(1,13)]
  | 23 => [(0,14)]
  | 24 => [(1,14)]
  | 25 => [(0,17),(0,31)]
  | 26 => [(1,17),(1,31)]
  | 27 => [(0,18),(0,32)]
  | 28 => [(1,18),(1,32)]
  | 29 => [(0,19),(0,33)]
  | 30 => [(1,19),(1,33)]
  | 31 => [(0,20),(0,34)]
  | 32 => [(1,20),(1,34)]
  | 33 => [(0,21),(0,35)]
  | 34 => [(1,21),(1,35)]
  | 35 => [(0,23),(0,37)]
  | 36 => [(1,23),(1,37)]
  | 37 => [(0,24),(0,38)]
  | 38 => [(1,24),(1,38)]
  | _ => []
private def R8 (a : Fin 2) (x : Fin 19) : Fin 19 :=
  Fin.ofNat 19 (((404974786343223364162374038892912043380809749671603963936 : ℕ) >>> (5*(2*x.val+a.val))) % 32)
private def preR8 (x : Fin 19) : List (Fin 2 × Fin 19) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,5),(1,5),(0,8),(1,8),(0,9),(1,9),(0,10),(1,10),(0,12),(1,12),(0,13),(1,13),(0,15),(1,15),(0,17),(1,17),(0,18),(1,18)]
  | 9 => [(0,6)]
  | 10 => [(1,6)]
  | 11 => [(0,7)]
  | 12 => [(1,7)]
  | 13 => [(0,11)]
  | 14 => [(1,11)]
  | 15 => [(0,14)]
  | 16 => [(1,14)]
  | 17 => [(0,16)]
  | 18 => [(1,16)]
  | _ => []
private def contexts8 : Tree (Context 39 19) :=
packedTree 13 0x2daa000a9180028c40009ec00026c000095200023c20008c380021c20007eb8001d8e0006d6000183a0005c90001678ad454400014640004da800128a00048380011c80004228000e766c231f00005ca00013980003b60000b480001b800002b800004c013000dbaeb9749ea174dc259d1fd8cac5960acf4b73eb235752b54562292939496149823ad1927cd33517785182270c1047413003b005d7868a53248e8c291d74bbb589282126a8d33888a903340b100cd3ea4ccf9a5bea6310362620264eb9a488f90ac45bcbe8a73 7 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional8 : TreeBound (n := 4) 106 [((3,1),⟨3,1,true⟩),((1,1),⟨1,0,false⟩),((3,0),⟨0,1,true⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := by
  apply sparse_bound _ L8 R8 preL8 preR8 contexts8
  all_goals decide +kernel


private def L9 (a : Fin 2) (x : Fin 19) : Fin 19 :=
  Fin.ofNat 19 (((404974786343223364162118567999797448081296717577921333280 : ℕ) >>> (5*(2*x.val+a.val))) % 32)
private def preL9 (x : Fin 19) : List (Fin 2 × Fin 19) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4),(1,4),(0,5),(1,5),(0,8),(1,8),(0,9),(1,9),(0,11),(1,11),(0,12),(1,12),(0,13),(1,13),(0,15),(1,15),(0,17),(1,17),(0,18),(1,18)]
  | 9 => [(0,6)]
  | 10 => [(1,6)]
  | 11 => [(0,7)]
  | 12 => [(1,7)]
  | 13 => [(0,10)]
  | 14 => [(1,10)]
  | 15 => [(0,14)]
  | 16 => [(1,14)]
  | 17 => [(0,16)]
  | 18 => [(1,16)]
  | _ => []
private def R9 (a : Fin 2) (x : Fin 33) : Fin 33 :=
  Fin.ofNat 33 (((35873327714033726263786485812798259831123425578490053148534765326214332846345001277835045150861923534032615598346477632 : ℕ) >>> (6*(2*x.val+a.val))) % 64)
private def preR9 (x : Fin 33) : List (Fin 2 × Fin 33) :=
  match x.val with
  | 0 => [(0,0)]
  | 1 => [(1,0)]
  | 2 => [(0,1)]
  | 3 => [(1,1)]
  | 4 => [(0,2)]
  | 5 => [(1,2)]
  | 6 => [(0,3)]
  | 7 => [(1,3)]
  | 8 => [(0,4)]
  | 9 => [(1,4)]
  | 10 => [(0,5)]
  | 11 => [(1,5)]
  | 12 => [(0,6)]
  | 13 => [(1,6)]
  | 14 => [(0,7),(1,7),(0,8),(1,8),(0,9),(1,9),(0,14),(1,14),(0,18),(1,18),(0,19),(1,19),(0,20),(1,20),(0,23),(1,23),(0,24),(1,24),(0,32),(1,32)]
  | 15 => [(0,10),(0,25)]
  | 16 => [(1,10),(1,25)]
  | 17 => [(0,11),(0,26)]
  | 18 => [(1,11),(1,26)]
  | 19 => [(0,12),(0,27)]
  | 20 => [(1,12),(1,27)]
  | 21 => [(0,13),(0,28)]
  | 22 => [(1,13),(1,28)]
  | 23 => [(0,15),(0,29)]
  | 24 => [(1,15),(1,29)]
  | 25 => [(0,16),(0,30)]
  | 26 => [(1,16),(1,30)]
  | 27 => [(0,17),(0,31)]
  | 28 => [(1,17),(1,31)]
  | 29 => [(0,21)]
  | 30 => [(1,21)]
  | 31 => [(0,22)]
  | 32 => [(1,22)]
  | _ => []
private def contexts9 : Tree (Context 19 33) :=
packedTree 13 0x245600090d00023b91cb8aa00020260007fe8001a2ed0665c800191e00062180016aeb4d5a100015a40005608001440a0f4fd8000bd60002ed0000aae52328a00008c000022780008863d31e2000069200017880005a42b715300004ee00003b8000048014000ccde43b1ea8b1c05e000d2565eb2798acbde5a4ace9588a2e5051bdcbba56628f14208a44451e40d5c67c2e215a0a280f6037003c8a63a3008686320d6a2ad050a97a4a9645e1eb8d185861cf0104849c22bfe55c974888e2ed036452167c50b147b2b87809ef 7 0
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem exceptional9 : TreeBound (n := 4) 106 [((3,0),⟨0,1,false⟩),((0,1),⟨0,0,true⟩),((3,1),⟨0,1,true⟩),((2,1),⟨3,1,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := by
  apply sparse_bound _ L9 R9 preL9 preR9 contexts9
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
  | 6 => decide (tb = [((0,1),⟨1,1,true⟩),((3,0),⟨0,0,true⟩),((1,1),⟨3,1,true⟩),((2,1),⟨1,0,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)])
  | 7 => decide (tb = [((3,1),⟨3,0,true⟩),((1,1),⟨3,1,false⟩),((3,0),⟨0,1,false⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)])
  | 8 => decide (tb = [((3,1),⟨1,1,true⟩),((1,1),⟨1,0,false⟩),((3,0),⟨0,1,true⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)])
  | 9 => decide (tb = [((3,1),⟨3,1,true⟩),((1,1),⟨1,0,false⟩),((3,0),⟨0,1,true⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)])
  | 10 => decide (tb = [((3,0),⟨0,1,false⟩),((0,1),⟨0,0,true⟩),((3,1),⟨0,1,true⟩),((2,1),⟨3,1,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)])
  | _ => false

set_option maxHeartbeats 0 in
private theorem exceptionalCheck_sound (v : ℕ) (tb : Program 4)
    (h : exceptionalCheck v tb = true) : TreeBound 106 tb := by
  unfold exceptionalCheck at h
  split at h
  next =>
    have ht : tb = [((0,1),⟨1,1,true⟩),((3,0),⟨0,0,true⟩),((1,1),⟨3,1,true⟩),((2,1),⟨1,0,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := of_decide_eq_true h
    rw [ht]
    exact SparseReaders.exceptional5
  next =>
    have ht : tb = [((3,1),⟨3,0,true⟩),((1,1),⟨3,1,false⟩),((3,0),⟨0,1,false⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := of_decide_eq_true h
    rw [ht]
    exact SparseReaders.exceptional6
  next =>
    have ht : tb = [((3,1),⟨1,1,true⟩),((1,1),⟨1,0,false⟩),((3,0),⟨0,1,true⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := of_decide_eq_true h
    rw [ht]
    exact SparseReaders.exceptional7
  next =>
    have ht : tb = [((3,1),⟨3,1,true⟩),((1,1),⟨1,0,false⟩),((3,0),⟨0,1,true⟩),((2,1),⟨3,0,true⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := of_decide_eq_true h
    rw [ht]
    exact SparseReaders.exceptional8
  next =>
    have ht : tb = [((3,0),⟨0,1,false⟩),((0,1),⟨0,0,true⟩),((3,1),⟨0,1,true⟩),((2,1),⟨3,1,false⟩),((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := of_decide_eq_true h
    rw [ht]
    exact SparseReaders.exceptional9
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
private theorem part012_2 : TreeBound (n := 4) 106 (programCode 0x4c29075111) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080430204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3 : TreeBound (n := 4) 106 (programCode 0x4c29075112) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000084002118004200100c82020080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4 : TreeBound (n := 4) 106 (programCode 0x4c29075113) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080430204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5 : TreeBound (n := 4) 106 (programCode 0x4c29075114) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080400200481,0x1080442208481,0x1080400200481,0x1080442208481,0x1080421204481,0x10804a4214481,0x10804e721c481,0x10804a4214481,0x1080400200481,0x0,0x16c800111600016c80003cc1e6408c0004fbe04601e7e601e61e601e679801e600f33ea6001e7037c5,0xf379840caa600f37980003ea600408c0004dd804601e7e601e61e601e7e6001ee8bf37b66001e703855,0x140005000090002022004080100102080080de3,0x0,0x420000002080000010200000010800000004a0600002001000010800000012818040000200200001001000008001000008000080004040000040140c00040400000100108535a7,0x8040001000090002002004080100002080080ce3,0xfa98002046000fa980003cde60408c0004fda7e601e7e601e61e601e679801e60f303ea6001e7037c5,0x16c80005b200016c80003cc1e6408c0004fbe04601e7e601e61e601e679801e600f33ea6001e7037c5,0x40200000800800001002000001008000000040002000804000001080000001240084000020080000400100000800100000801000000404000001012004004040000010030851da7,0x0,0x0,0x2040001000090002002004080100002080080ce3,0x0,0x0,0x0,0x0,0x0,0x80088204022],
[0x180488284222,0x180488284222,0x180488284222,0x240009000084002110804200100882020080ce3,0x281888204c82,0x80088204022,0x281888204c82,0x481088204862,0x481088204862,0x80088204022,0x481088204862,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c80003cc97e3f99000482dbac01e67981e63cc01e6f3001e604bf3e2c801e707485,0x7983cc1e6003d3980004bf00012fc0003cc079801e7e60079bcc01e600003cc0000f4e6001e64d995,0x1400050000a0002024004100100102100080de3,0x401010000a0002004004100100002100080ce3,0x0,0x0,0xfa98003ea6000fa980003cde603ea600044769cc01e6f301e63cc01e6f3001e9db307a73001e703855,0x400030000a0002004004100100002100080ce3,0x3d39803cde6003d3980003ea7e63f1f800464004601e6f301e63cc01e6f3000f7bff37aafc01e703345,0xf30798003ea610237980003cde603ea600044769cc01e6f301e63cc01e6f3001e9db307a73001e703855,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x80088204022,0x180488284222,0x180488284222,0x180488284222,0x0,0x281888204c82,0x80088204022,0x281888204c82,0x481088204862,0x481088204862,0x80088204022,0x481088204862,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_86 : TreeBound (n := 4) 106 (programCode 0x4c29075115) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080461208481,0x10804e4208481,0x1080461208481,0x1080440208481,0x1080442208481,0x10804e7208481,0x1080442208481,0x1080463208481,0x10804e4208481,0x10804e7208481,0x10804e4208481,0x1080442208481,0x0,0xf30000b6400088b0000798408c003cc3cc05efb4e601e7e601e61e601e601e60f31e603cc1e61e8e92b5,0xf30079bcc007a730079800408c003cc3cc05b201e601e7e601e61e601e601e61e61e607981e61e8e9855,0xf30000b640004bf0000f30408c003cc3cc05efb4e601e7e601e61e601e601e60f31e607981e61e8eb1a5,0xf300f33cc03ccf304bf000408c003cc3cc05efb4e601e7e601e61e601e601e60f31e603cc1e61f0812b5,0x4000001010000004040000008100000008000230100000808000001000200001000020000100080000400100000800100000800020001000080004000100010000100010054c7ffa7,0x400032101000008004000000010000000000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005087ffa7,0xf3000408c0010230007980408c003cc3cc05efb4e601e7e601e61e601e601e60f31e603cc1e61e8e92b5,0xf30000b641e60f30000798408c003cc3cc05b201e601e7e601e61e601e601e61e61e607981e61e8e9855,0x400001001000004004000008010000008000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005487ffa7,0x400021101000000804000000410000000000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005087ffa7,0x400001001000004004000010010000010000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005cc7ffa7,0x400030101000008004000000210000000000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005087ffa7,0xf300f33cc0f30f300f3000408c003cc3cc05efb4e601e7e601e61e601e601e60f31e603cc1e61e8e92b5,0x400020001000080004000200010000000000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005087ffa7,0xf300f33cc03ccf301e6000408c003cc3cc05efb4e601e7e601e61e601e601e60f31e603cc1e61ecb52b5,0x400020001000080004000200010000000000023010000080800000100020000100002000010008000040010000080010000080002000100008000400010001000010001005087ffa7,0x0,0xf30000b6400088b00007983cde603cc3cc05b2000f31e9cc01e600f31e601e61e61e607981e61e703855],
[0x8004200100081002008004000100202008080ce3,0xf300012fc0004bf0000f303cde603cc3cc05b2000f31e9cc01e600f31e601e61e61e607981e61e703855,0x0,0x8001200040081002158004020100202008080ee3,0xf3084d1040000f3000000114334e0f33cc03cc1099ae9bcc007980001e607983cc0798f301e61e64dcf5,0x8002200080081002158004020100202008080ee3,0xf30000b641e60f300007983cde603cc3cc05b20f3001e9cc01e600f31e601e61e61e607981e61e703855,0x8004200100081002008004000100202008080ce3,0xf3088ac340098d30000001152a1a1e63cc03cc1115149bea60f300001e607983cc0f30f301e61e6ceea5,0x8008200200081002048004008100202008080ee3,0xf3088ac340010230000001152a1a1e63cc03cc1115149bdb30f300001e607983cc0f30f301e61e6ceea5,0xf300f33cc0f30f300f3000408c003cc3cc05b201e601e9cc01e61e601e601e61e61e607981e61e8e9855,0xf307983cc1e60f3000000111bb201e63cc03cc0f30079bcc00f300001e607983cc0f30f301e61e6ceea5,0xf301e63cc0798f301e60004458003cc3cc05b203cc01e9cc01e63cc01e601e61e61e607981e61eacf855,0xf307983cc1e60f3000000111bb201e63cc03cc0f30079bcc00f300001e607983cc0f30f301e61e6ceea5,0x0,0xf30000b6400088b00007984458003cc3cc062c76cc01e67981e63cc01e601e61e61e603cc1e61ead3485,0x400001001000004004000002010000020000023010000081000000100020000100002000010008000040020000080020000080002000100008000400010001000010001009487ffa7,0xf30000b640002d90000f304458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61eacf2b5,0xf301e63cc0798f302d90004458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61eacf2b5,0x0,0xf301e63cc0000f30981cc04458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61eacf2b5,0xf3000408c001f5300079804458003cc3cc062c74e601e6f301e63cc01e601e60f31e607981e61eacf345,0x0,0xf3001e9cc01e6f3001e6004458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61eacf2b5,0xf3001e9cc001f5307c1c404458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61eacf2b5,0x0,0x4000301010000100040000002100000000000230100000810000001000200001000020000100080000400200000800200000800020001000080004000100010000100010094c7ffa7,0xf300f33cc0f30f300f30004458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61f44d2b5,0x0,0xf300f33cc03ccf301e60004458003cc3cc062c74e601e67981e63cc01e601e60f31e603cc1e61ecb52b5,0x0],
[0x0,0x8000600010081002048004008100202008080ee3,0x8004200100081002058004002100202008080ee3,0x8000a00020081002048004008100202008080ee3,0x0,0x8001200040081002008004000100202008080ce3,0xf307983cc0010230000000798f300f33cc03cc0f3003cfcc007980001e603cc3cc0798f301e61e64db45,0x0,0xf307983cc0012090000798798f300f33cc03cd023003cfcc007980799e603cc3cc0798f301e61e6554c5,0x8004200100081002058004002100202008080ee3,0xf30883a4c0098d3000000111d79a1e63cc03cc0f36ac9bcc3db300001e607983cc0f30f301e61e6ceea5,0x8008200200081002058004002100202008080ee3,0x8001200000081002008004000100202008080ce3,0x0,0xf307983cc1e60f3000000111bb201e63cc03cc0f30079bcc00f300001e607983cc0f30f301e61e6ceea5,0x0,0xf307983cc1e60f3000000111bb201e63cc03cc0f30079bcc00f300001e607983cc0f30f301e61e6ceea5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_167 : TreeBound (n := 4) 106 (programCode 0x4c29075116) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000080002008004200108002000080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_168 : TreeBound (n := 4) 106 (programCode 0x4c29075117) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080461208481,0x10804e4208481,0x1080461208481,0x1080440208481,0x1080442208481,0x10804e7208481,0x1080442208481,0x1080463208481,0x10804e4208481,0x10804e7208481,0x10804e4208481,0x1080442208481,0x0,0xf30000b6400088b00007984bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1ee9b2b5,0xf30079bcc01e6f300798004bf0003cc79805b201e601e7e601e61e601e603cc1e60f307983cc1ee9b855,0xf30000b640002d90000f304bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1ee9b2b5,0xf300f33cc0f30f304bf0004bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1f0812b5,0x0,0xf303cc3cc318a830c626404bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1ee9b2b5,0xf30007d4c00102300079804bf0003cc79806a6e7e601e7e601e61e601e603cc1e607983cc3cc1ee9b7c5,0xf30000b641e60f307987984bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1ee9b2b5,0x0,0xf30079bcc001f53083b4404bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1ee9b2b5,0xf3003cfcc007a73003cc004bf0003cc79806a6e7e601e7e601e61e601e603cc1e607983cc3cc1ef14fc5,0xf303cc3cc001f530c626404bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1ee9b2b5,0xf300f33cc0f30f300f30004bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1f0812b5,0x0,0xf300f33cc03ccf301e60004bf0003cc79806e49ae601e7e601e61e601e601e60f307983cc3cc1f44d2b5,0x0,0x0,0x80088200022],
[0x180488284222,0x80088200022,0x180488284222,0x240009000082002190804220100201010080ca3,0x281088218c82,0x80088200022,0x281088218c82,0x481088210862,0x481088210862,0x80088200022,0x481088210862,0x0,0x0,0x0,0x0,0x0,0xf30000b6400088b0000798408c003cc798066b1ae601e67981e63cc01e601e60f307983cc3cc1e8e92b5,0xf30079bcc01e6f30097e004458003ccb64062d67e601e6f301e63cc01e601e60f30f307983cc1eacf345,0xf30000b640004bf0000f304458003ccb64062d67e601e6f301e63cc01e601e60f30f307983cc1ead11a5,0xf301e63cc03ccf302d9000408c003cc798066b1ae601e67981e63cc01e601e60f307983cc3cc1ecb52b5,0x0,0xf301e63cc0000f309859804458003ccb64062d67e601e6f301e63cc01e601e60f30f307983cc1eacf345,0xf3000408c0010230007980408c003cc798066b1ae601e67981e63cc01e601e60f307983cc3cc1e8e92b5,0x0,0xf3001e9cc01e6f3001e6004458003ccb64062d67e601e6f301e63cc01e601e60f30f307983cc1eacf345,0xf30079bcc001f53079f9804458003cc79805b203cc01e6f301e63cc01e603cc1e60f307983cc1eacf855,0xf3001e9cc007a73003cc00408c003cc798066b1ae601e67981e63cc01e601e60f307983cc3cc1e962ab5,0xf301e63cc001f5307980004458003cc79805b203cc01e6f301e63cc01e603cc1e60f307983cc1eacf855,0xf300f33cc0f30f300f3000408c003cc798066b1ae601e67981e63cc01e601e60f307983cc3cc1e8e92b5,0x0,0xf300f33cc03ccf301e6000408c003cc798066b1ae601e67981e63cc01e601e60f307983cc3cc1ecb52b5,0x0],
[0x0,0x80088200022,0x180488284222,0x80088200022,0x180488284222,0x0,0x281088218c82,0x80088200022,0x281088218c82,0x481088210862,0x481088210862,0x80088200022,0x481088210862,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_249 : TreeBound (n := 4) 106 (programCode 0x4c29075118) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000080402018004200108002002080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_250 : TreeBound (n := 4) 106 (programCode 0x4c29075119) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10804b0210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_251 : TreeBound (n := 4) 106 (programCode 0x4c2907511a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000080002008004200100402000080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_252 : TreeBound (n := 4) 106 (programCode 0x4c2907511b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10804b0210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_253 : TreeBound (n := 4) 106 (programCode 0x4c2907511c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_254 : TreeBound (n := 4) 106 (programCode 0x4c2907511d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c80003cc1e63db3000408ed9001e9cc01e6f3001e679800fa98003d39801e7032b5,0xf37983cc1e600f37980003ea6003db30004274d9001e9cc01e6f3001e679801ed980079f9801e703855,0x16c800097e00025f80003cc3cc3db30004fc2a5001e9cc01e6f3001e679800fa980079f9801e7051a5,0x0,0x16c80014e200053880003cc97e3db300040957e0f4e600f4e6000f4e679801ed98003d39801e707485,0x0,0x25f800097e00025f80003cc3cc3db30004fbfcc0f4e6007b66001e7e679800fa980079f9801e7051a5,0x40001000090002000004000102002080080ce3,0x240009000090002040204008102002080080ee3,0x40001000090002000004000102002080080ce3,0x440011000090002080404010102002080080ce3,0x0,0xf379803cde600f37980003ea6003db30004273e9cc1e63cc1e603cc1e679801ed980079f9801e703855,0x440011000090002080404220102002080080ce3,0x0,0x0,0x0,0x40001000090002000004200102002080080ce3,0x0,0x40001000090002000004200102002080080ce3,0x20200000080800000102000000108000000230100000800080001020000001000040000100100000400400000801000000802000001008000004010000010010000010014c7ffa7,0x8040001000090002008004200102002080080ce3,0x8118002046000fa980003cde603db30005f0b53001e9cc01e6f3001e679800fa98003d39801e7032b5,0x16c83cc1e600016c80003cc1e63db3000408ed9001e9cc01e6f3001e679801ed980079f9801e703855,0x20020000080080000100200000100800000021321200080080000102000000100004000010010000040040000080100000080200000100800000401000001001000001001487ffa7,0xf30798003ea600007980003cc0003db30003cc0f3001e9cc01e6f3001e679801ed980079f9801e703855,0x0,0x4085b0220501,0x4205b0220501,0x4085b0220501,0x0],
[0x4105b0220501,0x1040040610090002618004200102002080083ce3,0x4105b0220501,0x1040040010090002618004200102002080083ce3,0x4205b0220501,0x4785b0220501,0x4205b0220501,0x4685b0220501,0x4405b0220501,0x4785b0220501,0x4405b0220501,0x4685b0220501,0x2040001000090002008004200102002080080ce3,0x0,0x808510220501,0x820510220501,0x808510220501,0x0,0x810510220501,0x2040080400090002408004200102002080082ce3,0x810510220501,0x2040080010090002408004200102002080082ce3,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0xf3007d4c00798f3007983cde603db30005f0b53001e9cc01e6f3001e679801ed98003d39801e7037c5],
[0x804080100090002408004200102001080082ca3,0xf3007d88c03dc2300f303ec4603db300060f339001e9cc01e6f3001e679800fa980079f9801e703345,0x0,0x2e81020040090002518004200102002080082ee3,0x1c7ae3d3cc222c0000000012bf4001f530003cc0f30079bcc00f3f3001e7e6003cfcc00f379801e870925,0x2c82020080090002518004200102002080082ce3,0xf30000ba4aa6000f3007983cde603db30005b20f3001e9cc01e6f3001e679801ed980079f9801e703855,0x804080100090002408004200102001080082ca3,0x1e1ab2ce2e601e6000000012f33841f530003cc0f30079bcc00f3f3001e7e6003cfcc00f379801e870925,0x1004080200090002408004200102001080083ca3,0x840510220501,0x840510220501,0x510220501,0x840510220501,0x510220501,0x0,0x808510220501,0x820510220501,0x808510220501,0x4020101000090002808004200102002080084ce3,0x810510220501,0x0,0x810510220501,0x0,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501],
[0x0,0x808510220501,0x920530220501,0x808510220501,0x0,0x0,0xf30d4a3cc222c0000000012828001f530003cc0f30079bcc00f3f3001e7e6003cfcc00f379801e870925,0x0,0x1c7a79a3989e63ea60007992bf4001f530003cc0f30079bcc00f3f3001e7e6003cfcc00f379801e870925,0x920530220501,0xf307af04c001e6000000012828001f530003cc0f30079bcc00f3f3001e7e6003cfcc00f379801e870925,0x920530220501,0x40510220501,0x40510220501,0x510220501,0x40510220501,0x510220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_367 : TreeBound (n := 4) 106 (programCode 0x4c2907511e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1000080220022,0x10000812210a2,0xf30000b6400088b00007983cc3cc3cc79805b20001e7e6007b66001e7e603cc1f530007983cc1e7056b5,0x10000812210a2,0x1000084220022,0x1021082220c82,0x1000080220022,0x1021082220c82,0x1000084220022,0x1000084220022,0x1000080220022,0x1000084220022,0xf30000b6400088b00007984bf0003cc79805b201e601e7e601e61e601e603cc1f530007983cc1ee9b855,0x0,0xf30000b6400088b00007984458003cc79805b203cc01e6f301e63cc01e603cc1f530007983cc1ead3515,0x0,0xf30811bcc01e6f3003cc011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x0,0x8000a00020082002090084002108002010080ce3,0x0,0xf300012fc0004bf0000f303cc3cc3cc79805b20001e7e6007b66001e7e603cc1f530007983cc1e7056b5,0x0,0x8000a00020082002040204008108002010080ee3,0x8000a00020082002000004000108002010080ce3,0x8000a00020082002080404010108002010080ce3,0x8000a00020082002080404002108002010080ce3,0x8000a00020082002190804020108002010080ce3,0x8000a00020082002080404020108002010080ce3,0x8000a00020082002291004040108002010081ce3,0x8000a00020082002080404010108002010080ce3],
[0xf300012fc0004bf0000f304bf0003cc79805b201e601e7e601e61e601e603cc1f530007983cc1ee9d6b5,0x0,0xf300012fc0004bf0000f304458003cc79805b203cc01e6f301e63cc01e603cc1f530007983cc1ead16b5,0x0,0x0,0x1dcd650000f5de817b9acbdcd650000f5de817b9adac388d00003b9acab2d06ce6b46bbd3e1aca07735a2e6b2f735cf9aca0b2d15b51da9dd11eaca077447ab28001dd11eaca01dd11eaca001dd11f23d594000f047fe5000eee25f70d65f047fe5000ee6b29dcd65ee6d0ce58cd19,0xf300012fc00088b0000f30f3f44e7b998f300f30028d3d9083f8980fa98f307983cca73e098007d51426,0x0,0xf300012fc00088b0000f30f3f4301b998f300f30027e0d90fd78981ed98f307983cc980e098007d51426,0x1dcd65001dd4d8597b9acbdcd65001dd4d8597b9cac6cd2f0007735940b2d23e8ffe8bc0f7c76a0773597b9ad17394daca00b2dfbfa1c459b059acaee6c166b2803b9b059aca3b9b059aca03b9b05a23d594000f047fe5000eee27d3e3b5f047fe5000ee6b45cd650ee6d0c6e573d9,0x800060002010406c20020d008342001080361ba4,0x1dcd65000eee25d97b9acbdcd65000eee25d97b9e894322f000ee6b280b2d41b664e8bf8d8e4ca0773597b9ad17712eca000b3c2868e54135cf9aca7736826b2807735cf9aca7735cf9aca07735cfa23d594000f047fe5000eee43c47265f047fe5000ee6d04d6500ee6d0c6e573d9,0x800060002010406c20020d0103420010803e1fa4,0xf30811bcc01e6f3003cc011160001e600003cc00f307981e60f303cc1e9cc003db3000f300001e68a925,0x80006000201040042008008203220008804221a4,0x4000000110000000140000001100000001000081001000201000000810014002010010000800000020400500028004000204001000200001000a000100008000100000011000f93a8,0x80006000201040042008008403220008804221a4,0x0,0x0,0x0,0x0,0x8001200040084002118004200108002020080ce3,0xf307983cc1e60f300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x8002200080084002118004200108002020080ce3,0x0,0x1011886220c82,0x1011881221d02,0x0,0x1011881221d02,0x1011884220c82,0x1011882220c82,0x1011886220c82],
[0x1011882220c82,0x1011884220c82,0x1011884220c82,0x1011886220c82,0x1011884220c82,0x40002001100000000c000200010000000080023010000012000000100040000180002000010001000008010000080010000080402000101000000104000001000020001011087d3a7,0x0,0x0,0x0,0x8004200100080002008004200108002000080ce3,0xf3086085c001f5300000011481241e600003cc0f30079bcc00f3f3001ea3024bdba980f300001e68a925,0x8008200200080002008004200108002000080ce3,0x8000200000080002008004200108002000080ce3,0x0,0x90002400090002418004200100402080082ce3,0x2c90020400090002518004200102c82080082ce3,0x1f5300088b0001f530003cc3cc3db30005b3f53001e9cc01e6f3001e679801e60f3079f9801e7056b5,0x0,0x20100000080400000100800000100800000231110000800080001020000001000040000100100000400400000801000000802200001008000004000400010010000010014c7ffa7,0x8010000400090002008004200108002080080ce3,0x7a73001f53000f3f30003ce0463dd16005f86b9001e9cc01e6f3001e679800f3f3003d48b01e7032b5,0x8010002400090002418004200108402080082ce3,0x4405b0234501,0x410080400090002408004200102802080082ce3,0x4405b0234501,0x840510220501,0x840510220501,0x840510220501,0x840510220501,0x40510220501,0xf307983cc1e60f300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x0],
[0xa00028000a0002818004200100402100084ce3,0x40200208000a0002808004200104002100084ce3,0x204600081180020460003cc3cc3ea60005b3f53001e9cc01e6f3001e6f3001e60f307a73001e7056b5,0x0,0x0,0x0,0xf4e6001e9cc00f4e60003ce0463dd1600672de9001e9cc01e6f3001e6f3001e6f3003d48b01e7037c5,0x0,0x4405b0234501,0x3cc1e6003d3990231e60003cde603ea60005b20f3001e9cc01e6f3001e6f3001f9fe307a73001e703855,0x4405b0234501,0x840510220501,0x840510220501,0x840510220501,0x840510220501,0x40510220501,0xf307983cc1e60f300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_480 : TreeBound (n := 4) 106 (programCode 0x4c2907511f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c80003cc7983ea600044608b001e9cc01e6f3001e6f3001e7e6003db3001e707485,0x0,0x5085b0220501,0x4205b0220501,0x5085b0220501,0x2211000a0002808004200102001100084ca3,0x0,0x0,0xf3007983cc1e6f30079803cde603ea60005b20f3001e9cc01e6f3001e6f3001e9cc007a73001e703855,0x0,0x4205b0220501,0x3cc07983cc1fc2a2c4bd83cde603ea60006913e9001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x4205b0220501,0xd685b0220501,0xc405b0220501,0x40201208000a0002808004200102001100084ca3,0xc405b0220501,0xd685b0220501,0x16c80005b200025f80003cc1e63ea6000482aa5001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x402010000a0002008004200104002100080ce3,0x0,0x4200000080800000102000000108000000040010000800200001040000001182c80004020000080400000100800000100800800000401000000804000002020000010031a50ca7,0x4200000080800000102000000108000000040800000800200001040000001122401000020004000400400000800040000800800000402000001008000004020000010031851da7,0x4200000080800000102000000108000000040002000800200001040000001182980004020000010400000040800000200800400000201000000804000002020000010031840ca7,0x2400090000a0002040204008104002100080ee3,0x2400090000a0002040204008104002100080ee3,0x2400090000a0002040a04008104002100080ee3,0x2400090000a00020c0404010104002100080ee3,0x4200000080800000102000000108000000040010000800200001040000001182c80004020000080400081200800204900800800000401000000804000002020000010031a50ca7,0x42000000808000001020000001080000000410000008002000010400000011ca880400020008000400010000800010000800400000201000000804000002020000010031840ca7,0x0],
[0x0,0x2400090000a0002044004008104002100080ee3,0x0,0x0,0x0,0x0,0x0,0xfa98003ea605ce0080003cde603ea6000485b0e0f4e600f4e6000f4e679800f4e6003db3001e7032b5,0xf307980001e6000079800044580011160003cc0f3001e9cc007983cc1e7e6003d39800f3f3001e64d995,0xfa98003ea603dd8f80003cde603ea6000447a2c1e7e6007b66001e7e6f3001e9cc007a73001e703855,0x400010000a0002000004000104002100080ce3,0x2a4260000010080000040200000000800000021521200080080000104000000100000020010000080040000100080000100080200000100800000402000001002000001001487ffa7,0x400010000a0002000004000104002100080ce3,0xf379803cde606e32c80003ea6003ea60004a8566799e601e7e600f31e679800f4e6003db3001e7032b5,0x41002000000208000000820000202080000000440000001001000010400000011010080800200000100800800008000001008020000010020000010200000100200000100108713a7,0x400010000a0002000804020104002100080ce3,0x6b2a60000000080000000200000000800000023595200010000000104000000100006b2a410010000008000080080000000080200000100800000402000001002000001001087f3a7,0x0,0xf307980001e6000079800044580011160003cc03cc01e6f3007980001e7e6003d39800f3f3001e64d995,0x0,0x0,0x0,0x0,0x8118003ea6000fa980003cde603f9900062d753001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x0,0x40002000000018000000060000000180000000440000001000080010400000011000c00000200010000804000008000500008020000010020000010200000100200000100108713a7,0x0,0x400030000a0002000004000104002100080ce3,0x2400030000a0002040204008104002100080ee3,0x400030000a0002000004000104002100080ce3,0x4400030000a0002080404010104002100080ce3],
[0x0,0x16c80005b200016c80003cc1e63ea60004825e9cc1e63cc1e603cc1e679800f4e6003db3001e7032b5,0x6b2a60000000180000000200000001800000023595200010000000104000000100006b2a410010000008000080080000000080200000100800000402000001002000001001087f3a7,0x16c800111600016c80003cc7983ea6000445f9f981e60f31e607981e6f3001e7e6003db3001e707485,0x400030000a0002004004000104002100080ce3,0x16c80005b200016c80003cc1e63ea6000482604601e7e601e61e601e679800f4e6003db3001e7032b5,0x0,0x400030000a0002004004100104002100080ce3,0x0,0x3d39803cde6003d3980003ea6003ea60004a8659001e9cc01e6f3001e679800f4e6003db3001e7032b5,0xf30798003ea61629f480003cde603ea60006913e9001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x0,0x4085b0220501,0x4205b0220501,0x4085b0220501,0x8040412000a0002918004200102001100084ca3,0x4105b0220501,0x0,0x4105b0220501,0x0,0x4205b0220501,0x4785b0220501,0x4205b0220501,0x4685b0220501,0x4405b0220501,0x4785b0220501,0x4405b0220501,0x4685b0220501,0x0,0x808510220501,0x820510220501,0x808510220501],
[0x40201018000a0002808004200102001100084ca3,0x810510220501,0x0,0x810510220501,0x0,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0x808510220501,0x820510220501,0x808510220501,0x0,0x810510220501,0x20400804000a0002408004200104002100082ce3,0x810510220501,0x20400800100a0002408004200104002100082ce3,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0x418e307a73001e6f300798445800111600044d459001e9cc007a73001e7e6003d39800f3f3001ea19995],
[0x1001000a0002808004200102001100084ca3,0x43b0f1e6f300799e600f30445800111600044d459001e9cc007a73001e7e6003d39800f3f3001ea3bc55,0x0,0x10200400a0002008004200104002100080ce3,0x680034001000000000000200000000000000023400000010000000104000000100004000010010000008040000080100000080200000100800000402000001002000001001087f3a7,0x20200800a0002008004200104002100080ce3,0x6b2a6001100000000810020000002000008002359520001020000010400000011200c000010010000008040000080100000080200000100800000402000001002000001001087f3a7,0x40001000a0002008004200104002100080ce3,0x20200800a0002008004200104002100080ce3,0x50081002000a0002a18004200104002100085ce3,0x840510220501,0x840510220501,0x510220501,0x840510220501,0x510220501,0x0,0x808510220501,0x820510220501,0x808510220501,0x40201010000a0002808004200104002100084ce3,0x810510220501,0x0,0x810510220501,0x0,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501],
[0x0,0x808510220501,0x920530220501,0x808510220501,0x0,0x0,0x400034001000000000000200000000000000023400000010000000104000000100004000010010000008040000080100000080200000100800000402000001002000001001087f3a7,0x0,0x600020011000000008000200002000000080023400000010000000104000000100004000010010000008040000080100000080200000100800000402000001002000001001087f3a7,0x920530220501,0x7980798f301e63cc01ea08c1e60f303cc3cc0f3f3084e7cc01e6f3003d1eee0463cc79803cc1e60f4dc6,0x920530220501,0x40510220501,0x40510220501,0x510220501,0x40510220501,0x510220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_657 : TreeBound (n := 4) 106 (programCode 0x4c29075120) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000600010080002008004200108002000080ce3,0x4000000110000000440000000900000000e0030100100000400000100400000001004000310190000010040000000100000100200030018800000000800200002000000200017fda8,0x0,0x108410200481,0x230010000880000001000080001400060030100100000400000100400000001004000310190000010040000000100000100200030018800000000800200002000000200017fda8,0x108410200481,0x0,0x0,0xf307983ed57608118003ccf40abb7985b20f3f3084e7cc02d9f300798f31e60798855e73001e77d266,0x0,0xf307987b99420fa98003ccf40ca17985b20f3f3084e7cc02d9f300798f31e60798865173001e77d266,0x408430204481,0x7983cc1e813903d44e41e60f409c87983cc0f3f3084e7cc02d9f300798f31e6079884e4f300f316df66,0x408430204481,0x8410200481,0x808510220501,0x0,0x808510220501,0x8410200481,0x0,0x400020011000000044000000010000000200022000000080000000100000000100000002010000008040000010080000010080400000100000000404000001000000001001087ffa7,0xf3000222c00088b0000f30f4e76cbd399e600f30029c5e607b6d980fa99e60f30798d4bf53000811d936,0x0,0xf3000222c00088b0000f30f4e76cbd399e600f3004825e60f4ed981ed99e60f30798b65f53000811d936,0xf307af04c005c13000798111bb201e679803cc001e679803ccf300799e9d7643db5d90f303cc1e68a925,0x8000a000201080482002090082040011000613e4,0x0,0x8000a000201080102004020102040021000a05e4,0xf3000222c00088b0000f30f4e6003d3980000f300000000000000f30799e60000798001f530007985756,0x8000a000201080002008000202040001000201e4,0x0],
[0x8000a000201080042010008402040009008241e4,0x0,0x0,0x0,0x0,0x0,0x1021084220862,0x8001200040084002118884020108002020080ce3,0x0,0xf303cc3cc2f76f300799e601e77bb0799e600f300489d8010416001ed99e60f30798b640f30f30799c76,0x1021084220862,0x1021082220c82,0x1021084220862,0x1021082220c82,0x1021084220862,0x1021084220862,0x1021084220862,0x1021084220862,0x0,0x8001200040084002118004020108002020080ce3,0x0,0x8001200040080002008004000108002000080ce3,0xf307983cc1e60f300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x0,0x1000080220022,0xf303cc3cc3528f303cc1e600f4a940799e600f3002baa0008b89000fa98f30f30798d4a0f30f30799766,0x0,0xf303cc3cc2d90f303cc1e601e76c80799e600f30048240010416001ed99e60f30798b640f30f30799c76,0x1000084220022,0x1031882220c82,0x1000080220022,0x1031882220c82],
[0x1000084220022,0x1000084220022,0x1000080220022,0x1000084220022,0x0,0x0,0x0,0x0,0xf3079a22c1e64bf00007991160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x8004200100080402018004200108002002080ce3,0xf307a76cc001f5300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x8008200200080402018004200108002002080ce3,0x8000200000080002008004200108002000080ce3,0x0,0x140430204481,0x8c90020400084002118004200108882020080ce3,0x140430204481,0x0,0x0,0x8010000400080002008004200108002000080ce3,0x0,0x8010002400080402018004200108082002080ce3,0x4404b0214481,0x410000400080002008004200108002000080ce3,0x4404b0214481,0x40410200481,0x840510220501,0x840510220501,0x840510220501,0x40410200481,0xf307983cc1e60f300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x0],
[0x140430204481,0x222c000904bcc0f301e600f4a95ed99e600f3f30d4b2fc1209f300798f31e60798d4b0230f30799766,0x140430204481,0x408c0010237981e601e601e76cbd399e600f3f30b643cc1116f300799e61e60798b65f530f30799c76,0x0,0x0,0x0,0x0,0x4404b0214481,0x0,0x4404b0214481,0x40410200481,0x840510220501,0x840510220501,0x840510220501,0x40410200481,0xf307983cc1e60f300000011160001e600003cc0f30079bcc00f3f3001e9cc003db3000f300001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1 : TreeBound (n := 4) 106 (programCode 0x4c290751) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part012_2 part012_3 part012_4 part012_5 part012_86 part012_167 part012_168 part012_249 part012_250 part012_251 part012_252 part012_253 part012_254 part012_367 part012_480 part012_657

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_771 : TreeBound (n := 4) 106 (programCode 0x4c29075211) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10818e1204481,0x10818c6204481,0x10818e1204481,0x10818e1204481,0x10818c2204481,0x10818c6204481,0x10818c2204481,0x10818c6204481,0x10818c4204481,0x10818c6204481,0x10818c4204481,0x10818c6204481,0x0,0xc0003000414020112004080100082002080ce3,0x440021000414020102004080100082002080ce3,0x140005000414020132004080100082002080de3,0x0,0xfa98007b66000811803cc20470274583cc0003cc03cde601e61e601e600799e603cc79803cde703a05,0x8040021000414020102004080100082002080ce3,0xfa98003ea6000fa9803cc20460f74583cd1347e601e7e601e61e601e6003cde603cc79803cde703855,0x840021000414020102004080100082002080ce3,0x840021000414020102004080100082002080ce3,0x4000200000100800002402000009008000020001200002008000008012000900048004000020080000400040000200100000800000400400008002000004008000010010024852e27,0x8020000080080000080200000200800000080080004000600002808800040026101000008001000008010000080010000080000100040000100400001000400001001003085b1a7,0x2840021000414020102004080100082002080ce3,0x0,0x0,0x0,0x0,0x0,0x180488284222],
[0x180488284222,0x180488284222,0x180488284222,0x240009000406030180804220100081002080ca3,0x8040031000406030180c04200100081002080ca3,0x180488284222,0x8040031000406030180c04200100081002080ca3,0x580488294a62,0x480488294a62,0x180488284222,0x480488294a62,0x0,0x0,0x0,0x0,0x0,0xc0003000424020114004100100082002080ce3,0xf3798003ea600f379803cc20460f55f83cc99c9cc01e6f301e63cc01e6003cde603cc79803cde703855,0x140005000424020134004100100082002080de3,0xc0101000424020114004100100082002080ce3,0x0,0x0,0xfa98003ea6000fa9803cc20460f55f83cc99c9cc01e6f301e63cc01e6003cde603cc79803cde703855,0x40021000424020104004100100082002080ce3,0x840021000424020104004100100082002080ce3,0x840221000424020104004100100082002080ce3,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x180488284222,0x180488284222,0x180488284222,0x180488284222,0x0,0x8040031000406030180c04200100081002080ca3,0x180488284222,0x8040031000406030180c04200100081002080ca3,0x580488294a62,0x480488294a62,0x180488284222,0x480488294a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_852 : TreeBound (n := 4) 106 (programCode 0x4c29075212) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_853 : TreeBound (n := 4) 106 (programCode 0x4c29075213) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10818e1204481,0x10818c6204481,0x10818e1204481,0x10818e1204481,0x10818c2204481,0x10818c6204481,0x10818c2204481,0x10818c6204481,0x10818c4204481,0x10818c6204481,0x10818c4204481,0x10818c6204481,0x0,0xc0003000414020132004080100102004080de3,0x440021000414020102004080100102004080ce3,0x140005000414020122004080100102004080de3,0x0,0xfa98007b66000811800f320464496a640a1894cc03cde601e61e601e6003ccf300f33cc0799e703465,0x8040021000414020102004080100102004080ce3,0xfa98003ea6000fa9803cc20460f74583cd1347e601e7e601e61e601e600799e601e67980799e703855,0x840021000414020102004080100102004080ce3,0x840021000414020102004080100102004080ce3,0x0,0x8020000080080000080200000200800000080080004000600000808800040026101000008001000008010000080010000080000080040000800400000800400002001003085b1a7,0x2840021000414020102004080100102004080ce3,0x0,0x0,0x0,0x0,0x0,0x180488280222],
[0x180488280222,0x80488280222,0x180488280222,0x240009000404020100804200100102004080ce3,0x420000008080000010200000010800000004040000080100000101000000101000400030008000010010000012a100004000404001081000080004040002010000008828451fa8,0x180488280222,0x0,0x580488284a62,0x480488284a62,0x180488280222,0x480488284a62,0x0,0x0,0x0,0x0,0x0,0xc0003000424020134004100100102004080de3,0x3d3980113460102a9800f320464469164099f12e603cc7981e63cc01e6003ccf300f33cc0799e703465,0x140005000424020124004100100102004080de3,0x140101000424020124004100100102004080de3,0x0,0x0,0x8118002046000fa9800f320464469164099f12e603cc7981e63cc01e6003ccf300f33cc0799e703465,0x40021000424020104004100100102004080ce3,0x840021000424020104004100100102004080ce3,0x840221000424020104004100100102004080ce3,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x180488280222,0x180488280222,0x80488280222,0x180488280222,0x0,0x42000000808000001020000001080000000404000008010000010100000010100080005000200001002000000aa200004000810000282000100008100008020000020829051fa8,0x180488280222,0x4368200000100800040002000004208000022021b4001000210000400200042080004368010010000040000400080100000080000200100000800400000400200002001001087fca7,0x580488284a62,0x480488284a62,0x180488280222,0x480488284a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_934 : TreeBound (n := 4) 106 (programCode 0x4c29075214) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10818e1204481,0x1081084210481,0x10818e1204481,0x1081080200481,0x1081082208481,0x1081084210481,0x1081082208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0xb7ceac000000afb2bb0000000206fc40000002df3ab0000000614f4c000000081bf10000159fe2dabc427f60000ae58c033fb6185b7835b67f60ae6fb755800adabbec15cb5b511de3897b000567f8b3fb000567f60567f6000acff6cfec00159fd959fd8002b3fb159fd8002b3fb567f60002b3fb0000567f6adabbec000005680b9fd8000acfec000acfec2b7057a60000159fdd7398d8a296b,0x0,0x0,0x0,0x0,0x4340200000400800040002000100008000434021a0001000200400000200040080002000010008000040010000080010000080634000100100000400100000204100001001087fca7,0x568a2fec0000015cb17b000000adabbec000015a28bfb000002b4a7fec000002b6aefb0000159fd80ad0427f60000acfec2b3fbad34cf9c0567f60ad0019fd80000acfec15a0034d33e9b3fb000567f8b3fb000567f60567f6000acff6cfec00159fd959fd8002b3fb159fd8002b3fb567f60002b3fb002b3fb00adabbec000005680b9fd8000acfec0567f6015a02e7f60000159fdd72ebd9e302b,0x0,0x0,0x0,0x0,0x4340200000400800000402000100008000434021a0001000200400000200040080002000010008000040010000080010000080634000100100000400100000204100001001087fca7,0x0,0x0,0x0,0x0,0x0,0x180488284222],
[0x180488284222,0x180488284222,0x180488284222,0x240009000804020100804200100802020080ce3,0x240009000088002202000c802001010040313e4,0x180488284222,0x440011000088002202000c802001020040305e4,0x580488284a62,0x480488284a62,0x180488284222,0x480488284a62,0x0,0x0,0x0,0x0,0x0,0x2200000008800000012000000018000422037b5a01000210c00002200042080002000010008000040004000080020000080280300100200000400000400201000001001087fca7,0x4340200000100800040002000004008000434021a0001000200400000200040080002000010008000040004000080020000080634000100200000400100000201100001001087fca7,0x1ebbd02800012a05f20001ebbd0280003f5476a00004a817cf92aa806ef7112e1d3a1da81dcd68bba74591e5724d517394daf02f29683b9ad1735940ee7a0eb283b9ae7cd6503b9ae7cd6503b9e83b8bb787b59403b9b05a23d594077359403b9bb888f565000ee6d0d72c71d9,0xee6b36e6b2800003b9aca1dcd73e6b2800003b9aca7735a2e6b2f9126e1d3b6a4800ee6b2801dcd68b9ca6d65003b9ad17394dacaee6b283b9ad1735940ee7a0eb283b9ae7cd6503b9ae7cd6503b9e83aca00773594000003ba23d594077359400000ee88f565000ee6d0c845bf59,0x0,0x0,0x20200000080800000042000000208000424021a0001000200400000200040080002000010008000040004000080020000080282400100200000400008000201000001001087fca7,0x4340200000100800000002000004008000434021a0001000200400000200040080002000010008000040004000080020000080634000100200000400100000201100001001087fca7,0x0,0x0,0x1ebbd02800012a05f20001ebbd02800012a05f20000861c46800007753616501dcf41d6500077536165007753616500077536341d6501dcd65003b9acc71d94901dcd65000ee6b6577a0501dcd65000ee6b45cd65ee6b2f73594ee6b2f735a3d51da80000ee6b639accefef75a,0x0,0x0,0x0,0x0,0x0],
[0x0,0x180488284222,0x180488284222,0x180488284222,0x180488284222,0x0,0x240009000088002204000d002001010040313e4,0x180488284222,0x440011000088002204000d002001020040305e4,0x580488284a62,0x480488284a62,0x180488284222,0x480488284a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1015 : TreeBound (n := 4) 106 (programCode 0x4c29075215) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1016 : TreeBound (n := 4) 106 (programCode 0x4c29075216) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1081081218481,0x1081084210481,0x1081081218481,0x1081084210481,0x1081082210481,0x1081084210481,0x1081082210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x0,0x1021088210481,0x0,0x0,0x1011088218481,0x1021088210481,0x1011088218481,0x8040200100804020102004080100802020080ce3,0x1021088210481,0x1021088210481,0x1021088210481,0x1021088210481,0x0,0x159fd800acfec567f600159fd959fd80567f60567f600159fd959fd800acfec567f6000acfec000005684c7f600000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f759fd800acff167f602c99d92bcf3800000ae5b717b002b3fc6f9d5800ad146131fd80159fd80015a02e8a2fec02b6aefb00000ad098fec000002b3fb02b962f75aafe76458bd959fd8056a12b48de49ff2c,0x0,0x159fd80159fd8567f600acfec159fd802b3fb0567f600acfec159fd80159fd8567f600159fd8000005684c7f600000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acff167f60360fc7abcf3800000ae6e5d58002b3fcb07ce000ad146aa7ec00159fd80015a28c05cfec02b6aefb00000ad098fec000002b3fb02b962f75ad5bf1e58bd959fd8056d73ae4de49ff2c,0x0,0x0],
[0x168f08f99ba565decd903e39ed1e135abe8f99cb41a4a78643e39c0000168f08f8e75a3c29875e3e39c0000168f08f8e70b478a219eaec94e70000168f09ad8c65ded76ed254121691352880000b47847ca09e11f49fe11f1ce000005a3c23e3f63c23e39c016b683489b48b847c73800000b4785e7dbb489ac15e1795903e39d68f08f8e7000002d1e1795903e39c2d1e12085d08f8e9d1e6c2df1e39c016907243b2b253a1a41d1846e26a5269071e9768e70168f09532323e39cb47847c73800002d1e11f1ce000002d1e29eb32e1519e380d,0x168f08f8e70000ba1c0a0571c0002e8702815c70000ba1c0a0571c000b5e13856c670000ba1c0a0571c00017f7f98875700001c343427b04e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f14406c30ebc7c73ad1e12a6465e564c406ba9919795903e39d68f08f8e9d1e121eec1795903e39c2d1e11f1d3a3c2410ba6c2df1e39c0168f08f8e7000005a41ceb28d0788469071e9768e70168f09532323e39d68f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x0,0x159fd80b314790f14e02f791943c53800b7d98153f6002df66054fd80bde44f6f3ce0002b3fb000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056965b5d0e57df2c,0x159fd80000056d5df60000015b577d800005684c7f60000015b577d800000ad553f6000000acfec002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056965c0a0d17df2c,0x168f08f8e7005a41c7a5da39c0169071e9768e7005a41c7a5da39c05a3d8cd42b8e7002d23b5b40c39c00b48ed6d030e7000b4d321d45a6a510000168f09ae9b1a4a8242d254121691352880000b47847ca09e11f49fe11f1ce000005a3c23e3f63c23e39c01694acbb25ee3847ccdbc23e450785e672c3fa1da5e1795903e39d68f08f99b7847ca09e1795903e39c2d1e11f336f08f9141e6c2df1e39c0169074611b89a949a41d1846e26a5269074611b89a95a8f09532323e39cb4785e5640f8e72d1e11f1ce000002d1e29eb32e1519e380d,0x168f08f99cb41a4a78643e39ed1e135abe8f99cb41a4a78643e672d06929e190f8e75a3c29875e3e672d06929e190f8e70b478a2a145226a510000168f09ae9b1a4a8242d254121691352880000b47847ca09e11f49fe11f1ce000005a3c23e3f63c23e39c016b683489b48b84d74d8d226b05785e7dbb489ac15e1795903e39d68f0a644f3489ac15e1795903e39c2d1e12085d08f8e9d1e6c2df1e39c0169074611b89a949a41d1846e26a5269074611b89a95a8f09532323e39cb47847c73800002d1e11f1ce000002d1e29eb32e1519e380d,0x159fd8000acff167f602f4dd42bcf3800000582fdce0002b3fc59fd8000ad14b6576000159fd800002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056965b5d0e57df2c,0x159fd800015a02e7f600005680b9fd800159fdd67f600005680b9fd80002b40067f600002b3fb00002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd805697339b7e57df2c,0x159fd80000001b07ce0000040f527d80000056d5df600000057d95d8000002cf02ce0000000acfec02b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056965b5d0e57df2c,0x159fd8000acff167f60002b3fc59fd8000acff167f60002b3fc59fd8000567fb67f60000567f600002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056965b5d0e57df2c,0x0,0x159fd800567f6567f600159fd959fd80567f60567f600159fd959fd800acfec567f6000acfec000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056a12b490e57df2c,0x0,0x159fd802b3fb0567f600acfec159fd802b3fb0567f600acfec159fd80159fd8567f600159fd8000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7f6acfec00acfec2b3fb2f4dd420ff4c0000057dc117b002b3fb159fd800ad146131fd80159fd8000ad099098fec02b6aefb00000ad098fec000002b3fb015f65775aafe76458bd959fd8056ecdabd0e57df2c,0x0,0x0,0x1021088210481,0x0,0x8004200800804020104004100100802020080ce3,0x1011088218481,0x1021088210481,0x1011088218481,0x0,0x1021088210481,0x1021088210481,0x1021088210481,0x1021088210481,0x0,0x0,0x0,0x0],
[0x0,0x159fd80acfec0567f60002b452d95d8000acff167f60363b0cc3c5380d942b26f14e00568213fb0002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056abfb350e57df2c,0x159fd80000001b07ce00000006c1f380000015f657600000006c1f3800000030a7a600000002b3fb02b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056abfb350e57df2c,0x159fd80acfec0567f601037e2159fd802b3fb0567f60360fc7554fd80f346eb553f600000159fd8002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8057027a950e57df2c,0x0,0x159fd80d8ec330f14e0000000159fd80000000567f60059361054fd80d8ec1d6f3ce0002b3fb000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056abfb350e57df2c,0x159fd80000056d5df60000015b577d800005684c7f60000015b577d800000ad553f6000000acfec002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056ac0604fa57df2c,0x0,0x168f08f99ba565decd903e39ed1e135abe8f99c59de2694c83e66de11f336f08f8e75a3c29875e3e39ed1e135abe8f8e70b478a219eaec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c016ab3bc41ed5384d6afa3e39cb4785e7273c41e4dde1795903e39d68f0a6231cbb2566de1795903e39c2d1e11fd15847c7651e6c2df1e39c0168f08f8e7000005a41ceb28d0788469071e9768e70168f09532323e39d68f08f8e7000002d1e11f1ce000002d1e29eb32e1519ece1d,0x168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6ccbdb226a510000168f09ae9b1a4a8242d254121691352880000b47847ca09e11f49fe11f1ce000005a3c23e3f63c23e39c016b683489b48b847ccdbc23e450785e7dbb489ac15e1795903e39d68f08f99b7847ca09e1795903e39c2d1e11f336f08f9141e6c2df1e39c0169074611b89a949a41d1846e26a5269074611b89a95a8f09532323e39cb4785e5640f8e72d1e11f1ce000002d1e29eb32e1519e380d,0x159fd800015a02e7f600005680b9fd800159fdd67f600005680b9fd80002b40067f600002b3fb00002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056aeaf300e57df2c,0x159fd80000001b07ce0000040f527d80000056d5df600000057d95d8000002cf02ce0000000acfec02b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056abfbe20d17df2c,0x159fd8000acff167f60002b3fc59fd8000acff167f60002b3fc59fd8000567fb67f60000567f600002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8056abfb350e57df2c,0x0,0x159fd800567f6567f600159fd959fd80567f60567f600159fd959fd800acfec567f6000acfec000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd80577969b90e57df2c,0x0,0x159fd802b3fb0567f600acfec159fd802b3fb0567f600acfec159fd80159fd8567f600159fd8000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c7fb67f6000acfed59fd83b77bd9b97560000057eefd58002b3fb2b3fb000ad14628bfb00159fd8000ad146084fec02b6aefb00000ad098fec000002b3fb015f65775ad5bf1e58bd959fd8057027a950e57df2c]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1097 : TreeBound (n := 4) 106 (programCode 0x4c29075217) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1098 : TreeBound (n := 4) 106 (programCode 0x4c29075218) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1081081210481,0x1081084210481,0x1081081210481,0x1081084210481,0x1081082218481,0x1081084210481,0x1081082218481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0xc0003000c94020112004080100082020080ce3,0x481088210481,0x140005000d14820122004080100102020080de3,0x0,0x281088218481,0x8040021000804020102004080100802020080ce3,0x281088218481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x168f08f99b7847ccdbc23e672d06929e190f99cb41a4a78643e66de11f336f08f8e7b4784d6afa3e39c0000168f08f8e7000005a52b2ec94e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e7dbb489ac15e1795903e39d68f08f8e7000002d1e1795903e39c2d1e11f1ce000002d1e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf68f08f8e7000002d1e124c0a23e39ed1e29eb32e0443b1f0d,0x0,0x0,0x168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6ccbdb226a510000168f09ae9b1a4a8242d2541216913528800b5b41a44d773e11f49fe11f336f08f9413c23e3f63c23e39c0168f08f8e7b4784d74d8d226b05785e7dbb489ac15e1795903e39d68f08fa4ff08f9141e1795903e39c2d1e11f1ce000002d1e6ccbdb226a5268f0a61d78f8e72d23bf92a026a5269074611b89a95a8f09260511f1cf68f08f8e7000002d1e124c0a23e39ed1e29eb32e0443b1f0d,0x159fd8000acff167f60002b3fc59fd800159fdd67f60002b3fc59fd80002b40067f600002b3fb00015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6d8aec00002b4109fd8002b3fb159fd8000015a131fd80159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d7398b2e7a2fac,0x168f08f8e72d1e1795903e39c5a3c3a72a4f8e72d1e1795903e39ed1e135abe8f8e72d1e1795903e39c5a3c3a72a4f8e705a3c7e364eec94e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c016b683489b48b847c73800000b4785e7dbb489ac15e1795903e39d68f0a6231cbb2566de1795903e39c2d1e11fd15847c7651e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf68f0a61d78f8e72d1e124c0a23e39ed1e29eb32e0443b1f0d,0x159fd8000acff167f60002b3fc59fd8000acff167f60002b3fc59fd8000567fb67f60000567f600015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6d8aec00002b4109fd8002b3fb159fd8000015a131fd80159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d7398b2e7a2fac,0x0,0x159fd802b3fb0567f600acfec159fd80567f60567f600acfec159fd800acfec567f6000acfec000015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6d8aec00002b4109fd8002b3fb159fd8000015a131fd80159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d5df8dae7a2fac,0x0,0x159fd802b3fb0567f600acfec159fd802b3fb0567f600acfec159fd80159fd8567f600159fd8000015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6d8aec00002b4109fd8002b3fb159fd8000015a131fd80159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d5df8dae7a2fac,0x0,0xc0003000ca4020114004100100082020080ce3,0x481088210481,0x140005000d24820124004100100102020080de3,0x840101000804020104004100100802020080ce3,0x281088218481,0x0,0x281088218481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x481088210481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x168f08f99ba565decd903e39ed1e135abe8f99cb41a4a78643e39c0000168f08f8e75a3c29875e3e39ed1e135abe8f8e70b478a219eaec94e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c016b683489b48b847c73800000b4785e7dbb489ac15e1795903e39d68f0a6231cbb2566de1795903e39c2d1e11fd15847c7651e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf68f0a61d78f8e72d1e124c0a23e39ed1e29eb32e0443b1f0d,0x168f08f8e70000ba1c0a0571c00017f7f9887570000ba1c0a0571c000b5e13856c670000ba1c0a0571c00017f7f98875700001c3ca9cb0da510000168f09ae9b1a4a8242d2541216913528800b5b41a44d773e11f49fe11f336f08f9413c23e3f63c23e39c016b683489b48b84d74d8d226b05785e7dbb489ac15e1795903e39d68f0a644f3489ac15e1795903e39c2d1e11f1ce000002d1e6ccbdb226a5268f0a61d78f8e72d23bf92a026a5269074611b89a95a8f09260511f1cf68f08f8e7000002d1e124c0a23e39ed1e29eb32e0443b1f0d,0x0,0x168f08f8e70168f63350ae39c0169071e9768e7005a41c7a5da39c02d1f7ae25d8e7005a41c7a5da39c005a52b2ec94e70005a9676968894e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c0168f08f8e7b47847c73800000b4785e5640f8e72d1e1795903e39d68f08f8e7000002d1e1795903e39c2d1e11f1ce000002d1e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf68f08f8e7000002d1e124c0a23e39ed1e29eb32e0443b1f0d,0x168f08f99b7847ccdbc23e672d06929e190f99cb41a4a78643e66de11f336f08f8e7b4784d6afa3e39c0000168f08f8e7000005a52b2ec94e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e7dbb489ac15e1795903e39d68f08f8e7000002d1e1795903e39c2d1e11f1ce000002d1e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf68f08f8e7000002d1e124c0a23e39ed1e29eb32e0443b1f0d,0x0,0x168f08f99ba565decd903e39ed1e135abe8f99cb41a4a78643e66de11f336f08f8e75a3c29875e3e39ed1e135abe8f8e70b478a219eaec94e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c016b683489b48b84d6afa3e39cb4785e7dbb489ac15e1795903e39d68f0a6231cbb2566de1795903e39c2d1e11fd15847c7651e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf68f0a61d78f8e72d1e124c0a23e39ed1e29eb32e0443b1f0d,0x0,0x159fd8000acff167f60002b3fc59fd800159fdd67f60002b3fc59fd80002b40067f600002b3fb00015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6822f600002b4109fd8002b3fb2b3fb0000015a28bfb00159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d7398b2e7a2fac,0x0,0x159fd8000acff167f60002b3fc59fd8000acff167f60002b3fc59fd8000567fb67f60000567f600015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6822f600002b4109fd8002b3fb2b3fb0000015a28bfb00159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d7398b2e7a2fac,0x0,0x159fd802b3fb0567f600acfec159fd80567f60567f600acfec159fd800acfec567f6000acfec000015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6822f600002b4109fd8002b3fb2b3fb0000015a28bfb00159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d5df8dae7a2fac,0x0,0x159fd802b3fb0567f600acfec159fd802b3fb0567f600acfec159fd80159fd8567f600159fd8000015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c7fb67f6000acfed59fd8363b8b6822f600002b4109fd8002b3fb2b3fb0000015a28bfb00159fd800568213fb000015a33904bb2bb568a2fec0000159fd80acfec02b4a7fec000002b3fb0056d5df8dae7a2fac]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1179 : TreeBound (n := 4) 106 (programCode 0x4c29075219) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1180 : TreeBound (n := 4) 106 (programCode 0x4c2907521a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1181 : TreeBound (n := 4) 106 (programCode 0x4c2907521b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1182 : TreeBound (n := 4) 106 (programCode 0x4c2907521c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1081090210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1183 : TreeBound (n := 4) 106 (programCode 0x4c2907521d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1095b0220501,0x5095b0220501,0x1095b0220501,0x0,0x0,0x8000420010094020108004200102002080080ce3,0xf30079bcc0798f3007d4c20460109c83ce046f3001e9cc01e6f3001e679801ed980079f9801e703855,0x8000420010094020108004200102002080080ce3,0x4095b0220501,0xf3f307d88c07a730007d4c1e600109c83cc1e6f3001e9cc01e6f3001e679801ed980079f9801e703855,0x4095b0220501,0xd095b0220501,0x8095b0220501,0xf3007d88c0798f3007d4c20460109c83ce046f3001e9cc01e6f3001e679801ed980079f9801e703855,0x8095b0220501,0x8095b0220501,0x1021090220481,0x0,0x1095b0220501,0x5095b0220501,0x1095b0220501,0x0,0x3b9aca01dce536b280773770d6503b9ad8e6b28ee6b639aca1dcf4211eaca03b9aca01dcd650f047fe50003bbc5112ac389561e2356503b9b4135940ee6d04d6501dcddc359400ee88f565003b9e83aca000ef599328003bb89765001dce536b28077394daca00ee6f643836449,0x8000820020114020108004200102002080080ce3,0xf300f33cc03ccf300f6cc2046022a583ce046f3001e9cc01e6f3001e679801ed980079f9801e703855,0x8000820020114020108004200102002080080ce3,0x4095b0220501,0xf4e60f710583dc4160f6cc1e9cc22a583cd11abf001e9cc01e6f3001e679801ed980079f9801e7056b5,0x4095b0220501,0xd095b0220501],
[0x8095b0220501,0xf300f708c03ccf300f6cc2046022a583ce046f3001e9cc01e6f3001e679801ed980079f9801e703855,0x8095b0220501,0x8095b0220501,0x0,0x0,0x8040200000004020100004020102002080080ce3,0x0,0x0,0x8040200040205020140204008102002080080ee3,0x8040200100804020100804020102002080080ce3,0x8040200080406020180404010102002080080ce3,0x8040200100804020100804020102002080080ce3,0x8040200100804020100804020102002080080ce3,0x8040200100804020100804020102002080080ce3,0x804020020100c020301004040102002080081ce3,0x8040200100804020100804020102002080080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x10118c6220481,0x1dcd65001dd4d85940077536165000eee25d9400079126a50001dcd82d11eaca03b9ad1735940fd51da87739894982712ac389561c46803bd664ca000ef5993280077536165001dce536b2803b9e83e83aca000ef599328003bb89765001dce536b28077394daca00ee7e4aeab6449,0x0,0x10118c2220481,0x10118c6220481,0x10118c2220481,0x10118c6220481,0x10118c4220481,0x10118c6220481],
[0x10118c4220481,0x10118c6220481,0x0,0x8001200040204020108004020102002080080ce3,0x0,0x8001200040204020108004000102002080080ce3,0x8040200100804020108004200102002080080ce3,0x0,0xf30007d4c001f5300079bcc5b200f37b69ce046000f4e600f4e6000f4e679801ed980079f9801e8e9855,0x10118c6220481,0xf30007d4c001f5300079bcd11600f37a76ce046001e7e6007b66001e7e679801ed980079f9801ee9b855,0x0,0x10118c2220481,0x10118c6220481,0x10118c2220481,0x10118c6220481,0x10118c4220481,0x10118c6220481,0x10118c4220481,0x10118c6220481,0x0,0x0,0x0,0x0,0x8040200100804020108004200102002080080ce3,0x1021090220481,0x1021090220481,0x1021090220481,0x1021090220481,0x0,0x1431b0220501,0xc43190220501],
[0x1431b0220501,0x0,0x0,0x8010020402004020108004200102002080080ce3,0x0,0x8010020402004020108004200102002080080ce3,0x443190220501,0xc43190220501,0x443190220501,0xc43190220501,0x843190220501,0x843190220501,0x843190220501,0x43190220501,0x0,0x82002100804020108004200102002080080ce3,0x421090220481,0x102004100804020108004200102002080080ce3,0x0,0x221090220481,0xad0427f600002b4109fd8000ad0427f6000002b4109fd800015a084fec000015a084fec000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c80b9fd8000acff167f602f638f0b9d3800567f7b07ce0002b3fc59fd8000ad14b6576000159fd8acfec0b27185f168a5b2bb000159fe2cfec002b3fb0159fdd7e42d77d8e3bd94f7d8000056a1d847ce57df2c,0x221090220481,0x1694acbbd9b207c73da3c26b57d1f338b3bc4d37a9e2694c83e66de11f1ceb47847c738005a3c23e39ed1e11f1e48f08f8e7005a52b2ec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e3f0fdff1ce0168f3616f8f1ce05a3cd85be3c738168f63350ae39c168f14406b7c738168f14406b7c7382d1e1d39527c7382d1e29eb32e1519ece1d,0x421090220481,0x421090220481,0x421090220481,0x421090220481,0x801090220481,0x1090220481,0x801090220481,0x1090220481,0x0],
[0x1431b0220501,0xc43190220501,0x1431b0220501,0x0,0x0,0x0,0x0,0x0,0x443190220501,0xc43190220501,0x443190220501,0xc43190220501,0x843190220501,0x843190220501,0x843190220501,0x43190220501,0x0,0x14b5b0220501,0x421090220481,0x14b5b0220501,0x0,0x0,0xad29ffb000002b4a7fec0000ad0173fb000002b4a7fec000015a131fd8000015a131fd8000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c80b9fd8000acff167f603625574bed3802b3fb1b07ce0002b3fc59fd8000ad14b6576000159fdd67f602b9685dfb68a5b2bb000159fe2cfec0159fd80acfec5bf225f98955ce4056c0000056d7e736cf97df2c,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x421090220481,0x843190220501,0x1090220481,0x843190220501],
[0x1090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1344 : TreeBound (n := 4) 106 (programCode 0x4c2907521e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x2200000008800000012000000018000420021a0001000200420000200040084004000010010000040040000080100000080402000101000000400008000210080001001087fca7,0x4340200000100800040002000004008000434021a0001000200400000200040080004000010010000040040000080100000080434000101000000400100000210000001001087fca7,0xacfec0567f602b3fb0159fd80acfec0567f602b3fb00acfec0acfec02b3fb02b3fb000000015a131fd8000acff167f600015a02e7f6000005684c7f600005684c7f6000005684c80b9fd8000567fb67f6000159fed9fd80567f60567f6000159fed9fd8000000b266b6000159fd8567f600000afb2bb00000000567f60acfec00159fd959fd80159fd8acfec00159fd800002b3fb0173699a4ac,0x0,0x206fc40567f602b3fb0000002becaec000000081bf10159fd80acfec0000001853d30000159fd80ad0427f60000acfec2b3fbad34cf9c0567f60ad0019fd80000acfec15a0034d33e70000ad0427f60000ad0427f60000015a084fec0002b4109fd80000568213fb00000568214109fd800002b3fb002b3fb00ae58bd80000056d5df600000acfec0567f6015a53ff600000159fdd72ebd9e302b,0x0,0x4002a00000002800040002000000018000424021a0001000200400000200040080000002010000008040000004080000020080402400101000000400008000210000001001087fca7,0x0,0x0,0xa00000002800000022000000028000000040400000801000001010000001010000041b0200080010000100012e0010040004000010880006808100000020100000098284d1fa8,0x0,0x0,0x1694acbbd9b207c73da3c26b57d1f338b3bc4d29907ccdd2b2ef66c81f1ceb478530ebc7ccdbc23e66de11f1ce168f14406b7ccdd2b2ec94e70000168f09ad5f47cce2cef134dea7883c41800b47847c73ad1e11f49fe135abe8f8e75a3c23e3f63c23e39c000168f08f99b7847c8a0f08f99b7847ccdbc23e66de11f49fe11f336f08f9413c23e66de11f2283c23e66de11f2283c23e66de6c9ebd10788469071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f0a61d78f8e72d23b5b40c39c002d1e29eb32e1519ece1d,0xa00000002800000022000000028000000040400000801000001010000001010000401b0000800010001000001e0100040004000001880006800100000002100000018000d1fa8,0x0,0x0,0x0,0x4000200010000800040002000000008000420021a0001000200400000200040080004000010010000040000000080100000080400000101000000400000000210000001001087fca7,0x0,0x4000200010000800040002000000008000420021a0001000200400000200040080004000010010000040000000080100000080400000101000000400000000210000001001087fca7,0x2d1ec66a15c73802d20e3d2ed1ce00b4838f4bb473805a3ef5c4bb1ce00b4838f4bb473800b4a565d929ce000b52cc00f04e2cef1078830000168f09ad5f47cce2cef134dea7883c41800b47847c73ad1e11f49fe135abe8f8e75a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c4480ec94e869071e9768e7005a41ceb28d0788468f09532323e3b28f63350ae39c0168f08fe8ac23e3c923b5b40c39c002d1e29eb32e1519ece1d,0x168f08f99b7847ccdbc23e66de11f338b3bc4d29907ccdbc23e66de11f1cf68f09ad5f47ccdbc23e66de11f1ce00000b47847ccdd2b2ec94e70000168f09ad5f47cce2cef134dea7883c41800b47847c73ad1e11f49fe135abe8f8e75a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f08f8e7000002d23b5b40c39c002d1e29eb32e1519ece1d,0x20200000080800000042000000208000434021a0001000200400000200040080004000010010000040040000080100000080420000101000000400100000210100001001087fca7,0x1694acbbd9b207c73da3c26b57d1f338b3bc4d29907ccdbc23e66de11f1ceb478530ebc7ccdbc23e66de11f1ce168f14406b7ccdd2b2ec94e70000168f09ad5f47cce2cef134dea7883c41800b47847c73ad1e11f49fe135abe8f8e75a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f0a61d78f8e72d23b5b40c39c002d1e29eb32e1519ece1d,0x159fe2cfec000567f8b3fb0002b3fbacfec000567f8b3fb000056800cfec0000568213fb000015a084fec0579de619cef2f700000acfec000acfec002b4109fd800159fd80159fd80000159fd8000acff167f60002b3fc59fd800159fdd67f60002b3fc59fd80002b40067f600002b4109fd800002b4529de5ee00acfec159fd8002b962f600000acfec000000015a53ff600000159fdeccea55c9fab,0x159fd80acfec0579de6193fb0159fd80acfec0567f602b3fb000015a084fec00000002b3fb000015a084fec0579de619cef2f700000acfec000acfec002b4109fd800159fd80159fd80000159fd8000acff167f60002b3fc59fd800159fdd67f60002b3fc59fd80002b40067f600002b4109fd800002b4529de5ee00acfec000000002b962f600000acfec000000015a53ff600000159fdeccea55c9fab,0x0,0x409090218481,0x421090210481,0x409090218481,0x0],
[0x411090210481,0x20010020400880022080106002020400804132e4,0x411090210481,0x20020020800880022080106002020400804124e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x443190230501,0x421090210481,0x443190230501,0x421090210481,0x159fe2cfec000567f8b3fb000159fe2cfec000567f8b3fb0000acff6cfec0000ad0173fb00000015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c80b9fd8000acff167f60363ade799ad802b3fb0567f60002b3fc59fd80000015f6576000159fdd67f6000acfed59fd8363ade6ecaec0acfec0159fd80acfec0159fd8acfec00159fd800005680ba2b2e7a2fac,0x0,0x0,0x821090210481,0x0,0x0,0x811090218481,0x10010400400880022080186002020400806132e4,0x811090218481,0x24820820800880022080106002020400804124e4,0x821090210481,0x821090210481,0x821090210481,0x821090210481,0x843190220501,0x801090200481,0x843190220501,0x843190220501,0x0,0x609090218481],
[0x421090210481,0x609090218481,0x0,0x411090210481,0x20010800400880022080106002020400804132e4,0x411090210481,0x20020800800880022080106002020400804124e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x843190220501,0x1090200481,0x843190220501,0x1090200481,0x0,0x0,0x821090210481,0x0,0x0,0x811090218481,0x0,0x811090218481,0x0,0x821090210481,0x821090210481,0x821090210481,0x821090210481,0x843190220501,0x801090200481,0x843190220501,0x843190220501],
[0x0,0x0,0x421090210481,0x800020804020108004200100002010080ce3,0x0,0x0,0x4001100040088002208030600202040080c172e4,0x0,0x4002100080088002208030600202040080c164e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x43190220501,0x1090200481,0x43190220501,0x1090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1457 : TreeBound (n := 4) 106 (programCode 0x4c2907521f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1095b0220501,0x5095b0220501,0x1095b0220501,0x6000100a4422918004200102001100084ca3,0x3b9aca0ee6c166b283b9ae7cd6507735a2e6b283b9b059aca0ee88f91eaca03b9aca01dcd653bd664ca0001deeec12ac389561e2356503b9b4135940ee6d04d6501dcddc359400ee88f565003b9b41359400ee88f565003ba9b0b2801dd11eaca00773d0759400ee6f643836449,0x0,0xf30079bcc0798f3007d4c204603f1f83ce046f3001e9cc01e6f3001e6f3001e9cc007a73001e703855,0x0,0x4095b0220501,0xf3007a73001e9db307984458000f4e60f307a73001e9cc007a73001e7e6003d39800f3f3001e64d995,0x4095b0220501,0xd095b0220501,0x8095b0220501,0x8004100100a4020108004200104002100080ce3,0x8095b0220501,0x8095b0220501,0x1021090220481,0x0,0x1095b0220501,0x5095b0220501,0x1095b0220501,0xa00020124020108004200104002100080ce3,0x0,0x0,0xf300f33cc03ccf300f6cc2046020bf83ce046f3001e9cc01e6f3001e6f3001e9cc007a73001e703855,0x0,0x4095b0220501,0x104160f708c04cf2300f6cc2046020bf83ce046f3001e9cc01e6f3001e6f3001e9cc007a73001e703855,0x4095b0220501,0xd095b0220501],
[0x8095b0220501,0x800810020124020108004200104002100080ce3,0x8095b0220501,0x8095b0220501,0x0,0x804030000a4020918004200104002100084ce3,0x21000004020108004200104002100080ce3,0x100805000124020928004200104002100084de3,0x201000004020108004200104002100080ce3,0x0,0x0,0x0,0x0,0x804021000804020108004200104002100080ce3,0x804021000804020108004200104002100080ce3,0x100804100100c020308004200104002100081ce3,0x804021000804020108004200104002100080ce3,0x0,0x0,0x4020101004024020908004200104002100084ce3,0x0,0x0,0x40000002100000040400000081000000080200050000880040480100110004008400000040200000804000001008000001008008000004040000020100000080200000100b1a52ea7,0x10118c6220481,0x0,0x0,0x10118c2220481,0x10118c6220481,0x10118c2220481,0x10118c6220481,0x10118c4220481,0x10118c6220481],
[0x10118c4220481,0x10118c6220481,0x0,0x8001200040204020108004020104002100080ce3,0x0,0x8001200040204020108004000104002100080ce3,0x0,0xf3025fbcc001f53081183cc97e00f37b69ce046000f4e600f4e6000f4e6f3001e9cc007a73001eacf855,0x1021084220481,0xf3025fbcc001f53081183cc97e00f37a76ce046001e7e6007b66001e7e6f3001e9cc007a73001eacf855,0x0,0x1021082220481,0x1021084220481,0x1021082220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021088220481,0x0,0x1021088220481,0x0,0x0,0xf30007d4c001f5300079bcc97e00f37b69ce046000f4e600f4e6000f4e6f3001e9cc007a73001eacf855,0x10118c6220481,0xf30007d4c001f5300079bcc97e00f37a76ce046001e7e6007b66001e7e6f3001e9cc007a73001eacf855,0x0,0x10118c2220481,0x10118c6220481,0x10118c2220481,0x10118c6220481],
[0x10118c4220481,0x10118c6220481,0x10118c4220481,0x10118c6220481,0x0,0x0,0x0,0x0,0x0,0x0,0x1021084220481,0x0,0x0,0x10318c2220481,0x1021084220481,0x10318c2220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x1021084220481,0x0,0x0,0x0,0x0,0x1021090220481,0x1021090220481,0x1021090220481,0x1021090220481,0x0,0x1431b0220501,0xc43190220501],
[0x1431b0220501,0x0,0x0,0x8010020402004020108004200104002100080ce3,0x0,0x8010020402004020108004200104002100080ce3,0x443190220501,0xc43190220501,0x443190220501,0xc43190220501,0x843190220501,0x843190220501,0x843190220501,0x43190220501,0x0,0x0,0x421090220481,0x0,0x4000200010000800000002000100000000420021a0001000200400000200040080004000010010000040040000080100000080200000100800000400400000202000001001087fca7,0x221090220481,0x0,0x221090220481,0x0,0x421090220481,0x421090220481,0x421090220481,0x421090220481,0x801090220481,0x1090220481,0x801090220481,0x1090220481,0x0],
[0x1431b0220501,0xc43190220501,0x1431b0220501,0x20200804004020108004200104002100080ce3,0x0,0x0,0x0,0x0,0x443190220501,0xc43190220501,0x443190220501,0xc43190220501,0x843190220501,0x843190220501,0x843190220501,0x43190220501,0x0,0x14b5b0220501,0x421090220481,0x14b5b0220501,0x4000200010000800000002000100000000420021a0001000200400000200040080004000010010000040040000080100000080200000100800000400400000202000001001087fca7,0x0,0x0,0x0,0x0,0x421090220481,0x421090220481,0x421090220481,0x421090220481,0x843190220501,0x1090220481,0x843190220501],
[0x1090220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1650 : TreeBound (n := 4) 106 (programCode 0x4c29075220) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x109090200481,0x121090210481,0x109090200481,0x0,0x0,0x159fd800000567f602b3fb0159fd8acfec056857a88007fed5b8424325bebad0990173fb00acfec002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c80b9fd8000acff167f6030a91609773802b3fb1b07ce0002b3fc59fd8000ad14b6576000159fdd67f6015a02e94ffd82b3fb00567f60acfec0159fd80acfec59335b0c2a40152b17b0000056ac0557fb97df2c,0x0,0x5af0c9497529ce05a3ef5c4bb1ce0174462d707f1060b74a28e654e000168f63350ae39c01960ea1803e0000168fbd718919eaec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c9ebd10788469071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f09ad5f47c73ad1e14c3af1f1ce2d1e29eb32e1519ece1d,0x121090210481,0x121090210481,0x121090210481,0x121090210481,0x0,0x159fd800567f602b3fb0159fd8acfec0567f6094aaedae58bda52abb6becaec0d83e700acfec000002b4a7fec00000ad29ffb00002b405cfec00000ad29ffb000005684c7f6000005684c80b9fd8000acff167f604a5576ec1f3802b3fb1b07ce0002b3fc59fd8000ad14b6576000159fdd67f601b07ce159fd82b3fb00567f60acfec0159fd80acfec59335b12955db5cb17b0000057780e6190d7df2c,0x0,0x101090200481,0x0,0x409090210481,0x421090210481,0x409090210481,0x0,0x0,0x810020400880022080206002040401008152e4,0x0,0x820020800880022080206002040401008144e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x441090210481],
[0x421090210481,0x441090210481,0x421090210481,0x2200000008800000006000000028000420021a0001000200400000200040080004000010010000040040000080100000080400000101000000400000000210000001001087fca7,0x0,0x0,0x0,0x0,0x0,0x0,0xa0000000280000000600000002800000020040000080100000100200000101000020002000080010000100010a001010c008000000a200010400400001202000004080e05dca8,0x4028200000020800040002000000108000424021a0001000200400000200040080000020010000080040000040080000200080402400101000000400008000210000001001087fca7,0x4340200000400800040002000001008000434021a0001000200400000200040080004340010000100040000400080004000080434000101000000400100000210000001001087fca7,0x0,0x0,0x4340200000200800040002000001008000434021a0001000200400000200040080000200010000800040000400080002000080434000101000000400100000210000001001087fca7,0x4340200010000800040002000001008000434021a0001000200400000200040080004340010000400040000400080100000080434000101000000400100000210000001001087fca7,0x0,0x4000200010000800040002000000008000420021a0001000200400000200040080004000010010000040000000080100000080400000101000000400000000210000001001087fca7,0x2cb4186e6b2800003b9aca1dcd73e6b2f73597b9aca7735a2e6b2f9126e1d3b6a4800ee6b2801dcd68b9ca6d65003b9ad17394dacaee6b283b9ad1735940ee7a0eb283b9ae7cd6503b9ae7cd6503ba5f705e00775361650003c11ff940077359400000eee25d94000ee6d0c845bf59,0x4000200010000800040002000000008000420021a0001000200400000200040080004000010010000040000000080100000080400000101000000400000000210000001001087fca7,0x0,0x0,0x20200000080800000102000000108000434021a0001000200400000200040080004340010000100040040000080004000080434000101000000400100000210100001001087fca7,0x0,0x0,0x0,0x568a2fec000015a28bfb00000ad098fec000015a28bfb0000015aaa7ec0000015cb17b000015a084fec0579de619cef2f700000acfec000acfec002b4109fd800159fd80159fd80000159fd8000acff179de5ee2b3fb0000000159fd800567f62b3fb000000002b3fb000000002b4109fd800002b4529de5ee00acfec159fd8002b962f600000acfec000000015a53ff600000159fdeccea55c9fab,0x20200000080800000102000000108000420021a0001000200420000200040084000020010000080040000040080000200080402000101000000400008000210080001001087fca7,0x20200000080800000102000000108000434021a0001000200400000200040080004340010000100040000400080004000080434000101000000400100000210100001001087fca7,0x159fd80acfec000e30e873fb000e5c6c647cc003971b191f300038c3a1cfec000acfeeb3fb000000159fed9fd800005684c7f60002b4109fd80000567fb67f600005684c7f6000005684c7f638c3971c61cb82b3fb0159fd8acfec0567f600acfec0567f6000046477e2323ea3fb0159fd8acfec01c61cbab3fb000008d3bfac00567f602b3fb0159fd82b3fb00000232672fb000005682ec666ba650ac,0x159fd80acfec0008c8f273fb00002b405cfec002bedca91f300002b405cfec000567f8b3fb000000159fed9fd8000567fb67f60002b405cfec0000567fb67f600005684c7f6000005684c7f6159fd80159fd8567f601b07ce2b3fb0567f600567f602b3fb00567f60002323c467f6159fd8acfec00159fdab3fb000008ce57b6000000ad29ffb0159fd82b3fb000000b7f9ebb0000056819268ecac4cac],
[0xacfec0567f602b3fb0159fd80acfec00000002b3fb00acfec0acfec0002b3fdb3fb00000005684c7f60000056d5df6000015a02e7f6000005684c7f600005684c7f6000005684c7f6acfec00000acfec05680b9fe37ceac567f60000005680b9fd8acfec00000acfec015a131fdab3fb0567f602b3fb000000002b3fb0567f6002b3fb159fd802b3fb05be75602b3fb000002b3fb017c2396cac,0x568a2fec000015a28bfb00000ad098fec000015a28bfb0000015aaa7ec0000015cb17b000015a084fec0579de619cef2f700000acfec000acfec002b4109fd800159fd80159fd80000159fd8000acff179de5ee2b3fc59fd800159fd800567f62b3fb02b3fb002b3fb000000002b4109fd800002b4529de5ee00acfec159fd8002b962f600000acfec000000015a53ff600000159fdeccea55c9fab,0x0,0x0,0x0,0x0,0x168f08f99b7847ccdbc23e66de11f338b3bc4d29907ccdbc23e66de11f1cf68f09ad5f47ccdbc23e66de11f1ce00000b47847ccdd2b2ec94e70000168f09ad5f47cce2cef134dea7883c41800b47847c73ad1e11f49fe135abe8f8e75a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f08f8e7000002d23b5b40c39c002d1e29eb32e1519ece1d,0x0,0x0,0x0,0xee6b2800003b9aca1dcd73e6b2800003b9aca0001ebbd02800007753616501dcf41d650007753616500775361650007753616500001dcd6500003b9aca000001dcd6500000003bb897651dcd6c73594000077359400000773597b9ad17359400000773594003b9acc01844da,0x0,0x0,0x2120000201080000004200000011800000004040000080100000101000000101000004050200080010000100012a001004000800001082000100820000002020000008828451fa8,0xacfec00000002b3fb00000000acfec02b3fb02b3fb00acfec0acfec00000059335b00000005684c7f60000056d5df6000015a02e7f6000005684c7f600005684c7f6000005684c7f60000000000acfec0000159fd800000567f602b3fb000159fe2cfec000000acfec05680b9fdab3fb00000002b3fb000000002b3fb000000002b3fb159fd802b3fb0567f6002b3fb000002b3fb017c2396cac,0x0,0x20200000080800000042000000208000434021a0001000200400000200040080000200010000800040001000080001000080420000101000000400100000210100001001087fca7,0x20200000080800000042000000208000434021a0001000200400000200040080004340010010000040001000080100000080434000101000000400100000210000001001087fca7,0x0,0x0,0x0,0x20200000080800000042000000208000434021a0001000200400000200040080004200010010000040001000080101000080420000101000000400100000210100001001087fca7,0x0,0x20200000080800000042000000208000420021a0001000200400000200040080004000010010000040000000080100000080400000101000000400000000210000001001087fca7,0x0,0x1694acbb2539c2d1e6c2df1e39c02e88c5ae0fe20c0ba1c0a0571c0005a3cd85be3c7380ba1c0a0571c0000b479b0b7c78e7010ecafab3cce70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0168f08f8e7000005a41ceb28d0788469071e9768e70168f08f8e700000168f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x1694acbbd9df25d92f71c23e66de135c81bc4d37a9e2694c83e39c0000000b47847ccdbc29875e3e39c0000000168f08f99b78a219eaec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c9ebd10788468f08f8e7000005a41ceb28d0788469071e9768e70168f08f8e700000168f09ad5f47c73ad1e14c3af1f1ce2d1e29eb32e1519ece1d,0x1694acbb2539c0b47deb897639c02e88c5ae0fe20c0ba1c0a0571c000b478fc3f7fc7380ba1c0a0571c000168f1f87eff8e701c343427b04e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c9ebd10788469073aca341e211a41ceb28d0788469071e9768e70168f63350ae39c0168f09ad5f47c73ad1e14c3af1f1ce2d1e29eb32e1519ece1d,0x0,0x0,0x1694acbbd9b207c73da3c23e39c0016ab3bc4d37a9e2694c83e66de11f1ceb47847d27f84d6afa3e66de11f1ce168f08f8e7005a52b2ec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x0],
[0x1694acbbd9df25d92f71c23e66de135c81bc4d37a9e2694c83e66de11f1ceb47847ccdbc29875e3e66de11f1ce168f08f99b78a219eaec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c9ebd10788469071e9768e7005a41ceb28d0788469071e9768e70168f63350ae39c0168f09ad5f47c73ad1e14c3af1f1ce2d1e29eb32e1519ece1d,0x0,0x1694acbb2539c00005a3c23e39c0016ab3bc4d37a9e2694c83e39c0000000b47847c738005a3c23e39ed1e11f1e48f08f8e7005a52b2ec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0168f08f8e7000005a41ceb28d0788469071e9768e70168f634b99ec94e868f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x1694acbb2566de11f771c23e450785e7273c41e4dde1795903e39ed1e11f2827847ca09e1795903e39c5a3c23e504f08f9413c7e364eec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c9ebd1078846907243b2b253a1a41ceb28d0788469071e9768e70168f08f8e700000168f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x1694acbb2539c00005a3c23e39c0016ab3bc4d37a9e2694c83e39c0000000b47847d27f84d6afa3e39d68f08f8fd8f08f8e7005a52b2ec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0168f08f8e7000005a41ceb28d0788469071e9768e70168f09532323e39d68f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x0,0x1694acbbd9b207c73da3c26b57d1f338b3bc4d37a9e2694c83e66de11f1ceb47847c738005a3c23e39ed1e11f1e48f08f8e7005a52b2ec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f634b99ec94e868f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x0,0x1694acbbd9b207c73da3c26b57d1f338b3bc4d37a9e2694c83e66de11f1ceb47847d27f84d6afa3e39d68f08f8fd8f08f8e7005a52b2ec94e70000168f08f8e70005aacef134dea7883c418000000000002d1e11f49fe11f1ce000005a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f09532323e39d68f09ad5f47c73ad1e11f1ce000002d1e29eb32e1519ece1d,0x200200000800800001002000001008000434021a0001000200400000200040080004000010010000040040000080100000080434000101000000400100000210100001001087fca7,0x159fe2cfec000567f8b3fb0002b3fbacfec000567f8b3fb000056800cfec0000568213fb00000015a084fec0000568213fb00002b405cfec0000568213fb000005684c7f6000005684c80b9fd8000acff167f60363ade799ad802b3fb0567f60002b3fc59fd80000015f6576000159fdd67f6000acfed59fd8363ade6962f60acfec0159fd80acfec02b3fb0acfec002b3fb000005680ba2b2e7a2fac,0x0,0x409090210481,0x421090210481,0x409090210481,0x0,0x0,0x40010020400880022080206002040401008152e4,0x0,0x40020020800880022080206002040401008144e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x441090210481,0x421090210481,0x441090210481,0x421090210481,0x159fd80acfec0579de6193fb0159fd80acfec0000568213fb0002b3fbacfec00000002b3fb000015a084fec0579de619cef2f700000acfec000acfec002b4109fd800159fd80159fd80000159fd8000acff167f60002b3fc59fd800159fdd67f60002b3fc59fd80002b40067f600002b4109fd800002b4529de5ee00acfec159fd8002b962f600000acfec000000015a53ff600000159fdeccea55c9fab,0x0,0x8095b0220501,0x821090230481],
[0x8095b0220501,0x0,0x0,0x1001040040088002208028600204040100a152e4,0x0,0xee6b3734edacd9b059aca1dcd6503b9bb86b64d3b6b366b28ee72c2771163b6a65ce584eda93dcd68b9cb09db527b9ad1739613b88156503b9b41359400ee88f56500773d0759403b9ca6d65003ba70c8e9c9773770d65003c14716d497736a0388d0eee27b61650ee6d0c845a7e9,0x821090230481,0x821090230481,0x821090230481,0x821090230481,0x843190220501,0x801090220481,0x843190220501,0x843190220501,0x0,0x0,0x421090210481,0x0,0x0,0xee6c3d88c049acdb9aca0ee6b4d40bf2e6b639aca0ee6b29dcd650007753616501dcf41d6500077536165007753616500077536341d6501dcddc3594d09de0cd6501dcddc35940003d77a0501dcd6c7359d50300735a2e6b28773597b9ad1735a2e6b28773594003be9072aa44da,0x2001080040088002208030600204040100c172e4,0x0,0x2002080080088002208030600204040100c164e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x843190220501,0x1090200481,0x843190220501,0x1090200481,0x0],
[0x8095b0220501,0x821090230481,0x8095b0220501,0x7735940001dcd6500001e449a940001dcd6500001e449a940001dcd657753616501dcf41d6500077536165007753616500077536341d6501dcddc35943b9ae7cd6501dcddc35940003d77a0501dcd6c7359400007735a2e6b28773597b9ad1735a2e6b28773594003b9acc01844da,0x0,0x0,0x0,0x0,0x821090230481,0x821090230481,0x821090230481,0x821090230481,0x843190220501,0x801090220481,0x843190220501,0x843190220501,0x0,0x9090200481,0x421090210481,0x9090200481,0x0,0x0,0x40011000400880022080206002040401008152e4,0x0,0x40021000800880022080206002040401008144e4,0x421090210481,0x421090210481,0x421090210481,0x421090210481,0x41090200481,0x1090200481,0x41090200481],
[0x1090200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_770 : TreeBound (n := 4) 106 (programCode 0x4c290752) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part012_771 part012_852 part012_853 part012_934 part012_1015 part012_1016 part012_1097 part012_1098 part012_1179 part012_1180 part012_1181 part012_1182 part012_1183 part012_1344 part012_1457 part012_1650

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1844 : TreeBound (n := 4) 106 (programCode 0x4c29075311) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080430204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1845 : TreeBound (n := 4) 106 (programCode 0x4c29075312) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000100004008004200100002020080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1846 : TreeBound (n := 4) 106 (programCode 0x4c29075313) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080430204481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1847 : TreeBound (n := 4) 106 (programCode 0x4c29075314) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080400200481,0x1080442208481,0x1080400200481,0x1080442208481,0x1080421204481,0x10804a4214481,0x10804e721c481,0x10804a4214481,0x1080400200481,0x0,0x0,0x8d40021000104804122004080100902080080de3,0x140005000100804022004080100102080080de3,0x0,0x0,0x8040001000100004002004080100002080080ce3,0x0,0x140005000100804022004080100102080080de3,0x840021000104804122004080100902080080de3,0x440001000100004002004080100002080080ce3,0x1040041000108804222004080101102080081de3,0x40001000100004002004080100002080080ce3,0x0,0x0,0x0,0x0,0x0,0x180488284222],
[0x180488284222,0x180488284222,0x180488284222,0x240009000100804020804200100102020080de3,0xfa98003ea60008118000f4e74f5039800f3f33cc81927302047e6079800f31e604643b207987a87c36,0x180488284222,0x0,0x580488284a62,0x480488284a62,0x180488284222,0x480488284a62,0x0,0x0,0x0,0x0,0x0,0x0,0x7983cc1e6003d398000f300003cc0000798079801e7e60079bcc01e600003cc0000f4e6001e64d995,0x140005000100804024004100100102100080de3,0x40101000100004004004100100002100080ce3,0x0,0x0,0x0,0x40005000100004004004100100002100080ce3,0x840021000104804124004100100902100080de3,0x0,0x1040041000108804224004100101102100081de3,0x40001000100004004004100100002100080ce3,0x0,0x0,0x0,0x0],
[0x0,0x180488284222,0x180488284222,0x180488284222,0x180488284222,0x0,0xfa98003ea60008118000f4e76db039800f3f379881936602049cc079800f31e60482d7e07987a87c36,0x180488284222,0x1ed98003ea6000fa986b1d266001e9cc007a73798e19f03001e9cc03cc01288e841e679807983cd2f26,0x580488284a62,0x480488284a62,0x180488284222,0x480488284a62,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1928 : TreeBound (n := 4) 106 (programCode 0x4c29075315) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080461208481,0x10804e4208481,0x1080461208481,0x1080440208481,0x1080442208481,0x10804e7208481,0x1080442208481,0x1080463208481,0x10804e4208481,0x10804e7208481,0x10804e4208481,0x1080442208481,0x0,0xf30000b6400088b0000798408c000f3f3009bbb4e601e7e601e61e601e601e60f31e603cc1e61e8e92b5,0xf30079bcc007a7300798007d4c001e6f30097e01e601e7e601e61e601e601e61e61e607981e61e8e9855,0xf30000b640004bf0000f30408c001e6f3009bbb4e601e7e601e61e601e601e60f31e607981e61e8eb1a5,0xf300f33cc03ccf304bf000408c000f3f3009bbb4e601e7e601e61e601e601e60f31e603cc1e61f0812b5,0x0,0x0,0xf3000408c0010230007980408c000f3f3009bbb4e601e7e601e61e601e601e60f31e603cc1e61e8e92b5,0xf300012fc1e60f30000f307d4c001e6f30097e01e601e7e601e61e601e601e61e61e607981e61e8eb6b5,0x0,0x4000000010000040040000002100008090000060000000140000000400800002880804000020080000400100000800100000800004000200080000800100002000100010210840ca7,0x0,0x0,0xf300f33cc0f30f300f3000408c000f3f3009bbb4e601e7e601e61e601e601e60f31e603cc1e61e8e92b5,0x0,0xf300f33cc03ccf301e6000408c000f3f3009bbb4e601e7e601e61e601e601e60f31e603cc1e61ecb52b5,0x0,0x0,0xf30000b6400088b0000798799e600f3f300980d90f31e9cc01e6f3f31e601e61e61e603cc1e61e7037c5],
[0x8004200100101004008004000100202008080ce3,0xf30000b640002d90000f303cde600f3f300980d90f31e9cc01e6f46c9e601e60f31e603cc1e61e7032b5,0x0,0x8001200040101004168004020100202008080fe3,0xf30822d2c0000f30000001138a583cc3cc07981045339bcc007980001e607983cc0798f301e61e64dcf5,0x8002200080101004168004020100202008080fe3,0x0,0x8004200100101004008004000100202008080ce3,0xf3001e9cc001f5308377803ea6001e6f30099d725301e9cc01e702b8ce601e60f31e607981e61e703345,0x8008200200101004048004008100202008080ee3,0xf3001e9cc003db3002e83079f9801e6f3007a3a0fcc1e9cc01e606c37e601e61e61e607981e61e7608b5,0xf300f33cc0f30f300f3000408c000f3f3009bbb4e601e9cc01e711601e601e60f31e603cc1e61e8e92b5,0x0,0xf300f33cc03ccf301e60004458000f3f300a3536cc01e9cc01e74e201e601e60f31e603cc1e61ecb52b5,0x0,0x0,0xf30000b6400088b0000798408c000f3f3009f874e601e67981e63cc01e601e60f31e603cc1e61e8e92b5,0x0,0xf300012fc0002d90000f308118000f3f3009f876cc01e67981e63cc01e601e61e61e603cc1e61eacf7c5,0xf301e63cc0798f302d9000408c000f3f3009f874e601e67981e63cc01e601e60f31e603cc1e61ecb52b5,0x0,0xf301e63cc0000f30981cc08118000f3f3009f876cc01e67981e63cc01e601e61e61e603cc1e61eacf7c5,0xf3000408c0010230007980408c000f3f3009f874e601e67981e63cc01e601e60f31e603cc1e61e8e92b5,0x0,0xf3001e9cc01e6f3001e6008118000f3f3009f876cc01e67981e63cc01e601e61e61e603cc1e61eacf7c5,0xf3001e9cc001f53079f9808118001e6f30097e03cc01e6f301e63cc01e601e61e61e607981e61eacf855,0x0,0x0,0xf300f33cc0f30f300f3000408c000f3f3009f874e601e67981e63cc01e601e60f31e603cc1e61e8e92b5,0x0,0xf300f33cc03ccf301e6000408c000f3f3009f874e601e67981e63cc01e601e60f31e603cc1e61ecb52b5,0x0],
[0x0,0x8000600010101004048004008100202008080ee3,0x8004200100101004068004004100202008080fe3,0x8000a00020101004048004008100202008080ee3,0x0,0x8001200040101004008004000100202008080ce3,0xf307a76cc0000f30000001119cc03cc3cc07980f30079bcc007980001e607983cc0798f301e61e64dcf5,0x0,0xf307a952c0010230000f31119cc03cc3cc0799024e679bcc007980799e607983cc0798f301e61e655675,0x8004200100101004068004004100202008080fe3,0x0,0x8008200200101004068004004100202008080fe3,0x8001200000101004008004000100202008080ce3,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2009 : TreeBound (n := 4) 106 (programCode 0x4c29075316) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x108046120c481,0x1080404200481,0x108046120c481,0x1080400200481,0x10804a2214481,0x1080400200481,0x10804a2214481,0x10804e721c481,0x1080404200481,0x10804e721c481,0x1080404200481,0x1080400200481,0x0,0x1008428204481,0x8006a00100104004122004080100802024080de3,0x1008428204481,0x0,0x4000001010000004040000008100000008000230100000808000002000200002000020000100080000400100000800100000806020001001000004000040010000000010054c7ffa7,0x1000408200481,0xf30007d4c001023000798088b0000f37980a72e7e601e7e601e61e601e7e6001e60f304275cc1ee9b7c5,0x8040200020100804022004080100102004080de3,0x10204a8214481,0x8002200000100004002004080100002000080ce3,0x10204a8214481,0x1000408200481,0x0,0xf307983cc1e60f300000011160003cc000079807980798f300f31e601e9cc003cc0000f300001e68a925,0x0,0xf307983cc1e60f300000011160003cc000079807980798f300f31e601e9cc003cc0000f300001e68a925,0x0,0x0],
[0xf30811bcc01e6f3003cc011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0x0,0xf3000f6cc0010230003cc11160003cc00007981023079bcc007983cc1e9cc003cc0000f300001e64dcf5,0xf307983cc0000f300000011160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0xf3000f6cc003db300079811160003cc00007981023079c08c0f307981e9cc003cc0000f300001e68a925,0x0,0xf30079bcc007a73001e6011160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0xf307a76cc003db300000011160003cc00007981023079c08c0f300001e9cc003cc0000f300001e68a925,0xf30079bcc01e6f3003cc011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0xf307983cc0000f300000011160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0x0,0xf307983cc1e60f300000011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0xf307983cc1e60f300000011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0x1008428204481,0x8000200100100004004004100100002000080ce3,0x1008428204481,0x8000200800100004004004100100002000080ce3,0x0,0x1000408200481,0xf3000408c001f5300079804458001e679809f967e601e6f301e63cc01e6f3000f30f307e42cc1eacf345,0x0,0x10204a8214481,0xf30079bcc001f5309ff1804458001e67980a17e64601e6f301e63cc01e6f3000f30f307e7fc8deacf345,0x10204a8214481,0x1000408200481,0x0,0x0,0x0,0x0],
[0x0,0xf3000222c0002d900007991160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0x0,0xf3000222c00088b0000f311160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0xf3000f6cc0010230003cc11160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0xf307983cc0000f300000011160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0x0,0xf3079a22c0000f30000f311160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0x0,0xf307a76cc003db300000011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0xf307983cc0000f300000011160003cc00007980f30079bcc007980001e9cc003cc0000f300001e64dcf5,0x0,0xf307983cc1e60f300000011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0xf307983cc1e60f300000011160003cc00007980f30079bcc00f300001e9cc003cc0000f300001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2090 : TreeBound (n := 4) 106 (programCode 0x4c29075317) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080461208481,0x10804e4208481,0x1080461208481,0x1080440208481,0x1080442208481,0x10804e7208481,0x1080442208481,0x1080463208481,0x10804e4208481,0x10804e7208481,0x10804e4208481,0x1080442208481,0x0,0xf30000b6400088b0000798408c000f33cc0a72e7e601e7e601e61e601e601e60f307983cc3cc1e8e92b5,0xf30079bcc01e6f30097e004bf0001e67980a72e7e601e7e601e61e601e601e60f30f307983cc1ee9b345,0xf30000b640004bf0000f304bf0001e67980a72e7e601e7e601e61e601e601e60f30f307983cc1ee9b345,0xf300f33cc0f30f304bf000408c000f33cc0a72e7e601e7e601e61e601e601e60f307983cc3cc1f0812b5,0x0,0xf303cc3cc2daf530b6b9804bf0001e67980a72e7e601e7e601e61e601e601e60f30f307983cc1ee9b345,0xf3000408c0010230007980408c000f33cc0a72e7e601e7e601e61e601e601e60f307983cc3cc1e8e92b5,0xf30000b641e60f30798f304bf0001e67980a72e7e601e7e601e61e601e601e60f30f307983cc1ee9b345,0x0,0xf30079bcc001f5308191804bf0001e67980a72e7e601e7e601e61e601e601e60f30f307983cc1ee9b345,0xf3003cfcc00f3f3003cc0088b0001e6798097e01e601e7e601e61e601e603cc1e60f307983cc1ef15055,0xf303cc3cc001f530b6b9804bf0001e67980a72e7e601e7e601e61e601e601e60f30f307983cc1ee9b345,0xf300f33cc0f30f300f3000408c000f33cc0a72e7e601e7e601e61e601e601e60f307983cc3cc1e8e92b5,0x0,0xf300f33cc03ccf301e6000408c000f33cc0a72e7e601e7e601e61e601e601e60f307983cc3cc1ecb52b5,0x0,0x0,0x80088200022],
[0x180488284222,0x80088200022,0x180488284222,0x2400090001020041a0804200100402010080de3,0x0,0x80088200022,0x0,0x480088210862,0x480088210862,0x80088200022,0x480088210862,0x0,0x0,0x0,0x0,0x0,0xf30000b6400088b00007988118000f33cc09bca9cc01e67981e63cc01e603cc1e607983cc3cc1ead3485,0xf3001e9cc01e6f30097e004458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1eacf2b5,0xf30000b640002d90000f304458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1eacf2b5,0xf301e63cc03ccf302d90004458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1ecb52b5,0x0,0xf301e63cc0000f308929804458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1eacf2b5,0xf3000408c001f5300079804458001e679809f967e601e6f301e63cc01e601e60f30f307983cc1eacf345,0x0,0xf3001e9cc01e6f3001e6004458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1eacf2b5,0xf30079bcc001f5308191804458001e679809f967e601e6f301e63cc01e601e60f30f307983cc1eacf345,0xf3001e9cc00f3f3003cc004458001e679809f967e601e6f301e63cc01e601e60f30f307983cc1eb48b45,0xf301e63cc001f5309859804458001e679809f967e601e6f301e63cc01e601e60f30f307983cc1eacf345,0xf300f33cc0f30f300f30004458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1f44d2b5,0x0,0xf300f33cc03ccf301e60004458000f33cc09bca7e601e67981e63cc01e601e60f307983cc3cc1ecb52b5,0x0],
[0x0,0x80088200022,0x180488284222,0x80088200022,0x180488284222,0x0,0x0,0x80088200022,0x0,0x480088210862,0x480088210862,0x80088200022,0x480088210862,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2171 : TreeBound (n := 4) 106 (programCode 0x4c29075318) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x10804e721c481,0x1080421204481,0x1080421204481,0x108046220c481,0x10804e721c481,0x108046220c481,0x1080421204481,0x1080424204481,0x10804e721c481,0x1080424204481,0x1080421204481,0x0,0x180428204481,0xd40021000104004122004080100802004080de3,0x180428204481,0x0,0x0,0x8040001000100004002004080100002004080ce3,0x0,0x180428204481,0x4804a8214481,0x440001000100004002004080100002004080ce3,0x4804a8214481,0x180428204481,0x0,0x0,0x0,0x0,0x0,0x0],
[0xf30000b6400088b0000b6400f379803d1b200f31e603cde61e6204603cc03ea7e60fa98003db30799556,0x0,0x0,0x0,0xf30822d2c0000f30000001138a583cc00007981045339bcc007980001ea114b3cc0000f300799e64dcf5,0x0,0x0,0xf30079bcc007a73001e6011167983cc00007980f33d39bcc007980001e9ccf33cc0000f300799e64dcf5,0xf3003cfcc00f3f3001e6f300f42fc079bcc00f33cc7d4cf321391e6079803ea6001ef7e003d398539f66,0xf303cc3cc1e60f303cc3cc00f379803cfcc00f31e603cde62d901e603cc03ea6000fa98003db30799556,0xf30822d2c0000f30000001138a583cc00007981045339bcc007980001ea114b3cc0000f300799e64dcf5,0x0,0xf301e63cc0798f300f30f300f42fc079bcc00f33cc97e0f328d11e6079803ea6001ef7e003d3983cd766,0x0,0xf301e63cc0f30f301e60f300f42fc079bcc00f33ccb640f330691e6079803ea6001ef7e003d398b65766,0x0,0x180428204481,0x0,0x180428204481,0x40101000100004004004100100002004080ce3,0x0,0x0,0x0,0x180428204481,0x4804a8214481,0x0,0x4804a8214481,0x180428204481,0x0,0x0,0x0,0x0],
[0x0,0xf3000222c0002d900007991167983cc00007980f33d39bcc0079801e7e9ccf33cc0000f300799e64dcf5,0x0,0xf303cc3cc2d90f307981e601e76c8079bcc00f3798b641e620463cc079807b66001f164003db30799c76,0x0,0xf3000f6cc0010230003cc11167983cc00007980f30079bcc007980001e9ccf33cc0000f300799e64dcf5,0xf307a952c0000f300000011167983cc00007980f33d39bcc007980001e9ccf33cc0000f300799e64dcf5,0x0,0xf3079a22c0000f30000f311167983cc00007980f33d39bcc007980001e9ccf33cc0000f300799e64dcf5,0xf30079bcc007a73001e6011167983cc00007980f33d39bcc0079801e7e9ccf33cc0000f300799e64dcf5,0xf3003cfcc00f3f3001e6f300f46c8079bcc00f33cc7d4de621393cc079803ea6001f34a003d398539f66,0x0,0xf3079a22c0000f300000011167983cc00007980f33d39bcc007980001e9ccf33cc0000f300799e64dcf5,0x0,0xf301e63cc0798f300f30f300f46c8079bcc00f33cc97e1e628d13cc079803ea6001f34a003d3983cd766,0x0,0xf301e63cc0f30f301e60f300f46c8079bcc00f33cc97e1e630693cc079803ea6001f34a003d398b65766]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2252 : TreeBound (n := 4) 106 (programCode 0x4c29075319) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10804b0210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2253 : TreeBound (n := 4) 106 (programCode 0x4c2907531a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10804e121c481,0x10804e721c481,0x10804e121c481,0x10804e721c481,0x10804e221c481,0x10804e721c481,0x10804e221c481,0x10804e721c481,0x10804e421c481,0x10804e721c481,0x10804e421c481,0x10804e721c481,0x0,0xf30000b6400088b0000798408c000f33cc0ace264601e7e601e61e601e60f300f30798414648de8e92b5,0xf30079bcc2f76f30463e004bf0001e67980a91664601e7e601e61e601e63cc00f30f307f728c1ee9b345,0xf30000b640004bf0000f304bf0001e67980a91664601e7e601e61e601e63cc00f30f307f72c8dee9b345,0xf300f33cc316fef04bf0007d4c000f33cc0ad6cfa601e7e601e61e601e60f301e60798433d9b9f0817c5,0x0,0xf303cc3cc2f97390be59184bf0001e67980a91664601e7e601e61e601e63cc00f30f307f728c1ee9b345,0xf3000408c0010230007980408c000f33cc0ad6ee0601e7e601e61e601e60f300f30798433dd85e8e92b5,0xf30000b641e60f30798f304bf0001e67980a91664601e7e601e61e601e63cc00f30f307f72c8dee9b345,0x0,0xf30079bcc001f530be51804bf0001e67980a91664601e7e601e61e601e63cc00f30f307f728c1ee9b345,0xf3003cfcc00f3f3003cc0088b0001e6798097e01e601e7e601e61e601e63cc01e60f307d6a601ef15055,0xf303cc3cc001f530be59184bf0001e67980a91664601e7e601e61e601e63cc00f30f307f728c1ee9b345,0xf300f33cc0f30f300f3000408c000f33cc0ace264601e7e601e61e601e60f300f3079841460c1e8e92b5,0x0,0xf300f33cc03ccf301e6000408c000f33cc0b47a64601e7e601e61e601e60f300f3079842390c1ecb52b5,0x0,0x0,0x480088210862],
[0x181088210a62,0x80088210022,0x181088210a62,0x2400090001020041a0804200100402034080de3,0x0,0x80088210022,0x0,0x480088210862,0x480088210862,0x80088210022,0x480088210862,0x0,0x0,0x0,0x0,0x0,0xf30000b6400088b00007988118000f33cc0a5de96c01e67981e63cc01e60f301e60798424bcb5ead3485,0x400001801000092104000048410000020000012404400021210000080040000200001000010002000040008000080020000080490800080042000100008000400000001009086dda7,0xf30000b640002d90000f304458000f33cc0a5d6e0601e67981e63cc01e60f300f30798424ad85eacf2b5,0x40000400100009011400004005000010000001240440002121000008004000020000100001000200004000800008002000008049088008004200010000800040000000100908edda7,0x0,0xf301e63cc0000f30af29184458000f33cc0a54a64601e67981e63cc01e60f300f30798423948deacf2b5,0xf3000408c001f5300079804458001e67980a17e64601e6f301e63cc01e63cc00f30f307e7f8c1eacf345,0x0,0xf3001e9cc01e6f3001e6004458000f33cc0a5d6e0601e67981e63cc01e60f300f30798424ad85eacf2b5,0xf30079bcc001f5309ff1804458001e67980a17e64601e6f301e63cc01e63cc00f30f307e7f8c1eacf345,0xf3001e9cc00f3f3003cc004458001e67980a27530601e6f301e63cc01e63cc00f30f307e9dec1eb48b45,0xf301e63cc001f5309ff9184458001e67980a17e64601e6f301e63cc01e63cc00f30f307e7f8c1eacf345,0xf300f33cc0f30f300f30004458000f33cc0b47a64601e67981e63cc01e60f300f30798441f0c1f44d2b5,0x0,0xf300f33cc03ccf301e60004458000f33cc0a54a64601e67981e63cc01e60f300f3079842390c1ecb52b5,0x0],
[0x0,0x480088210862,0x181088210a62,0x80088210022,0x181088210a62,0x0,0x0,0x80088210022,0x0,0x480088210862,0x480088210862,0x80088210022,0x480088210862,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2334 : TreeBound (n := 4) 106 (programCode 0x4c2907531b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10804b0210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2335 : TreeBound (n := 4) 106 (programCode 0x4c2907531c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2336 : TreeBound (n := 4) 106 (programCode 0x4c2907531d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c80003cc1e612fc0007d4ed9001e9cc01e6f3001e679800fa98003d39801e7032b5,0xf37983cc1e610603980003ea600222c000ad4225001e9cc01e6f3001e679800fa980079f9801e703345,0x16c80005b200025f80003cc1e612fc0008c82a5001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x16c80014e200053880003cc1e612fc0007d557e0f4e600f4e6000f4e679800fa98003d39801e7032b5,0x0,0x25f800097e00025f80003cc3cc222c0008c7fcc0f4e6007b66001e7e679800fa980079f9801e7051a5,0x40001000110004000004000102002080080ce3,0x240009000110004040204008102002080080ee3,0x40001000110004000004000102002080080ce3,0x440011000110004080404010102002080080ce3,0x20000000080001000a0000400280000000420000002000000020800000022801000000200000200801000008000002008004000002010000010100000100100000100108413a7,0xf379804c0e601303980003ea600222c0008ee135cc1e63cc1e603cc1e679800fa980079f9801e703345,0x440011000110004080404220102002080080ce3,0x0,0x0,0x0,0x40001000110004000004200102002080080ce3,0x0,0x40001000110004000004200102002080080ce3,0x0,0x0,0x102000000808000001020000001080000000482000001004100008800000028a08804000800050004004000008010400008010000002080000008100000040100000100128c8da7,0x0,0x240009000110004040204008102002080080ee3,0x240009000110004040204008102002080080ee3,0x240009000110004040a04008102002080080ee3,0x2400090001100040c0404010102002080080ee3,0x0,0xfa98007b66000811800079a22c22a5800798007983cc3cc1e603cc1e6f3001ed980079f9801e705865,0x10200000080800000102000000108000000048840000200510000880000002aad901080080104a2040000080080155b2008010000002080000010100000040100000100128c9da7],
[0xfa98007b6600081180003ce22c2268c008da05fcc3cc1e61e607981e6f3000fa980079f9801e705355,0x240009000110004042004008102002080080ee3,0xfa98007b6600081180003cde6012fc0007d5b6cc03cde601e61e601e6f3000fa98003d39801e703465,0x0,0x0,0x0,0x8040001000110004008004200102002080080ce3,0xfa98002046000fa98000799e6012fc0009bcb53001e9cc01e6f3001e679801ed98003d39801e7037c5,0x16c83cc1e60f325f80003cc1e612fc000aae2a5001e9cc01e6f3001e679800fa98003d39801e7032b5,0x402000008008000010020000010080000000400020001040000004800000022c81c0000020100000400400000801000000800400000208000000810000002010000010030840ca7,0x0,0xf30799e6089b32307983cc1e612fc0009db339001e9cc01e6f3001e679800fa98003d39801e7032b5,0xf3079803ce611efd27e003ea600222c000ad6085001e9cc01e6f3001e679800fa980079f9801e703345,0xf30799e603857610f303cc1e612fc000ad6fb5001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x0,0x440000000110004008004200102002080080ce3,0xf307981e610cf66e7980799e6012fc000ad6dcf001e9cc01e6f3001e679801ed98003d39801e7037c5,0xf3079a04619f7da8f303cc1e612fc000ad6fb5001e9cc01e6f3001e679800fa98003d39801e7032b5,0x3cc1e603cde67e5d7e60079f980222c000892e3f001e9cc01e6f3001e679801ed980079f9801eeda2b5,0x402000000110004008004200102002080080ce3,0x7983cc01e67b270e4cc007a730012fc000ae62b5001e9cc01e6f3001e679801ed98003d39801ef14fc5,0x410000000110004008004200102002080080ce3,0x410080400110004408004200102002080082ce3,0x404000000110004008004200102002080080ce3,0x1e60f3001e9cddc37f6000408c0012fc000b507b5001e9cc01e6f3001e679800fa98003d39801ecb52b5,0x17ddeae967980000000000122ba583db30007980f30079bcc007a73001e7e6003cde600f379801e64dcf5,0x0,0x4085b0220501,0x4205b0220501,0x4085b0220501,0x0],
[0x4105b0220501,0x1040040620110004628004200102002080083de3,0x4105b0220501,0x1040040020110004628004200102002080083de3,0x4205b0220501,0x4785b0220501,0x4205b0220501,0x4685b0220501,0x4405b0220501,0x4785b0220501,0x4405b0220501,0x4685b0220501,0x2040001000110004008004200102002080080ce3,0x0,0x808510220501,0x820510220501,0x808510220501,0x0,0x810510220501,0x2040080400110004408004200102002080082ce3,0x810510220501,0x2040080020110004408004200102002080082de3,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0xf3007d4c00798f300798799e6012fc0009bcb53001e9cc01e6f3001e679801ed98003d39801e7037c5],
[0x804080100090004408004200102001080082ca3,0xf300bb43583080bb0f303cde6012fc0009dc269001e9cc01e6f3001e679800fa98003d39801e7032b5,0x0,0x2f01020040110004528004200102002080082fe3,0x0,0x2d02020080110004528004200102002080082de3,0x0,0x804080100090004408004200102001080082ca3,0xf300003cc01e6f30811803ea600222c0007f34d9001e9cc01e6f3001e679800fa980079f9801e703345,0x1004080200090004408004200102001080083ca3,0x840510220501,0x840510220501,0x510220501,0x840510220501,0x510220501,0x0,0x808510220501,0x820510220501,0x808510220501,0x4020101000110004808004200102002080084ce3,0x810510220501,0x0,0x810510220501,0x0,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501],
[0x0,0x808510220501,0x920530220501,0x808510220501,0x0,0x0,0x0,0x0,0x0,0x920530220501,0x0,0x920530220501,0x40510220501,0x40510220501,0x510220501,0x40510220501,0x510220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2481 : TreeBound (n := 4) 106 (programCode 0x4c2907531e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x16c800111600016c80007987980f379809805f80f4e600f4e6000f4e9cc001e60f30408fcc1e707485,0x0,0xc00030001020040a0104004100402200080de3,0x0,0xc0003000102004040204008100402200080ee3,0xc0003000102004000004000100402200080ce3,0xc0003000102004080404010100402200080ce3,0xc0003000102004080404004100402200080ce3,0xc00030001020041a0804020100402200080de3,0xc0003000102004080404020100402200080ce3,0xc00030001020042a1004040100402200081de3,0xc0003000102004080404010100402200080ce3,0x0,0xc0003000102004080404200100402200080ce3,0x0,0x0,0x16c800111600016c83cc00f3000f6d045bdb3f3003cfcc1e62d9003cc79a22c7987980798001e61556,0x0,0x16c80005b200025f80003cc1e60f33cc09805f80f4e600f4e6000f4e9cc000f30798408fcc1e7032b5,0x400010000080002000800022020100800000e4,0x80080220022,0x400010000080002001000042020100800000e4,0x80084220022,0x280882220482,0x80080220022,0x280882220482,0x80084220022,0x80084220022,0x80080220022,0x80084220022],
[0x0,0x80088220022,0x0,0x80088220022,0x0,0x16c83cc1e600044580007987980f3798097e0000f4e600f4e6000f4e9cc001e60f30408c001e707485,0x0,0x4002a0000000280004000200000001800000022017600080000800040040000280000002010000008040000004080000020080402400101000000400008000210000001001087fca7,0x0,0x0,0x16c800097e00025f8001e679802dcd22e1d330079bcc07b767e279bcc79b1715b8003d398014ea4026,0x0,0x2000000008000400020000000080000000a000000028000000100000000200000000810000000040000000020000020080400000041000000100000000810000001000485de27,0x420020000090080004000200000400800000022000000080000000040000000280000200010000400020001000080001000080400000101000000400000000210000001001087f8a7,0x0,0x0,0x25f800111600025f8000f3f4301b998f300f307a180dcce1409f98798f30007d4c980e098007985426,0x0,0x25f800111600025f8000f3f4301b998f300f33cc980e832140b660798f30007d4c980e098007985426,0x0,0x445800111600025f8000f4e7301b998f300f379898004620463cc0798f30007d4c97fed98007985936,0x240009000104004128004200100802200080de3,0xf307983cc1e600007980011160003cc00007980f30079bcc007a73001e9cc003cc0000f6cc001e64dcf5,0x440011000104004128004200100802200080de3,0x0,0x40002000000028000400020000000280000002200000002000080020010000028000000040200000100800001008000001008040000010100000010002000101000000100108713a7,0xfa98003ea6000fa98003ccf300f33cc00f3f3000f6cc00f300000f6cc7980007980f3079801e610856,0x280882220482,0xa000100008000400020000000280000000a000000088000000100080000200004000010000000040040000020100000080400000041000000400010000810000001000485fe27,0x281884220c82,0x280882220482,0x280882220482],
[0x280882220482,0x281884220c82,0x281884220c82,0x280882220482,0x281884220c82,0x0,0x0,0x0,0x0,0x840021000100004008004200100002200080ce3,0x1045a58007b660000798001138a583cc00007980f30079bcc007a73001ea114b3cc0000f6cc001e64dcf5,0x1040041000100004008004200100002200080ce3,0x40001000100004008004200100002200080ce3,0x0,0x1e600097e0007b660007983ce0460f30798980139001e9cc01e6f3001e601e60f300f33cc408de7032b5,0x2006880100104004128004200100802034080de3,0x2000880020100804028004200100102010080de3,0x0,0x0,0x2040080000100004008004200100002200080ce3,0x0,0x2040080020100804028004200100102210080de3,0x8204b0214481,0x2002080000100004008004200100002020080ce3,0x8204b0214481,0x800410200481,0x840510220501,0x800410200481,0x840510220501,0x840510220501,0x0,0x42728001001020000804000002002000008002213940008008100010020000020081400001001000000804000002010000008042728010001020040004000080002000100058ff227],
[0x20410200481,0x100000400000002020000008004000010000800000004000000010100000020401400000201000004004000002010000008000100004000000020020000080004000100258d2e27,0x0,0x1020040100004008004200100002020080ce3,0x3cc007a73001e7e6003db300f44e20798f300f3f307a3a0c02f85300798f31e603cca710798798549266,0x2020080100004008004200100002020080ce3,0x0,0x20410200481,0x2020000100004008004200100002020080ce3,0x20410200481,0x410200481,0x840510220501,0x410200481,0x840510220501,0x410200481,0x0,0x3cc0008118007d4c000798799e600f31e60980139001e9cc01e6f3001e603cc1e603cc3cc408de7037c5,0x4000100100100004008004200100002000080ce3,0x4000900020100804028004200100102010080de3,0x0,0x0,0x0,0x0,0x0,0x8204b0214481,0x0,0x8204b0214481,0x800410200481,0x840510220501,0x800410200481,0x840510220501,0x840510220501],
[0x0,0x0,0x0,0x800020100004008004200100002010080ce3,0x0,0x0,0x3cc007b66001e9cc003ea600f4a940798f300f3f3079fd4c02f85300798f31e603ccd4a0798f30915266,0x0,0x422220011088800040000200000000000100022111000080000000080000000200004000010010000020040000080100000080422200101008000400000000400020001001087f9a7,0x0,0x3cc03cde600f33cc01e7e600f4a940798f300f3f307d4fcc02d9f300798f31e603ccd4a0798f30905f66,0x0,0x410200481,0x40510220501,0x410200481,0x40510220501,0x410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2626 : TreeBound (n := 4) 106 (programCode 0x4c2907531f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c80003cc1e6102300084ee71001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x0,0x5085b0220501,0x4205b0220501,0x5085b0220501,0x21000120004008004200104002100080ce3,0x0,0x0,0x3cc07981e60f4023079807b84601023000a55c4f001e9cc01e6f3001e6f3001e7e6003db3001e7037c5,0x0,0x4205b0220501,0xf3007983cc1f66f7191803cde6020460009f9753001e9cc01e6f3001e679800f6cc007a73001e703345,0x4205b0220501,0xd685b0220501,0xc405b0220501,0x20000120004008004200104002100080ce3,0xc405b0220501,0xd685b0220501,0x16c800097e00025f80003cc3cc2046000811cbf001e9cc01e6f3001e679800f6cc007a73001e7051a5,0x40201000120004008004200104002100080ce3,0x0,0x4200000080800000102000000108000000080010000100200000840000002102400004020000080400000100800000100800800000401000000808000004020000010031a50da7,0x4200000080800000102000000108000000040800000100200000840000002122080400020004000400400000801050000800400000201000000808000004020000010031840da7,0x4200000080800000102000000108000000040002000100200000840000002102080004020000010400000080800000200800400000201000000808000004020000010031840da7,0x240009000120004040204008104002100080ee3,0x240009000120004040204008104002100080ee3,0x240009000120004040a04008104002100080ee3,0x2400090001200040c0404010104002100080ee3,0x4200000080800000102000000108000000040002000100200000840000002102080004020000010400081040800200200800400000201000000808000004020000010031840da7,0x4200000080800000102000000108000000041000000100200000840000002142080400020008000400010000800010000800400000201000000808000004020000010031840da7,0x0],
[0x0,0x240009000120004044004008104002100080ee3,0x0,0x0,0x0,0x0,0x0,0xfa98003ea603df758000799e602046000813df80f4e600f4e6000f4e6f3001e9cc007a73001e703855,0x0,0xfa98003ea603dd8f80003cde602046000813a2c0f4e6007b66001e7e679800f6cc007a73001e703345,0x40001000120004000004000104002100080ce3,0x2540cd26b2800089d5f32060dc76ab2818371daaca00000ee6b280000f224d4a0003b9adac3894741af710803c893528000ee6b28000ee6c166b28ee6c166b281dcd82cd6503b9b059aca03b9b059b41359400ee88f565003bd664ca00773770d65003ba23d59400ee713f6aed379,0x40001000120004000004000104002100080ce3,0xf379803cde604fd2c80003ea600204600082ffe6799e603cde600f31e679800f6cc007a73001e703345,0x0,0x40001000120004000804020104002100080ce3,0x632220000040080000100200000000800000023191000080200000084000000200006322010010000040000080080000000080200000100800000400800000402000001001087fda7,0x0,0x0,0x0,0x600020000000080004000200000000800000023000000021000000108000000200004000010010000040000000020100000080200000100200000101000000802000001000487de27,0x0,0x600020000000080004000200000000800000023000000021000000108000000200006000010010000040000000020100000080200000100200000101000000802000001000487de27,0x8118002046000fa980003cde6010230009f8823001e9cc01e6f3001e679800f4e6003db3001e7032b5,0x0,0x0,0x0,0x0,0x40005000120004000004000104002100080ce3,0x240005000120004040204008104002100080ee3,0x40005000120004000004000104002100080ce3,0x440005000120004080404010104002100080ce3],
[0x7981e61e600025f8001023000408c000798000001e7e60079801e7e7e6003d39800f3f3001e64d995,0x16c8000d4a00025f80003cc5b22046000811db5cc1e63cc1e603cc1e679800f6cc007a73001e7051a5,0x1ed983cc97e00025f8001023000408c00079bcc1e61e607987a76cc1e7e6003d39800f3f3001e66bf95,0x16c800097e00025f80003cc3cc2046000811bcfcc1e61e61e607981e679800f6cc007a73001e7051a5,0x40005000120004004004000104002100080ce3,0x16c8000d4a00025f80003cc5b22046000811dd0601e7e601e61e601e679800f6cc007a73001e7051a5,0x0,0x40005000120004004004100104002100080ce3,0xa000000008000400020000000280000000a000000021000000108000000200004000010010000040010000020100000080080000040200000101000000802000001000485de27,0x3d39803cde6003d3980003ea60020460008300d9001e9cc01e6f3001e679800f6cc007a73001e703345,0xf30798003ea61032a980003cde6020460009f9753001e9cc01e6f3001e679800f6cc007a73001e703345,0x0,0x4085b0220501,0x4205b0220501,0x4085b0220501,0x1008041000120004a28004200104002100085de3,0x4105b0220501,0x0,0x4105b0220501,0x0,0x4205b0220501,0x4785b0220501,0x4205b0220501,0x4685b0220501,0x4405b0220501,0x4785b0220501,0x4405b0220501,0x4685b0220501,0x0,0x808510220501,0x820510220501,0x808510220501],
[0x4020101000120004808004200104002100084ce3,0x810510220501,0x0,0x810510220501,0x0,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0x808510220501,0x820510220501,0x808510220501,0x0,0x810510220501,0x2040080400120004408004200104002100082ce3,0x810510220501,0x2040080020120004408004200104002100082de3,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0x7a73001e6f300799023000408c0007980f3001e9cc007a73001e7e6003d39800f3f3001e64d995],
[0x100100090004808004200102001100084ca3,0x1e6f300799e600f31023000408c0007980f3001e9cc007a73001e7e6003d39800f3f3001e64d995,0x0,0x1020040120004008004200104002100080ce3,0x600030001000000000000200000000000000023000000080000000084000000200004000010010000008040000080100000080200000100800000400800000402000001001087f1a7,0x2020080120004008004200104002100080ce3,0x622220011000000040100200000020000100023111000080200000084000000200004000010010000040040000080100000080200000100800000400800000402000001001087fda7,0x4000100120004008004200104002100080ce3,0x2020080120004008004200104002100080ce3,0x5008100200120004a28004200104002100085de3,0x840510220501,0x840510220501,0x510220501,0x840510220501,0x510220501,0x0,0x808510220501,0x820510220501,0x808510220501,0x4020101000120004808004200104002100084ce3,0x810510220501,0x0,0x810510220501,0x0,0x820510220501,0x810510220501,0x820510220501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501],
[0x0,0x808510220501,0x920530220501,0x808510220501,0x0,0x0,0x400030001000000000000200000000000000023000000080000000084000000200004000010010000008040000080100000080200000100800000400800000402000001001087f1a7,0x0,0x600020011800000040000200002000000100023000000080000000084000000200004000010010000020040000080100000080200000100800000400800000402000001001087f9a7,0x920530220501,0x7980798f301e63cc01eca501e63cc03ccf300f3f3084e7cc01e6f3003d2a535283cc7980f307984c0dc6,0x920530220501,0x40510220501,0x40510220501,0x510220501,0x40510220501,0x510220501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2803 : TreeBound (n := 4) 106 (programCode 0x4c29075320) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108410200481,0x0,0x108410200481,0x0,0x0,0xf30003cc7983dba980408c00f301e63cfcc00f3f3003cfcc1f53f3003ccf31e9cfcc7980f3003cc99356,0x0,0x220010000100010001200000001000100022000000020000000200000000200004000010010000008040000080100000080400000101000000100000001000000001001087d3a7,0x120430204481,0x7983d02720f30f301e61e60f409c879c2720f3f3084e7cc2139f300798f31e6079884e4f300f316df66,0x120430204481,0x100410200481,0x140430204481,0x3cc1e64bf07983cc0f30f300f42fc079cbf00f3f3097e3cc28d1f300798f31e6079897e0f307983cd766,0x140430204481,0x100410200481,0x0,0x7735940ee6b2800003d77af36b280ee6b2800003c1972ed400ee6b3aa05f20000861c4680003b9aca00000773595dcd65ee6b31502f903b9b4135940ee6d04d65003ba23d59400ee88f565003b9aca000000f047fe500077359400003b9aca03b9b41359400000ee6bb5f474f19,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb478487bb04930288f8f25e1c0bfbbf8998933694e4c26d8ce0002d1e11f1ce2d1e11f1ce000005a3c3a72a4f8e7000000002feff313bcc11f336f08fbb8e11f22b0e0510d2459bea9c23e39c00000b47847d27f847c7ec7847ddc708f8f247847c8a0f08f8e72d1e1795903e39cb4785e5640f8e72d1e1795903e39c5a3c3a72a4f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df23dd824981447c7923c243dddc7a5f66c8b4dafc8f8e70000168f08f8e868f09260511f1d0d1e121eec11f1ce000002d1e163408c39e0c765d,0x0],
[0x572c5ec00000572c5ec000002b962f6000000572c5ec000000572c5ec000000572c5ed59fd8000acff2c1f3d68213fb00002b3fc5a02e7f6568213fb000005684c7f759fd80005680b9fd8000567fb67f60363adf2699980000020c643600030a7bb9fd802b3fb0567f6000159fdd67f602b3fb0159fd8360f9f61a6becacfec0159fd80000081ea4fb0acfec002b3fb0000056d5df8d9b1f43ac,0xb4784821963fe1b334cb06338ff86ccd32c18c2e00c0fc95d8e72d1e14c3af1f1ce000002d1e11f1cf68f09260511f1ce002feff313bcc11f336f08fbb8e11f22b0f15e2a6c7c5929c23e39c00000b47847d27f847c7ec7847ddc708f8f247847c8a0f08f8e72d1e1795903e39cb4785e5640f8e72d1e1795903e39c5a3c3a72a4f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df23dd824981447c7923c243dddc9c79a158fa0ffc8f8e70000168f634bc70aa6db9fe11f1d0d1e121eec11f1ce000002d1e163408c39e0c765d,0x59335b000000572c5ec000002b4517f600000572c5ec00000057d95d800000057d95d959fd8000acff2c1f3d68213fb00002b3fc5a02e7f6568213fb000005684c7f759fd80005680b9fd8000567fb67f60363adf2699980000020c643600030a7bb9fd802b3fb0567f6000159fdd67f602b3fb0159fd8360f9f61a6becacfec0159fd80000081ea4fb0acfec002b3fb0000056d5df8d9b1f43ac,0x140005000100004008004200100002200080ce3,0x0,0x0,0x0,0x0,0x0,0x445800097e00025f86a66e66001e9ccf300f4c071231ae7e63d3983cde63533a0c0010230003cc3c26,0x16c800097e00025f8001e679801e9d0c160730079bcc07b7623079bcc799e7338c003db30013044026,0x0,0x7983cc1e600025f800097e0003cc00007980001ed98000079801e7e9cc001e60000f6cc001e64d7e5,0x0,0x0,0x1ebbd0280007aef40a00004a817c80003f5476a00004a817c800077447ab2801dd11eb7cd0d53770d6500ee88f617d0d53770e536b28000f224d4f9686a9acbdd11eb7cd0d8ef4459acaee88f5a09aca0003c89353e5a1aae25ded686b11ff9b73594773594003b9acc15ece9a,0x445800111600025f8000f4e76cbd399e600f30f3799e9ce0460798799e60008118b65f530007985936,0x0,0x445800111600025f8000f4e76cbd399e600f33cc799f5320461e60799e60008118b66e830007985936,0x2200000008800000012000000028000000201000000804006003008008000010020000001080008004500021001000002002000000108000800410003001020000004000277668,0x445800111600025f8000f4e76cbd399e600f379879a04620463cc0799e60008118b65f530007985936,0x0,0x0,0x240009000104004128904020100802200080de3,0x481084220862,0x0,0x481084220862,0x481882220c82,0x481084220862,0x481882220c82,0x481084220862,0x481084220862],
[0x481084220862,0x481084220862,0x20200000080800000102000000108000000232120000800080002020000002000020000100080000400100000800100000806000001010000004004000010100000010014c7ffa7,0x0,0x0,0x0,0xf307983cc1e600007980011160003cc00007980f30079bcc007a73001e9cc003cc0000f6cc001e64dcf5,0x0,0x0,0x0,0x80080220022,0x0,0x80084220022,0x280882220482,0x80080220022,0x280882220482,0x80084220022,0x80084220022,0x80080220022,0x80084220022,0xfa98002046000fa98000799e6012fc000aafa7e601e7e601e61e601e9cc001ed98004105801e7037c5,0x80088220022,0x8118002046000fa980003cde601023000a371ae601e67981e63cc01e9cc000f4e600417f001e7032b5,0x80088220022,0xf344583cc1e600025f80011160003cc00007980f30079bcc007a73001e9cc003cc0000f6cc001e64dcf5,0x840021000100804028004200100102200080de3,0xf4ed98007b6600007980011160003cc00007980f30079bcc007a73001e9cc003cc0000f6cc001e64dcf5,0x1040041000100804028004200100102200080de3,0x40001000100004008004200100002200080ce3,0x0,0x808510220501,0x2046080100110004408004200102002204082ce3],
[0x808510220501,0x0,0x2001080040110004408004200102002200082ee3,0x2040080400110004408004200102002280082ce3,0x2002080080110004408004200102002200082ce3,0x2040080020110004408004200102002280082de3,0x820530224501,0x2002080000110004408004200102002200082ce3,0x820530224501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0x0,0x1e600097e0007b66000b6400f379803d22b80f3f3003cfcc1e62d9003ccf325f83cc7980f30f30799556,0x0,0x0,0x42728010000400008000080020010000080002200140008000100010000400020001400001001000000804000002010000008040028010000020040000080081000000100058ff227,0x3cc007a73001e7e6003db300f42fc0798f300f3f3079fd4c02f85300798f31e6079897e0f30798549266,0x0,0x0,0x4000100100004008004200100002004080ce3,0x3cc03ccf300f31e601e6f300f42fc0798f300f3f307d4fcc02d9f300798f31e6079897e0f30798539f66,0x8000200100004008004200100002004080ce3,0x410200481,0x840510220501,0x410200481,0x840510220501,0x410200481,0x0],
[0x808510220501,0x7980001e61e9cfcc01e601023000408c00088b0f3001e9cc007a73001e7e6003d39800f6cc799ede5995,0x808510220501,0x7983cc1e62d903cc798001023000408c00088b0f3001e9cc007a73001e7e6003d39800f8b2001ede5995,0x4001100040120004808004200104002200084ee3,0x0,0x4002100080120004808004200104002200084ce3,0x0,0x820530224501,0x4002100080120004808004200104002200084ce3,0x820530224501,0x840510220501,0x840510220501,0x800510220501,0x840510220501,0x840510220501,0x0,0x8410200481,0x0,0x8410200481,0x0,0x0,0x3cc007b66001e9cc003db300f4a940799e600f3f3079fd4c02f85300798f31e60798d4a0f30798549266,0x0,0x79800f3f3001e9cc00802501e63cc03ccf300f3f3086544c001f53003cde635283cc7980f307983dd0c6,0x120430204481,0x3cc03cde600f33cc01e6f300f4a940799e600f3f307d4fcc02d9f300798f31e60798d4a0f30798539f66,0x120430204481,0x410200481,0x40410200481,0x410200481,0x40410200481],
[0x410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_1843 : TreeBound (n := 4) 106 (programCode 0x4c290753) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part012_1844 part012_1845 part012_1846 part012_1847 part012_1928 part012_2009 part012_2090 part012_2171 part012_2252 part012_2253 part012_2334 part012_2335 part012_2336 part012_2481 part012_2626 part012_2803

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2965 : TreeBound (n := 4) 106 (programCode 0x4c29075431) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1081ce121c481,0x1080421204481,0x1080421204481,0x1080461208481,0x1080c6120c481,0x1080461208481,0x1080421204481,0x10804a1210481,0x1081ce121c481,0x10804a1210481,0x1080401200481,0x0,0x16c800111600016c80003cc1e61023001338de60f4e600f4e6000f4e679800fa98003d39801e7032b5,0x7736826b2f73597b9aca07736826b2f73597b9aca01dce536b280007753616577359400ee6b2f7394dacbdcd6c73594001deeefcb4ca1dd11eaca077447ab28001dd11eaca01dd11eaca001dd11eb059aca00ef59932800ee6ee1aca00eea6c2ca00ee6ee1aca00ee6d0c6e573d9,0x16c800097e00025f8000f305b2324f001bc41b20f4e600f4e6000f4e679800fa980079f9801e7051a5,0x16c80014e200053880003cc97e4ce300133957e0f4e600f4e6000f4e679801ed98003d39801e707485,0x7823ff280077712eca003ba9b0b28003bd664ca0003c8935280003b9acaee7233f191daa35139ad8e6b2caf8b2140001dcd65000003ba23d59403ba23d59401dd11eaca001dd11eaca001dd11eb41359403ba23d59400eea6c2ca003b9e83aca00ee6ee1aca00ee6d0c7b6ecd9,0x440001000010002000084002102002080080ce3,0x202000000208000002020000002080000008000080001001000080200000050812000040200000100800001008000001008004000010010000010100000100100000100108713a7,0x44580799e60004458000f307983db3000f6d3980f4e600f4e6000f4e679801ed980079f9801e707515,0x0,0x30e8d21c702800003b9acbdcd65ee6b2800eea6c2ca00000ee6b343a34ad52e25c0bdcd650773646d05e0000003b9aca0001dcd6500001dd11eaca001dd11eaca00ee88f565001dd11eaca001dd11ee83aca0077394daca01dcf41d650077394daca0077394daca00ee6d0c852ae49,0x0,0x2040001000010002000084002102001080080ca3,0x0,0x0,0x0,0x0,0x0,0x80002000001080042000000002020000800201e4],
[0x400021001000004004000000010000020040022000000080000000000000000400000002010000008040000010080000010080400000100000000404000001000000001001087ffa7,0x40000001100000001400000011000000014000201000001000080004010000058040800040200000100800001008000001008040000010000800010400000100008000100108713a7,0x0,0x40000002100000008400000081000000084000202000001000280014020000058082800040200000100800001008000001008040000010001000010400000100010000100109713a7,0x80012000401080042002000002020000800201e4,0x4000001010000001040000010100000010400020a0000010002800140a0000058282800040200000100800001008000001008040000010001000010400000100050000100109713a7,0x80022000801080042004020102020020800a05e4,0x400001001000001004000008010000008040022000000080000400040000000480000002010000002010000010080000010080400000100000000084000001010000001001087c7a7,0x0,0x40000800100000004400008001000000040002010000002010000020100000020100000208001000804000002280014000040010000800010008000100028000100000041002793a8,0x400020001000000004000000010000800040022000000080000400040000000480000002010000002010000010080000010080400000100000000084000001010000001001087c7a7,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c80003cc7983ea6001375f980f4e600f4e6000f4e6f3001e7e6003db3001e707485,0x0,0x16c800097e00025f8000f303cc2139001b4a7cc0f4e600f4e6000f4e679800f6cc007a73001e7051a5,0x40003000020002000084002102001100080ca3,0x3c893528000f224d4a003ba9b0b28003bd664ca0003c8935280001dcd68b9acdb9acafd51daf73770d65ee7a0eb2800257c7a9111a1dd11eaca0077447ab281dd11eaca001dd11eaca001dd11eb41359400eee25d9400ee729b59400eee25d9400ee729b59400ee74908af12d9,0x82000000208000000820000202480000008000080001001000080400000051012000040200000100800001008000001008020000010020000010200000100200000100108713a7,0x0,0x0,0x4020000010080000100200000100800000400000a0001020001000400000051200800040200000100800001008000001008020000010020000010200000100200000100108713a7,0x10820001000080000008200010420800001080000a0001001000080400000051012000040200000100800001008000001008020000010020000010200000100200000100108713a7,0xf379803cde60079f9803cc1e60f31e60003ea6000f4e6003d39800f4e7e6003d39800f3f3001e740995,0x0,0x0,0x0,0x0,0x0],
[0x0,0x80002000001080042000000002040001000201e4,0x0,0x0,0x400020011000000044000000010000000240022000000080000000000000000400000002010000008040000010080000010080400000100000000404000001000000001001087ffa7,0x80002002001080042000000002040001000201e4,0x80012000401080042002000002040001000201e4,0x80002000201080042000000002040001000201e4,0x80022000801080042004020102040021000a05e4,0x80002002001080042000000002040001000201e4,0x168f08f8e72d1e1795903e39cb4785e5640f8e72d1e1795903e39ed1e135abe8f8e72d1e1795903e39c2d1e2880d6f8e702d1e11f1ce0b479b0b7c78e7168f3616f8f1ce05a3cd85be3c7382d1e6c2df1e39c0b479b0b7c78e700b479b0b7c78e700b479b0b7c78e702d20e3d2ed336f08f8e7007522319dbaff4e5d5ab910cd39c05a3d8cd42b9413c23e3f63c26b57d1f1ce0002d1f7ae25ef7608fe8ac23e66de11f1ce00017438140e3cbb5dc7cd437875c0016a59801e2b8e11f1e48f08f99b7847c8a0f08f8e7005a5562fa417bc40275e,0x0,0x400020001000000004000000010000800040022000000080000400040000000480000002010000002010000010080000010080400000100000000084000001010000001001087c7a7,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3046 : TreeBound (n := 4) 106 (programCode 0x4c29075432) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1081ce6204481,0x1081084210481,0x1081ce6204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x0,0x0,0x0,0x8000a000201080042000800022080000000201e4,0x8000a002001080042000880022080080400211e4,0x80012000401080042000880022080080400211e4,0x80002000201080042000800022080000000201e4,0x80022000801080042000800022080000000201e4,0x80082002001080042000880022080080400211e4,0x80042001001080042000880022080080400211e4,0x0,0x80082002001080042000880022080080400211e4,0x0,0xf300f33cc0f30f300f30007a73001e9cc007a73000f6cc00f6cc000f6cc799e60f300f30798003ea93b6,0x0,0xf301e63cc0798f301e60007a73001e9cc007a73000f6cc00fa98000f6ccf31e60f301e60f3000408f3b6,0x0,0x0],
[0xf30000b6400088b00007987a73001e9cc007a73000f6cc00f6cc000f6cc799e607980f30798003ea93b6,0x0,0xf3000222c00088b0000f30f4e6003d398007a73002046000a531980fa98f307983cca72ed98007d51936,0xf3003cfcc1e64bf003cc007a73001e9cc007a73000f6cc00f6cc000f6cc799e607980f30798003f22bb6,0xf3000408c003db30003cc07a73001e9cc007a73000f6cc00f6cc000f6cc799e607980f30798003f2a536,0xf307983cc03ccf30000f307a73001e9cc007a73000f6cc00f6cc000f6cc799e607980f30798003ea93b6,0xf3000f6cc003db30007980f4e6003d398007a73002046000a531980fa98f307983cca72ed98007d6ff36,0xf3003cfcc03ccf3003cc007a73001e9cc007a73000f6cc00f6cc000f6cc799e607980f30798003f22bb6,0xf3003cfcc00f3f3001e600f4e6003d398007a73002046000a531980fa98f307983cca72ed98007ebe136,0xf301e63cc07a08b0001e60f4e6003d398007a73002046000a531980fa98f307983cca72ed98007d51936,0xf30079bcc01e6f3003cc00f4e6003d398007a73002046000a531980fa98f307983cca72ed98007e44936,0x0,0xf301e63cc0798f300f3000f4e6003d398007a73002046000a531980fa98f307983cca72ed98007d51936,0x0,0xf303cc3cc0f30f301e6000f4e6003d398007a73002046000a531980fa98f307983cca72ed980084e9936,0x0,0x0,0x80006000101080042000800022080000000201e4,0x0,0x0,0x0,0x80012000401080042000804022080004020301e4,0x0,0x80022000801080042000804022080004020301e4,0x0,0xf3001e9cc01e6f3001e6007a73001e9cc007a73000f6cc00f303cc0f6cc0097e0f30000f307983cc33b6,0x0,0xf3003cfcc00f3f3003cc007a73001e9cc007a73000f6cc00f303cc0f6cc0097e0f30000f307983cc33b6,0x0,0x0,0x0,0x0],
[0x0,0xf300003cc2d90f303cc000f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000811d936,0x0,0x0,0xf3000222c00088b0000f30f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000811d936,0x400000101000000204000000810000000842002100108000000420000000000000004200010000800020000000080004000080420000100080000404000001000400001001087fba7,0xf3000408c003db30003cc07a73001e9cc007a73000f6cc00fa98000f6ccf31e603cc1e60f300041271b6,0xf303cc3cc35308b0001e60f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000811d936,0xf3000f6cc003db30007980f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000813bf36,0xf303cc3cc37168b0079800f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000811d936,0xf3003cfcc00f3f3001e600f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000828a136,0xf303cc3cc0f388b0001e60f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000811d936,0xf30079bcc01e6f3003cc00f4e6003d398007a7300222c000b095980fa99e60f30798d4bf530008210936,0x0,0xf301e63cc0798f300f3000f4e6003d398007a7300222c000b095980fa99e60f30798d4bf5300084e9936,0x0,0xf303cc3cc0f30f301e6000f4e6003d398007a7300222c000b095980fa99e60f30798d4bf53000811d936]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3127 : TreeBound (n := 4) 106 (programCode 0x4c29075433) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1081ce121c481,0x1080421204481,0x1080421204481,0x1080461208481,0x1080c6120c481,0x1080461208481,0x1080421204481,0x10804a1210481,0x1081ce121c481,0x10804a1210481,0x1080401200481,0x0,0x16c800111600016c80007981e613ef000c93de60f4e6003ea6001e7e679800fa98003d39801e7032b5,0x0,0x16c800097e00025f80007985b2324f0008c81b20f4e6007b66001e7e679800fa980079f9801e7051a5,0x25f800097e00025f80007983cc222c00088b3cc0f4e6007b66001e7e679800fa980079f9801e7051a5,0x0,0x440001000010004000104004102002080080ce3,0x202000000208000002020000002080000008000100008001000080200000080814000200200000200800002008000002008004000010010000010100000100100000100108713a7,0x25f81e61e600025f80007983cc222c00088b3cc1e7e6007b66001e7e679801ed980079f9801e7056b5,0x1dce536b281dcda09aca0077447ab28077394daca0077447ab280003d77a0502540be40773597b9e83aca773d075940003d7b5bd97653ba9b0b2803ba9b0b28003b9e83aca03b9e83aca003b9e83bb86b2800ef59932800ee6ee1aca00eea6c2ca00ee6ee1aca00ee6d0c70b9979,0x2e27e59933f389f9664cfbdcd65ee6b280077712eca00000ee6b3389f98701f955919713f30e03f2ab230000000773594001dcd6500001dd11eaca001ddc4bb2800ee6ee1aca01dd11eaca003b9e83e83aca0077447ab280077394daca03b9e83aca0077394daca00ee6d0c84c5549,0x0,0x2040001000010006000084004102001080080ca3,0x0,0x0,0x0,0x0,0x0,0x80400010001080042000000802020000800201e4],
[0x0,0x7981e61e607987980007a73001e9cc007a7300003cde6000079803cc7980007980000798003cc33b6,0x0,0x4200000010800000102000000108000000220200000200044002002000008808400008020000020080000200800000200800040000410000001000400010100000010010a513a7,0x3c893528003bd664ca003ba9b0b28003bd664ca0003c8935280000ee88f565003ba23d59400ee88f56500ee88f565000ee88f56500001dcd650ee729b59403b9aef40be4fd51e1f394daca1dcd68b9aca00257c590bdcd68b9aca0077394daca01dcda09aca0007783d524a3fa,0x3ba9b0b2800eea6c2ca0007823ff280077712eca0007823ff28000b2d50617c81ebbd028000773599b45055012a05f20b68eb84e4b0dce536b2807736826b2803b9e83aca03b9e83aca003b9e83ad17359477359b73595dd4d8594000ee6d04d650eee25d94000ee6d4ae8b2e79,0x4400110001080042004020902020020800a05e4,0x2002000008008000008020000010080004002a000100008000400040000000480000002010000001040000010040000020080400000100000000084000000810000001000887ce67,0x2002000002008000010020000010080000002010000008040000008040000020100338299414400a010030c0014044000010020001941420002005100001404100000010280ff5a8,0x0,0x40002000100008000000020001000080004002a000100008000400040000000480000002010000001040000010040000020080400000100000000084000000810000001000887ce67,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c800079897e3f99000445f981e7e6003ea6001e7e6f3001e7e6003db3001e707485,0x0,0x16c800097e00025f80007983cc2046000811bcc0f4e6007b66001e7e679800f6cc007a73001e7051a5,0x40005000020004000104004104002100080ce3,0xef59932800eea6c2ca0003c893528003bd664ca0003c8935280003c89352803b9aca01dcd68b9b413594eea6c2ca0003c89acd4c997ba9b0b2803ba9b0b28003b9e83aca03b9e83aca003b9e83b41359400eee25d9400ee729b59400eee25d9400ee729b59400ee6d480b83979,0x0,0x0,0x0,0x0,0x0,0xf379803cde60079f9803cc1e60f33cc000f4e6003cde600f379801e7e7e6003d39800f3f3001e740995,0x7981e61e6000079800000007983cc000f300003cde600f379801e7e7e6003d39800f3f3001e64d995,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x401010001080042000001002040001000201e4,0x0,0x0,0x8118007b6600081180007a73001e9cc007a7300003cc07983cfcc03ccf300003cc00f3f30003d5b1b6,0x400050001080042000001002040001000201e4,0x4400110001080042004021102040021000a05e4,0x400410001080042000001002040001000201e4,0x1dd3af41b92f73597b9aca001ddc4bb28000f224d4a00000ee6b2f73660e41ca9534eee6b280007ea8ed5dcd6500001dcd68b9aca00001dd11eaca0007823ff2801dce536b2803b9e83aca003b9e8423d65d2ae0f59403b9ae8449a940077359400000eee25d94000ee6d0c844ec69,0x0,0xf379801e7e60079f98000f4e6001e9cc007a73cd698b1ae60f708c03cde619aca0c03dc230003d3d426,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3208 : TreeBound (n := 4) 106 (programCode 0x4c29075434) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080421204481,0x1080000210481,0x1080421204481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000208481,0x1080000200481,0x1080000210481,0x1080000200481,0x1080000210481,0x1080000200481,0x0,0x16c800111600016c80003cc1e61023000408de60f4e6003ea6000f4e679800fa98003d39801e7032b5,0x8040021000804020100804020102002080080ce3,0x16c800097e00025f8000b645b2324f000c941b22dae600b826002dae679800fa980079f9801e7051a5,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0,0x0,0xf300003cc2d90f30b640007a73001e9cc007a73001e9cc0088b0001e9cc799e607983cc079800445b3b6],
[0xf30000b6400088b00007987a73001e9cc007a73001e9cc0088b0001e9cc799e607983cc079800445b3b6,0x0,0xf3000222c00088b0000f30f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed98007d51936,0xf300003cc0f30f3003cc007a73001e9cc007a73001e9cc0088b0001e9cc799e607983cc079800445b3b6,0xf3000408c003db30003cc07a73001e9cc007a73001e9cc0088b0001e9cc799e607983cc07980044dc536,0x0,0xf3000f6cc003db30007980f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed98007d6ff36,0xf3003cfcc0f30f3003cc007a73001e9cc007a73001e9cc0088b0001e9cc799e607983cc07980044d4bb6,0xf3003cfcc00f3f3001e600f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed98007ebe136,0xf301e63cc07a08b0001e60f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed98007d51936,0xf30079bcc01e6f3003cc00f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed98007e44936,0x0,0xf301e63cc0798f300f3000f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed98007d51936,0x0,0xf303cc3cc0f30f301e6000f4e6003d398007a73003ea60011ae5981ed98f307983cc97fed980084e9936,0x0,0x16c800111600016c80012fc7983ea6001375f984c0e600f4e6004c0e6f3001e7e6003db3001e707485,0x0,0x16c800097e00025f80007983cc2046000811bcc1e7e6007b66001e7e679800f6cc007a73001e7051a5,0x80000220481,0x280842220481,0x80000220481,0x280842220481,0x80000220481,0x481084220481,0x80000220481,0x481084220481,0x80000220481,0x0,0x0,0x0,0x0],
[0x0,0xf300003cc2d90f303cc000f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936,0x0,0x0,0xf3000222c00088b0000f30f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936,0xf303cc3cc2f7e8b0079800f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936,0xf3000408c003db30003cc07a73001e9cc007a73001e9cc008118001e9ccf31e603cc1e60f300041271b6,0xf303cc3cc2d988b0001e60f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936,0xf3000f6cc003db30007980f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000813bf36,0xf303cc3cc2f7e8b0079800f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936,0xf3003cfcc00f3f3001e600f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000828a136,0xf303cc3cc0f388b0001e60f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936,0xf30079bcc01e6f3003cc00f4e6003d398007a7300408c001227d981ed99e60f30798b65f530008210936,0x0,0xf301e63cc0798f300f3000f4e6003d398007a7300408c001227d981ed99e60f30798b65f5300084e9936,0x0,0xf303cc3cc0f30f301e6000f4e6003d398007a7300408c001227d981ed99e60f30798b65f53000811d936]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3289 : TreeBound (n := 4) 106 (programCode 0x4c29075435) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983d3b69db4e607983cc0001e679803ccf300799e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3290 : TreeBound (n := 4) 106 (programCode 0x4c29075436) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80402010001080042002010082080012000613e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3291 : TreeBound (n := 4) 106 (programCode 0x4c29075437) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080c62204481,0x1080842218481,0x1080c62204481,0x1080842208481,0x1080842208481,0x1080842218481,0x1080842208481,0x1080842208481,0x1080842210481,0x1080842210481,0x1080842210481,0x1080842208481,0x0,0x16c800111600016c8003cc2046102a9840cac46799e603cde600f31e679800fa980079f9801e703345,0x8040021000802010080404010102002080080ce3,0x16c800097e00025f8003cc2412325698458a012799e603cde600f31e679800fa980079f9801e7051a5,0x280842220481,0x280842220481,0x6818c2220481,0x280842220481,0x280842220481,0x4818c2220481,0x6818c2220481,0x4818c2220481,0x280842220481,0x0,0x0,0x0,0x0,0x0,0xf307983cc1e60000798000f4e6003d398007a7300007987983cc003d3987980007980f307980079857b6],
[0x0,0x200008000800020002000080008000000080400000402000001008000002010000000080000000000200010000000402000400000008000000004001000010000002000152e28,0x0,0xf307980001e61023798000f4e6003d398007a730000000f3097e003d398f300001e61e60798007985906,0x1e4ae4d5b9281dcda09aca0007823ff28077394daca0077447ab2f74ebd07adca69c0ee9d729a7ee6b3704862e534fdcd6c7359400003b9b059aca00ee7a0eb283b9b059aca07735cf9aca07735cfa26609296af3594773595e449a940077359400000eee276b94d46e6d0c844fc09,0x20000000080001000200000008800000020100000080400000100800000201000000000000000040010000800000080600100000000100000000400080001000000400027b228,0x1ed98007b66000fa98000f4e6003d398007a7301e60f3faa1bac223398f3003cde61f537980445a3f06,0x7736826b281dcda09aca07736826b28077394daca0077447ab2f74ebd07adca69c0ee9d729a7ee6b3704862e534fdcd6c7359400003b9b059aca00ee7a0eb283b9b059aca07735cf9aca07735cfa23eeb94daf3594773595e449a940077359400000eee276b94d46e6d0c844fc09,0x0,0x0,0x1dd3af41b92f73597b9aca0007823ff28000f224d4a00000ee6b2f74ebd07adca69c0ee6b28000ee6b37047fe50001dcd6c7359400003b9b059aca00ee7a0eb283b9b059aca07735cf9aca07735cfa26476d4977359b735941e449a940077359400000eee25d94000ee6d0c844fc09,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c8003cc25f83ead983d3bdf8f31e603cde600f31e6f3001e9cc007a73001e707515,0x0,0x16c800097e00025f8003cc222c204d9844d3a2c799e603cde600f31e679800f6cc007a73001e7051a5,0x280842220481,0x280842220481,0x6818c2220481,0x280842220481,0x280842220481,0x4818c2220481,0x6818c2220481,0x4818c2220481,0x280842220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x7980001e60798798000f4e6003d398007a730000001e60f30003d399e600007983cc0f30007985756,0x0,0x200010000800000002000108008000000201000000804000001008000002010000000000000000000200010000000806002000000008000000010001000020000004000273228,0x1020000001080000004200000010800000020100000080400000100800000201000010000800040042020101008000480600200000080800000201000100802000002402127b228,0x7981e61e60004458000f4e6003d398007a730000001e60f30003d399e600007983cc0f30007985756,0x1ed98007b66000fa98000f4e6003d398007a7301e60f4eda76cc223399e6003d3983db3f300445a3d56,0x7981e61e600f3798000f4e6003d398007a730000001e60f30003d399e600007983cc0f30007985756,0x3b9bb86b280ee6ee1aca03b9bb86b28077394daca0077447ab280000ee88f56500ee88f5650077447ab280077447ab2800ee88f56501dcd65f57db3e8b982e717969a8183f3597b9aca001dce536b9f3594003c11ffa225179ba97a03b9b059acaee6b2f73594003b9acc051450a,0x0,0x1dd3af41b92f73597b9aca0007823ff28000f224d4a00000ee6b2f74ebd07adca69c0ee6b28000ee6b37047fe50001dcd6c7359400003b9b059aca00ee7a0eb283b9b059aca07735cf9aca07735cfa23eeb94daf3594773595e449a940077359400000eee25d94000ee6d0c844fc09,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3372 : TreeBound (n := 4) 106 (programCode 0x4c29075438) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80402010001080042004020102080022000a05e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3373 : TreeBound (n := 4) 106 (programCode 0x4c29075439) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10814a4204481,0x1081084210481,0x10814a4204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x16c800111600016c803cc1e7e6109c83cc5b3e9cc1e63cc1e603cc1e679801ed980079f9801e703855,0x8040021000804020100804020102002080080ce3,0x25f800097e00025f803cc1e9cc22a583cd119cfcc1e63cc1e603cc1e679801ed980079f9801e7056b5,0x481084220481,0x2818c4220481,0x481084220481,0x2818c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x2200000008800000012000000018000420021a0001000200420000200040084000200010000800040001000080001000080402000101000000400008000210080001001087fca7],
[0x0,0xacfec02b3fb02b3fb00acfec0acfec02b3fb02b3fb00acfec0acfec02b3fb02b3fb00000002b4109fd8000568213fb000015a084fec00000ad0427f60000ad0427f600000ad0427f6159fd80acfec000000000000acfec0567f6000567f602b3fb0000159fd80ad06dbf1040df88567f60000002b3fb000000000567f6567f600159fd959fd80159fd800000ad145fd800002b3fb0173b6ba0ac,0x0,0x20200000080800000102000000108000420021a0001000200420000200040084000200010000800040001000080001000080420000101000000400040000210800001001087fca7,0x15aaa7ec0000056aa9fb0000015aaa7ec0000056aa9fb0000015aaa7ec0000015cb17b00000002b4109fd8000ad0427f6000015a084fec00000ad0427f60000ad0427f600000ad0427f64e636f2731b7800567f602b4109fd80acfec01398dbc9cc6de0004e636f2731e2bfb0159fd959fd802731b7d67f600002b4109fd80acfec0567f60350f6eb77dd800002733117d800002b4497a83cf54fac,0xacfec00000002b3fb00acfec0acfec02b3fb02b3fb000000164cd6c00000059335b00000002b4109fd8000568213fb000015a084fec00000ad0427f60000ad0427f600000ad0427f6159fd80acfec000000000000acfec0567f6000567f602b3fb0000159fd80ad06dbf1040df88567f60000002b3fb000000000567f6567f600159fd959fd80159fd800000ad145fd800002b3fb0173b6ba0ac,0x7823ff2800eea6c2ca000ef5993280077712eca0007823ff280000ee88f56501dd11eaca001dd11eaca00ee88f565000ee88f5650773597b9e83acbdcd6a4d9f1fc657aad273597b9e83acbdcd68b9aca00eea6c2ca7735a2e6b329b3e264d8a000eea6c2ca003b9ad3750597a,0xc1b7feeb28ee6b639aca0c1b7feeb28000c570bd203b9bb86b280000ee88f56501dd11eaca000ee88f56500ee88f565000ee88f5711b7168db9726b2f73594c1b7168db8840c1b7168df41ecbdcd73e6b29836e5c9acbdcd65ee6b30f72878230a00183a9bbca003ba6e7751440a,0x1dce536b28077394daca01dce536b28077394daca0077447ab280000ee88f56501dd11eaca000ee88f56500ee88f565000ee88f566dcd65ee6c166b2f73594c1b7168db8840c1b7168df41ecbdcd73e6b283b9b059acbdcd65ee6b2faf5521230a00183a9bbca003ba8c44b6440a,0x200200000800800000402000002008000434021a0001000200400000200040080000200010000800040001000080001000080434000101000000400040000210000001001087fca7,0xee7a0eb281dcda09aca00ee7a0eb280ee6ee1aca00ee7a0eb280000ee88f56501dd11eaca000ee88f56500ee88f565000ee88f565ee6b2f736826b2f73594c1b7168db8840c1b7168df41ecbdcd73e6b281dcda09acbdcd65ee6b2f9187bc230a00183a9bbca003ba6e7751440a,0x0,0x0,0x0,0x0,0x0,0x16c800111600016c803cc1ed983f1f83cc9859bcc1e63cc1e603cc1e6f3001e9cc007a73001e707515,0x0,0x25f800097e00025f803cc1e9cc20bf83cc981cfcc1e63cc1e603cc1e6f3001e9cc007a73001e7056b5,0x481084220481,0x2818c4220481,0x481084220481,0x2818c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x2200000008800000006000000028000420021a0001000200400000200040080000200010000800040001000080001000080400000101000000400000000210000001001087fca7,0x4340200000100800040002000004008000434021a0001000200400000200040080000200010000800040001000080001000080434000101000000400040000210000001001087fca7,0x20200000080800000102000000108000420021a0001000200420000200040084000200010000800040001000080001000080420000101000000400040000210800001001087fca7,0x42000000408000001020000001080000000804000004020000020100000020100220011000ee5e772f000480024080004000800110004000772f200000024200000090284d2ba8,0xee6b2bb9acdb9acaee6b36e6b280007aef40a0001ebbd02800077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565000000003b9acbdcd650773597b9aca00773597ba5f70639686a9aca00000ee6b2f735947735b1cd65773594000eee25d94003b9acc137225a,0x3ba9b0b2800eea6c2ca0007823ff280077712eca0007823ff2800077447ab2801dd11eaca000ee88f56500ee88f565000ee88f5653b9acbdd11eacbdcd650773597b9aca00773597ba5f70639686a9aca0077447ab2f735947735b1cd65773594000eee25d9407aef447ae3c25a,0xee6b2bb9acdb9aca07736826b280007aef40a0b2d14c6b2800077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565000000003b9acbdcd650773597b9aca00773597ba5f70639686a9aca00000ee6b2f735947735b1cd65773594000eee25d94003b9acc137225a,0x1dce536b28077394daca01dce536b28077394daca0077447ab280000ee88f56501dd11eaca000ee88f56500ee88f565000ee88f566dcd65ee7135b8b46dc42c1b7168db8840c1b7168df41ecbdcd6c735943b9bb86b341b710f735c4a9c03cbdd400183e55694003ba8c44b6440a,0x0,0xee7a0eb281dcda09aca00ee7a0eb280ee6ee1aca00ee7a0eb280000ee88f56501dd11eaca000ee88f56500ee88f565000ee88f5711b7168dbe91b8b46dc42c1b7168db8840c1b7168df41ecbdcd6c73595836f0f6b341b710f735c5f19393bdd400183e55694003ba6e7751440a,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3454 : TreeBound (n := 4) 106 (programCode 0x4c2907543a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3455 : TreeBound (n := 4) 106 (programCode 0x4c2907543b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10814a4204481,0x1081084210481,0x10814a4204481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084208481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x1081084210481,0x0,0x0,0x804002100080c040301004040102002080081ce3,0x0,0x481084220481,0x2818c4220481,0x481084220481,0x2818c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0,0x0,0x0],
[0x600000008800000006000000018000000080400000402000001008000002010000010080080000000840010000000402000400020008000000084001000010000002800152e28,0x2000000008000100020000400080000002010000002010000020100000020100100000000000804001000080000008040010000000010000000100008000100000040002793a8,0x0,0x0,0x81180020460008118000f4e6003d398007a731e6003d3983cc003d39879800f4e60f30798016d800d6,0x2000000008000100020000000880000002010000002010000020100000020100100000000000804001000080000008040010000000010000000100008000100000040002793a8,0x0,0xf37980799e600f3798000f4e6003d398007a731e607987983cc003d3987981e61e60f307981eda78756,0x4020000080080000040200000100800000008040000040200000100800000201000001008008000008004001000000040200040000004800000800400100001000008201c152e28,0x1200008000800004002000000048000000080400000402000001008000002010000010080080000002040010000000402000400100008000000204001000010000002000152e28,0xf379803cde60079f98000f4e6003d398007a731e603cc7983cc003d3987980f31e60f307980faaf1f56,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x481084220481,0x2818c4220481,0x481084220481,0x2818c4220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x481084220481,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x7980001e60798798000f4e6003d398007a737980001e60f30003d399e600007983cc0f30007985756,0xa00000004800000012000000028000000080400000402000001008000002010000010080040000002100008000000402000800080004000000210000800020000002000152e28,0x0,0x81180020460008118000f4e6003d398007a73798003ea60f30003d399e6000fa983cc0f30016d800d6,0x7981e61e60004458000f4e6003d398007a737980001e60f30003d399e600007983cc0f30007985756,0x8200000040800000102000000208000000080400000402000001008000002010000010080040000020100008000000402000800080004000002010000800020000022001152e28,0x7981e61e600f3798000f4e6003d398007a737980001e60f30003d399e600007983cc0f30007985756,0x40200000800800000402000001008000000080400000402000001008000002010000010080040000400100008000000402000800000044000040010000800020000402038152e28,0x0,0xf379803cde60079f98000f4e6003d398007a737980799e60f30003d399e601e67983cc0f301eda78756,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3536 : TreeBound (n := 4) 106 (programCode 0x4c2907543c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf307983cc1e60f307983cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3537 : TreeBound (n := 4) 106 (programCode 0x4c2907543d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x182428204481,0x16c800111600016c81e601e679800097e111804601e7e601e61e601e63cc01e6f30079bcc01e703855,0x182428204481,0x0,0x1ebbd02800012a05f20000fd51da8000218711a00002cb417c30e2647b20df70e9dcf43b3265000f233bb52f73d163ff45d514e275283b9ad1735941dcddc35941dcd73e6b283b9ad8e6b283b9acaee6b2f73594773595dcd6c7359b73594ee6b2f73594ee6b36e6d0c842a8b9,0x22000000048000000120000000180006002600129000000040024000840008004a000010004000020010000080010000080400240100000000084000001010009001001087cba7,0x16c800111600016c8079801ed980009f78f5064601e7e601e61e601e601e60f307983cc3cc1e7032b5,0x0,0xa00000008800000012000000018000100008000400001001000000104000000008000040080000400100000800100000800080000400800001001000004001000010018a55da7,0x1ebbd028000218711a0000fd51da8000218711a00002cb41834bcb5ab5e8f127a80000d09dc3000000000000007823ff280000ee6b283b9ad8e6b283b9b4135941dcd73e6b283b9ad8e6b283ba615cb005f0359400001dcd65ee6b2f753616500077359400000ee6d0c852ae49,0xc0003000000480202004080100801040081ca3,0x182428204481,0x0,0x0,0x0,0x0,0x0,0x40000000201000000c0000000805000000c0002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x0,0x0,0x400020000010008004000200000500280040002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x0,0x0,0x400000100010000104000001000500001040002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x400000a0001000800400000a000500280040002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x0,0x0,0x0,0x0,0x400002000010008004000080000500080040002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7],
[0x0,0x400010000010010004000100000500100040002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000103d08713a7,0x0,0x0,0x182428204481,0x140005002000880002004080100002020080ce3,0x182428204481,0xc0005000100884022004080100101084080fa3,0x0,0x0,0x16c800097e00025f81e6001ed980019278f5064601e7e601e61e601e601e60f30f307983cc1e703345,0xc0005000100884022004080100101084080fa3,0x25f80005b200025f807981e697e00118f85b5ea601e7e601e61e601e60f301e6f3003ccf301e7037c5,0x0,0x140005000000880202004080101002040081de3,0x182428204481,0x0,0x0,0x0,0x25f800111600025f80799e60f3000118f800079807987980799e601e9cc001e60000f6cc001e64d7e5,0x0,0x445ad9097e0001e60000f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x0,0x0,0x1008040201080042000000002080002000201e4,0x0,0x0,0x1000040201080042000000002080002000201e4,0x1020040801080042000000002080002000201e4,0x0,0x0,0x445ad9097e0001e60f30f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26],
[0x0,0x1000040001080042000000002080002000201e4,0x0,0x445800097e0001e60000f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x0,0x0,0x4000020010000080100000800100000c000200001000080040000002050008808040000200100000801000008001000008040000010100000010400000101000000100508713a7,0x3b9e83aca0eea6c2ca0003b9e83aca03bd664ca0003b9bb86ee1acdb9acbdcd65ee6b2bb9aca1dcd82cd650001ddc4bb657817947ab283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283ba23d594000f047fe5000eee25d94000f047fe5000eee25d94000ee7bf320d73d9,0x0,0x42000000100800001020000001028004000200001000080040000002050008808040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x1e60f303cc1e6079842722dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x1f360c83d3b66079805b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x40010000100010001000100001000104000200001000080040000002050008808040000200100000801000008001000008040000010100000010400000101000000100508713a7,0x40002000100800001000020001028004000200001000080040000002050008808040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x1e679803ccf300799ebb22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x1ee11803ccf30079805b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea56925,0xee6b281dcda09acbe9e37d8dd893b863b9aca077359400773597ba23d59401dd11eaca001dd11eaca00ee88f565000ee88f568b9aca0000000000003d84ad7df6277626cee1aca0001dcf41ddc359400001dcd650000f5de817b9b342bb7dee6b2f735940003b9acc0ffa73a,0x1f173303d3b66079805b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x1e9cc003d398007a735b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x1f435683cc798079805b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ea93525,0x1e9cc003db30007b665b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001f1ee925,0x1ebc8c83cfdb3079805b22dce2c81eda7300007980798f300f31e601e9cc003db3000f6cc001ec80ea5,0x400020000000080004000200000000800060002000080000000600000000400000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0x0,0xf362bad901e60001e60000f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x0,0x0,0x8040201080042000000002080002000201e4,0x8000800040004000100002000200008200022001100080104000000409000081010000080080000400040000200100000804000000410000002040000008100000010044c5ae27,0x822000004088100010220400020081020002200110008010400000040900008101000008008000040004000020010000080400000041000000204000000810000001004485ae27,0x40201080042000000002080002000201e4,0x20040801080042000000002080002000201e4],
[0x800800004004000010002000020008020002200110008010400000040900008101000008008000040004000020010000080400000041000000204000000810000001004485ae27,0x820200004080800010202000020008020002200110008010400000040900008101000008008000040004000020010000080400000041000000204000000810000001004485ae27,0xf362bad901e60001e60f30f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x822000004080100010000400020081020002200110008010400000040900008101000008008000040004000020010000080400000041000000204000000810000001004485ae27,0x40001080042000000002080002000201e4,0x82224000408c900010002000020089020002200110008010400000040900008101000008008000040004000020010000080400000041000000204000000810000001004485ae27,0xf362b80001e60001e60000f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x200048001080042000001002080002000201e4,0x0,0x1ed9ad93ea6000f300000f4e6001e9cc007a740a2b71190000000003cfcc1e6c5700003cc0003cc3c26,0x0,0x0,0x4008100201080042000000002080002000201e4,0x0,0x0,0x4000100201080042000000002080002000201e4,0x4020100801080042000000002080002000201e4,0x0,0x0,0x1ed9ad93ea6000f300f30f4e6001e9cc007a740a2b71190000000003cfcc1e6c5700003cc0003cc3c26,0x0,0x4000100001080042000000002080002000201e4,0x4100104001080042004020802080022000a05e4,0x4000100001080042000000002080002000201e4,0x4200108001080042004021002080022000a05e4,0x0,0x40000020100000081000000801000000c00020000100028004000002005000a880040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x0,0x0,0x40200000100080001002000001002800400020000100028004000002005000a880040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x77447ab2f73594000000077447ab332d061b9aca0077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565000000000000000003ba23d597b9acbdcd65003ba23d599968a6359400001dcd650000f5de817b9acbdcd650000f5de8140003b9acc138a8fa,0x77447ab281dcda80e2340773770d6507739c5d09f2f7465b42b83acdb9acbdcd65ee6b2bb9aca7735b1cd65003b9bb86b6b1d0a0166b283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283ba23d594000f047fe5000eee25d94000f047fe5000eee25d94000eea8a738573d9],
[0x40001000100001001000010001000010400020000100028004000002005000a880040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x40002000100080001000020001002800400020000100028004000002005000a880040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x773597ba23d597b9aca00773597ba5f70639682f0077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565000000000000000003b9aca003b9acbdcd65003ba23d599968a6359400001dcd650000f5de817b9acbdcd650000f5de8140003b9acc138a8fa,0x0,0x0,0x77447ab281dcda09aca00773770d650773594ee6b2f7465b42b83acdb9acbdcd65ee6b2bb9aca7735b1cd65003b9bb86b6b1d0a0166b283b9e83aca0ee6b36e6b283b9bb86b283b9ad8e6b283ba23d594000f047fe5000eee25d94000f047fe5000eee25d94000eea8a738573d9,0x40020000100080001000800001000800400020000100028004000002005000a880040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x2b3fb00000ad553f6002b3fb02b3fb00000ad553f60046477e2b3fb01191df8acfec00002b4109fd80000ad0427f6000002b4109fd8000568213fb00000568213fb00000ad0427f600000000000000000000005684c7f60159fd81037e2000056836df882323bf159fd808c8f119fd80000000567f600000057d95d80acfec0567f600000057d95d8002323c467f600000081bf104362b4ed2c,0x40100000100100001001000001001000400020000100028004000002005000a880040000200100000801000008001000008040000010100000010400000101000000103d08713a7,0x77359400079126a507735a2e6b28007823ff28b2d06ce6b280077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565000000000000000003c8935283b9acbdcd65003d006abc5968a6359400001dcd650000f5de817b9acbdcd650000f5de8140003b9acc138a8fa,0x400020000000080004000200000000800060002000080000000600000000400000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0x0,0x840041000088482012004080100081002080ca3,0x0,0x840041000088484032004080100081004080fa3,0x8400410010080c02020040801010010c0081ca3,0x0,0xee7a0eb280ee6ee1aca07736826b280ee6ee1aca00ee7a0eb280000007737fb9ac184d5900d6500002679aae839ad8e6b74f355d7e6b283b9ca6d6507735b1cd6507736826b283b9ad8e6b283ba23d594000f0d2c2ae48ee6b2800007753d89a940ef050eab920ee6d0c6e52d89,0x0,0x8400410010080c02020040801010010c0081ca3,0x0,0x168f09ad5f47c738b47874e549f1ce2d1e1d39527c73ad1e14c3af1f1ce5a3c2f2b207c738b47874e549f1ce0b478fc3f7fd0105524de554924bc95000b52cc00eff380000168f0b164fd755a8000005a3c23e39c00000000000002d1e121eec11f1ce0000b47847c7434784a99191f1d0d1e12a64647c74347848217423e3a1a3c254c8c8f8e868f09260511f1d0d1e121eec11f1d0d1e9f772049792fa3d8cd42b8e7002d23b5b40c39c00b47847c7380000b4784a99191f1cf69071e9768e7002d1e11f1ce000002d1e135c2a4ec649bb7d,0x840041000008080002004080100801040080ca3,0x840041000008080002004080101001000080ca3,0x8400410010080c0202004080102001080081ca3,0x0,0x1040041001008080202004080104002100081ce3,0x0,0xf307980001e600007985b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0xf362bad901e60000000000f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x3000c0002000000008000800008002010000004020000020100000020100000000001000c8606000020000000804004000000010000800640002000100000004000272ba8],
[0x0,0x8000201080042000000002080002000201e4,0x79800f3f3001e7e60042722d916c81e60f300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x798d4a0f307981e60005b22d916c81e60f300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x201080042000000002080002000201e4,0x20000801080042000000002080002000201e4,0x7980798f300f31e601ebb22d916c81e60f300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x7987980f300001e60005b22d916c81e60f300007980798f300f31e601e9cc003db3000f6cc001ea56925,0xf362bad901e60000000f30f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x798b640f307981e60005b22d916c81e60f300007980798f300f31e601e9cc003db3000f6cc001ea56925,0x1080042000000002080002000201e4,0x20100804001080042020100802080102004221e4,0x1080042000000002080002000201e4,0x40201008001080042040201002080202008241e4,0x0,0x8000091961000400400000200200000a0002200110008010400000040900008101000008008000040004000020010000080400000041000000204000000810000001004485ae27,0x0,0x0,0x0,0x3b9aca00000ee6b28ee6b36e6b280000ee6b28ee6b36e6b2bb9aca0077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565000000000000000003ba23d597b9acbdcd65003ba23d595dcddc359400001dcd650000f5de817b9acbdcd650000f5de8140003b9acc15ece9a,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x554800100010000105540001000500001040002000010002800400000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7,0x20020800801080042004020102080022000a05e4,0xf3007980000f300001ebb21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x20000800001080042000000002080002000201e4,0x20100804001080042020100802080102004221e4,0x20100804001080042020100802080102004221e4,0x20200808001080042040101002080102004261e4,0x0],
[0xf3079ad901e60000000000f4e6001e9cc007a73f36371190000000003cfcc1e6c5700003cc0003cc3c26,0x0,0x0,0x0,0x0,0xee6b3e5a0bfb9acaee6b29dcd68b9acbdcd6a9682f1dcd7b5a0c373597b9acbdcd65ee6b283b9ad8e6b45cd650ee6b3aa064b682f0ee6b283b9b059aca0ee6c166b283b9bb86b283b9ad8e6b283ba23d5940077536165001dd4d8594000f047fe5000eee25d94000eee4421445159,0x0,0x20000801080042000000002080002000201e4,0x0,0x0,0x0,0x0,0x1080042000000002080002000201e4,0x100004001080042000000802080002000201e4,0x1080042000000002080002000201e4,0x200008001080042000001002080002000201e4,0x0,0x0,0x0,0x0,0x0,0xd4a00f46c801e7e600427238f56c82d90f300007980798f300f31e601e9cc003db3000f6cc001ec80ea5,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x40001000201080042000000002080002000201e4,0x40021000801080042004020102080022000a05e4,0x0,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x0,0xf3079800000000000005b21e616c80000f300007980798f300f31e601e9cc003db3000f6cc001e68a925,0x40001000001080042000000002080002000201e4,0x40101004001080042020200802080202008261e4,0x40201008001080042040201002080202008241e4],
[0x40201008001080042040201002080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3762 : TreeBound (n := 4) 106 (programCode 0x4c2907543e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80400010001080042020000802080002000201e4,0x16c800111600016c80007a73001e9cc007a731e603cde6000204603cfcc1e60f30000b640003cc33b6,0x0,0x180488284222,0x180488284222,0x80488280222,0x180488284222,0x0,0x2becaec000000afb2bb0000000360f9c00000059335b0000000614f4c0000000d83e700001191df881bf1030aa59fb00000c2a9684284c7f602b410a132084fec081bf1046477e159fd80acfec0acfec02b3fb159fed9fd8000567f600159fd959fd800159fd8ad0427f600002b3fb0159fd80567f62b3fb0015a132084fec00567f8b3fb000ad145fd800000acfec2b3fb00159fda11f45f29f2b,0x180488284222,0x7735a2e6b2800003b9aca7735a2e6b28ee6b639aca003ba9b0b2800077447ab28003ba23d594077447ab280077447ab2800ee88f5dc3594000003b9acaee6b9f3597f54778e6b2807736826b28ee6b28ee6b2800000773594ee6c167a0eb2800ee6b45cd651dcd653b9acc165742a,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x25f800097e00025f8003cc222c2233983db531f001e603cde6f3001e679801ed980079f9801e7056b5,0x200000000800020002000080008000000080400000402000001008000002010004000080080000200100010000100002000400000088000000010001000010000002000152ea8,0x25f800097e00025f8003cc222c204d983d3bb1f001e603cde6f3001e6f3001e9cc007a73001e7056b5,0x200000000800000002000080008000000201000000804000001008000002010008000000020004000040011000100006002000000008000400010001000020000004000277628,0x445800111600025f8000f4e6003d398007a733cc001f532051826079bcc00088b079b15c0007985936,0x80400410001080042020080802080082000211e4,0x8118007b6600081180007a73001e9cc007a731e603cde6000f4e603cfcc03ccf3000408c0003d44536,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0x0,0x0,0x180488284222,0x0],
[0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x440011000404020100804200102002080080ce3,0xacfec00000002b3fb00567f60acfec0159fd82b3fb0000002becaec000000afb2bb0000002b4109fd800000ad0427f60002b4109fd800000ad0427f60000ad0427f600000ad0427fb67f600000000159fd80567f6567f602b3fb00159fd80567f6159fd8000015a131fd80159fdd67f600000000159fd8000000567f602b3fb00159fd8acfec0159fd8000015a131fd80000567f602de24d34ac,0x440011000404020100804200104002100080ce3,0xacfec00000002b3fb00acfec0acfec02b3fb02b3fb0000002becaec000000afb2bb0000002b4109fd800000ad0427f60002b4109fd800000ad0427f60000ad0427f600000ad0427fb67f600000000159fd80567f6567f60567f600159fd80567f6159fd8000015a131fd80159fe2cfec000000002b3fb0000000acfec0567f6002b3fb159fd802b3fb0000015a28bfb00000567f602de24d34ac,0x1ed98007b66000fa98000f4e6003d398007a733cc00f3f32840d66079bcc003db30996eac00079a3f36,0x10400410001080042020080802080082000211e4,0x8400210001080042020040802080042000219e4,0x25f83cc1e600025f80007a73001e9cc007a731e603cde60003ea603cfcc1e60f300012fc0003cc33b6,0x10400410001080042020080802080082000211e4,0x0,0x0,0x0,0x0,0x8000201080042020000802080002000201e4,0x10080402001080042020080802080082000211e4,0x10010400401080042020080802080082000211e4,0x201080042020000802080002000201e4,0x20000801080042020000802080002000201e4,0x10080402001080042020080802080082000211e4,0x10040401001080042020080802080082000211e4,0x0,0x10080402001080042020080802080082000211e4,0x1080042020000802080002000201e4,0x20100804001080042020100802080102004221e4,0x1080042020000802080002000201e4,0x40201008001080042020200802080202008241e4,0x0,0x20400804001080042020100802080102004221e4],
[0x20004800101080042020100802080102004221e4,0x0,0x20008800201080042020100802080102004221e4,0x20080802001080042020100802080102004231e4,0x20010800401080042020100802080102004233e4,0x20100804201080042020100802080102004221e4,0x20020800801080042020100802080102004225e4,0x20100802001080042020100802080102004231e4,0x20040801001080042020100802080102004239e4,0x20400800201080042020100802080102004221e4,0x20080802001080042020100802080102004231e4,0x20000800001080042020100802080102004221e4,0x20100804001080042020100802080102004221e4,0x20100804001080042020100802080102004221e4,0x20200808001080042020100802080102004261e4,0x0,0x0,0x0,0x0,0x0,0xacfec0002b3fdb3fb00015a0033fb00002b3fdb3fb00000ad29ffb00000ad0173fb00000acfec15aaa7ec00001b0a81fb0159fd80acfec0000159fd802b554fd800164cd6c00567f62df3ac59fd80acfec0acfec0567f6000567f6acfec00567f602b3fb00159fdab3fb00567f602b4109fd80000056d5df60000015b577d8000015a53ff60000015b577d8000015a53ff600000159fdee27f17324ab,0x20010800401080042020100802080102004233e4,0x0,0x20020800801080042020100802080102004225e4,0x0,0x7987981e600003cc0003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x7987981e600003cc0003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x1080042020000802080002000201e4,0x100004001080042020000802080002000201e4,0x1080042020000802080002000201e4,0x200008001080042020000802080002000201e4],
[0x0,0x0,0x40005000101080042020200802080202008241e4,0x0,0x40009000201080042020200802080202008241e4,0x40081002001080042020200802080202008251e4,0x40011000401080042020200802080202008253e4,0x40201008201080042020200802080202008241e4,0x40021000801080042020200802080202008245e4,0x40201002001080042020200802080202008241e4,0x40041001001080042020200802080202008259e4,0x0,0x40081002001080042020200802080202008251e4,0x40001000001080042020200802080202008241e4,0x40101004001080042020200802080202008261e4,0x40201008001080042020200802080202008241e4,0x40201008001080042020200802080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_3875 : TreeBound (n := 4) 106 (programCode 0x4c2907543f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x182428204481,0x16c800111600016c80f301e63cc001f530985d4c01e6f301e63cc01e63cc01e6f30079bcc01e703855,0x182428204481,0x0,0xa0000000880000001200000001800008000400020000040080000008200000000800004002000040008000080020000080000800040008000100010000400010001001a955da7,0x1ebbd028000218711a0000fd51da8000218711a00002cb41832d0d8ef4468935280000b2d05e000000000000007823ff280000ee6b283b9b059aca03b9bb86b281dcd73e6b283b9ae7cd6503ba23d60b360b359400001dd4d8594007753616500077359400000ee6d0c852ae49,0x16c800111600016c80f3001e7e600276483ec82c01e67981e63cc01e603cc1e607983cc3cc1e7037c5,0x0,0x0,0x10020001040c80000080200000400800000020100000040200000201000000201000003008010404860600012000100000400010000800040082060100200000100000401027aba8,0xc0003000000580202004100100801040081ca3,0x182428204481,0x0,0x0,0x0,0x0,0x0,0x0,0x40021004000100004004100100002020080ce3,0x0,0x7983cc1e6003d39800000000000001e6000079801e7e60079bcc01e600003cc0000f4e6001e64d995,0x0,0x0,0x0,0x0,0x40021004000100004004100100802020080ce3,0x0,0x40021000000100004004100101002040080ce3,0x40021000000100004004100100002000080ce3,0x0],
[0x12000000018000000120000000180000002010000002010000020100000020100040000003000004000400200010000040010000000210008800100020000100000040002793a8,0x0,0x0,0x0,0x182428204481,0x140005004000900004004100100002020080ce3,0x182428204481,0x140005000100900024004100100102100080de3,0x0,0x0,0x16c800097e00025f80f3001e9cc00102307ba4a601e6f301e63cc01e601e60f30f307983cc1e703345,0x140005000100900024004100100102100080de3,0x16c800097e00025f80f301e63cc0010230981ea601e6f301e63cc01e60f300f3f300798f301e703345,0x0,0x140005000000900204004100101002040081de3,0x182428204481,0x0,0x1ebbd0280007aef40a00004a817c80003f5476a00004a817cbb9aca0003c893536e6b2bb9aca00775361650000f401ab496fdee275280ee6ee1aca00ee6d04d6503b9ca6d6503b9ae7cd6503b9acaee6b2f73597b9acbdd4d8594000ee6b45cd65eee25d94000ee6d481d716f9,0x0,0x220000000880000001200000002800040002001080008000400000010c00000002000008008000020010000020020000080000000101000000400000000810000001000487ba27,0x0,0xc0101000080500014004100100082002080ce3,0x7981e61e6079879800000007980001e6000079801e7e60079bcc01e600003cc0000f30f301e64d995,0x140101000100900024004100100102004080de3,0x40101000000100004004100100002100080ce3,0x0,0x0,0x0,0x40101000000100004004100100002100080ce3,0x0,0x0,0x40101000000100004004100101002040080ce3],
[0x40101000000100004004100100002000080ce3,0x0,0x0,0x40101000000100004004100104002100080ce3,0x2200000008800000012000000028000000201000000804000001008000002010020000001080008004500031011000002002000000108000800410003001020000004000277668,0x0,0x10000080080000400040000200100000900024001400080484000001004000100808000080040000400100000200200000804000000410000002040000008100000010084c5ae27,0x0,0x0,0x0,0x10000800080004000040002000100008100024001400080484000001004000100808000080040000400100000200200000804000000410000002040000008100000010084c5ae27,0x10a232f300003cc79803cc07a73003d398007a7300085155d6c80000079bcc1e6c5700003cc0003cc37a6,0x0,0x10080000080a04000040002000102000100024001400080484000001004000100808000080040000400100000200200000804000000410000002040000008100000010084c5ae27,0x10008000080040000040020000100080100024001400080484000001004000100808000080040000400100000200200000804000000410000002040000008100000010084c5ae27,0x0,0x0,0x0,0x100800000804000000402000001008001000240014000804840000010040001008080000800400004001000002002000008040000004100000020400000081000000100c4c5ae27,0x0,0x10040000080200000040800000101000100024001400080484000001004000100808000080040000400100000200200000804000000410000002040000008100000010184c5ae27,0x10000200080100000040c00000101048100024001400080484000001004000100808000080040000400100000200200000804000000410000002040000008100000010184c5ae27,0x0,0x0,0x0,0x0,0x0,0x4000001000080004000040002020100008100020001000080004000001004000100808000100040000400100000200200000804000000410000002040000008100000010084c5ee27,0x2010080401080042000000002080002000201e4,0x0,0x2020080801080042000000002080002000201e4,0x0],
[0x0,0x0,0x0,0x0,0x2100084001080042002010082080012000613e4,0x2000080001080042000000002080002000201e4,0x2200088001080042002010082080012000613e4,0x0,0x20000020020000080200000800200000c00020000800040004000001008000c040200000200200000802000008002000008040000010100000010400000101000000102108713a7,0x0,0x0,0x0,0x0,0xf35b2f300003cc01e63cc07a73003d398007a7300085155c0000000079bcc1e6c5700003cc0003cc37a6,0x0,0x0,0x0,0x0,0x0,0x0,0x20020000020080000200800000200800400020000800040004000001008000c040200000200200000802000008002000008040000010100000010400000101000000102508713a7,0x0,0x20100000020100000201000000201000400020000800040004000001008000c040200000200200000802000008002000008040000010100000010400000101000000102108713a7,0x20100000020004000201000000204040400020000800040004000001008000c040200000200200000802000008002000008040000010100000010400000101000000102108713a7,0x7985b21e607987983cc1e616c80001e61e6079801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x0,0x40000020100000081000000801000000c00020000800040004000002008000c080200000200200000802000008002000008040000010100000010400000101000000102108713a7,0x0,0x0,0x0,0x0,0x10a232f300003ccf3003cc07a73003d398007a7300085155d6c80000079bcc1e6c5700003cc0003cc37a6],
[0x0,0x0,0x0,0x0,0x0,0x0,0x40020000100080001000800001000800400020000800040004000002008000c080200000200200000802000008002000008040000010100000010400000101000000102508713a7,0x0,0x40100000100100001001000001001000400020000800040004000002008000c080200000200200000802000008002000008040000010100000010400000101000000102108713a7,0x40100000100008001001000001004080400020000800040004000002008000c080200000200200000802000008002000008040000010100000010400000101000000102108713a7,0x0,0x0,0x0,0x0,0x7983cc1e6000079800000000000001e6000079801e7e60079bcc01e600003cc0000f4e6001e64d995,0x0,0x400020000000080004000200000000800060002000180000000000000000400000002000010008000020010000080020000080400000101000000404000000800000001001087faa7,0x0,0x400020000000080004000200000000800060002000180000000000000000400000002000010008000020010000080020000080600000101800000404000000804000001001087faa7,0x0,0x400020000000080004000200000000800060002000180000000000000000400000002000010008000020010000080020000080400000100000000404000000800000001001087faa7,0x7983cc1e6000079800000000000001e6000079801e7e60079bcc01e63cc03ccf300f31e601e64d995,0x7983cc1e6000079800000000000001e6000079801e7e60079bcc01e600003cc0000f300001e64d995,0x7983cc1e6000079800000000000001e6000079801e7e60079bcc01e679803cde600f379801e64d995,0x0,0x0,0x0,0x0,0x1040041000088500014004100100082002080ce3,0xf379803cde60079f9800001e67980799e6000079801e7e60079bcc01e600003cc0000f30f301e64d995,0x1040041000108900024004100100102004080de3,0x1040041001008100204004100101002100081ce3],
[0x0,0x0,0x0,0x1040041001008100204004100101002100081ce3,0x0,0x1dce536b2801dd11eaca0001ebbd028077394daca0002da282a800077447ab2801dd11eaca000ee88f56500ee88f565000ee88f565003ba9b0b2800ee6b31502f903b9aca9506b2acbdcd65059682f773597b9aca77359401dcf4211ead175362536b2801dcd68bd672c45d2c7fa,0x1040041000008100004004100101002040080ce3,0x1040041000008100004004100101002000080ce3,0x1040041001008100204004100102002080081ce3,0x0,0x1040041001008100204004100104002100081ce3,0x0,0x0,0x182428204481,0x82008210481,0x182428204481,0x82008220481,0x82008208481,0x400020000000080000000200000000800060002000180000000000000000400000002000010008000020010000080020000080400000101000000404000000800000001001087faa7,0x82008208481,0x82008220481,0x82008210481,0x400020000000080000000200000000800060002000180000000000000000400000002000010008000020010000080020000080400000100000000404000000800000001001087faa7,0x82008210481,0x82008200481,0x82008220481,0x0,0x82008220481,0x0,0x0,0x1e600088b0003ea6000b64222d6c80f31e6222c79801e7e600f33cc01e9cc003db3000f6cc001e8705c5,0xee6b2803b9e83aca077360b35a2e6b283b9b059aca0ee6b2a1872086b639aca3b9ad8e6b2f73597b9acbdcd653b9acaee6b45cd651dcd653b9ad173594ee6b639aca1dcd73e6b280ee6d04d6503ba23d594000f047fe50003c11ff94001deb326500077acc994000ef5a11f9e9a49],
[0x0,0x0,0x0,0x0,0x1e600f3f3003cde6007d4c222d6c80f31e6222c79801e7e600f33cc01e9cc003db3000f6cc001e8705c5,0x20000801080042000000002080002000201e4,0x0,0x0,0x1e60798f301e61e603cfcc222d6c80f31e6222c79801e7e600f33cc01e9cc003db3000f6cc001e8705c5,0x0,0x1080042000000002080002000201e4,0x20100804001080042020100802080102004221e4,0x1080042000000002080002000201e4,0x40201008001080042040201002080202008241e4,0x0,0x800010000000040040000020020000090002000100008000400000000400000000800010004000040010000020020000080400000041000000204000000810000001000485ee27,0x4000000210000000900000008100000008002010000002010000020100000020100040002001000004000400200010000040040000200100008000400020001000008040402713a8,0x0,0x0,0x722000100000000400000000200100000870003910100008000400000000400000002000010004000040010000020020000080400000101000000204000000810000001000487ee27,0x20010800401080042020100002080102004233e4,0x4000200010008800100022000100008040002010000002010000020100000020100040002001100004000400220011000040040000200100008800400022001000008040402713a8,0x20020800801080042020100802080102004225e4,0x400001000000004000000002000000008070002000100008000400000000400000002000010004000040010000020020000080400000101000000204000000810000001000487ee27,0x40000200200001000800004001000008000008040000080400000100800000201000800040002000880004012740c000202004000040010000880040002600d000010040b8253668,0x4002000010000004100020000100000040002010000002010000020100000020100040002001000004000400200010000040040000200100008000400020001000008040402713a8,0x400020000000080000000000000000000070002000100008000400000000400000002000010004000040010000020020000080400000101000000204000000810000001000487ee27,0x20000800001080042020100002080102004221e4,0x20100804001080042020100802080102004221e4,0x20100804001080042020100802080102004221e4,0x20200808001080042020100802080102004261e4,0x0],
[0x79800097e000408c000b642d916c83cc1e62d9079801e7e600f33cc01e9cc003db3000f6cc001ee225c5,0x0,0x0,0x0,0x0,0x10000401080042000000002080002000201e4,0x0,0x20000801080042000000002080002000201e4,0x0,0x0,0x0,0x0,0x1080042000000002080002000201e4,0x100004001080042000000002080002000201e4,0x1080042000000002080002000201e4,0x200008001080042000000002080002000201e4,0x0,0x0,0x200000002800000011000000042000000080020100000080400000100800000201002000100008000c000500031011000006004000100010000c00040003001100004004200273668,0x0,0x200000010800000041000000082000000100020100000080400000100800000201002000100008000c000500031011000006004000100010000c00040003001100004004200273668,0x3ea6001e9cc00408c1e616c80001e61e6079801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x40011000401080042040200002080202008253e4,0xf4e6003d398007d4c1e616c80001e61e6079801e7e600f33cc01e9cc003db3000f6cc001e68a5c5,0x40021000801080042040201002080202008245e4,0x100001000000004000000002004000008010002000100008000400000000400000000800010004000040010000020020000080400000041000000204000000810000001000485ee27,0x80000200800001001000004002000008000008040000080400000100800000201000800040008000c00010013d40c000202004000040010000c00040003c00d000020041b8253668,0x0,0x400020000000080000000000000000000070002000100008000400000000400000002000010004000040010000020020000080400000101000000204000000810000001000487ee27,0x40001000001080042040200002080202008241e4,0x40101004001080042040201002080202008261e4,0x40201008001080042040201002080202008241e4],
[0x40201008001080042040201002080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4132 : TreeBound (n := 4) 106 (programCode 0x4c29075440) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0x0,0x10400410001080042040081002002080080211e4,0x180488284222,0x400010001080042040001002004000100201e4,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x0,0x0,0x0,0x0,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0xc00030001080042040005002080004442211e4,0xc00030001080042040005002002004080613e4,0x180488284222,0xc00030001080042040005002004004100a05e4,0x180488294a62,0x180488290a62,0x180488284222,0x180488290a62,0x0],
[0x0,0x0,0x0,0x0,0x180488284222,0x180488284222,0x80488280222,0x180488284222,0x0,0x0,0x180488284222,0x0,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x0,0x200000000800020002000080008000000080400000402000001008000002010008000080040000200100010000200002000400000088000000010001000010000002000152ea8,0x0,0x401010001080042040001002040001000201e4,0x445800111600025f8000f4e6003d398007a73798002046204dd4c079bcc00088b079a22c0007985936,0x0,0x0,0x0,0x0,0x3cc2269b307a73000f30f4e6003d398007a73798002046204dd4c079bcc00088b0813a2c0007985936,0x402001080042040001002080002000201e4,0x2010400401080042040011002080012008253e4,0x400201080042040001002080002000201e4,0x4020500801080042040021002080022008245e4,0x402001080042040001002080002000201e4,0x8040401001080042040041002080042000219e4],
[0x0,0x10080402001080042040081002080082000211e4,0x10080402001080042040081002080082000211e4,0x20100c04001080042040101002080102006231e4,0x0,0x40201408001080042040201002080202008241e4,0x8118007b6600081180007a73001e9cc007a733cc03ccf3003cfcc03cfcc0798f3000f6cc0003d5b1b6,0x400050001080042040001002080002000201e4,0x1ed98007b66000fa98000f4e6003d398007a7379800f4e62fba94c079bcc003db30b7552c00079a3f36,0x400410001080042040001002080002000201e4,0x8400210001080042040041002080042000219e4,0x0,0x180488284222,0x180488284222,0x180488280222,0x180488284222,0x0,0x25f8007b6600025f80007a73001e9cc007a733cc03ccf3003cfcc03cc01ed9801e60f301e603d5b1b6,0x180488284222,0x1ed98008a960004458000f4e6003d398007a7379800f4e6115a94c079807983cc1e9dd163cc079a3f36,0x580488294a62,0x580488290a62,0x180488284222,0x580488290a62,0x1040041001008040201004200102002080081ce3,0x0,0x1040041001008040201004200104002100081ce3,0x0,0x10400410001080042040081002080082000211e4,0x0,0xf362bad901e60000000000f4e6001e9cc007a7379885128300003cc03cfcc1e6c5700003cc0003cc3c26,0x4040101080042040001002080002000201e4],
[0x0,0x8000201080042040001002080002000201e4,0x10000402001080042040081002080082000211e4,0x10010400401080042040081002080082000211e4,0x201080042040001002080002000201e4,0x20000801080042040001002080002000201e4,0x10080402001080042040081002080082000211e4,0x10040401001080042040081002080082000211e4,0xf362bad901e60000000f30f4e6001e9cc007a7379885128300003cc03cfcc1e6c5700003cc0003cc3c26,0x10080402001080042040081002080082000211e4,0x1080042040001002080002000201e4,0x20100804001080042040101002080102004221e4,0x1080042040001002080002000201e4,0x40201008001080042040201002080202008241e4,0x0,0x20400804001080042040101002080102004221e4,0x20004800101080042040101002080102004221e4,0x0,0x20008800201080042040101002080102004221e4,0x20000802001080042040101002080102004231e4,0x20010800401080042040101002080102004233e4,0x20100804201080042040101002080102004221e4,0x20020800801080042040101002080102004225e4,0x20100802001080042040101002080102004231e4,0x20040801001080042040101002080102004239e4,0x20400800201080042040101002080102004221e4,0x20080802001080042040101002080102004231e4,0x20000800001080042040101002080102004221e4,0x20100804001080042040101002080102004221e4,0x20100804001080042040101002080102004221e4,0x20200808001080042040101002080102004261e4,0x0],
[0xf3079ad901e60000000000f4e6001e9cc007a7379885128300003cc03cfcc1e6c5700003cc0003cc3c26,0x0,0x0,0x0,0x0,0x11000401080042040001002080002000201e4,0x0,0x21000801080042040001002080002000201e4,0x0,0x0,0x0,0x0,0x1080042040001002080002000201e4,0x100004001080042040001002080002000201e4,0x1080042040001002080002000201e4,0x200008001080042040001002080002000201e4,0x0,0x0,0x40005000101080042040201002080202008241e4,0x0,0x40009000201080042040201002080202008241e4,0x40001002001080042040201002080202008241e4,0x40011000401080042040201002080202008253e4,0x40201008201080042040201002080202008241e4,0x40021000801080042040201002080202008245e4,0x40201002001080042040201002080202008241e4,0x40041001001080042040201002080202008259e4,0x0,0x40081002001080042040201002080202008251e4,0x40001000001080042040201002080202008241e4,0x40101004001080042040201002080202008261e4,0x40201008001080042040201002080202008241e4],
[0x40201008001080042040201002080202008241e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_2964 : TreeBound (n := 4) 106 (programCode 0x4c290754) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part012_2965 part012_3046 part012_3127 part012_3208 part012_3289 part012_3290 part012_3291 part012_3372 part012_3373 part012_3454 part012_3455 part012_3536 part012_3537 part012_3762 part012_3875 part012_4132

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4294 : TreeBound (n := 4) 106 (programCode 0x4c29075531) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x10808e121c481,0x1080821204481,0x1080821204481,0x1080861208481,0x108086120c481,0x1080861208481,0x1080861208481,0x10808e1210481,0x10808e121c481,0x10808e1210481,0x1080821204481,0x0,0xf30000b6400088b0000799e9cc01e60079a082de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0xf30079bcc01e6f30079801e9cc01e60079a0460000f4e600f4e6000f4e679801ed980079f9801e8e9855,0xf30000b640004bf0000f31e9cc01e60079a082de60f4e600f4e6000f4e679800fa980079f9801e8eb1a5,0xf3000222c1e60f30001e61e9cc01e60079a0460000f4e600f4e6000f4e679801ed980079f9801e8ed515,0x4000001010000004040000008100000008002030010008008000010000020010000000020100000080400000100800000100802000001008000004010000010010000010054c7ffa7,0x400030111000008004000000410000000000203001000800800001000002001000000002010000008040000010080000010080200000100800000401000001001000001005087ffa7,0xf3000408c0010230007981e9cc01e60079a082de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0x4000101010000004040000200100000008002030010008008000010000020010000000020100000080400000100800000100802000001008000004010000010010000010054c7ffa7,0x400001001000004004000008010000008000203001000800800001000002001000000002010000008040000010080000010080200000100800000401000001001000001005487ffa7,0x400021101000000104000002010000000000203001000800800001000002001000000002010000008040000010080000010080200000100800000401000001001000001005087ffa7,0xf3001e9cc007a73003cc01e9cc01e60079a082de60f4e600f4e6000f4e679800fa98003d39801e962ab5,0x400030011000008004000000030000000000203001000800800001000002001000000002010000008040000010080000010080200000100800000401000001001000001005087ffa7,0xf300f33cc0f30f300f3001e9cc01e60079a082de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0x400020001000080004000200010000000000203001000800800001000002001000000002010000008040000010080000010080200000100800000401000001001000001005087ffa7,0xf300f33cc03ccf301e6001e9cc01e60079a082de60f4e600f4e6000f4e679800fa98003d39801ecb52b5,0x400020001000080004000200010000000000203001000800800001000002001000000002010000008040000010080000010080200000100800000401000001001000001005087ffa7,0x0,0x1021084220862],
[0x100b0852a18e2,0x8000a00020200408090084002108002010080ce3,0x100b0852a18e2,0x1021084220862,0x1011086220c82,0x1021084220862,0x1011086220c82,0x1021084220862,0x1021084220862,0x1021084220862,0x1021084220862,0xf300f33cc0f30f300f3001e9cc01e60079a0460000f4e600f4e6000f4e679801f5300079f9801e8e9855,0xf307983cc1e60f30000007b66b64f300799e600003d398007a73000f4e9cc003db3000f300001e68a925,0xf301e63cc0798f301e6001ed9801e60079a0460000f4e600f4e6000f4e6f3001f530007a73001eacf855,0xf307983cc1e60f30000007b66b64f300799e600003d398007a73000f4e9cc003db3000f300001e68a925,0x0,0xf30000b6400088b0000799ed9801e60079a0bf9e60f4e600f4e6000f4e6f3001e7e6003db3001ead3485,0xf3001e9cc0000f30097e01ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001eacf2b5,0xf30000b640002d90000f31ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001eacf2b5,0x0,0x0,0xf301e63cc001f530989dd9ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001eacf2b5,0xf3000408c001f530007981ed9801e60079a0bf9e60f4e600f4e6000f4e679800f6cc007a73001eacf345,0xf3000408c0798f302dccc1ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001eacf2b5,0xf3001e9cc01e6f3001e601ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001eacf2b5,0x400021301000000104000002010000000000203001000801000001000002001000000002010000008040000010080000010080200000100800000402000001002000001009487ffa7,0xf3001e9cc00f3f3003cc01ed9801e60079a0bf9e60f4e600f4e6000f4e679800f6cc007a73001eb48b45,0xf301e63cc0002d9097e799ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001eacf2b5,0xf300f33cc0f30f300f3001ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001f44d2b5,0x0,0xf300f33cc03ccf301e6001ed9801e60079a0bf9e60f4e600f4e6000f4e679800f4e6003db3001ecb52b5,0x0],
[0x0,0x1021084220862,0x100b0852a18e2,0x0,0x100b0852a18e2,0x1021084220862,0x1011086220c82,0x1021084220862,0x1011086220c82,0x1021084220862,0x1021084220862,0x1021084220862,0x1021084220862,0x0,0xf307983cc1e60f30000007b66b64f300799e600003d398007a73000f4e9cc003db3000f300001e68a925,0x0,0xf307983cc1e60f30000007b66b64f300799e600003d398007a73000f4e9cc003db3000f300001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4375 : TreeBound (n := 4) 106 (programCode 0x4c29075532) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040201000204008148004020108002200080ee3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4376 : TreeBound (n := 4) 106 (programCode 0x4c29075533) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x10808e121c481,0x1080821204481,0x1080821204481,0x1080861208481,0x108086120c481,0x1080861208481,0x1080861208481,0x10808e1210481,0x10808e121c481,0x10808e1210481,0x1080821204481,0x0,0xf30000b6400088b0000799f53001e600f321761b20f4e6003ea6001e7e679800fa98003d39801ee9b2b5,0xf30079bcc01e6f30079801f53001e600f320460001e7e6007b66001e7e679801ed980079f9801ee9b855,0xf30000b640002d90000f31f53001e600f321761b20f4e6003ea6001e7e679800fa98003d39801ee9b2b5,0xf300012fc1e60f30000f31f53001e600f320460001e7e6007b66001e7e679801ed980079f9801ee9d6b5,0x0,0xf303cc3cc0010230c60049f53001e600f321761b20f4e6003ea6001e7e679800fa98003d39801ee9b2b5,0xf30007d4c0010230007981f53001e600f321393cc1e7e6003ea6001e7e679801ed98003d39801ee9b7c5,0x0,0x0,0xf30007d4c007a73079f981f53001e600f320460001e7e6007b66001e7e679801ed980079f9801ee9b855,0xf3003cfcc00f3f3003cc01f53001e600f320460001e7e6007b66001e7e679801ed980079f9801ef16eb5,0xf303cc3cc0004bf0c586c9f53001e600f321761b20f4e6003ea6001e7e679800fa98003d39801ee9b2b5,0xf300f33cc0f30f300f3001f53001e600f321761b20f4e6003ea6001e7e679800fa98003d39801f0812b5,0x0,0xf300f33cc03ccf301e6001f53001e600f321761b20f4e6003ea6001e7e679800fa98003d39801f44d2b5,0x0,0x0,0xc00030002008080a0104004100402200080de3],
[0x804002d000200808160084004100b01200080fa3,0x481084220862,0x4002a00000002800040002000000018000002020176008000100010000040010805d8002010000008040000004080000020080402400101000000400008000210000001001087fca7,0x481084220862,0x281086220c82,0x481084220862,0x281086220c82,0x481084220862,0x481084220862,0x481084220862,0x481084220862,0x0,0x0,0x0,0x0,0x0,0xf30000b6400088b0000799e9cc01e600f320fc9b20f4e6003ea6001e7e679800f4e6003db3001e8e92b5,0xf3001e9cc0000f30079801e9cc01e600f32082fcc1e7e6003ea6001e7e6f3001e7e6003db3001e8e97c5,0xf30000b640004bf0000f31ed9801e6016ca0bfbcc0f4e6007b66001e7e679800f6cc007a73001ead11a5,0x0,0x0,0xf301e63cc001f5309868b1ed9801e6016ca0bfbcc0f4e6007b66001e7e679800f6cc007a73001eacf345,0xf3000408c0010230007981e9cc01e600f320fc9b20f4e6003ea6001e7e679800f4e6003db3001e8e92b5,0xf3000408c0798f301e9cc1ed9801e6016ca0bfbcc0f4e6007b66001e7e679800f6cc007a73001eacf345,0xf3001e9cc01e6f3001e601ed9801e6016ca0bfbcc0f4e6007b66001e7e679800f6cc007a73001eacf345,0x0,0xf3001e9cc00f3f3003cc01ed9801e6016ca0bfbcc0f4e6007b66001e7e679800f6cc007a73001eb4a9a5,0xf301e63cc0006a5097ef31ed9801e6016ca0bfbcc0f4e6007b66001e7e679800f6cc007a73001ead11a5,0xf300f33cc0f30f300f3001e9cc01e600f320fc9b20f4e6003ea6001e7e679800f4e6003db3001e8e92b5,0x0,0xf300f33cc03ccf301e6001e9cc01e600f320fc9b20f4e6003ea6001e7e679800f4e6003db3001ecb52b5,0x0],
[0x0,0x0,0x8040021000200808060084004100201200080fa3,0x481084220862,0x0,0x481084220862,0x281086220c82,0x481084220862,0x281086220c82,0x481084220862,0x481084220862,0x481084220862,0x481084220862,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4457 : TreeBound (n := 4) 106 (programCode 0x4c29075534) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x1080842218481,0x1080821204481,0x1080800200481,0x1080800208481,0x1080800200481,0x1080800208481,0x1080800208481,0x1080842210481,0x1080842210481,0x1080842210481,0x1080800200481,0x0,0x0,0x8040021000204008140804020102002080080ee3,0x0,0x80800220481,0x280842220481,0x80800220481,0x280842220481,0x280842220481,0x4808c4220481,0x6808c6220481,0x4808c4220481,0x80800220481,0x0,0x0,0x0,0x0,0x0,0x10230812218e2],
[0x100b0812a18e2,0x0,0x100b0812a18e2,0x80102002020080402001080042020100804030e4,0x80012000420080402001090042020100804233e4,0x0,0x800220008200805020010a0042020100804235e4,0x10230812218e2,0x10230812218e2,0xf307983cc0798f30a710f301e74e207983cc0f3004731000f4e6001ed98f307981e688b07987983cdc46,0x10230812218e2,0x0,0xf301e63cc03ccf300f30f301e711607983cc0f300454b000f4e6001ed98f307981e688b07987985b3c46,0x0,0xf303cc3cc0f30f301e60f301e78ae07983cc0f3004a0a000f4e6001ed98f307981e688b0798798b65c46,0x0,0x0,0x0,0x0,0x80800220481,0x280842220481,0x80800220481,0x280842220481,0x280842220481,0x4808c4220481,0x6808c6220481,0x4808c4220481,0x80800220481,0x0,0x0,0x0,0x0],
[0x0,0x10230812218e2,0x100b0812a18e2,0x0,0x100b0812a18e2,0xf303cc3cc2d90f300799e601e76c807983cc0f3004824000f4e6001ed99e60f30798b640f30f30799c46,0x80012000440080402001090042040201008253e4,0xf303cc3cc2d90f303cc1e601e76c807983cc0f3004824000f4e6001ed99e60f30798b640f30f30799c46,0x800220008400805020010a0042040201008255e4,0x10230812218e2,0x10230812218e2,0x0,0x10230812218e2,0x0,0xf301e63cc03ccf300f31e601e78ae07983cc0f3004731000f4e6001ed99e60f30798b640f30f30d4bc46,0x0,0xf303cc3cc0f30f301e61e601e76c807983cc0f3004824000f4e6001ed99e60f30798b640f30f30799c46]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4538 : TreeBound (n := 4) 106 (programCode 0x4c29075535) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4539 : TreeBound (n := 4) 106 (programCode 0x4c29075536) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4540 : TreeBound (n := 4) 106 (programCode 0x4c29075537) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4541 : TreeBound (n := 4) 106 (programCode 0x4c29075538) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4542 : TreeBound (n := 4) 106 (programCode 0x4c29075539) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10808c4240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4543 : TreeBound (n := 4) 106 (programCode 0x4c2907553a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10808c6240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4544 : TreeBound (n := 4) 106 (programCode 0x4c2907553b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10808c4240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4545 : TreeBound (n := 4) 106 (programCode 0x4c2907553c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4546 : TreeBound (n := 4) 106 (programCode 0x4c2907553d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c8001e601e7e6f3002082e04601e7e601e61e601e9cc001023000408c001e7032b5,0xf37983cc1e600f3798001e7e601e6f3001ebc14e601e7e601e61e601e9cc001f530007d4c001e703855,0x16c800097e00025f8001e603cde6f3002082fea601e7e601e61e601e9cc0010230007d4c001e7051a5,0x0,0x8000480010210008402004080108002200082ce3,0x109084240862,0x8000880020210008402004080108002200082de3,0x109084240862,0x121084240862,0x111084240862,0x121084240862,0x111084240862,0x121084240862,0x121084240862,0x121084240862,0x121084240862,0x121084240862,0x600020000800000004000000004000000000203000000802000001002000001000002000010008000040010000080010000080400000101000000404000001010000001011087ffa7,0x8020080800210008402004080108002200086ce3,0x0,0x202000000208000001020000001080000020141800020001800100a0000010000020000100020000100100000800100000804000001010000001040000010100000010014c7d7a7,0x8040001000210008002004080108002200080ce3,0x8118002046000fa98001e61e61e6f3001f929ae601e7e601e61e601e9cc001023000408c001e7032b5,0x2820000002080000014200000010800000201e1e00020001800100a0000010000020000100020000100100000800100000804000001010000001040000010100000010014c7d7a7,0x20020000080080000100200000100800000201332000800080001002000001000002000010008000040010000080010000080400000101000000404000001010000001001487ffa7,0xf3079800f4e60000798001e60001e6f3001e6001e601e7e601e61e601e9cc001f530007d4c001e703855,0x0,0x4089c8240501,0x409084240862,0x4089c8240501,0x409084240862],
[0x4109c8240501,0x4709c8240501,0x4109c8240501,0x4309c8240501,0x4209c8240501,0x4709c8240501,0x4209c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x2040001000210008002004080108002200080ce3,0x0,0x808908240501,0x409084240862,0x808908240501,0x409084240862,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x880490010210008482004080108001200082ca3],
[0x20004800100080402000880002080402000000e4,0x9004980202100084c2004080108001200082fa3,0xf303cc5b21e607983cc001f53001e6f300204601e601e7e601e61e601e9cc001f530007d4c001ee9b855,0xe109c8240501,0x840908240501,0xe109c8240501,0xe709c8240501,0xe209c8240501,0xe709c8240501,0xe209c8240501,0x840908240501,0x840908240501,0x908240501,0x840908240501,0x908240501,0x0,0x808908240501,0x0,0x808908240501,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501],
[0x0,0x0,0x40005000100080402000880002080402000000e4,0x0,0x0,0x810908240501,0x40908240501,0x810908240501,0x850908240501,0xa20948240501,0xa20948240501,0xa20948240501,0x40908240501,0x40908240501,0x908240501,0x40908240501,0x908240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4659 : TreeBound (n := 4) 106 (programCode 0x4c2907553e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108842240481,0xc00020000080402020080802080006000000e4,0x108842240481,0x422000011088000024000000080000000080202110000400000001000040001000004220010000080020000000080000200080400000101000000404000001010000001001087fba7,0x2088c6240481,0x6088c6240481,0x2088c6240481,0x6088c6240481,0x408842240481,0x408842240481,0x408842240481,0x6088c6240481,0x1e600097e0007b66000799e601e7e607982046000f31e6003ea600f31e9cc001f530007d4c001e703855,0x6088c6240481,0x3cc00088b0007d4c000799e60799e607982046000f31e600f4e600f31e9cc001f530007d4c001e707515,0x0,0xf30811bcc2046f3003cc07b66000f300001e600f30079bcc00f300001e9cc003db3000f6cc001e68a925,0x0,0x108842240481,0x0,0x108842240481,0x0,0x2088c6240481,0x6088c6240481,0x2088c6240481,0x6088c6240481,0x408842240481,0x408842240481,0x408842240481,0x6088c6240481],
[0x1e60011160003ea6000f31e603cde607982046000f31e6007b6600f31e9cc001f530007d4c001e7056b5,0x6088c6240481,0x3cc001023000408c000f31e603cde607982046000f31e6007b6600f31e9cc001f530007d4c001e7056b5,0x0,0x0,0x80008000201080402020080802080002000201e4,0xf30f30f303cc0f30f4eda73001e9cc1e60f31e603cde600f504603cfcc1e64bf0000b640003cc33b6,0x0,0x1e60f30f307981e60f30f3f40a239981e60f33cc85128302e0b66079bcc00088b085155c0007985426,0x1008400201080402020080802080082000211e4,0x20040802010406c20200d080348001200763ba4,0x2021100008084400020200000020020000202110000400000001000000001000004220010010880020001000080000000080400000101000000404000001010000001001087fba7,0x20041002010407420200e0803880022007a3da4,0x180046002010406420200c08030800c2003219a4,0x80042002010406420200c0803080042003219a4,0xf33cc1e60f3089a8b20f30f4e7028b9983cc0f33cc81468301e61e6079bcc00088b081495c0007985936,0x80044002010406420200c0803080082003219a4,0x8000201080402020080802080002000201e4,0x200048002010406420201c0807080102007239a4,0x0,0x40009000201080442020280802080202008241e4,0x8001200040204008148004020108002200080ee3,0x80012000402080402020080802080402000412e4,0x8002200080204008148004020108002200080ee3,0x80022000804080402020080802080402000814e4,0x8004200100200008008004000108002200080ce3,0x8004200000200008008004000108002200080ce3,0x8008200200200008008004000108002200080ce3,0x8000200000200008008004000108002200080ce3,0x0,0x10230010230001023001e62047e6fa982084c64601e603cde61f531e9cc001f53000408c001e7037c5,0x801002040021000854aa04080108002200082ee3],
[0x102300088b0001f53001e6222de6fa982084e4a601e603cde61f531e9cc0010230007d4c001e7051a5,0x1e60f307983cc1e60f4eda73001e9cc1e60f31e603cde600f6ea603cfcc1e64bf00012fc0003cc33b6,0x2409cc240501,0x840908240501,0x2409cc240501,0x2409cc240501,0x4409ce240501,0xe409ce240501,0x4409ce240501,0x840908240501,0x840908240501,0x840908240501,0x840908240501,0x40908240501,0x8020200407008040204038080208078200e07104,0x0,0x1116000f6cc001116001e62047e6fa9820c1e34c01e603cde61f531e9cc001f53000408c001e7037c5,0x0,0x10230008118002046001e6222de7ed9820c1a68c01e603cde63db31e9cc0010230007d4c001e7051a5,0x0,0x2409cc240501,0x840908240501,0x2409cc240501,0x2409cc240501,0x4409ce240501,0xe409ce240501,0x4409ce240501,0x840908240501,0x840908240501,0x840908240501,0x840908240501,0x40908240501],
[0x8020200805008040204028080208068200a05104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4756 : TreeBound (n := 4) 106 (programCode 0x4c2907553f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c8001e60799e7e60020bffd4c01e67981e63cc01e9cc001f53000408c001e707485,0x0,0x3d398003ea60147018001e61e61e7e6001f3f12e601e67981e63cc01e6003ccf303cc3cc03cde7032b5,0x40021000220008004004100100002020080ce3,0xf3798003ea600f3798001e61e61e7e6001edb69cc01e6f301e63cc01e600799e601e67980799e703855,0x0,0x20020000080080000040200000400800000201532000800080001004000001000002000010008000040020000080020000080002000100008000400010001000010001001487ffa7,0xf307980001e6003d398001ed98007b66001e60079801e7e60079bcc01e9cc003db3000f300001e64d995,0x3d39803cde60130398001e7e601e7e6001f3d2ce601e67981e63cc01e601e60f307983cc3cc1e7032b5,0x6a64200000800800000402000004008000002035320008000800010040000010000020000100080000400200000800200000806a6400100008000400040001000010001001487ffa7,0x40021000220008004004100100802020080ce3,0x6a2020000080080000000200000c008000002035100001000000010040000010000020000100080000080200000800200000806a6000101000000400040001000000001001087f3a7,0x0,0xf307980001e6003d398001ed98007b66001e60079801e7e60079bcc01e6f3003cfcc00f300001e64d995,0x0,0x0,0x0,0x0,0x16c80005b200025f8001e601e7e7e60020fc9d0601e67981e63cc01e9cc001023000408c001e7032b5,0x0,0xc0101000220008014004100100082002080ce3,0x280020000a000800000202000080008000001004000008000400010040000010000008000080020000400200000800200000800100000400400001000200010004000010012859fa7,0x140101000220008024004100100102004080de3,0x40101000220008004004100100002100080ce3,0x0,0xf307980001e60798798001ed98007b66001e60079801e7e60079bcc01e9cc003db3000f300001e64d995,0x0,0x0,0x2020200008000800000042000080008000002014120008000080010040000010000020000100080000400200000800200000800200001000800004001000010001000010014c7ffa7,0x602420000800080000000200008000800000203412000100000001004000001000002000010008000008020000080020000080424000101000000400040001000000001001087f3a7,0x0],
[0x40101000220008004004100104002000080ce3,0x0,0x0,0x40101000220008004004100104002100080ce3,0x0,0x0,0x208948240501,0x0,0x208948240501,0x0,0x210948240501,0x250948240501,0x210948240501,0x210948240501,0x220948240501,0x220948240501,0x220948240501,0x250948240501,0x240948240501,0x270948240501,0x240948240501,0x250948240501,0x0,0x3cc0798f308c80bf0799e60799e7e60020bffd4c01e67981e63cc01e9cc001f53000408c001e707485,0x0,0xf307983cc3344d90f31e601e7e7e60020fc9d0601e67981e63cc01e9cc001023000408c001e7032b5,0x0,0xa10948240501,0x840908240501,0xa10948240501,0xa50948240501,0xe209c8240501],
[0xe709c8240501,0xe209c8240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x8118003ea6000fa98001e61e61e8d9001edb67e601e6f301e63cc01e9cc0010230007d4c001e703345,0x40009000220008004004100108002200080ce3,0x3d39803cde6003d398001e7e601e7e6001f3d2ce601e67981e63cc01e9cc001023000408c001e7032b5,0x6a6420001000080000040200000000800000203532000800080001004000001000002000010008000040020000080020000080400000101000000404000001010000001001487ffa7,0x0,0x4089c8240501,0x0,0x4089c8240501,0x0,0x4109c8240501,0x4709c8240501,0x4109c8240501,0x4309c8240501,0x4209c8240501,0x4709c8240501,0x4209c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x0,0x808908240501,0x0,0x808908240501],
[0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x808908240501,0x2040080100220008404004100108002200082ce3,0x808908240501,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x4207b07a73001e6f300799ed98007b66001ee2129801e7e60079bcc01e9cc003db3000f6cc001ea21315],
[0x622021001888004000000200000000020000203110000400000001004000001000002000010008000020020000080020000080400000101000000404000001010000001001087fba7,0x432841e6f300799e600f31ed98007b66001ee2129801e7e60079bcc01e9cc003db3000f6cc001ea435d5,0x0,0xe109c8240501,0x840908240501,0xe109c8240501,0xe709c8240501,0xe209c8240501,0xe709c8240501,0xe209c8240501,0x840908240501,0x840908240501,0x908240501,0x840908240501,0x908240501,0x0,0x808908240501,0x0,0x808908240501,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501],
[0x0,0x0,0x0,0x0,0x200000010400000021000000082000000173030100000040200400000800040001006000398184000a00010000080100000200400039819000020004000200010000000210017ee28,0x810908240501,0x40908240501,0x810908240501,0x850908240501,0xa20948240501,0xa20948240501,0xa20948240501,0x40908240501,0x40908240501,0x908240501,0x40908240501,0x908240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4933 : TreeBound (n := 4) 106 (programCode 0x4c29075540) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x8000600010200408018004002100082002080ce3,0x8000600010204008148004020100a02020080ee3,0x8000600010200808028004004100102004080de3,0x0,0x8000600010201008048004008100202008080ee3,0x8000600010200008008004000108002000080ce3,0x0,0x8000600010201008048004008108202008080ee3,0x8000600010204008148004020100802020080ee3,0x8000600010200008008004000100802000080ce3,0x8000600010208008248004040101002040081ee3,0x8000600010200008008004000100002000080ce3,0x0,0x0,0x0,0x8000600010200008008004000108002000080ce3,0x0,0x0,0x8005200100201008048004008100a02020080ee3,0x0,0x0,0x8004200100201008048004008100202008080ee3,0x159fd80aeb5ff29ff6000567f759fd80ae5f7fc9ff6000159fed9fd80000000567f60000acfec00ad0990581f382b42641607ce02b3fb0000000159fd80567f60159fd82b3fb00159fd80015a0b03e859fd8000acff167f75a0b03e7567f600000002b3fc59fd80002b3fb00159fd82b410d6bfda705684c82c0f9c15a131fd80000567f600acfec159fdab3fb000159fd80000000159fe86e1cdb720ab,0x8004200100201008048004008100402010080ee3,0x6,0x8001200100201008048004008100802020080ee3,0x8001200100201008048004008100802020080ee3,0x8001200100201008048004008101002040080ee3,0x8004200100201008048004008100202008080ee3,0x8004200100201008048004008102002080080ee3],
[0x0,0x8000200100201008048004008104002100080ee3,0x0,0x0,0x8000a00020200408018004002100082002080ce3,0x8000a00020200008008004000100002020080ce3,0x8000a00020200808028004004100102004080de3,0x0,0x8000a00020201008048004008100202008080ee3,0xf3000222c00088b0000f37b66000f300001e600f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0xf303cc3cc2d90f307981e601e76c807983cc0f3798b641e601e63cc079807b66001ed98003db30799c46,0x8000a00020204008148004020100802020080ee3,0x8000a00020204008148004020100802028080ee3,0x8000a00020208008248004040101002040081ee3,0x8000a00020200008008004000100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3cc1e60f307981e60f30f4e6003d3983cc0f379800204601e63cc079bcc00088b079a22c0007985906,0x3cc1e60f307a73000f30f4e6003d3983cc0f379800204601e63cc079bcc00088b079a22c0007985906,0x2008080201080402040091002080012008253e4,0x8040201080402040081002080002000201e4,0x40081002010805020400a1002080022008255e4,0x10008400201080402040081002080082000211e4,0x80082002010804020400c1002080042002219e4,0x0],
[0x10008400201080402040081002080082000211e4,0x8000201080402040081002080002000201e4,0x20008800201080442040181002080102004221e4,0x0,0x40009000201080442040281002080202008241e4,0x8001200040200008008004000108002200080ce3,0x80012000402080402040081002080402000412e4,0x0,0x0,0x0,0x0,0x3cc1e611167981e61e60f4e6f33d3983cc0f379879a04601e63cc079bcc00088b079a22c0007985906,0x210800240481,0x10800240481,0x210800240481,0x210800240481,0x410842240481,0x410842240481,0x410842240481,0x10800240481,0x810908240501,0x610842240481,0x810908240501,0x10800240481,0x80022000804080402040081002080402000814e4,0x8004200100201008048004008108002200080ee3,0x8004200100201008048004008108002200080ee3,0x8008200200201008048004008108002200080ee3,0x8000200000200008008004000108002200080ce3,0x0,0x0,0x8010020400204008148204020108002200080ee3],
[0x0,0x3cc1e6111679825f9e60f4e6f33d3983cc0f379879a04601e63cc079bcc00088b079a22c0007985906,0x240842240481,0x40800240481,0x240842240481,0x240842240481,0x4408c6240481,0x6408c6240481,0x4408c6240481,0x40800240481,0x840908240501,0x840908240501,0x840908240501,0x40800240481,0x8020200405008040204028100208068200a05104,0x0,0x0,0x0,0x0,0x0,0x240842240481,0x40800240481,0x240842240481,0x240842240481,0x4408c6240481,0x6408c6240481,0x4408c6240481,0x40800240481,0x840908240501,0x840908240501,0x840908240501,0x40800240481],
[0x8020200805008040204028100208068200a05104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_4293 : TreeBound (n := 4) 106 (programCode 0x4c290755) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part012_4294 part012_4375 part012_4376 part012_4457 part012_4538 part012_4539 part012_4540 part012_4541 part012_4542 part012_4543 part012_4544 part012_4545 part012_4546 part012_4659 part012_4756 part012_4933

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5062 : TreeBound (n := 4) 106 (programCode 0x4c290756) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x80402010002080082080082002080402000412e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5064 : TreeBound (n := 4) 106 (programCode 0x4c29075731) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x10808e121c481,0x1080821204481,0x1080821204481,0x1080861208481,0x108086120c481,0x1080861208481,0x1080861208481,0x10808e1210481,0x10808e121c481,0x10808e1210481,0x1080821204481,0x0,0xf30000b6400088b0000799e9cc007981e63ee2de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0xf30079bcc01e6f30079803cfcc00f301e63ea60000f4e600f4e6000f4e679801ed980079f9801e8e9855,0xf30000b640004bf0000f31e9cc00f301e63ee2de60f4e600f4e6000f4e679800fa980079f9801e8eb1a5,0xf3000222c1e60f30001e63cfcc00f301e63ea60000f4e600f4e6000f4e679801ed980079f9801e8ed515,0x0,0x0,0xf3000408c0010230007981e9cc007981e63ee2de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0xf3000408c03ccf300fa981e9cc007981e63ee2de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0x0,0x4000000010000000840000080100008090000420000001040000004000080020880080004020000080400000100800000100800400000208000000810000002010000010210840ca7,0xf3003cfcc007a73003cc03cfcc007981e63ee2de60f4e600f4e6000f4e679801ed98003d39801e966c85,0x0,0xf300f33cc0f30f300f3001e9cc007981e63ee2de60f4e600f4e6000f4e679800fa98003d39801e8e92b5,0x0,0xf300f33cc03ccf301e6001e9cc007981e63ee2de60f4e600f4e6000f4e679800fa98003d39801ecb52b5,0x0,0x0,0x1000080220022],
[0x100a0812a10a2,0x8000a00020400410090084002108002010080ce3,0x100a0812a10a2,0x1020084220022,0x1011886220c82,0x1000080220022,0x1011886220c82,0x1020084220022,0x1020084220022,0x1000080220022,0x1020084220022,0xf300f33cc0f30f300f3001e9cc007981e63ee2de60f4e600f4e6000f4e6798010230004105801e8e92b5,0x0,0xf300f33cc03ccf301e6001ed98007981e63f5c5e60f4e600f4e6000f4e6f300102300041f8801ecb52b5,0x0,0x0,0xf30000b6400088b0000799e9cc007981e63f1f9e60f4e600f4e6000f4e679800f4e6003db3001e8e92b5,0xf3001e9cc0000f30079803d398007981e63f1f9e60f4e600f4e6000f4e6f3001e7e6003db3001eacf7c5,0xf300012fc0002d90000f33d398007981e63f1f9e60f4e600f4e6000f4e6f3001e7e6003db3001eacf7c5,0x0,0x0,0xf301e63cc001f53098611bd398007981e63f1f9e60f4e600f4e6000f4e6f3001e7e6003db3001eacf7c5,0xf3000408c0010230007981e9cc007981e63f1f9e60f4e600f4e6000f4e679800f4e6003db3001e8e92b5,0xf3000408c0798f302e0981e9cc007981e63f1f9e60f4e600f4e6000f4e679800f4e6003db3001ecb52b5,0xf3001e9cc01e6f3001e603d398007981e63f1f9e60f4e600f4e6000f4e6f3001e7e6003db3001eacf7c5,0xf30007d4c01e6f30837783d398007981e63f1f9e60f4e600f4e6000f4e6f3001e7e6003db3001eacf7c5,0xf30079bcc007a73003cc07a731e67981e63f1f9e60f4e600f4e6000f4e7e6003cde6003db3001ee9bcd5,0xf301e63cc00088b097e79bd398007981e63f1f9e60f4e600f4e6000f4e6f3001e7e6003db3001ead3485,0xf300f33cc0f30f300f3001e9cc007981e63f1f9e60f4e600f4e6000f4e679800f4e6003db3001e8e92b5,0x0,0xf300f33cc03ccf301e6001e9cc007981e63f1f9e60f4e600f4e6000f4e679800f4e6003db3001ecb52b5,0x0],
[0x0,0x1000080220022,0x100a0812a10a2,0x0,0x100a0812a10a2,0x1020084220022,0x1011886220c82,0x1000080220022,0x1011886220c82,0x1020084220022,0x1020084220022,0x1000080220022,0x1020084220022,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5145 : TreeBound (n := 4) 106 (programCode 0x4c29075732) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x10808c6204481,0x10808c6218481,0x10808c6204481,0x10808c6218481,0x10808c4208481,0x10808c6218481,0x10808c4208481,0x10808c4208481,0x10808c6210481,0x10808c6218481,0x10808c6210481,0x10808c6218481,0x0,0xf30000b6400088b0000799e9cc00798079bf0baf9cc1e6003ea6130b4e679800fa98003d39801e8e92b5,0x10208c4220481,0xf30000b640002d90000f31f530007980f33ffeec5cc1e6007b661329ae679800fa98003d39801ee9b2b5,0x8040200000400010000004020102002080080ce3,0x10108c6220481,0x10308c6220481,0x10108c6220481,0x10308c6220481,0x10208c4220481,0x10308c6220481,0x10208c4220481,0x10308c6220481,0x0,0xf300f33cc0f30f300f33cc00f31e603cc7980f3000f6cc01152c000f6cc799e60f300f307983cc1e7556,0x0,0xf301e63cc0798f301e63cc00f33cc03ccf300f3000f6cc0118f8000f6ccf31e60f301e60f307983cd556,0x0,0x10020812210a2],
[0x100a0812a10a2,0x40000001100000001400000011000000010020200000020001000200020000208090400000200010000800040008000500008040000010000800010400000100008000100108713a7,0x100a0812a10a2,0x80102002020080802000880022020100804030e4,0xf30007d4c001f530003db300f44e4e098f300f30028ddd087c77600fa98f307983cca727418798549266,0xf307983cc03ccf300f33cc00f31e603cc7980f3000f6cc01152c000f6cc799e607980f307983cc1e7556,0xf3000408c001f530007980f3799e603cc7980f3000f6cc00f31e600f6ead980081180f307983cc1f6346,0x10220812210e2,0x10220812210e2,0xf300f33cc1e60f300f33cc00f31e603cc7980f3000f6cc01152c000f6cc799e607980f307983cc1e7556,0x10220812210e2,0x0,0xf301e63cc0798f300f30f300f44e20798f300f30028d100083f1000fa98f307983cca7107987983cd766,0x0,0xf301e63cc0f30f301e60f300f44e20798f300f3002baa0008b89000fa98f307983cca710798798b65766,0x0,0xf30000b6400088b0000799e9cc007981e63f85a91cc1e600f4e6130b4e679800f4e6003db3001e8e92b5,0x10208c4220481,0xf30000b640002d90000f31ed9800798079bf856c5cc1e6003ea6131a7e679800f4e6003db3001eacf2b5,0x0,0x10108c6220481,0x10308c6220481,0x10108c6220481,0x10308c6220481,0x10208c4220481,0x10308c6220481,0x10208c4220481,0x10308c6220481,0x0,0x0,0x0,0x0],
[0x0,0x10020812210a2,0x100a0812a10a2,0x0,0x100a0812a10a2,0x400000101000000204000000810000000800202110000800000002000000002000004220010000800020000000080004000080422000100080000404000001000400001001087fba7,0xf30007d4c001f530003ea600f4a95ed99e600f3002bb28b07c77600fa98f30f30798d4b0230f30915266,0xf303cc3cc3528f303cc1e600f4a940799e600f3002baa0008b89000fa98f30f30798d4a0f30f30799766,0xf3000408c003db30007b66007b296e099e63db3002bbe6888a2d960fad5398f30798d4b7bb0f327a9fd6,0x10220812210e2,0x10220812210e2,0x40000100100000100400001001000001000020200000020001000200020000208090400000200010000800040008000500008040000010000800010400000100008000100108713a7,0x10220812210e2,0x0,0xf301e63cc0798f300f31e600f4a940799e600f30027de00083f1000fa98f30f30798d4a0f30f30b65766,0x0,0xf301e63cc0f30f301e61e600f4a940799e600f3002baa00083f1000fa98f30f30798d4a0f30f30b65766]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5226 : TreeBound (n := 4) 106 (programCode 0x4c29075733) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x10808e121c481,0x1080821204481,0x1080821204481,0x1080861208481,0x108086120c481,0x1080861208481,0x1080861208481,0x10808e1210481,0x10808e121c481,0x10808e1210481,0x1080821204481,0x0,0xf30000b6400088b0000799e9cc00798079bf993cc0f4e6003ea6001e7e679800fa98003d39801e8e92b5,0xf30079bcc0260730097e01f53000f300f33f993cc0f4e6007b66001e7e679800fa980079f9801ee9b345,0xf30000b640004bf0000f31f53000f300f33f993cc0f4e6007b66001e7e679800fa980079f9801ee9b345,0xf300012fc1e60f30798f31f53000f300f33f993cc0f4e6007b66001e7e679800fa980079f9801ee9d1a5,0x0,0xf303cc3cc001f530b6c8b1f53000f300f33f993cc0f4e6007b66001e7e679800fa980079f9801ee9b345,0xf3000408c0010230007981e9cc00798079bf993cc0f4e6003ea6001e7e679800fa98003d39801e8e92b5,0xf3000408c0f30f300fa981e9cc00798079bf993cc0f4e6003ea6001e7e679800fa98003d39801e8e92b5,0x0,0xf30007d4c01e6f307bdf81f53000f300f33f993cc0f4e6007b66001e7e679800fa980079f9801ee9b345,0xf3001e9cc007a73003cc01e9cc00798079bf993cc0f4e6003ea6001e7e679800fa98003d39801e962ab5,0xf303cc3cc0004bf0b64f31f53000f300f33f993cc0f4e6007b66001e7e679800fa980079f9801ee9b345,0xf300f33cc0f30f300f3001e9cc00798079bf993cc0f4e6003ea6001e7e679800fa98003d39801e8e92b5,0x0,0xf300f33cc03ccf301e6001e9cc00798079bf993cc0f4e6003ea6001e7e679800fa98003d39801ecb52b5,0x0,0x0,0xc00030004008100a0104004100402200080de3],
[0x0,0x80080220022,0x0,0x480084220022,0x280882220482,0x80080220022,0x280882220482,0x480084220022,0x480084220022,0x80080220022,0x480084220022,0x0,0x0,0x0,0x0,0x0,0xf30000b6400088b000079bd39800798079bee2fcc1e7e6003ea6001e7e6f3001e7e6003db3001ead3485,0xf3001e9cc0000f30097e01ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001eacf2b5,0xf30000b640002d90000f31ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001eacf2b5,0x0,0x0,0xf301e63cc001f5309868b1ed9800f300f33f1fbcc0f4e6007b66001e7e679800f6cc007a73001eacf345,0xf3000408c001f530007981ed9800f300f33f1fbcc0f4e6007b66001e7e679800f6cc007a73001eacf345,0xf3000408c03ccf301ed981ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001ecb52b5,0xf3001e9cc01e6f3001e601ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001eacf2b5,0xf30007d4c01e6f30833ac1ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001eacf2b5,0xf3001e9cc00f3f3003cc01ed9800f300f33f1fbcc0f4e6007b66001e7e679800f6cc007a73001eb4a9a5,0xf301e63cc0002d9088bf31ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001eacf2b5,0xf300f33cc0f30f300f3001ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001f44d2b5,0x0,0xf300f33cc03ccf301e6001ed9800798079bee2fcc0f4e6003ea6001e7e679800f4e6003db3001ecb52b5,0x0],
[0x0,0x0,0x0,0x80080220022,0x0,0x480084220022,0x280882220482,0x80080220022,0x280882220482,0x480084220022,0x480084220022,0x80080220022,0x480084220022,0x0,0x0,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5307 : TreeBound (n := 4) 106 (programCode 0x4c29075734) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1080821204481,0x1080842218481,0x1080821204481,0x1080800200481,0x1080800208481,0x1080800200481,0x1080800208481,0x1080800208481,0x1080842210481,0x1080842210481,0x1080842210481,0x1080800200481,0x0,0x0,0x8040021000404010180804020102002080080ce3,0x0,0x80800220481,0x280842220481,0x80800220481,0x280842220481,0x280842220481,0x4808c4220481,0x6808c6220481,0x4808c4220481,0x80800220481,0x0,0x0,0x0,0x0,0x0,0x10020812210a2],
[0x100a0812a10a2,0x0,0x100a0812a10a2,0x80102002020080802001080042020100804030e4,0xf30007d4c001f530003db3007ace7b9996d73f30019af3d0fc32101ee127307983cca73e098b6c0f6f96,0xf300003cc0f30f303cc00000f379803cde600f3001e9cc007980001e9cc7980007983cc0798f30799556,0x4000000210000004040000002100000010100000201100104001000002001001010000006204200080100000042242000200c0100008000200088009000080001000080084c84b4a8,0x10220812210e2,0x10220812210e2,0xf303cc3cc1e60f303cc3cc00f379803cde600f3001e9cc00a710001e9cc799e607983cc0798f30799556,0x10220812210e2,0x0,0xf301e63cc0798f300f30f300f42fc0798f300f30027de000fd71001ed98f307983cc97e07987983cd766,0x0,0xf301e63cc0f30f301e60f300f42fc0798f300f30029c40010509001ed98f307983cc97e0798798b65766,0x0,0x0,0x0,0x0,0x80800220481,0x280842220481,0x80800220481,0x280842220481,0x280842220481,0x4808c4220481,0x6808c6220481,0x4808c4220481,0x80800220481,0x0,0x0,0x0,0x0],
[0x0,0x10020812210a2,0x100a0812a10a2,0x0,0x100a0812a10a2,0xf303cc3cc2f76f300799e601e76c80799e600f30048240010416001ed99e60f30798b640f30f30799c76,0xf30007d4c001f530003db300f4a97d398f300f30027e5980f5f7601ed98f30798798d4bf530798549266,0xf303cc3cc2d90f303cc1e601e76c80799e600f30048240010416001ed99e60f30798b640f30f30799c76,0xf3000f6cc00102300080a02b261e601e6f33db3004bd12684469161e8616639016860f30f3079a2fadb6,0x10220812210e2,0x10220812210e2,0x0,0x10220812210e2,0x0,0xf301e63cc0798f300f30f300f4a940798f300f30027de000fd71001ed98f30798798d4a0f307983cd766,0x0,0xf301e63cc0f30f301e60f300f4a940798f300f3002baa0010509001ed98f30798798d4a0f30798b65766]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5388 : TreeBound (n := 4) 106 (programCode 0x4c29075735) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5389 : TreeBound (n := 4) 106 (programCode 0x4c29075736) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5390 : TreeBound (n := 4) 106 (programCode 0x4c29075737) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5391 : TreeBound (n := 4) 106 (programCode 0x4c29075738) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080842240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5392 : TreeBound (n := 4) 106 (programCode 0x4c29075739) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10808c4240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5393 : TreeBound (n := 4) 106 (programCode 0x4c2907573a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10808c6240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5394 : TreeBound (n := 4) 106 (programCode 0x4c2907573b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x10808c4240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5395 : TreeBound (n := 4) 106 (programCode 0x4c2907573c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x1080800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5396 : TreeBound (n := 4) 106 (programCode 0x4c2907573d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c8001e601e67d4c003ee2e04601e7e601e61e601e9cc001023000408c001e7032b5,0xf37983cc1e61060398001e7e600f6cc003ffe92e601e7e601e61e601e9cc0010230007d4c001e703345,0x16c80005b200025f8001e601e67d4c003ee2fea601e7e601e61e601e9cc001023000408c001e7032b5,0x0,0x8000480010410010402004080108002200082ce3,0x108080240022,0x8000880020410010402004080108002200082de3,0x108080240022,0x120084240022,0x110084240022,0x100080240022,0x110084240022,0x120084240022,0x120084240022,0x100080240022,0x120084240022,0x100080240022,0x0,0x8020080800410010402004080108002200086ce3,0x0,0xfa98007b660008118001e61e607d4c003cfdb6cc03cde601e61e601e9cc001023000408c001e703465,0x8040001000410010002004080108002200080ce3,0xfa98002046000fa98003cc1e607d4c003df1a7e601e7e601e61e601e9cc001f53000408c001e7037c5,0xfa98003ea6000fa98003cc1e607d4c003df1a7e601e7e601e61e601e9cc001f53000408c001e7037c5,0x402000008008000010020000010080000008000400010040000040800000202c9004000020080000400100000800100000804000000410000000840000002100000010030850ca7,0x0,0xf307d4c0093757b0799e601e67d4c003ffeb14601e7e601e61e601e9cc001023000408c001e7032b5,0x408084240022,0xf307d4c003857610f31e601e67d4c003ffeee0601e7e601e61e601e9cc001023000408c001e7032b5,0x408084240022,0xe109c8240501],
[0xe709c8240501,0xe109c8240501,0xe709c8240501,0xe209c8240501,0xe709c8240501,0xe209c8240501,0xe709c8240501,0xe409c8240501,0xe709c8240501,0xe409c8240501,0xe709c8240501,0x0,0x4089c8240501,0x8080240022,0x4089c8240501,0x8080240022,0x4109c8240501,0x4709c8240501,0x4109c8240501,0x4309c8240501,0x4209c8240501,0x4709c8240501,0x4209c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x2040001000410010002004080108002200080ce3,0x0,0x808908240501,0x8080240022],
[0x808908240501,0x8080240022,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x880490010210010482004080108001200082ca3,0x0,0x9004980202100104c2004080108001200082fa3,0x0,0xe109c8240501,0x840908240501,0xe109c8240501,0xe709c8240501,0xe209c8240501,0xe709c8240501,0xe209c8240501,0x840908240501,0x840908240501,0x908240501,0x840908240501,0x908240501,0x0],
[0x808908240501,0x0,0x808908240501,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x0,0x0,0x0,0x0,0x810908240501,0x40908240501,0x810908240501,0x850908240501,0xa20948240501,0xa20948240501,0xa20948240501,0x40908240501,0x40908240501,0x908240501,0x40908240501],
[0x908240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5525 : TreeBound (n := 4) 106 (programCode 0x4c2907573e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0003000402010080404200108002200080ce3,0x16c800111600016c83cc00f3000f6cc003db31e603cde61e6204603cfcc1e60f30000b640001e61556,0x140005000402010080404200108002200080ce3,0x25f800111600025f8000f3f3f35b99800f3f33cc79ae8302e0b66079bcc00088b079b15c0007985426,0x240009000404010180804200108002200080ce3,0x280888240482,0x80088240022,0x280888240482,0x481088240862,0x481088240862,0x80088240022,0x481088240862,0x0,0x0,0x8088240022,0x0,0x8088240022,0x8108c6240481,0x800800240481,0x8108c6240481,0x8308c6240481,0x8208c6240481,0x8308c6240481,0x8208c6240481,0x800800240481,0x840908240501,0x800800240481,0x840908240501,0x840908240501,0x0,0x6088c6240481],
[0x1e600097e0007b66000b6400f31e603cc7980f31e603cde61e6204603cfcc1e60f300f33cc03cc1e7556,0x6088c6240481,0x3cc0010230007b6600102300f44e20798f300f33cc79ae8302e0b66079bcc0798f30a713cc07983d1426,0x6108c6240481,0x800240481,0x6108c6240481,0x6308c6240481,0x20800240481,0x20800240481,0x20800240481,0x800240481,0x840908240501,0x800240481,0x840908240501,0x800240481,0x0,0x0,0x0,0x0,0x0,0x8108c6240481,0x800800240481,0x8108c6240481,0x8308c6240481,0x8208c6240481,0x8308c6240481,0x8208c6240481,0x800800240481,0x840908240501,0x800800240481,0x840908240501,0x840908240501],
[0x0,0x0,0x0,0x0,0x7980020460007d4c00111601e7a940799e600f33cc799f5301edb66079bcc0f30f30d4a3cc0f3079d936,0x6108c6240481,0x800240481,0x6108c6240481,0x6308c6240481,0x6208c6240481,0x6308c6240481,0x6208c6240481,0x800240481,0x40908240501,0x800240481,0x40908240501,0x800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5606 : TreeBound (n := 4) 106 (programCode 0x4c2907573f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x16c800111600016c8001e601e67a73003f1ffb6601e67981e63cc01e9cc001023000408c001e7032b5,0x0,0x3d398003ea60102a98003ce04607a73003d9689cc01e67981e63cc01e6003cde603cc3cc03cde7037c5,0x40021000420010004004100100002020080ce3,0x3d3980020460102a98003ce04607a73003d977ccc01e67981e63cc01e600799e600f33cc0799e7037c5,0x7983cc1e6003d398007a73001e9cc003cc0079801e7e60079bcc01e600003cc0000f4e6001e64d995,0x10020000010080000040200000c0080000008000400020060000040200000201e9008000020020000400040000800200000800004000400080001000100002000100010030851ca7,0x0,0xf379803cde60130398001e7e600f4e6003d58d4e601e6f301e63cc01e601e60f30f307983cc1e703345,0x79800f4e6003d398007a73001e9cc003cc0079801e7e60079bcc01e600003cc3cc0f303cc1e64d995,0x40021000420010004004100100802020080ce3,0x7983cc1e6003d398007a73001e9cc003cc0079801e7e60079bcc01e60f303cc3cc0f6cc001e64d995,0x0,0x0,0x0,0x6220200000100800040002000004008000002031100008002000004020000020900020000100080000400040000800200000806a2000101000000400100000210000001001087fca7,0x0,0x3d3983cc1e600f3798003cde6007a73003f7c89cc01e67981e63cc01e9cc001e60f30408c001e7037c5,0x16c800097e00025f8001e603ccf4e6003f1fbea601e6f301e63cc01e9cc0010230007d4c001e7051a5,0x0,0xc0101000420010014004100100082002080ce3,0x798003ea60798798007a73001e9cc003cc0079801e7e60079bcc01e600003cc0000f30f301e64d995,0x140101000420010024004100100102004080de3,0x40101000420010004004100100002100080ce3,0x0,0x0,0x0,0x7981e61e60798798007a73001e9cc003cc0079801e7e60079bcc01e600003d39800f303cc1e64d995,0x3cc798003ea603cc798003cc1e60f4e6003d3b69cc01e6f301e63cc01e60f301e6f300798f301e703855,0x480020000200080000020200002000800000080400000800040000804000002000000800008008000040008000080020000080010000041000000400100000400000001001285bda7,0x3cc798003ea603dba98001e61e60f4e6003d3b67e601e6f301e63cc01e60f300f37980799e601e703345],
[0x40101000420010004004100104002000080ce3,0x0,0x0,0x40101000420010004004100104002100080ce3,0x2200000002800000022000000028000000201001800001004000010000008010020002001100000400200020011000004002000000102000c000200020000200000040002793a8,0x0,0x208948240501,0x0,0x208948240501,0x0,0x210948240501,0x250948240501,0x210948240501,0x210948240501,0x220948240501,0x220948240501,0x220948240501,0x250948240501,0x240948240501,0x270948240501,0x240948240501,0x250948240501,0x0,0x3cc0798f3088b000079bcc0798f4e6003ea603cc01e6f301e63cc01e9cc001f530007d4c001e707515,0x0,0x1e607987984fbde60f31e603ccf4e6003f1fbea601e6f301e63cc01e9cc0010230007d4c001e7051a5,0x0,0xa10948240501,0x840908240501,0xa10948240501,0xa50948240501,0xe209c8240501],
[0xe709c8240501,0xe209c8240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x8118002046000fa98001e61e607a73003d791ae601e67981e63cc01e9cc001023000408c001e7032b5,0x40011000420010004004100108002200080ce3,0x3d39803cde6003d398001e7e600f4e6003d58d4e601e6f301e63cc01e9cc0010230007d4c001e703345,0xf3079803cde61060398001e7e600f4e6003d58d4e601e6f301e63cc01e9cc0010230007d4c001e703345,0x0,0x4089c8240501,0x0,0x4089c8240501,0x0,0x4109c8240501,0x4709c8240501,0x4109c8240501,0x4309c8240501,0x4209c8240501,0x4709c8240501,0x4209c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x4409c8240501,0x4709c8240501,0x0,0x808908240501,0x0,0x808908240501],
[0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x808908240501,0x2040080100420010404004100108002200082ce3,0x808908240501,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x7a73001e6f30079fa73001e9cc003cc0079801e7e60079bcc01e9cc003db3000f6cc001e64d995],
[0x622021001888002000000210000000020000203110000800000000804000002000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x1e6f300799e600f37a73001e9cc003cc0079801e7e60079bcc01e9cc003db3000f6cc001e64d995,0x0,0xe109c8240501,0x840908240501,0xe109c8240501,0xe709c8240501,0xe209c8240501,0xe709c8240501,0xe209c8240501,0x840908240501,0x840908240501,0x908240501,0x840908240501,0x908240501,0x0,0x808908240501,0x0,0x808908240501,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x820908240501,0x820908240501,0x820908240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501],
[0x0,0x0,0x0,0x0,0x400030001000010000000300000000100000203000000800000000804000002000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x810908240501,0x40908240501,0x810908240501,0x850908240501,0xa20948240501,0xa20948240501,0xa20948240501,0x40908240501,0x40908240501,0x908240501,0x40908240501,0x908240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5783 : TreeBound (n := 4) 106 (programCode 0x4c29075740) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80088200022,0x80088204022,0x80088200022,0x80088204022,0x0,0x481088208862,0x80088200022,0x481088208862,0x481088210862,0x481088210862,0x80088200022,0x481088210862,0x16c800111600016c8001e601e67a73003ee2ed9001e67981e711601e679800fa98003d39801e7032b5,0x0,0x16c800111600016c8003cc07987b66003f2008b001e6f301e72fc01e6f3001e7e6003db3001e707485,0x0,0x16c800111600016c800000f3003cfcc00f3f33cc03ccf300003cc03cfcc0000f3000222c0007985216,0x0,0x80088200022,0x180488284222,0x80088200022,0x180488284222,0x0,0x0,0x80088200022,0x0,0x80088210022,0x80088210022,0x80088200022,0x80088210022],
[0x16c80005b200025f8001e601e67d4c003fd62a5001e7e601e711601e679800fa98003d39801e7032b5,0x80088220022,0x16c800097e00025f8001e603ccf4e6003f1fcbf001e6f301e72fc01e679800f6cc007a73001e7051a5,0x80088220022,0x445800111600025f8000f4e6f33d39800f3f379879a04601edd4c079bcc00088b079a22c0007985936,0x0,0x0,0x798f3079f980079800f3003cfcc00f3f33cc03ccf300003cc03cfcc0000f3000222c0007985216,0x0,0x3cc2269b307a73000f30f4e7026d39800f3f379881384601edd4c079bcc00088b0813a2c0007985936,0x210800240481,0x200800240481,0x210800240481,0x210800240481,0x220842240481,0x220842240481,0x220842240481,0x200800240481,0x240842240481,0x230842240481,0x240842240481,0x200800240481,0x280888240482,0x80088240022,0x280888240482,0x481088240862,0x481088240862,0x80088240022,0x481088240862,0x0,0x2000480010410010402004200108002200082ce3,0x8088240022],
[0x2000880020410010402004200108002200082de3,0x8088240022,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x82094a240501,0x82094a240501,0x82094a240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0xc00410010402010080404200108002200080ce3,0x1e600097e0007b66000b6400f379803cde600f33cc03ccf31e6222c03cfcc1e60f303cc3cc0f30799556,0xc00810020402010080404200108002200080ce3,0x3cc0010230007b6600102300f42fc0798f300f33cc79a04602e0d4c079bcc0798f3097e3cc07983d1426,0x610842240481,0x800240481,0x610842240481,0x610842240481,0x620842240481,0x620842240481,0x620842240481,0x800240481,0x840908240501,0x800240481,0x840908240501,0x800240481,0x0],
[0x4000500010420010804004200108002200084ce3,0x0,0x4000900020420010804004200108002200084de3,0x0,0x810908240501,0x840908240501,0x810908240501,0x850908240501,0x82094a240501,0x82094a240501,0x82094a240501,0x840908240501,0x840908240501,0x800908240501,0x840908240501,0x840908240501,0x0,0x0,0x0,0x0,0x3cc0011160007d4c00102300f4a940798f300f33cc79af7602e0d4c079bcc0798f30d4a3cc07983d1426,0x10800240481,0x800240481,0x10800240481,0x10800240481,0x220842240481,0x220842240481,0x220842240481,0x800240481,0x40800240481,0x800240481,0x40800240481],
[0x800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5063 : TreeBound (n := 4) 106 (programCode 0x4c290757) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part012_5064 part012_5145 part012_5226 part012_5307 part012_5388 part012_5389 part012_5390 part012_5391 part012_5392 part012_5393 part012_5394 part012_5395 part012_5396 part012_5525 part012_5606 part012_5783

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5912 : TreeBound (n := 4) 106 (programCode 0x4c290758) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x80402010004080102080002002080402000804e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5913 : TreeBound (n := 4) 106 (programCode 0x4c290759) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x1081090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5914 : TreeBound (n := 4) 106 (programCode 0x4c29075a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x1080010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5915 : TreeBound (n := 4) 106 (programCode 0x4c29075b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x1081090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5916 : TreeBound (n := 4) 106 (programCode 0x4c29075c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 4)
    (a := List.flatten [
[0x1080010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5918 : TreeBound (n := 4) 106 (programCode 0x4c29075d71) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x182030204481,0x16c800111600016c807981e679800081185b4d9001e9cc01e6f3001e63cc01e6f30079bcc01e703855,0x182030204481,0x0,0x182021204481,0xc0003002000480000004020100002000080ce3,0x182021204481,0x182020200481,0x182062208481,0xc0003002000480000004000100002000080ce3,0x182062208481,0xc0003002000480010084080100082002080ce3,0x16c800111600016c807981e679800081185b3e9cc1e63cc1e603cc1e63cc01e8d9f379bcc01e703855,0x0,0x16c800111600016c807980f37980008119024ed981e61e61e607981e61e601ee1273799e601e77d055,0x182021204481,0x0,0xc0003002000480080404200100402010080ce3,0x0,0xc0003002000480000004200100002000080ce3,0x2200000008800000012000000018000200020110800000081000000021000000040000100100000400400000801000000800020001000080004000100010000100010014c7ffa7,0xc0003002000480008004200108002000080ce3,0x16c800111600016c8079801ed980008119e8139001e9cc01e6f3001e601e60f307983cc3cc1e7032b5,0x0,0x80402012000480418004200108002080082ce3,0xc4002102000480418004200108002080082ce3,0x80802022000480418004200108002080082de3,0x0,0x81002042000480418004200108002080082ee3,0xc0002412000480418004200108002080082ce3,0x82002082000480418004200108002080082ce3],
[0xc0002402000480418004200108002080082ce3,0x84002102000480418004200108002080082ce3,0x82002082000480418004200108002080082ce3,0x88002202000480418004200108002080083ce3,0x80402412000480418004200108002080082ce3,0x90002402000480418004200108002080082ce3,0x82002592000480418004200108002080082ce3,0xa0002802000480418004200108002080086ce3,0x90002412000480418004200108002080082ce3,0x220000000880000001200000001800020001321280000080100000002100000004000010010000040040000080100000080020000100080000400100001000100001001487ffa7,0x445800097e00016c81e63869a6c0008118000f30079bcc00f3f3001ed0d2d7db3f30f300001e68a925,0x16c800111600016c807980f37980008119025d9001e9cc01e6f3001e60f300f33cc03cde601e77cab5,0x182030204481,0x0,0x10a130220501,0x122130220501,0x10a130220501,0x0,0x112130220501,0xc0002412000480418004200102002080082ce3,0x112130220501,0xc0002402000480418004200102002080082ce3,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501,0x0,0xf30798f307980f30811801ed980008119e8139001e9cc01e6f3001e603cc1e60f303cc3cc1e7037c5],
[0x84002102000480008004200100402000080ce3,0xf30798f303cc0f30fa9801ed980008119e8139001e9cc01e6f3001e603cc0f316c87983cc1e703345,0x0,0x81002042000480518004200100402020082ee3,0x4ada5a897e1e60f301e63869a6c0008118000f30079bcc00f3f3001ed0d2d7db3f30f300001e68a925,0x82002082000480518004200100402020082ce3,0x48240009f780010231e6358ec0c0f38118000f30079bcc00f3f3001ebb9983df0b30f379801e870925,0x84002102000480008004200100402000080ce3,0x4ada5a8799e600f301e63869a6c0008118000f30079bcc00f3f3001ed0d2d7cc88b0f300001e68a925,0x88002202000480018004200100402002080ce3,0x4ada5a87981e60f301e63869a6c0008118000f30079bcc00f3f3001ed0d2d7cc0f30f300001e68a925,0x90002402000480418004200100402080082ce3,0x4ada5a87a93460f301e63869a6c0008118000f30079bcc00f3f3001ed0d2d7cc89a3f300001e68a925,0xa0002802000480818004200100402100084ce3,0x80002002000480008004200100402000080ce3,0x0,0x10a130220501,0x122130220501,0x10a130220501,0x80403012000480818004200102001100084ca3,0x112130220501,0x0,0x112130220501,0x0,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501],
[0x0,0x10a030200481,0x122130220501,0x10a030200481,0x0,0x0,0x445ad9097e1e60f301e61e6ba0c0008118000f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x0,0x48240009f780010231e61e6d86c0008118000f30079bcc00f3f3001e9cda97db32d9f3003cde68a925,0x122130220501,0x446ec80799e600f301e61e6ba0c0008118000f30079bcc00f3f3001e9cc003db3000f300001e68a925,0x122130220501,0x10a030200481,0x142030204481,0x4ada5a87a93460f301e63533a0c0008118000f30079bcc00f3f3001eca66cbdefc00f300001e68a925,0x142030204481,0x102030200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6031 : TreeBound (n := 4) 106 (programCode 0x4c29075d72) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000420012004080508004200108002200082ce3,0x8040020102004080508004200108002200082ce3,0x8000820022004080508004200108002200082de3,0x0,0x8040020012004080500084002108002200082ce3,0x0,0x8040020022004080500104004108002200082de3,0x0,0x108084240022,0x108882240482,0x108080240022,0x108882240482,0x108084240022,0x108084240022,0x108080240022,0x108084240022,0x108080240022,0x808020200080022020000802080006000000e4,0x0,0x808020200080022040001002080006000000e4,0x8001020042004080508004200108002200082ee3,0x8040020502004080508004200108002200082ce3,0x8002020082004080508004200108002200082ce3,0x8040020402004080508004200108002200082ce3,0x8004020102004080508004200108002200082ce3,0x8014020502004080508004200108002200082ce3,0x8008020202004080508004200108002200083ce3,0x8004020502004080508004200108002200082ce3,0x8010020402004080508004200108002200082ce3,0x3b9aca000782403d78b217b9aca000773595dcd6501dcd650001dcd65077360b35a6be2cc09acbdcd653b9aca0ee6b639aca0001dcd6501dcddc35940773770d6503b9b41359403b9ca6d65003ba23d594003bb89765000eee25d94003bb89765000eee25d94000ef5b77a5d1279,0x8020020802004080508004200108002200086ce3],
[0x440000008200000004800000011000100000400000802000002008004000010040000080100000000400008001000002004000000010000800040002000100000004000252e28]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6064 : TreeBound (n := 4) 106 (programCode 0x4c29075d73) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x182030204481,0x140005002000880008004200100002020080ce3,0x182030204481,0x0,0x182021204481,0x140005002000880000004020100002000080ce3,0x182021204481,0x182020200481,0x182062208481,0x140005002000880000004000100002000080ce3,0x182062208481,0xc0005002000880020104084100101084080fa3,0x0,0x0,0x0,0x182021204481,0xc0005002000880022004080100101084080fa3,0x140005002000880080404200100402010080ce3,0x140005002000880024004100100102100080de3,0x140005002000880000004200100002000080ce3,0x0,0x182061208481,0xa0000000280000000a000000028000040000800800000201000000041000422101000020004000400024000800040000800004000400080001000100004000100010031851da7,0x182061208481,0x182060208481,0x182062208481,0x140005002000880040a04008100202008080ee3,0x182062208481,0x0,0x6000000018000000060000000280000400010008000002010000000410000ca980400020008000400010000800010000800004000200080000800100002000100010031840ca7,0xa0000000280000000a000000028000040000040800000201000000041000800002000020000200400400000801040000800004000400080001000100004000100010031851da7],
[0x6000000088000000060000000280000400010028000002010000000410002d2d00400020008000400004000800020000800004000200080004000100002000100010031843ca7,0x182063208481,0x0,0x0,0x0,0x0,0x0,0x18206120c481,0x140005002000880000004020100002000080ce3,0x18206120c481,0xc0005002000880020004000100001004080fa3,0x220000000880000002200000002800020001321480000080100000004100000000020010000080040000100080000100080264280100010000400040001000000001001487ffa7,0x140005002000880000004000100002000080ce3,0x16c80005b200025f807981e6798000fa9863132799e601e7e600f31e63cc00f3f3003d86265e7032b5,0x0,0x182024204481,0x220000000880000002200000002800020003111410000000100000004100000006222810000080008040000080000000080622280100000000400000001000000001001087f3a7,0x182024204481,0x445800111600025f80798003ea6000fa98000001e7e60079f980001e607983cc0000f300001e64d995,0x0,0x0,0x0,0x0,0x16c800097e00025f8079801ed980017419e831f001e9cc01e6f3001e601e60f30f307983cc1e703345,0x0,0x0,0x0,0xc0005002000880020084004100001080080fa3,0xc0005002000880020104004100001080080fa3,0xc0005002000880060204008100201088080fa3,0x140005002000880000004000100002080080ce3,0xc00050020008800e0204010100201090080fa3],
[0xc0005002000880020104084100101084080fa3,0x0,0x220000000880000002200000002800020003111410000000100000004100000006222810000080008040000080000000080622280100100000400000001001000001001087f3a7,0x0,0xc0005002000880020104004100001080080fa3,0xc0005002000880022004080100101084080fa3,0x0,0x140005002000880024004100100102080080de3,0x0,0x16c80005b200025f807981e6798000fa9863225001e9cc01e6f3001e60f300f3f3003ccf301e7032b5,0x0,0xf307983cc7981e6081180025f8000fa9a4bfb5001e9cc01e6f3001e601e60f300f34157d85e7032b5,0x1168041020008805280042001008020b4082de3,0x8040402200088002800420010010100c080fa3,0x0,0x2001000008004000020008000020008200033334800000081000000041000000040000100100000400400000801000000806666801000080004000040010000000010014c7ffa7,0x140004002000880008004200100002010080ce3,0xf33cc03ccf301e679f9801ed98000fa9a4bfb5001e9cc01e6f3001e601e60f30f304157d85e7032b5,0x140004402000880428004200102002090082de3,0x840041020008805280042001008010ac082fa3,0x109c87985b21e709c81e65b20f409c87981e60f3f3084e7cc02d9f3007983ce1390f379800f32d916e146,0x8400420200088062800420010100104c083fa3,0x8080402200088002800420010010100c080fa3,0x90004402000880428004200102001088082fa3,0x1ed9800799e601ed987981e6798000fa985b6bf001e9cc01e6f3001e603cc1e6f30079c08c1e703855,0x120004802000880828004200104002110084de3,0x100004002000880008004200100002010080ce3,0x16c800097e00025f807980f37980017419029a5001e9cc01e6f3001e60f300f37980799e601e77e9a5,0x182030204481,0x0,0x10a130220501,0x122130220501],
[0x10a130220501,0x0,0x112130220501,0x140004422000880428004200102002080082de3,0x112130220501,0x140004402000880428004200102002080082de3,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501,0x25f800097e00025f8079801ed98000fa99e60f3001e9cc01e6f3001e9cc001e60f307d4c001e703855,0x0,0x10a130220501,0x122130220501,0x10a130220501,0x100805002000880828004200104002100084de3,0x112130220501,0x0,0x112130220501,0x0,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501],
[0xc0005002000880028004200100001200080fa3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6193 : TreeBound (n := 4) 106 (programCode 0x4c29075d74) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x182021204481,0x44580799e6000445807981e6798001ed985b9980f4e600f4e6000f4e63cc01e6f30079bcc01e703855,0x182021204481,0x182021204481,0x182061208481,0x38206120c481,0x182061208481,0x0,0x0,0x44584469160004458079801ed98001ed98025f80f4e600f4e6000f4e603cc1f5300079c08c1e703855,0x44581e61e6000445807980f3798001ed9902a980f4e600f4e6000f4e61e601e67980799e601e780d15,0x182021204481,0x0,0x0,0x0,0x0,0x0,0xc0011002002080080404020100082002080ce3,0x2040001002000080000004020100002020080ce3,0x140011002002080080404020100102004080ce3,0x40001002000080000004020100002000080ce3,0x0,0x40001002000080000004020100002000080ce3,0x0,0x0,0x2040001002000080000004020100802020080ce3,0x16c800111600025f801e607a7e6479bea60f30026ae4009b32800fa981e60f3079ff320f30f31aa656,0x2040001002000080000004020101002040080ce3,0x40001002000080000004020100002000080ce3,0x0],
[0x0,0x0,0x0,0x0,0x182021204481,0x2040005002000880000104004100002020080ce3,0x182021204481,0x182021204481,0x182061208481,0x38206120c481,0x182061208481,0x140005002000880000104004100002080080ce3,0x25f80799e600025f807981e6798000fa985b5cc1e7e6007b66001e7e60f301e6f300798f301e703855,0x0,0x25f81e61e600025f807980f3798000fa99026cc1e7e6007b66001e7e61e601e67980799e601e77eeb5,0x182021204481,0x0,0x0,0x0,0x0,0x0,0x182021204481,0x0,0x182021204481,0x82000200481,0x82000208481,0x82000200481,0x82000208481,0x82000220481,0x0,0x16c800111600025f801e607a7e6479bf990f300177e40114b2801ed981e60f3079ff320f316c9aa656,0x0],
[0x82000200481,0x82000220481,0x0,0x82000220481,0x0,0x8040009002001080040204008108002200080ee3,0x8040001002000080000004000108002200080ce3,0x8040011002002080080404010108002200080ce3,0x8040001002000080000004080108002200080ce3,0x0,0x8000420012004080500804020108002200082ce3,0x108084240022,0x8000820022004080500804020108002200082de3,0x108084240022,0x121084240862,0x111084240862,0x100084240022,0x111084240862,0x121084240862,0x121084240862,0x100084240022,0x121084240862,0x100084240022,0x210000000840000001080000002080060020100080020400200080800100001006202b1014880244010400020000400020040003001100000001400010005000040012000ffea8,0x8020020802004080500804020108002200086ce3,0x210000000840000001080000002100000000100000080400000200800c0000100000000000000000002000100000c0006004000000010000000440000001100000004000273228,0x0,0x0,0x108084240022,0x0,0x108084240022,0x121084240862],
[0x111084240862,0x100084240022,0x111084240862,0x121084240862,0x121084240862,0x100084240022,0x121084240862,0x100084240022,0x1100044020080802008100202080102004221e4,0x0,0x1200048040081002008200202080202008241e4,0x0,0x8000440012008080601004040108002200083ce3,0x108080240022,0x8000840022008080601004040108002200083de3,0x108080240022,0x121084240862,0x111084240862,0x100080240022,0x111084240862,0x121084240862,0x121084240862,0x100080240022,0x121084240862,0x100080240022,0x0,0x8020040802008080601004040108002200087ce3,0x0,0x8040001002000080000004000108002200080ce3,0x0,0x8000480012010080402004080108002200082ce3,0x108080240022],
[0x8000880022010080402004080108002200082de3,0x108080240022,0x121084240862,0x111084240862,0x100080240022,0x111084240862,0x121084240862,0x121084240862,0x100080240022,0x121084240862,0x100080240022,0x0,0x8020080802010080402004080108002200086ce3,0x0,0x25f800111600025f8000f3f3f35b99bcc00f33cc79ae832140b66079bcc00088b079b15c0007985426,0x0,0xc0101002020080014004100100082002080ce3,0x7980799e607987980798f301e63cc079800079801e7e60079bcc01e600003cc0000f30f301e64d995,0x140101002020080024004100100102004080de3,0x40101002020080004004100100002100080ce3,0x0,0x0,0x0,0x7981e61e607987980798f301e63cc079800079801e7e60079bcc01e600003d39800f379801e64d995,0x0,0x0,0x0,0x40101002020080004004100104002000080ce3,0x0,0x0,0x40101002020080004004100104002100080ce3,0x2200000002800000022000000028000000201001000001004000010010000010020002001100000400200020001000004002000000102000c000200020000200000040002793a8],
[0x445800111600025f8000f4e6f33d39bcc00f379879a04620463cc079bcc00088b079a22c0007985936]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6354 : TreeBound (n := 4) 106 (programCode 0x4c29075d75) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8118007b66000811807980025f8003d399e71160f4e600f4e6000f4e9cc001023000408c001e7032b5,0x8118007b66000811807981e6798003d3985c13f301e9cc01e60f301e9cc001f530007d4c001e703855,0x8118007b6600081180798004458003d399e72fc0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0x282061204481,0x0,0x282061204481,0x282040200481,0x282040208481,0x282040208481,0x282040208481,0x282042228481,0x0,0x109cf9803cde60079f9842721e616c83cfcc00f300450e4009ab9001e9cc3ce1390f307980f32d916e5c6,0x0,0x282040208481,0x282042220481,0x0,0x282042220481,0x0,0x282042240481,0x240009002001080040804008108001200080ea3,0x282042240481,0x0,0x20a14a240501,0x409882240c82,0x20a14a240501,0x409882240c82,0x21214a240501,0x27214a240501,0x21214a240501],
[0x25214a240501,0x22214a240501,0x22214a240501,0x22214a240501,0x25214a240501,0x24214a240501,0x27214a240501,0x24214a240501,0x25214a240501,0x2020000008080000010200000010800020001332080000080100000020100000000200010000800040001000080001000080400000101000000404000001010000001001487ffa7,0x1ed98003ea600081181e63cb10cc003d398001e586f9bdb30f300001e9cc003db3000f6cc001e6ceea5,0x2020000008080000010200000010800020001910080000100100000020100000000200010000800040002000080002000080400000101000000404000001010000001001cc7ffa7,0x282042240481,0x0,0x20a148240501,0x409084240862,0x20a148240501,0x409084240862,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501,0x0,0x20a1c6240501],
[0x804400110080402020080802080082002010e4,0x20a1c6240501,0x1008400210080402020080802080082002010e4,0x2121c4240501,0x2721ce240501,0x2121c4240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2421cc240501,0x2721ce240501,0x2421cc240501,0x2721ce240501,0x0,0x20a148240501,0x0,0x20a148240501,0x0,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501],
[0x0,0x0,0x804400110080402040081002080006002010e4,0x0,0x7b660f307983d39800f307a7307b69cc007a733cc03ccf300f708c03cfcc1f57bf00012fc00f6d3cbb6,0x212040240481,0x212040240481,0x212040240481,0x252042240481,0x222148240501,0x222148240501,0x222148240501,0x212040240481,0x242042240481,0x27214a240501,0x242042240481,0x202040240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6467 : TreeBound (n := 4) 106 (programCode 0x4c29075d76) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040001002000080008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6468 : TreeBound (n := 4) 106 (programCode 0x4c29075d77) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xfa98002046000fa9807980081180079f99e85f80f4e600f4e6000f4e9cc001f53000408c001e707485,0x0,0x240011002002080080404030100081002080ca3,0x240011002002080080404020100401020080ca3,0x440011002002080080404020100102004080ce3,0x440011002002080000004020100002000080ce3,0x2020000008080000020200000020800020001334080000080100000040100000000200010000800040000400080004000080002000100008000400010001000010001001487ffa7,0x440011002002080000004020100002000080ce3,0x8118002046000fa9807981e67980079f9865913cc1e63cc1e612fc1e601e60f307983cc3cc1e7032b5,0x0,0x240011002002080080404030100801020080ca3,0x1ed98007b66000fa98079801e7e60079f98000f3001e600007983cc1e9cc003db3000f30f301e64d995,0x240011002002080080404030100801040080ca3,0x1ed98007b66000fa98079801e7e60079f9800003cc1e600007983cc1e603cc3cc0f30f300001e64d995,0x0,0x0,0x0,0x0,0x8118002046000fa9807980025f80079f99e93420f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0x282061204481,0x0,0x282061204481,0x282040200481,0x282040208481,0x282040208481,0x282040208481,0x282042228481,0x0,0x102379803cde600f3798408c1e60f303cfcc00f300450e40099c6001e9cc3ce0460f307980f31e60f4dc6,0x0],
[0x282040208481,0x282042220481,0x0,0x282042220481,0x0,0x282042240481,0x440011002002080000004000108002200080ce3,0x282042240481,0x240011002002080080404090108001200080ca3,0x8118002046000fa9807981e67980079f9865913cc1e63cc1e603cc1e9cc001023000408c001e7032b5,0x0,0x7980799e60798f30081180025f80079f9a4bb05301e6003ea725d7ce9cc001023000408c001e7032b5,0x8084240022,0xf300f33cc03ccf300fa980044580079f99e600f301e6007b66f3f31e9cc001f530007d4c001e7056b5,0x8084240022,0x2121ce240501,0x2721ce240501,0x2121ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2421ce240501,0x2721ce240501,0x2421ce240501,0x2721ce240501,0xfa98003ea6000fa9807980f37980079f9904167981e61e61e607981e9cc001f530007d4c001e77d055,0x282042240481,0x0,0x20a148240501,0x8080240022],
[0x20a148240501,0x8080240022,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501,0x8118002046000fa9807981e67980079f9a4ba03001e63cc1e6f6cc1e9cc001023000408c001e7032b5,0x0,0x20a148240501,0x0,0x20a148240501,0x0,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501],
[0x240011002002080080004200108001200080ca3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6565 : TreeBound (n := 4) 106 (programCode 0x4c29075d78) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8000480012010080408004200108002200082ce3,0x8040080102010080408004200108002200082ce3,0x8000880022010080408004200108002200082de3,0x0,0x8040080012010080400084002108002200082ce3,0x0,0x8040080022010080400104004108002200082de3,0x0,0x209084240862,0x209882240c82,0x209084240862,0x209882240c82,0x209084240862,0x209084240862,0x209084240862,0x209084240862,0x209084240862,0x209888240c82,0x0,0x209888240c82,0x8001080042010080408004200108002200082ee3,0x8040080402010080408004200108002200082ce3,0x8002080082010080408004200108002200082ce3,0x8040080402010080408004200108002200082ce3,0x8004080102010080408004200108002200082ce3,0x8000080002010080408004200108002200082ce3,0x8008080202010080408004200108002200083ce3,0x8010080402010080408004200108002200082ce3,0x8010080402010080408004200108002200082ce3,0x4100104020080802080102002080402004824e4,0x8020080802010080408004200108002200086ce3],
[0x4200108040081002080202002080402008844e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6598 : TreeBound (n := 4) 106 (programCode 0x4c29075d79) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40a190240501,0x840020102004080508004200108002200082ce3,0x40a190240501,0x0,0x840020012004080500084002108002200082ce3,0x0,0x840020022004080500104004108002200082de3,0x0,0x409084240862,0x409882240c82,0x409084240862,0x409882240c82,0x409084240862,0x409084240862,0x409084240862,0x409084240862,0x409084240862,0x409088240862,0x0,0x409088240862,0x412190240501,0x840020502004080508004200108002200082ce3,0x412190240501,0x840020402004080508004200108002200082ce3,0x422190240501,0x462190240501,0x422190240501,0x462190240501,0x442190240501,0x462190240501,0x442190240501],
[0x462190240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6631 : TreeBound (n := 4) 106 (programCode 0x4c29075d7a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8040001002000080008004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6632 : TreeBound (n := 4) 106 (programCode 0x4c29075d7b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40a190240501,0x1040040102008080608004200108002200083ce3,0x40a190240501,0x0,0x1040040012008080600084002108002200083ce3,0x0,0x1040040022008080600104004108002200083de3,0x0,0x8084240022,0x609882240c82,0x8080240022,0x609882240c82,0x8084240022,0x8084240022,0x8080240022,0x8084240022,0x8080240022,0x8088240022,0x0,0x8088240022,0x412190240501,0x1040040602008080608004200108002200083ce3,0x412190240501,0x1040040402008080608004200108002200083ce3,0x422190240501,0x462190240501,0x422190240501,0x462190240501,0x442190240501,0x462190240501,0x442190240501],
[0x462190240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6665 : TreeBound (n := 4) 106 (programCode 0x4c29075d7c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x82010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6666 : TreeBound (n := 4) 106 (programCode 0x4c29075d7d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80a110240501,0x2040080102010080408004200108002200082ce3,0x80a110240501,0x0,0x2040080012010080400084002108002200082ce3,0x0,0x2040080022010080400104004108002200082de3,0x0,0x8084240022,0x609882240c82,0x8080240022,0x609882240c82,0x8084240022,0x8084240022,0x8080240022,0x8084240022,0x8080240022,0x8088240022,0x0,0x8088240022,0x812110240501,0x2040080402010080408004200108002200082ce3,0x812110240501,0x2040080402010080408004200108002200082ce3,0x822110240501,0x802110240501,0x822110240501,0x842110240501,0x842110240501,0x802110240501,0x842110240501],
[0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6699 : TreeBound (n := 4) 106 (programCode 0x4c29075d7e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf3007d97f0798f30081180081180079f99e60000f4e600f4e6000f4e9cc001f530007d4c001e707515,0x0,0x7980c2df2479cbf0081183d0458029cb9a2c7ac0f4e6007b66001e7e9cc0010230007d4c001e8eb1a5,0x0,0x8004180120030800c0204008108001200080ea3,0x800410012002080000004000108002200080ce3,0x8004180120030800c0204010108001200080ea3,0x800410012002080080404090108001200080ca3,0x2c80410012002080580804020108002200082ce3,0xf3007d8c8c798f30081180025f80079f99e600f301e6003ea6f3f31e9cc001f530007d4c001e703855,0x3c80410012002080681004040108002200083ce3,0x800410012002080080404010108001200080ca3,0x880490012012080482004080108001200082ca3,0x232e307a73001e6f300811801e7e60079f98464032e4e60f307980f31e9cc003db3000f6cc001e833995,0x880490012012080482004100108001200082ca3,0x800410012002080080004280108001200080ca3,0xf30811bcc204600003cde61e603cc0000798000f30079bcc00f3f3001e9cc003db3000f6cc001e68a925,0x0,0xf300f717f03ccf300fa980081180079f99e60000f4e600f4e6000f4e9cc001f530007d4c001e707515,0x0,0xf3008528583dc2300fa983d04580811f9a4342c0f4e6007b66001e7e9cc0010230007d4c001e8eb1a5,0x0,0x8004180220030800c0204008108001200080ea3,0x800810022002080000004000108002200080ce3,0x8004180220030800c0204010108001200080ea3,0x9004980220130804c2604098108001200082fa3,0x2d00810022002080580804020108002200082de3,0xf300852c243dc2300fa983d22b80811f9a4363fbdae600b82721b0ae9cc0010230007d4c001e8eb1a5,0x3d00810022002080681004040108002200083de3,0x8004180220030800c0604018108001200080ea3],
[0x9004980220130804c2004080108001200082fa3,0x1e6f300799e600fa9803cde600f379800000001e60f307981e61e9cc003db3000f6cc001e64d995,0xf3009458583dc2300fa98b647980811f9abcc4a601e6f301e63cc01e9cc0010230007d4c001ecb71a5,0x159fdab3fb0000567f6000000159fdab3fb00005694ffd80000567f6acfec0005be7560000567f759fd8000000567f60000567f759fd80acfec159fd8000159fed9fd80ad553f6000000acff167f600002b3fb567f600acff167f600002b3fb567f6002b40067f600002b4109fd800005684c7f60000015b577d800005684c7f60000015b577d8000015a53ff60000015a049bd9305834ab,0x0,0x1dcd650000f5e6147f161bdcd650000f5e5f4d4daca0007735943bd665059acaee6b36e6b283b9aca000f224d4a003b9e83b059aca00001dd11eaca077447ab28001dd11eaca01dd11eaca001dd11f23d594000f047fe5000eee25d94000f047fe5000eee25d94000ee6d0ce58cd19,0x0,0x0,0x0,0xee6b28001ebbd028001ddc4bb2800ef599328001ddc4bb28001dcd65ee88f56501dcf41d650077447ab28003bb8976500773770d650000000000ee6b2803b9aca001dcd65ee6b2803b9e83acc54135759400001dcd650000f5de817b9acbdcd650000f5de814000430e257d0e00a,0x200048002010400c20020d008348001200061ba4,0x0,0x200048002010401c20020d0103480012000e1fa4,0xf30811bcc204600003cde61e603cc00007980000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0x20008800201080002008000202080002000201e4,0x0,0xf307983cc1e600000001e61e603cc0000798000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x3cc00088b0007b66000f30f379bd1b99d39ed733cca73e832b3c02625fbcc0798f30a7415c079fd50f16,0x0,0x3cc0010230007b66000f30f3f4301b99cc06d733cc980f7628dca0c079bcc0798f3098115c0007d51426,0x2a01020042004080508004200108002200082ee3,0x20010800402080402080082002080402000412e4,0x2c02020082004080508004200108002200082ce3,0x20020800804080002080002002080402000804e4,0x22010240481,0x2010240481,0x22010240481,0x2010240481,0x842110240501,0x2010240481,0x842110240501],
[0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6764 : TreeBound (n := 4) 106 (programCode 0x4c29075d7f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80a110240501,0x0,0x832110204501,0x862110230501,0x832110204501,0x0,0x822110208501,0x0,0x822110208501,0x0,0x862110210501,0x862110230501,0x862110210501,0x822110220501,0x822110220501,0x862110230501,0x822110220501,0x822110220501,0x80a110240501,0x0,0x4000501002020080808004200100082002084ce3,0x7983cc1e603cc3cc79807987981e61e60798f30f3001e9cc007a73001e7e6003d39800f30f301ede5995,0x4000901002020080808004200100102004084de3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x4020101002020080808004200104002100084ce3,0x4020101002020080808004200102002080084ce3,0x0,0x4020101002020080808004200104002100084ce3,0x7983cc1e62d903cc79807987981e61e60798f30f3001e9cc007a73001e7e6003d39800f8b2001ede5995,0x812110240501,0x0,0x852101240501,0x0,0x852101240501,0x0,0x862102240501,0x842108240501,0x862102240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x812110240501,0x0,0x0,0x0,0x0,0x0,0x852102240501,0x842108240501,0x852102240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x822110240501,0x802110240501,0x822110240501,0x842110240501,0x842110240501,0x802110240501,0x842110240501,0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6845 : TreeBound (n := 4) 106 (programCode 0x4c29075d80) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10a030204481,0x2800420012004080508004200102c82020082ce3,0x10a030204481,0x0,0x0,0x400012000080008004200108002000080ce3,0x0,0x2000480012010080408004200108002080082ce3,0xc0a190210501,0x400012000080008004200100082000080ce3,0xc0a190210501,0xa010200481,0x80a110220501,0x0,0x80a110220501,0xa010200481,0x3cc00088b0007d4c00079800f3003cfcc00f3f3f3003cfcc0000f3003cfcc0000f307983cc0007985216,0x0,0x10a030204481,0x800022000080008004200100002020080ce3,0x10a030204481,0x0,0x0,0x0,0x0,0x0,0xc0a190210501,0x100804022000880028004200100102010080de3,0xc0a190210501,0xa010200481],
[0x80a110220501,0x800022000080008004200100002010080ce3,0x80a110220501,0xa010200481,0x0,0x0,0x0,0x0,0x0,0xf5e0a76d7829cc0f307b661ebb5cc0079f9800001e679803ccf300799e9cc003db3000f6cc001e68a925,0x40009000201080082002090082080012000613e4,0x0,0x40009000201080102004020102080022000a05e4,0x7980020460007d4c000f30f4e6003d39800f3f300000000000000f3079bcc0000f3000222c0007985756,0x40009000201080002008000202080002000201e4,0x0,0xf307983cc1e600000001e61e603cc0000798000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x7980020460007d4c000f30f4e679bd39ea5f3f33cc3cdf532f7db66079bcc0f30f30d4c22c000811d936,0x200000010800000041000000082000000100020100000080400600100801800801002000100008000c004500031011000006004000100010000c00040003001100004004200273668,0x7980020460007d4c000f30f4e679bd39db2f3f37983ce0462f7dd4c079bcc0f30f30b6622c000811d936,0x0,0x0,0x2801020042004080508004020108002200082ee3,0x0,0x0,0x212042240481,0x12000240481,0x212042240481,0x812108240501,0xc12184240501,0xe121ce240501],
[0xc12184240501,0x12000240481,0x812108240501,0xe121ce240501,0x812108240501,0x12000240481,0x40011000402080402080082002080402000412e4,0x0,0x0,0x0,0x0,0x0,0x212042240481,0x12000240481,0x212042240481,0x812108240501,0xc12184240501,0xe121ce240501,0xc12184240501,0x12000240481,0x812108240501,0xe121ce240501,0x812108240501,0x12000240481,0x40021000804080002080002002080402000804e4,0x822110240501,0x2010240481,0x822110240501,0x2010240481,0x42010240481,0x2010240481,0x42010240481],
[0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_5917 : TreeBound (n := 4) 106 (programCode 0x4c29075d) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part012_5918 part012_6031 part012_6064 part012_6193 part012_6354 part012_6467 part012_6468 part012_6565 part012_6598 part012_6631 part012_6632 part012_6665 part012_6666 part012_6699 part012_6764 part012_6845

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6943 : TreeBound (n := 4) 106 (programCode 0x4c29075e61) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10020802010a2,0x0,0x0,0x80002000020080802000000002001000044020e4,0x10220842110e2,0x10220842090e2,0x10020802210a2,0x10220842090e2,0x10220842110e2,0x10220842110e2,0x40000000300000000c0000000900000000c000200000020010040000000800208000000040200000100800001008000001008002000010002000010020000100020000100189713a7,0x10220842110e2,0x40000000300000000c0000000900000000c000200000020080040000000800208000000040200000100800001008000001008004000010010000010100000100100000100508713a7,0x10020802210a2,0x40000000300000000c0000000900000000c000200000020100040000000800208000000040200000100800001008000001008020000010020000010200000100200000100909713a7,0x10020802210a2,0x0,0x10020812010a2,0xf303cc3cc2d90f30b6407980f379803cc7980f3000f6cc012090000f6cc005b20003cc07984bf0799556,0x0,0x8000a000220080802000808022001008044221e4,0x10220812318e2,0x1022081209502,0x10020812210a2,0x1022081209502,0x10220812118e2,0x10220812118e2,0x80402000020080802000800022080100804020e4,0x10220812118e2,0x40000000300000000c0000000900000000c000200000020080040000000200208000000040200010000800000408000500008004000010010000010100000100100000100508713a7],
[0x10020812210a2,0x40000000300000000c0000000900000000c000200000020100040000000800208000000040200010000800001008000500008020000010020000010200000100200000100909713a7,0x10020812210a2,0x0,0x4000000110000000440000000300000000800820001000080004000000080020000400008100000040400000100200000200800002000400008002000004008000010010004a5ee27,0x40002400100008000400004001000090000800010001000010010000100010000100000164001000004000000650010000040000008000200019000000120000000110000800753a8,0x0,0x400000011000000044000000030000000080082000100008000400000008002000000000810000004040000010020000020080000100040000000200000000800004001000485ee27,0x0,0x0,0x0,0x400000011000000044000000030000000080082000100008000400000008002000000000810000004040000010020000020080000800040000000200000000800020001000485ee27,0x0,0x0,0x0,0x0,0x40000000300000000c0000000900000000c000200000020080040000001000208000000200200000200800002008000002008004000010010000010100000100100000100508713a7,0x0,0x40000000300000000c0000000900000000c000200000020400040000001000208000000200200000200800002008000002008020000010020000010200000100200000102108713a7,0x0,0x0,0x10020812010a2,0xf300003cc0f30f3000007980f379803cc7980f3001e9cc007980001e9cc003cc0003cc1e604bf0799556,0x0,0x8000a000220080802001008042001008044221e4,0x10220812318e2,0x1022081209502,0x10020812210a2,0x1022081209502,0x10220812118e2,0x10220812118e2,0x0],
[0x10220812118e2,0x0,0x10020812210a2,0x0,0x10020812210a2,0x80402000020080802010000402080102004020e4,0x80402002020080802002080082080012004030e4,0x0,0x108842240481,0x0,0x108842240481,0x0,0x2098c2240481,0x6098c2240481,0x2098c2240481,0x6098c2240481,0x408842240481,0x408842240481,0x408842240481,0x6098c2240481,0x0,0x6098c2240481,0x0,0x0,0x80402000020080802004000102080022004020e4,0x80402000020080802000000402080102004020e4,0x80402000020080802008000202080102004020e4,0x0,0x1088c4240481,0x0,0x1088c4240481,0x0],
[0x2098c4240481,0x6098c4240481,0x2098c4240481,0x6098c4240481,0x4098c4240481,0x6098c4240481,0x4098c4240481,0x6098c4240481,0x4000000210000000900000008100000008000600000020000080004100000208000020000200020000800200008000200008040000010100000010400000101000000100108713a7,0x6098c4240481,0x20000000220000000a00000008200000008000600000020000080010100000208000020000200020000800200008000200008040000010100000010400000101000000100108713a7,0x0,0x80402000020080802010000402080102004020e4,0x0,0xf30798f307980f30799e601e6f7bf005e35e04601e7e601e61e601e9cc001023000408c001e7032b5,0x9000000000000000840000000000000004040000000000000844000004000000041000000000000000800000000000000009000000000000000081000000008000000001000000800000000200000004000000001000000800000000040000040000000004000000800000000040000008000000000800000080000000008000220000021100000100000000001000000200000000008000008a000008440400042200000200000000080000000001400000400000000410000000000000000200002000000000000000080000000400000042000000000000000080000000440000042000000000000000280000000440000042000000000400000080000000080000000480000031790c9ac8d30,0xf307983cc7981e60799e601e67d4c003ee2fea601e7e601e61e601e9cc001023000408c001e7032b5,0x2400000110000000440000000290000000800820001000080000002420000020480020000100080000400040000200100000804000000410000002040000008100000010244a5ee27,0x2099c8240501,0x80400010410010002004080108002200080ce3,0x2099c8240501,0x400410010812010482004080108002200082ce3,0x40b9c8240501,0x554c400020001000081000000955310000d54c6aa6200100000d54c480000020aa98840000200100000801000008001000008040000010100000008400000101000000100108703a7,0x40b9c8240501,0x16c8001ed98001e60000b6cf5500000f3003cc0079807987980799e601e9cc003db3000f6cc001e64dcf5,0x798001ed980020460007a0f550001023003cfcc79807987980799e601e9cc003db3000f6cc001e833cf5,0x1f5301e6f6cc1e6f3008156e4a63dc2a983cfead9807987980799e601e9cc001f53000f6cc001e8337e5,0x80000008400000041000000022000000080082c0000048e0000000420000020300010000080080000400040000200100000804000000410000002040000008100000010184a5ae27,0x0,0x0,0x108842240481],
[0x12fc00111600012fc07980f379803cc7980f31e603cde60f301e603cfcc0002d90000b640f30799556,0x108842240481,0x1e60f3097e00025f8fa980f379803cc7980f31e603cde61e63ea603cfcc1e60f300012fc0f3079b3b6,0x2098c6240481,0x6098c6240481,0x2098c6240481,0x6098c6240481,0x408842240481,0x408842240481,0x408842240481,0x6098c6240481,0x0,0x6098c6240481,0x0,0x0,0x0,0xf30798f307980f3079bcc01e6f3f3003ee2e22c01e67981e63cc01e9cc001f53000408c001e7037c5,0x0,0xf307987987981e60799e603ccf4e6003f1fbea601e6f301e63cc01e9cc0010230007d4c001e7051a5,0x0,0x2099c8240501,0x6002000100004000400010000800000000c0223001000200002000804000002000002000010002000040008000080020000080400000101000000104000000410000001001097dda7,0x2099c8240501,0x410010810010482004100108001200082ca3,0x40b9c8240501,0x672a400100001000081000000800000000e72a7395200800000000002000002000002000010008000008004000080020000080400000101000000404000000210000001001087f0a7,0x40b9c8240501,0x6000000100000000090000000200000000c0223000000010000000008000002000002000010008000008010000020020000080400000101000000404000000810000001000487f227,0x1e600088b0003ea6000798e3d001f9ef003ee2c79801e7e600f33cc01e9cc003db3000f6cc001f0085c5,0x7a7301e702301e6f300981f9ae640c93983db4e9cc0799e60079bcc01e9cc001f53000f6cc001ede94a5,0x79800097e000408c0007986a5002082c003f99079801e7e600f33cc01e9cc003db3000f6cc001ee225c5,0x0],
[0x0,0x0,0xf300011160000f3007980f379803cc7980f33cc03ccf300003cc03cfcc0000f3000222c0f30799556,0x0,0x1e60f3097e00025f8fa980f379803cc7980f33cc03ccf31e6408c03cfcc1e60f300012fc0f3079b3b6,0x0,0x2400082020080802040081002080012004030e4,0x200410010806030180004200108001200080ca3,0x4400100020080802040001002080022004020e4,0x800420010402010080404210108001200080ca3,0x800400010000010000004210108001200080ca3,0x800440010000010000004210108001200080ca3,0x400010000010000004200108001200080ca3,0x798001ed980020460007a0f91c001023003cfcd8ae079879807a73001e9cc003db3000f6cc001e833cf5,0x800410010800010080004210108001200080ca3,0x8000000840000004100000002200000008008280000048a0000000480000020200040000080140000400100000201000000804000000410000002040000008100000010104a5ae27,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7120 : TreeBound (n := 4) 106 (programCode 0x4c29075e62) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf30811bcc2046f3003cfcc1e60f300000000000f30079bcc00f3f3001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7121 : TreeBound (n := 4) 106 (programCode 0x4c29075e63) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf3000222c00088b00012fc1e62dae60079fb661e60f4e6007a73000f4e6003cfcc01e6f3003cde68a5c5,0x0,0x0,0x4000000050000000240000000900000001001020011004080044000000100040000400010080000080400000040200000100800002000400009002000024008000090010004a5ae27,0x0,0x0,0x400000005000000024000000090000000100102004100408004c00000010004000108001008000008040000004020000010080000800040004000200010000800020001000485ae27,0x0,0x0,0x0,0x40000001100000001400000011000000014000200000080010040000000200808000000040200000100800001008000001008002000010002000010020000100020000100188713a7,0x0,0x0,0x0,0x0,0x0,0x0,0x400000005000000024000000090000000100102000100008000400000040004000100240010000020040000080020009000080000200040000800200000400800001001000485ee27,0xf30000b640002d9079881180f379803cc7980f3000f6cc011161e60f6cc005b21e63cc07984bf0799556,0x0,0xf300012fc0004bf0798fa980f379803cc7980f3000f6cc011163cc0f6cc0097e3cc1e60f3088b079b3b6,0x0,0xf30000b640002d9079881180f379803cc7980f3000f6cc011161e60f6cc02046f31e603cc1f530799556,0x0,0x0,0xf303cc3cc2d90f3079807980f379803cc7980f3000f6cc012090000f6cc1e7e616c803cc1e6f30799556,0x0,0x0,0xf303cc3cc0f30f3079807980f379803cc7980f3000f6cc012090000f6cc1e7e6007983cc1e6f30799556,0x0],
[0x0,0x0,0x0,0x0,0x4000000050000000240000000900000001001020001000080004000000080040000400008100000040400000100200000200800002000400008002000004008000010010004a5ee27,0x40000000b00008000c00000003000080000800010001000010010000100010000100000160003000104000000610010000040000008000200019000000120002000110000800753a8,0x0,0x40000001100000004400000009000000014000200110080800040000001000c00000000200800000802000001002000002008000000010000080040000200080000c001000487ba27,0x0,0x0,0x0,0x40000001100000004400000009000000014000200110080800040000001000c0000000020080000080200000100200000200800000001010080004000000008000c0001000487ba27,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000000050000000240000000900000001001020001000080004000000120040000480024100000090400000240200000900800002000400008002000004008000010010004a5ee27,0xf30000b640002d9079881180f379803cc7980f3001e9cc0097e1e61e9cc005b21e63cc1e604bf0799556,0x0,0xf3000222c00088b0001303b660f300000079800000079800007980001e600003cc0000f300001e64dcf5,0xf3000222c00088b0001303b660f300000079800000079800007980001e607983cc0798f301e61e64dcf5,0xf300012fc0004bf0798fa980f379803cc7980f3001e9cc0097e3cc1e9cc02049cc1e60f301f5308331b6,0xf3000222c00088b0001303b660f300000079800000079800007980001e607983cc1e60f303cc1e64dcf5,0x400000005000000024000000090000000100102000100008000400000000004000000000010000000040000000020000000080001000040000000200000000800040001000485ee27,0x0,0x0,0x0],
[0xf303cc3cc0f30f3079807980f379803cc7980f3001e9cc00a710001e9cc1e7e6007983cc1e6f30799556,0x0,0x0,0x0,0x0,0x0,0x108842240481,0x4200000110c0000044000000080400000140302018100800020001000080004000000020010000040020000100080000100080400000101000000404000000810000001001187faa7,0x108842240481,0xfd51da80003f547c36830dcd65ee6b292a05f200003b9ad9047fe5077360b35941dcd82cd650ee6b639aca07735cf9aca1dcd65000ee6c97f202803838fc2f000773597b9aca03b9bb86b2f73d0759400001dcd6647d4c414157b9acbdcd651dcd6c73594773597b9cdafff9a,0x2098c2240481,0x6098c2240481,0x2098c2240481,0x6098c2240481,0x408842240481,0x408842240481,0x408842240481,0x6098c2240481,0x0,0x6098c2240481,0x0,0x0,0xf3000408c1e60f3079bd3980f379803cc7980f30079bcc07b66f3079bcfcc1e7023000408c0f3081a6d6,0x0,0x108842240481,0x0,0x108842240481,0x0,0x2098c2240481,0x6098c2240481,0x2098c2240481,0x6098c2240481],
[0x408842240481,0x408842240481,0x408842240481,0x6098c2240481,0x0,0x6098c2240481,0x0,0x0,0x400000005000000024000000090000000100102000100008000400000000004000000010010000000040000000020000400080400000041000000204000000810000001000485ee27,0x0,0x1088c4240481,0x0,0x1088c4240481,0x0,0x2098c4240481,0x6098c4240481,0x2098c4240481,0x6098c4240481,0x4098c4240481,0x6098c4240481,0x4098c4240481,0x6098c4240481,0x0,0x6098c4240481,0x0,0x0,0x0,0x1088c6240481,0xf3079911600016c881180f379803cc7980f303cc3cc3cde61e9cc3cfcc1e60f300f33cc0f30799556,0x1088c6240481,0x422000011088000044000000080400000142202110100800000000000000004000004220010000000020001000080000000080400000101000000404000000810000001001087faa7,0x2098c6240481],
[0x6098c6240481,0x2098c6240481,0x6098c6240481,0x4098c6240481,0x6098c6240481,0x4098c6240481,0x6098c6240481,0x0,0x6098c6240481,0x0,0x0,0x0,0x1088c4240481,0x0,0x1088c4240481,0x0,0x2098c4240481,0x6098c4240481,0x2098c4240481,0x6098c4240481,0x4098c4240481,0x6098c4240481,0x4098c4240481,0x6098c4240481,0x0,0x6098c4240481,0x0,0x0,0x0,0x108800240481,0xf3079911600016c881180f379803cc7980f307983cc1e7e61ed983cfcc1e60f303cc3cc0f30799556,0x108800240481],
[0x1e60f3097e00025f8fa980f379803cc7980f307983cc1e7e63d3983cfcc1e60f303cc3cc0f3079b3b6,0x2098c6240481,0x8800240481,0x2098c6240481,0x6098c6240481,0x408800240481,0x408800240481,0x408800240481,0x8800240481,0x0,0x6098c6240481,0x0,0x0,0x0,0xf30798f301e60f30f33cc01e6f7bf005df9204601e7e601e61e601e9cc001023000408c001e7032b5,0x0,0xf307987983cc1e60f33cc01e6f6cc003f99204601e7e601e61e601e9cc0010230007d4c001e703345,0x0,0x2099c8240501,0x100800020410010002004080108002200080ce3,0x2099c8240501,0x400810020812010482004080108002200082de3,0x40b9c8240501,0x776e800100002000400400000200000001776ebbb7400a00000000002000001000002000010004000020010000080010000080400000101000000404000000210000001001087f8a7,0x40b9c8240501,0x600000010000000041000000080000000140223000000880000000008000004000002000010004000020010000080010000080400000101000000404000000810000001001087faa7,0x0,0x0,0x0,0x0,0x0,0x108842240481],
[0x0,0x108842240481,0x0,0x2098c6240481,0x6098c6240481,0x2098c6240481,0x6098c6240481,0x408842240481,0x408842240481,0x408842240481,0x6098c6240481,0x0,0x6098c6240481,0x0,0x0,0x0,0xf30f30f301e60f30f33cc097ef5d9005d42e22c01e67981e63cc01e9cc001f53000408c001e707485,0x0,0xf307987983cc1e60f33cc03ccf4e6003f1fbea601e6f301e63cc01e9cc0010230007d4c001e7051a5,0x0,0x2099c8240501,0x6802800100002000100008000400000001402ab40140020000100080400000200000200001000200004000800008002000008040000010100000010400000041000000100108fdda7,0x2099c8240501,0x418020830018cc2004100108001200086fa3,0x40b9c8240501,0x1001000004004000008000800010000000000000400000201000000c0000020000020080000080100000200200000804000001010000004040000008100000010004873227,0x40b9c8240501,0x0,0x0,0x7,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400810020802010000004200108002200080ce3,0x0,0x800820020402010080404200108002200080ce3,0x800820020402010080404200108002200080ce3,0x1000840020000010000004200108002200080ce3,0x800020000010000004200108002200080ce3,0x0,0xc00810020c02010080404200108002200080ce3,0x0,0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7362 : TreeBound (n := 4) 106 (programCode 0x4c29075e64) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80006000220040802000008043200000044021a4,0x0,0x0,0x8000a000220080802001008042001008044221e4,0x100a0852b18e2,0x100a085289502,0x100a0812a10a2,0x100a085289502,0x80006000220040802019008043201008644221a4,0x100a0852918e2,0x0,0x100a0852918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0xf300012fc0004bf0000fa980f379803cc7980f3000f6cc00f303cc0f6cde61e60f303cc1e60f3079b3b6,0x100a0812918e2,0xf300012fc0004bf0000fa980f379803cc7980f3000f6cc00f303cc0f6cc001e60f300000000f3079b3b6],
[0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x40000000900000004c0000001300000002001820001000080004000000080060000400008100000040400000100200000200800002000400008002000004008000010010004a5ee27,0xf3000222c00088b000102301e61e607987980f3000f32d903eaabf0fa98007981e616c96c8445a231906,0x0,0xf3000222c00088b000102301e61e607987980f3003cc2d90f4eabf3d39800f307984459e60811fd51906,0x0,0x0,0x0,0x400020011000000044000000110000000640002001100808000400000010008000000002008000008020000010020000020080000000101008000400000000800080001000487ba27,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0x0],
[0x100a0812918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x0,0x0,0x220100000800200000a010000020020422021101080001300088004c0020000000020010000020010000100080000100080400000101000000404000000410000001001987f5a7,0x0,0x904800f8b99879f980111600f379807987980f39048b738b9983d39879bcc2d90f304827cc0f30907fa6,0x1e600f37980798798111600f379807987980f3922eb738b9983d39879bcc2d90f30491acc0f309265a6,0x0,0x8,0x20020100020000200100201000100002042802140108000100008000400020000000020010000020010000100080000100080400000101000000404000000410000001001887f5a7,0xf3000f6cc0079bcc0111600f379807987980f39048b738b9983d39879bcc2d90f30445bcc0f30907fa6,0x798001116000811800111600f379807987980f39048b738b9983d39879bcc2d90f303cc3cc0f3079b7a6,0x79800f6cc0079f980111600f379807987980f39048b738b9983d39879bcc2d90f30408fcc0f30907fa6,0x2000201002000002010002010010000020422021101080001300090004c0020000000020010000020010000100080000100080400000101000000404000000410000001001987f5a7,0x7980011160007b6600111600f379807987980f39048b738b9983d39879bcc2d90f303cc3cc0f3079b7a6,0x0,0x9,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0xf30000b640004bf0000fa98079f9803cc7980f3004c2cfcc3cc62bcc2db303cc97e44587984bf9f7cd06,0x0,0x0,0x1dcd65000eee25d94000f047fe5000eee25d94000f047fe5000ee6b9f394dacbdcd65ee6b280773597b9ca6d6500ee6b45cda0d664ca07735cf9aca7736826b2807735cf9aca7735cf9aca07735cf9aca0ee6b36e6b639acaee6b28ee6b36e6b36e6b36e6b28ee6b36e6d0c6e573d9,0x40000000300000001400000009000000010800002008000010008000080010000100002000801a0b00002682c00406808002020008001000080d0580008341600010404021a045e68,0x0,0x0],
[0x0,0x0,0x0,0xf30000b640004bf0000fa98079f9803cc7980f307983d1b2000633183db3f30f307a36401e7023812846,0x0,0x0,0x0,0x0,0xf3000222c00088b000102301e63cc07987980f301e601e6799e9ccf379bcc003db3098d6cc07983eff36,0xf30811bcc2046f3003cfcc1e60f3000000000000f307981e60f303cc1e9cc003db3000f6cc001e68a925,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x306de5a71295de822e6b2f735940000f5de8140001dcd653b9acc18711a0ee6b9f3594077394daca0ee6b639aca1dcd68b9aca1dd06bde5aacc3bf993287771a5ff940773d075a2e6b2faef40a1dcddc359a0dbcd2af9a2a05f973597b9acbdcd6500000773594ee6b2f7360a721ea,0x4200210010c0084004000200000400020040002000100000000000000000000000000200010000800020001000080002000080400000101000000404000000810000001001087faa7,0x221000000801000000a10000002010042202110108800110008800440022000000200010000800010000800080002000080400000101000000404000000410000001001887f5a7,0x420021001080084004000200000400020040002000100000000000000000000000000200010000800020001000080002000080400000101000000404000000810000001001087faa7,0x798000f4ed983d39800fa980f379803cc7980f379803ce04600445803cfcc1e60f303cc3cc0f3079b3b6,0x7980f379803cc7980fa980f379803cc7980f379803cc01e60445803cfcc1e60f303d008c0f3081c536,0x0,0xf300f33cc03ccf300fa980f379803cc7980f379803cc03cc0445803cfcc1e60f30007d4c0f307aa6b6,0x79800f307983d39800fa980f379803cc7980f379803cc1e600445803cfcc1e60f30408fcc0f30814bb6,0x3cc00f6cc003cfcc00fa980f379803cc7980f379803cc0f300445803cfcc1e60f301119cc0f30a377b6,0x3cc0010230007d4c00102300f33cc07987980f33cc001f5302e4a0c079bcc0798f3097e3cc07983d1426,0x79800f6cc0079f980102300f33cc07987980f30f3001fae22e4a0c079bcc097ef309f7bcc079853dc26,0xf300003cc0000fa980f379803cc7980f379803cc00000445803cfcc1e60f300003cc0f3079b3b6,0x1e60011160003ea6000fa980f379803cc7980f379803cc79800445803cfcc1e60f300f33cc0f309813b6,0x0,0x7980020460007d4c00102301e63cc07987980f3798001f5301ea08c079bcc0f30f30d4a3cc0798b69936,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0],
[0x0,0x1e60f307983cc1e60fa980f379803cc7980f300003cc000003cc003cfcc1e60f300003cc0f3079b3b6,0x203000000202000001030000001020006300319018000219010c008640400000002000010002000010010000080010000080400000101000000404000000410000001011c87f5a7,0x7980f379803cc7980fa980f379803cc7980f379f9bcc1e600445f9bcfcc1e60f303d008c0f3081c536,0x600000005c0000002000000010800000012000004004000020010000100010000100000001009c0060302400080004000004004000300010000e000400000001000040002000deba8,0x0,0x79800f307983d39800fa980f379803cc7980f381183ce0460044d183cfcc1e60f30408fcc0f30814bb6,0x79801e7e60079bcc0102301e63cc07987980f30f3001f7161eb035879bcc088bf309bafcc079853e136,0x0,0xf3001e9cc0079f980102301e63cc07987980f30f3001f8fc1eb0af079bcc097ef309f7bcc07984c4936,0xf300003cc0000fa980f379803cc7980f300003cc000003cc003cfcc1e60f300003cc0f3079b3b6,0x0,0x0,0x0,0x0,0x0,0xf30f30f303cc0f30fa980f379803cc7980f31e603cde60003ea603cfcc1e60f30000b640f3079b3b6,0x0,0x1e60f30f307981e6102300f33cc07987980f33cc001f5302e4826079bcc00088b098115c07983d1426,0x79800f307983d39800fa980f379803cc7980f31e603cde60003ea603cfcc1e60f3003cfcc0f30814bb6,0x7980f379803cc7980fa980f379803cc7980f31e603cde60003ea603cfcc1e60f3000408c0f3081c536,0x2021000008084000020200000020020042002100108000000010000000000000004200010010800020001000080000000080400000101000000404000001010000001001087fba7,0xf300f37980798f30102300f33cc07987980f33cc001f5302e4826079bcc003db3099504c07983efa26,0x79800f307983d39800fa980f379803cc7980f31e603cde60003ea603cfcc1e60f3003cfcc0f30814bb6,0x79800f4e60079bcc0102300f33cc07987980f33cc001f5302e4826079bcc00f3f309d95cc079853dc26,0x3cc0010230007d4c00102300f33cc07987980f33cc001f5302e4826079bcc0798f3097e3cc07983d1426,0x79800f6cc0079f980102300f33cc07987980f33cc001f5302e4826079bcc01e6f30a347cc079853dc26,0xf300003cc0000fa980f379803cc7980f31e603cde60003ea603cfcc1e60f300003cc0f3079b3b6,0x3cc0010230007b6600102300f33cc07987980f33cc001f5302e4826079bcc0798f30a713cc07983d1426,0x0,0x7980020460007d4c00102301e63cc07987980f33cc001f5301e9ea6079bcc0f30f3097e3cc0798b69936,0x0],
[0x1dcd653b9ad173594000059682f3b9ad173594000059682f3b9aca001e08ffcbdcd662a05f2001dcd65059682f00000ee6b332d06230e23403b9ca6d650ee6b9f359403b9ca6d6503b9ae7cd6503b9aca0077394daca1dcd73e6b28077394daca07736826b2807736826d0c7a47e19,0xf3000222c00088b0000fa981e61e607987980f3f300012fc0003cc0fa98005b20000f30798408e0498f6,0x0,0x0,0x0,0xf3000222c00088b0000fa981e61e607987980f3f300012fc0003cc79f98020460007983cc1e9db5e4276,0x0,0x0,0xf3000222c00088b0000fa981e61e607987980f3f300012fc0003cc1ed980097e0001e60f6cc3cfea98f6,0xf3000222c00088b0000fa981e61e607987980f3f300012fc0003cfcc7980f4e6003ccf300f3445b92cf6,0x0,0xf3000222c00088b0000fa981e61e607987980f3f300012fc0003db307983cde600f30f301e65b22dc8f6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3cc1e60f307981e6102301e63cc07987980f379800204601ea08c079bcc00088b098022c07983d1936,0x3cc235cb307a7300102301e63cc07987980f379800204601ea08c079bcc00088b09f9a2c07983d1936,0x7980f379803cc7980fa980f379803cc7980f33cc03ccf3000408c03cfcc1e60f3000f6cc0f308331b6,0x13ef0007d4c00102300f33cc07987980f33cc00204602e4a0c079bcc0000f3097e3cc07983d1426,0x1e601e67980798f30102301e63cc07987980f379800204601ea08c079bcc003db3098d6cc07983eff36,0x3cc0f8c8c87a7300102300f33cc07987980f33cc00204602e4a0c079bcc00088b0a3755c07983d1426,0x79800f4e60079bcc0102300f33cc07987980f33cc00204602e4a0c079bcc00f3f309bafcc079853dc26,0x3cc0010230007d4c00102300f33cc07987980f33cc00204602e4a0c079bcc0798f3097e3cc07983d1426,0x79800f6cc0079f980102300f33cc07987980f33cc00204602e4a0c079bcc00f3f309f7bcc079853dc26,0xf300003cc0000fa980f379803cc7980f33cc03ccf3000408c03cfcc1e60f300003cc0f3079b3b6,0x3cc0010230007b6600102300f33cc07987980f33cc00204602e4a0c079bcc0798f3097e3cc07983d1426,0x0],
[0x3cc0011160007d4c00102300f33cc07987980f33cc00204602e4a0c079bcc0798f30d4a3cc07983d1426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7555 : TreeBound (n := 4) 106 (programCode 0x4c29075e65) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80402002020080802080082002080402004030e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7556 : TreeBound (n := 4) 106 (programCode 0x4c29075e66) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x800220004400808020800b200208060200805704]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7557 : TreeBound (n := 4) 106 (programCode 0x4c29075e67) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x0,0x0,0x0,0x1118c2240481,0x1118c6240481,0x1118c2240481,0x1118c6240481,0x1118c4240481,0x1118c6240481,0x1118c4240481,0x1118c6240481,0xf37980f31e600f379bcc1e7e6f74583ce0461e601e7e601e61e601e9cc001f530007d4c001e703855,0x1118c6240481,0xf37980f31e600f379bcc1ed98f55f83ce0463cc01e6f301e63cc01e9cc001f530007d4c001e707515,0x0,0x0,0x611090204481,0x411090210481,0x611090204481,0x0,0x411090208481,0x1694acbb253a1a3c29875e3e39cb48efe4a809a949a41d1846e26a56a3c24981447c73da3c23e39c00000b4784930288f8e7b4d321d45a6a510000168f09ae9b1a4a8242d2541216913528800b5b41a44d773e11f49fe11f336f08f9413c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169074611b89a946d23bf92a026a5269071e9768e70168f09532323e39d69071e9768e7002d1e11f1ce000002d1e29eb32e0443b1f0d,0x411090208481,0x1694acbb253a1a3c29875e3e39cb48efe4a809a949a41c7a5da39c05a3c24981447c73da3c29875e3e39cb4784930288f8e7b4d29a7a2494e70000168f09ae9b1a4a8242d2541216913528800b4a565d92c9fe11f49fe11f336f08f9413c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c4480ec94e868f0a61d78f8e72d23bf92a026a5269071e9768e70168f09260511f1cf69071e9768e7002d1e124c0a23e39ed1e29eb32e0443b1f0d,0x411090210481,0x411090210481,0x411090210481,0x411090210481,0x611090220481],
[0x411090210481,0x611090220481,0x0,0x0,0x0,0x0,0x0,0x0,0x1118c2240481,0x1118c6240481,0x1118c2240481,0x1118c6240481,0x1118c4240481,0x1118c6240481,0x1118c4240481,0x1118c6240481,0x1e67980799e601e679bcc1e9ccf74583ce0461e601e7e601e61e601e9cc001f530007d4c001e7056b5,0x1118c6240481,0x1e67980799e601e679bcc1e9ccf55f83ce0463cc01e6f301e63cc01e9cc001f530007d4c001e7056b5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x168f08f8e7005a41c7a5da39c0169073aca341e211a41c7a5da39c05a3d8cd42b8e7005a3c23e39c00000b48ed6d030e7000b4d29a7a2494e70000168f09ad5f47cce2cef134dea7883c41800b47847c73ad1e11f49fe135abe8f8e75a3c23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c0169071e9768e7005a41ceb28d0788469071e9768e70168f09532323e39d69071e9768e7002d1e11f1ce000002d1e29eb32e1519ece1d,0x0,0x0,0x4340001010000004001000002101000010434021a0001000200400000200040080004000010010000040040000080100000080020000100080000400100000200100001001087fca7,0x15a084fec000059e30de63fb0164cd6c000000567f602b3fb00b7ceac0000000c29e980567f6000acfed59fd8002b3fbacfec000acfed59fd8002b3fb159fd800567f6159fd8005680b9fd8000acff167f60363ade799ad8000000b266b60002b3fc59fd80567f60567f6000159fd8159fd80acfec0567f963ade64263fbacfec000567f600002b4006800cfec00005680b9fd80ae58bfeeca2fac,0x0],
[0x159fd800002b4529de5ee00acfec159fd8002b962f600000acfec000000015a53ff600000159fd95a084fec0579de619cef2f700000acfec000acfec002b4109fd800159fd80159fd80000159fd8000acff167f60002b3fc59fd800159fdd67f60002b3fc59fd80002b40067f600002b4109fd800002b4529de5ee00ad145fd8000002b3fb567f600acfeeb3fb000159fd80000000159fdeccea55c9fab,0x0,0x0,0x4000001010000004000000002100000010420021a0001000200400000200040080004000010010000040040000080100000080200000100800000400400000202000001001087fca7,0x0,0x211090240481,0x0,0x611081240481,0x168f08f8e7005a41d1846e26a5269074611b89a949a41d1846e26a56a3c254c8c8f8e72d1e1795903e39cb47847c73800000b4d321d45a6a510000168f09ae9b1a4a8242d254121691352880000b47847ca09e11f49fe11f1ce000005a3c23e3f63c23e39c01694acbb25ee3847ccdbc23e450785e672c3fa1da5e1795903e39d68f08f99b7847ca09e1795903e39c2d1e11f336f08f9141e6c2df1e39c0169071e9768e7005a41c7a5da39c0169071e9768e70168f63350ae39c00b48ed6d030e7002d23b5b40c39c002d1e29eb32e1519e380d,0x611081240481,0x0,0x411082240481,0x411084240481,0x411082240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x611088240481,0x411084240481,0x611088240481,0x411084240481,0x211090240481,0x0,0x0,0x0,0x0,0x0,0x611082240481,0x411084240481,0x611082240481],
[0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411088240481,0x411084240481,0x411088240481,0x411084240481,0x411090240481,0x411090240481,0x411090240481,0x411090240481,0x0,0x0,0x0,0x0,0x0,0x8118c2240481,0x8118c6240481,0x8118c2240481,0x8118c6240481,0x8118c4240481,0x8118c6240481,0x8118c4240481,0x8118c6240481,0x8119c8240501,0x8118c6240481,0x8119c8240501,0x8119c8240501,0x411090240481,0x0],
[0x0,0x0,0x0,0x0,0x8118c2240481,0x8118c6240481,0x8118c2240481,0x8118c6240481,0x8118c4240481,0x8118c6240481,0x8118c4240481,0x8118c6240481,0x8119c8240501,0x8118c6240481,0x8119c8240501,0x8119c8240501,0x0,0x0,0x0,0x0,0x0,0x211082240481,0x411084240481,0x211082240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x8119c8240501,0x411084240481,0x8119c8240501],
[0x11080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7718 : TreeBound (n := 4) 106 (programCode 0x4c29075e68) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x800220008400808020800a200208060200805504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7719 : TreeBound (n := 4) 106 (programCode 0x4c29075e69) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002020080802080082002080402004030e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7720 : TreeBound (n := 4) 106 (programCode 0x4c29075e6a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80042001020080802080042002080402004038e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7721 : TreeBound (n := 4) 106 (programCode 0x4c29075e6b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0xf30079bcc01e6f3003cfcc1e60f300000000000f30079bcc00f3f3001e9cc003db3000f6cc001e68a925]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7722 : TreeBound (n := 4) 106 (programCode 0x4c29075e6c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002020080802080082002080402004030e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7723 : TreeBound (n := 4) 106 (programCode 0x4c29075e6d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x408c000408c0010231f1826798f3008118002d90079bcc007a73001e600f33cc00f3f3003cde64dcf5,0x21000000010800000108000000108002028339521000020000080000210000a00c000010010000008040000080100000080672a4010008000010672a401000400001001087d3a7,0x0,0x0,0x2100000008400000010800000010800202020110800000080008000021000000040000100100000400400000801000000800020001000080004000100010000100010014c7ffa7,0x408c000408c0010231f1826798f3008118000f30079bcc007a73001e9ccf33db3000f300001e64dcf5,0x4200000010800000108000000108000008200001000001000080000210008000400000201000000804000008010000008000200010000200010002000100002000100108713a7,0x408c000408c0010231f191f2b8f30081183ced90079bcc007a73001ebbd643db3000f379801e833cf5,0x408c000408c0010231f193d8b8f3008118448590079bcc007a73001e63cc03cc3cc0f30f301e833cf5,0x408c00081180010231edd435a7b3008118000f30079bcc00f3f3001ed86ad7cdf530f300001e68a925,0x4200000010800000108000000108000008200001000010000080000210008010400000201000000804000008010000008002000010002000010020000100020000100188713a7,0x408c000408c0010231f1826798f3008118000f30079bcc007a73001e9ccf33cc00f3f300001e64dcf5,0x408c000408c0010231f1919798f30081183ced90079bcc007a73001e7e6003cde600f379801e833cf5,0x408c000408c0010231f191f2b8f30081183ced90079bcc007a73001e7f1643cc0f30f379801e833cf5,0x408c000408c0010231f1919798f300811879ad90079bcc007a73001e7e6003d39800f3f3001ebffcf5,0x408c000408c0010231f182697ef3008118002d90079bcc007a73001e6012ffcc00f3f3003cde64dcf5,0x900020020080802080002002080402004020e4,0x0,0x408c000f6cc001f531edb66799e600fa98002d90079bcc007a73001e600f33cc00f3f3003cde64dcf5,0x210000000820000002080000002080020203111040000000002000004100000004000010010000020040000080100000080622200100080000400000001000400001001087fba7,0x0,0x0,0x0,0x0,0x0,0x0,0x20200000020800000208000000208000020200001000020000200000410008a01400000201000000804000008010000008000400010001000010010000100010000100108713a7,0x20200000020800000208000000208000020200001000080000200000410008801400000201000000804000008010000008000400010000800010040000101108000100508713a7,0x0,0x0],
[0x2020000002080000020800000020800002020000100020000020000041000a001400000201000000804000008010000008004000010010000010100000100100000101508713a7,0x0,0x2020000002080000020800000020800002020000100040000020000041000c004400000201000000804000008010000008020000010020000010200000100200000102508713a7,0x408c000f6cc001f531edb66799e600fa98000f30079bcc007a73001e600f33cc0000f300799e64dcf5,0x0,0x0,0x0,0x0,0x0,0x1100040020080802010000402080102004020e4,0x1010042020080802002080082080012004030e4,0x0,0x1020040020080802004000102080022004020e4,0x1100040020080802000000402080102004020e4,0x1100040020080802008000202080102004020e4,0x0,0x1100040020080802010000402080102004020e4,0x1000040020080802000000002080002004020e4,0x1e60f307983cc1e60fa980f379803cc7980f31e603cde60003ea603cfcc1e60f300012fc0f3079b3b6,0x0,0x1e60f307983cc1e60fa980f379803cc7980f33cc03ccf3000408c03cfcc1e60f300012fc0f3079b3b6,0x0,0x40200000100800001008000001008000040020201100080080400002010008008800040200000100800001008000001008040000008100000040400000081000000100508632a7,0x210008400811080548004020108002200082ee3,0x4200210010800040002000100008000000200001000200004000800008001000010042002100100000400420001000080002004000300010000c000400010001000010000a007f668,0x0,0x2431c2240501,0x2431ce240501,0x2431c2240501,0x2431ce240501,0x2431c4240501,0x2431ce240501],
[0x2431c4240501,0x2431ce240501,0x2431c8240501,0x2431cc240501,0x2431c8240501,0x2431c2240501,0x2080082020080802080082002080402004030e4,0x0,0xf3f3003db3000f3f307980260730fa9f99e67980f4e600f4e6000f4e9cc001f530007d4c001e707515,0x0,0xf3f3003db3000f3f307980223b30fa9f99e63cc1e7e6007b66001e7e9cc001f530007d4c001e7056b5,0x0,0x2431c2240501,0x2431ce240501,0x2431c2240501,0x2431ce240501,0x2431c4240501,0x2431ce240501,0x2431c4240501,0x2431ce240501,0x2431c8240501,0x2431cc240501,0x2431c8240501,0x2431c2240501,0x4000100020080802080002002080402004020e4,0x443190240501,0x842110240501,0x443190240501,0x42010240481,0x842110240501,0x842110240501,0x842110240501],
[0x42010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7820 : TreeBound (n := 4) 106 (programCode 0x4c29075e6e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8020200404008080208038200208060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7821 : TreeBound (n := 4) 106 (programCode 0x4c29075e6f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x12fc00088b000111600b826260730097e1e62d9001e9cc00f3f3001e6003cfcc01e6f3003cde68a5c5,0x0,0x0,0x0,0x0,0x0,0x5000000011000000110000000110000008200008000001000080000280008000400000201000000804000008010000008000200010000200010002000100002000100108713a7,0x12fc00088b000111600b82626076cc97e2d92d9001e9cc00f3f3001e9cc003e2d730f4e6001ee225c5,0x0,0x0,0x5000000011000000110000000110000008200008000010000080000280008010400000201000000804000008010000008002000010002000010020000100020000100188713a7,0x0,0x12fc00088b000111600b82626073f397e222ed9001e9cc00f3f3001e679803cfcc00f379801f3d45c5,0x12fc00088b000111600b82626076cc97e2d92d9001e9cc00f3f3001e60b643d3a730f4e6001ee225c5,0x10400000082000000048000000110001000240004020800480180001040001000c000008010000040040000020100000080080000040400000201000000802000001018485ae27,0x1040000008200000004800000011000100020010402080040018000104000000440000080100000400400000201000000800002000400009002000024008000090010004a5ae27,0x0,0x0,0xc43190230501,0x0,0x0,0x443190208501,0x0,0x443190208501,0x0,0xc43190210501,0xc43190230501,0xc43190210501,0xc43190230501,0xc43190220501],
[0xc43190230501,0xc43190220501,0xc43190230501,0x0,0x840000004200000010800000021000100020000004080000010000084000000440000100100000400400000201000000800002000400008002000004008000010010004a5ee27,0x400340003000d800680006001b000d0000200000800400002001000010001000010040002081b00008206c000000010000040000022801a0004a0068001200000001400020006eba8,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2100000002100000021000000021000002020000800008000020000108000a001400000201000000804000008010000008004000010010000010100000100100000102d08713a7,0x0,0x2100000002100000021000000021000002020000800040000020000108000c004400000201000000804000008010000008020000010020000010200000100200000102108713a7,0x210000000840000001080000002100000202001080808000001000010c0000000400000801000002004000002010000008000000010000080040000000080000c001000487ba27,0x0,0x40000400000092000000248001000010001000200000020800040000001240000004c0000100100000400400000201000000800002000400008002000004008000010010004a5ee27,0x1004040120080802080006002000c00024120e4,0x0,0x0,0x0,0x0,0x0,0x0,0x1000040020080802080002002000400404020e4,0x0,0x0],
[0x222c0007a73002269ba980f379803cc7980f3f3003cfcc1027bf003cc1e7026d39f9801e6f30799556,0x0,0x0,0x1000040020080802080002002000400004020e4,0x0,0x0,0x408000001040000010080000010100000401802081006000804000020c0008008800040200000100800001008000001008040000008100000040400000081000000103108632a7,0x220008800821100948004020108002200084ee3,0xee7a0eb280ee7a0eb28003ba9b0b2803ba9b0b28003ba9b0b45cd65007735b940f9dacbdcd650000773d07595dcf41d68b9aca00003ba9b0b2803ba9b0b28003b9e83aca03b9e83aca003b9e8423d594000f047fe5000eee25d94000f047fe5000eee25d94000ee74d96dc3619,0x0,0x2431c2240501,0x2431ce240501,0x2431c2240501,0x2431ce240501,0x2431c4240501,0x2431ce240501,0x2431c4240501,0x2431ce240501,0x2431c8240501,0x2431cc240501,0x2431c8240501,0x2431c2240501,0x0,0x80400000241000000810001002410000100240082000001241080404080008012000040200000100800001008000001008040000004100000010400000101000000100109513a7,0x0,0x6b2a9000000224000000804000000010006b2ab59542000001101000404020000000000201000000804000000808000002008040000010100000040400000041000000100108ffda7,0x0,0xc43182240501,0x42000240481,0xc43182240501,0x842108240501,0x42004240481],
[0x842108240501,0x42004240481,0x42000240481,0x842108240501,0x842108240501,0x842108240501,0x42000240481,0x0,0xf4e6003d39800f4e60f300260731eda731e67980f4e600f4e6000f4e9cc001f530007d4c001e707515,0x0,0xf4e6003d39800f4e60f300223b31eda731e63cc1e7e6007b66001e7e9cc001f530007d4c001e7056b5,0x0,0x2431c2240501,0x2431ce240501,0x2431c2240501,0x2431ce240501,0x2431c4240501,0x2431ce240501,0x2431c4240501,0x2431ce240501,0x2431c8240501,0x2431cc240501,0x2431c8240501,0x2431c2240501,0x0,0x0,0x0,0x0,0x0,0xe439c2240501,0x842108240501,0xe439c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x443190240501,0x842110240501,0x443190240501,0x42010240481,0x842110240501,0x842110240501,0x842110240501,0x42010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7966 : TreeBound (n := 4) 106 (programCode 0x4c29075e70) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8020200804008080208028200208060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_6942 : TreeBound (n := 4) 106 (programCode 0x4c29075e) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part012_6943 part012_7120 part012_7121 part012_7362 part012_7555 part012_7556 part012_7557 part012_7718 part012_7719 part012_7720 part012_7721 part012_7722 part012_7723 part012_7820 part012_7821 part012_7966

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7968 : TreeBound (n := 4) 106 (programCode 0x4c29075f71) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x182030204481,0x16c800111600016c807981e63cc001f530dcdf1001e9cc01e6f3001e63cc01092d4779cbf01e703345,0x182030204481,0x0,0x182021204481,0xc0003004000500000004020100002000080ce3,0x182021204481,0x182020200481,0x182062208481,0xc0003004000500000004000100002000080ce3,0x182062208481,0xc0003004000500010084100100082002080ce3,0x16c800111600016c807981e63cc001f530dcd01cc1e63cc1e603cc1e63cc00f9e67f7a45701e703345,0x0,0x16c800111600016c80f300f31e6001f530cda05981e60f31e607981e61e601ec6cff3e5b3fde780c85,0x182021204481,0x0,0xc0003004000500080404200100402010080ce3,0x0,0xc0003004000500000004200100002000080ce3,0x0,0x182061208481,0x0,0x182061208481,0x182060208481,0x182062208481,0xc0003004000500040a04008100202008080ee3,0x182062208481,0xa00000008800000012000000018000080004000200000400400000082000104a880000400200004000c250080020850080000800040008000100010000200010001001a955ca7,0x0,0x0],
[0x0,0x182063208481,0xa0000000880000001200000001800004000400020000040040000008200008088800004008000040010000080010000080000800020008000100010000200010001001a945ca7,0x0,0xa00000008800000012000000018000080004000200000400400000082000104a8800004002000040004000080020000080000800040008000100010000200010001001a955ca7,0x0,0xc0003004000500008004200108002000080ce3,0x16c800111600016c80f3001e7e6001f531e8139001e9cc01e6f3001e603cc1e607983cc3cc1e7037c5,0x0,0x80402014000500818004200108002100084ce3,0x16c80003cc0000f4e7e600025f800088b079ad9001e9cc007a73001e9cc003db3000f3f3001ea19995,0x80802024000500818004200108002100084de3,0x16c80003cc1e616c81e600025f800088b079ad9001e9cc007a73001e9cc003db3000f3f3001ea19995,0x81002044000500818004200108002100084ee3,0x0,0x82002084000500818004200108002100084ce3,0x0,0x84002104000500818004200108002100084ce3,0x80002084000500818004200108002100084ce3,0x88002204000500818004200108002100085ce3,0x80402814000500818004200108002100084ce3,0x90002404000500818004200108002100086ce3,0x82002994000500818004200108002100084ce3,0xa0002804000500818004200108002100084ce3,0xa0002814000500818004200108002100084ce3,0x0,0x10a1b0210501,0x16a1b0210501,0x10a1b0210501,0xa0003802000500918004200100801020084ca3,0x1121b0210501,0x0],
[0x1121b0210501,0x0,0x1221b0210501,0x17a1b0210501,0x1221b0210501,0x16a1b0210501,0x1421b0210501,0x17a1b0210501,0x1421b0210501,0x16a1b0210501,0x16c800111600016c80f3001e7e6001f532806d1001e9cc01e6f3001e603cc1f5300040cc8c1e7037c5,0x16c800111600016c80f300f31e6001f5304c1d9001e9cc01e6f3001e61e601e63cc03cde601e780c85,0x182030204481,0x0,0x10a130220501,0x122130220501,0x10a130220501,0x0,0x112130220501,0xc0002414000500418004200102002080082ce3,0x112130220501,0x0,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501,0x0,0xf30798f307980f3088b001e7e6001f531e8139001e9cc01e6f3001e603cc1e60f303cc3cc1e7037c5],
[0x84002104000500008004200100402000080ce3,0xf30798f301e60f30fa9801e7e6001f531e9069001e9cc01e6f3001e603cc0f30f303cc5b21e7032b5,0x0,0x81002044000500918004200100402020084ee3,0x0,0x82002084000500918004200100402020084ce3,0x0,0x84002104000500008004200100402000080ce3,0xf33cc0f300001a46ab180001e6001f532c5b81001e9cc01e6f3001e600000f30f30424b51de7032b5,0x88002204000500018004200100402002080ce3,0xf37980f30798193186b001e7e6001f532806d1001e9cc01e6f3001e603cc1e60f3040cd7f1e7037c5,0x90002404000500418004200100402080082ce3,0xfa9800f31e601a46ab181e61e6001f532c5b81001e9cc01e6f3001e63cc00f30f30424b51de7032b5,0xa0002804000500818004200100402100084ce3,0x80002004000500008004200100402000080ce3,0x0,0x10a130220501,0x122130220501,0x10a130220501,0x80403012000500818004200102001100084ca3,0x112130220501,0x0,0x112130220501,0x0,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501],
[0x0,0x10a030200481,0x122130220501,0x10a030200481,0x0,0x0,0x0,0x0,0x0,0x122130220501,0xf33cc0f3000016cf9f980001e6001f531e62d9001e9cc01e6f3001e600001023000408c001e7032b5,0x122130220501,0x10a030200481,0x142030204481,0x0,0x142030204481,0x102030200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8113 : TreeBound (n := 4) 106 (programCode 0x4c29075f72) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x440021004002100010084002100082002080ce3,0x440021004002100080404020100082002080ce3,0x440021004002100030104004100082002080de3,0x440021004002100010084002100082002080ce3,0x440021004002100040204008100082002080ee3,0x440021004002100000004000100082002080ce3,0x440021004002100080404010100082002080ce3,0x440021004002100080404100100082002080ce3,0x3d398003ea6014701807981e61e6007a730df113cc1e63cc1e603cc1e6003ccf303cc3cc03cde7032b5,0x0,0xf3798003ea600f37980f300f33cc007a7308a967981e61e61e607981e6003cde603cc79803cde77d055,0x440021004002100080404010100082002080ce3,0x0,0xfa98003ea6003d3981e6001ed98007a73000003cc1e600007a73001e6003cfcc00f3f3003cde64d995,0x0,0x0,0x40021004000100008004200100002020080ce3,0x0,0x440021004002100030084002100102004080de3,0x440021004002100080404020100102004080ce3,0x440021004002100020104004100102004080de3,0x440021004002100020104004100102004080de3,0x440021004002100040204008100102004080ee3,0x440021004002100000004000100102004080ce3,0x440021004002100080404010100102004080ce3,0x440021004002100080404100100102004080ce3,0xf3798003ea6013f69807981e63cc007a730de1e3cc1e63cc1e603cc1e6003ccf301e67980799e703345,0x0,0xf3798003ea6013f69807980f33cc007a730ed4e3cc1e61e61e607981e6003ccf301e67980799e77cb45,0x440021004002100080404010100102004080ce3],
[0x0,0xf3798003ea600f37980f301e63cc007a73099d53001e63cc1e6f3001e600799e601e67980799e703855,0x0,0x1ed98007b66003d3981e6003d39800f3f3000000001e6f3007a73001e600f33cc03ccf300799e64d995,0x0,0x440021004002100010084002100082002080ce3,0x40021004000100000004020100002000080ce3,0x440021004002100020104004100002004080de3,0x40021004000100000004000100002000080ce3,0x0,0x40021004000100000004000100002000080ce3,0x0,0x40021004000100000004100100002000080ce3,0x620020000080080000000200000400800020003100080000000200000000200000000200010000400020001000080001000080620000100080000402000001000400001001087fba7,0x0,0x0,0x40021004000100000004000100002000080ce3,0x0,0x40021004000100000004200100002000080ce3,0x0,0x0,0x0,0x40a190208501,0x422190208501,0x40a190208501,0x0,0x412190208501,0x0,0x412190208501,0x0,0x422190208501,0x462190208501],
[0x422190208501,0x462190208501,0x442190208501,0x462190208501,0x442190208501,0x462190208501,0x17bb7980001e601303981e62f767980000f30000f30079bcc007a73001ebeec03db3000f300001e64dcf5,0x0,0x40a190208501,0x422190208501,0x40a190208501,0x0,0x412190208501,0x0,0x412190208501,0x0,0x422190208501,0x462190208501,0x422190208501,0x462190208501,0x442190208501,0x462190208501,0x442190208501,0x462190208501,0x0,0x1026cc1e603cc1f8fc0097e2f7e11800088b079ad90079bcc007a73001ebb2003db3000f3f3001ea19cf5,0x804020104080102080002002004400100804e4,0x0,0x808020204080102080002002004400100804e4,0x0,0x0,0x0],
[0x0,0x800022004080102080002002004400100804e4,0x840021004080002080002002004400100804e4,0x0,0x880022004080102080002002004400100804e4,0x0,0x102300102300010230003db300f33cc003db3f3003cfcc001f53003cc03ea6000fa98003cc1e610856,0x0,0x1116000fa98001116000f3f300f33cc00f3f3f3003cfcc0000f3003cc03cc0000fa98003cc1e610856,0x40021004000100008004200100802020080ce3,0x17bb7980001e601303981e62f767980000f30000f30079bcc007a73001ebeec03db3000f300001e64dcf5,0x40021004000100008004200101002040080ce3,0x40021004000100008004200100002000080ce3,0x0,0x50a1b0220501,0x422190220501,0x50a1b0220501,0x0,0x0,0x40020004000100008004200102002080080ce3,0x0,0x0,0x422190220501,0xc62190220501,0x422190220501,0xc62190220501,0xc42190220501,0xc62190220501,0xc42190220501,0xc62190220501,0x0,0x1bf60f1e6f3001f8fc0097e37ec97801e6f30812730079bcc007a73001ecfd83fe7f60ff303cc1ea19cf5],
[0xc62190230501,0xf3000f6d3983db300102307b69cc07a82328011f001e9cc01e6f3001e603cc1e9db307983cc1ead16b5,0x0,0x1020044000100008004200100002020080ce3,0xf33cc0f33cc00f3408c00f31e603cfcc00f3f3003cfcc1e7023003cc799e6079879807983cc2686d6,0x2020084000100008004200100002020080ce3,0x0,0xc22190230501,0xc62190230501,0xc22190230501,0xc62190230501,0xc42190230501,0xc62190230501,0xc42190230501,0xc62190230501,0x0,0x50a1b0220501,0x422190220501,0x50a1b0220501,0x21004000100008004200104002100080ce3,0x0,0x0,0x0,0x0,0x422190220501,0xc62190220501,0x422190220501,0xc62190220501,0xc42190220501,0xc62190220501,0xc42190220501,0xc62190220501],
[0x0,0x50a1b0220501,0x422190220501,0x50a1b0220501,0x0,0x0,0xf33cc0f33cc00f3408c00f33cc03cfcc00f3f3003cfcc1e9db3003ccf31e603cc7980f30798465356,0x0,0x620030000080040000000200000400100020003100080000000200000000200000004000010010000020040000080100000080620000101880000402000001000000001001087fba7,0x422190220501,0xc62190230501,0x422190220501,0xc62190230501,0xc42190230501,0xc62190230501,0xc42190230501,0xc62190230501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8290 : TreeBound (n := 4) 106 (programCode 0x4c29075f73) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x182030204481,0x140005004000900008004200100002020080ce3,0x182030204481,0x0,0x182021204481,0x140005004000900000004020100002000080ce3,0x182021204481,0x182020200481,0x182062208481,0x140005004000900000004000100002000080ce3,0x182062208481,0x140005004000900000104100100002004080ce3,0x445800111600025f81e60008118001f5300079bcc1e60f307983cc1e600f33cfcc00f30f301e66fc55,0x0,0x445800111600025f81e60008118001f530007a7301e63cc07987981e600f33d39800f33cc01e66fc55,0x182021204481,0x140005004000900022004080100102080080de3,0x140005004000900080404200100402010080ce3,0x140005004000900024004100100102100080de3,0x140005004000900000004200100002000080ce3,0x0,0x182061208481,0x60000000180000000a0000000280000400008001000002008000000420000a2100400020004000400024000800050000800004000200080000800100004000100010031840da7,0x182061208481,0x182060208481,0x182062208481,0x140005004000900040a04008100202008080ee3,0x182062208481,0x0,0x60000000180000000a0000000280000400010001000002008000000420000c2100400020008000400010000800010000800004000200080000800100004000100010031840da7,0x60000000180000000a0000000280000400000401000002008000000420008031020000200002004004000008010c2000800004000200080000800100004000100010031840da7],
[0x60000000280000000a0000000280000400004002000002008000000420001121004000200020004000080008000200008000040002000800010001000040001000100398c1da7,0x182063208481,0x0,0x0,0x0,0x0,0x0,0x18206120c481,0x140005004000900000004020100002000080ce3,0x18206120c481,0xc0005002000500020004000100001004080fa3,0x0,0x140005004000900000004000100002000080ce3,0x16c800097e00025f807981e63cc00102305b5cc799e603cde600f31e63cc00f3f3007a45e99e703345,0xa0000000280000001200000002800008002424820000001100000008200000120800010000020040000010020020000080484900040002000104040000800024001000495de27,0x182024204481,0x0,0x182024204481,0x445800111600025f81e60008118001f530044583cde600f3798222de607983cc5b20f3088b1e66fc55,0x0,0x22000000018000000220000000280002000000101000020020000001020008a01002000801000000800020008010020008001000010004000008410000101140200100108783a7,0x0,0x0,0x16c80005b200025f8079801e7e600088b1e73ef001e9cc01e6f3001e601e60f307983cc3cc1e7032b5,0x0,0x0,0x0,0x140005004000900000104004100002100080ce3,0x140005004000900000104004100002100080ce3,0x140005004000900040204008100202100080ee3,0x140005004000900000004000100002100080ce3,0x140005004000900080404010100402100080ce3],
[0x140005004000900020104100100102100080de3,0x0,0x0,0x0,0x140005004000900000104000100002100080ce3,0x140005004000900022004080100102100080de3,0x445800111600025f81e60008118001f53003cc1e61e607987a73001e607983db3000f3f3001e66bf95,0x140005004000900024004100100102100080de3,0x0,0x16c800097e00025f807981e63cc00102305b6bf001e9cc01e6f3001e60f300f3f300798f301e703345,0x0,0x1e607987987981e6088b0007d4c0010231e7f53001e9cc01e6f3001e603cc1e603cc7d8c8c1e707515,0x3cc0000f379801e7e7e60008118001f530000f3001e9cc007a73001e600003cc3cc0f307981e64d995,0x100804024000900028004200100102010080de3,0x1023000f6cc007a73000f6cc0f402307983cc0f3f3084e7cc00f3f3007983ce0460f379800f31e616e146,0x0,0x0,0xf33cc0799e601e679f9801e9cc0010231e831f001e9cc01e6f3001e603cc0f30f307d8c8c1e703345,0x0,0x104004104000900928004200100802134084de3,0x100004084000900008004200100002010080ce3,0x108004204000900a28004200101002054085de3,0x100804024000900028004200100102010080de3,0x110004404000900428004200102002090082de3,0xfa9800799e601ee11f9801e9cc0010231e831f001e9cc01e6f3001e603cc0f30f307d8c8c1e703345,0x120004804000900828004200104002110084de3,0x100004004000900008004200100002010080ce3,0x16c80005b200025f807980f31e600088b0cd725001e9cc01e6f3001e60f300f33cc03cde601e77cab5,0x182030204481,0x0,0x10a130220501,0x122130220501],
[0x10a130220501,0x0,0x112130220501,0x140004424000900428004200102002080082de3,0x112130220501,0x0,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501,0x16c800097e00025f8079801e9cc0010231e831f001e9cc01e6f3001e9cc000f30f307d4fcc1e703345,0x0,0x10a130220501,0x122130220501,0x10a130220501,0x100805004000900828004200104002100084de3,0x112130220501,0x0,0x112130220501,0x0,0x122130220501,0x112130220501,0x122130220501,0x14a130220501,0x142130220501,0x17a130220501,0x142130220501,0x14a130220501],
[0x140005004000900008004200100002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8419 : TreeBound (n := 4) 106 (programCode 0x4c29075f74) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xc0201004000500018004200100082002080ce3,0x0,0x400000009290000040800000030000000088002400040009480100004000200010004000008010000040040000020100000080020000041212100204800000800900001008485ae27,0x4020200104020100808004200104002020084ce3,0xa,0x4020201004020100808004200104002020084ce3,0x4000000812000004008000002100000008080024000400090001000040002000100040000080100000400400000201000000800200000412110002048000008009000010084c5ae27,0x0,0x0,0x0,0x4004200104020100808004200104802020084ce3,0x4000200004020100808004200104002020084ce3,0x4008200204020100808004200105002020085ce3,0x4020200804020100808004200104002020084ce3,0x40000800120004000080002001000008000800240004000900010000400020001000400000801000004004000002010000008002000004131000020480000080090000100c485ae27,0x0,0x4020200804020100808004200104002020084ce3,0x0,0x140201004000900028004200100102004080de3,0x0,0x182021204481,0x40001004000100000004020100002000080ce3,0x182021204481,0x82000200481,0x282042208481,0x82000200481,0x282042208481,0x40001004000100000004100100002000080ce3,0x0,0x0,0x7981e61e600f37981e600007983cc0f300000f301e63cc07987981e600003d39800f33cc01e64d995],
[0x82000200481,0x0,0x40001004000100000004200100002000080ce3,0x40101004000100004004100100002100080ce3,0x40001004000100000004200100002000080ce3,0x0,0x182061208481,0x0,0x182061208481,0x82000208481,0x282042208481,0x82000208481,0x282042208481,0x0,0x0,0x40201004000100008004000100202008080ce3,0x0,0x82000208481,0x0,0x0,0x0,0x0,0xf307980001e60f307981e61e607980000f30000f30079bcc007a73001e9cc003db3000f300001e64dcf5,0x0,0x182061208481,0x0,0x182061208481,0x82000208481,0x282042208481,0x82000208481,0x282042208481,0x40001004000100000004100100402010080ce3],
[0x0,0x0,0x0,0x82000208481,0x0,0x40001004000100000004200100402010080ce3,0x0,0x40001004000100000004200100402010080ce3,0xf307980001e60f307981e61e607980000f30000f30079bcc007a73001ebb2003db3000f3f3001e64dcf5,0x0,0x4000600014020100808004200100802020084ce3,0x4020200104020100808004200100802020084ce3,0x4000a00024020100808004200100802020084de3,0x4020201004020100808004200100802020084ce3,0x4001200044020100808004200100802020084ee3,0x0,0x4002200084020100808004200100802020084ce3,0x0,0x4004200104020100808004200100802020084ce3,0x4000200004020100808004200100802020084ce3,0x4008200204020100808004200100802020085ce3,0x4020200804020100808004200100802020084ce3,0x4010200404020100808004200100802020086ce3,0x0,0x4020200804020100808004200100802020084ce3,0x0,0xf307980001e60f307981e61e607980000f30000f30079bcc007a73001e9cc003db3000f300001e64dcf5,0x0,0x4000600014020100808004200101002040084ce3,0x4020200104020100808004200101002040084ce3,0x4000a00024020100808004200101002040084de3,0x4020201004020100808004200101002040084ce3],
[0x4001200044020100808004200101002040084ee3,0x0,0x4002200084020100808004200101002040084ce3,0x0,0x4004200104020100808004200101002040084ce3,0x4000200004020100808004200101002040084ce3,0x4008200204020100808004200101002040085ce3,0x4020200804020100808004200101002040084ce3,0x4010200404020100808004200101002040086ce3,0x7980001e61e60f307981e60f307983cc0f30f30f3001e9cc007a73001e63cc03ccf300f31e601ede5995,0x4020200804020100808004200101002040084ce3,0x7983cc1e61e60f30b641e60f307983cc0f30f30f3001e9cc007a73001e63cc03ccf300f31e601ede5995,0x40201004000100008004200100002000080ce3,0x0,0x0,0x0,0x0,0x82000220481,0x282042220481,0x82000220481,0x282042220481,0x40001004000100000004100102002080080ce3,0x0,0x0,0x0,0x82000220481,0x0,0x40001004000100000004200102002080080ce3,0x0,0x40001004000100000004200102002080080ce3,0x0,0x0],
[0x1004040120080802080006002020400804020e4,0x0,0x0,0x16c800f3f30010230003ea62d907981e60f30798f30079bcc007a73001ea123e3db3000f30f301ea21675,0x1e63cc079bcc01e6408c00f379803cfcc00f3f3003cfcc1e7023003cc799e607987980798f3081a6d6,0x0,0x0,0x1080042020080802080082002020400804030e4,0x1040041020080002080042002020400804038e4,0x222c00088b3cc222c1e67a7379803cc007a73f3003cfcc2d90f3003cc799e644587980798f30799556,0x1080042020080802080082002020400804030e4,0x0,0x2046000fa98001f530f300f33cfd398007a73f3097e3cc28d98b00798f31e603cc97fed987983cd766,0x0,0x204600102300020460f300f33d1b99800f3f3f30d4d15c3069f300798f31e603cc980e098798b65766,0x40201004000100008004200104002100080ce3,0x0,0xf30001e600002d9000088b1e607980000f30000f30079bcc007a73001e600001f53000f300001e64d7e5,0x1004040140081002080006002040401008040e4,0x0,0x0,0x0,0x1e63cc079bcc01e6408c00f33cc03cfcc00f3f3003cfcc1e9db3003ccf31e603cc7980f30798465356,0x0,0x400030001000040000000200010000100020002000080000000200000000200000004000010010000020040000080100000080400000101000000404000001000000001001087fba7,0x1000042040081002080002002040401008040e4,0x1040041040080002080042002040401008058e4,0x0,0x1080042040081002080082002040401008050e4,0x0,0x2046000fa98001f530f300f379bd398007a73f3097e3cc380d5700798f31e60798d4ce8307983cd766,0x408c0010237981e601e601e679bd3980000f3f30b643cc01e6f300799e61e60798b65f530f30799c76],
[0x204600102300020460f300f379db99800f3f3f30d4d15c3069f300798f31e60798d4ce830798b65766]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8580 : TreeBound (n := 4) 106 (programCode 0x4c29075f75) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8118007b660008118079800204600f3f31e71160f4e600f4e6000f4e9cc001023000408c001e7032b5,0x8118007b66000811807981e63cc00f3f32c6f7f301e9cc01e705fc1e9cc0010230007d4c001e703345,0x8118007b660008118079800204600f3f31e72fc0f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0x282061204481,0x102000000108000001020000001080002000000802000000020000008020000000000000800000000800800008002000008000000010004000010000000100040000100108793a7,0x282061204481,0x282040200481,0x282040208481,0x282040208481,0x282040208481,0x282042228481,0x0,0x0,0x0,0x282040208481,0x282042220481,0x0,0x282042220481,0x0,0x282042240481,0x240009002001100040804008108001200080ea3,0x282042240481,0x0,0x20a14a240501,0x0,0x20a14a240501,0x0,0x21214a240501,0x27214a240501,0x21214a240501],
[0x25214a240501,0x22214a240501,0x22214a240501,0x22214a240501,0x25214a240501,0x24214a240501,0x27214a240501,0x24214a240501,0x25214a240501,0x0,0x20a1c4240501,0x0,0x20a1c4240501,0x0,0x2121c4240501,0x2721c4240501,0x2121c4240501,0x2421c4240501,0x2221c4240501,0x2721c4240501,0x2221c4240501,0x2721c4240501,0x2421c4240501,0x2721c4240501,0x2421c4240501,0x2721c4240501,0x0,0x798079f980798798088b0079bcc00f3f3084e43cc1e600f4e642aede9cc001f530007d4c001eb2e715,0x0,0x7980f379803cc79810230079bcc00f3f3084e43cc1e6007b6642907e9cc001f530007d4c001eb2c8b5,0x0,0x2121ce240501],
[0x2721ce240501,0x2121ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2421ce240501,0x2721ce240501,0x2421ce240501,0x2721ce240501,0x0,0x20a1c4240501,0x0,0x20a1c4240501,0x0,0x2121c4240501,0x2721c4240501,0x2121c4240501,0x2421c4240501,0x2221c4240501,0x2721c4240501,0x2221c4240501,0x2721c4240501,0x2421c4240501,0x2721c4240501,0x2421c4240501,0x2721c4240501,0x282042240481,0x0,0x20a148240501,0x240008104001100442004080108002200082ee3],
[0x20a148240501,0x240008404001100442004080108002200082ee3,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501,0x0,0x20a1c6240501,0x0,0x20a1c6240501,0x0,0x2121c4240501,0x2721ce240501,0x2121c4240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2421cc240501,0x2721ce240501,0x2421cc240501,0x2721ce240501,0x0],
[0x20a148240501,0x0,0x20a148240501,0x0,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501,0x0,0x0,0x0,0x0,0x0,0x212040240481,0x212040240481,0x212040240481,0x252042240481,0x222148240501,0x222148240501,0x222148240501,0x212040240481,0x242042240481,0x27214a240501,0x242042240481],
[0x202040240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8741 : TreeBound (n := 4) 106 (programCode 0x4c29075f76) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x4458003ea60f437580f30007b66007a731e85f80f4e600f4e6000f4e9cc001f53000408c001e707485,0xf307980001e600007981e61e607980000f30001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x25f8003ea60f418f8079800408c007a731e822c0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0x382061204481,0x0,0x382061204481,0x82000200481,0x82000208481,0x82000200481,0x82000208481,0x82000220481,0x0,0xfa98003ea60008118000f3f3f35b99bcc00f30026379911439001ed981e60f3079fd799f3007af1c26,0x0,0x82000200481,0x82000220481,0x0,0x82000220481,0x0,0x0,0xc0a182240501,0x0,0xc0a182240501,0x0,0xc12182240501,0xc62182240501,0xc12182240501,0xc52182240501,0xc22182240501,0xc62182240501],
[0xc22182240501,0xc62182240501,0xc42182240501,0xc62182240501,0xc42182240501,0xc62182240501,0x82000240481,0x0,0xc0a182240501,0x0,0xc0a182240501,0x0,0xc12182240501,0xc62182240501,0xc12182240501,0xc52182240501,0xc22182240501,0xc62182240501,0xc22182240501,0xc62182240501,0xc42182240501,0xc62182240501,0xc42182240501,0xc62182240501,0x0,0x0,0x0,0x0,0x0,0xe121ce240501,0x2008240481,0xe121ce240501],
[0x842108240501,0xc2218c240501,0x2008240481,0xc2218c240501,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x82004240481,0xf307980001e600007981e61e607980000f30000f30079bcc007980001e9cc003db3000f6cc001e64dcf5,0x82004240481,0x82000240481,0x0,0x0,0x0,0x0,0x2040000404010100002004080108002200080ce3,0xa12148240501,0x2008240481,0xa12148240501,0x842108240501,0xc22188240501,0x2008240481,0xc22188240501,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x0,0x1bf60f1e6f3002268c0097e37ec97801e6f308133f61699026d3980f31e9cc003db3000f6cc001ea19cf5],
[0xf30811800204600003cde61e607980000f30000f30079bcc00f300001e9cc003db3000f6cc001e68a925,0x6b6a400102100000400400000200000001200035b5280001080040000200200000006b6a4100000a0020000000080000100080400000101000000404000000210000001009487f8a7,0x7980f379803cc79812fc00f31e603cfcc00f31e603cde61e63ea603cfcc1e60f3000408c03cc26a536,0x12004240481,0x2000240481,0x12004240481,0x842108240501,0x22000240481,0x2000240481,0x22000240481,0x2000240481,0x842108240501,0x2000240481,0x842108240501,0x2000240481,0x0,0x0,0x0,0x0,0x0,0xa12148240501,0x2008240481,0xa12148240501,0x842108240501,0xc22188240501,0x2008240481,0xc22188240501,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481],
[0x0,0x0,0x0,0x0,0x7980f379803cc79812fc00f33cc03cfcc00f33cc03ccf31e6408c03cfcc1e60f3000f6cc07984671b6,0x12000240481,0x2000240481,0x12000240481,0x42000240481,0xc2218c240501,0x2000240481,0xc2218c240501,0x2000240481,0x42000240481,0x2000240481,0x42000240481,0x2000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8886 : TreeBound (n := 4) 106 (programCode 0x4c29075f77) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x8118002046000fa980798002046003db31e85f80f4e600f4e6000f4e9cc001023000408c001e7032b5,0x0,0x440011004002100080404020100082002080ce3,0x440011004002100000004020100002020080ce3,0x440011004002100080404020100102004080ce3,0x440011004002100000004020100002000080ce3,0x0,0x440011004002100000004020100002000080ce3,0x8118003ea6000fa9807981e63cc007a7305d06f301e63cc1e612fc1e601e60f30f307983cc1e703345,0x0,0x440011004002100000004020100802020080ce3,0x0,0x440011004002100080404020101002040080ce3,0x1020000002080000008200000020800010000484020000210080000040200000000300010010420040001080080004000080090800080042000100008000400000001001086dda7,0x0,0x1ed98007b66000fa981e6003d39800f3f3000000001e9cc007983cc1e60f303cc3cc0f6cc001e64d995,0x0,0x0,0x8118003ea6000fa98079800408c007a731e822c0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0x282061204481,0x1ed98007b66000fa981e6003d39800f3f3000000001e6f30079bcc01e600003cc0000f30f301e64d995,0x282061204481,0x282040200481,0x282040208481,0x282040208481,0x282040208481,0x282042228481,0x0,0x0,0x0],
[0x282040208481,0x282042220481,0x0,0x282042220481,0x0,0x282042240481,0x440011004002100000004000108002200080ce3,0x282042240481,0x440011004002100080404100108002200080ce3,0x8118003ea6000fa9807981e63cc007a7305d063cc1e63cc1e603cc1e9cc0010230007d4c001e703345,0x0,0xf30079bcc0798f30088b0007d4c007a731e600f301e600f4e6f3f31e9cc001f530007d4c001e707515,0x0,0x798079bcc03ccf300fa9800408c007a731e823b301e6007b6703417e9cc0010230007d4c001e7051a5,0x0,0x2121ce240501,0x2721ce240501,0x2121ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2221ce240501,0x2721ce240501,0x2421ce240501,0x2721ce240501,0x2421ce240501,0x2721ce240501,0x8118003ea6000fa9807980f33cc007a7308a963cc1e61e61e607981e9cc0010230007d4c001e77cb45,0x282042240481,0x0,0x20a148240501,0x440010104002100482004080108002200082ce3],
[0x20a148240501,0x440010404002100482004080108002200082ce3,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501,0x8118003ea6000fa9807981e63cc007a7305d153001e63cc1e6f6cc1e9cc0010230007d4c001e703345,0x0,0x20a148240501,0x0,0x20a148240501,0x0,0x212148240501,0x252148240501,0x212148240501,0x252148240501,0x222148240501,0x222148240501,0x222148240501,0x252148240501,0x242148240501,0x272148240501,0x242148240501,0x252148240501],
[0x440011004002100000004200108002200080ce3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_8983 : TreeBound (n := 4) 106 (programCode 0x4c29075f78) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xc0101004000500010084002100082002080ce3,0x0,0x140101004000900020084002100102004080de3,0xc0101004000500010084002100082002080ce3,0x240101004001100050084002100202008080ee3,0x40101004000100000084002100402000080ce3,0x440101004002100090084002100402010080ce3,0x0,0x0,0x40101004000100000084002108002000080ce3,0x0,0x40101004000100000084002100002000080ce3,0x0,0x0,0x0,0x0,0x0,0x80000009600000040800000022000000088002c0004000b000100004000200010000200008010100040040000020009000080400000041000000204000000810000001008485ae27,0x0,0x0,0x0,0x80000081600000400800000202000000808002c0004000b0001000040002000100002000080101000400400000200090000804000000410000002040000008100000010084c5ae27,0x0,0x0,0xf307983cc1e60f307980f3f3003cfcc00f3f3000f6cc00f300000f6cfcc0000f307983cc0007985216,0xf33cc03cc0000f33cc0000f3003cfcc00f3f3000f6cc00f300000f6cfcc0000f307983cc0007985216,0xf31e603cde600f31e60000f3003cfcc0000f3000f6cc00f300000f6cfcc0000f307983cc0007985216,0x0,0xf33cc03ccf300f33cc00f3f3003cfcc00f3f3000f6cc00f300000f6cfcc0000f307983cc0007985216,0xf300003cc0000f30000000f3003cfcc0000f3000f6cc00f300000f6cfcc0000f307983cc0007985216],
[0xf3f3003db3000f3f3003ccf3003cfcc03ccf3000f6cc00f300000f6cfcc0000f307983cc0007985216,0x80004001600020000800080002000100008002c0004000b000100004000200010000200008010100040040000020009000080400000041000000204000000810000001018485ae27,0xf4e6003d39800f4e6003ccf3003cfcc03ccf3000f6cc00f300000f6cfcc0000f307983cc0007985216,0x0,0xc0101004000500010104004100082002080ce3,0x40101004000100000104004100002020080ce3,0x140101004000900020104004100102004080de3,0x40101004000100000104004100002004080ce3,0x240101004001100060104004100202008080fe3,0x4401010040021000a0104004100402014080de3,0x4401010040021000a0104004100402010080de3,0x40101004000100000104004100002100080ce3,0x0,0x0,0x0,0x40101004000100000104004100002000080ce3,0x0,0x0,0x0,0x40101004000100000104004100002200080ce3,0x0,0xc0101004000500010084002100082002080ce3,0x40101004000100004004100100002020080ce3,0x140101004000900020104004100102004080de3,0x40101004000100000004000100002000080ce3,0x40101004000100000004000100202008080ce3,0x40101004000100000004000100002000080ce3,0x40101004000100000004000100402010080ce3,0x40101004000100000004000100002100080ce3,0x40101004000100004004100100802020080ce3,0x1ed98007b66000fa98000f4e6f33d39bcc00f3004494c011346001ed981e60f3079fd6a6f3007af2136,0x40101004000100004004100101002040080ce3],
[0x40101004000100000004000100002000080ce3,0x40101004000100004004100102002080080ce3,0x0,0x40101004000100000004000104002100080ce3,0x0,0x240101004001100040204008108002200080ee3,0x40101004000100000004000108002200080ce3,0x440101004002100080404010108002200080ce3,0x40101004000100000004100108002200080ce3,0x0,0x80a104240501,0x0,0x80a104240501,0x0,0x812104240501,0x842104240501,0x812104240501,0x842104240501,0x822104240501,0x802104240501,0x822104240501,0x842104240501,0x842104240501,0x802104240501,0x842104240501,0x842104240501,0x16c87980001e603cc7981e62d907980000f30000f30079bcc007980001e9cc003db3000f6cc001e64dcf5,0x0,0x80a104240501,0x0,0x80a104240501,0x0],
[0x812104240501,0x842104240501,0x812104240501,0x842104240501,0x822104240501,0x802104240501,0x822104240501,0x842104240501,0x842104240501,0x802104240501,0x842104240501,0x842104240501,0x40101004000100000004000108002200080ce3,0x0,0x80a108240501,0x0,0x80a108240501,0x0,0x812108240501,0x842108240501,0x812108240501,0x842108240501,0x822108240501,0x802108240501,0x822108240501,0x842108240501,0x842108240501,0x802108240501,0x842108240501,0x842108240501,0x0,0x0],
[0xf30079bcc0798f300b6400f379803cfcc00f31e603cde61e6204603cfcc1e60f30007d4c0f30799556,0xf6cc003ea6000fe6bd4c00f379803d1b5ccf31e603cde62d901e603cfcc1e7f530007d4c0f30799556,0x0,0xe121ce240501,0x842108240501,0xe121ce240501,0x842108240501,0x82210c240501,0x802100240501,0x82210c240501,0x842108240501,0x842108240501,0x802100240501,0x842108240501,0x842108240501,0x40101004000100004004100108002200080ce3,0x0,0x0,0x0,0x0,0x6000300008000c0000000200002000000020003000080000000080000000200000006000010018000020000000080000000080400000101000000404000000410000001001087f9a7,0x812108240501,0x842108240501,0x812108240501,0x842108240501,0x822108240501,0x802108240501,0x822108240501,0x842108240501,0x842108240501,0x802108240501,0x842108240501],
[0x842108240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9144 : TreeBound (n := 4) 106 (programCode 0x4c29075f79) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40a190240501,0x0,0x432190204501,0x462190230501,0x432190204501,0x0,0x422190208501,0x10004400100080082080082002002400080000e4,0x422190208501,0x4400100080102080002002004400100000e4,0x462190210501,0x462190230501,0x462190210501,0x462190230501,0x422190220501,0x462190230501,0x422190220501,0x422190220501,0x40a190240501,0x0,0x800421012004100908004200100081002084ca3,0x824021902004100908004200104801120084ca3,0x800421022004100908004200100081004084ca3,0x0,0x0,0x10008400200080082080082002002400080000e4,0x0,0x8400200080102080002002004400100000e4,0x820021802004100908004200100801020084ca3,0x824021004004100908004200104802120084ce3,0x820021004004100908004200101002040084ce3],
[0x824021802004100908004200100801120084ca3,0x804021102004100908004200102001080084ca3,0x0,0x804021102004100908004200102001100084ca3,0x0,0x412190240501,0x0,0x472181240501,0x10400400080022000800022080402000000e4,0x472181240501,0x0,0x462182240501,0x46218c240501,0x462182240501,0x46218c240501,0x462184240501,0x46218c240501,0x462184240501,0x46218c240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x412190240501,0x0,0x0,0x20400800080022000800022080402000000e4,0x0,0x0,0x452182240501,0x46218c240501,0x452182240501],
[0x46218c240501,0x442184240501,0x46218c240501,0x442184240501,0x46218c240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x422190240501,0x462190240501,0x422190240501,0x462190240501,0x442190240501,0x462190240501,0x442190240501,0x462190240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9225 : TreeBound (n := 4) 106 (programCode 0x4c29075f7a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80410014000500018004200100082002080ce3,0x80532014000500918004200104c82020084ce3,0x80410014000500028004200100102004080de3,0x0,0x0,0x80410014000500008004200108002000080ce3,0xf300798f3089b6ef088b001e7e6001f532806d1001e9cc01e6f3001e603cc1e607983cc3cc1e7037c5,0x80412014000500818004200108002100084ce3,0x80532014000500918004200100802020084ce3,0xf300798f3089b6ef088b001e7e6001f532806d1001e9cc01e6f3001e603cc1e603cc40cdbbde7037c5,0x80412014000500a18004200101002040085ce3,0x80410014000500008004200100082000080ce3,0x7980798f308b9923081183cc1e6001f53243339001e9cc01e6f3001e679800fa98003d39801e8e92b5,0xf300798f3089b6ef088b001e7e6001f532806d1001e9cc01e6f3001e603cc1f632303cc3cc1e7037c5,0x80412014000500818004200104002100084ce3,0x80410014000500008004200108002000080ce3,0x0,0x0,0xc62190230501,0x0,0x0,0xc22190208501,0x8004200102080082080082002002400080412e4,0xc22190208501,0x8004200104080102080002002004400100804e4,0xc62190210501,0xc62190230501,0xc62190210501,0xc62190230501,0xc22190220501],
[0xc62190230501,0xc22190220501,0xc62190230501,0x0,0x100810024000900018004200100082002080ce3,0x100810024000900008004200100002020080ce3,0x100810024000900028004200100102004080de3,0x0,0x0,0x0,0xf3007983cc348b610fa9801e7e600088b2c57b5001e9cc01e6f3001e601e60f307983cc3cc1e7032b5,0x0,0x100934024000900928004200100802020084de3,0x100810024000900028004200100102010080de3,0x100814024000900a28004200101002040085de3,0x100810024000900028004200100102004080de3,0xf300798798548d090fa98f303cc001023336705001e9cc01e6f3001e679800fa980079f9801ee9b345,0x41088000800220001000080004000000011000248442000021108000000420000000400001001000004004000008010000008000080008104220010010800040002000100108edda7,0x100814024000900828004200104002100084de3,0x3cc1e60f30799e6011160008118001f530000f3001e9cc007a73001e600003db3000f6cc001e64d995,0x0,0x80411004000500018004200100082002080ce3,0x4020101004020100808004200104002020084ce3,0x100811004000900028004200100102004080de3,0x0,0x0,0x8008200202080082080082002002400080412e4,0x0,0x8008200204080102080002002004400100804e4,0x4020101004020100808004200100802020084ce3,0x1004000100008004200100002000080ce3,0x4020101004020100808004200101002040084ce3],
[0x1004000100008004200100002000080ce3,0x1004000100008004200102002080080ce3,0x0,0x1004000100008004200104002100080ce3,0x0,0x0,0x3cc03cc7983e24ba73d39800204600f3f32c974e0f4e600f4e6000f4e9cc001023000408c001e7032b5,0x201128044001100948004020108002200084ee3,0x3cc03cc7983e249c13d39800204600f3f32c93820f4e6003ea6001e7e9cc001023000408c001e7032b5,0x0,0xe121c2240501,0xe121ce240501,0xe121c2240501,0xe121ce240501,0xe121c4240501,0xe121ce240501,0xe121c4240501,0xe121ce240501,0xe121c8240501,0xe121ce240501,0xe121c8240501,0xe121ce240501,0x0,0xf3001e63cc1fa029c10d30007b66007a732803f80f4e600f4e6000f4e9cc001f53000408c001e707485,0xf3079800000000000001e61e607980000f30001023079c08c0f307981e9cc003db3000f6cc001e68a925,0xf3000f33cc1f81aa6d129800408c007a7324342c0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0xc62182240501,0x2000240481,0xc62182240501,0x2008240481,0x2004240481],
[0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x0,0x3cc03cc1e61092d4779f98002046003db32c5a8e0f4e600f4e6000f4e9cc001023000408c001e7032b5,0x0,0xf3003cc3cc1f6341679f9800408c007a7324342c0f4e6007b66001e7e9cc0010230007d4c001e7051a5,0x0,0xe121c2240501,0xe121ce240501,0xe121c2240501,0xe121ce240501,0xe121c4240501,0xe121ce240501,0xe121c4240501,0xe121ce240501,0xe121c8240501,0xe121ce240501,0xe121c8240501,0xe121ce240501,0x0,0x0,0x3cc079bcc01e63cc07980f3f3003cfcc00f3f3000f6cc00f300000f6cfcc0000f307983cc0007985216,0x0,0x0,0xe521c2240501,0x842108240501,0xe521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0xc22190240501,0x2010240481,0xc22190240501,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9370 : TreeBound (n := 4) 106 (programCode 0x4c29075f7b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x40a190240501,0x0,0x432190204501,0x462190230501,0x432190204501,0x0,0x422190208501,0x0,0x422190208501,0x0,0x462190210501,0x462190230501,0x462190210501,0x462190230501,0x422190220501,0x462190230501,0x422190220501,0x422190220501,0x40a190240501,0x0,0x1000441004008100a08004200100082002085ce3,0x1028041004008100a08004200105002020085ce3,0x1000841004008100a08004200100102004085de3,0x0,0x0,0x0,0x0,0x0,0x1020041004008100a08004200100802020085ce3,0x1028041004008100a08004200105002140085ce3,0x1020041004008100a08004200101002040085ce3],
[0x1028041004008100a08004200101002140085ce3,0x1008041004008100a08004200102002080085ce3,0xf33cc03cef76079f981e601e67980798f31116f3001e9cc007a73001e63cc03ccf300f8eec01eed8995,0x1008041004008100a08004200104002100085ce3,0xf307983ce046079f981e601e67980798f31116f3001e9cc007a73001e7e6003d39800f8b2001eed8995,0x412190240501,0x0,0x472181240501,0x0,0x472181240501,0x0,0x462182240501,0x46218c240501,0x462182240501,0x46218c240501,0x462184240501,0x46218c240501,0x462184240501,0x46218c240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x412190240501,0x0,0x0,0x0,0x0,0x0,0x452182240501,0x46218c240501,0x452182240501],
[0x46218c240501,0x442184240501,0x46218c240501,0x442184240501,0x46218c240501,0x462188240501,0x46218c240501,0x462188240501,0x46218c240501,0x422190240501,0x462190240501,0x422190240501,0x462190240501,0x442190240501,0x462190240501,0x442190240501,0x462190240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9451 : TreeBound (n := 4) 106 (programCode 0x4c29075f7c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x82010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9452 : TreeBound (n := 4) 106 (programCode 0x4c29075f7d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80a110240501,0x2040080104010100408004200108002200082ce3,0x80a110240501,0x0,0x2040080014010100400084002108002200082ce3,0x0,0x2040080024010100400104004108002200082de3,0x0,0x2040080044010100400204008108002200082ee3,0x2040080004010100400004080108002200082ce3,0x2040080084010100400404010108002200082ce3,0x2040080404010100402004100108002200082ce3,0x2040080104010100400804020108002200082ce3,0x0,0x2040080204010100401004040108002200083ce3,0x2040080404010100402004080108002200082ce3,0x2040080404010100402004080108002200082ce3,0x2040080004010100400004200108002200082ce3,0x0,0x2040080404010100402004280108002200082ce3,0x812110240501,0x2040080404010100408004200108002200082ce3,0x812110240501,0x0,0x0,0x20000800080022000800022080402000000e4,0x0,0x0,0x852102240501,0x842108240501,0x852102240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x822110240501,0x802110240501,0x822110240501,0x842110240501,0x842110240501,0x802110240501,0x842110240501,0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9501 : TreeBound (n := 4) 106 (programCode 0x4c29075f7e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x1bf60f1e6f3001e6f30097e37ec97801e6f30812730079bcc007a73001e9cc003db3000f6cc001ea19cf5,0x1e600097e0007b66000b6400f31e603cfcc00f3f3003cfcc1e62d9003cfcc1e60f307983cc03cc1e7556,0x100000400000002020000008004000010800000004000000010000100020001400400000201000004004000002010000008040000004100000020400000081000000100a5952e27,0x0,0x0,0x0,0x0,0x0,0x6220201010c0000600000200000400002020003110080000000080000000200000000020010000040020000100080000100080400000101000000404000000410000001001087f9a7,0x1e60011160003ea60012fc00f31e603cfcc00f30079bcc07b663cc79bcfcc1e60f3000408c03cc26a536,0x6220201010c0000500000200000400001020003110080000000080000000200000000020010000080020000080080000200080400000101000000404000000410000001001087f9a7,0x6000300018000c0000000200000000000020003000080000000080000000200000006000010008000020000000080020000080400000101000000404000000410000001001087f9a7,0x400021001000002000000210000000020020002000080000000080000000200000000200010000200010001000080001000080400000101000000404000000410000001001087f5a7,0x0,0x400021001000001000000210000000010020002000080000000080000000200000000200010000800010000800080002000080400000101000000404000000410000001001087f5a7,0x3cc0010230007b6600102300f44e2079bcc00f3079f9adcce1409f9879bcc0798f30a713cc07983d1426,0x0,0x3cc0010230007b6600102300f44e2079bcc00f33cc79ae832140b66079bcc0798f30a713cc07983d1426,0x0,0x3cc0010230007b6600102300f44e2079bcc00f33cc79af762140d4c079bcc0798f30a713cc07983d1426,0x1020044000100008004200108002200080ce3,0x1e6003ea6003cde600408c00f31e603cfcc00f3f3003cfcc1e7023003cfcc1e60f307983cc03cc2686d6,0x2020084000100008004200108002200080ce3,0x0,0x0,0x0,0x0,0x0,0xe521c2240501,0x842108240501,0xe521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x22010240481,0x2010240481,0x22010240481,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9550 : TreeBound (n := 4) 106 (programCode 0x4c29075f7f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x80a110240501,0x0,0x832110204501,0x862110230501,0x832110204501,0x0,0x822110208501,0x0,0x822110208501,0x0,0x862110210501,0x862110230501,0x862110210501,0x822110220501,0x822110220501,0x862110230501,0x822110220501,0x822110220501,0x80a110240501,0x0,0x4000501004020100808004200100082002084ce3,0x4020101004020100808004200104002020084ce3,0x4000901004020100808004200100102004084de3,0x0,0x0,0x0,0x0,0x0,0x4020101004020100808004200100802020084ce3,0x4000101004020100808004200100002000084ce3,0x4020101004020100808004200101002040084ce3],
[0x4020101004020100808004200104002100084ce3,0x4020101004020100808004200102002080084ce3,0x0,0x4020101004020100808004200104002100084ce3,0x7983cc1e62d903cc7981e60f307983cc0f30f30f3001e9cc007a73001e7e6003d39800f8b2001ede5995,0x812110240501,0x0,0x852101240501,0x0,0x852101240501,0x0,0x862102240501,0x842108240501,0x862102240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x812110240501,0x0,0x0,0x0,0x0,0x0,0x852102240501,0x842108240501,0x852102240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x822110240501,0x802110240501,0x822110240501,0x842110240501,0x842110240501,0x802110240501,0x842110240501,0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9631 : TreeBound (n := 4) 106 (programCode 0x4c29075f80) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10a030204481,0x4000420014020100808004200104c82020084ce3,0x10a030204481,0x0,0x0,0x400014000100008004200108002000080ce3,0x0,0x500014000100008004200108002100080ce3,0xc0a190210501,0x400014000100008004200100082000080ce3,0xc0a190210501,0xa010200481,0x80a110220501,0x0,0x80a110220501,0xa010200481,0x0,0x0,0x862110230501,0x0,0x0,0x822110208501,0x40005000140080082080086002002400088452e4,0x822110208501,0x40005000140080102080006002004400108844e4,0x862110210501,0x862110230501,0x862110210501,0x822110220501,0x822110220501],
[0x862110230501,0x822110220501,0x822110220501,0x0,0x10a030204481,0x800024000100008004200100002020080ce3,0x10a030204481,0x0,0x0,0x0,0x0,0x0,0xc0a190210501,0x100804024000900028004200100102010080de3,0xc0a190210501,0xa010200481,0x80a110220501,0x800024000100008004200100002010080ce3,0x80a110220501,0xa010200481,0x0,0x0,0x0,0x0,0x0,0x798001f53000408c0014e201e63cc03cfcc00f4c06b7027e7e63d3983cfcc3528f301e63cc07983cfc26,0x3cc001023000408c0012fc00f33cc03cfcc00f30079bcc07b663cc79bcfcc1e60f3000408c0798450536,0x798001f53000408c0014e201e63cc03cfcc00f4a948503531e6408c03cfcc3528f301e63cc07983cfc26,0x400030001000010000000300000000100020002000080000000080000000200000006000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x0,0x0,0x600021001a00005000000200002000010020003000080000000080000000200000000200010000800020000800080002000080400000101000000404000000410000001001087f9a7],
[0x3cc0011160007d4c00102300f46c8079bcc00f3079f98f6ce1409f9879bcc0798f30d4a3cc07983d1426,0x0,0x7980020460007d4c00111601e76c8079bcc00f33cc799f5320461e6079bcc0f30f30d4a3cc0f3079d936,0x400030001000010000000300000000100020002000080000000080000000200000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x3cc0011160007d4c00102300f46c8079bcc00f33cc7991162140d4c079bcc0798f30d4a3cc07983d1426,0x0,0x0,0x4001020044020100808004020108002200084ee3,0x0,0x0,0x212042240481,0x12000240481,0x212042240481,0x812108240501,0xc12184240501,0xe121ce240501,0xc12184240501,0x12000240481,0x812108240501,0xe121ce240501,0x812108240501,0x12000240481,0x3cc003db3003cfcc00408c00f33cc03cfcc00f3f3003cfcc1e9db3003cfcc1e60f307983cc0798465356,0x0,0x0,0x0,0x0,0x0,0x212042240481,0x12000240481,0x212042240481,0x812108240501],
[0xc12184240501,0xe121ce240501,0xc12184240501,0x12000240481,0x812108240501,0xe121ce240501,0x812108240501,0x12000240481,0x400030001000040000000200000000100020002000080000000080000000200000004000010010000020040000080100000080400000101000000404000000410000001001087f9a7,0x822110240501,0x2010240481,0x822110240501,0x2010240481,0x42010240481,0x2010240481,0x42010240481,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_7967 : TreeBound (n := 4) 106 (programCode 0x4c29075f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part012_7968 part012_8113 part012_8290 part012_8419 part012_8580 part012_8741 part012_8886 part012_8983 part012_9144 part012_9225 part012_9370 part012_9451 part012_9452 part012_9501 part012_9550 part012_9631

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9745 : TreeBound (n := 4) 106 (programCode 0x4c29076061) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf3000222c0002d90000b6511688b00007983cc2d90079bcc007a73001e600f33cc00f3f3003cde64dcf5,0x0,0x109090210481,0x409090210481,0x109090210481,0x4340000110000000400400000901000000c34021a0001000200410000200040082804000010010000040040000080100000080434000100010000400100000200400001001087fca7,0x0,0x0,0x0,0x0,0x409090210481,0x409090210481,0x409090210481,0x409090210481,0x2000480012014020508004200102c82020082ce3,0x168f08f8e7b4d283eb1b9c0b47847ddc708f8e7b4d283eb1b9c02d1e12085d08f8e7b47deb897639c0b4784930288f8e7b4d283eb1e6de11f336f08f99b7847ccdbc26b57d1f1ce5a3c2f2b207c73968f08fbb8e135abe8f8e7e19659b9603c512ecc0528be8f8e702d1e6c2df1e39ed1e135abe8f8e702d1e6c2df1e39cb4785e5640f8e702d1e6c2df1e39c2d1e2880d6f8e702d1e124c0a23e39c2d34b789cfdfe7b4784d6afa3e39c2d34b789cfdfe7b4784930288f8e72d34b789cfdfe72d1e124c0a23e39ed1e29eb321bb59cb9dd,0x4000500014024020908004200104c82020084ce3,0x409090210481,0x0,0x108430204481,0x0,0x108430204481,0x40003000000008002000090002000080006000200020000c0020001000028005c00000201000000804000008010000008000004002000020010000200100000200100108413a7,0x0,0x0,0x0,0x0,0x408430204481,0x100208000400820001000080001000200080000400400002002000010002000010040002080100008700400000801000004000100200014400f0001000200000400100009005aba8,0x408430204481,0x108430204481],
[0x80a530204501,0x4000200200000810000008002000008000a000000020000c0000001000028005c00000201000000804000008010000008000004002000020010000200100000200100108413a7,0x80a530204501,0x108430204481,0x0,0x80002000040081002000000002001000048040e4,0x8000a000240081002000808022001008048241e4,0xf30000b640004bf0000b641e60f33cc00011160003cde600f3f3001e7e600003cc03ccf300f31e68a5c5,0x8000a000240081002001008042001008048241e4,0xf3000222c0004bf0000b6f82bc15d907983cc0001e679803ccf300799e60b643cc2d90f303cc1e68a925,0x80012002440081002002010082001010048452e4,0x0,0x80022000840081002004020102001020048844e4,0x0,0xf3000222c0004bf0000b641e60f300000000000f3007980000f300001e9cc003db3000f300001e68a925,0x0,0xf3000222c0004bf0000b641e60f300000000000f3007980000f300001e9cc003db3000f300001e68a925,0x0,0x0,0x0,0x0,0x0,0x10220842110e2,0x10220812318e2,0x0,0x10220812318e2,0x10220842110e2,0x1022082211502,0x0,0x1022082211502,0x10220842110e2,0x10220842110e2],
[0x0,0x10220842110e2,0x0,0x0,0x0,0x80082012040081002040081002010400408050e4,0x80082012040081002080082002002400088050e4,0x0,0x10020802210a2,0x10020812210a2,0x0,0x10020812210a2,0x10020842210a2,0x1022082229502,0x0,0x1022082229502,0x10020842210a2,0x10020842210a2,0x0,0x10020842210a2,0x0,0x0,0x0,0x0,0x80002010040081002080002002004400108040e4,0x80082012040081002080082002010400408050e4,0x80082012040081002080082002008400208050e4,0x0,0x109090210481,0x409090210481,0x109090210481,0x0],
[0x0,0x2080092040081002080082002002401008050e4,0x0,0x4000110040081002080002002004401008040e4,0x409090210481,0x409090210481,0x409090210481,0x409090210481,0x80b190210501,0x0,0x80b190210501,0x409090210481,0x80082012040081002080082002010400408050e4,0x0,0x10a130220501,0x50a1b0220501,0x10a130220501,0x0,0x0,0xf3000222c0001e60000d4a1e600000000798000f30079bcc007a73001e7e6003cde600f379801e64dcf5,0x0,0x16c800222c0002046000d4a315c1e60f307983ccf30079bcc007a73001e7e6003cde600f379801e833cf5,0x40a190220501,0x80400010000080008004200102001080080ca3,0x40a190220501,0xa010220481,0x80a110220501,0x0,0x80a110220501,0x80a110220501,0x0,0x10020802210a2],
[0x10020812210a2,0x0,0x10020812210a2,0x10020842210a2,0x1022082221502,0x0,0x1022082221502,0x10020842210a2,0x10020842210a2,0x0,0x10020842210a2,0x0,0x0,0x0,0x0,0x0,0x10a130220501,0x50a1b0220501,0x10a130220501,0xf30001e600002d9000088b1e60f300000f30000f30079bcc007a73001e6f3001ed9800f3f3001e64d7e5,0x0,0x0,0x0,0x0,0x40a190220501,0xf40231e603cc1e7023088b25fb15c00088b079ad90079bcc007a73001e6f3001ed9800f3f3001ea197e5,0x40a190220501,0xa010220481,0x80a110220501,0x1bf60f1e6f3001e6f300e95bbad11001e6f30812730079bcc007a73001e7e6003d39800f3f3001ea19cf5,0x80a110220501,0x80a110220501],
[0x80002010040081002080002002040401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9906 : TreeBound (n := 4) 106 (programCode 0x4c29076062) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf300012fc0002d9000097e01e67980798f300f3000000f3001e7e61ed9800000000000000088b445baa6,0x100a0812a52a2,0x4000012010000001040000004100000480000120001000080004000000100004000400008100000040400000100200000200800002000400008002000004008000010010004a5ee27,0x100a0812a52a2,0xf30000b6400088b000088b00f33cc03ccf300f3003cfcc1f53079f983cc00f307983ea7e60fa983d1216,0x100a0822bdf02,0x0,0x100a0822bdf02,0x100a0852a52a2,0x100a0842a52a2,0x0,0x100a0842a52a2,0x0,0x0,0x0,0x0,0x80006000140081002080006002000c00028140e4,0x0,0x0,0x0,0x0,0x0,0x0,0xf30000b6400088b000088b00f33cc03ccf300f30079bcc0798079879bcc01e61023798408ded98452396,0x0,0xf30000b6400088b000088b00f33cc03ccf300f300f33cc03cc0798f33cc03cc1f53f307d4fd3983e0516,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x80006000140081002001004062001008048241e4,0x100a0812852a2,0x400001201000000004000000810000048000012000100008000400000000000400000000810000004040000010020000020080000100040000000200000000800004001000485ee27,0x100a0812852a2,0x400001201000004804000012010000048000002000100008000400000000000000000020010000080040000040020000100080002400040009000200024000800090001000485ee27,0x100a082285702,0x400001001000004804000010010000048000002000100008000400000000000000000008008000040040000100020000200080001000040004000200010000800040001000485ae27,0x100a082285702,0x100a0852852a2,0x100a0842852a2,0x0,0x100a0842852a2,0x0,0x0,0x0,0x0,0x8000600014008100208000600208040140a050e4,0x80006000140081002080006002002400088452e4,0x80006000140081002080006002080401008040e4,0x80006000140081002080006002004400108844e4,0x80006000140081002080006002000c0040a050e4,0x80006000140081002080006002008400209058e4,0x80006000140081002080006002080401008040e4,0x8000600014008100208000600201040040a050e4,0x80006000140081002080006002080401008040e4,0x8000600014008100208000600202040080c060e4,0x80006000140081002080006002080400008040e4],
[0x80006000140081002080006002040401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9971 : TreeBound (n := 4) 106 (programCode 0x4c29076063) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0xf307983cc0000f307981e601e63cc03ccf300f3f3084e7cc0000f3003cfcc352800079800007983cddc6,0x80006010140081002080006002000c00028140e4,0x0,0x108430204481,0x0,0x108430204481,0x445ad907980001e6111601e63cc03ccf300f3f3085155c0000f3003cfcda1b364079800081183cddc6,0x0,0x0,0x0,0x0,0x408430204481,0x0,0x408430204481,0x108430204481,0x80a530204501,0x0,0x80a530204501,0x108430204481,0x0,0x8000a010240081002001008042001008048241e4,0x8000a010240081002000808022001008048241e4,0xf3000222c00088b00012fc1e60f300000011160003cde600f3f3001e7e600003cc03ccf300f31e68a5c5,0x8000a010240081002001008042001008048241e4,0xf3079b15c0004bf07981e601e63cc03ccf300f4c06b711ae6003d3983cc01283364204600081183cfc26,0x8000a010640081002002008082001010048253e4,0x0,0x8000a010a40081002004008102001020048245e4,0x8000a010240081002001008402001208048241e4,0x8000a010240081002008008202001200048241e4,0x0],
[0x8000a010240081002010008402001200048241e4,0x0,0x0,0x0,0x0,0x0,0x4000000010000b000400010001000080000800004004000020020000100020000100000000001e600b30002001000080000400008004001ec00e00000002000002001000280052ba8,0x0,0x0,0xf3000222c00088b0001303b660f300000097e00000079800007980001e607983cc0798f301e61e64dcf5,0xf3000222c00088b0001303b69db4e607983cc0001e679803ccf300799e607983cc0f30f301e61e68a925,0xf3000222c00088b0001303b660f4e600003cc00f3007980000f300001e607983cc0f30f301e61e68a925,0x0,0x0,0x1dcd6500000773595dcd66dcd65ee6b2f73595dcd66dcd65ee6b2bb9aca0ee6c166b283b9ad1735941dcddc35941dcd6c735941dcd65000000003b9acbdcd650773597b9b059acbdcd650b2d0639682f0003b9aca00000ee6b2800003b9aca077360b35941dcd82cd65ee6b5eb43fa,0x400000011000000044000000110000000140202110000800000402000000004000004220010000000010000800080000000080002000100002000400010001000010001001087f7a7,0x0,0xf3000222c00088b0001303b660f4e600003cc00f3007980000f300001e607983cc0f30f301e61e68a925,0x0,0x0,0x0,0x0,0x0,0x80002010040081002010000002002200088040e4,0x80006010140081002000804022002010088452e4,0x0,0x8000a010240081002001008042002010088453e4,0x80082010040081002010080402002200088050e4,0x80012010440081002002010082002010088452e4,0x0,0x80022010840081002004020102002020088844e4,0x80082010040081002010080402002200088050e4],
[0x80042010040081002008040202002200088058e4,0xf3000222c00088b00012fc1e60f3000000000000f307983cc0f307981e9cc003cc0000f300001e68a925,0x80082010040081002010080402002200088050e4,0x0,0x0,0x0,0xf3000222c00088b00012fc1e60f300000000000f30079bcc00f300001e9cc003cc0000f300001e68a925,0x0,0x400000005000000024000000090000000100102004100408004c00000010004000108001008000008040000004020000010080000800040004000200010000800020001000485ae27,0x0,0x0,0xf3000222c00088b0001303b660f300000079800000079800007980001e607983cc1e60f303cc1e64dcf5,0x0,0x400000011000000024000000090000000140302000100008000400000000004000004000010000000040000000020000000080002000100004000200010000800020001000487ee27,0x0,0x400000005000000024000000090000000100102000100008000400000000004000000010010000000040000000020000400080000800040004000200010000800020001000485ee27,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80002010040081002000000002004000108040e4,0x80006010140081002000804022004020108844e4,0x80002010040081002000002002004400108040e4,0x8000a010240081002001008042004020108845e4,0x80082010040081002010080402004200108050e4,0x80012010440081002002010082004010108452e4,0x0],
[0x80022010840081002004020102004020108844e4,0x80002010040081002000000402004200108040e4,0x80042010040081002008040202004200108058e4,0x0,0x80082010040081002010080402004200108050e4,0x0,0x0,0x0,0xf303cc3cc2d90f307981e601e67980798f300f37983cc1e62f763cc079807b66001f164003db30799c76,0x0,0x109090210481,0x409090210481,0x109090210481,0x1dcd6500000773597b9aca4a817c80003d77a0500004a818ba24d4a0ee6c166b283b9ad1735941dcddc35941dcd6c735941dcf41d65000007735940003d77a0503b9b413595dcd66dcd65059682f0003b9aca0001ebbd0281dcd65003c893536e6b282cb4354d65ee6b5e9bd5a,0x0,0x0,0x0,0x0,0x409090210481,0x409090210481,0x409090210481,0x409090210481,0x80b190210501,0x0,0x80b190210501,0x409090210481,0xf3000222c00088b00012fc1e60f300000000000f30079bcc00f3f3001e9cc003cc0000f300001e68a925,0x0,0x109090210481,0x409090210481,0x109090210481,0x0],
[0x0,0x0,0x0,0x0,0x409090210481,0x409090210481,0x409090210481,0x409090210481,0x80b190210501,0x0,0x80b190210501,0x409090210481,0xf3000222c00088b00012fc1e60f300000000000f30079bcc00f3f3001e9cc003cc0000f300001e68a925,0x0,0x10a130220501,0x50a1b0220501,0x10a130220501,0x0,0x0,0x40000001000000000c000000110000000160002000080000000440000000400080004000010010000010040000080100000080200000100200000081000001001000001001087c7a7,0x0,0x1f360c83cc0000f307b6601e63cc03ccf300f3f30e1744c0000f3003d30bb98320079800007983cddc6,0x40a190220501,0x100400020000080008004200102001080080ca3,0x40a190220501,0xa010220481,0x80a110220501,0x0,0x80a110220501,0x80a110220501,0x0,0x0],
[0x800820020000000008004200100002010080ce3,0x0,0x0,0x80080410040081002080082002020400808050e4,0x8118007980f3081273f300f33cc03ccf300f3f3003cfcc001023003cc799e60798798079879844e6d6,0x0,0x1e60f307b6bb20f30f4e601e67980798f300f3f3000f6cc20a21300798f31e603ccb640798f307b8276,0x800820020000000008004200100002010080ce3,0x800020000000008004200100002010080ce3,0x1000840020000000008004200100002010080ce3,0x800020000000008004200100002010080ce3,0x2000880022010804428004200100102010082de3,0x0,0x4000900024020804828004200100102010084de3,0x800020000000008004200100002010080ce3,0x0,0x10a130220501,0x50a1b0220501,0x10a130220501,0x222c00088b00012fc1e616c80001e61e60f3001e9cc00f3f3001e7e6003d39800f3f3001e68a5c5,0x0,0x0,0x0,0x0,0x40a190220501,0xf381183cc1e603cc799e601e63cc03ccf300f3f3084e7cc01e6f3003d1b23528b647981e607984c0dc6,0x40a190220501,0xa010220481,0x80a110220501,0x0,0x80a110220501,0x80a110220501],
[0x0,0x108010200481,0x408010200481,0x108010200481,0x0,0x0,0x8118007983cc081273f300f33cc03ccf300f3f3003cfcc003db3003ccf31e603cc7980f30798465356,0x0,0x1e60f307b69cc0f30f4e601e67980798f300f3f3000f6cc2083b300799e61e60798b640f30f307b8276,0x408010200481,0x8010200481,0x408010200481,0x8010200481,0x80a110220501,0x0,0x80a110220501,0x8010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10180 : TreeBound (n := 4) 106 (programCode 0x4c29076064) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x8000a000240081002000008042000000048041e4,0x1dcd65f225ca7e8140003d77a0500000773597c8954d23b50000255e8be1893528000f224dc13597c89370c49a9400000ee6b280000001dd11eaca0077447ab2800ee88f565000ee88f565001dd11f25b26a5077360b35941dd4f626a507735cf9aca07735cf9aca0ee6c1e1a1b499,0x0,0x8000a000240081002001008042001008048241e4,0x100a0852b18e2,0x100a085289502,0x100a0812a10a2,0x100a085289502,0x0,0x100a0852918e2,0x0,0x100a0852918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0xf300012fc0004bf000102300f33cc03ccf300f3000f6cc00f303cc0f6ccf31e60f301e60f307983cf3b6,0x100a0812918e2,0xf300012fc0004bf000102300f33cc03ccf300f3000f6cc00f303cc0f6cc001e60f3000000007983cf3b6],
[0x100a0812a10a2,0x0,0x100a0812a10a2,0x0,0x40000000900000004c0000001300000002000260001000080004000000120009000480008100000040400000100200000200800002000400008002000004008000010010004a5ee27,0xf3000222c00088b000111601e67980798f300f3000f31e603cc88b0fa98003cc1e616c87984bf25fd756,0x0,0xf300003cc00088b000222c1e60f300000001e60003cde600f3f3001e7e600003cc03ccf300f31e68a5c5,0x0,0x0,0x0,0xf3000222c00088b000111601e67980798f300f3000001e6000088b0079807980001ed98003db6d3bbd56,0x400000011000000044000000090000000120000100080000400100000800200001000002000100008000420000000900080600000200010000880000001200100c004004200273228,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100a0812a52a2,0x100a0812852a2,0x0,0x100a0812852a2,0x100a0812b18e2,0x100a081289502,0x100a0812a10a2,0x100a081289502,0x100a081295ae2,0x100a0812918e2,0x0],
[0x100a0812918e2,0x0,0x100a0812a10a2,0x0,0x100a0812a10a2,0xf307a76cc1e9db30007d53b69db4e607983cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0x0,0x0,0x11cc0c0002000200010080000012000010004000020020000100020000100000000011cc0c0602000000010800004004000000010000e6064000000010000400020027aba8,0x0,0x1a94001e60000408c00111601e63cc03ccf300f4a940b8260000408c03cfcc3528f300003cc07983cfc26,0x1e601e63cc03ccf30111601e63cc03ccf300f4ac19b8263cc0408c03cfcc3584130007d4c07983def26,0x0,0x0,0xb64001e60000408c00111601e63cc03ccf300f4a940b8260000408c03cfcc3528f300003cc07983cfc26,0xf3001e7e6003d3980111601e63cc03ccf300f4c008b8371600408c03cfcc3801f30222fcc0798449426,0x1a99b21e600003cc000111601e63cc03ccf300f4a99bd8260000408c03cfcc35345700003cc07983cfc26,0x0,0x0,0x798001f53000408c00111601e63cc03ccf300f4a940b8353000408c03cfcc3528f301e63cc07983cfc26,0xf300012fc00088b000102300f37980798f300f300f300f379ae098f379bcc001f530d596cc079854cf26,0x0,0x100a0852a52a2,0x100a0852852a2,0x0,0x100a0852852a2,0x100a0852b18e2,0x100a085289502],
[0x100a0852a10a2,0x100a085289502,0x100a085295ae2,0x100a0852918e2,0x0,0x100a0852918e2,0x0,0x100a0852a10a2,0x0,0x100a0852a10a2,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0x0,0x0,0xee6b2800003d77a0500001dcd6c73595dd4d859400218711a0ee6c166b283b9ad1735941dcddc35941dcd6c735941dcd650000000ee6b2800003c8935283b9aca00773595e449a941dcddc359400001dcd65ee6b2f73597b9acbdcd6500000773595dcd65ee6d3dece9a,0xf301e63cc0798798111601e67980798f300f300f302049cdee118079bcc0f4f530b6bd4c0f3089fc36,0xf30000f30000408c00102300f33cc03ccf300f33cc03cc00000408c03cfcc1e60f300003cc07983cf3b6,0x1e601e67980798f30111601e67980798f300f301e60204d99ee118079bcc003db30b736cc0f307bbf36,0x0,0x79801e7e60079bcc0111601e67980798f300f307980206461ee118079bcc1023f30ba0fcc0f3090a136,0x2046000811800111601e67980798f300f300000204601ee118079bcc0000f30b643cc0f3079d936,0x79800f6cc0079f980102300f37980798f300f3079801245c2e1118079bcc0a71f30d86fcc079853dc26,0xf300003cc000102300f33cc03ccf300f33cc03cc00000408c03cfcc1e60f300003cc07983cf3b6,0x3cc0010230007b6600102300f37980798f300f33cc00120902e1118079bcc0798f30d4a3cc07983d1426,0x0,0x7980020460007d4c00111601e67980798f300f379800204601ee118079bcc0f30f30b643cc0f3079d936,0xf307983cc1e60f300003cc1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0],
[0x0,0x1e60f307983cc1e6102300f33cc03ccf300f300003cc000003cc003cfcc1e60f300003cc07983cf3b6,0x2030000002040000010300000010200078203e1e100800010042008000002000002000010002000010010000080010000080400000101000000404000001010000001001087f7a7,0x7980f379803cc798102300f33cc03ccf300f33ea63cc1e60040aa63cfcc1e60f301f56cc07984671b6,0x0,0x0,0x0,0xf30b640002d900001e63cc1e60f3000000000007980798f300f31e601e9cc003db3000f6cc001e68a925,0x100040000200800001003000002005000400020000000080004100000000400800004000020080000400080000400100000804000000810000001040000008100000010008861e67,0xf30b640002d900001e63cc1e60f3000000000007980798f300f31e601e9cc003db3000f6cc001e68a925,0xf300003cc000102300f33cc03ccf300f300003cc000003cc003cfcc1e60f300003cc07983cf3b6,0x0,0x0,0x0,0x0,0x221100000484400001200000001001042202110108800010400000040002000004220010010880020000080080004000080400000101000000404000001010000001001087fba7,0xf30f30f303cc0f3102300f33cc03ccf300f31e603cde60003ea603cfcc1e60f30000b6407983cf3b6,0x0,0x1e60f30f307981e6102300f37980798f300f33cc00102302e0b66079bcc00088b0d4d15c07983d1426,0x79800f307983d3980102300f33cc03ccf300f31e603cde60003ea603cfcc1e60f3003cfcc0798448bb6,0xf300f33cc0798798102300f37980798f300f33cc00102302e0b66079bcc001f530d55a0c079854cf26,0x0,0x1e601e67980798f30111601e67980798f300f33cc001f5301edb66079bcc003db30b6bd4c0f307bbf36,0x1e60f8c1307a7300102300f37980798f300f33cc00102302e0b66079bcc02e18b0e0262c079853dc26,0x79800f4e60079bcc0102300f37980798f300f33cc00102302e0b66079bcc00f3f30da55cc079853dc26,0x2046000811800111601e67980798f300f33cc001f5301edb66079bcc0f30f30b643cc0f3079d936,0x79800f6cc0079f980102300f37980798f300f33cc00102302e0b66079bcc01e6f30e007cc079853dc26,0xf300003cc000102300f33cc03ccf300f31e603cde60003ea603cfcc1e60f300003cc07983cf3b6,0x3cc0010230007b6600102300f37980798f300f33cc00102302e0b66079bcc0798f30e3d3cc07983d1426,0x0,0x7980020460007d4c00111601e67980798f300f33cc001f5301edb66079bcc0f30f30d4a3cc0f3079d936,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4000080000000800040002800000002000400020001000080004000000000000800010000020040000400100000400200000804000000810000002040000008100000010008862e67,0x0,0x400030000000010000000300000000100040002000100000000000000000000000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x80200000800b000010030000020020000000218010c008700408000000080000000800008008000020010000040020000080400000041000000404000000810000001000885ba67,0x400030000000010000000300000000100040002000100000000000000000000000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x0,0x0,0x0,0x400030001000010000000300000000100040002000100000000000000000000000002000010008000010008000080020000080400000101000000404000000410000001001087f5a7,0x0,0x0,0x0,0x0,0x3cc1e60f307981e6111601e67980798f300f379800204601edd4c079bcc00088b0b6622c0f3079d936,0x3cc1e9db307a7300111601e67980798f300f379800204601edd4c079bcc00088b0bdfa2c0f3079d936,0xf300f33cc0798798102300f37980798f300f33cc00111602e0d4c079bcc001f530d51d4c079854cf26,0x15d50007d4c00102300f37980798f300f33cc00111602e0d4c079bcc0000f30d4a3cc07983d1426,0xf300f37980798f30102300f37980798f300f33cc00111602e0d4c079bcc001f530d596cc079854cf26,0x3cc1e9db307a7300111601e67980798f300f379800204601edd4c079bcc00088b0bdfa2c0f3079d936,0x79800f4e60079bcc0102300f37980798f300f33cc00111602e0d4c079bcc00f3f30d86fcc079853dc26,0x1209000811800102300f37980798f300f33cc00111602e0d4c079bcc0000f30d4a3cc07983d1426,0x79800f6cc0079f980102300f37980798f300f33cc00111602e0d4c079bcc00f3f30dc3bcc079853dc26,0xf300003cc000102300f33cc03ccf300f33cc03ccf3000408c03cfcc1e60f300003cc07983cf3b6,0x3cc0010230007b6600102300f37980798f300f33cc00111602e0d4c079bcc0798f30d4a3cc07983d1426,0x0],
[0x3cc0011160007d4c00102300f37980798f300f33cc00111602e0d4c079bcc0798f30d4a3cc07983d1426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10373 : TreeBound (n := 4) 106 (programCode 0x4c29076065) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10220842110e2,0x400000021000000084000000810000000840002000000010000c00000a0000018280800040200000100800001008000001008041484010001000010414040100050000100108713a7,0x0,0x80002002040081002000000002001000048040e4,0x10220842110e2,0x10220842090e2,0x10220842210e2,0x10220842090e2,0x10220842110e2,0x10220842110e2,0x0,0x10220842110e2,0x0,0x10220842210e2,0x0,0x10220842210e2,0x0,0x0,0x0,0x0,0x0,0x201008040804020108004020108002200080ce3,0x0,0x0,0x0,0x801020040804020108004020108002200080ce3,0x801020040804020108004020108002200080ce3,0x1001040040004020108004020108002200080ce3,0x801020040804020108004020108002200080ce3,0x2001080042014020508004020108002200082ee3],
[0x801020040804020108004020108002200080ce3,0x4001100044024020908004020108002200084ee3,0x801020040804020108004020108002200080ce3,0x0,0xf3000f6cc001023000408d11688b00007987981e63d39800f379801e7e600f33cc00f3f3003cde64dcf5,0x400000101000000204000000810000000840022111000080000400000000000200000002010000008020000020080000020080422200100080000400000001000400001001087fba7,0x0,0x40000008100000020400000021000000084000200010008800040000001000020000000200800000802000001002000002008000000010000080040000200080000c001000487ba27,0x0,0x0,0x0,0xf3000f6cc001023000408d11688b00000007980003d39800f379801e7e9ccf33cc0000f300799e64dcf5,0x0,0x0,0x0,0xf3000f6cc001023000408d1160f300000007980003d39800f379801e7e9cc003cc0000f300001e64dcf5,0x0,0x0,0x0,0x0,0x0,0x80002002040081002001000042000000008040e4,0x8000600a140081002001004042000804028140e4,0x0,0x8000a002240081002001008042001008048241e4,0x80002002040081002001000042000000408040e4,0x80012002040081002001010042002010088253e4,0x80002002040081002001000042000001008040e4,0x80022002840081002001020042004020108245e4,0x80002002040081002001000042000000408040e4,0x80042002040081002001040042008040208058e4,0x0],
[0x80082002040081002001080042010080408050e4,0x0,0xf300003cc0f30f3003ccf300f33cc03ccf300f3001e9cc0088b0001e9cc799e607983cc0798798b65556,0x0,0xf303cc3cc2f76f300799e601e67980798f300f300408c0012276001ed99e60f30798b640f30f30799c76,0x10220842410e2,0x1022082241502,0x0,0x0,0x0,0x0,0x0,0x210842240481,0x610842240481,0x210842240481,0x210842240481,0x410842240481,0x410842240481,0x410842240481,0x210842240481,0x812942240501,0x610842240481,0x812942240501,0x210842240481,0x1022082241502,0x10220842410e2,0x10220842410e2,0x0,0x0,0xf30000f300000f6ccf300f33cc03ccf300f33cc03cc00f3003cc03cfcc0000f3079a22c07983cd556,0x0,0x0],
[0x211084240481,0x411084240481,0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x813184240501,0x411084240481,0x813184240501,0x411084240481,0x10220842410e2,0x0,0x0,0x880022040081002040080402080206008050e4,0x0,0x0,0x212148240501,0xa12948240501,0x212148240501,0x812108240501,0x412188240501,0xe139c8240501,0x412188240501,0x12008240481,0x812108240501,0xe139c8240501,0x812108240501,0x812108240501,0x80082002040081002020080802080402008050e4,0x0],
[0x0,0x0,0x0,0x0,0x212148240501,0xa12948240501,0x212148240501,0x812108240501,0x412188240501,0xe139c8240501,0x412188240501,0x12008240481,0x812108240501,0xe139c8240501,0x812108240501,0x812108240501,0x80002002040081002040001002080402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10518 : TreeBound (n := 4) 106 (programCode 0x4c29076066) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x800220004400810020800a200208060200805504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10519 : TreeBound (n := 4) 106 (programCode 0x4c29076067) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80002008040081002000000002000000008040e4,0x400000101000000104000001010000001040002000000010002c00000a0000058282800040200000100800001008000001008041494010001000010414140100050000100109713a7,0x0,0x80002008040081002000000002001000048040e4,0x400000101000000104000001010000001040002000000010000c0000002000058008800040200000100800001008000001008000040010000100010001000100001000100108713a7,0x400000101000000404000001010000001040022011000080000400200000000400000002010000002010000010080000010080402200100000000400008001000000001001087f7a7,0x80002008040081002000000002000001008040e4,0x80002008040081002000000002004000108040e4,0x400000101000000104000001010000001040002000000010002c0000020000058082800040200000100800001008000001008000400010001000010010000100010000100109713a7,0x400000101000000404000001010000001040022111000080000400200000000400000002010000002010000010080000010080422200100000000400020001000000001001087f7a7,0x0,0xf3000f6cc003db30007d4d1160f33cc00007980003d398007a73000f4e9cc003cc0000f300001e68a925,0x0,0x400000101000000104000001010000001040002000000010002c00000a0000058282800040200000100800001008000001008040000010001000010400000100050000100109713a7,0x0,0x80002008040081002000000002040001008040e4,0x0,0x80002008040081002000800022000000008040e4,0x80006008140081002000804022000804028140e4,0x0,0x8000a008240081002000808022001008048241e4,0x80082008040081002000880022040080408050e4,0x80012008140081002000810022002010088152e4,0x0,0x80022008140081002000820022004020108144e4,0x80082008040081002000880022010080408050e4,0x80042008040081002000840022008040208058e4,0xf307983cc0798f301e60f300f33cc03ccf300f3000f6cc00fa98000f6ccf31e60f301e60f307983cd556,0x80082008040081002000880022010080408050e4,0x80002008040081002000800022080000008040e4],
[0xf307983cc03ccf301e60f300f33cc03ccf300f3000f6cc00f6cc000f6cc799e607980f307987985b3556,0x0,0xf303cc3cc3528f303cc1e601e67980798f300f300222c000b08e000fa99e60f30798d4a0f30f30799c76,0x0,0xf3000f6cc003db30007d4c1e62d93cc07991161e63cde600f3f3001e7e6003cfcc01e6f3003cde68a5c5,0x40000000300008000c0002000300004000a00001000200001002000010002000010000004000300010400000060003000104000000400020001800080012000200014000a000713a8,0x0,0xf3000f6cc003db30007d4c1e60f33cc00011160003cde600f3f3001e7e600003cc03ccf300f31e68a5c5,0x0,0x0,0x0,0xf3000f6cc003db30007d4c1e60f33cc00011160003cde600f3f3001e7e600003db33ccf300f31e68a5c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80002008040081002001000042000000008040e4,0x80006008140081002001004042000804028140e4,0x0,0x8000a008240081002001008042001008048241e4,0x80002008040081002001000042000000408040e4,0x80012008240081002001010042002010088253e4,0x80002008040081002001000042000001008040e4,0x80022008240081002001020042004020108245e4,0x80002008040081002001000042000000408040e4,0x80042008040081002001040042008040208058e4,0x0],
[0x80082008040081002001080042010080408050e4,0x0,0x0,0x0,0xf303cc3cc2d90f303cc1e601e67980798f300f300408c0012276001ed99e60f30798b640f30f30799c76,0xf3000f6cc003db30007d53b69db4e607983cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x80012008440081002002010082080012008452e4,0x0,0x0,0x0,0x0,0x0,0x210842240481,0x610842240481,0x210842240481,0x210842240481,0x410842240481,0x410842240481,0x410842240481,0x210842240481,0x812942240501,0x610842240481,0x812942240501,0x210842240481,0x80022008840081002004020102080022008844e4,0x0,0x0,0x0,0x0,0x0,0x211084240481,0x411084240481],
[0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x813184240501,0x411084240481,0x813184240501,0x411084240481,0xf3000f6cc003db30007d4c1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x0,0x0,0x0,0x211084240481,0x411084240481,0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x813184240501,0x411084240481,0x813184240501,0x411084240481,0xf3000f6cc003db30007d4c1e60f300000000000f3007980000f300001e9cc003db3000f6cc001e68a925,0x0,0x0,0x4000001000100001040000010005000010400020a0010002800140000a005000aa80040000200100000801000008001000008040000010100000010400000101000000101508713a7],
[0x0,0x1000048040081002000000002080002008040e4,0x212148240501,0xa12948240501,0x212148240501,0x812108240501,0x412188240501,0xe139c8240501,0x412188240501,0x12008240481,0x812108240501,0xe139c8240501,0x812108240501,0x812108240501,0x0,0x80000008040081002020000802080002008040e4,0x16c8000f301e611160f300f33cc03ccf300f31e603cde6000204603cfcc1e60f30000b6407983cd556,0x0,0x3cc1e61209b64222c1e601e67980798f300f33cc001f532f81826079bcc00088b0b6715c0f3079d936,0x211084240481,0x411084240481,0x211084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x8139c6240501,0x411084240481,0x8139c6240501,0x411084240481,0x0],
[0x0,0x0,0x0,0x0,0x212148240501,0xa12948240501,0x212148240501,0x812108240501,0x412188240501,0xe139c8240501,0x412188240501,0x12008240481,0x812108240501,0xe139c8240501,0x812108240501,0x812108240501,0x0,0x0,0x0,0x0,0x3cc1e61209798222c1e601e67980798f300f37980020462f7dd4c079bcc00088b0b6622c0f3079d936,0x210000240481,0x10000240481,0x210000240481,0x10000240481,0x410000240481,0x10000240481,0x410000240481,0x10000240481,0x812108240501,0x410000240481,0x812108240501],
[0x10000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10712 : TreeBound (n := 4) 106 (programCode 0x4c29076068) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x800220008400810020800a200208060200805504]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10713 : TreeBound (n := 4) 106 (programCode 0x4c29076069) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80002002040081002080002002080402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10714 : TreeBound (n := 4) 106 (programCode 0x4c2907606a) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80042001040081002080042002080402008058e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10715 : TreeBound (n := 4) 106 (programCode 0x4c2907606b) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x120430204481,0x121090210481,0x120430204481,0x0,0x0,0x88002200000000008004200108002000080ce3,0x0,0x88002200000000008004200108002000080ce3,0x121090210481,0x120010200481,0x121090210481,0x120010200481,0x122130220501,0x88002200000000008004200100402000080ce3,0x122130220501,0x120010200481,0x0,0x0,0x420010210481,0x0,0x0,0x420010208481,0x804028040081002080006002002400088452e4,0x420010208481,0x804028040081002080006002004400108844e4,0x420010210481,0x420010200481,0x420010210481,0x420010200481,0x420010220481],
[0x420010200481,0x420010220481,0x420010200481,0x0,0x120430204481,0x121090210481,0x120430204481,0x0,0x0,0x0,0x0,0x0,0x121090210481,0x120010200481,0x121090210481,0x120010200481,0x122130220501,0x0,0x122130220501,0x120010200481,0x0,0x0,0x0,0x0,0x0,0x4273e607983cc20461e601e63cc03ccf300f4c0698a27e6003d3983cfcc35345701e63cc07983cfc26,0x3cc1e61023798222c1e601e67980798f300f300f301e63dd1d9879f9bcc001f530b69eec0f3089fc36,0x0,0x3cc1e61023798222c1e601e67980798f300f301e601e67a91d98f379bcc003db30b7552c0f307bbf36,0x0,0x3cc1e61023798222c1e601e67980798f300f3079801e7e711d9bcc79bcc0f30f30d4c22c0f3079d936,0x0],
[0x3cc1e61023798222c1e601e67980798f300f30f3001e9cd11d9f9879bcc0f30f30b6622c0f3079d936,0x0,0x3cc1e61023798222c1e601e67980798f300f33cc001f53111db66079bcc00088b0b6715c0f3079d936,0x0,0x3cc1e61023798222c1e601e67980798f300f3798002046111dd4c079bcc00088b0b6622c0f3079d936,0x0,0x0,0x208008200804020108004020108002200080ce3,0x0,0x0,0x220842240481,0x220000240481,0x220842240481,0x220000240481,0x221084240481,0x220000240481,0x221084240481,0x220000240481,0x222148240501,0x221084240481,0x222148240501,0x220000240481,0x42200880400810020802a200208062200805504,0x0,0x0,0x0,0x0,0x0,0x220842240481,0x220000240481,0x220842240481,0x220000240481],
[0x221084240481,0x220000240481,0x221084240481,0x220000240481,0x222148240501,0x221084240481,0x222148240501,0x220000240481,0x42201080400810020802a200208062200805504,0x420010240481,0x20010240481,0x420010240481,0x20010240481,0x822110240501,0x20010240481,0x822110240501,0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10828 : TreeBound (n := 4) 106 (programCode 0x4c2907606c) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x80082002040081002080082002080402008050e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10829 : TreeBound (n := 4) 106 (programCode 0x4c2907606d) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x140430204481,0x90002400804402118004200100c82020080ce3,0x140430204481,0x0,0x0,0x90002400000002008004200108002000080ce3,0x0,0x90002400080402018004200108002002080ce3,0x1414b0210481,0x90002400000002008004200100401000080ca3,0x1414b0210481,0x140410200481,0x142530220501,0x90002402010402418004200100402080082ce3,0x142530220501,0x140430204481,0x0,0x0,0x441090210481,0x0,0x0,0x441090208481,0x1694acbb7f75e3e3a1a3c243dd823fa473bc434afc8fe8ac23e4507847c7434784930288f8e700000168f08f8e868f090f76095339b2ec94e70000168f09ad8c65ded49cf134dea7883c4180000b47847ca09e11f49fe11f2827847ccdbc23e3f63c23e39c0168f08f8e7b4784d6afa3e39cb4785e5640f8e72d1e1795903e39d68f0a61d78f8e72d1e1795903e39c2d1e2880d6f8e702d1e6c2df1e39c016907243b2b253a1a41ceb28d0788469071e9768e70168f09532323e39d69071e9768e7002d1e11f1ce000002d1e29eb32e1519ece1d,0x441090208481,0x0,0x441090210481,0x441090210481,0x441090210481,0x441090210481,0xc43190220501],
[0xc43190230501,0xc43190220501,0x441090210481,0x0,0x140430204481,0x110004400000004008004200100002020080ce3,0x140430204481,0x0,0x0,0x0,0x0,0x0,0x1414b0210481,0x0,0x1414b0210481,0x140410200481,0x142530220501,0x0,0x142530220501,0x140430204481,0x0,0x0,0x0,0x0,0x0,0xf4e9cc3d39f9800f3f33d3b6bc15d907983cc0001e679803ccf300799e9cc003db3000f6cc001e68a925,0x1010042040081002002010082080012008452e4,0x0,0x1020040840081002004020102080022008844e4,0x0,0x1200048040081002008200202080202008241e4,0x0],
[0x1200048040081002010200402080202008241e4,0x1000040040081002000000002080002008040e4,0x3cc1e61209b641e601e601e67980798f300f33cc001f532f81826079bcc00088b0b6715c0f3079d936,0x0,0x3cc1e612097981e601e601e67980798f300f37980020462f7dd4c079bcc00088b0b6622c0f3079d936,0x0,0x0,0x210008400805008148004020108002200080ee3,0x0,0x0,0x240842240481,0x240800240481,0x240842240481,0x240842240481,0x2418c4240481,0x2418c6240481,0x2418c4240481,0x240800240481,0x242948240501,0x2439cc240501,0x242948240501,0x240842240481,0x2080082040081002080082002080402008050e4,0x0,0x0,0x0,0x0,0x0,0x240842240481,0x240800240481,0x240842240481,0x240842240481],
[0x2418c4240481,0x2418c6240481,0x2418c4240481,0x240800240481,0x242948240501,0x2439cc240501,0x242948240501,0x240842240481,0x4000100040081002080002002080402008040e4,0x441090240481,0x40010240481,0x441090240481,0x40010240481,0x842110240501,0x842110240501,0x842110240501,0x40010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10942 : TreeBound (n := 4) 106 (programCode 0x4c2907606e) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8020200404008100208028200208060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_10943 : TreeBound (n := 4) 106 (programCode 0x4c2907606f) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x140430204481,0xa0002800804402118004200100c82020080ce3,0x140430204481,0x0,0x0,0xa0002800000002008004200108002000080ce3,0x0,0xa0002800080402018004200108002002080ce3,0x1414b0210481,0x90002800000002008004200100401000080ca3,0x1414b0210481,0x140410200481,0x142530220501,0xa0002804020402818004200100402100084ce3,0x142530220501,0x140430204481,0x0,0x0,0x441090210481,0x0,0x0,0x441090208481,0x16c8000f30f3016c80f300f33cc03ccf300f3f3003cfcc001023003cc02046001ed98001ed9844e6d6,0x441090208481,0x1e6f30097fe600f301e601e67980798f300f3f3000f6cc2065530079807b66001f164003db307b8276,0x441090210481,0x441090210481,0x441090210481,0x441090210481,0xc43190220501],
[0xc43190230501,0xc43190220501,0x441090210481,0x0,0x140430204481,0x120004800000004008004200100002020080ce3,0x140430204481,0x0,0x0,0x0,0x0,0x0,0x1414b0210481,0x2b962f600000572c5ec0000002b962f600000572c5ec000000572c5ec000000ae58bd80000159fd800000000000002b3fb01bb4ccc000acfeeb3fb00000567f759fd800006c1f382c99ad80000ad0427f6000567f759fd8000567fb67f6000159fed9fd80000ad0427f600002b3fb00567f600567f60000000ad145fd80000056800cfec000acfec0567f600acfec159fd8015a004fc708103f2b,0x1414b0210481,0x140410200481,0x142530220501,0x0,0x142530220501,0x140430204481,0x0,0x44580007980001e601e601e63cc03ccf300f3f3084e7cc0000f3003cfcc352800079800007983cddc6,0x1004040140081002080006002000c00028140e4,0x445ad907980001e601e601e63cc03ccf300f3f3085155c0000f3003cfcda1b364079800081183cddc6,0x0,0x0,0x25f800079bcc025f80f300f33cc03ccf300f3f3003cfcc003db3003cc02046001ed98001ed98465356,0x0,0x3ccf301119cc01e601e601e67980798f300f3f3000f6cc2083b30079807b66001f164003db307b8276,0x1000040040081002080002002000400408040e4,0x1040049240081002080042002008400208058e4,0x0],
[0x108004a240081002080082002010400408050e4,0x0,0x0,0x1000040040081002080002002000400008040e4,0x408c0010237981e601e601e67980798f300f3f303cc3cc111e8b00799e61e60798b65f530f30799c76,0x0,0x0,0x220008800805008148004020108002200080ee3,0x0,0x0,0x240842240481,0x240800240481,0x240842240481,0x240842240481,0x2418c4240481,0x2418c6240481,0x2418c4240481,0x240800240481,0x242948240501,0x2439cc240501,0x242948240501,0x240842240481,0x0,0x0,0xf303cc0000f300001e63cc1e60f300000000001023079c08c0f307981e9cc003db3000f6cc001e68a925,0x0,0x0,0x441082240481,0x40000240481,0x441082240481,0x40000240481,0x40004240481],
[0x40000240481,0x40004240481,0x40000240481,0x842108240501,0x842108240501,0x842108240501,0x40000240481,0x0,0x0,0x0,0x0,0x0,0x240842240481,0x240800240481,0x240842240481,0x240842240481,0x2418c4240481,0x2418c6240481,0x2418c4240481,0x240800240481,0x242948240501,0x2439cc240501,0x242948240501,0x240842240481,0x0,0x0,0x0,0x0,0x0,0x240842240481,0x40000240481,0x240842240481],
[0x40000240481,0x40004240481,0x40000240481,0x40004240481,0x40000240481,0x40008240481,0x40008240481,0x40008240481,0x40000240481,0x441090240481,0x40010240481,0x441090240481,0x40010240481,0x842110240501,0x842110240501,0x842110240501,0x40010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_11088 : TreeBound (n := 4) 106 (programCode 0x4c29076070) := by
  conv in programCode _ => reduce
  refine prepared_bound exceptionalCheck exceptionalCheck_sound (fuel := 3)
    (a := List.flatten [
[0x8020200804008100208028200208060200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_9744 : TreeBound (n := 4) 106 (programCode 0x4c290760) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part012_9745 part012_9906 part012_9971 part012_10180 part012_10373 part012_10518 part012_10519 part012_10712 part012_10713 part012_10714 part012_10715 part012_10828 part012_10829 part012_10942 part012_10943 part012_11088

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part012_0 : TreeBound (n := 4) 106 (programCode 0x4c2907) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part012_1 part012_770 part012_1843 part012_2964 part012_4293 part012_5062 part012_5063 part012_5912 part012_5913 part012_5914 part012_5915 part012_5916 part012_5917 part012_6942 part012_7967 part012_9744

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned012 : TreeBound (n := 4) 106 [((0,0),⟨1,1,false⟩),((1,0),⟨2,0,false⟩),((2,0),⟨2,1,true⟩)] := part012_0
open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem zero_one_return_2_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 0 .right))
    (h2 : M 2 0 = some (some 2, Stmt.write 1 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 106 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,0,false⟩),((2,0), ⟨2,1,true⟩)] := by
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
  rcases partitioned012 M hm with h | h
  · exact h
  · exact (h halts).elim

end BeaverBound


/- Exact residual adapter: Hanan Beer (@hananzlt).
Residual specification and freeze reduction: @pageman, PR6963, adapting
@henry10101001. All existing verifier and certificate attribution above is retained.
This proves only the named auxiliary return-state branch. -/
open Turing Turing.BusyBeaver
theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H2_R1.H3 := by
  intro M h0 h1 h2 hRun _hUsed _hForm _hMissing _hLoop hHalts
  have stopped := BeaverBound.zero_one_return_2_machine M h0 h1 h2 hHalts
  change M.multiStep (Machine.init []) 107 = none at stopped
  obtain ⟨q,t,live⟩ := hRun
  rw [live] at stopped
  contradiction
