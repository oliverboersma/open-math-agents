/- Standalone proof component for the one/zero-write Busy Beaver family.
This proves only return states 3. -/
import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1

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
107 steps. The new bit-mask tests imply the original verifier checks. Nonhalting leaves use finite-automata reduction: a DFA summarizes
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

theorem flip_move (c : Position n) (m : Move n) :
    (c.move m).flip = c.flip.move m.flip := by
  cases m with
  | mk q a d => cases d <;> rfl

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

theorem view_start (n : ℕ) [NeZero n] : (start n).view = Machine.init [] := rfl

def Move.command (m : Move n) : Option (Option (Fin n) × Stmt Symbol) :=
  some (some m.state, Stmt.write m.write (if m.left then Dir.left else Dir.right))

def ongoing [NeZero n] (M : MachineOf n) (k : Key n) : Option (Move n) :=
  match M k.1 k.2 with
  | some (some q, ⟨b, .left⟩) => some ⟨q, b, true⟩
  | some (some q, ⟨b, .right⟩) => some ⟨q, b, false⟩
  | _ => none

theorem ongoing_command [NeZero n] (M : MachineOf n) (k : Key n) (m : Move n)
    (h : ongoing M k = some m) : M k.1 k.2 = m.command := by
  rcases m with ⟨q, a, d⟩
  unfold ongoing at h
  split at h <;> simp_all [Move.command, Move.mk.injEq]

theorem step_move [NeZero n] (M : MachineOf n) (c : Position n) (m : Move n)
    (h : ongoing M (c.state, c.head) = some m) :
    M.step c.view = some (c.move m).view := by
  have he := ongoing_command M (c.state, c.head) m h
  change M c.state c.head = m.command at he
  cases m with
  | mk q a d =>
    cases d <;> simp [Position.view, Machine.step, he, Move.command, Position.move,
      Tape.write, Tape.move, mk_push]

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

theorem matches_empty [NeZero n] (M : MachineOf n) : Matches M [] := by
  intro k m h
  contradiction

theorem matches_add [NeZero n] {M : MachineOf n} {tb : Program n} {k : Key n} {m : Move n}
    (hm : Matches M tb) (h : ongoing M k = some m) : Matches M ((k, m) :: tb) := by
  intro k' m' hh
  by_cases e : k' = k
  · subst k'
    simp [Program.get] at hh
    simpa [← hh] using h
  · apply hm k' m'
    simpa [Program.get, e] using hh

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

theorem TapeDFA.blank (D : TapeDFA) : D.next 0 0 = 0 := by
  apply Fin.ext
  simp [TapeDFA.next]

def TapeDFA.read (D : TapeDFA) (xs : List Symbol) : Fin D.size :=
  xs.foldr D.next 0

theorem TapeDFA.read_push (D : TapeDFA) (a : Symbol) (xs : List Symbol) :
    D.read (push a xs) = D.next a (D.read xs) := by
  unfold push
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    exact D.blank.symm
  · rfl

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

theorem allFin {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (a : Fin n) : p a = true := (List.all_eq_true.mp h) a (by simp)

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

theorem Reads.push {cert : Certificate n} {p q : Node cert} {a : Symbol} {xs : ListBlank Symbol}
    (he : cert.edge p a q = true) (h : Reads cert q xs) : Reads cert p (xs.cons a) :=
  .step (by simpa using he) (by simpa using h)

theorem Reads.pop {cert : Certificate n} {p : Node cert} {xs : ListBlank Symbol} {a : Symbol}
    (h : Reads cert p (xs.cons a)) : ∃ q, cert.edge p a q = true ∧ Reads cert q xs := by
  cases h with
  | done => exact ⟨none, rfl, .done _⟩
  | step he hr => exact ⟨_, by simpa using he, by simpa using hr⟩

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

theorem holes_add (tb : Program n) (k : Key n) (m : Move n) :
    holes ((k, m) :: tb) = (holes tb).erase k := by
  ext k'
  simp only [holes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  rw [Program.get]
  by_cases e : k' = k <;> simp [e]

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

theorem upper_cannot_stop [NeZero n] {M : MachineOf n} {tb : Program n} {limit : ℕ}
    (hm : Matches M tb) (h : ¬ CanStop tb (start n)) : Upper M limit := by
  right
  intro halts
  obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp halts
  apply cannot_stop_run hm (start n) h (k + 1)
  rwa [view_start]

abbrev TreeBound [NeZero n] (limit : ℕ) (tb : Program n) : Prop :=
  ∀ M : MachineOf n, Matches M tb → Upper M limit

theorem branch_bound [NeZero n] {limit : ℕ} {tb : Program n} {k : Key n}
    (h : firstMissing tb limit (start n) = some k)
    (children : ∀ m, TreeBound limit ((k, m) :: tb)) : TreeBound limit tb := by
  intro M hm
  cases hs : ongoing M k with
  | none =>
    left
    simpa only [view_start] using firstMissing_stops hm limit (start n) h hs
  | some m => exact children m M (matches_add hm hs)

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

namespace BeaverBound

def forceNat {α : Type} (v : ℕ) (f : ℕ → α) : α :=
  match v with
  | 0 => f 0
  | k + 1 => f (k + 1)

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

theorem state_nodeId_lt (cert : Certificate n) (q : Fin n) (l : Fin cert.dfa.size) :
    nodeId cert (some (q,l)) < n * cert.dfa.size := by
  have hh := Nat.mul_le_mul_right cert.dfa.size (Nat.succ_le_of_lt q.isLt)
  simp only [Nat.succ_mul] at hh
  have hl := l.isLt
  simp only [nodeId]
  omega

theorem nodeId_lt (cert : Certificate n) (p : Node cert) :
    nodeId cert p < n * cert.dfa.size + 1 := by
  rcases p with _ | ⟨q,l⟩
  · simp [nodeId]
  · exact Nat.lt_succ_of_lt (state_nodeId_lt cert q l)

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
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkGenerated special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkChoice tb (v-17) then some rest else none

theorem generated_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 107 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkGenerated special fuel tb a = some b) :
    TreeBound 107 tb := by
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
        cases hFirst : firstMissing tb 107 (start 4) with
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

/- This is only a data preparation pass. The result is checked again by
`checkPrepared`, including every branch and every certificate. No correctness
assumption about this pass is used by the soundness theorem. -/
def prepareCertificates : ℕ → Program 4 → List ℕ → List ℕ →
    Option (List ℕ × List ℕ)
  | 0, _, rest, acc => some (rest, acc)
  | _ + 1, _, [], _ => none
  | fuel + 1, tb, v :: rest, acc =>
    if v = 0 then
      match firstMissing tb 107 (start 4) with
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
      match firstMissing tb 107 (start 4) with
      | none => none
      | some k => (moves 4).foldlM (fun xs m => checkPrepared special fuel ((k,m)::tb) xs) rest
    else if v < 17 then if special v tb then some rest else none
    else if checkCertificateBits tb (v-17) then some rest else none

theorem prepared_bound (special : ℕ → Program 4 → Bool)
    (hspecial : ∀ v tb, special v tb = true → TreeBound 107 tb)
    {fuel : ℕ} {tb : Program 4} {a b : List ℕ}
    (hCount : (holes tb).card ≤ fuel) (h : checkPrepared special fuel tb a = some b) :
    TreeBound 107 tb := by
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
        cases hFirst : firstMissing tb 107 (start 4) with
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
    (h : firstMissing tb 107 (start 4) = some k)
    (p0 : TreeBound (n := 4) 107 ((k,⟨0,0,false⟩)::tb))
    (p1 : TreeBound (n := 4) 107 ((k,⟨0,0,true⟩)::tb))
    (p2 : TreeBound (n := 4) 107 ((k,⟨0,1,false⟩)::tb))
    (p3 : TreeBound (n := 4) 107 ((k,⟨0,1,true⟩)::tb))
    (p4 : TreeBound (n := 4) 107 ((k,⟨1,0,false⟩)::tb))
    (p5 : TreeBound (n := 4) 107 ((k,⟨1,0,true⟩)::tb))
    (p6 : TreeBound (n := 4) 107 ((k,⟨1,1,false⟩)::tb))
    (p7 : TreeBound (n := 4) 107 ((k,⟨1,1,true⟩)::tb))
    (p8 : TreeBound (n := 4) 107 ((k,⟨2,0,false⟩)::tb))
    (p9 : TreeBound (n := 4) 107 ((k,⟨2,0,true⟩)::tb))
    (p10 : TreeBound (n := 4) 107 ((k,⟨2,1,false⟩)::tb))
    (p11 : TreeBound (n := 4) 107 ((k,⟨2,1,true⟩)::tb))
    (p12 : TreeBound (n := 4) 107 ((k,⟨3,0,false⟩)::tb))
    (p13 : TreeBound (n := 4) 107 ((k,⟨3,0,true⟩)::tb))
    (p14 : TreeBound (n := 4) 107 ((k,⟨3,1,false⟩)::tb))
    (p15 : TreeBound (n := 4) 107 ((k,⟨3,1,true⟩)::tb))
    : TreeBound (n := 4) 107 tb := by
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
private theorem part103_1 : TreeBound (n := 4) 107 (programCode 0x4e2b0771) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0xc00030080022010080082002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3 : TreeBound (n := 4) 107 (programCode 0x4e2b077211) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4400410080082010080082002000820020814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4 : TreeBound (n := 4) 107 (programCode 0x4e2b077212) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x400410080002010080082002000020400814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5 : TreeBound (n := 4) 107 (programCode 0x4e2b077213) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4400410080082010080082002001020040814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6 : TreeBound (n := 4) 107 (programCode 0x4e2b077214) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x4400410080082010000880022000820020814e3,0x400410080002010000080402000020000814e3,0x4400410080082010001080042000020040814e3,0x400410080002010000080002000020000814e3,0x10400410080002010002080082002020080814e3,0x400410080002010000080002000020000814e3,0x10400410080002010004080102004020100814e3,0x0,0x180d02184642,0x180502084642,0x180d02184642,0x180502084642,0x180d02184642,0x180902184642,0x180d02184642,0x180902184642,0x0,0x0,0x180502084642,0x0,0x0,0x182102084642,0x400410040001010000081002000020000814e3,0x182102084642,0x0,0x4459e60f300000f303cc0f30f303cc3cc03ccf3445a22c1e600000007991167983cc00007983cc3cb6,0x3cc1e60f307980f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x0,0x0,0x3ccf300f33cc00f3408c0f30f303cc3cc03ccf4ed9a22c1e6000798079911a4583cc3cc07983ccb636],
[0x0,0x0,0x44580011160000f303cc0f30f303cc3cc03ccf3079a22c1e600000007991167983cc00007983cc3cb6,0x0,0x4459e611160000f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x4459e60f303cc0f303cc0f30f303cc3cc03ccf3445a22c1e600000007991167983cc00007983cc3cb6,0x408c00102300010233cc0f30f303cc3cc03cd6c879a22c1e601e60007991167983cc07987983cc3cb6,0x3cc1e60f303cc0f303cc0f30f303cc3cc03ccf3445a22c1e600000007991167983cc00007983cc3cb6,0x0,0x0,0x180504084222,0x180504084222,0x180504084222,0x180504084222,0xc0003002010004400800c200101008040201e4,0xc00030002100084008040200101010040603e4,0x180504084222,0x0,0x0,0x0,0x180504084222,0x0,0x0,0x0,0x0,0x0,0x445800111600016c83cc0f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x180504084222,0x180504084222,0x180504084222],
[0x180504084222,0x0,0xc00030002100084010080400101010040603e4,0x180504084222,0x0,0x0,0x0,0x180504084222,0x0,0x16c800111600016c83cc03cc00222c3cc03cc079802634de6007980079897e0003cc0f307983cc3446,0x0,0x400410040001010000082002000020000814e3,0x0,0x0,0x4459e60f300000f303cc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x1000080004000200010000800010000c000080010000200040000800100000800400120001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x4459e60f300000f312fc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x3ccf300f33cc00f3408c0f30f303cc3cc03ccf34459e6097e0000f307991167983cc0f307983cc3cb6,0x4459e60f300000f312fc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x0,0x44580011160000f303cc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x3d39800f4e6000f4e9cc0f30f303cc3cc03cd6cc459e6097e01e60007991167983cc07987983cc3cb6,0x1200000004800200012000000010000c000080010000200040000800100000800400120001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x10100000010100000101000000101004000080010000080040000800100000800400020000400000008000a00004000000080022001000028000000200002000200010000f93a8,0x4459e60f303cc0f303cc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x408c00102300010233cc0f30f303cc3cc03cd6cc459e6097e01e60007991167983cc07987983cc3cb6,0x3cc1e60f303cc0f303cc0f30f303cc3cc03ccf34459e6097e00000007991167983cc00007983cc3cb6,0x0,0x400410080002010000082002000020000814e3,0x0],
[0x7983cc1f53000b64001f530007d4c001ed980799e601e63cc03cc00003cc0000f4e6001e703d95,0x402080002000040081002000021000814e3,0x1e60f307a730012fc003db3000f6cc003d3980799e601e63cc03cc00003cc0000f4e6001e722395,0x408080002000040081002000021000814e3,0x3cc1e60f3f300408c00f3f3003cfcc00f37980799e601e63cc03cc00003cc0000f4e6001e77d595,0x400080002000040081002000021000814e3,0xf307983ccf3007d4c01e6f30079bcc01e67980799e601e63cc03cc00003cc0000f4e6001e703d95,0x410080002010040081002000021000814e3,0x1e60f30798f301e9cc0000f300003cc00007980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0,0x7983cc1e60f303cfcc0000f300003cc00007980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0,0xf307983cc0f30f33cc03ccf300f33cc03cc7980799e601e63cc03cc00003cc0000f4e6001e8e9d95,0x400080002000040081002000021000814e3,0x40200408080202008040081002040021000854e3,0x1e600f37983cc0000f300003cc1e607980799e601e63cc03cc00003cc0000f4e6001e703d95,0x0,0x180508084222,0x180508084222,0x180508084222,0x180508084222,0x0,0x180908484222,0x180508084222,0x180908484222,0x0,0x0,0x180508084222,0x0,0x0,0x182108084222,0x0],
[0x182108084222]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_135 : TreeBound (n := 4) 107 (programCode 0x4e2b077215) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10400410080002010080082002002020080814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_136 : TreeBound (n := 4) 107 (programCode 0x4e2b077216) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x140003008020200408040a00010442008040304]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_137 : TreeBound (n := 4) 107 (programCode 0x4e2b077217) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10400410080002010080082002004020100814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_138 : TreeBound (n := 4) 107 (programCode 0x4e2b077218) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x445800111600016c83d49a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0x16c800111600016c8000408c00408c000408cf30000b64001f53000079bea6000fa98003cc1e610856,0x0,0x180d03188642,0x180d01188642,0x180100088442,0x180d01188642,0x180d03188642,0x180902188442,0x180902188442,0x180902188442,0x4400410001080050008080202001020040814e3,0x16c800111600016c800003cc0f33cc03cc3cc03cc007d4c00003cc0079bcc0000f379803cc1e610856,0x180d03188642,0x0,0x14400410001080050020080802010020040814e3,0x40002000107f080000004200000810800000004040000048780000200400000280000080002010f00020000800100100000100000200021000f00204000001000008001002884aba7,0x14400410001080050040081002014020040814e3,0x0,0x16c800111600016c80007d4c00222c0007d4cf30000b64001f53000079bea6000fa98003cc1e610856,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180d03188642,0x180d02188442,0x180d02188442,0x180d02188442,0x10400410002000090008080202002020080814e3,0x0],
[0x180901088442,0x0,0x10400410002000090020080802010020080814e3,0x0,0x10400410002000090040081002010020080814e3,0x0,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180903188642,0x180902188442,0x180902188442,0x180902188442,0x0,0x0,0x180901088442,0x0,0x0,0x0,0x0,0x0,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180d03188642,0x180902188442,0x180902188442,0x180902188442],
[0x10400410004000110008080202004020100814e3,0x0,0x180901088442,0x0,0x10400410004000110020080802010020100814e3,0x0,0x10400410004000110040081002010020100814e3,0x0,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180903188642,0x180902188442,0x180902188442,0x180902188442,0x400410000000010008080202000020000814e3,0x0,0x180901088442,0x0,0x400410010000410020080802010020400814e3,0x0,0x400410000000010040081002000020000814e3,0x0,0x0,0x4469160f300000f303d49a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0x3cc1e60f307980f30b70663000f6cc000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x0,0x0,0x0,0x0],
[0x0,0x0,0x800020000100004080002000104400100804e4,0x84002102810020408004600010440010182ce4,0x4469160f31e600f30b70663000f6cc000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x880022030100404080186000104400106934e4,0x820020000100004080002000104400100804e4,0x900024020100804080006000104400100804e4,0x4467300f35b200f303d49a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0xa00028040101004080006000104400100804e4,0x0,0x16c8000f37980104160f33cc0f33cc00f33ccf30000b64007a73000079bcc7980fa98003cc1e833456,0x80402010810020408004200010440010182ce4,0x0,0x0,0xc0002580810020408004200010440010182ce4,0x81002040810020408004200010440010182ee4,0xc0002180810020408004200010440010182ce4,0x82002080810020408004200010440010182ce4,0x90002000810020408004200010440010182ce4,0x84002100810020408004200010440010182ce4,0x84002010810020408004200010440010182ce4,0x88002200810020408004200010440010183ce4,0x86002500810020408004200010440010182ce4,0x90002400810020408004200010440010182ce4,0x4467300f31e600f3003ccf300f33cc00f33ccf3007ba2c007a73000079fb8fc41ed98003cc1e833d56,0xa0002800810020408004200010440010186ce4,0x445800111600016c83d49a3000f6cc000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x0,0x0,0x804020110100404080082000104400102834e4,0x0],
[0x0,0xc00026810100404080082000104400102834e4,0x810020410100404080082000104400102836e4,0xc00022810100404080082000104400102834e4,0x820020810100404080082000104400102834e4,0x900020010100404080082000104400102834e4,0x84002101010040408008200010440010283ce4,0x880020110100404080082000104400102834e4,0x880022010100404080082000104400102834e4,0x8a0026010100404080082000104400102834e4,0x900024010100404080082000104400102834e4,0x0,0xa00028010100404080082000104400102874e4,0x0,0x4459e60f300000f303d3a73000f6cc00003ccf3079a22c0000f3000079fb69cc1ed98003cc1e611156,0x0,0x0,0x0,0x44691611160000f37d549a3000f6cc00003ccf307a952c0000f3000079fb69cc1ed98003cc1e611156,0x3ccf300f33cc00f340949a3000f6cc000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x44673011160000f37d549a3000f6cc00003ccf307a952c0000f3000079fb69cc1ed98003cc1e611156,0x3ccf300f33cc00f37d549a3000f6cc00003ccf307a952c0000f3000079fb69cc1ed98003cc1e611156,0x25f87983cc0000f303cfd398f3f3f300003ccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x1e9cc003d39800f4e9cfd3981f53f307983ccf30798b640002d9000079fb66001ed9f983cc1e610f46,0x0,0x1ed98003ea6000f6cfcfd3983db3f316c83ccf30798b640002d9000079fb66001ed9f983cc1e610f46,0x4470ae03cde600f303d8663000f3f300003ccf307a952c0000f3000079fb69cc1ed98003cc1e6110f6,0x2046000408c0010233cfd3981f53f307983ccf30798b640002d9000079fb66001ed9f983cc1e610f46,0x4467300f31e600f303d49a3000f6cc00003ccf307a952c0000f3000079fb69cc1ed98003cc1e611156,0x0,0xc00030020100804080006000104400100804e4,0x0],
[0x4459e60f300000f303d3a73000f6cc00003ccf3079a22c0000f3000079fb69cc1ed98003cc1e611156,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x25f87983cc0000f3000b6b98f3f3f300003ccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x1e9cc003d39800f4e60b6b9800f3f300003ccf307983cc0002d9000079fb66001ed98003cc1e610f46,0x0,0x0,0x4469160f31e600f303d3a73000f6cc00003ccf3079a22c0000f3000079fb69cc1ed98003cc1e611156,0x408c00102300010230089a3000f6cc000408cf307a952c001f53000079fb69cc1ed98003cc1e611156,0x4467300f31e600f303d3a73000f6cc00003ccf3079a22c0000f3000079fb69cc1ed98003cc1e611156,0x4000000014400a200000008000080000001000000004000a200200000000200000004000008010000020040000100100000100400000081400000204000001008000001002086aba7,0xc00030040101004080006000104400100804e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_315 : TreeBound (n := 4) 107 (programCode 0x4e2b077219) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x60c0d0210481,0x424010210481,0x60c0d0210481,0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03ccf34459e601e60000000b6511688b00000007983cc3cb6,0xf30f30f303cc0f312fc03ccf303cc3cc03cc000f307991160000f3079897e0f30000f307983cc33b6,0x0,0x0,0x0,0xf30f30f303cc0f312fc03ccf303cc3cc03cc00798079fb66000798079897e0f30003cc07983ccad36,0x0,0x0,0x0,0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03ccf3445a22c1e60000f30b6511688b0000f307983cc3cb6,0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03ccf34459e6097e0000000b6511688b00000007983cc3cb6,0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e600097e1e601e600079897e0f300007987983cc33b6,0x0,0x0,0x414090210481,0x102002048020200408040a00018442008040304,0x414090210481,0x0,0x3ccf300f31e600f37d549a300003cc00003ccf307a952c0000f30000b6ca9a4580798003cc1e6110c6,0xf37980f31e600f37980408c00408c000408cf30000b64001f53000079bea60f3fa98003cc1e610856,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x82002080810020408004200012040010182ce4,0x3ccf300f33cc00f37d58663000f6cc000408cf307b0eac001f530000b7075c2b8fa98003cc1e611156,0x820020810100404080082000120400102834e4,0x3ccf300f33cc00f37d549a3000f6cc00003ccf307a952c0000f30000b6ca9a4580798003cc1e611156,0x820020820100804080006000104400100804e4,0x0,0x820020840101004080006000104400100804e4,0x424010210481,0x108002108020200408040a00019048020102904,0x424010210481,0x108002208020200408040a00019048040205104,0xc44110210501,0x404010210481,0xc44110210501,0x120002808020200408040a0001c060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_364 : TreeBound (n := 4) 107 (programCode 0x4e2b07721a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x170002408020200408040a00011048020102904,0x100802018020200408040a00011048020102904,0x0,0x6084d0218481,0x6098d0218481,0x6084d0218481,0x0,0x6088d0218481,0x143002040420008408040a00011048020102b04,0x6088d0218481,0x0,0x6090d0218481,0x6098d0218481,0x6090d0218481,0x0,0x60a0d021c481,0x6098d0218481,0x60a0d021c481,0x8400200000000880082002000020400814e3,0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03cd9e2f89ed99e601e60007d4e0c90d30007a73079a268b6,0xf30f30f303cc0f312fc03ccf303cc3cc03cc000f307991160000f307a74e600f301e60f3079a25fb6,0x0,0xf30f30f303cc0f312fc03ccf303cc3cc03cc001e6079897e0001e607a74e600f307980f3079b18fb6,0x0,0xf30f30f303cc0f312fc03ccf303cc3cc03cc00798079fb6600079807a74e600f3003ccf3079a2d936,0x0,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03ccf3445a22c1e60000f307d4e0460f301e60f3079a268b6],
[0x0,0x3cc1e60f307980f312fc0f30f303cc3cc03cd023799e6f4e600000007d4e0460f300000f3079a268b6,0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e600097e1e601e60007a74e600f30007a73079a25fb6,0x0,0x0,0x148002108020200408040a00011048020102904,0x102002048020200408040a00011048020102b04,0x148002108020200408040a00011048020102904,0x0,0x3ccf300f33cc00f37fab8f301e63cc07983ccf3079a9c40002d900007d4e0bf8f379800f3079a33d56,0x82002080090002408004200010840020112ce4,0x10ca89adae7e60079800f311494201e60000799f530079bcc00f3f3003d032843cc0f30799e601e68a8c5,0xf37980f31e600f379807d4c00222c0007d4cf30000b6401e6f300007a73003db379800f3079b26456,0x3ccf300f33cc00f3800412f0f303cc00f33ccf30d08444007a7300007d4f4202d379800f3079a33d56,0x0,0x109cfaec801e60079807987b93900f300003ccf3f30079bcc00f3f3003d027203cc79807980001e68a8c5,0x0,0x0,0x82002080810020408004200010840020102ce4,0x82002080890002408004600010840020112ce4,0x82002081010040408008200010840020303ce4,0x82002080810000408000200010840020102ce4,0x82002082010080408000600010840020102ce4,0x0,0x82002084010100408000600010840020102ce4,0x140002008020200408040a00011048020102904,0x108002108020200408040a00011048020102904,0x140802018020200408040a00011048020102904,0x108002208020200408040a00011048020107904,0x17c002008020200408040a00011048020102904,0x120002408020200408040a00011048020102904,0x14c002008020200408040a00011048020102904],
[0x120002808020200408040a00011048020106904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_429 : TreeBound (n := 4) 107 (programCode 0x4e2b07721b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x400410080002010080082002010020400814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_430 : TreeBound (n := 4) 107 (programCode 0x4e2b07721c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x12fc0010230001a943cc03ccf303cc3cc03cc000f307991160000f307b67e6007983cc1e60f3812d56,0x0,0x12fc0010230001a943cc03ccf303cc3cc03cc001e6079897e0001e607b67e6007983cc1e60f3812d56,0x0,0xf307990230001a943cc03ccf303cc3cc03cc00798079fb6600079807b67e60079803cde60f3812d56,0x0,0x0,0x0,0x0,0x400000003044000020000000080c000000c00000001000082204000208810000001001000080004000200020001000020001004000000810400002040000010008000010020862ba7,0x0,0x231010000800000001080000001200040001000100004000400008001000008006202200100000000442822000000000000820021010020080000200000000200010010807dfa8,0xf6cc010230001a943cc03ccf303cc3cc03cc1e600097e1e601e60007b67e600798007b660f3812d56,0x400000003040500020000400080c000000c00000041000080304000200c1000000101000008004000020020000100020000100400000081c000002040000010080000010020862ba7,0x0,0xf30798f307980f30b6403ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f3812d56,0x0,0x0,0x0,0x0,0x0,0x0,0xf33cc111600016c83cc03ccf303cc3cc03cc00798079fb6600079807b67e60079803cde60f381a6d6,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0xf6cc0111600016c83cc03ccf303cc3cc03cc1e600097e1e601e60007b67e600798007b660f3812d56,0x0,0xf6cc0111600016c83cc03ccf303cc3cc03cc3cc00088b1e603cc0007b67e60079801e7e60f3812d56,0x0,0x0,0x1e60f307987980f312fc0798f301e63cc03cc0025f800097e3cc0f307b661e60f384e41e60f353dc26,0x0,0x1e60f307987980f312fc0798f301e63cc03cc0025f80011163cc1e607b660f30f381181e60f344ac26,0x0,0xf30f30f303cc0f312fc03ccf303cc3cc03cc00798079fb6600079807b67e60079803cde60f381c536,0x0,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x0,0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e600097e1e601e60007b67e600798007b660f3814bb6,0x0,0x0,0x0,0x610490204481,0x411090210481,0x610490204481,0x12fc0011160000f6cc007d4c00222c0007d4cf30000b6400f3f300007b66003d39f9801e60f3812d56,0x0,0x0,0x0,0x0,0x411090210481,0x411090210481],
[0x411090210481,0x410090200481,0x612090238481,0x411090210481,0x612090238481,0xc00022040101004080006000110400402030e4,0xf33cc0f33cc00f3408c03ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f381a6d6,0x0,0x610490204481,0x411090210481,0x610490204481,0x0,0x0,0x0,0x0,0x0,0x411090210481,0x411090210481,0x411090210481,0x410090200481,0x612090238481,0x411090210481,0x612090238481,0xc00022040101004080006000110400402030e4,0x0,0x0,0x820020800900024080082000110400402134e4,0x0,0x1e6798079bcc00f379808118003ea60007d4cf3003cfcc01eabf00007b67e600f38145ae60f3465566,0x0,0x0,0x0],
[0x0,0x0,0x82002080810020408004200011040040303ce4,0x820020810100024080082000110400402034e4,0x820020810100404080082000110400402034e4,0x820020810100404080082000110400402034e4,0x820020820100804080006000110400402034e4,0x0,0x820020840101004080006000110400402034e4,0xf300011160000f303cc03ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f3812d56,0x108002108020200408040a00011048040205104,0xf307991160000f30b6403ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f3812d56,0x108002208020200408040a00011048040205104,0x489d800820b000f303cc0f30f301e63cc03ccf3079a22c1e64bf00007d4e0460f381181e60f3447626,0x120002408020200408040a00011048040205104,0x0,0xc40510230501,0xc43110230501,0xc40510230501,0x0,0x0,0xf3f300f3f30016c8001e9cc01e9cc001e9ccf30000b641e60f300007b67e60079f9801e60f3831356,0x0,0x0,0xc41110230501,0xc42110230501,0xc41110230501,0xc43110230501,0xc42110230501,0xc42110230501,0xc42110230501,0xc43110230501],
[0x120002808020200408040a00011048040205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_559 : TreeBound (n := 4) 107 (programCode 0x4e2b07721d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x50c050220481,0x424010220481,0x50c050220481,0x0,0x52c041220481,0x424004220481,0x52c041220481,0x424004220481,0x634082220481,0x424000220481,0x634082220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0xc64188220501,0x424000220481,0xc64188220501,0x0,0x614090220481,0x400400080002010080082002020020800814e3,0x614090220481,0x0,0xc00400100820030880082002020020800814e3,0x400400000000410080082002020020800814e3,0x1400400201020050880082002020020800814e3,0x10400402010002010080082002020020800814e3,0x2400400402080092080082002020020800814e3,0x0,0x4400400804080112080082002020020800814e3],
[0x0,0x0,0x82002080810020408004200010840020102ce4,0x10400402010000410080082002020020800814e3,0x820020810100404080082000110400402034e4,0x20400404020100814080082002020020800834e3,0x400400000002010080082002020020800814e3,0x0,0x400400000002010080082002020020800814e3,0x424010220481,0x108002108020200408040a0001e070080402904,0x424010220481,0x108002208020200408040a0001c060100805104,0xc44110220501,0x404010220481,0xc44110220501,0x120002808020200408040a0001c060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_608 : TreeBound (n := 4) 107 (programCode 0x4e2b07721e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40c050208481,0x424010200481,0x40c050208481,0x0,0x40c041208481,0x424004200481,0x40c041208481,0x404000200481,0x3cc1e60f307980f312fc0f30f303cc3cc03cd8b51e9e6097e01e600097e3165f7800081183cc1e9cb6,0x404000200481,0x109cfaec801e60079807d4c2139f300003cc00f301e679803ccf300f33d027203cc0000799e601e68a8c5,0x0,0x424004200481,0x0,0x424004200481,0x0,0x20080404080102004020080802020020800834e3,0x404000200481,0x408080002000040081002000020000814e3,0x0,0x414090210481,0x102002048020200408040a00014060080402304,0x414090210481,0x0,0x0,0x820020800900024080102000120400804124e4,0x109cf9adae7e60079800f3111bb201e60000799f530079bcc00f3f3003cfd7643cc00007983cc1e68a8c5,0x820020801100044080102000120400804124e4,0x1e6f3003cfcc00f37d4c0798f300f307983ccf307983cc0002d9000088b1e601e679807983cc1f6f46,0x0,0x109cfaec801e60079807987b93900f300003ccf3f30079bcc00f3f3003d027203cc0000799e601e68a8c5],
[0x0,0x0,0x82002080810020408004200012040080502ce4,0x820020820900024080106000120400804124e4,0x820020810100404080082000120400806034e4,0x820020820900824080106000120400804124e4,0x820020820100804080006000120400804024e4,0x0,0x820020840101004080006000120400804024e4,0x424010200481,0x108002108020200408040a00014060080402904,0x424010200481,0x108002208020200408040a00014060080407104,0xc44110220501,0x404010200481,0xc44110220501,0x120002808020200408040a00014060080406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_657 : TreeBound (n := 4) 107 (programCode 0x4e2b07721f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x50c050220481,0x424010220481,0x50c050220481,0x410080002010080082002040021000814e3,0x614090220481,0x0,0x634081220481,0x404004220481,0x634081220481,0x404004220481,0x424002220481,0x404000220481,0x424002220481,0x0,0x404004220481,0x10200204802020040104082001184c020102b04,0x404004220481,0xf33cc0f33cc00f3408c03ccf303cc3cc03cc0798007b67e600798007b67e60079f9801e60f381a6d6,0x404008220481,0x404000220481,0x404008220481,0xf33cc0f33cc00f3408c03ccf303cc3cc03cc3cc00088b1e603cc00088b1e603cc001f5307983ebb56,0x614090220481,0x0,0x40200410080202018000880022040021000854e3,0x0,0x40200410080202018001080042040021000854e3,0x410080002010000080002040021000814e3,0x2010410080082012002080082040021000814e3,0x410080002010000080002040021000814e3,0x4020410080082012004080102040021000814e3],
[0x0,0x0,0x0,0x0,0x0,0x10080410080002010020080802040021000814e3,0x0,0x410080002010040081002040021000814e3,0x0,0x424010220481,0x0,0x630490220481,0x401010220481,0x630490220481,0x0,0x420810220481,0x108002100420008408040a00010643008040304,0x420810220481,0x0,0x401010220481,0x400010220481,0x401010220481,0x400010220481,0x402010220481,0x400010220481,0x402010220481,0x400010220481,0x424010220481,0x0,0x40201608000a0002808004200202001100084ca3,0x421010220481,0x40200408001200048080082002040021000854e3],
[0x0,0x0,0xf6cc00f3f3000f6cc01e9cc01e9cc001e9ccf30000b641e60f3000079fb66001ed98007983cc1fb56,0x0,0x0,0x421010220481,0x400010220481,0x421010220481,0x400010220481,0x422010220481,0x400010220481,0x422010220481,0x400010220481,0xc44110220501,0x404010220481,0xc44110220501,0x0,0xd685f0220501,0x421010220481,0xd685f0220501,0x400000002000080082002040021000814e3,0x0,0x0,0x0,0x0,0x421010220481,0x400010220481,0x421010220481,0x400010220481,0xc62190220501,0x400010220481,0xc62190220501],
[0x400010220481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_754 : TreeBound (n := 4) 107 (programCode 0x4e2b077220) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x660018042200088004200208001000080ca3,0x0,0x0,0x421010210481,0x0,0x402000002000080082002000020000814e3,0x420810208481,0x0,0x420810208481,0x0,0x421010210481,0x420010200481,0x421010210481,0x420010200481,0x422010220481,0x420010200481,0x422010220481,0x420010200481,0x0,0x0,0x8400200000400880082002000020000814e3,0x0,0x8400200002000880082002000020000814e3,0x408850208481,0x0,0x408850208481,0x0,0x0,0x8400200000400880082002000020000814e3,0x8400210000400880082002010020400814e3,0x0],
[0x50a050220481,0x408850208481,0x50a050220481,0x408050200481,0x0,0x3cc1e60f303cc0f312fc0f30f303cc3cc03ccf362b9e6097e0001e6097e35283cc1e60f307983cfc26,0x1e61e607987980f312fc0798f301e63cc03cc0025f800097e3cc0f3097e0f30798d4a0f30798b69936,0x43002001902008001000000000040000024000201c100000000400020001000000100002010000002010000010080000020100400000100000000104000000800000001001087dea7,0x1e60f307987980f312fc0798f301e63cc03cc0025f80011163cc1e6088b0798798b640f307983d1426,0x1000040004000200010001000010001400008001000020004000080010000080008002000140048002000220000200000008800040004000a0022000000082000100008025aba8,0xf30f30f303cc0f312fc03ccf303cc3cc03cc00798079fb66000798088b1e603cc003db307983d6d36,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf30f30f303cc0f312fc03ccf303cc3cc03cc1e600097e1e601e600088b1e603cc00088b07983cf3b6,0x0,0x0,0x0,0xf30003cc3cc0f46c80408c01e6f30811bcc00f3000f6cc003ea6000f6cc003cdf53000f3003cde703885,0x4824000fa980011163cc0f30f303cc3cc03cc004459e611160000f3097e2d907981e60f307983cde56,0x0,0x16c8000fa980011163cc03ccf303cc3cc03cc001e6079897e0001e6088b1e603cc1e60f307983cd556,0x4825e60f3000011163cc0f30f303cc3cc03cd6cc459e601e603cc00097e2d97d4c001f5307983cddc6,0x16c8000f301e611163cc03ccf303cc3cc03cc00798079fb66000798088b1e603cc003db307983cd556,0x4825e60f3000011163cc0f30f303cc3cc03cd6cc459e6111603cc00097e2d98118001f5307983cde56,0x0,0x4825e60f3000011163cc0f30f303cc3cc03cd6cc45a22c1e603cc00097e2d98118001f5307983cde56,0x16c8000f6cc0011163cc03ccf303cc3cc03cc03cc007d4de6003cc0088b1e603cc7980f307985b3556],
[0x4824000fa980011163cc0f30f303cc3cc03ccf3445a22c1e60000f3097e2d907981e60f307983cde56,0x0,0x4825e60f3000011163cc0f30f303cc3cc03cd6cc459f531e6000000097e2d981180000f307983cde56,0x4825e60fa980011163cc0f30f303cc3cc03cc79879a0461e601e600097e2d9811800088b07983cde56,0x0,0xf30003cc0000f46c80408c0000f307983cc00f300003cfcc01e600003cc00001f53000f300001e703885,0xf33cc0f33cc00f3408c03ccf303cc3cc03ccf30000b641e60f3000088b1e603cc7980f307983ebb56,0x0,0xf30007983cc3cd6c807d4c01e6f30811bcc02d9000f6cc003ea6000f6cc003cdf53000f3003cde703885,0x10d940f300001026cc07d4c21b37307b69cc007a8d9479800007a76cc3d036503db30003cc0001e64dc35,0x10c278f303cc1026cc07d4c21b37307b69cc0079803d398003d39801e9cfcd6cbdb30003cc03cde64dc35,0x109c80f300001026cc07d4c21b37307b69cc007a730079800007a73003cfcc003db30003cc0001e64dc35,0x0,0x16c8000f30f3011163cc03ccf303cc3cc03cc00798079fb66000798088b1e603cc003db307983d4ed6,0x0,0x0,0x0,0x0,0x4824000fa980011163cc0f30f303cc3cc03ccf3445a22c1e60000f3097e2d907981e60f307983cde56,0x0,0xf30007983cc3cd6c807d4c01e6f30811bcc02d91e603cc7981e61e603cc79801f53000f379801e703885,0x16c8000f301e611163cc03ccf303cc3cc03cc1e600097e1e601e600088b1e603cc00088b07983cd556,0x10c278f303cc1026cc07d4c21b37307b69cc0079f980798798079bcc03d2a5003db30003d39801e64dc35,0x0,0x0,0x0,0x820020800900024080202000140401008144e4,0x4020200010ee080070000200000800000400008000000048770000220400000200104000004010000020040000100100000100000000041000e00204000801000000001002085aba7,0x820020801100044080202000140401008144e4,0x0,0x0,0x0],
[0x0,0x0,0x82002080810020408004200014040100906ce4,0x820020840900024080206000140401008144e4,0x82002081010040408008200014040100a074e4,0x820020840901024080206000140401008144e4,0x820020820100804080006000140401008044e4,0x0,0x820020840101004080006000140401008044e4,0x0,0x25f80007980000f303cc0798f301e600003ccf307983cc0004bf000097e1e60798b640f307983cdc76,0x421010210481,0x0,0x0,0x420810208481,0x25f8f307981e60f30003d39800f4e6001e9ccf307983cc1e64bf000097e1e60798b640f307983cdc76,0x420810208481,0x0,0x421010210481,0x420010200481,0x421010210481,0x420010200481,0x422010220481,0x420010200481,0x422010220481,0x420010200481,0x108002108020200408040a00014060100805104,0x0,0x4825e60f300000f30d4b02300003cc00003ccf30b6622c0000f3000097e2d97d4c7980f307983cddc6,0x421010210481,0x0,0x80402000002000080082002000020000814e3],
[0x420810208481,0x0,0x420810208481,0x0,0x421010210481,0x420010200481,0x421010210481,0x420010200481,0x422010220481,0x420010200481,0x422010220481,0x420010200481,0x108002208020200408040a00014060100805104,0x48240008118000f303cc0f30f301e63cc03ccf3079a22c1e64bf000097e2d90798b640f307983cde26,0x120002408020200408040a00014060100804104,0x1de6bcc00003ccf6cde63cc38f4f3088b3cc03ccf30079bcc007a73003d388d03db30003cc0001ebffc35,0x120002808020200408040a00014060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2 : TreeBound (n := 4) 107 (programCode 0x4e2b0772) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part103_3 part103_4 part103_5 part103_6 part103_135 part103_136 part103_137 part103_138 part103_315 part103_364 part103_429 part103_430 part103_559 part103_608 part103_657 part103_754

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_899 : TreeBound (n := 4) 107 (programCode 0x4e2b0773) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x1400050080022010080082002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_901 : TreeBound (n := 4) 107 (programCode 0x4e2b077411) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x16c80005b20f316c83cc001f53079fd4c1e7f53001e9cc01e6f3003cc003ccf300f3f3003cde703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_902 : TreeBound (n := 4) 107 (programCode 0x4e2b077412) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x400060001000080000000600010000800000006004000010010000060000000180004000010010000040040000080100000100410800101040000404008000800c000010010873227,0x1400050000900024080006000200c00020100e4,0x164cd6c00000059335b000000164cd6c00000059335b0000000360f9c0000000d83e70159fd80159fd8000004d09718159fd944b4276567f62b962f6000000c34b96c000002b4a7fed59fd8000000b266b602b3fb29e5b28000000b266b60000002c99ad800000025d7ba0000000567f60b7ceaca22ed4afb2bb00000002b3fb159fd802b3fb00d83e70614f4d59fd800567f60acfec07cd607dac,0x1400050001100044080006000200c00020100e4,0x0,0x180501084222,0x180501084222,0x180501084222,0x180501084222,0x180501084222,0x180d02184642,0x180501084222,0x180d02184642,0x0,0x2400410002080090010082402010020400814e3,0x180501084222,0x1400050020100804010008400200900020100e4,0x0,0x2400410002080090010082002010020400814e3,0x0,0x0,0x0,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x180902184642,0x180901084222,0x180902184642,0x0],
[0x1400050002100084008040200200810020503e4,0x180901084222,0x1400050002100084010080400200810020503e4,0x0,0x180908484222,0x0,0x180908484222,0x1ed98007b660f3079800799e601ed98003ea60f30079bcc01e6f3003cc3cc03ccf300f33cc01e703d95,0x0,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x180902184642,0x180901084222,0x180902184642,0x1400050004100104000002000200c00020100e4,0x0,0x180901084222,0x0,0x0,0x180908484222,0x1400050004100104000806000200c04020100e4,0x180908484222,0x0,0x1023001e6f30088b00007d4de9ccf379800f301f530079bcc007a73003d02eb83cc0f303ccf301e64dc35,0x1004040100900024080006000200c00020100e4,0xbfbfcc445ff847f727f310eae00002d1e121fa08a39c25612001483ad8e29fcc43ab80002d1e11f1fb1e11f49fe122a8dd2922b19fe6233eb08f9413c23e39c0016e99f58efe88c943cdebca74a1c23e3f63c23e39c0032c777f245f9c01c332573460c8c8f8e700005fdfe621d5c00017f7f98875700001c32cb374dde12d79f2b67b1500005fdfe621d5c0003158e3a07950000168f08fe8ac23e93fc23e94b09c2c22f7cc4405bc243dd823e67928a3995380005a3c23e3c91e11f8263a8600f800005a3c23eee3847cf00eef1798e,0x3cc1e60f307981e612fd0230f300f30007d4cf3079a22c0002d90000f3111679816c80003cc1e61df6,0x0,0x0],
[0x1400040100900024080006000200c00020100e4,0x0,0x1000040000100004080002000200c00020100e4,0x104004102810020408004a000200c00021128e4,0x4459e60f301e61e612fd0230f300f30007d4cf3079a22c0002d90000f3111679816c80003cc1e61df6,0x0,0x400002001000008000040020010000080000402000001000800004020000010008004000010010000040040000080100000100440000101100000404400000800c000010050873227,0x110004402010080408000a000200c00020100e4,0x1004040100900024080006000200c00020100e4,0x120004804010100408000a000200c00020100e4,0x0,0x108d501e6f30088b0000bbb751aa0fa9800f301f530079bcc007a73003d041b43cc0f303ccf301e64dc35,0x1004040108100204080042000200c00021128e4,0x25f80007981e61e7eda733cc0f33cc00f33ccf300012fc007a730000f303d398044580003cc7ba7e16,0x0,0x0,0x0,0x1400041108100204080042000200c00021128e4,0x1020040808100204080042000200c0002112ce4,0x1100040008100204080042000200c00021128e4,0x1040041008100204080042000200c00021128e4,0x0,0x1080042008100204080042000200c00021138e4,0x40000800150002000040008001000008000400020015000a800040020000100008004000008010000020040000100100000100040000081540000200400001000800001006086aba7,0x1100044008100204080042000200c00021128e4,0x1004040108100204080042000200c00021128e4,0x1200048008100204080042000200c00021168e4,0x1400050000900044080006000200c00020100e4,0x0,0x0,0x1004040110100404080082000200c00022130e4,0x0],
[0x0,0x222c00097e00025f801e63cc079bcc01e63ccf300012fc00f3f30000f303db30044580003cc8196a16,0x0,0x1400042110100404080082000200c00022130e4,0x1020040810100404080082000200c00022134e4,0x1100040010100404080082000200c00022130e4,0x1040041010100404080082000200c00022138e4,0x0,0x1080042010100404080082000200c00022130e4,0x0,0x1100044010100404080082000200c00022130e4,0x1004040110100404080082000200c00022130e4,0x1200048010100404080082000200c00022170e4,0x0,0x4700000030c0000008400000030000000084002000210000000840020000100000104000010010000040040000080100000100410840101002000404000400800c000010010873227,0x1e607987981e6f3007987981e61e679807981e6f30079bcc01e6f3003cc3cc03ccf300f33cc01e703d95,0x0,0x0,0x0,0x3ccf300f30f301e6408d0230f300f30007d4cf3079a22c0002d90000f3111679816c80003cc1e61df6,0x440000101000000400400000810000001004002004010000010040020000100006004000010010000040040000080100000100410800101040000404008000800c000010010873227,0x400020001000080000400200010000080004002000010000800040020000100088004000010010000040040000080100000100440000101100000404400000800c000010050873227,0x1e601e679807a73001e67980799e67980798000f30079bcc01e6f3003cc00003cc3cc0f33cc01e740995,0x3d39800f379801e7ebb30230f300f307983ccf3079a22c0004bf0000f3111679816c80003cc1e61df6,0x0,0x4000000000000800020002000100008000040020000800000000400200001000800040000040100000200400000801000001000100000400000002000000008004000010010852e27,0x400002001000008000400020010000080004002000010000800040020000100008004000010010000040040000080100000100440000101100000404400000800c000010050873227,0x16c87980799e60f300001e61e607987980798000f30079bcc007a73003d027203cc00003ccf301e64dc35,0x1e63cc0798f30f301e607987981e67980798f30f30079bcc01e6f3003cde6003cfcc00f33cc01f267d95,0x0,0x140005002010080408000a000200c00020100e4,0x0],
[0x6300000030c000000a0000000300000000a0002000280000000900020000200000104000010010000040040000080100000100410840101002000404000400800c000010010873227,0x1004040100900024080006000200c00020100e4,0xb5e13856c67000b5e13856c67000168f08f8e7000002fd0afde1a9020218928a3995380017f7f988757000017438140ae3800b52cc00f0a7f847c8a0f08f8e7000002d1e11f1ce001691dada08f3e7d4685e30cd9ae847c74e8f08f8e70b48ed6d030e72d1e1795903e39ed1e135abe8f8e75a3c29875e3e39cb4785e5640f8e70b478a2035be39c5a3c3a72a4f8e705a3c23e39c00000168f08f8e70000168f090f7608f8e9d1e11f49fe11f22841d1f344cdea861e723e3c91e121eec12a64647c73ad1e1a9627ca911d205d,0x1008040200900024080006000200c00020100e4,0x0,0x0,0x168f08f8e7000005a3cd85be3c7380b47deb897639c016918be566b5b7816928f524de4180b48ed6d030e7000b4a565d929ce00000b47847c738168f1f87effbb8e11f1fb1e11f1ce21d690473ba1efa8b3766413ec42e847c74e8f08f93050de91df4f8e7b4784d6afa3e39ed1e135abe8f8e75a3c29875e3e39cb4785e5640f8e70b478a2035be39c5a3c3a72a4f8e705a3c23e39c000005a3c23e39c0000168f08f8e7000002d1e135abe8f8e75a41cf18c528300c5bc2427491aeae21e1b1be9a51ddad1e2b97d0c83b7586fd,0x0,0x1004040000900024080006000200c00020100e4,0x1040041000900004080006000200c00020100e4,0x1004040200900024080006000200c00020100e4,0x1080042000900024080006000200c00020100e4,0x400002001000008002000020010000080020002000080000800100020000200008004000010010000040040000080100000100440000101100000404400000800c000010050873227,0x1100044000900044080006000200c00020100e4,0x1004040100900024080006000200c00020100e4,0x1200048000900044080006000200c00020100e4,0x140005004010100408000a000200c00020100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1047 : TreeBound (n := 4) 107 (programCode 0x4e2b077413) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x25f80011160f307983cc001f5307a76cc1e60f3003cfcc01e6f3003cc00799e603ccf300799e703885]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1048 : TreeBound (n := 4) 107 (programCode 0x4e2b077414) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080022010000880022000820020814e3,0x400010080002010000080402000020000814e3,0x400050080022010001080042000020040814e3,0x400010080002010000080002000020000814e3,0x2400090080082010002080082002020080814e3,0x400010080002010000080002000020000814e3,0x4400110080082010004080102004020100814e3,0x0,0x180d02184642,0x180502084642,0x180d02184642,0x180502084642,0x180d02184642,0x180902184642,0x180d02184642,0x180902184642,0x0,0x0,0x180502084642,0x0,0x400010020000810000080802000020000814e3,0x182102084642,0x400010040001010000081002000020000814e3,0x182102084642,0x0,0x3d3980005b2003d3980003cde6016c80005b2003cc3cc0f31e603cc3cc0f301e600f3f30f301e703885,0x79803cde6003d3980000000f3079803cde6003cc7980f31e603cc3cc00003ccf300f30f301e703d95,0x25f800097e003d398000f33cc0445800097e003cc7980f31e603cc3cc0079bcc01e6f30f301e722395,0x0,0x0,0x2000004008000000020000040080004000000000000800040002000100008000010001000010001000100010000100010000000010004000010000000100040000100208793a7],
[0x3d398003ea6003d398003cde601ed98003ea6003cc3cc0f31e603cc3cc0f301e60f30f30f301e703885,0x7980001e6003d39800000000007980001e6003cc1e60f31e603cc3cc00000f30000f30f301e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x180504084222,0x180504084222,0x180504084222,0x180504084222,0x1400050020100004008008200201000040201e4,0x1400050002100084008040200201010040603e4,0x180504084222,0x0,0x0,0x0,0x180504084222,0x0,0x0,0x0,0x0,0x0,0x0,0x180501084222,0x180501084222,0x180501084222,0x180501084222],
[0x180501084222,0x180901084222,0x180501084222,0x180901084222,0x0,0x0,0x180501084222,0x0,0x0,0x182101084222,0x0,0x182101084222,0x0,0x180504084222,0x180504084222,0x180504084222,0x180504084222,0x0,0x1400050002100084010080400201010040603e4,0x180504084222,0x0,0x0,0x0,0x180504084222,0x0,0x400010020000810000082002000020000814e3,0x0,0x400010040001010000082002000020000814e3,0x0,0x0,0x80c068220481,0x824088220481],
[0x80c068220481,0x844108220501,0x8140c8220481,0x804008220481,0x8140c8220481,0x0,0x824088220481,0x7980001e61e607987983cc1e60f300003cc1e601e603cde600f31e603cde6001ed98007b66001e68a055,0x824088220481,0x7980001e61e607987983cc1e60f300003cc1e601e603cde600f31e603cde6001ed98007b66001e68a055,0x844108220501,0x804008220481,0x844108220501,0x844108220501,0x400010080002010000082002000020000814e3,0x7980001e60b647983cc0000f307983cc1e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0x400010080002010000082002000020000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1161 : TreeBound (n := 4) 107 (programCode 0x4e2b077415) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080022010000880022002020080814e3,0x10400410080002010010080402002020080814e3,0x1400050080022010001080042002020080814e3,0x400010080002010000080002002020080814e3,0x2400090080082010002080082002020080814e3,0x400010080002010000080002002020080814e3,0x4400110080082010004080102002020080814e3,0x0,0x180d0218c642,0x18050218c642,0x180d0218c642,0x18050218c642,0x180d0218c642,0x18090218c642,0x180d0218c642,0x18090218c642,0x0,0x0,0x180d0218c642,0x0,0x0,0x18210208c642,0x0,0x18210208c642,0x0,0x40c044208481,0x424004208481,0x40c044208481,0x424004208481,0x414084208481,0x404004208481],
[0x414084208481,0x0,0x424004208481,0x3d39800f4e6001e7e9cc0f30f303cc3cc03cd02379a22c1e6003cc014e22d901e67983cc03cc224a56,0x424004208481,0x3d39800f4e6001e9cfcc0f30f303cc3cc03cd02379a22c1e600798014e22d907987983cc0f3088ce56,0x444104208501,0x404004208481,0x444104208501,0x408c00102300020463cc0f30f303cc3cc03cd6c879a22c1e603cc0014e32098118001e610230799e56,0x0,0xf300007d4c0088b0000b64001f5307983cc001f53003cfcc01e60f303cc01e61e61e60f301e61e7038e5,0x1e607987987981e60b6403ccf303cc3cc03cc03cc00f6cde6003cc012fc1e601e67983cc03cc1e7556,0x0,0x0,0x0,0x0,0x25f800097e0001f533cc03ccf303cc3cc03cc03cc00f6cde6003cc012fc1e601e67983cc03cc1e7556,0x0,0xf3001e60001e6f3001e9cc0000f307983cc0000f3003cfcc01e600003cc01e61e61e60f301e61e7038e5,0x1e7e6007b66001e7e9cc03ccf303cc3cc03cc03cc00f6cde6003cc012fc1e601e67983cc03cc224156,0x0,0x1e9cc007a73001e9cfcc03ccf303cc3cc03cc03cc00f6cde6003cc012fc1e601e67983cc03cc9f8d56,0xf300f30798f30f300f33cc03ccf307983cc03ccf3003cfcc01e61e603cc01e61e61e60f301e61e8e98e5,0x1f5300088b0001f533cc03ccf303cc3cc03cc03cc00f6cde6003cc012fc1e601e67983cc03cc1e7556,0xf301e62d90f30f301e63cc16c8f307983cc0f30f3003cfcc01e6b6403cc01e61e61e60f301e61f2678e5,0x204600081180020463cc03ccf303cc3cc03cc03cc00f6cde6003cc012fc1e601e67983cc03cc5b3556,0x10400410080002010010080402002020080814e3,0x0,0x0,0x1e607987987981e60b6403ccf303cc3cc03cc079800f4e7e600798012fc1e607987983cc0f30799556,0x0],
[0x0,0x0,0x0,0x0,0x0,0xf3001e60001e6f3001e9cc0000f307983cc0000f3003cfcc01e600003cc01e61e61e60f301e61e7038e5,0x1e7e6007b66001e7e9cc03ccf303cc3cc03cc079800f4e7e600798012fc1e607987983cc0f309bc156,0x0,0x1e9cc007a73001e9cfcc03ccf303cc3cc03cc079800f4e7e600798012fc1e607987983cc0f30812d56,0x0,0x1f5300088b0001f533cc03ccf303cc3cc03cc079800f4e7e600798012fc1e607987983cc0f3097f556,0x0,0x204600081180020463cc03ccf303cc3cc03cc079800f4e7e600798012fc1e607987983cc0f30b65556,0x0,0x80c068208481,0x824088208481,0x80c068208481,0x844108208501,0x8140c8208481,0x804008208481,0x8140c8208481,0x0,0x824088208481,0x3d39800f4e6001e7e9cc0f30f303cc3cc03cd9e3eb9e6097e01e60015a91046e7cc00f3079f9a24a56,0x824088208481,0x3d39800f4e6001e9cfcc0f30f303cc3cc03cd7bf459e61116079800151fe27da73001e60f4e688ce56,0x844108208501,0x804008208481,0x844108208501,0x844108208501,0x0,0x60c0c6208481],
[0x24000208481,0x60c0c6208481,0x4000208481,0x414084208481,0x4000208481,0x414084208481,0x0,0x24000208481,0x1e7e6007b66001e7e9cc03ccf303cc3cc03cc1e60011161e601e60012fc1e6003cc00f3079f9a24156,0x24000208481,0x1e9cc007a73001e9cfcc03ccf303cc3cc03cc1e60011161e601e60012fc1e60079800f307a73812d56,0x844108208501,0x4000208481,0x844108208501,0x4000208481,0x0,0x80c068208481,0x824088208481,0x80c068208481,0x844108208501,0x8140c8208481,0x804008208481,0x8140c8208481,0x40201010080202018040081002002020080854e3,0x824088208481,0x0,0x824088208481,0x0,0x844108208501,0x804008208481,0x844108208501,0x844108208501],
[0x0,0x20c0c2208481,0x0,0x20c0c2208481,0x4000208481,0x14080208481,0x4000208481,0x14080208481,0x0,0x0,0x1e7e6007b66001e7e9cc03ccf303cc3cc03cc3cc0010231e603cc0012fc1e600f3000f307b66317156,0x0,0x1e9cc007a73001e9cfcc03ccf303cc3cc03cc3cc0010231e603cc0012fc1e60079800f307a73812d56,0x44100208501,0x4000208481,0x44100208501,0x4000208481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1306 : TreeBound (n := 4) 107 (programCode 0x4e2b077416) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080022010000880022004020100814e3,0x400010080002010000080402000020000814e3,0x1400050080022010001080042004020100814e3,0x400010080002010000080002000020000814e3,0x0,0x180d03188642,0x180503188642,0x180d03188642,0x180503188642,0x180d03188642,0x180903188642,0x180d03188642,0x180903188642,0x0,0xfd51da80003f5476a0001ebbd0280003f5476a00004a817c80ee6c166b283b9b059aca0ee6c166b281dcd82cd6501dcd82cd82cd6501dcdfeb6ff8c65b704bb2800ee6b28000ee6b280000001dcddc3594077377209bdff0a5835a2e6b28ee6b2800000ee6b45cd661334d75a,0x180d03188642,0xa0000000880000000a00000002800000800800008000800008008000020008004000004004000000440020040140480001001000010001001000010280900010002000125b1a8,0x0,0x182103088642,0x0,0x182103088642,0x400010080002010000080002000020000814e3,0x0,0x180d02188442,0x180502188442,0x180902188442,0x180502188442,0x180d02188442,0x180902188442,0x180902188442,0x180902188442],
[0x0,0x0,0x180d02188442,0x0,0x0,0x182102088442,0x0,0x182102088442,0x0,0x180d02188442,0x180502188442,0x180902188442,0x180502188442,0x180d02188442,0x180902188442,0x180902188442,0x180902188442,0x0,0x0,0x180d02188442,0x0,0x22000000028000000220000000280000020020010000080000200800100000800002000100002000010020200000020000100040010000108000001000100001000600030f13a8,0x182102088442,0x0,0x182102088442,0x0,0x40c044208481,0x424004200481,0x40c044208481,0x424004200481,0x0,0x404004200481],
[0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x444104220501,0x404004200481,0x444104220501,0x0,0x0,0x0,0x25f800097e00025f8000408c00408c000408c03cc00f6cc00f33cc00f31e67981e600799e63cc219b6,0xfd51daf7360eef40bea4bcc6f3e80003f5476a001ddc4bb280003f54b23aca1dcd82cd65021a1f5f6230eea6c2ca0012a05f2001dcd82cd650ee6c166d12487b2066b2877360b3770d65007735a2e6b283b9b4135941dd50e21ec47deb3265000ee6d04d6500ee6f24ede7639,0x25f800111600025f80008118003ea60007d4c07980799e6025fbcc00f33cc0798f347311e61e614726,0x1400050020100004008008200202000080403e4,0x1400050002100084008040200202010080403e4,0x1400050002100084008040200202010080403e4,0x0,0x0,0x0,0x445800111600025f802326980131a60007d4c0798463fe6025fbcc00f33cc25f8f347311e61e614c36,0x0,0x0,0x0,0x0,0x0,0x400410080002010010080402000020000814e3,0x0,0x25f800097e00025f80007d4c00222c1e67d4c079800f4e6040939800f31e72fc1e600f31e63cc219b6,0x0,0x0],
[0x445800111600025f8000fa98003ea60007d4c0f30079bcc025ff9800f33cc0798f382fe1e61e614c36,0x0,0x1400050002100084010080400202010080403e4,0xc00050000100084008080400202000080403a4,0x0,0x0,0x0,0x400020001040080000000200000800800001000000004008000020000000020080000100008010400020002000100100000100000000081000000204000001000000001002086aba7,0x0,0x25f800097e00025f83cc03cc0003cc3cc03cc079800f4e7e60079800f32046001e600001e63cc219b6,0x0,0x25f800097e00025f83cc03cc01e9cc3cc03cc079800f4e7f53079800f32049cc1e60f301e63cc219b6,0x0,0x0,0x400084000000090004000840000000c000000430000001040000000300000010100001000100001001000010001000010000004010000210010000040100000100100208793a7,0x0,0x2100484028001a000e200408020010101c081fa3,0x844108220501,0x20010800480012002020080802002020080816e3,0x804008200481,0x20020800880022002020080802004020100814e3,0x0,0x0,0x1e7e6007b66001e7e9cc03ccf303cc3cc03cc1e6000fb1afe01e6000f32046001e703231e63ce445b6,0x0,0x1e9cc007a73001e9cfcc03ccf303cc3cc03cc79800111e2fe0798000f32046001e9dc231e63d4331b6,0x844108220501,0x804008200481,0x844108220501,0x844108220501,0x25f800097e00025f83cc03ccf303cc3cc03cc1e60011161e601e6000f32046001e600f31e63cc219b6,0x0],
[0x88000000080000000880000000c000000010000001040000000900000010200001000200001002000010002000010000010010000000010000100100000400100208793a7,0x1002080002000040081002000020000814e3,0x4100900028002a000840081002001020140815e3,0x844108220501,0x40011000480012002040081002002020080816e3,0x804008200481,0x40021000880022002040081002004020100814e3,0x1010080002010040081002000020000814e3,0x0,0x0,0x0,0x0,0x844108220501,0x804008200481,0x844108220501,0x844108220501,0x25f800097e00025f83cc03ccf303cc3cc03cc3cc0010231e603cc000f32046001e600f31e63cc219b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1451 : TreeBound (n := 4) 107 (programCode 0x4e2b077417) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080022010000880022004020100814e3,0x10400410080002010010080402004020100814e3,0x1400050080022010001080042004020100814e3,0x400010080002010000080002004020100814e3,0x2400090080082010002080082004020100814e3,0x400010080002010000080002004020100814e3,0x4400110080082010004080102004020100814e3,0x0,0x180d02188442,0x180502188442,0x180902188442,0x180502188442,0x180d02188442,0x180902188442,0x180902188442,0x180902188442,0x0,0x0,0x180d02188442,0x0,0x400010020000810000080802004020100814e3,0x182102088442,0x400010040001010000081002004020100814e3,0x182102088442,0x0,0x40c044208481,0x424004208481,0x40c044208481,0x424004208481,0x414084208481,0x404004208481],
[0x414084208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x444104208501,0x404004208481,0x444104208501,0x0,0x0,0x180104080022,0x180504084222,0x180104080022,0x180504084222,0x10400410002000090010082002004020100814e3,0x1400050002100084008040200202010080403e4,0x180104080022,0x0,0x0,0x0,0x180504084222,0x0,0x0,0x0,0x0,0x0,0x10400410080002010010080402004020100814e3,0x0,0x180104080022,0x180504084222,0x180104080022],
[0x180504084222,0x0,0x1400050002100084010080400202010080403e4,0x180104080022,0x0,0x0,0x0,0x180504084222,0x0,0x400010020000810000082002004020100814e3,0x0,0x400010040001010000082002004020100814e3,0x0,0x0,0x80c068208481,0x824088208481,0x80c068208481,0x844108208501,0x8140c8208481,0x804008208481,0x8140c8208481,0x0,0x824088208481,0x7980001e61e607987983cc1e60f300003cc1e601e603cde600f31e603cc03cc1e60f307983cc1e68a055,0x824088208481,0x7980001e61e607987983cc1e60f300003cc1e601e603cde600f31e603cc03cc1e60f307983cc1e68a055,0x844108208501,0x804008208481,0x844108208501,0x844108208501,0x400010080002010000082002004020100814e3,0x0],
[0x80c068208481,0x824088208481,0x80c068208481,0x844108208501,0x8140c8208481,0x804008208481,0x8140c8208481,0x40201010080202018040081002004020100854e3,0x824088208481,0x0,0x824088208481,0x0,0x844108208501,0x804008208481,0x844108208501,0x844108208501,0x400010080002010000082002004020100814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1564 : TreeBound (n := 4) 107 (programCode 0x4e2b077418) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x445800097e00025f83d49a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x25f800111600025f80008118002046000408cf3000f6cc0063ab0000f33ea6001ed9f983cc3cc1fd66,0x0,0x180d03188642,0x180d01188642,0x180100088442,0x180d01188642,0x180d03188642,0x180902188442,0x180902188442,0x180902188442,0x25f800097e003d398000f33cc0445800097e003cc7980f31e603cc3cc0079bcc01e6f300f31e722395,0x25f800097e00025f800003cc0f33cc03cc3cc03cc00f6cc00003cc00f33cc0000f379803cc1e610856,0x180d03188642,0x0,0x0,0xc00050020100884020108800202008100603a4,0x7980001e60b64798000798000445800097e03cc03cde601e63cc03cc00001e60000f3016c9e703885,0x445800111600025f81e603cc7980f31ed9bcc7980020460f37d4c000f37980799e601e63cc445a3d56,0x445800111600025f8000fa98003ea60007d4cf3000f6cc00454b0000f37b66001eda7303cc3cc20276,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180d03188642,0x180d02188442,0x180d02188442,0x180d02188442,0x0,0x1400050020100004008008200204000100805e4],
[0x180901088442,0x0,0x0,0x0,0x0,0x0,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180903188642,0x180902188442,0x180902188442,0x180902188442,0x0,0x0,0x180901088442,0x0,0x0,0x0,0x0,0x0,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180d03188642,0x180902188442,0x180902188442,0x180902188442],
[0x0,0x0,0x180901088442,0xc00050000100084008080400202000100403a4,0x0,0x25f800111600025f81ee20b000222c0079bcc7980104160f70aa6000f33db708de600f33cc3cc21da6,0x0,0x400020001000080000000200010000800000202000000100000001020000002080004000010000000008040000080100000100402800101000000084004000800040001001087ce67,0x0,0x180901088442,0x180901088442,0x180900088442,0x180901088442,0x180903188642,0x180902188442,0x180902188442,0x180902188442,0x1400050004100104000002000204400100804e4,0x0,0x180901088442,0x0,0x0,0x0,0x1400050004100104004022000204420100804e4,0x0,0x0,0x44691607980001e603d49a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x0,0x0,0x0,0x0,0x100080000400200002000800002000840000800100442000000088000001008004000001010000802240002000100000001001020000004080200020200000020004000206aba8],
[0xa00000004802000022000000020040000002001004420000000080000080080040000000100008022400020001000000010008200000040802000202000000200040002052ba8,0x0,0x1000040000100004080002000204400100804e4,0x0,0x0,0x0,0x446916097e0001e603d49a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x0,0x4467300799e601e603d49a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0x0,0x0,0x25f800079f9801f7160f33cc0f33cc00f33ccf300012fc007a730000f33cc7980fa98003cc1e833456,0x100404010810020408004200020440010182ce4,0x0,0x0,0x0,0x0,0x140004180810020408004200020440010182ce4,0x102004080810020408004200020440010182ce4,0x110004000810020408004200020440010182ce4,0x104004100810020408004200020440010182ce4,0x0,0x108004200810020408004200020440010183ce4,0x0,0x110004400810020408004200020440010182ce4,0x0,0x120004800810020408004200020440010186ce4,0x0,0x180d03188642,0x180d01188642,0x180d00188442,0x180d01188642],
[0x180d03188642,0x180d02188442,0x180d02188442,0x180d02188442,0xf379803cde6003d39803cc0000f379801e7e6003cc7980f31e603cc3cc1e603cc7980f33cc01e703d95,0x0,0x180d03188642,0x0,0x0,0x0,0x1400050004100044004022000204420100804e4,0x0,0x0,0x0,0x1004040110100404080082000204400102834e4,0x0,0x0,0x222c00097e00025f801e63cc079bcc01e63ccf300012fc00f3f30000f33ccf300fa98003cc1ee22056,0x0,0x1400042810100404080082000204400102834e4,0x1020040810100404080082000204400102834e4,0x1100040010100404080082000204400102834e4,0x104004101010040408008200020440010283ce4,0x0,0x1080042010100404080082000204400102834e4,0x0,0x1100044010100404080082000204400102834e4,0x0,0x1200048010100404080082000204400102874e4,0x0,0xc00030020020810000880022020020800814e3,0x0],
[0x1400050020020810001080042000020800814e3,0x400010020000810000080002000020800814e3,0x2400090020080810002080082002020800814e3,0x400010020000810000080002000020800814e3,0x4400110020080810004080102004020800814e3,0x400010020000810000080802000020800814e3,0x0,0x0,0x10400410020000810010080402020020800814e3,0xf307980001e6000079807980001e67980799e6000003cc0001e6f3003cc00001f53000f379801e703885,0x0,0x25f800111600025f85ba20b000222c3cc03cc7980104162dd0aa6000f33f9d08de600f33cc3cc21da6,0x0,0x400020001000080000000200010000800020002000080000000080020000100080004000010000000008040000080100000100640000101000000086000000802000001001087ce67,0x0,0x182101088442,0x182101088442,0x182100088442,0x182101088442,0x182103088642,0x182102088442,0x182102088442,0x182102088442,0x0,0x0,0x182101088442,0x0,0x0,0x182108088642,0x0,0x182108088642,0x0],
[0x400030040021010000880022040021000814e3,0x0,0x400050040021010001080042000021000814e3,0x400010040001010000080002000021000814e3,0x2400090040081010002080082002021000814e3,0x400010040001010000080002000021000814e3,0x4400110040081010004080102004021000814e3,0x400010040001010000081002000021000814e3,0x7980001e6003d3980f300007987980f31e6003cc3cc0f31e603cc3ccf3001e9cc00f5d9001e703885,0x0,0x400410040001010010080402040021000814e3,0x0,0x0,0x0,0x7980001e60b647980f300007987980f31e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x182101088442,0x182101088442,0x182100088442,0x182101088442,0x182103088642,0x182102088442,0x182102088442,0x182102088442,0x0,0x0,0x182101088442,0x0,0x0,0x182108088642,0x7980001e60b6479800000000007983cc1e603cc03cde601e63cc03cc00001e60000f300001e703885],
[0x182108088642]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1789 : TreeBound (n := 4) 107 (programCode 0x4e2b077419) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c80003cde6016cf9805b3f53001e9cc01e6f3003cc0f300f33cc0f30f301e703375,0xf379803cde60f307983cc0000f3079803cde60f30079bcc01e6f3003cc0f303cc3cc0f30f301e703d95,0x25f800097e0f30798000f33cc0445800097e0f30079bcc01e6f3003cc0f303cc3cc0f30f301e722395,0x0,0xc00030000820030000880022008020200814e3,0x0,0x1400050001020050001080042008020200814e3,0x400010000000010000080002008020200814e3,0x2400090002080090002080082008020200814e3,0x400010000000010000080002008020200814e3,0x4400110004080110004080102008020200814e3,0x400010000000010000080002008020200814e3,0x0,0x400010000000010000082002008020200814e3,0x10400410010000410010080402008020200814e3,0x400010000000010000082002008020200814e3,0x0,0x400010000000010000082002008020200814e3,0x0,0x400010000000010000082002008020200814e3,0x0,0x24000300020a0090000880022008020200814e3,0x0,0x24000500020a0090001080042008020200814e3,0x2400090002080090002080082008020200814e3,0x2400090002080090002080082008020200814e3,0x2400410002080090010080402008020200814e3,0x2400110002080090004080102008020200814e3,0x2400090002080090002080082008020200814e3,0x0,0x2400410002080090010082402008020200814e3],
[0x2400410002080090010080402008020200814e3,0x0,0x0,0x2400410002080090010082002008020200814e3,0x0,0x1020001004080000004200000000800000100040000408200001000000001080004000008010000020000000100100000100010000080040000200100001000100001002886aba7,0x0,0x144000300040a0510000880022008020200814e3,0x0,0x144000500040a0510001080042008020200814e3,0x400010000000010000080002008020200814e3,0x10400090010080410002080082008020200814e3,0x400010000000010000080002008020200814e3,0x10400110010080410004080102008020200814e3,0x400010000000010000080002008020200814e3,0x0,0x1400050002100084008040200201012000603e4,0x400410000000010010080402008020200814e3,0x1400050002100084010080400201012000603e4,0x0,0x400010080000010000082002008020200814e3,0x0,0x400010080000010000082002008020200814e3,0xfa98003ea60f3fa98001e7e601ee11803ec46f3001e9cc01e6f3003cc0f300f33cc0f30f301e703375,0x0,0x0,0x0,0x0,0x400010000000010000080002008020200814e3,0x2400090002080090002080082008020200814e3,0x400010000000010000080002008020200814e3,0x4400110004080110004080102008020200814e3],
[0x400010000000010000080002008020200814e3,0x1400050004100104000002000200402000000e4,0x0,0x400410000000010010080402008020200814e3,0x0,0x0,0x0,0x1400050004100104000002000200402000000e4,0x0,0x0,0x800620010842020088004200200801020080ca3,0x1004040100900024080006000200c00020100e4,0x3cc01e6f30088b0000f3f303cc3d39800f303db30079bcc01e6f3003cc0f303cc3cc0f30f301e722395,0x0,0x0,0x0,0x1400040000100004080002000200400000000e4,0x0,0x804220100840020008004200200801020080ca3,0x104004102810020408004a000228400205028e4,0x0,0x108004205020040408028a00025068840a05104,0x810220400850020408004200200801020082ca3,0x110004402010080408000a000220400804020e4,0x810220800870020c08004200200801020086ca3,0x120004804010100408000a000240401008040e4,0x0,0x1041601e6f30089c1600ba87882c0fb20b0f301f530079bcc007a73003cc3cc03ccf3003ccf301e64dc35,0x1004040108100204080042000220400025028e4,0x0,0x0,0x0],
[0x0,0x1400045008100204080042000220400a05028e4,0x102004080810020408004200022040010502ce4,0x1100040008100204080042000220400005028e4,0x1040041008100204080042000220400205028e4,0x0,0x1080042008100204080042000220400405038e4,0x16c83cc0798f316c80f35b22d901e6b6407983ccf30079bcc007a73003cc3cc03ccf3003ccf301e833c35,0x1100044008100204080042000220400805028e4,0x1c7a3cc0f303cdc7a1e671eb8f41e6e3d0f303ccf30079bcc007a73003cc3cc03ccf3003ccf301ebffc35,0x1200048008100204080042000220401005068e4,0x0,0x10400030010020410000880022008020200814e3,0x0,0x10400050010020410001080042008020200814e3,0x10400410010000410010080402008020200814e3,0x10400090010080410002080082008020200814e3,0x10400010010000410000080002008020200814e3,0x10400110010080410004080102008020200814e3,0x10400410010000410010080402008020200814e3,0x0,0x10400010010000410000082002008020200814e3,0x10400410010000410010080402008020200814e3,0x10400410010000410010082002008020200814e3,0x0,0x10400010010000410000082002008020200814e3,0x0,0x10400410010000410010082002008020200814e3,0x0,0x0,0x1004040110100404080082000220400026030e4,0x0],
[0x0,0x222c00097e00025f801e63cc079bcc01e63ccf300012fc00f3f3000111600f37987983cc0f30799556,0x0,0x1400046010100404080082000220400c06030e4,0x1020040810100404080082000220400106034e4,0x1100040010100404080082000220400006030e4,0x1040041010100404080082000220400206038e4,0x0,0x1080042010100404080082000220400406030e4,0x0,0x1100044010100404080082000220400806030e4,0x0,0x1200048010100404080082000220401006070e4,0x0,0x2000680012040480098004200200801020080ca3,0x1e607987981e6f3007987981e61e679807981e6f30079bcc01e6f3003cc0f303cc3cc0f30f301e703d95,0x1e6001ed980088b0000fa98003ea6798079803db30079bcc01e6f3003cc0f303cc3cc0f30f301e7241f5,0x0,0x0,0x0,0x1e6003d39803dd160079f9801e7e679f9f98371d3001e9cc01e6f3003cc0f300f33cc0f30f301e703375,0x1e67980799e60f300f307983cc1e688b079a22cf3003cfcc01e6f3003cc0f301e63cc0f30f301e8e9885,0x2004280102044080108004200200801020080ca3,0x3d39800f379801e7ebefc230f300f307983ccf30bdfa2c0004bf000151fe27d9bd39800f3079a249f6,0x0,0x3d39800f4e6001e9cfcc07993ef1e60f303ccf3079a22c00088b000142bde600f39f781e61e64c0c76,0x2010280402050080408004200200801020082ca3,0x16c87980799e616c80001e61e607987980798000f30079bcc007a73003cc3cc03ccf3003ccf301e64dc35,0x2010280802060080c08004200200801020086ca3,0x408c00102300020463cc07996c81e61e603ccf3079a22c00088b00014e21e60798b640f30f30799c76,0x0,0xc00630018c46030188004200200801020080ca3],
[0x100404012010080408000a000200c00020100e4,0x1e601e6798088b0000f6cc1e6f30798007983db30079bcc01e6f3003cc0f303cc3cc0f30f301e703d95,0x0,0x0,0x0,0x140004002010080408000a000200400000000e4,0x0,0x4200108040000008004200200801020080ca3,0x104004102010080408000a000208400201028e4,0x0,0x108004202010080408000a000210400402030e4,0x201028040a050080408004200200801020082ca3,0x110004402010080408000a000220400804020e4,0x601038080e070180c08004200200801020086ca3,0x120004802010080408000a000240401008040e4,0x0,0x4000700012040500098004200200801020080ca3,0x1004040100900024080006000200c00020100e4,0x3cc00102300088b00010230008118799f53005c13003cfcc01e6f3003cc0f301e63cc0f30f301e707545,0x1008040200100004080002000200400040000e4,0x0,0x0,0x3cc00f3f3003db30007b66003d3987980f301e6f30079bcc01e6f3003cc0f303cc3cc0f30f301e722395,0x0,0x4004300102044100108004200200801020080ca3,0x1040041000100004080002000200400200000e4,0x1000040200100004080002000200400040000e4,0x1080042000100004080002000200400400000e4,0x4010300402050100408004200200801020082ca3,0x0,0x4010300802050100c08004200200801020086ca3,0x0],
[0x0,0x800620018842020088004200200801020080ca3,0x100404014010100408000a000200c00020100e4,0x3cc01e6f30088b0000f3f303db3079800f303db30079bcc01e6f3003cc0f303cc3cc0f30f301e722395,0x0,0x0,0x0,0x0,0x0,0x4200108040000008004200200801020080ca3,0x104004104010100408000a000208400201028e4,0x0,0x108004204010100408000a000210400402030e4,0x0,0x110004404010100408000a000220400804020e4,0x100004004010100408000a000200400000000e4,0x120004804010100408000a000240401008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_1998 : TreeBound (n := 4) 107 (programCode 0x4e2b07741a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x4000000030004000200004000900000000800040040000480200001200000001001040000080100000200400001001000001000010000810460002000080010008000010020862ba7,0x10bae01e6f30088b0000bc6d882c0fa9800f301f530079bcc007a73003d010583cc0f303ccf301e64dc35,0x0,0x0,0x0,0x0,0x20000030040000200200000900000000802001000004082200020200000020001040000100100000200400001001000001000200001010440002002000010008000010020872ba7,0x0,0x4000000030400000200400000900000000804000040040080200100200000100001040000080100000200400001001000001004010000810460002000080010008000010020862ba7,0x1041601e6f30088b0000ba87882c0fa9800f301f530079bcc007a73003d010583cc0f303ccf301e64dc35,0x0,0x0,0x1e80355e003bc77e178010c388d00000fd51da80010c388d00000fd51de39acdf5476a0000f224d4a077394dad8e6b283b9aca00f047fe503b9b4135940ee6d04d6503b9b4135940773770d650077359400773d0759401dcf424d8770d6c7359401dce536df341780ee6ee959172c9,0x25f80007d4c001f5307983cc7983cc07983ccf300012fc0004bf0000f3f31e60f379800f31e62da556,0x0,0x25f80007d4c001f530f303cc3cc3cc0f303ccf300012fc0004bf0000f3f31e60f379800f31e62da556,0x1e607987987981e60b6403ccf303cc3cc03ccf300012fc1e60f30000f3f4e600f379800f31e62da556,0x0,0x0,0x25f80007981e61e7ed98408c00408c000408cf300012fc007a730000f3f3001f5379800f31e6317156,0x0,0x4000000050000000200000001100000001400000001000080300000200010000004040000040100000200400001001000001000000000410c00002040000010002000010020852ba7,0x0,0x0,0x200001100c0000200200001100000001002001000004086600020200000020004040000100100000200400001001000001000200001010cc0002002000010008000010020872ba7,0x0,0x0,0x25f800079f9801e7e60f33cc0f33cc00f33ccf300012fc007a730000f3f30798f379800f31e6317156,0x4000000050600000202000001100000001008000000040080300200200000200004040000040100000200400001001000001000000000410c60002040000010002000010020852ba7,0x0],
[0x22757cc8001dcd6d61c46d9682f0000ef953653c487aa3b8b9acbebbd0639aca3b9aca013acd347ca051f88f6d8e7b1b26a7ca04a9f49e500773d0759400ee88f56503b9b4135940773770d650077359400ee6c166b29dcd66e45b01cbd07359421872086c704a8ca2e6f8061ab7f9,0x25f80007d4c001f5307983cc7983cc07983ccf300012fc0004bf0000f3f31e60f379800f31e62da556,0x200011cccc000220000001100000001200000110400086662000200002000004040000100100000200400001001000001000002001010ccc002000020010008000010022a7aba7,0x25f800081180020460f303cc3cc3cc0f303ccf300012fc0004bf0000f3f31e60f379800f31e66a6556,0x0,0x0,0x1e60f30f307981e612fc0798f301e63cc03cc0025f800097e7980f30f4e60f3079ff320f30f344ac26,0x0,0x1e60f30f307981e612fc0798f301e63cc03cc0025f80011167981e60f4e60f3079fd4c0f30f344ac26,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc000000f301e60000000f3f4e600f300000f31e62dc3b6,0x1e60f30f307981e612fc0798f301e63cc03cc3cc7980f31e67b66000f4e60079f9fd799f30f344ac26,0x0,0x3cc1e60f307981e612fc0798f301e63cc03cc7987981e61e67d4c000f4e60079f9fd6a6f30f344b136,0x0,0x0,0x25f800099c6001e7e9cc03ccf303cc3cc03cc000f30f311160000f30f3f4e600f301e60f31e6317156,0x0,0x25f80007b66001ed9bcc03ccf303cc3cc03cc001e60f3097e0001e60f3f4e600f307980f31e62da556,0x0,0x25f80007983cc1e6408c03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x0,0x0],
[0x400000081040000200000000800800000840000000100008200400000001000001000100008000400020002000100002000100400000081040000204000001000000001002086aba7,0x0,0x1dcd6500077acc994001dd11eaca001dd11eaca01dd11eaca001e449a97b9acbdcd650001e449a940773770d650001e449a9401dcda09aca3b9ad8e6b28ee6b36e6b29dcd73e6b287735a2e6b28773d075940077536165001dd4dc12eca3bb89765000ee6b28ee6b36e6fdb7de95b9,0x25f800097e3cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62dc3b6,0x1dcd6500077acc994001ddc4bb28001deb3265001de3bf0bc001e449a97b9acbdcd6500077acc9940773770d6500077acc99401dce536b283b9b059aca0ee6b9f35941dcd82cd6507735b1cd650773d075940077536165001dd4e73ff283bb89765000ee6b2bb9acaee6ef83fc73b9,0x25f80007980001e612fc03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f3000f3f31e62dc3b6,0x0,0x0,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc000f30f311160000f30f3f4e600f301e60f31e6320936,0x0,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc001e60f3097e0001e60f3f4e600f307980f31e62e3d36,0x0,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x600020001800000000000000004000000040002000100000000400000001000000002000010008000040010000080010000100400000101000000404000000800000001001087fea7,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62e3d36,0x600020001800000000000000004000000040002000100000000400000001000000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f3000f3f31e62e3d36,0x25f800097e0001ed9bcc03ccf303cc3cc03ccf300012fc1e60f30000f3f4e600f379800f31e62da556,0x0,0x0,0x102004080090002408004200020840020112ce4,0x0,0x1e67980f33cc01e679808118003ea60007d4cf3003cfcc00fb8b0000f4e7e60079fd6a6f30f3465566,0x0,0x0,0x3ccf300f33cc01e67d88cf30f300f300f33ccf30813a2c007a730000f6ce04603d39800f3079a33cf6],
[0x0,0x0,0x102004080810020408004200020840020102ce4,0x1e67980f33cc01e679807d4c0f33cc0007d4cf300012fc01e6f30000f3f4e63db379800f31e62e98e6,0x102004081010040408008200020840020303ce4,0x0,0x0,0x0,0x0,0x1e6000097e0001e603cc03ccf303cc3cc03ccf300012fc1e60f30000f3f4e600f379800f31e62da556,0x108004108020200408040a00021048020205104,0x0,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc000f30f311160000f30f3f4e600f301e60f31e6318fb6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc001e60f3097e0001e60f3f4e600f307980f31e62dc3b6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62dc3b6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f3000f3f31e62dc3b6,0x108004208020200408040a00021048020205104,0x0,0x0,0x1f5300079f9801e603cc03ccf303cc3cc03cc000f30f311160000f30f3f4e600f301e60f31e62da556],
[0x0,0x1f530007b66001e603cc03ccf303cc3cc03cc001e60f3097e0001e60f3f4e600f307980f31e62da556,0x4000040010020100000080400000200800400020801000002004000048010000080000080100000200400000800800001001004000001010000004049000008010000010010877667,0x1e60f30798f301e64fbc03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x4000040010000080000c00200003000800400020001000008004000020010000080000800100001000400004000800010001004000001010000004040000008010000010050877227,0x0,0x420008001080020000100080000400080040002000100002000400008001000008000200010000800040001000080002000100400000101400000404000000801000001011087baa7,0x0,0x1e600007980001e603cc03ccf303cc3cc03cc000000f301e60000000f3f4e600f300000f31e62da556,0x1e60f307983cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62dc3b6,0x40000400100000800300002000c00008004000200010000180040000600100000800200001000800004001000008002000010040000010100000040400000080100000100d0877227,0x1e60f307983cc1e612fc03ccf303cc3cc03cc3cc0010231e603cc000f3f4e600f3000f3f31e62dc3b6,0x120004408020200408040a00021048020205104,0x0,0x0,0x1040041100900024080042000208400201128e4,0x0,0xf303cc00003ccf301e63cc35280007983cc03ccf30079bcc007a73003d22b803db30003db3001ebffc35,0x0,0x0,0x44d1800f379801e7ea08cf30f300f300f33ccf30813a2c007a730000f6ce04603d39800f3079a249f6,0x0,0x1040040000100004080002000208400201028e4,0x1040041008100204080042000208400201028e4,0x1e60f307b66001e6000081180f522c0007d4cf300012fc01eabf0000f4e61e9db381180f31e64c0706,0x1040042010100404080082000208400203038e4,0x0,0x0,0x1040040008100004080002000208400201028e4,0x0],
[0x120004808020200408040a00021048020205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2159 : TreeBound (n := 4) 107 (programCode 0x4e2b07741b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c80003cde6016cf9805b3f53001e9cc01e6f3003cc0f300f3f300f31e601e703375,0x0,0x180501084222,0x180501084222,0x180501084222,0x180501084222,0x180501084222,0x180502084642,0x180501084222,0x180502084642,0x0,0x180504084222,0x180501084222,0x180504084222,0x0,0x180508084222,0x0,0x180508084222,0x25f80011160f30798000799e60446730097e0f3003cfcc01e6f3003cc1e601e6f300f31e601e703885,0x1400050001100044080002000200400040000e4,0x0,0x180501084222,0x180501084222,0x180501084222,0x180501084222,0x180501084222,0x180d0218c642,0x180501084222,0x180d0218c642,0x0,0x2400410002080090010082402010020400814e3],
[0x180501084222,0x0,0x0,0x2400410002080090010082002010020400814e3,0x0,0x0,0x0,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x18090218c642,0x180901084222,0x18090218c642,0x0,0x0,0x180901084222,0x0,0x0,0x0,0x0,0x0,0x1ed98007b660f3079800799e601ed98003ea60f30079bcc01e6f3003cc3cc03ccf300f31e601e703d95,0x0,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x180901084222,0x18090218c642,0x180901084222],
[0x18090218c642,0x1400050004100104000002000200400040000e4,0x0,0x180901084222,0x0,0x0,0x0,0x1400050004100104000002000200400040000e4,0x0,0x0,0x800620010842020088004200200801040080ca3,0x0,0x3cc01e6f30088b0000f3f303cc3d39800f303db30079bcc01e6f3003cc3cc03ccf300f31e601e722395,0xf6d3b663cc1e6f6d3b660f30000f379800f4e60f3001e9cc01e6f3003cc0f300f3f300f31e601e7033d5,0x0,0x0,0x1400040000100004080002000200400040000e4,0x0,0x804220100840020008004200200801040080ca3,0x1e7e600f379801e7e60f33cc1e60f300f33ccf300012fc007a730000f3097e003d39800079f9a24186,0xf6cc1e63cc1e6f6cc3cc0f30000f379800f4e60f3001e9cc01e6f3003cc0f300f3f300f31e601e7033d5,0x1e9cc00f4e6001e9cc1e63cc7983cc01e63ccf300012fc0f30f30000f3097e445879800088b0812de6,0x810220400850020408004200200801040082ca3,0x0,0x810220800870020c08004200200801040086ca3,0x0,0x0,0x108d501e72fc088fbf00bbb751aa4c6bdf92fc98d30079bcc007a73003cc3cc03cc3cc03cde601e64dc35,0x1004040108100204080042000208400041028e4,0x25f800079f9801e7e60f33cc0f33cc00f33ccf300012fc007a730000f3079f983d39800079f9a24156,0x0,0x0],
[0x0,0x1400041008100204080042000208400041028e4,0x102004080810020408004200020840004102ce4,0x1100040008100204080042000208400041028e4,0x1040041008100204080042000208400041028e4,0x0,0x1080042008100204080042000208400041038e4,0x18ae3cc0798f311160f362bb15c1e688b07983ccf30079bcc007a73003cc3cc03cc3cc03cde601e833c35,0x1100044008100204080042000208400041028e4,0x1040041008100204080042000208400041028e4,0x1200048008100204080042000208400041068e4,0x1400050000100044080002000200400040000e4,0x0,0x0,0x1004040110100404080082000210400042030e4,0x0,0x0,0x222c00097e00025f801e63cc079bcc01e63ccf300012fc00f3f30000f307a73079f980007a73812d56,0x0,0x1400042010100404080082000210400042030e4,0x1020040810100404080082000210400042034e4,0x1100040010100404080082000210400042030e4,0x1040041010100404080082000210400042038e4,0x0,0x1080042010100404080082000210400042030e4,0x0,0x1100044010100404080082000210400042030e4,0x1080042010100404080082000210400042030e4,0x1200048010100404080082000210400042070e4,0x0,0x2000680012040480098004200200801040080ca3,0x1e60798799e60f3007987981e61e6798079a046f30079bcc01e6f3003cc3cc03ccf300f31e601e703d95],
[0x1e6001ed980088b0000fa98003ea6798079803db30079bcc01e6f3003cc3cc03ccf300f31e601e7241f5,0x0,0x0,0x3ccf300f30f301e6408d0230f300f30007d4cf3079a22c0000f300012fd11679807980007980001df6,0x1e6003d39803dd160079f9801e7e679f9f98371d3001e9cc01e6f3003cc0f300f3f300f31e601e703375,0x1e67980799e60f300f307983cc1e688b079a22cf3003cfcc01e6f3003cc1e601e6f300f31e601e8e9885,0x2004280102044080108004200200801040080ca3,0x0,0x0,0x0,0x2010280402050080408004200200801040082ca3,0x0,0x2010280802060080c08004200200801040086ca3,0x0,0x0,0x182101084222,0x182101084222,0x182101084222,0x182101084222,0x182101084222,0x182102084642,0x182101084222,0x182102084642,0x0,0x0,0x182101084222,0x0,0x0,0x182108084222,0x0,0x182108084222,0x0],
[0x2000700012040500098004200200801040080ca3,0x1004040100100044080002000200400040000e4,0x1e600097e0008c7c000fa980025f8799f53006f0f001e9cc01e6f3003cc0f300f3f300f31e601e703375,0x1008040200100004080002000200400040000e4,0x0,0x0,0x3cc007b66003db30007a73001ed987a73f302d9f3003cfcc01e6f3003cc1e601e6f300f31e601e703885,0x0,0x2004300102044100108004200200801040080ca3,0x1040041000100004080002000200400040000e4,0x1000040200100004080002000200400040000e4,0x1080042000100004080002000200400040000e4,0x2010300402050100408004200200801040082ca3,0x1100044000100044080002000200400040000e4,0x2010300802050100c08004200200801040086ca3,0x1200048000100044080002000200400040000e4,0x0,0x182101084222,0x182101084222,0x182101084222,0x182101084222,0x182101084222,0x182102084642,0x182101084222,0x182102084642,0x0,0x0,0x182101084222,0x0,0x0,0x182108084222,0x7980001e60b6479800000000007983cc1e603cc03cde601e63cc03cc1e601e6f300f31e601e703885],
[0x182108084222]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2352 : TreeBound (n := 4) 107 (programCode 0x4e2b07741c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x3d77a0500040c36d22130dcd65000000f5de8140003d77a0c735947735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda1895c34baa,0x222c00088b00029c43cc03ccf303cc3cc03cc000f30f311160000f30f4e7e6007983cc1e60f3812d56,0x0,0x222c00088b00029c43cc03ccf303cc3cc03cc001e60f3097e0001e60f4e7e6007983cc1e60f3812d56,0x4000000050020000100080000400200000c00020801000002004000008810000001000080100000200400000800800001001004000001010000004040080008000200010010877667,0x1e60f3088b00029c43cc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x0,0x0,0x0,0x0,0x400000005000000008c000000230000000c0002000100000000c000000830000001008000100010000400040000800100001004000001010000004040000008010000010010877227,0x1e60f3088b00029c43cc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3814bb6,0x0,0x1e60f3088b00029c43cc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e60079800f4e60f3814bb6,0x1e607987987981e60b6403ccf303cc3cc03ccf300012fc1e60f30000f4e7e60079f9801e60f3812d56,0x0,0x773596540be400010c38b240be7b9aca00001dcd65773596540be4001deb326500000773597ba150caee500077acc994003b9aca0773d07594077394daca0077447ab2801dd4d8594001dd4d8594000000f047fe500077acca290316eb3265000ee6b287735a2e6ee946cff99,0x0,0x0,0x0,0x4000000110020000400080000800200001400020801000002004000009010000002000080100000200400000800800001001004000001010000004040080008000200010010877667,0x1e63cc097e00025f83cc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x1e9cc0097e00025f83cc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3812d56,0x0,0x1e9cc0097e00025f83cc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e60079800f4e60f3812d56,0x0,0x3b9acbdcd68b9acbdcd66dcd65ee6b28ee6b2f73597b9acc540be47735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda18b390b0aa,0x1e60f30f307981e612fc0798f301e63cc03cc0025f800097e7980f30f4e61e60f384e41e61e64c4426,0x0,0x1e60f30f307981e612fc0798f301e63cc03cc0025f80011167981e60f4e60f30f384e41e61e653dc26,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420021001080084000000000000400020040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc000000f301e60000000f4e7e6007980001e60f3814bb6,0x1e60f30f307981e612fc0798f301e63cc03cc3cc7980f31e67b66000f4e6007a737d79ae61e64c4426,0x0,0x3cc1e60f307981e612fc0798f301e63cc03cc7987981e61e67d4c000f6cc007a7381367e61e64c4936,0x0,0x0,0x222c00097e00025f8000408c00408c000408cf300012fc00f3f30000f4e60079f9f9801e60f3812d56,0x210004002000000008100000008000040000000482200002200000002010040000020100000200400001001000001000000000210004002000000010000080010020842ba7,0x222c00097e00025f80007d4c00222c0007d4cf300012fc00f3f30000f4e6003d39f9801e60f3812d56,0x0,0x0,0x0,0x0,0x0,0x0],
[0x222c00097e00025f80007d4c079bcc0007d4cf300012fc00f3f30000f4e60f3079f9801e60f3812d56,0x222c00097e00025f801e63cc079bcc01e63ccf300012fc00f3f30000f4e60f3079f9801e60f3812d56,0x0,0x0,0x210000002000000008100000008080000000400082002000200002000010040000040100000200400001001000001000000000414000002000000010080000010020852ba7,0x0,0x0,0x0,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc000f30f311160000f30f4e7e6007983cc1e60f381c536,0x0,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc001e60f3097e0001e60f4e7e6007983cc1e60f381c536,0x0,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x600020001800000000000000004000000040002000100000000400000001000000002000010008000040010000080010000100400000101000000404000000800000001001087fea7,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f381c536,0x600020001800000000000000004000000040002000100000000400000001000000002000010008000040010000080020000100400000101000000404000000800000001001087fea7,0x1e63cc079bcc01e6408c03ccf303cc3cc03cc3cc0010231e603cc000f4e7e60079800f4e60f381c536,0x0,0x26718011160001ed9c4583cc7983cc44583ccf300012fc1e64bf0000f4e80460f379801e61e62da5e6,0x1400042100900024080082000210400402130e4,0xf36a5f300001023000798114a35016c800079fa730079bcc007a73003cfcd2ffcc00003cc0799e64dc35,0x0,0x0,0x0,0x0,0x0],
[0x25f80011160001ed983cc3cc1e60f303cc3ccf300012fc01e6f30000f4e7e600f379801e61e62da586,0x1400043008100204080042000210400403038e4,0x1400042010100044080082000210400402030e4,0x1400042010100404080082000210400402030e4,0x0,0x140004202010080408000a000210400402030e4,0x41000000200000001010000001008000000040008300200020000200004004000004010000020040000100100000100000000041c000002000000010020000010020852ba7,0x140004204010100408000a000210400402030e4,0x0,0x0,0x1020040800900024080082000210400402134e4,0x0,0x1e67980f33cc01e679808118003ea60007d4cf3003cfcc01ee8b0000f4e7e600f37d79ae61e6558566,0x0,0x0,0x0,0x0,0x0,0x102004080810020408004200021040040303ce4,0x1020040810100044080082000210400402034e4,0x1020040810100404080082000210400402034e4,0x0,0x0,0x0,0x0,0x1e6000097e0001e603cc03ccf303cc3cc03ccf300012fc1e60f30000f4e7e60079f9801e60f3812d56,0x108004108020200408040a00021048040205104,0x0,0x4a817c80003f54787cd66dcd65ee6b292a05f200003b9acc540be47735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda18b390b0aa,0x1e60f3097e0001e612fc03ccf303cc3cc03cc000f30f311160000f30f4e7e6007983cc1e60f3814bb6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc001e60f3097e0001e60f4e7e6007983cc1e60f3814bb6],
[0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x420001001080004000000008000400010040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3814bb6,0x0,0x1e60f3097e0001e612fc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e60079800f4e60f3814bb6,0x108004208020200408040a00021048040205104,0x0,0x3b9aca000040c36d22130dcd65000000ee6b639aca3b9aca7735947735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda1895c34baa,0x222c0007a7300222c3cc03ccf303cc3cc03cc000f30f311160000f30f4e7e6007983cc1e60f3812d56,0x0,0x222c0007a7300222c3cc03ccf303cc3cc03cc001e60f3097e0001e60f4e7e6007983cc1e60f3812d56,0x4000040010020100000080400000200800400020801000002004000048010000080000080100000200400000800800001001004000001010000004040080008000200010010877667,0x1e60f30798f301e64fbc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x0,0x0,0x0,0x0,0x1e600007980001e603cc03ccf303cc3cc03cc000000f301e60000000f4e7e6007980001e60f3812d56,0x1e60f307983cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3814bb6,0x0,0x1e60f307983cc1e612fc03ccf303cc3cc03cc3cc0010231e603cc000f4e7e60079800f4e60f3814bb6,0x120004408020200408040a00021048040205104,0x0],
[0x222c0007a73002269efc03cc7983cc5b203ccf300012fc1e64bf0000f4e7f53079f9801e60f3812d56,0x1080042100900024080082000210400402130e4,0x3d39800f4e6001e600000798f301e600003ccf307983cc00088b0000f6cde600f381181e61e64c0c76,0x0,0x0,0x0,0x0,0x0,0x1080040000100004080002000210400402030e4,0x1080041008100204080042000210400403038e4,0x1080042010100044080082000210400402030e4,0x1080042010100404080082000210400402030e4,0x0,0x3d39800fc7e0020c175307981e60f307983ccf3000315c000c570000f6cde600f381181e61e64c0c46,0x1080042010100404080082000210400402030e4,0x3d3980104160022a784607987980f30f303ccf3000222c00088b0000f6cde600f381181e61e6c58c46,0x120004808020200408040a00021048040205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2529 : TreeBound (n := 4) 107 (programCode 0x4e2b07741d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030080022010000880022020020800814e3,0x0,0x50c045220481,0x424004220481,0x50c045220481,0x424004220481,0x614086220481,0x404004220481,0x614086220481,0x0,0x424004220481,0x1e7e6007b66001e7e9cc03ccf303cc3cc03cc000f30f311160000f30fa99e601e60f307983cc224156,0x424004220481,0x1e9cc007a73001e9cfcc03ccf303cc3cc03cc000f30f311160000f311161e607983cc1e60f30812d56,0xc4410c220501,0x404004220481,0xc4410c220501,0x80002000000080402020020800814e3,0x1400050080022010001080042020020800814e3,0x400010080002010000080002020020800814e3,0x2400090080082010002080082020020800814e3,0x400010080002010000080002020020800814e3,0x4400110080082010004080102020020800814e3,0x0,0x0,0x0,0x0,0x400010000000010000080002020020800814e3,0x2400090002080090002080082020020800814e3,0x400010000000010000080002020020800814e3,0x400010004000110000080102020020800814e3],
[0x400010000000010000080002020020800814e3,0x0,0x0,0x10400410010000410010080402020020800814e3,0x0,0x400010020000810000080802020020800814e3,0x400010000002010000080002020020800814e3,0x400010040001010000081002020020800814e3,0x400010000002010000080002020020800814e3,0x0,0x40c044220481,0x424004220481,0x40c044220481,0x424004220481,0x414084220481,0x404004220481,0x414084220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0x444104220501,0x404004220481,0x444104220501,0x0,0x0,0x4400110000880030004082402020020800814e3,0x25f800097e00025f8000408c00408c000408c03cc00f6cde6003cc012fc1e60000f30b640001e61556,0x4400110001080050004082402020020800814e3,0x400010000000010000082002020020800814e3,0x10400410002000090010082002020020800814e3],
[0x1400050002100084008040200202012000403e4,0x10400410004000110010082002020020800814e3,0x0,0x0,0x0,0x400010010000410000082002020020800814e3,0x0,0x0,0x0,0x0,0x0,0x10400410080002010010080402020020800814e3,0x0,0x0,0x0,0x0,0x400010000000010000082002020020800814e3,0x0,0x1400050002100084010080400202012000403e4,0x400010004000110000082002020020800814e3,0x0,0x0,0x0,0x10400410010000410010082002020020800814e3,0x0,0x400010020000810000082002020020800814e3,0x0,0x400010040001010000082002020020800814e3,0x0,0x0,0x80c068220481,0x824088220481],
[0x80c068220481,0x844108220501,0x8140c8220481,0x804008220481,0x8140c8220481,0x0,0x824088220481,0x7980001e61e607987983cc1e60f300003cc1e601e603cde600f31e603cc79801ed980079f9801e68a055,0x824088220481,0x7980001e61e607987983cc1e60f300003cc1e601e603cde600f31e603cc79801ed980079f9801e68a055,0x844108220501,0x804008220481,0x844108220501,0x844108220501,0x400010080002010000082002020020800814e3,0x0,0x80c068220481,0x824088220481,0x80c068220481,0x844108220501,0x8140c8220481,0x804008220481,0x8140c8220481,0x40201010080202018040081002020020800854e3,0x824088220481,0x0,0x824088220481,0x0,0x844108220501,0x804008220481,0x844108220501,0x844108220501],
[0x400010080002010000082002020020800814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2658 : TreeBound (n := 4) 107 (programCode 0x4e2b07741e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c041208481,0x40c044208481,0x10c041208481,0xc040208481,0x4000000030000000080040000200100000c00020001000001004000004010000001000040100000100400000400800001001004000001000200004000800008000200010018873227,0x4000180002000800080002000020100814e3,0x0,0x0,0x40c044208481,0x0,0x40c044208481,0x0,0x4008000020020000084000000210000000c0002080100000000c000000030000001004000100010000400040000800100001004100001000001004000004008000200010010873227,0x4000180002000800080102000020100814e3,0x40080000200200000900000002c0000000c0002080100000000c000000030000001020000100080000400100000800200001004100001000001004000004008000200010010873227,0x4000180002000800080102000020100814e3,0x1e607987987981e60b6403ccf303cc3cc03ccf300012fc1e60f30000fa99e607987980798f30799556,0x0,0x10c041208481,0x40c044208481,0x10c041208481,0xc040208481,0x4000000110000000400040000800100001400020001000001004000004010000006000040100000100400000400800001001004000001000200004000800008000c00010018873227,0x8000280002000800080002000020100814e3,0x0,0x0,0x40c044208481,0x0,0x40c044208481,0x0],
[0x1e7e61ed98007b660012fc00417f00012fc003cde607987981e61e603cc0811bcc01e6f307981e7241f5,0x8000280002000800080102000020100814e3,0x1000000004200000008c0000001400000001000000044000000110000006020000100080000400100000800200001000000001000008004000020008000c00010032a73227,0x8000280002000800080002000020100814e3,0x0,0x10c041208481,0x424004200481,0x10c041208481,0x4000200481,0x0,0x4000200481,0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x0,0x4000000210000000800004002100000008000060000000100100000600000001010040000100100000400400000801000001004000001000020004040000008002000010010873227,0x0,0x0,0xf30003cc0001023000408c00000007983cc00f3f3003cfcc01e6f3003cc00001f53000f31e601e703885,0x0,0x0,0x0,0x0,0x0,0x0],
[0xf30003cfcc010230003cde60000f379801e60f3f3003cfcc01e6f3003cc00001f53000f31e601e703885,0x222c00097e00025f801e63cc079bcc01e63ccf300012fc00f3f30000fa980f37987980798f30799556,0x0,0x0,0x0,0x0,0x0,0x0,0x404004200481,0x0,0x4000200481,0x0,0x4000200481,0x0,0x0,0x404004200481,0x0,0x404004200481,0x0,0x804008200481,0x4000200481,0x804008200481,0x4000200481,0x0,0x400000101000000400000400810000001000006000000010010000060000000106004000010010000040040000080100000100400000100002000404000000800c000010010873227,0x0,0x0,0x0,0x0,0x0,0xf55f8f303cc10230007987b939008118003cc7a730079bcc007a73003d027203db30003ccf301e64dc35,0x0],
[0x140004402010080408000a000220400804020e4,0x1400045008100204080042000220400805028e4,0x0,0x1400046010100404080082000220400806030e4,0x400000101000000400400000810000001004002000010000010040020000100006004000010010000040040000080100000100400000100002000404000000800c000010010873227,0x140004402010080408000a000220400804020e4,0x0,0x140004404010100408000a000220400804020e4,0x0,0x0,0x1e67980f33cc01e679808118002046000408cf301e63cc0b6c8b00010231e603cc980e0987983ebd66,0x0,0x1e67980f33cc01e679808118003ea60007d4cf301e63cc07a08b00010231e603cc97fed987983ebd66,0x0,0x0,0x0,0x0,0x0,0x102004080810020408004200022040080502ce4,0x1e67980f33cc01e679807d4c7983cc0007d4cf300012fc0f30f30000fa99e644587980798f307a88e6,0x1020040810100404080082000220400806034e4,0x0,0x0,0x0,0x0,0x4200108040200008004200208001000080ca3,0x108004108020200408040a00024060080805104,0x0,0x124041208481,0x424004200481,0x124041208481,0x24000200481],
[0x0,0x24000200481,0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x0,0x24000200481,0x0,0x80002080002000000082002000020000814e3,0x108004208020200408040a00024060080805104,0x0,0x144141228501,0xc4410c220501,0x144141228501,0x44100220501,0x4000020010000080000040200000100800400020001000001004000004010000080000040100000100400000400800001001004000001000200004000800008010000010018873227,0x844108220501,0x0,0x0,0x444104220501,0x0,0x444104220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x44100220501,0x120004408020200408040a00024060080804104,0x0],
[0x144141228501,0xc4410c220501,0x144141228501,0x44100220501,0x0,0x844108220501,0x0,0x0,0x444104220501,0x0,0x444104220501,0x0,0x844108220501,0x844108220501,0x844108220501,0x44100220501,0x120004808020200408040a00024060080804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2835 : TreeBound (n := 4) 107 (programCode 0x4e2b07741f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x7980001e60f307983cc0000f307983cc1e60f3001e9cc01e6f3003cc79800fa9800f3f3001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_2836 : TreeBound (n := 4) 107 (programCode 0x4e2b077420) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x600018040200088004200208001000080ca3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e60798f307981e60798408c7983cc000408cf300012fc0798f300010231e681187980f30f307995e6,0x1004040108100204080042000240401009068e4,0x1e60798f307981e607987d4c7983cc0007d4cf300012fc0f30f300010231e644587980f30f307995e6,0x100404011010040408008200024040100a070e4,0x0,0x100404012010080408000a000240401008040e4,0x100404014010100408000a000240401008040e4,0x100404014010100408000a000240401008040e4,0x0,0x10c041200481,0x8000280002000800080402000020000814e3,0x10c041200481,0xc040200481,0x20c0c2208481,0x8000280002000800080002000020000814e3,0x20c0c2208481,0x0,0x0,0x0,0x0,0x0],
[0x80c068220481,0x8000280002000800080102000020000814e3,0x80c068220481,0xc040200481,0x0,0x10c041200481,0x80002000000080402000020000814e3,0x10c041200481,0x4000200481,0x214082208481,0x4000200481,0x214082208481,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x0,0x1140c1204481,0x0,0x1140c1204481,0x14080200481,0x214082208481,0x10000480002002000080002000020000814e3,0x214082208481,0x0,0x0,0x0],
[0x0,0x0,0x8140c8220481,0x0,0x8140c8220481,0x14080200481,0x0,0x820020880022002000880022000820020814e3,0x80002000000080402000020000814e3,0x20040880022002001080042000020040814e3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800040001000080001000100400000100000000404000000800000001001087fea7,0x0,0x420020001080000000000000000400000040002000100000000400000001000000000200010000800040001000080002000100400000100000000404000000800000001001087fea7,0x0,0x804008220481,0x4000200481,0x804008220481,0x4000200481,0x0,0x1140c1204481,0x20000880002002000080402000020000814e3,0x1140c1204481,0x14080200481,0x214082208481,0x20000880002002000080002000020000814e3,0x214082208481,0x0],
[0x0,0x0,0x0,0x0,0x8140c8220481,0x20000880002002000080402000020000814e3,0x8140c8220481,0x14080200481,0x0,0x0,0x3ccf300f33cc01e679808118002046000408cf303cc3cc07a08b00011161e60798b65f530f307b8276,0x3ccf300799e601e680267bb000222c0007d4cf30d4d15c0798f300011163533a0c7980f307983dd0c6,0x3ccf300f33cc01e67980fa98003ea60007d4cf303cc3cc0f388b00011161e60798b65f530f307b8276,0x0,0x0,0x0,0x0,0x0,0x102004080810020408004200024040100906ce4,0x1e67980f33cc01e679807d4c7983cc0007d4cf300012fc0f30f300010231e644587980f30f307a88e6,0x102004081010040408008200024040100a074e4,0x0,0x0,0x0,0x0,0x0,0x842001000c0002088004200208001002080ca3,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x804200100840020008004200208001020080ca3,0x1100040008100204080042000240401009068e4,0x804200100840040008004200208001040080ca3,0x110004001010040408008200024040100a070e4,0x0,0x4200108040000008004200208001000080ca3,0x4200102040100008004200208001100080ca3,0x4200108040000008004200208001000080ca3,0x108004108020200408040a00024060100805104,0x0,0xf3003cc003ea6f3003cc003cde6016c80005b3f53003cfcc01e6f3003cc003cdf53000f3003cde703885,0x222c00109cf981e60f308118002046000408cf303cc3cc16d08b00010231e60798980e830f30799766,0x4a0cd908118001e615d67bb000222c0007d4cf30d4d15c0798f300011163533a0c7980f307983cddc6,0x408c0010237981e60f30fa98003ea60007d4cf303cc3cc0f388b00011161e60798b65f530f30799c76,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x108004208020200408040a00024060100805104,0x0,0x144141204501,0x100004080002004000080402000020000814e3],
[0x144141204501,0x44100200501,0x244182208501,0x844108220501,0x244182208501,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x844108220501,0x844108220501,0x44100200501,0x120004408020200408040a00024060100804104,0xf303cc00003ccf301e63cc3528f307983cc03ccf30079bcc007a73003cfcc003db30003cc0001ebffc35,0x120004808020200408040a00024060100804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_900 : TreeBound (n := 4) 107 (programCode 0x4e2b0774) := by
  conv in programCode _ => reduce
  exact branchFour (k := (0,1)) (by decide +kernel) part103_901 part103_902 part103_1047 part103_1048 part103_1161 part103_1306 part103_1451 part103_1564 part103_1789 part103_1998 part103_2159 part103_2352 part103_2529 part103_2658 part103_2835 part103_2836

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3013 : TreeBound (n := 4) 107 (programCode 0x4e2b0775) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x2400090080082010080082002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3015 : TreeBound (n := 4) 107 (programCode 0x4e2b077631) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4400410080082010000880022080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3016 : TreeBound (n := 4) 107 (programCode 0x4e2b077632) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x440009008020200400142002048040a00010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3017 : TreeBound (n := 4) 107 (programCode 0x4e2b077633) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4400410080082010001080042080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3018 : TreeBound (n := 4) 107 (programCode 0x4e2b077634) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x4400410080082010000880022000820020814e3,0x0,0x280501184222,0x280501184222,0x280501184222,0x280501184222,0x280d01184222,0x280901184222,0x280501184222,0x280901184222,0x0,0x0,0x280d01184222,0x0,0x0,0x282101104222,0x0,0x282101104222,0x4400410080082010001080042001020040814e3,0x400010080002010000080002000020000814e3,0x400010080002010000080002002020080814e3,0x400010080002010000080002000020000814e3,0x400010080002010000080002004020100814e3,0x0,0x280d01188642,0x280501108642,0x280d01188642,0x280501108642,0x280d01188642,0x280901188642,0x280d01188642],
[0x280901188642,0x0,0x0,0x280d01188642,0x0,0x400010020000810000080002000020800814e3,0x282101108642,0x400010040001010000080002000021000814e3,0x282101108642,0x0,0x4400410000880030000880022008020200814e3,0x400010080000410010080402008020200814e3,0x4400410001080050001080042008020200814e3,0x400010000000010000080002008020200814e3,0x10400010002000090002080082008020200814e3,0x400010000000010000080002008020200814e3,0x10400010004000110004080102008020200814e3,0x400010000000010000080002008020200814e3,0x0,0x0,0x400010010000410010080402008020200814e3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x798079f9807987980b6403ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003f9c3b6,0x0,0x7980f379803cc79812fc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003f9c3b6,0x811800799e600798408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36],
[0x7983cc7983cc0798408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36,0x811800799e60079812fc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003f9c3b6,0x0,0x7980007b6600079803cc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003f9c3b6,0x799e60799e600799e9cc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fd8fb6,0x7983cc7b66000798408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36,0x79bcc0798f30079bcfcc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f30047adbb6,0x7983cc7980f30798408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36,0x7a73007a730007a733cc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003f9c3b6,0x0,0x7b660079f98007b663cc03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f30043683b6,0x0,0x280d0118c642,0x280501108642,0x280d0118c642,0x280501108642,0x280d0118c642,0x28090118c642,0x280d0118c642,0x28090118c642,0x0,0x0,0x280d0118c642,0x0,0x0,0x282101108642,0x0,0x282101108642,0x0,0x7d4c007a730008154fcc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044d4bb6,0x798079f9807987980b6403ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044d4bb6,0x0],
[0x7980f379803cc79812fc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044d4bb6,0x0,0x7983cc7983cc0798408c03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044dc536,0x0,0x0,0x7980007b6600079803cc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044d4bb6,0x799e60799e600799e9cc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60046f77b6,0x7983cc7b66000798408c03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044dc536,0x79bcc0798f30079bcfcc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044d4bb6,0x7983cc7980f30798408c03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044dc536,0x7a73007a730007a733cc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60046babb6,0x79bcc079803cc81183cc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044d4bb6,0x7b660079f98007b663cc03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60048a0bb6,0x400010080002010000080002020020800814e3,0x0,0x4000180002000800080002000020100814e3,0x24000200481,0x8000280002000800080002000020100814e3,0x4000200481,0x0,0x4000200481,0x0,0x0,0x24000200481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x24000200481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x844108220501,0x4000200481,0x844108220501,0x4000200481,0x400010080002010000080002040021000814e3],
[0x0,0x4000180002000800080002000020000814e3,0x0,0x8000280002000800080002000020000814e3,0x4000200481,0x10000480002002000080002000020000814e3,0x4000200481,0x20000880002002000080002000020000814e3,0x0,0x0,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x0,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003cc00007980001e68a8c5,0x844108220501,0x4000200481,0x844108220501,0x4000200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3163 : TreeBound (n := 4) 107 (programCode 0x4e2b077635) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10400010080002010002080082080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3164 : TreeBound (n := 4) 107 (programCode 0x4e2b077636) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x400010080002010000080002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3165 : TreeBound (n := 4) 107 (programCode 0x4e2b077637) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10400010080002010004080102080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3166 : TreeBound (n := 4) 107 (programCode 0x4e2b077638) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1ed98007b6600081183d3a730f303cc00003cc01eda7307980000f30408c1e9db3000f6cc001e611156,0x0,0x280502108442,0x280502184642,0x280502108442,0x280502184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x0,0x0,0x280502108442,0x0,0x0,0x0,0x0,0x0,0x0,0x280902108442,0x280d02184642,0x280902108442,0x280d02184642,0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0,0x280902110442,0x280902108442,0x280902110442],
[0x0,0x280902120442,0x4000200010ff08000000420000000080000000404000004878000020000000028000000000201ffff020004000100000080100040000020400000202000001002000001002884aba7,0x280902120442,0x0,0x280502108442,0x280502184642,0x280502108442,0x280502184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x400010000000010000080002008020200814e3,0x0,0x280502108442,0x0,0x400010000000010000080002020020800814e3,0x0,0x400010000000010000080002040021000814e3,0x0,0x280902140442,0x280902140442,0x280902140442,0x280902140442,0x0,0x6090c4240481,0x0,0x6090c4240481,0x0,0x411084240481,0x1004240481],
[0x411084240481,0x21004240481,0x21004240481,0x1004240481,0x21004240481,0x21004240481,0x841104240501,0x1004240481,0x841104240501,0x1004240481,0x0,0x6098c6240481,0x209102340d02,0x6098c6240481,0x209102340d02,0x411084240481,0x240481,0x411084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x280902140442,0x0,0x6080c0240481,0x209102340d02,0x6080c0240481],
[0x209102340d02,0x410080240481,0x240481,0x410080240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x148045001200a0800834080802080022000814e3,0x208902140442,0x150085002200a0800834080802080022000814e3,0x208902140442,0x61208e240481,0x2008240481,0x61208e240481,0x842108240501,0x42200c240481,0x2008240481,0x42200c240481,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x282102140442,0x0],
[0x7983cc1f6230097e001ed98081273001e60007980001e679803cfcc003db3000f6cc001e703d95,0x0,0x1e60f307a91601116003d398088bf3003cc0007980001e679803cfcc003db3000f6cc001e722395,0x0,0x61208e240481,0x2008240481,0x61208e240481,0x842108240501,0x42200c240481,0x2008240481,0x42200c240481,0x2008240481,0x842108240501,0x2008240481,0x842108240501,0x2008240481,0x282102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3311 : TreeBound (n := 4) 107 (programCode 0x4e2b077639) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x60c0c4240481,0x400808018020200408142002048040a00010104,0x60c0c4240481,0x0,0x62c0c4204481,0x0,0x62c0c4204481,0x0,0x24004208481,0x24004200481,0x24004208481,0x0,0x0,0x400021000000084000000000000000020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x400021000000084000000000000000020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x24004220481,0x24004200481,0x24004220481,0x0,0x414084240481,0x4004240481,0x414084240481,0x0,0x6084c4240481,0x0,0x6084c4240481,0x0,0x410884240481,0x4240481,0x410884240481],
[0x4240481,0x21004240481,0x4240481,0x21004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x24004240481,0x408008108020200409042020048048200102904,0x24004240481,0x408008208020200409042040048048200205104,0x844104240501,0x4004240481,0x844104240501,0x4004240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3360 : TreeBound (n := 4) 107 (programCode 0x4e2b07763a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x460008408020200401042020048048200102904,0x400808018020200401042020048048200102904,0x0,0x6084c6240481,0x440808010120002401042020048048e00102904,0x6084c6240481,0x1ed98f37b660007980f3088b000222c0007d4c0f300f33cde6003cc0408c2046f300012fc0079a26316,0x6088c6240481,0x6098c6240481,0x6088c6240481,0x6098c6240481,0x6090c6240481,0x6098c6240481,0x6090c6240481,0x6098c6240481,0x60a0c7240481,0x6098c6240481,0x60a0c7240481,0x0,0x0,0x1e601e6798079879815b269b0f303cc07983cc0f3d04b8cc00f33cc0408c3413c700f33cc0079a268b6,0x7980f379803cc7980f30408c00408c000408c03cc03cfcde6003cc0408c1e60f30000b640079a25fb6,0x109d06509e7e600000079811439001e600007a740bae79803ccf300003cfcc003db30007d4c001e68a8c5,0x7980f379803cc7980f307d4c00222c0007d4c03cc03cfcde6003cc0408c1e60f300012fc0079a25fb6,0x200408022010088400805020048011200542ba4,0x208904340d02,0x2091043408e2,0x208904340d02,0x7980f379803cc7980f307d4c00222c0007d4c03cc03cfcde6003cc0408c1e60f300012fc0079a25fb6,0x2091043408e2,0x209904340d02],
[0x2091043408e2,0x209904340d02,0x20a1041418e2,0x0,0x20a1041418e2,0x472008048020200401042020048048200102b04,0x402008048020200401042020048048200102b04,0x448008108020200401042020048048200102904,0x0,0x6384c6240481,0x0,0x6384c6240481,0x0,0x410884240481,0x240481,0x410884240481,0x240481,0x21000240481,0x240481,0x21000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x440008008020200401042020048048200102904,0x408008108020200401042020048048200102904,0x442008048020200401042020048048200102b04,0x408008208020200401042020048048200107904,0x443008008020200401042020048048200102904,0x420008408020200401042020048048200102904,0x44c008008020200401042020048048200102904],
[0x420008808020200401042020048048200106904]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3425 : TreeBound (n := 4) 107 (programCode 0x4e2b07763b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x400010080002010010080402080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3426 : TreeBound (n := 4) 107 (programCode 0x4e2b07763c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x0,0x0,0x7980f37b6600084e40007d4c00222c0007d4c079803cde7e6007980408c1e60f300012fc00f3814bb6,0x6088c2240481,0x6098c6240481,0x6088c2240481,0x6080c0240481,0x6090c4240481,0x6098c6240481,0x6090c4240481,0x6080c0240481,0x70a0cf240481,0x6098c6240481,0x70a0cf240481,0x0,0x798079f9807987980b6403ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f3812d56,0x0,0x0,0x0,0x0,0x0,0x6088c2240481,0x6098c6240481,0x6088c2240481,0x6080c0240481,0x6090c4240481,0x6098c6240481,0x6090c4240481,0x6080c0240481],
[0x70a0cf240481,0x6098c6240481,0x70a0cf240481,0x798f307b660007b660f303cc3cc3cc0f303cc079803cde603cc7980408c00f3f301e63cc00f3838cd6,0x0,0x0,0x0,0x0,0xf301e63cc07987980f30fa98003ea60007d4c0f379803cde7e67980408c00088b0813a2c00f344b136,0x2004080220100884008090400480102006433a4,0x208904340d02,0x2091043408e2,0x208904340d02,0x7980f379801e67980f307d4c0003cc0007d4c079803ccf4e6007980408c1e60f300003cc00f74d4b26,0x2091043408e2,0x209904340d02,0x2091043408e2,0x209904340d02,0x20a1041418e2,0xf307980001e600000001e61e603cc0000f30000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x20a1041418e2,0x0,0x1f1ecb03d3b66079842b667317d97e60f303cc0f3becb3cc01e67980408c2fb3b30bececc00f3456926,0x0,0x0,0x0,0x410882240481,0x411084240481,0x410882240481,0x410080240481,0x411084240481,0x411084240481],
[0x411084240481,0x410080240481,0x61208e240481,0x411084240481,0x61208e240481,0x410080240481,0x7983cc7983cc0798408c03ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f381a6d6,0x0,0x2031100001001000010200000010010062201000100000800400008000400008000200311000800000802000002002000008400031101000001004000200010000010010807f3a8,0x0,0x0,0x0,0x410882240481,0x411084240481,0x410882240481,0x410080240481,0x411084240481,0x411084240481,0x411084240481,0x410080240481,0x61208e240481,0x411084240481,0x61208e240481,0x410080240481,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x240481,0x410882240481],
[0x240481,0x21004240481,0x240481,0x21004240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x7980007b6600079803cc03ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f3812d56,0x408008108020200401042040048048200205104,0x7983cc7b66000798408c03ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f381a6d6,0x408008208020200401042040048048200205104,0x1edaec83cc0f3079803cc0f30f301e63cc03cc0f37a733cde7e67980408c2046f30811bcc00f344efa6,0x420008408020200401042040048048200205104,0x0,0x0,0x0,0x0,0x7980f3798f30081180007d4c00222c0007d4c079803cde7e6007980408c1e60f300012fc00f3814bb6,0x840908240501,0x842108240501,0x840908240501,0x842108240501,0x84110c240501,0x842108240501,0x84110c240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501],
[0x420008808020200401042040048048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3555 : TreeBound (n := 4) 107 (programCode 0x4e2b07763d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x70c0c8240481,0x10400002080002010020080802080022000814e3,0x70c0c8240481,0x20400804080102014020080802080022000834e3,0x614088240481,0x4008240481,0x614088240481,0x0,0x7384c8240481,0x0,0x7384c8240481,0x0,0x630888240481,0x8240481,0x630888240481,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x424008240481,0x40800810802020040c642080048073200402904,0x424008240481,0x40800820802020040c642100048063200805104,0x844108240501,0x4008240481,0x844108240501],
[0x4008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3588 : TreeBound (n := 4) 107 (programCode 0x4e2b07763e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x60c0c6240481,0x400808018020200404042080048063200402104,0x60c0c6240481,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x414084240481,0x4000240481,0x414084240481,0x0,0x6384c6240481,0x0,0x6384c6240481,0x0,0x410884240481,0x240481,0x410884240481,0x240481,0x21000240481,0x240481,0x21000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x24000240481,0x408008108020200404042080048063200402904,0x24000240481,0x408008208020200404042080048063200407104,0x844108240501,0x4000240481,0x844108240501],
[0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3621 : TreeBound (n := 4) 107 (programCode 0x4e2b07763f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x70c0c8240481,0x0,0x634088204481,0x424008210481,0x634088204481,0x2080002000040081002000021000814e3,0x424008208481,0x424008210481,0x424008208481,0x0,0x424008210481,0x40080801802020040184202004104c020102904,0x424008210481,0x798079f9807987980b6403ccf303cc3cc03cc079803cde7e60079803cde7e60079f9801e60f3812d56,0x424008220481,0x424008200481,0x424008220481,0x0,0x70c0c8240481,0x0,0xf4c1e8204501,0x0,0xf4c1e8204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x0,0x0,0x0,0x0],
[0x0,0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x614088240481,0x4008240481,0x614088240481,0x10080002010040081002080022000814e3,0x424008240481,0x0,0x630488240481,0x4080081001200024001c2002048040e00010104,0x630488240481,0x0,0x420808240481,0x8240481,0x420808240481,0x8240481,0x1008240481,0x8240481,0x1008240481,0x8240481,0x2008240481,0x8240481,0x2008240481,0x8240481,0x424008240481,0x0,0x0,0x0,0x0],
[0x0,0x840908240501,0x8240481,0x840908240501,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x2008240481,0x8240481,0x2008240481,0x8240481,0x844108240501,0x4008240481,0x844108240501,0x4008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3702 : TreeBound (n := 4) 107 (programCode 0x4e2b077640) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108d501e63cc07980000b64211b9300003cc0098d33d398000079800f6cc00f33cc03cc3cc03cde64dc35,0x4000180002000800080402000020400814e3,0x1106d01e61e607980000b64220e9300003cc0112533d398000079801e9cc00f33cc00f33cc0799e6c7435,0x4000180002000800080002000020000814e3,0x1eda7307980f30798408c0f30f303cc3cc03cc7987a73f31e603cc004093c5ccc0798f301ed983d5746,0x4000180002000800080002000020000814e3,0x1eda730798000079803cc0f30f303cc3cc03cc7987a74e61e603cc004279c5ccc1e60f3f307983cde56,0x0,0x1eda730798000079803cc0f30f303cc3cc03cc7987a74e61e603cc004093c5cdb3000f30007983cde56,0x4000180002000800080402080020400814e3,0x4000180002000800080402010020400814e3,0x4000180002000800080002080020000814e3,0x80630018046200088004080202001080080ca3,0x1eda730798000079803cc0f30f303cc3cc03cc7987a74e61e603cc003ea62dcd39800f37987983cde56,0x80630018046200088004100202001100080ca3,0x630018046200088004000208001000080ca3,0x0,0x0,0x0,0x10ca94e403ea6007983cc011439001e9cc007a73f35b998007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x20000100010000080100000800100000e0221000000040800000108000001008002000301008000000820000400020000008400030101000000204000000810000100008157f3a8,0x2089085414c2,0x20a9085414c2,0x2089085414c2,0x0,0x209108341d02,0x20a9085414c2,0x209108341d02,0x20a9085414c2],
[0x20a1081414c2,0x0,0x20a1081414c2,0x0,0x1f173307980000798f6cc0f30f303cc3cc03cc7987a73f31e603cc004279c5ccc0000f30007983cddc6,0x8000280002000800080002000020400814e3,0x110e681e63cc01e600012fc221dc300003cc0089a36ac98000079800f6cc00f33cc00f33cc0799e6cedb5,0x8000280002000800080002000020000814e3,0x1f1733079f9800798f6cc0f30f303cc3cc03cc7987a74e61e603cc004279c5ccfcc00f301ed983cde56,0x8000280002000800080002000020000814e3,0x1030000001040000010000800010802040000800100000800400008001000008002000200008000000820002000020000008001000081000080000010000802000100008147b3a8,0x8000280002000800080002000022000814e3,0x42ec00010011000040008000020000000140002172100000010400000001000000884300010000100040000000020004000100020000100080000400100000200100001000cc7fca7,0x0,0x8000280002000800080402010020400814e3,0x0,0x159fd8159fd80614f4c57dcf7b446240567f8c99ad802b3fb0159fd800acfec00000006c1f3800005938c2f60005be76b9fd80aecbca41af6000016fb2f7d80000000567f60000164cec5fd80159fd8567f600567f79add0800567f66c1f3802b3fb000000000acff167f6000567f759fd8000567fb67f600015a0033fb000015a084fec0000ad0019fd800002b4109fd800015a0080b0885dcb6b,0x8000280002000800080002000020100814e3,0x11150d1e607981e600012fc221dc300003cc0010f7a07980000799e603cde6003cde6003db3001e6cedb5,0x8000280002000800080002000020000814e3,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x10000480002002000080002080022000814e3,0x4000240481,0x20000880002002000080002080022000814e3,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x240481,0x410882240481],
[0x240481,0x21004240481,0x240481,0x21004240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x620481240481,0x40001080000400000080402080022000814e3,0x620481240481,0x40001080000000000080002080022000814e3,0x420802240481,0x20000240481,0x420802240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422008240481,0x20000240481,0x422008240481,0x20000240481,0x408008108020200404042100048062200805104,0x0,0x620481240481,0x0,0x620481240481,0x0],
[0x420802240481,0x20000240481,0x420802240481,0x20000240481,0x21004240481,0x20000240481,0x21004240481,0x20000240481,0x422008240481,0x20000240481,0x422008240481,0x20000240481,0x408008208020200404042100048062200805104,0x844108240501,0x4000240481,0x844108240501,0x4000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3014 : TreeBound (n := 4) 107 (programCode 0x4e2b0776) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part103_3015 part103_3016 part103_3017 part103_3018 part103_3163 part103_3164 part103_3165 part103_3166 part103_3311 part103_3360 part103_3425 part103_3426 part103_3555 part103_3588 part103_3621 part103_3702

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3815 : TreeBound (n := 4) 107 (programCode 0x4e2b0777) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x4400110080082010080082002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3817 : TreeBound (n := 4) 107 (programCode 0x4e2b077831) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c83cc001f53079fd4c1e7e600f4e6003ea6000f6cc003ccf300f3f3003cde703375,0xf379803cde60f307983cc0000f307983cc1e60000fa98003ea6000f6cc00003cc0000f33cc01e703d95,0x25f800097e0f307983cc003db307983cc1e60000fa98003ea6000f6cc00f33cc03ccf300799e722395,0x16c80005b20f316c83cc001f53079fd4c1e7e600f4e6003ea6000f6cc003ccf300f3f3003cde703375,0x0,0x280902108442,0x280502108442,0x280902108442,0x280502108442,0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0,0x0,0x280902108442,0x0,0x0,0x282102108442,0x0,0x282102108442,0x0,0x280902108442,0x280502108442,0x280902108442,0x280502108442,0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0],
[0x0,0x280902108442,0x0,0x0,0x282102108442,0x0,0x282102108442,0xfa98003ea60f3fa983cc01e6f30811bcc2046000f4e6003ea6000f6cc01e60f31e60f303cc1e703375,0x0,0x280902108442,0x280502108442,0x280902108442,0x280502108442,0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0,0x0,0x280902108442,0x0,0x0,0x282102108442,0x0,0x282102108442,0x0,0x800620018042200080084002200801020080ca3,0x3cc0000f3000f30079bcc0000f307983cc0000000fa98003ea6000f6cc0f303cc3cc0f30f301e703d95,0x3cc01e6f30088b00012fc003db307983cc003cc00fa98003ea6000f6cc0f303cc3cc0f30f301e722395,0x1e601e67980798f3012fc0f30f303cc3cc03ccf307a73001e60000007d4d1160f300000007980001e56,0x0,0x0],
[0x3cc0f30f303db30007d4c01e6f307983cc01e6000fa98003ea6000f6cc0f303cc3cc0f30f301e703d95,0x0,0x804220108040200000084002200801020080ca3,0x1e67980799e600f31e9cc0f30f303cc3cc03cd7d9da73799e6003cc07d88efd213079800f33cc224a56,0x0,0x1e67980799e600f33cfcc0f30f303cc3cc03cd7d9da74e61e600f3007d88efb3b3079801e6f3088ce56,0x810220408050200400084002200801020082ca3,0x102379800f4e610230003cc1e60f307983cc0000003d39800f379800f6cc3cc03ccf3003ccf301e64dc35,0x810220808070200c00084002200801020086ca3,0x1e9cc007a73000f4e63cc0f30f303cc3cc03cd6e6da74e61e60798007f322dcdb3000f3f30f30799e56,0x0,0xf300007d4c0088b0000b64001f5307983cc001e600f6cc00f4e6000f6cfcc001f53000f33cc01e7038e5,0xf30079bcc0798f300b6403ccf303cc3cc03cd1160079f99e60f30f3798f4e600f37bdf8f33cc1e7556,0x0,0x0,0x0,0x0,0xfa98003ea7e60f3f33cc03ccf303cc3cc03ccf300079f99e6111600798f4e600f379f98f33cc1e7556,0x0,0xf3001e60001e6f3001e9cc0000f307983cc0000000f6cc00f4e6000f6cfcc001f53000f300001e7038e5,0xf31e603cde600f31e9cc03ccf303cc3cc03ccf300079f99e60f6cc0798f4e600f379f98f33cc224156,0x0,0xf33cc03ccf300f33cfcc03ccf303cc3cc03ccf300079f99e60fa980798f4e600f379f98f33cc9f8d56,0xf300f30798f30f300f33cc03ccf307983cc03cc000f6cc00f4e6000f6cfcc001f53000f379801e8e98e5,0xf3f3003db3000f3f33cc03ccf303cc3cc03ccf300079f99e6111600798f4e600f379f98f33cc1e7556,0xf301e62d90f30f301e63cc16c8f307983cc0f30000f6cc00f4e6000f6cfcc001f53000f5d9001f2678e5,0xf4e6003d39800f4e63cc03ccf303cc3cc03ccf300079f99e612fc00798f4e600f379f98f33cc5b3556,0x0,0x280902108442,0x280502108442,0x280902108442,0x280502108442],
[0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0,0x0,0x280902108442,0x0,0x0,0x282102108442,0x0,0x282102108442,0x0,0xf30000798f3088b0000b64001f5307983cc001e600f6cc00f4e6000f6cfcc001f53000f300f31e7038e5,0xf30079bcc0798f300b6403ccf303cc3cc03cd6c8007b661e60f30f3799e7e60079fdc59e6f30799556,0xf30000f312fc88b00012fc001f5307983cc003cc00f6cc00f4e6000f6cfcc001f53000f3012fde7038e5,0x0,0x0,0x0,0x0,0x0,0xf3001e60001e6f3001e9cc0000f307983cc0000000f6cc00f4e6000f6cfcc001f53000f300001e7038e5,0xf31e603cde600f31e9cc03ccf303cc3cc03ccf30007b661e60f6cc0799e7e60079f9f99e6f309bc156,0x0,0xf33cc03ccf300f33cfcc03ccf303cc3cc03ccf30007b661e60fa980799e7e60079f9f99e6f30812d56,0x0,0xf3f3003db3000f3f33cc03ccf303cc3cc03ccf30007b661e6111600799e7e60079f9f99e6f3097f556,0x0,0xf4e6003d39800f4e63cc03ccf303cc3cc03ccf30007b661e612fc00799e7e60079f9f99e6f30b65556,0x0,0x2000680018040600090084002202001080080ca3,0x1e607987981e6f30079bcc01e6f307983cc01e6000fa98003ea6000f6cc79803cde600f379801e703d95],
[0x1e6001ed980088b00012fc0004bf07983cc003cc00fa98003ea6000f6cc79803cde600f379801e7241f5,0x1e67980799e60f30000b640002d90798b641e7e600f6cc003ea6000f6cc79801e7e600f379801e703885,0x0,0x0,0x1e6003d39803dd16007d4c001f53079fd4c0370e00f4e6003ea6000f6cc79800f4e600f379801e703375,0x0,0x2004280108044200100084002202001080080ca3,0x1e67980799e600f31e9cc0f30f303cc3cc03cd7d9da730f4e601e6007f39c7b3b300079f98079a24a56,0x0,0x1e67980799e600f33cfcc0f30f303cc3cc03cd7d9da733cde60798007f39c7b3b3000f4e601e688ce56,0x2010280408050200400084002202001080082ca3,0x16c87980799e616c80003cc1e60f307983cc0000003d39800f379800f6cde6003d398003d39801e64dc35,0x2010280808060200c00084002202001080086ca3,0x1e9cc007a73000f4e63cc0f30f303cc3cc03cd6e6da74e61e60798007f39c5cdb3000f4e60f30799e56,0x0,0xc00630018046200180084002208c01030080ca3,0xf30079bcc0798f300b6403ccf303cc3cc03ccf30f379805b20f30f379f99e6079888b0798001e61556,0x1e601e6798088b00012fc01e6f307983cc003cc00fa98003ea6000f6cc3cc03db3000f307981e703d95,0x1e601e67980798f3012fc0f30f303cc3cc03cd6eaa6730097e0000007b662dd4d180000798003cc3cb6,0x0,0x0,0xf300f33cc03db30007d4c0000f307983cc01e6000fa98003ea6000f6cc00003db3000f33cc01e703d95,0x0,0x4200108040200000084002208001000080ca3,0xf31e603cde600f31e9cc03ccf303cc3cc03ccf3000798f4e611160079f99e6079879f9f98079a24156,0x0,0xf33cc03ccf300f33cfcc03ccf303cc3cc03ccf3000799e7e616c80079f99e6079879f9f980f3812d56,0x201028040805020040008400220a001080082ca3,0xf307980001e60f300003cc1e60f307983cc0000003d39800f379800f6cfcc003db30003cc0001e64dc35,0x6010380808070200c0008400220e001180086ca3,0xf307980001e60f300003cc1e60f307983cc0000003d39800f379800f6cfcc003db30003cc0001e64dc35,0x0],
[0x4000700018040600090084002202001100080ca3,0x3cc0000f300012fc0d4dcc0000f307983cc1e60000f4e6003ea6000f6cc79800fa9800f3f3001e703375,0x3cc00102300088b00012fc00088b079a22c005b200f6cc003ea6000f6ccf3001ed9800f3f3001e707545,0x3cc1e60f307992fc97eb640798f3097e3cc2616600f4e6003ea6000f6cc79800fa9800f3f3001eacf375,0x0,0x3cc007a73001f8fc81954c001f53079fd4c2064600f4e6003ea6000f6cc79800fa9800f3f3001e703375,0x3cc00f3f3003db30007d4c003db307983cc01e6000fa98003ea6000f6cde6003d39800f3f3001e722395,0x3cc1e60f307992fc97e3cc0798f3097e3cc25f8000f4e6003ea6000f6cc79800fa9800f3f3001eacf375,0x4004300108044200100084002202001100080ca3,0x0,0x3cc01e6f301e72fc03cfcc01e6f30811bcc2046000f4e6003ea6000f6cc79800fa9800f3f3001e703375,0x0,0x4010300408050200400084002202001100082ca3,0x0,0x4010300808050200c00084002202001100086ca3,0x0,0x0,0x600018040200080084002208001000080ca3,0x0,0x0,0x400020011000080040000000010000000240002010100000000400020001000000400002010000008040000010080000010100400000100000000404000000800000001001087fea7,0xf33cc03cd0230f3408c001f53079fd4c0111600f4e6003ea6000f6cc003cd0230f3f3003cde703375,0x0,0xf33cc03cfdb30f37d4c001f53079fd4c0370e00f4e6003ea6000f6cc003cd0230f3f3003cde703375,0x0,0x0,0xf31e603cde600f31e9cc03ccf303cc3cc03ccf300079bcde61116007a731e603cc79fa7301e6317156,0x0,0xf33cc03ccf300f33cfcc03ccf303cc3cc03ccf3000799e7e616c8007a731e603cc79fa7300f3812d56,0x0,0xf307980001e60f300003cc1e60f307983cc0000003d39800f379800f6cfcc003db30003cc0001e64dc35,0x1e60000f30f301e63cc0000f307983cc16c8000f6cc003ea6000f6cc00001f53000f300001e703885],
[0xf307980001e60f300003cc1e60f307983cc0000003d39800f379800f6cfcc003db30003cc0001e64dc35]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4010 : TreeBound (n := 4) 107 (programCode 0x4e2b077832) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40002000100008000000060000000180000000600000001001000004004000018000400001001000004004000008000c0001004000001010000004040000008100000010010873227,0x0,0x280501184222,0x280501184222,0x280501100222,0x280501184222,0x28050118c642,0x280501108642,0x280501184222,0x280501108642,0x0,0x4400110000900024000840020808040200100e4,0x280501108642,0x4400110000900024000880020810080400100e4,0x0,0x0,0x0,0x0,0x0,0x280501184222,0x280501184222,0x280101100222,0x280501184222,0x280d0118c642,0x280d01188642,0x280501184222,0x280d01188642,0x0,0x8200000020800000082000000208000000002000080040000200080000800080000004004000080010000100000000100100040000080800000001000120001000002000151da8,0x280d0118c642,0x4400110000100404000800020810080400100e4],
[0x0,0x4003a000100028000000060001000480000002201a0000100100001200200002802042c0010010200008040400080004000100403400100002000084004000810040001001087ce67,0x0,0x0,0x0,0x280501184222,0x280501184222,0x280501100222,0x280501184222,0x28050118c642,0x280501108642,0x280501184222,0x280501108642,0x0,0x0,0x280501108642,0x0,0x4400110001100044000800020800402000100e4,0x0,0x0,0x0,0x1ed98007b66000fa983d4d6f000102300003cc0044691603cc0000f37d4c1e688b07983cc0001e61df6,0x0,0x280901184222,0x280901184222,0x280901180222,0x280901184222,0x28090118c642,0x280901188642,0x280901184222,0x280901188642,0x0],
[0x0,0x28090118c642,0x0,0x0,0x0,0x0,0x0,0x0,0x280501184222,0x280501184222,0x280501100222,0x280501184222,0x280d0118c642,0x280d01188642,0x280501184222,0x280d01188642,0x0,0x1ed98007b66000fa9804d2ef003ccf3000408c003d696f83d39800f379bcc26901cc1e60f3001e61df6,0x280d0118c642,0x0,0x0,0x0,0x0,0xacfec00000002b3fb0159fd80acfec0568471a1dfb00000568a2fec00000ad29ffb000002b3fb00000002b4263fb00000567f759fd800056ab41ded4002b3fbacfec0002b6aefb0159fd8000567f60000000567f600000000acff17c3bda80ad0019fd8000567f602b3fb00567f60000000015a53ff60000159fd800000002b452c3bda8002b3fb000000015a53ff60000015a00e1a8e12970ab,0x0,0x280901184222,0x280901184222,0x280901180222,0x280901184222,0x28090118c642,0x280901188642,0x280901184222],
[0x280901188642,0x0,0x0,0x28090118c642,0x0,0x0,0x0,0x0,0x0,0x0,0x40000000300000000804000002010000008040200000100001000400004001000010400001001000004004000008000c0001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x4004100000100004000800020880402000100e4,0x0,0x0,0x0,0x4000100000100004000800020880402000100e4,0x4040101028100204000860020880402001128e4,0x0,0x40801020301004040009a0020880402006934e4,0x4000100000100004000800020880402000100e4,0x4100104020100804000820020880402000100e4,0x40001000100004000004008000010010000040200000100600000401800001006000400001001000004004000008000c0001004000001010000004040000008100000010310873227,0x4200108040101004000820020880402000100e4,0x0,0xfa98003ea6000f41160f33cc0f33cc00f33cc000f37980f379800f37d4c007a7307983cc0007ba7e16,0x4004100108100204000840020880402001128e4,0x0,0x0,0x4044105008100204000840020880402001128e4],
[0x401010040810020400084002088040200112ee4,0x4400101108100204000840020880402001128e4,0x402010080810020400084002088040200112ce4,0x4100100008100204000840020880402001128e4,0x4040101008100204000840020880402001128e4,0x404010080810020400084002088040200112ce4,0x4080102008100204000840020880402001138e4,0x4040104008100204000840020880402001128e4,0x4100104008100204000840020880402001128e4,0x600010001800040002000080008000100060003000080004000200010000800020004200010010800040042000080004000100400000101000000404000000810000001021087fa67,0x4200108008100204000840020880402001168e4,0x0,0x280d01184222,0x280d01184222,0x280d01180222,0x280d01184222,0x280d0118c642,0x280d01188642,0x280d01184222,0x280d01188642,0x0,0x0,0x280d0118c642,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4004100110100404000880020880402002130e4,0x0],
[0x0,0x4084106010100404000880020880402002130e4,0x4010100410100404000880020880402002136e4,0x4400102110100404000880020880402002130e4,0x4020100810100404000880020880402002134e4,0x4100100010100404000880020880402002130e4,0x4040101010100404000880020880402002138e4,0x4080100810100404000880020880402002134e4,0x4080102010100404000880020880402002130e4,0x4080104010100404000880020880402002130e4,0x4100104010100404000880020880402002130e4,0x0,0x4200108010100404000880020880402002170e4,0x0,0x40000000300000000840000002100000008400200001000000084000000210000010400001001000004004000008000c0001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0xf300003cc0798f30000003cc0003cc00003cc000f37980f300000f37d4c0000f307983cc0007985216,0x0,0x40000010100000040040000080100000100400200001000001004000004010000600400001001000004004000008000c0001004000001010000004040000008100000010010873227,0x4020100800100004000800020880402000100e4,0x4000100000100004000800020880402000100e4,0x1e679807987980f31ebbad6f000f3f307983cc0044698f83cde600f37d4c1e688b07983cc0001e61df6,0x4000100800100004000800020880402000100e4,0x8004000040020000100080000200100200002001000140000008020009000080000004004000088000800040040000100104000200010000800040002000100000000800052e28,0x4000100000100004000800020880402000100e4,0x1e9cc0079bcc00f3f35bad6f000f3f307983cc0044698f83cde600f37d4c1e688b07983cc0001e61df6,0x40001000100004000040008000100010000400200001000100004000400010006000400001001000004004000008000c0001004000001010000004040000008100000010390873227,0x0,0x4400110020100804000820020880402000100e4,0x0],
[0x40000000300000000a00000002c0000000a000200008000000090000000220000010400001001000004004000008000c0001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x40000002100000008200000020c00000082000200008000000810000002020000100400001001000004004000008000c0001004000001010000004040000008100000010018c73227,0x0,0x0,0x0,0x1ed9a5ff980000f3003cd023000102300003cc0044673003cc0000f37d4c1e688b07983cc0001e61df6,0x1e679807987980f31e601023000102300003cc0044673003cc0000f37d4c1e688b07983cc0001e61df6,0x0,0x0,0x1eda7307980000f3003cd023000102300003cc0044673003cc0000f37d4c1e688b07983cc0001e61df6,0x0,0x40001000100004000200008000c00010002000200008000400010001000020006000400001001000004004000008000c0001004000001010000004040000008100000010210873227,0x0,0x4400110040101004000820020880402000100e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4219 : TreeBound (n := 4) 107 (programCode 0x4e2b077833) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c83cc001f53079fd4c1e7e600f4e600f4e6001e9cc003ccf300f3f3003cde703375,0x7980001e60f307983cc0000f307983cc1e60003d39800f4e6001e9cc00003cc0000f33cc01e703d95,0x25f80011160f307983cc001f5307a76cc1e60001e9cc00f4e6001e9cc00799e603ccf300799e703885,0x7980001e60f307983cc0000f307983cc1e60001e9cc00f4e6001e9cc00001e60000f3016c9e703885,0x0,0x280900108022,0x280500108022,0x280100108022,0x280500108022,0x280900108022,0x280900108022,0x280100108022,0x280900108022,0x0,0x0,0x280900108022,0x0,0x0,0x282100108022,0x0,0x282100108022,0x1ed98007b660f307983cc01e6f307983cc1e60003d39800f4e6001e9cc07983cc1e60f708c01e703d95,0x1ed98007b660f307983cc01e6f307983cc1e60003d39800f4e6001e9cc07983cc1e60f303cc1e703d95,0x7980001e60f307983cc0000f307983cc1e60000f4e600f4e6001e9cc00000f30000f6cc001e703375,0x0,0x800620018042200080084004200801020080ca3,0x3cc0000f3000f30079bcc0000f307983cc0000003d39800f4e6001e9cc0f303cc3cc0f30f301e703d95,0x3cc01e6f30088b00012fc003db307983cc003cc03d39800f4e6001e9cc0f303cc3cc0f30f301e722395,0x0,0x0,0x1e60f307983cc0f30408c0f30f303cc3cc03ccf307a73001e60000007d53b660f30000001e600001e56],
[0x3cc0f30f303db30007d4c01e6f307983cc01e6003d39800f4e6001e9cc0f303cc3cc0f30f301e703d95,0xf6d3b663cc1e6f6d3b69cc0000f307983cc1e60000f4e600f4e6001e9cc0f300f3f300f30f301e7033d5,0x804220108040200000084004200801020080ca3,0x0,0xf6cc1e63cc1e6f6cc3cfcc0000f307983cc1e60000f4e600f4e6001e9cc0f300f3f300f30f301e7033d5,0x0,0x810220408050200400084004200801020082ca3,0x0,0x810220808070200c00084004200801020086ca3,0x0,0x0,0x44000300008a0030001080042004022500814e3,0x4400110000900024000840220808044200100e4,0x280100110022,0x1ed98007b66000fa980010230003db30007d4c1357a8b0079f983cc079bcc26ae7cc00f3f3003cc3c56,0x280902110442,0x280902110442,0x280100110022,0x280902110442,0x0,0x0,0x280902110442,0x0,0x0,0x0,0x0,0x0,0x3d39803cde60fa9f983cc0000f307983cc1e60000f4e600f4e6001e9cc0f300f3f300f31e601e703375,0x0,0x0,0x4400110000900024000880420810084400100e4,0x280100110022],
[0x0,0x280902110442,0x280902110442,0x280100110022,0x280902110442,0x0,0x0,0x280902110442,0x0,0x0,0x0,0x7980001e61c7a79807980007987980f31e60000f4e600f4e6001e9cc00000f30000fa1e801e703375,0x0,0x0,0x2000680018040600090084004202001080080ca3,0x1e607987981e6f30079bcc01e6f307983cc01e6003d39800f4e6001e9cc79803cde600f379801e703d95,0x1e6001ed980088b00012fc0004bf07983cc003cc03d39800f4e6001e9cc79803cde600f379801e7241f5,0x1e67980799e60f3000222c00088b07983cc1e9cc03d39800f4e6001e9cc79803cde600f379801e726055,0x0,0x1e60f307983cc0f30408c0f30f303cc3cc03ccf307a73001e60000007d53b660f30000003cc00001e56,0x1e6003d39803dd16007d4c001f53079fd4c0370e00f4e600f4e6001e9cc79800f4e600f379801e703375,0x0,0x2004280108044200100084004202001080080ca3,0x0,0x0,0x0,0x2010280408050200400084004202001080082ca3,0x0,0x2010280808060200c00084004202001080086ca3,0x0,0x0,0x144000300008a0030001080042014022000814e3],
[0x0,0x280902120442,0x0,0x280902120442,0x280902120442,0x280902120442,0x280902120442,0x0,0x0,0x280902120442,0x0,0x0,0x282102120442,0x0,0x282102120442,0x0,0x2000700018040600090084004202001100080ca3,0x1e60001e600012fc0d4dcc0000f307983cc21b2800f4e600f4e6001e9cc79800fa9800f3f3001e703375,0x1e600097e0008c7c0012fc0002d9079a22c006e1c0f4e600f4e6001e9cc79800fa9800f3f3001e703375,0x3cc1e61e60f30f3000315c0798f30b643cc1723201e9cc00f4e6001e9ccf3001ed9800f3f3001f267885,0x0,0x3cc007b66003db307af04c001f5307a76cc2139001e9cc00f4e6001e9ccf3001ed9800f3f3001e703885,0x3cc007b66003db30007d4c001f5307a76cc02d9001e9cc00f4e6001e9ccf3001ed9800f3f3001e703885,0x3cc1e61e60f30f307983cc0798f30b643cc3528001e9cc00f4e6001e9ccf3001ed9800f3f3001f267885,0x2004300108044200100084004202001100080ca3,0x0,0x7980799e601e6f3003cfcc01e6f307983cc2046003d39800f4e6001e9cde6003d39800f3f3001e703d95,0x0,0x2010300408050200400084004202001100082ca3,0x1e60001e61e612fc7983cc0000f307983cc1e60000f4e600f4e6001e9cc79800fa9800f3f3001e703375,0x2010300808050200c00084004202001100086ca3,0x7983cc1e61e60f30b643cc0f30f307983cc2d90003d39800f4e6001e9cde6003d39800f3f3001ee9bd95],
[0x0,0x0,0x0,0x280902120442,0x0,0x280902120442,0x280902120442,0x280902120442,0x280902120442,0x0,0x0,0x280902120442,0x0,0x0,0x282102120442,0x7980001e60b647980f300007987980f31e60001e9cc00f4e6001e9cc00001e60000f6cc001e703885,0x282102120442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4364 : TreeBound (n := 4) 107 (programCode 0x4e2b077834) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c83cc001f53079fd4c1e7e600f4e6003ea6000f6cc003ccf300f3f3003cde703375,0x0,0x280501184222,0x280501184222,0x280501184222,0x280501184222,0x280d01184222,0x280901184222,0x280501184222,0x280901184222,0x0,0x0,0x280d01184222,0x0,0x0,0x282101104222,0x7980001e607987981e600007987980f31e600000799e601e679803cc00003cc0000f33cc01e703d95,0x282101104222,0x44580011160f307983cc003db307983cc1e60003d39800f4e6003cfcc00f33cc03ccf300799e722395,0x7980001e60f307983cc0000f307983cc1e6000001e60001e600003cc00000f30000f300001e703375,0x7980001e60f307983cc0000f307983cc1e6000001e60001e600003cc01e60f30798f301e61e703375,0x0,0x280d01188642,0x280501108642,0x280d01188642,0x280501108642,0x280d01188642,0x280901188642,0x280d01188642,0x280901188642,0x0],
[0x0,0x280d01188642,0x0,0x0,0x282101108642,0x0,0x282101108642,0x7980001e60f307983cc0000f307983cc1e6000001e60001e600003cc01e60f31e60f303cc1e703375,0x0,0x280d01188642,0x280501108642,0x280d01188642,0x280501108642,0x280d01188642,0x280901188642,0x280d01188642,0x280901188642,0x0,0x0,0x280d01188642,0x0,0x0,0x282101108642,0x7980001e60b647980f300007987980f31e6000003cc0001e600003cc00001e60000f5d9001e703885,0x282101108642,0x0,0x0,0x0,0x0,0x400010000000010000080002008020200814e3,0x2400090002080090002080082008020200814e3,0x400010000000010000080002008020200814e3],
[0x4400110004080110004080102008020200814e3,0x400010000000010000080002008020200814e3,0x0,0x0,0x10400410010000410010080402008020200814e3,0x0,0x0,0x0,0x7980001e60d4a79807980007987980f31e603cc01e6f301e63cc03cc0f300f33cc0f30f301e703375,0x0,0x0,0x0,0xf30079bcc0798f300b6403ccf303cc3cc03cc001e6798097e0001e6798f4e600f307980f3003f9c3b6,0x0,0xf300f37980798f3012fc0798f301e63cc03cc0025f8001119cc01e6799e60f3079fd5b3f3007dcac26,0x0,0x0,0xfa98003cde600f3012fc03ccf303cc3cc03cc001e6798097e0001e6798f4e600f307980f3003f9c3b6,0x0,0xf300003ea6000f3003cc03ccf303cc3cc03cc001e6798097e0001e6798f4e600f307980f3003f9c3b6,0xf33cc0798f300f31e9cc0798f301e63cc03cc0025f8001119cc01e6799e60f3079fd5b3f3007dcac26,0x0,0xf33cc0799e600f33cfcc0798f301e63cc03cc0025f8001119cc01e6799e60f3079fd5b3f3007ebdc26,0x0,0xf4e60079f9800f3f33cc0798f301e63cc03cc0025f8001119cc01e6799e60f3079fd5b3f3007dcac26,0x0,0xf4e6007a73000f4e63cc0798f301e63cc03cc0025f8001119cc01e6799e60f3079fd5b3f3008562c26,0x0,0x280d0118c642,0x280501108642,0x280d0118c642,0x280501108642],
[0x280d0118c642,0x28090118c642,0x280d0118c642,0x28090118c642,0x0,0x0,0x280d0118c642,0x0,0x0,0x282101108642,0x7980001e60b647980f300007987980f31e603cc03cde601e6b6403cc1e601e6f300f31e601e703885,0x282101108642,0x0,0xf6cc003db3000fad4fcc03ccf303cc3cc03cc001e6798097e0001e6799e7e6007983cc1e60044d4bb6,0xf30079bcc0798f300b6403ccf303cc3cc03cc001e6798097e0001e6799e7e6007983cc1e60044d4bb6,0x0,0xf300f37980798f3012fc0798f301e63cc03cc0025f8001119cc01e6799e60f30f381274e6007dcac26,0x0,0x0,0x0,0x0,0xf300003ea6000f3003cc03ccf303cc3cc03cc001e6798097e0001e6799e7e6007983cc1e60044d4bb6,0xf33cc0798f300f31e9cc0798f301e63cc03cc0025f8001119cc01e6799e60f30f381274e6007dcac26,0x0,0xf33cc0799e600f33cfcc0798f301e63cc03cc0025f8001119cc01e6799e60f30f381274e6007ebdc26,0x0,0xf4e60079f9800f3f33cc0798f301e63cc03cc0025f8001119cc01e6799e60f30f381274e6007dcac26,0xf33cc03cc03ccfa983cc03ccf303cc3cc03cc001e6798097e0001e6799e7e6007983cc1e60044d4bb6,0xf4e6007a73000f4e63cc0798f301e63cc03cc0025f8001119cc01e6799e60f30f381274e6008562c26,0x0,0x0,0x0],
[0x0,0x400010000000010000080002020020800814e3,0x2400090002080090002080082020020800814e3,0x400010000000010000080002020020800814e3,0x4400110004080110004080102020020800814e3,0x400010000000010000080002020020800814e3,0x0,0x0,0x10400410010000410010080402020020800814e3,0x0,0x0,0x400010000002010000080002020020800814e3,0x7980001e60b647980f300007987980f31e60b6403ced901e6b6403cc79801e7e600f379801e703885,0x400010000002010000080002020020800814e3,0x0,0xf300003f99000fe643cc03ccf303cc3cc03cc001e6798097e0001e679f99e607983cc079800445b3b6,0xf30079bcc0798f300b6403ccf303cc3cc03cc001e6798097e0001e679f99e607983cc079800445b3b6,0x0,0xf300f37980798f3012fc0798f301e63cc03cc0025f8001119cc01e67a7307983cc97efa98007d51426,0x0,0x0,0x0,0x0,0xf300003ea6000f3003cc03ccf303cc3cc03cc001e6798097e0001e679f99e607983cc079800445b3b6,0xf33cc0798f300f31e9cc0798f301e63cc03cc0025f8001119cc01e67a7307983cc97efa98007dcac26,0x0,0xf33cc0799e600f33cfcc0798f301e63cc03cc0025f8001119cc01e67a7307983cc97efa98007e44426,0x0,0xf4e60079f9800f3f33cc0798f301e63cc03cc0025f8001119cc01e67a7307983cc97efa98007d51426,0xf6cc003cc03ccf6d4c7c03ccf303cc3cc03cc001e6798097e0001e679f99e607983cc079800445b3b6,0xf4e6007a73000f4e63cc0798f301e63cc03cc0025f8001119cc01e67a7307983cc97efa980084e9426,0x7980001e60f307983cc0000f307983cc1e6000003cc0001e600003ccf3001ed9800f3f3001e703885],
[0x0,0x1e600007c59000f6cc3cc0798f301e63cc03cc004458001119cc01e67b660f30798b65f53000811d936,0x0,0x0,0xf300f37980798f3012fc0798f301e63cc03cc0025f8001119cc01e67a730798798b650230007d51426,0x1e9cc007c59798faa76cc0798f301e63cc03cc004458001119cc01e67b660f30798b65f53000811d936,0x0,0x1e9cc007c59798f30222c0798f301e63cc03cc004458001119cc01e67b660f30798b65f53000811d936,0x0,0x0,0xf33cc0798f300f31e9cc0798f301e63cc03cc0025f8001119cc01e67a730798798b650230007dcac26,0x0,0xf33cc0799e600f33cfcc0798f301e63cc03cc0025f8001119cc01e67a730798798b650230007e44426,0x0,0xf4e60079f9800f3f33cc0798f301e63cc03cc0025f8001119cc01e67a730798798b650230007d51426,0x1e601e67a77458f3003cc0798f301e63cc03cc004458001119cc01e67b660f30798b65f53000811d936,0xf4e6007a73000f4e63cc0798f301e63cc03cc0025f8001119cc01e67a730798798b6502300084e9426]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4541 : TreeBound (n := 4) 107 (programCode 0x4e2b077835) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x24000300008a0030002080082080022000814e3,0x0,0x280502108442,0x280503184642,0x280502108442,0x280503184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x0,0x0,0x280502108442,0x0,0x0,0x0,0x0,0x0,0x24000500010a0050002080082080022000814e3,0x0,0x280502108442,0x280503184642,0x280502108442,0x280503184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x2400090002080090002080082008020200814e3,0x0,0x280502108442],
[0x0,0x2400010000080090002080082020020800814e3,0x0,0x2400090002080090002080082040021000814e3,0x0,0x280902140442,0x280902140442,0x280902140442,0x280902140442,0x0,0x6090c2240481,0x0,0x6090c2240481,0x0,0x611082240481,0x621082240481,0x611082240481,0x631082240481,0x621082240481,0x621082240481,0x621082240481,0x621082240481,0x641182240501,0x621082240481,0x641182240501,0x631082240481,0x0,0x6098c2240481,0x4004100108100204028840a00880462005128e4,0x6098c2240481,0x1e601e67980798f300f3f33cc03ccf300f33cc233d7e679f9f9a22c07d4c22c89f002634c04496f57f6,0x611082240481],
[0x621082240481,0x611082240481,0x631082240481,0x621082240481,0x621082240481,0x621082240481,0x621082240481,0xe43182240501,0x621082240481,0xe43182240501,0x631082240481,0x280902140442,0x0,0x2088c2240481,0x4004100110100404030880c008804a2006130e4,0x2088c2240481,0x1e601e67980798f300f6cc3cc0f30f301e63cc2ea1d9879fb662d9007d4c24351f008154c05b5fabbf6,0x210082240481,0x220082240481,0x210082240481,0x210082240481,0x220082240481,0x220082240481,0x220082240481,0x200082240481,0x240982240501,0x220082240481,0x240982240501,0x210082240481,0x0,0xa0a0e2240481,0x208902140442],
[0xa0a0e2240481,0x208902140442,0xa120c2240481,0xa22082240481,0xa120c2240481,0xa521c2240501,0xa22082240481,0xa22082240481,0xa22082240481,0xa521c2240501,0xa42182240501,0xa22082240481,0xa42182240501,0xa521c2240501,0x282102140442,0x0,0xa0a0e2240481,0x0,0xa0a0e2240481,0x0,0xa120c2240481,0xa22082240481,0xa120c2240481,0xa521c2240501,0xa22082240481,0xa22082240481,0xa22082240481,0xa521c2240501,0xa42182240501,0xa22082240481,0xa42182240501,0xa521c2240501],
[0x282102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4670 : TreeBound (n := 4) 107 (programCode 0x4e2b077836) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x14c000300008a0030014080502080022000814e3,0x0,0x280502108442,0x280502184642,0x280502108442,0x280502184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x0,0x0,0x280502108442,0x0,0x0,0x0,0x0,0x0,0x154000500010a0050014080502080022000814e3,0x0,0x280502108442,0x280502184642,0x280502108442,0x280502184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x400010000000010000080002008020200814e3,0x0,0x280502108442],
[0x0,0x400010000000010000080002020020800814e3,0x0,0x400010000000010000080002040021000814e3,0x0,0x280902140442,0x280902140442,0x280902140442,0x280902140442,0x0,0x6090c6240481,0x0,0x6090c6240481,0x0,0x411084240481,0x401000240481,0x411084240481,0x421000240481,0x421000240481,0x401000240481,0x421000240481,0x421000240481,0x441108240501,0x401000240481,0x441108240501,0x421000240481,0x0,0x6098c6240481,0x209102340d02,0x6098c6240481,0x209102340d02,0x411084240481],
[0x240481,0x411084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x280902140442,0x0,0x6098c6240481,0x209102340d02,0x6098c6240481,0x209102340d02,0x10084240481,0x240481,0x10084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40108240501,0x240481,0x40108240501,0x240481,0x0,0x0,0x208902140442],
[0x0,0x208902140442,0xe120c6240481,0x802000240481,0xe120c6240481,0x842108240501,0x822084240481,0x802000240481,0x822084240481,0x842108240501,0x842108240501,0x802000240481,0x842108240501,0x842108240501,0x282102140442,0x0,0x0,0x0,0x0,0x0,0xe120c6240481,0x802000240481,0xe120c6240481,0x842108240501,0x822084240481,0x802000240481,0x822084240481,0x842108240501,0x842108240501,0x802000240481,0x842108240501,0x842108240501],
[0x282102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4799 : TreeBound (n := 4) 107 (programCode 0x4e2b077837) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1ed98007b660f307983cc01e6f307983cc1e6001e67980799e600f33cfcc003db3000f6cc001e703d95]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4800 : TreeBound (n := 4) 107 (programCode 0x4e2b077838) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x280902108442,0x280902104442,0x280902108442,0x280902104442,0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0,0x282902110442,0x280902108442,0x282902110442,0x0,0x0,0x0,0x0,0x0,0x280502108442,0x280502184642,0x280502108442,0x280502184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x0,0x0,0x280502108442,0x0,0x0],
[0x0,0x0,0x0,0x0,0x280902108442,0x280d02184642,0x280902108442,0x280d02184642,0x280902108442,0x280902108442,0x280902108442,0x280902108442,0x0,0x280902110442,0x280902108442,0x280902110442,0x0,0x280902120442,0x0,0x280902120442,0x0,0x280502108442,0x280502184642,0x280502108442,0x280502184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x400010000000010000080002008020200814e3,0x0,0x280502108442],
[0x0,0x400010000000010000080002020020800814e3,0x0,0x400010000000010000080002040021000814e3,0x0,0x280902140442,0x280902140442,0x280902140442,0x280902140442,0x0,0x409044240481,0x402000004000400004020000040004000100000000100800001002000001000000004001000040001000040010000400010040000010100000010400000101000000100208793a7,0x409044240481,0x402000004000080004020000040000800100000000100800001002000001000000004000400040001000040010000400010040000004100000010400000101000000100208593a7,0x411084240481,0x401004240481,0x411084240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441104240501,0x401004240481,0x441104240501,0x421004240481,0x0,0x6098c6240481,0x209102340d02,0x6098c6240481,0x209102340d02,0x411084240481],
[0x240481,0x411084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x280902140442,0x0,0x8040240481,0x209102340d02,0x8040240481,0x209102340d02,0x10080240481,0x240481,0x10080240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40100240501,0x240481,0x40100240501,0x240481,0x0,0x80a068240481,0x208902140442],
[0x80a068240481,0x208902140442,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x282102140442,0x7980001e60b647980f300007987980f31e6000003cc0001e6b6403cfcc001f53000f6cc001e703885,0x282102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_4945 : TreeBound (n := 4) 107 (programCode 0x4e2b077839) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030000820030008080202080022000814e3,0xf379803cde60f307983cc0000f3079803cde6003cc7980f31e603cc3cfcc003db3000f6cc001e703d95,0x1400050001020050008080202080022000814e3,0x0,0x3cc007a73002d90000b64001f53079f98f301e63cc3cc0f31e603cc3cfcc001f53000f6cc001e703885,0x0,0x3cc01e6f30088b00012fc003db3079800f303cc3cc7980f31e603cc3cfcc003db3000f6cc001e722395,0x0,0x0,0x0,0x3cc0f30f303db30007d4c01e6f3079800f31e603cc7980f31e603cc3cfcc003db3000f6cc001e703d95,0xf6d3b663cc1e6f307983db3000f3079803cde6003cc3cc3cc1e603cc3cfcc001f53000f6cc001e7038e5,0x3cc1e60f307a73001e9cc0000f3079800f300003cc3cc0f31e603cc3cfcc001f53000f6cc001e703885,0x1e67980799e600f31e601023000408c0007d4d02746730097e003cc07d4c204e8b00012fc0003cc3cb6,0xf6cc3cc3cc1e6f3003cfdb3000f3079803cde6003cc3cc3cc1e603cc3cfcc001f53000f6cc001e7038e5,0x0,0x3ccf300f33ccf300f33cc03ccf3088b00f33cc03cc3cc0f31e603cc3cfcc001f53000f6cc001e8e9885,0x0,0x3cde600f3f30f301e63cc16c8f30d4a00f46c803cc3cc0f31e603cc3cfcc001f53000f6cc001f267885,0x0,0x2400090002080090008080202080022000814e3,0x0,0x6098c4240481,0xf30079bcc0798f300799e9cc01e9cc001e9cc000f37983cc01e60f37d4c1e60f3079fd4c001e610856,0x6098c4240481,0x0,0x411084240481,0x4240481,0x411084240481,0x4240481,0x20004240481],
[0x4240481,0x20004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x4400110004080110008080202080022000814e3,0x400010000000010008080202080022000814e3,0x0,0x409044240481,0xf300799e60798f300798408c0003cc000408c000f379801e60000f37d4c1e60f307983cc00000014c6,0x409044240481,0x0,0x411084240481,0x401004240481,0x411084240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441104240501,0x401004240481,0x441104240501,0x421004240481,0x0,0x6098c4240481,0x200410010810020402004082188042200582ca4,0x6098c4240481,0x0,0x411084240481],
[0x4240481,0x411084240481,0x4240481,0x20004240481,0x4240481,0x20004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x10400410010000410008080202080022000814e3,0x0,0x409044240481,0x200410010810040402004082288042200783ca4,0x409044240481,0x0,0x10084240481,0x4240481,0x10084240481,0x4240481,0x20004240481,0x4240481,0x20004240481,0x4240481,0x40104240501,0x4240481,0x40104240501,0x4240481,0x0,0x80a064240481,0x20400802020080812008080202080022000814e3],
[0x80a064240481,0x0,0x8120c4240481,0x802004240481,0x8120c4240481,0x842104240501,0x822084240481,0x802004240481,0x822084240481,0x842104240501,0x842104240501,0x802004240481,0x842104240501,0x842104240501,0x0,0x6098c4240481,0x4004100120100804000820020880402000100e4,0x6098c4240481,0x0,0x411084240481,0x4240481,0x411084240481,0x4240481,0x20004240481,0x4240481,0x20004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x0],
[0x80a064240481,0x0,0x80a064240481,0x0,0x8120c4240481,0x802004240481,0x8120c4240481,0x842104240501,0x822084240481,0x802004240481,0x822084240481,0x842104240501,0x842104240501,0x802004240481,0x842104240501,0x842104240501,0x0,0x0,0x4004100140101004000820020880402000100e4,0x0,0x0,0x411084240481,0x4240481,0x411084240481,0x4240481,0x20004240481,0x4240481,0x20004240481,0x4240481,0x40104240501,0x4240481,0x40104240501],
[0x4240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5106 : TreeBound (n := 4) 107 (programCode 0x4e2b07783a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x7084c6240481,0x0,0x7084c6240481,0x0,0x6088c6240481,0x6098c6240481,0x6088c6240481,0x8044240481,0x6090c6240481,0x6098c6240481,0x6090c6240481,0x6098c6240481,0x4000000035c6500020400400084000000084000004240008632900000008100000100001008010c650200000041000082001004000000810000002040000010100000010020862ba7,0x6098c6240481,0x0,0xfa98003ea6000f3f30f303cc3cc3cc0f303cc03cc079bcc01e63cc07d4c01e6f301e63cc01e62da556,0xf30079bcc0798f300b6403ccf303cc3cc03cc03cc079bcde6003cc07d4c1e60f307983cc01e62da556,0x0,0x7084c6240481,0x0,0x7084c6240481,0x0,0x6088c6240481,0x6098c6240481,0x6088c6240481,0x8044240481,0x6090c6240481,0x6098c6240481,0x6090c6240481,0x6098c6240481],
[0x0,0x6098c6240481,0x0,0x0,0x0,0x8200010c4486200000200000004001000010000000048620000100080000104000010008010c40020000080100000000100400000081000000204000001010000001002086aba7,0xf300f33cc03ccf300f30408c00408c000408c03cc079bcde6003cc07d4c1e60f30000b6401e62dc3b6,0x10d048508463e0001e679811494201ea45807a740ca179803ccf3088b3cfcc003db30007d4c001e68a8c5,0xf300f37980798f300f308118003ea60007d4c079f9801e7e9cc3cc07d4c00088b07d7d5c00f344ac26,0x1e601e67980798f300fa983cc1e60f300003cc03cc0798f300003cc07d4c0000f300003cc0079a264f6,0x208904340d02,0x2091043408e2,0x208904340d02,0xf300f33cc03ccf300f307d4c00222c0007d4c03cc079bcde6003cc07d4c1e60f300012fc01e62dc3b6,0x2091043408e2,0x209904340d02,0x2091043408e2,0x209904340d02,0x20a1041418e2,0x0,0x20a1041418e2,0x0,0x7104c6240481,0x0,0x7104c6240481,0x0,0x210884240481,0x411084240481,0x210884240481,0x10084240481,0x411084240481,0x411084240481],
[0x411084240481,0x10084240481,0xe120c6240481,0x411084240481,0xe120c6240481,0x411084240481,0x0,0x7304c6240481,0x0,0x7304c6240481,0x0,0x220884240481,0x240481,0x220884240481,0x240481,0x401000240481,0x240481,0x401000240481,0x240481,0x802000240481,0x240481,0x802000240481,0x240481,0xfa98003ea6000f379bcc03ccf303cc3cc03cc03cc079bcde6003cc07d4c1e60f307983cc01e62da556,0x0,0x7384c6240481,0x0,0x7384c6240481,0x0,0x210884240481,0x240481,0x210884240481],
[0x240481,0x421000240481,0x240481,0x421000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0xf300003ea6000f3003cc03ccf303cc3cc03cc03cc079bcde6003cc07d4c1e60f307983cc01e62da556,0x408010108020200401042020088048200205104,0x0,0x7204c6240481,0x0,0x7204c6240481,0x0,0x220884240481,0x20000240481,0x220884240481,0x20000240481,0x421000240481,0x20000240481,0x421000240481,0x20000240481,0x822084240481,0x20000240481,0x822084240481,0x20000240481,0x408010208020200401042020088048200205104,0x0,0xf405ce240501,0x0],
[0xf405ce240501,0x0,0x24098c240501,0x842108240501,0x24098c240501,0x40108240501,0x441108240501,0x842108240501,0x441108240501,0x40108240501,0x842108240501,0x842108240501,0x842108240501,0x40108240501,0x420010408020200401042020088048200205104,0x0,0xf405ce240501,0x0,0xf405ce240501,0x0,0x24098c240501,0x842108240501,0x24098c240501,0x40108240501,0x441108240501,0x842108240501,0x441108240501,0x40108240501,0x842108240501,0x842108240501,0x842108240501,0x40108240501],
[0x420010808020200401042020088048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5267 : TreeBound (n := 4) 107 (programCode 0x4e2b07783b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030000820030010080402080022000814e3,0x0,0x280502108442,0x280503184642,0x280502108442,0x280503184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x0,0x0,0x280502108442,0x0,0x0,0x0,0x0,0x0,0x1400050001020050010080402080022000814e3,0x0,0x280502108442,0x280503184642,0x280502108442,0x280503184642,0x280502108442,0x280502108442,0x280502108442,0x280502108442,0x10400410010000410010080402008020200814e3,0x0,0x280502108442],
[0x0,0x400010000000410010080402020020800814e3,0x0,0x400010000000410010080402040021000814e3,0x0,0x280902140442,0x280902140442,0x280902140442,0x280902140442,0x0,0x409044240481,0x0,0x409044240481,0x0,0x411084240481,0x401004240481,0x411084240481,0x421004240481,0x421004240481,0x401004240481,0x421004240481,0x421004240481,0x441104240501,0x401004240481,0x441104240501,0x421004240481,0x0,0x6098c4240481,0x209106340d02,0x6098c4240481,0x209106340d02,0x411084240481],
[0x4240481,0x411084240481,0x4240481,0x20004240481,0x4240481,0x20004240481,0x4240481,0x842104240501,0x4240481,0x842104240501,0x4240481,0x280902140442,0x0,0x409044240481,0x209106340d02,0x409044240481,0x209106340d02,0x10084240481,0x4240481,0x10084240481,0x4240481,0x20004240481,0x4240481,0x20004240481,0x4240481,0x40104240501,0x4240481,0x40104240501,0x4240481,0x0,0x80a064240481,0x208902140442],
[0x80a064240481,0x208902140442,0x8120c4240481,0x802004240481,0x8120c4240481,0x842104240501,0x822084240481,0x802004240481,0x822084240481,0x842104240501,0x842104240501,0x802004240481,0x842104240501,0x842104240501,0x282102140442,0x0,0x80a064240481,0x0,0x80a064240481,0x0,0x8120c4240481,0x802004240481,0x8120c4240481,0x842104240501,0x822084240481,0x802004240481,0x822084240481,0x842104240501,0x842104240501,0x802004240481,0x842104240501,0x842104240501],
[0x282102140442]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5396 : TreeBound (n := 4) 107 (programCode 0x4e2b07783c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x0,0x0,0xf300f33ea6000fe640007d4c00222c0007d4c07980799e7e60079807d4c1e60f300012fc00f3814bb6,0x2088c2240481,0x6098c6240481,0x2088c2240481,0x8040240481,0x409044240481,0x6098c6240481,0x409044240481,0x8040240481,0x500000008400000009000000084000000090002000210000040100000002100000101000010010000040010000040040000100400000101000000404000000410000001000887b1a7,0x6098c6240481,0xf6cc003ea6000fe643cc03cc079bcc3cfcfcc07980799e7f53079807d4c1f53f3003cfcc00f3812d56,0x0,0xf30079bcc0798f300b6403ccf303cc3cc03cc07980799e7e60079807d4c1e60f307983cc00f3812d56,0x0,0x0,0x0,0x0,0x0,0x2088c2240481,0x6098c6240481,0x2088c2240481,0x8040240481,0x409044240481,0x6098c6240481,0x409044240481,0x8040240481],
[0x12fc0010230007d4c0010230007d4c7b0b59803cfcc03d0bf01e63cc03cfcc001f53000f6cc001e707725,0x6098c6240481,0x1a94001e60000408c0011161ec6c0c001023002009407980000f300003cfcc003db30007d4c001e68c725,0xf307983ea6000f4e60f303cc3cc3cc0f303cc07980799e601e679807d4c00f3f301e63cc00f3822056,0x0,0x0,0x0,0x0,0x1e601e67980798f300f30fa98003ea60007d4c0f379803cde9cc79807d4c00088b0813a2c01e64c4936,0x1e601e67980798f300fa983cc1e60f300003cc0f30079bcc000079807d4c03ccf300f33cc01e62dc8f6,0x208904340d02,0x2091043408e2,0x208904340d02,0xf300f31e601e6f300f307d4c0003cc0007d4c07980798f4e60079807d4c1e60f300003cc007d6e5f26,0x2091043408e2,0x209904340d02,0x2091043408e2,0x209904340d02,0x20a1041418e2,0xf300f37980798f300f4e67990231e63cc03cc079fd4c3ce082c79807d4c00f3f3084e7cc01e653dc26,0x20a1041418e2,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481],
[0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x0,0x0,0x0,0x0,0x0,0x220882240481,0x240481,0x220882240481,0x240481,0x401004240481,0x240481,0x401004240481,0x240481,0x802008240481,0x240481,0x802008240481,0x240481,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481],
[0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x240481,0x210882240481,0x240481,0x421004240481,0x240481,0x421004240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0xf300003ea6000f3003cc03ccf303cc3cc03cc07980799e7e60079807d4c1e60f307983cc00f3812d56,0x408010108020200401042040088048200205104,0x0,0x0,0x0,0x0,0x0],
[0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x408010208020200401042040088048200205104,0x0,0x0,0x0,0x0,0x0,0x240982240501,0x842108240501,0x240982240501,0x40100240501,0x441104240501,0x842108240501,0x441104240501,0x40100240501,0x842108240501,0x842108240501,0x842108240501,0x40100240501,0x420010408020200401042040088048200205104,0x0],
[0x0,0x0,0x0,0xf300f33ccf300fa980007d4c00222c0007d4c07980799e7e60079807d4c1e60f300012fc00f3814bb6,0x240982240501,0x842108240501,0x240982240501,0x40100240501,0x441104240501,0x842108240501,0x441104240501,0x40100240501,0x842108240501,0x842108240501,0x842108240501,0x40100240501,0x420010808020200401042040088048200205104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5573 : TreeBound (n := 4) 107 (programCode 0x4e2b07783d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xc00030000820030020080802080022000814e3,0x0,0x4400110004080410020080802000820020814e3,0x400010000000410020080802000020400814e3,0x4400110004080410020080802001020040814e3,0x0,0x10400410010000410020080802002020080814e3,0xfa98003ea6000fa98000408c00408c000408cf30007981e610230007982046001ed98001e60f3181d6,0x10400410010000410020080802004020100814e3,0x400010000000410020080802000020000814e3,0x0,0x0,0x400010000000410020080802010020400814e3,0x0,0x0,0x0,0x0,0x0,0x1400050001020050020080802080022000814e3,0x0,0xc00030000820810020080802000820020814e3,0x400010000000810020080802000020400814e3,0x1400050001020810020080802001020040814e3,0x400010000000810020080802000020800814e3,0x0,0xfa98003ea6000fa980007d4c00222c0007d4cf30007987983db30007982046001ed98001e63cc2ee56,0x0,0x400010000000810020080802000020000814e3,0x0,0x0,0x400010000000810020080802010020400814e3],
[0x0,0x400010000000810020080802020020800814e3,0x0,0x400010000000810020080802040021000814e3,0x0,0x2400090002080090020080802080022000814e3,0x0,0x709cc8240481,0x208902140442,0x709cc8240481,0x208902140442,0x611888240481,0x8240481,0x611888240481,0x8240481,0x421008240481,0x8240481,0x421008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x4400110004080110020080802080022000814e3,0x400010000000010020080802080022000814e3,0x0,0x409048240481,0x0,0x409048240481,0x0,0x411088240481,0x401008240481],
[0x411088240481,0x421008240481,0x421008240481,0x401008240481,0x421008240481,0x421008240481,0x441108240501,0x401008240481,0x441108240501,0x421008240481,0x0,0x6098c8240481,0x209106340d02,0x6098c8240481,0x209106340d02,0x411088240481,0x8240481,0x411088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x10400410010000410020080802080022000814e3,0x0,0x4000100000800820080802080022000814e3,0x209106340d02,0x8000200000800820080802080022000814e3],
[0x209106340d02,0x10088240481,0x8240481,0x10088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40108240501,0x8240481,0x40108240501,0x8240481,0x0,0x80a068240481,0x208902140442,0x80a068240481,0x208902140442,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x400010000002010020080802080022000814e3,0x0],
[0x80a068240481,0x0,0x80a068240481,0x0,0x8120c8240481,0x802008240481,0x8120c8240481,0x842108240501,0x822088240481,0x802008240481,0x822088240481,0x842108240501,0x842108240501,0x802008240481,0x842108240501,0x842108240501,0x400010000002010020080802080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5718 : TreeBound (n := 4) 107 (programCode 0x4e2b07783e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x7084c6240481,0x0,0x7084c6240481,0x0,0x6088c6240481,0x6098c6240481,0x6088c6240481,0x6098c6240481,0x6090c6240481,0x6098c6240481,0x6090c6240481,0x6098c6240481,0x400030000000080004000210000000840020000100000100400000021000001040000080000200400000040800002001004000000810000004040000008100000010010863227,0x6098c6240481,0x4000300000000800040002c0000000900020000800000101000000022000001040000080000200400000040800002001004000000810000004040000008100000010010863227,0x4000100002000800080102080022000814e3,0xf30079bcc0798f300b6403ccf303cc3cc03cc1e6007b661e601e6007d4c1e60f30007d4c0f30799556,0xf6cc003ea6000fa9fd4c03ccf303cc3cc03cc1e6007b661e601e6007d4c1e60f30007d4c0f30799556,0x0,0x0,0x0,0x10d04850a2c3e0001ea45811494201ea45807a926ca1798222cf3088b3cfcc003db30007d4c001e68a8c5,0x0,0x1e601e67980798f3014eb13b0001f5300003cc798b7337980001e6007d4c2dec130007d4c03cc1f8f56,0x2089085414c2,0x20a9085414c2,0x2089085414c2,0x0,0x209108341d02,0x20a9085414c2],
[0x209108341d02,0x20a9085414c2,0x20a1081414c2,0x0,0x20a1081414c2,0x0,0x7104c6240481,0x0,0x7104c6240481,0x0,0x210884240481,0x411084240481,0x210884240481,0x10084240481,0x411084240481,0x411084240481,0x411084240481,0x10084240481,0xe120c6240481,0x411084240481,0xe120c6240481,0x411084240481,0x0,0x7304c6240481,0x0,0x7304c6240481,0x0,0x220884240481,0x240481,0x220884240481,0x240481,0x401000240481],
[0x240481,0x401000240481,0x240481,0x802000240481,0x240481,0x802000240481,0x240481,0x0,0x7104c6240481,0x0,0x7104c6240481,0x0,0x210884240481,0x411084240481,0x210884240481,0x10084240481,0x411084240481,0x411084240481,0x411084240481,0x10084240481,0xe120c6240481,0x411084240481,0xe120c6240481,0x411084240481,0x0,0x7384c6240481,0x0,0x7384c6240481,0x0,0x210884240481,0x240481,0x210884240481],
[0x240481,0x421000240481,0x240481,0x421000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x4200108040200008004000208001200080ca3,0x408010108020200404042080088062200805104,0x0,0x7204c6240481,0x0,0x7204c6240481,0x0,0x220884240481,0x20000240481,0x220884240481,0x20000240481,0x421000240481,0x20000240481,0x421000240481,0x20000240481,0x822084240481,0x20000240481,0x822084240481,0x20000240481,0x408010208020200404042080088062200805104,0x0,0xf405ce240501,0x0],
[0xf405ce240501,0x0,0x24098c240501,0x842108240501,0x24098c240501,0x40108240501,0x441108240501,0x842108240501,0x441108240501,0x40108240501,0x842108240501,0x842108240501,0x842108240501,0x40108240501,0x420010408020200404042080088062200804104,0x0,0xf405ce240501,0x0,0xf405ce240501,0x0,0x24098c240501,0x842108240501,0x24098c240501,0x40108240501,0x441108240501,0x842108240501,0x441108240501,0x40108240501,0x842108240501,0x842108240501,0x842108240501,0x40108240501],
[0x420010808020200404042080088062200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5879 : TreeBound (n := 4) 107 (programCode 0x4e2b07783f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x7980001e60f307983cc0000f307983cc1e601e601e7e601e63cc03cfcc001023000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_5880 : TreeBound (n := 4) 107 (programCode 0x4e2b077840) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80600018040200088004002200081002080ca3,0x0,0x80600018040200088004004200081004080ca3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x600018040200088004100202001100080ca3,0x600018040200088004000208001000080ca3,0x0,0x0,0x0,0x0,0x0,0x0,0x2089085414c2,0x20a9085414c2,0x2089085414c2,0xf30079f980798f300798408c7983cc000408c3cc007b661e603cc007d4c1e7f53000f6cc0f307995e6,0x209108341d02,0x20a9085414c2,0x209108341d02,0x20a9085414c2],
[0x20a1081414c2,0xf30079f980798f300c5703cc7983cc3cc03cc3cc007b661e9cfcc007d4c261753000f6cc0f307995e6,0x20a1081414c2,0x0,0xf30000f303cc88b00012fc001f5307983cc005b200f6cfcc01e6000f6cc003cde600f3f3003cde703885,0xf4e6003cc01e6fa9fd4c03ccf303cc3cc03cc3cc007a731e603cc0079805b20003cc798044583cd556,0x0,0x0,0x0,0xf6cc007cd64c0f307d4c0798f301e63cc03cc3cc7981e61e9cfcc007983cc1e60fc8d301f530799766,0x4000000050060000200000001100000001400000001000086304000200010000004000000040100600200400001000008001000008000400040002000200010000200010020852ba7,0x1e9cc007c5ccc0f30f6cc0798f301e63cc03cc7987981e61e9cfcc007987983cc1f173303db30799c76,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2089085414c2,0x20a9085414c2,0x2089085414c2,0x0,0x209108341d02,0x20a9085414c2],
[0x209108341d02,0x20a9085414c2,0x20a1081414c2,0x20001e000f000000020000800000000800000004000f00020002000020000000000000401e000020000000100000000100400000041000000204000001010000001002085aba7,0x20a1081414c2,0xf30003cc0001023000408c0000f307983cc00f300003cfcc01e600003cfcc001f53000f6cc001e703885,0x0,0x0,0x0,0x0,0x0,0x220882240481,0x240481,0x220882240481,0x240481,0x401004240481,0x240481,0x401004240481,0x240481,0x802008240481,0x240481,0x802008240481,0x240481,0x0,0x0,0x0,0x0,0x0,0x210880240481,0x411084240481,0x210880240481,0x10080240481],
[0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x0,0x0,0x0,0x0,0x0,0x210880240481,0x240481,0x210880240481,0x240481,0x421004240481,0x240481,0x421004240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x0,0x0,0x0,0x0,0x220882240481,0x20000240481],
[0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x408010108020200404042100088062200805104,0x0,0x0,0x0,0x0,0x0,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x421004240481,0x20000240481,0x421004240481,0x20000240481,0x822088240481,0x20000240481,0x822088240481,0x20000240481,0x408010208020200404042100088062200805104,0x0,0x0,0x0],
[0x0,0x0,0x240982240501,0x842108240501,0x240982240501,0x40100240501,0x441104240501,0x842108240501,0x441104240501,0x40100240501,0x842108240501,0x842108240501,0x842108240501,0x40100240501,0x420010408020200404042100088062200804104,0xf303cc00003ccf301e63cc3528f307983cc03ccf30079bcc007980003cfcc003db3000408c001ebffc35,0x420010808020200404042100088062200804104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_3816 : TreeBound (n := 4) 107 (programCode 0x4e2b0778) := by
  conv in programCode _ => reduce
  exact branchFour (k := (1,1)) (by decide +kernel) part103_3817 part103_4010 part103_4219 part103_4364 part103_4541 part103_4670 part103_4799 part103_4800 part103_4945 part103_5106 part103_5267 part103_5396 part103_5573 part103_5718 part103_5879 part103_5880

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6058 : TreeBound (n := 4) 107 (programCode 0x4e2b077961) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x40c050240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6059 : TreeBound (n := 4) 107 (programCode 0x4e2b077962) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x434090204481,0x424010210481,0x434090204481,0x0,0x434081204481,0x8000202080002000000080402000020000814e3,0x434081204481,0x424000200481,0x424002208481,0x424000200481,0x424002208481,0x0,0xf33cc222c0007980f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0xf33cc222c0007980f30b640f30f303cc3cc03ccf3445a22c1e60000f307991167983cc0f307983cc3cb6,0x0,0x4000000090004000240000000800010000c000080010000200040000800100000800400020001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x424000200481,0x4000000090004000240000000800010000c000080010000200040000800100000800400020001000480020000a00000002000080010001000048002000200010000200010002eaba8,0x0,0x424010208481,0x8100802018020200408040a00010442008040304,0x424010208481,0x0,0xf522c1e600007980f30b6c9a300003cc00003ccf307a952c0000f3000079fb69cc0fa98003cc1e6110c6,0xf30b67cc07980f30798408c00408c000408cf30000b64001f53000079bea6000fa98003cc1e610856,0x0,0xf30b640007980f307987d4c00222c0007d4cf30000b64001f53000079bea6000fa98003cc1e610856,0x0,0x0,0x0],
[0x0,0xf615c1e63cc07980f30b70663000f6cc000408cf307b0eac001f53000079fb69cc1ed98003cc1e611156,0x2000402010810020408004200010440010182ce4,0xf615c1e63cc07980f30b70663000f6cc000408cf307b0eac001f53000079fb69cc1ed98003cc1e611156,0x20004020110100404080082000104400102834e4,0x0,0x804020120100804080006000104400100804e4,0x0,0x804020140101004080006000104400100804e4,0x424010210481,0x8100802018020200408040a00011048020102904,0x424010210481,0xf30b640007980f30b6403ccf303cc3cc03ccf30000b641e60f300007b67e60079f9801e60f3812d56,0x424010220481,0x424010200481,0x424010220481,0x0,0x0,0x421010210481,0x6002000100001000080000000800010000e00210001000008000000080000000080040003001100000000c0000000100000000a00030010800000000800200002000100008017f1a8,0x0,0x420810208481,0x0,0x420810208481,0x0,0x421010210481,0x420010200481,0x421010210481,0x420010200481,0x422010220481,0x420010200481,0x422010220481],
[0x420010200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6124 : TreeBound (n := 4) 107 (programCode 0x4e2b077963) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x40c050240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6125 : TreeBound (n := 4) 107 (programCode 0x4e2b077964) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x3d3987d4c001e9d398b64001f53079fd4c1e7f53001e9cc01e6f3003cc003ccf303ccf3003cde7033d5,0x0,0x40200020100800001000000201008000000060040000100100001200400001801040000100100000400400000801000001004108001010c0000404008000800c0000100108732a7,0x808040200900024080006000200c00020100e4,0x168f08f99b7847ccdbc23e684702815c70000168f08f99b7847ccdbc23fa2b08f99b7847d3e8750c0793c23e66de11f3912cb372391e12085d08f9413c23e39c00033764c77cef8005ba67d63bfa2323e3c91e11f1ce0066f23cb1dc29c019614454292c8c8f8e70000ba1c0a0571c0002e87028167b7847ccdbc23e39c000070cb2cdc830000ba1c0a0571c0001ac9daa79250000168f08fbb8e11f771c23e94b09c2b6338000b74a28e654e0000168f090f7608f9141e11f1fb1e11f8263a8600f800005a3c23eee3847cf2e324fb29e,0x80008040201100044080006000200c00020100e4,0x0,0x0,0xf33cc1e603cc7981e612fd0230f300f3000408cf3079a22c0002d90000f3111679816c80003cc1e61df6,0x0,0xf33cc222c0007981e612fd0230f300f30007d4cf3079a22c0002d90000f3111679816c80003cc1e61df6,0x0,0x80808040200900044080006000200c00020100e4,0x0,0x0,0x100804022010080408000a000200c00020100e4,0x808040200900024080006000200c00020100e4,0x100804024010100408000a000200c00020100e4,0x3d398f6cc0079bd3983cc001f5307a76cc1e9db3003cfcc01e6f3003cc00799e603ccf300799e7038e5,0x0,0x40c041204481,0x8000200080002000000080402000020000814e3,0x40c041204481,0x404000200481,0x414082208481,0x404000200481,0x414082208481,0x0,0x0,0x0,0x0],
[0x0,0x802000002008080004004200010018004000262010000188040002620100001880080001000200004000400008001000010040000010101000040084000080300000100d4877627,0x404000200481,0x0,0x0,0x0,0x40c041208481,0x424004208481,0x40c041208481,0x404000208481,0x414082208481,0x404000208481,0x414082208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x444108208501,0x404000208481,0x444108208501,0x0,0x0,0x40c041208481,0x424004200481,0x40c041208481,0x404000200481,0x0,0x404000200481,0x0,0x0,0x424004200481],
[0x0,0x424004200481,0x0,0x8040204080102004020080802020020800834e3,0x404000200481,0x8000208080002000040081002000020000814e3,0x0,0x0,0x40c041208481,0x424004208481,0x40c041208481,0x404000208481,0x414082208481,0x404000208481,0x414082208481,0x0,0x424004208481,0x0,0x424004208481,0x0,0x444108208501,0x404000208481,0x444108208501,0x0,0x0,0xf522c1e600003cc1e613049a300003cc00003ccf307a952c0000f30000f37b69cc0fa98003cc1e6110c6,0xf3f3013085707981e60f308118002046000408cf3000f6cc1ec3ab0000f33ea6001ed9f983cc3cc1fd66,0x0,0xf300022348b07981e60f30fa98003ea60007d4cf3000f6cc1ea54b0000f37b66001eda7303cc3cc20276,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3d3987d4c001e9d3987983cde60445f9805b3f53001e9cc01e6f3003cc0f300f3f300f30f301e7033d5,0x804020090002408000a000200400040000e4,0xf33cc1e600003cc1e612fd02300003cc00003ccf3079a22c0000f300012fd11679807980007980001dc6,0x0,0x0,0x0,0x3d39bcfcc01e63d39f981e7e601ee4e403ed39f3001e9cc01e6f3003cc0f300f3f300f30f301e7033d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8040200100004080002000200400040000e4,0x0,0x0,0x0,0xf300012fcf307981e612fc0798f301e63cc03cc0025f800097e7980f30f4e60f3079ff320f30f344ac26,0x0,0xf300012fcf307981e612fc0798f301e63cc03cc0025f80011167981e60f4e60f3079fd4c0f30f344ac26,0x0],
[0x1e612fc0003cc1e612fc03ccf303cc3cc03cc007980f37b660007980f3f4e600f3003ccf31e62e3d36,0x0,0x0,0x20021000080084000100000000100020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x20021000080084000100000000100020040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x3b9bb86b2803b9bb86b283b9bb91df85fdce5636697f739c4e2ab3598c5e54acd66317952b35950c38aacd65430e2ab35950c3894735943b9ad1735943b9b4135943b9acdb9aca3b9ad8e6b28773d0759400775bc32968077acc99400775bc32968077571b11a00eef328c9f3669,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f3f4e600f3000f3f31e62dc3b6,0x0,0x0,0x0,0x3d3987d4c0079bd3980003cde60445f9805b3f53003cfcc01e6f3003cc1e601e6f300f31e601e7038e5,0x0,0x3d398f6cc0079bd398000799e604467300981db3003cfcc01e6f3003cc1e601e6f300f31e601e7038e5,0x80008040201100044080002000200400040000e4,0x0,0x0,0xf33cc1e600007981e612fd0230f300f300003ccf3079a22c0000f300012fd11679807980007980001df6,0x0,0x3d3b663cc1e603d3b660f30000f379800f4e60f3001e9cc01e6f3003cc0f300f3f300f31e601e7033d5,0x0,0x80008040200100044080002000200400040000e4,0x0,0x0,0x0,0x8040200100004080002000200400040000e4,0x0,0x0,0x1dcd6500002540c1f9acbdcd66dcd65f5de8140000773597b9acc540be47735b1cd653b9ad173594ee6b45cd651dcd6c735941dcd68b9ad8e6b3251467fc0c7cd6500000ef5993639aca3b9aca0001dd11eaca00003b9bbac099a289a09aca00ee6b280ee6ee1acbdcda18b390b0aa,0xf300012fcf307981e612fc0798f301e63cc03cc0025f800097e7980f30f4e61e60f384e41e61e64c4426,0x0],
[0xf300012fcf307981e612fc0798f301e63cc03cc0025f80011167981e60f4e60f30f384e41e61e653dc26,0x0,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc007980f37b660007980f4e7e60079803cde60f381c536,0x0,0x0,0x20021000080084000100000000100020040002000100000000400000001000000000200010000800040001000080001000100400000101000000404000000800000001001087fea7,0x0,0x20021000080084000100000000100020040002000100000000400000001000000000200010000800040001000080002000100400000101000000404000000800000001001087fea7,0x0,0x0,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc1e60011161e601e6000f4e7e60079800f4e60f3814bb6,0x0,0x0,0x0,0x42c041220481,0x424004220481,0x42c041220481,0x424004220481,0x434082220481,0x424000220481,0x434082220481,0x0,0x424004220481,0x0,0x424004220481,0x0,0x464188220501,0x424000220481,0x464188220501,0x0,0x0,0x40c041208481],
[0x424004200481,0x40c041208481,0x404000200481,0x0,0x404000200481,0x0,0x0,0x424004200481,0x0,0x424004200481,0x0,0x8040204080102004020080802020020800834e3,0x404000200481,0x8000208080002000040081002000020000814e3,0x0,0x3d3b663cc1e603d3b69cc0000f307983cc1e60f3001e9cc01e6f3003cc79800fa9800f3f3001e7033d5,0x0,0xf33cc222c0003cc1e612fc0f30f303cc3cc03ccf362b9e6097e0001e6111635283cc1e60f307983cfc26,0xf3000222cf307981e612fc0798f301e63cc03cc0025f800097e7980f311160f30798d4a0f30f3079d936,0x0,0xf3000222cf307981e612fc0798f301e63cc03cc0044580011167981e611160f30798b640f30f3079d936,0xf33cc222c0003cc1e612fc0f30f303cc3cc03cd6cc459e601e600000011162d97d4c0000f307983cfc26,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc007980f37b6600079810231e603cc003db307983d6d36,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e612fc0003cc1e612fc03ccf303cc3cc03cc1e60011161e601e60010231e603cc00102307983cf3b6,0x0],
[0x0]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6350 : TreeBound (n := 4) 107 (programCode 0x4e2b077965) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x414090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6351 : TreeBound (n := 4) 107 (programCode 0x4e2b077966) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x434081240481,0x8402008048020200400142002048040a00010104,0x434081240481,0x0,0x434081204481,0x0,0x434081204481,0x404000200481,0x404000208481,0x404000200481,0x404000208481,0x0,0x0,0x798408c003cc0798408c03ccf303cc3cc03cc001e63cc097e0001e63ccf4e600f307980f3003fa3d36,0x0,0x798408c003cc0798408c03ccf303cc3cc03cc001e63cc097e0001e63cde7e6007983cc1e60044dc536,0x404004220481,0x404000200481,0x404004220481,0x798408c003cc0798408c03ccf303cc3cc03cc001e63cc097e0001e63db31e603cc1e60f300040b5336,0x424002240481,0x404000240481,0x424002240481,0x0,0xf4e60f300003cc07984093a730f303cc00003cc01eda7307980000f30408c1e9db3000f6cc001e611156,0x0,0x0,0x0,0x420802240481,0x400000240481,0x420802240481],
[0x400000240481,0x401004240481,0x400000240481,0x401004240481,0x400000240481,0x40200c240481,0x400000240481,0x40200c240481,0x400000240481,0x404004240481,0x8402008048020200401042020048048200102b04,0x404004240481,0x798408c003cc0798408c03ccf303cc3cc03cc079803cde7e6007980408c1e60f307983cc00f381a6d6,0x404008240481,0x404000240481,0x404008240481,0x798408c003cc0798408c03ccf303cc3cc03cc3cc003db31e603cc00408c1e60f307983cc07983f34d6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6400 : TreeBound (n := 4) 107 (programCode 0x4e2b077967) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x414090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6401 : TreeBound (n := 4) 107 (programCode 0x4e2b077968) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x3d3987d4c001e9d398b64001f53079fd4c1e7e600f4e600f4e6000f6cc003ccf303ccf3003cde7033d5,0x3d3d4c3cc1e603d3983cc0000f307983cc1e60000f6cc00f4e6000f6cfea601f53000f33cc01e7038e5,0xf4e60f6cc001e60f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e600000000000000001dc6,0x3d39a634c0079bd3983cc001f53079fd4c1e7e600f6cc00f4e6000f6cc012fde604bff300f31e7038e5,0x0,0x0,0x3d39bcfcc01e63d39fd4c01e6f3084e7cc2139000f4e600f4e6000f6cc01e60f31e60f303cc1e7033d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3d48b03cc79803d57e3cc0798f3097e3cc25f8000f4e600f4e6000f6cc79800fa9800f3f3001eacf3d5,0x0,0x0,0x402000201008000810000002010000028000601400001001000012014000018050400001001080004004000008000c00010040000010100000040400000081000000100108732a7,0x0,0x0,0x0,0xf531ff300003cc0f307d54d6f000102300003cc0044698f83cc0000f37d4c1e688b07983cc0001e61df6,0x0,0x0,0x0,0x0,0x2002010080810020400084002088040200112ce4,0x0,0x20020100810100404000880020880402002134e4,0x20100800100004000800020880402000100e4],
[0x4020100820100804000820020880402000100e4,0x0,0x4020100840101004000820020880402000100e4,0x0,0x3d3987d4c0079bd3983cc001f53079fd4c1e7e601e9cc00f4e6001e9cc003cde603ccf3003cde7038e5,0xf307d4c001e60f307d4c03ccf303cc3cc03ccf30f379805b20f30f379805b200044587983cc1e61556,0x3d398f6cc0079bd3983cc001f5307a76cc1e9cc01e9cc00f4e6001e9cc00799e603ccf300799e7038e5,0xf4e60f6cc001e60f307d4c0f30f303cc3cc03ccf362c730097e0001e67981116b641e60f307983cc3c26,0x0,0xf4e60f6cc003cc0f307d4c0f30f303cc3cc03ccf307a73001e60000007987b66001e600001e600001e56,0xf4e60f6cc001e60f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e600000000000000001dc6,0x3d39803cc00003d3983cc0000f307983cc1e60000f4e600f4e6001e9cfcc000f30000f6cc001e7033d5,0x3d3b663cc1e603d3b69cc0000f307983cc1e60000f4e600f4e6001e9cc0f300f3f300f30f301e7033d5,0x0,0x3d3b663cc1e603d3d4fcc0000f307983cc1e60000f4e600f4e6001e9cc0f300f3f300f31e601e7033d5,0x0,0x0,0x0,0xf4e60f6cc003cc0f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e600000000000000001e56,0x0,0x0,0x3d3987d4c001e9d398b64001f53079fd4c1e7e600f4e6003ea6000f6cc003ccf303ccf3003cde7033d5,0x0,0xf4e60f6cc001e60f307d4c0f30f303cc3cc03cc00446730097e0001e67d4c1e679800000000003cc3c26,0x3d39803cc00003d3983cc0000f307983cc1e6000001e60001e600003cc00000f30000f300001e7033d5,0x3d39803cc00003d3983cc0000f307983cc1e6000001e60001e600003cc01e60f31e60f301e61e7033d5,0x0,0x3d39803cc00003d3983cc0000f307983cc1e6000001e60001e600003cc01e60f31e60f303cc1e7033d5,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x4184c2240481,0x0,0x4184c2240481,0x0,0x410882240481,0x431082240481,0x410882240481,0x410882240481,0x431082240481,0x431082240481,0x431082240481,0x410082240481,0x4521c2240501,0x431082240481,0x4521c2240501,0x410882240481,0x0,0x4384c6240481,0x0,0x4384c6240481,0x0,0x410884240481,0x400000240481,0x410884240481,0x400000240481,0x421000240481],
[0x400000240481,0x421000240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481,0xf4e60f6cc001e60f307d4c0f30f303cc3cc03ccf307a73001e60000007d4c1e60f300003cc0000001dc6,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x400000240481,0x410882240481,0x400000240481,0x421004240481,0x400000240481,0x421004240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481,0x0,0x408444240481,0x3d3d4c3cc1e603d3983ea6000f3079803cde6003cc3cc3cc1e603cc3cfcc001f53000f6cc001e7038e5,0x408444240481,0x3d3b663cc1e603d3983db3000f3079803cde6003cc3cc3cc1e603cc3cfcc001f53000f6cc001e7038e5,0x410884240481,0x400004240481],
[0x410884240481,0x400004240481,0x421004240481,0x400004240481,0x421004240481,0x400004240481,0x442104240501,0x400004240481,0x442104240501,0x400004240481,0x0,0x4384c6240481,0x0,0x4384c6240481,0x0,0x410884240481,0x400000240481,0x410884240481,0x400000240481,0x421000240481,0x400000240481,0x421000240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481,0x0,0x408444240481,0x0,0x408444240481,0x0],
[0x410884240481,0x400004240481,0x410884240481,0x400004240481,0x421004240481,0x400004240481,0x421004240481,0x400004240481,0x442104240501,0x400004240481,0x442104240501,0x400004240481,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x400000240481,0x410882240481,0x400000240481,0x421004240481,0x400000240481,0x421004240481,0x400000240481,0x442104240501,0x400000240481,0x442104240501,0x400000240481,0x0,0x428448240481,0x0],
[0x428448240481,0x0,0x430888240481,0x421008240481,0x430888240481,0x421008240481,0x421008240481,0x420008240481,0x421008240481,0x420008240481,0x462188240501,0x420008240481,0x462188240501,0x420008240481,0x0,0x4384c6240481,0x0,0x4384c6240481,0x0,0x410884240481,0x400000240481,0x410884240481,0x400000240481,0x421000240481,0x400000240481,0x421000240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481,0x3d3b663cc1e603d3b69cc0000f307983cc1e601e601e7e601e63cc03cfcc001023000f6cc001e7033d5],
[0x0,0x0,0x0,0x0,0x0,0x410882240481,0x400000240481,0x410882240481,0x400000240481,0x421004240481,0x400000240481,0x421004240481,0x400000240481,0x46218c240501,0x400000240481,0x46218c240501,0x400000240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6642 : TreeBound (n := 4) 107 (programCode 0x4e2b077969) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x424010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6643 : TreeBound (n := 4) 107 (programCode 0x4e2b07796a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x430490240481,0x9188020100120002408048e00108040a00010104,0x430490240481,0x0,0x1026d3980001e603cc1e601023000408c0007d4cf344d3a2c1e6000001e9cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0x1026d3980fab6603cc1e601023000222c0007d4d7bf4d36e8ce601e601e9cc204e8b001f8fc0003ee6826,0x3cc1e601e7e603cc1e6007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x0,0x0,0x1026d398007b6603cc1e601023000408c0007d4d0274d366097e003cc1e9cc1e688b00012fc0003cc3cb6,0x3cc1e6007b6603cc1e6007d4c00222c0007d4c03cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0x1026d398007b6603cc1e601023000408c0007d4d0274d3a2c1e6003cc1e9cc1e688b00012fc0003cc3cb6,0x3cc1e6007b6603cc1e6007d4c00222c0007d4c07981e61e7e6007981e9cc1e60f300012fc0003cc33b6,0x3cc1e60f31e603cc1e6007d4c00222c0007d4c1e601e6799e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3cc1e60f31e603cc1e6007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x0,0x3cc1e60001e603cc1e6007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f300003cc0003cc33b6,0x420810240481,0x980802010042000840804c200108043200042b04,0x420810240481,0x0,0x0,0x0,0x0,0x0,0x420802240481,0x400000240481,0x420802240481],
[0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x401008240481,0x400000240481,0x401008240481,0x400000240481,0x401010240481,0x400010240481,0x401010240481,0x400010240481,0x402010240481,0x400010240481,0x402010240481,0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6692 : TreeBound (n := 4) 107 (programCode 0x4e2b07796b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x424010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6693 : TreeBound (n := 4) 107 (programCode 0x4e2b07796c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x3d3987d4c001e9d3987983cde60445f9805b3f53001e9cc01e6f3003cc003ccf303ccf3003cde7033d5,0x420410210481,0x102307980000f307983cfcc0f300003cc00003ccf30811bcc0000f3003cfcc1e600007980000000001dc6,0x0,0x17bb07983cc1e607983d1eecf300f33cc1e603ccf30bddbcc2f76f3003d1eeef76f307981e601e688ce56,0x8000200000800020080082002080020000814e3,0x3d39e2f4c01e63d3a1f783ea6004519a405e2783001e9cc01e6f3003cc01e60f31e60f303cc1e7033d5,0x3d3987d4c0079bd3980003cde60445f9805b3f53003cfcc01e6f3003cfcc3cdf53000f300f31e7038e5,0x420410210481,0x8000200000800020080082002004020000814e3,0x420410210481,0x400410200481,0x8100200000800020080082002020020800814e3,0x400410200481,0x8200209000a0002808004200202001100084ca3,0x8000200000800020080082002000820000814e3,0x0,0x420201000020001000001010000200010000021000000010800000108000000108004000210110000010040000000100000100400220011000000004000200000000000200017d3a8,0x421010210481,0x0,0x0,0x421010208481,0x0,0x421010208481,0x0,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481],
[0x421010200481,0x421010220481,0x421010210481,0x0,0x3d3987d4c0079bd398000799e60445f98097ff53003cfcc01e6f3003cc003cde603ccf3003cde7038e5,0x420410210481,0x3d398f6cc0079bd398000799e604467300981db3003cfcc01e6f3003cc00799e603ccf300799e7038e5,0x0,0x520001000480004005200008000200010052000800148002000120008001480008004000290010000a400400029001000001004000200014800a4004000200004000240012007baa8,0x0,0x102307980001e607983cfcc0f300003cc00003ccf30811bcc0000f3003cfcc1e60f307980000000001e56,0x0,0x420410210481,0x102307980001e607983cfcc0f300003cc00003ccf30811bcc0000f3003cc3cde600f379800f3000001e56,0x420410210481,0x400410200481,0x8100200001000040080082002020020800814e3,0x400410200481,0x8200201001200048080082002040021000854e3,0x17bb07980000f307983d1eecf300003cc00003ccf30bddbcc0000f3003cde62f763cc7980f30000001dc6,0x0,0x0,0x0,0x0,0x0,0x0,0x7983cc01e6f307983cc007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x0,0x0,0x0,0x3cfd00a2e6607983cc008118003ea60007d4c079f9801e805167cc3cfcc00088b079b15c0007985426,0x0],
[0x3d39c09b4e607983cc00fa98003ea60007d4c0f379803ce04d9f983cfcc00088b079a22c0007985936,0x7983cc1e60f307983cc007d4c00222c0007d4c79803cde61e6079803cfcc1e60f3003cfcc00044d4bb6,0x7983cc1e60f307983cc007d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044d4bb6,0x0,0x3d0093b6607983cc008118003ea60007d4c3cc7981e6204a08c03cfcc0000f30812afc0007985426,0x0,0x408841240481,0x8080200002000080080080402080022000814e3,0x408841240481,0x0,0x410882240481,0x400800240481,0x410882240481,0x410882240481,0x420804240481,0x420804240481,0x420804240481,0x400800240481,0x4709c8240501,0x400800240481,0x4709c8240501,0x410882240481,0x7983cc1e60f307983cc01e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d431356,0x0,0x408841240481,0x0,0x408841240481,0x0,0x410882240481,0x400800240481,0x410882240481,0x410882240481],
[0x420804240481,0x420804240481,0x420804240481,0x400800240481,0x4709c8240501,0x400800240481,0x4709c8240501,0x410882240481,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x400000240481,0x410882240481,0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x421008240481,0x400000240481,0x421008240481,0x400000240481,0x421010240481,0x400010240481,0x421010240481,0x400010240481,0x422010240481,0x400010240481,0x422010240481],
[0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6822 : TreeBound (n := 4) 107 (programCode 0x4e2b07796d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x444110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6823 : TreeBound (n := 4) 107 (programCode 0x4e2b07796e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x404010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6824 : TreeBound (n := 4) 107 (programCode 0x4e2b07796f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x444110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6825 : TreeBound (n := 4) 107 (programCode 0x4e2b077970) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x3d3987d4c001e9d3987983cde60445f9805b3f53001e9cc01e6f3003cfcc001023000f6cc001e7033d5,0x3d3d4c3cc1e603d3983ea6000f3079803cde60f3003cfcc01e6f3003cfcc001f53000f6cc001e7038e5,0x16c83cc0000f303cc1e65b20f30f303cc00003ccf30b643cc0000f301e63cc2d90f307983cc0000001e56,0x0,0x3d3987d4c0079bd3983cc3cdf53079f981117e600f6cc00f4e6000f6cfcc001f53000f6cc001e7038e5,0x0,0x3d398f6cc0079bd3983cc799f5307a7301119cc01e9cc00f4e6001e9cfcc001f53000f6cc001e7038e5,0x0,0x8010200480080082002080082080022000814e3,0x8000200080000000000080002080022000814e3,0x8020200880080102004080102080022000814e3,0x0,0x8040201080000200008080202080022000814e3,0x3cc1e600081183cc1e60007d4c00222c0007d4c03cde603cde6003cde63cc1e60f300012fc0003cc33b6,0x3d3d4c3cc1e603d3983ea6000f3079803cde6007983cc3cc1e607983cfcc001f53000f6cc001e7038e5,0x3cc1e600081183cc1e60007d4c00222c0007d4c0799e601e7e600799e63cc1e60f300012fc0003cc33b6,0x810020508014080502008080208002200083ce3,0x8000200080000000000080002080022000814e3,0x8200209080201008040081002080022000854e3,0x8000200080000000000080002080022000814e3,0x16c83cc1e60f303cc1e63cc07996c81e61e603ccf30b643cc2d90f301e63cc1e60f30b643cc0f30799c76,0x8000200080000000080082002080022000814e3,0x3d39bcfcc01e63d39f981e7e601ee4e403ed39f3001e9cc01e6f3003cfcc001023000f6cc001e7033d5,0x0,0x0,0x0,0x0,0x0,0x410882240481,0x400000240481,0x410882240481],
[0x400000240481,0x400004240481,0x400000240481,0x400004240481,0x400000240481,0x421008240481,0x400000240481,0x421008240481,0x400000240481,0x421010240481,0x400010240481,0x421010240481,0x400010240481,0x462190240501,0x400010240481,0x462190240501,0x400010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6057 : TreeBound (n := 4) 107 (programCode 0x4e2b0779) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part103_6058 part103_6059 part103_6124 part103_6125 part103_6350 part103_6351 part103_6400 part103_6401 part103_6642 part103_6643 part103_6692 part103_6693 part103_6822 part103_6823 part103_6824 part103_6825

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6875 : TreeBound (n := 4) 107 (programCode 0x4e2b077a51) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040021008020000408048200108040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6876 : TreeBound (n := 4) 107 (programCode 0x4e2b077a52) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040021000120002408048200108040a00010104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6877 : TreeBound (n := 4) 107 (programCode 0x4e2b077a53) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040021008020000408048200108040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6878 : TreeBound (n := 4) 107 (programCode 0x4e2b077a54) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0xf379803cde6003d398001023000408c0007d4cf344d1bcc1e6000001e9cc1e688b00003cc0003cc3cb6,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0x0,0x0,0x480501284222,0x8400210001100044000820021004020100305e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x480501284222,0x480501284222,0x480500200222,0x480501284222,0x1ed98007b6610237980007b660026718011160003d39800f4e6001e9cc01e63cc0798f301e61e703d95,0x3d39803cde6003d3980007d4c00222c0007d4c00001e607983cc1e61e601e60001e600001e603cc33b6,0x480501284222,0x8400210001100044000020101004000100201e4,0x1ed98007b661023798000f4e60044d18011160003d39800f4e6001e9cc0f303cc3cc0f30f301e703d95,0xf379800f4e6003d3980010230003db30007d4c0f8b9980079f983cc1e63cc2671bcc00f3f3003cc3c56,0x8400210000900044001000001000000200201a4,0x0],
[0x0,0x0,0xf3798007b66102379803cc1e601ee118011160003d39800f4e6001e9cde6003d39800f3f3001e703d95,0x0,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0x8400210001100044001000041000000800201e4,0x0,0x480501284222,0x8400210001100044001020041004020100205e4,0x8400210001100044001000041000002000201e4,0x0,0x8400210001100044001000041000000200201e4,0x0,0x0,0x0,0x840021000110004400100804100100a000201e4,0x0,0x0,0xf3cf1bccde6003cc1e601023000408c0007d4d9e3f3180f4e601e601e9cc20cbd7001e9cc0003ee68b6,0xf3001e9cc0079bcc00799023000408c0007d4d9e4e618005b201e601e9cc20cbd7001e9cc0003ee68b6,0x0,0xf3001e9cc0079bcc00f31023000408c0007d4d9e3f3180097e01e601e9cc20cbd7001e9cc0003ee68b6,0xf3b6403cc3cc03ccf3001023000222c0007d4d6c88118799e601e601e9cc204e8b001e9cc0003ee6826,0xf300f33cc03cc3cc03cc1023000222c0007d4d7d9e1188ab4601e601e9cc2fbb4b01128fc0003eee1a6,0xf3832bccc07983cc00f31023000408c0007d4d9e3f3180097e01e601e9cc20cbd7001e9cc0003ee68b6,0x0,0xf381369cc07983cc00001023000222c0007d4d7bf4d18001e601e601e9cc204e8b001e9cc0003ee6826,0xf307983cc1e603cc1e601023000222c0007d4d7bb811888ce601e601e9cc204e8b001f8fc0003ee6826],
[0xf381183cde6003cc1e601023000222c0007d4d7bb811888ce601e601e9cc204e8b001f8fc0003ee6826,0xf307983cc1e603cc3cc01023000408c0007d4d7bb81181e7e601e601e9cc204e8b001e9cc00047eb0b6,0xf33cc03cd2fc03cc00001023000222c0007d4d6c88118001e601e601e9cc204e8b001e9cc0003ee6826,0xf33cc03ccf3003ccf3001023000222c0007d4d6c88118799e601e601e9cc204e8b001e9cc0003ee6826,0xf3799e9cc00b67cc00001023000222c0007d4d7bf4d18001e601e601e9cc204e8b001e9cc0003ee6826,0xf33cc03cc79803cde6001023000222c0007d4d6c88118f31e601e601e9cc204e8b00981cc0004b3d826,0x0,0xf3840f9cde6003cc03cc1023000408c0007d4c01ee11807b66000799e9cc1ea54b000408c0003eee236,0x3cc007d4c0079bcc007987d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x0,0x3cc00f6cc003cfcc00f307d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3d39803cc07983ccf30007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3cc03cfcc03cc3cc03cc07d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3d39803cc00f33cc00f307d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x0,0x3cc0003cc00f33cc000007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3cc1e63cc1e603cc1e6007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3cc1e63cde6003cc1e6007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3cc3cc3cc0f303cc3cc007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c00046ff136,0x3cc0003cc3cc03cc000007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0x3ccf303ccf3003ccf30007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c0003eed936,0xf3799e9cc003cfcc00001023000408c0007d4c01ee11807b66000799e9cc1ea54b000408c0003eee236,0x3cde603cc79803cde60007d4c00222c0007d4c00799e607b66000799e9cc1e60f3000408c00042b9936,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0x8400210001100044000000041000000800201e4,0x0,0x480501284222,0x8400210001100044004020141004020100a05e4],
[0x8400210001100044000000041000002000201e4,0x0,0x8400210000900044000000041000000200201a4,0x0,0x0,0x0,0x840021000110004400100804100100a000201e4,0x0,0x0,0x8400210001100044004000101000020100205e4,0x8400210001100044004004101000820020305e4,0x8400210001100044004020101004020100a05e4,0x8400210001100044004008101001020040205e4,0x8400210001100044004000101000020800205e4,0x0,0x8400210001100044004020101004020140a05e4,0x8400210001100044004020101004020100a05e4,0x8400210001100044004020101004022000a05e4,0x0,0x8400210001100044004000101000020200205e4,0x0,0x0,0x0,0x8400210001100044004008101001022000205e4,0x0,0x0,0xf3799e9cde6003cc00001023000222c0007d4cf344d18001e6000001e9cc1e688b00003cc0003cc3c26,0x0,0x0,0x0,0xf3cf1bccc3cc03ccf3001023000408c0007d4d9e3f3180f4e601e601e9cc20cbd7001e9cc0003ee68b6,0x3cc03cfcc03cc3cc03cc07d4c00222c0007d4c00799e602046000799e9cc1e60f3000408c0003eed936],
[0x0,0x3cc079bcc01e63cc079807d4c00222c0007d4c00f31e6001e6000f31e9cc1e60f300003cc0003cc33b6,0x3cc0003cc00003cc000007d4c00222c0007d4c00001e6001e6000001e9cc1e60f300003cc0003cc33b6,0xf307983cc1e603cc1e601023000408c0007d4d0274d180097e003cc1e9cc1e688b00012fc0003cc3cb6,0xf381183cde6003cc1e601023000408c0007d4d0274d180097e003cc1e9cc1e688b00012fc0003cc3cb6,0x0,0x3cc0003cc3cc03cc000007d4c00222c0007d4c00001e6001e6000001e9cc1e60f300003cc0003cc33b6,0xf33cc03ccf3003ccf3001023000408c0007d4d7c133180f4e601e601e9cc205257001e9cc0003ee68b6,0xf3799e9cc00b67cc00001023000222c0007d4cf344d18001e6000001e9cc1e688b00003cc0003cc3c26,0xf33cc03ccf3003cde6001023000408c0007d4d7bf4d183cde603cc01e9cc204e8b0079bcc000454ecb6,0x3d39803cde6003d3980007d4c00222c0007d4c03cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0xf379803cde6003d398001023000408c0007d4d023811bcc1e6003cc1e9cc1e688b00012fc0003cc3cb6,0x3d39803cde6003d3980007d4c00222c0007d4c07981e61e7e6007981e9cc1e60f300012fc0003cc33b6,0x0,0xf3cf1bccde6003cc00001023000408c0007d4d9e3f318799e6000001e9cc20cbd700003cc0003cc3cb6,0x0,0x0,0xf3001e9cc0079bcc00f31023000408c0007d4d7fdf318799e6000001e9cc20cbd700003cc0003cc3cb6,0xf3c5703cc3cc03ccf3001023000408c0007d4d8ae8118799e601e601e9cc20c80b001e9cc0003ee68b6,0x3cc03cfcc03cc3cc03cc07d4c00222c0007d4c03cc1e6799e6003cc1e9cc1e60f3001f8fc0003eed936,0xf3832bccc00003cc00f31023000408c0007d4d9e3f318799e6000001e9cc20cbd700003cc0003cc3cb6,0x0,0x3cc0003cc07983cc000007d4c00222c0007d4c1e601e6799e6000001e9cc1e60f3001e9cc0003ee5fb6,0x3cc1e63cc1e603cc1e6007d4c00222c0007d4c1e601e6799e601e601e9cc1e60f3001e9cc0003ee5fb6,0xf381183cde6003cc1e601023000408c0007d4d6c88118799e601e601e9cc20c80b001e9cc0003ee68b6,0x3cc3cc3cc0f303cc3cc007d4c00222c0007d4c79801e6799e6079801e9cc1e60f3001e9cc00046f77b6,0x3cc0003cc3cc03cc000007d4c00222c0007d4c00001e6799e6000001e9cc1e60f3001e9cc0003ee5fb6,0x3ccf303ccf3003ccf30007d4c00222c0007d4c1e601e6799e601e601e9cc1e60f3001e9cc0003ee5fb6,0xf3799e9cc003cfcc00001023000408c0007d4d7fdf318799e6000001e9cc20cbd700003cc0003cc3cb6,0x3cde603cc79803cde60007d4c00222c0007d4c3cc01e6799e603cc01e9cc1e60f300981cc00043a4fb6,0x0,0xf3cd269cde6003cc1e601023000408c0007d4c7988119e61e601e601e9cc204e8b001e9cc0003ee68b6],
[0x3cc007d4c0079bcc007987d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x0,0x3cc00f6cc003cfcc00f307d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3d39803ce22c03ccf30007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3cc03cfcc03cc3cc03cc07d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003eed936,0x3d39803cc07983cc00f307d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x0,0x3cc0003cc07983cc000007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3cc1e63cc1e603cc1e6007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3cc1e63cde6003cc1e6007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3cc3cc3cc0f303cc3cc007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc00046f77b6,0x3cc0003cc3cc03cc000007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0x3ccf303ccf3003ccf30007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc0003ee5fb6,0xf3799e9cc003cfcc00001023000408c0007d4c7988119e61e601e601e9cc204e8b001e9cc0003ee68b6,0x3cde603cc79803cde60007d4c00222c0007d4c1e601e7e61e601e601e9cc1e60f3001e9cc00042b1fb6,0x0,0xf3799e9cde6003cc00001023000408c0007d4cf344d180097e000001e9cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0xf3c59dccc3cc03ccf3001023000408c0007d4d0640d180097e003cc1e9cc1e6c5700012fc0003cc3cb6,0xf300f33cc03cc3cc03cc1023000408c0007d4c0044d180097e000001e9cc1e688b00003cc0003cc3cb6,0x0,0x0,0xf3799e9cc00003cc00001023000408c0007d4cf344d180097e000001e9cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0xf33cc03cc3cc03cc00001023000408c0007d4c1340d180097e000001e9cc1e6c5700003cc0003cc3cb6,0xf33cc03ccf3003ccf3001023000408c0007d4c0f74d180097e003cc1e9cc1e688b00012fc0003cc3cb6,0xf3799e9cc003cfcc00001023000408c0007d4cf344d180097e000001e9cc1e688b00003cc0003cc3cb6,0x400020001000000000000000000000000060002000100000000600000000400000002000010008000040010000080020000100400000101000000404000000810000001001087f667],
[0x0,0x0,0x3cc007d4c0079bcc007987d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x0,0x3cc00f6cc003cfcc00f307d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x3d39803cc00003ccf30007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x3cc03cfcc03cc3cc03cc07d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003fe0936,0x3d39803cc1e603cc00f307d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x0,0x3cc0003cc1e603cc000007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x3cc1e63cc1e603cc1e6007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003fd8fb6,0x3cc1e63cde6003cc1e6007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003fd8fb6,0x3cc3cc3cc0f303cc3cc007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc00047adbb6,0x3cc0003cc3cc03cc000007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x3ccf303ccf3003ccf30007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc0003f9c3b6,0x0,0x3cde603cc79803cde60007d4c00222c0007d4c3cc01e6f31e603cc01e9cc1e60f30079bcc00043683b6]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7087 : TreeBound (n := 4) 107 (programCode 0x4e2b077a55) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x408850240481,0x100082001e02008040804c200108070200402104,0x408850240481,0x0,0x0,0x0,0xf3001e6f30079bcc0155b8f301e60f307983cd0604301cc007983cc1e9cc315cf300f33cc03cc1e9c56,0x0,0xf3001e6f30079bcc015a8ebb0001f5307983cd9e4411b9079f99e601e9cc33c7d7001e9cc03cc226856,0xf3001e6f30079bcc015b269b003ccf307983cc01f304b51e67980799e9cc3413c7000408c03cc22e1d6,0xf3001e6f30079bcc015a8ebb0001f5307983cd9e4411b9f30799e601e9cc33c7d7001e9cc03cc226856,0xf3001e9cc003cfcc015b44fb0222fcc07983cc01f308813d04580f31e9cc3422f70007d4c03cc235b26,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x3cc00f6cc003cfcc0137583cc1e822c07983cc222c1e6799ed9a22c1e9cc222cf301119cc03cc225fb6,0xf3001e6f30079bcc014e37bb0001f5307983cc79881187980799e601e9cc2ffbd7001e9cc03cc226856,0x0,0xf3001e6f30079bcc014e30230003db307983cc7988119e60079bcc01e9cc2f7e8b001e9cc03cc226856,0x410890240481,0x100202004e02008040804c200108070200402b04,0x410890240481,0x7980f30f303cc3cc07d4c0798f300f307983ccf307983cc007a73001e9cc1e60f307983cc03cc233b46,0x420810240481,0x420810240481,0x420810240481,0x100802020e02008040804c200108070200407104,0xc40910240501,0x400810240481,0xc40910240501],
[0x102002080e02008040804c200108070200406104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7120 : TreeBound (n := 4) 107 (programCode 0x4e2b077a56) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1048020100420008408048200108042200042b04,0x1000820010420008408048200108042200042b04,0x0,0x408841240481,0x1040820010420008400108c02108042200042b04,0x408841240481,0x0,0x6098c2240481,0x6098c6240481,0x6098c2240481,0x6098c6240481,0x408844240481,0x408844240481,0x408844240481,0x408840240481,0x609cc8240481,0x6098c6240481,0x609cc8240481,0x0,0x0,0xf3001e6f30079bcc00f37a730007a73001e9cd0604301cc007983cc1e9cc1eace3000408c000f52e1d6,0x0,0x109cf9adae7e6007980130782bb20f300000001e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0xf3001e9cc0079bcc00f37a73001e9cc001e9cda0a3a4b507d4c1e601e9cc3413c7001e9cc000f52e236,0x408902340502,0x408902340502,0x408902340502,0x0,0x408904240502,0x408904240502],
[0x408904240502,0x40890e741d02,0x408908640d02,0x0,0x408908640d02,0x1060020400420008408048200108042200042b04,0x1002020040420008408048200108042200042b04,0x1042020040420008408048200108042200042b04,0x0,0xf300f30f303cc3cc07987a730007a73001e9cd0604301cc007983cc1e9cc1eace3000408c000f53b676,0x3cc079bcc01e63cc07981e9cc01e9cc001e9cc000f4e600f301e60f4e9cc1e60f307983cc000f53add6,0x109d06509e7e60000007daed93900f30000000f3003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x431082240481,0x240481,0x431082240481,0x240481,0x4240481,0x240481,0x4240481,0x240481,0x8240481,0x240481,0x8240481,0x240481,0x104c020000420008408048200108042200042b04,0x1008020100420008408048200108042200042b04,0x1048020100420008408048200108042200042b04,0x1008020200420008408048200108042200047b04,0x1030020000420008408048200108042200042b04,0x1020020400420008408048200108042200042b04,0x1043020000420008408048200108042200042b04],
[0x1020020800420008408048200108042200046b04]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7185 : TreeBound (n := 4) 107 (programCode 0x4e2b077a57) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x1040021008020000408048200108040200000104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7186 : TreeBound (n := 4) 107 (programCode 0x4e2b077a58) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x8400210002100104000000001000000000804a4,0x8400210002100104004020101800820020804a4,0x8400210002100104000000001000000000804a4,0x8400210002100104000000101800800040804a4,0x0,0x0,0x8400210002100104000000001000000100804a4,0x8400210002100104000000201002020100804a4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8400210002100104000804021104824120904a4,0x8400210002100104000804021100804020904a4,0x8400210002100104000804021100804020904a4,0x8400210002100104000804021100808040a05a4,0x7980001e60f3079800000000007980001e6007981e61e61e61a943cc01e60f30798f301e61e703375,0x0,0x8400210002100104000804021104020100804a4,0x8400210002100104000804021102020100804a4,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x8400210002100104000000001000000000804a4,0x8400210002100104000804021100804020904a4,0x8400210002100104000000001000000000804a4,0x840021000210010400080406130080c040b05a4,0x0,0x8400210002100104000000001002000080804a4,0x8400210002100104000000001000000100804a4,0x8400210002100104000000001002000100804a4,0x0,0x8400210002100104004020101808020200804a4,0x8400210002100104004020101804020300804a4,0x8400210004100104004020101010020400804e4,0x0,0x0,0x0,0x0,0x0,0x8400210002100104000804041204824120904a4,0x8400210002100104000804041200804020904a4,0x8400210002100104000804041200804020904a4,0x8400210002100104000804041200804040b05a4,0x8400210004100104001008041000000800805e4,0x0,0x8400210002100104000804041200000100804a4,0x8400210004100104001008041004020100805e4,0x840021000410010400100804100100a000a05e4,0x0,0x8400210004100104001008041001008200a05e4],
[0x0,0x0,0x0,0x8400210004100104001008041004022000805e4,0x0,0x0,0x408842240481,0x3cc007d4c0079bcc0079bcfcc00f6cc003cfcc01024e60408e064601e9cc1e813907beae4001e610856,0x408842240481,0xf3001e9cc0079bcc00f37a73001e9cc003cfcda11d288107983ea601e9cc3422f7001e9cc001e835bb6,0x410882240481,0x420802240481,0x410882240481,0x410882240481,0x420802240481,0x420802240481,0x420802240481,0x410882240481,0xc40902240501,0x400802240481,0xc40902240501,0x410882240481,0x0,0x6098c6240481,0x408902340502,0x6098c6240481,0x408902340502,0x410084240481,0x240481,0x410084240481,0x240481,0x20000240481],
[0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x8400210002100104000000101880002000804a4,0x8400210004100104004020101080022000804e4,0x8400210004100104000002001080402000804e4,0x0,0x408044240481,0x408904240502,0x408044240481,0x408904240502,0x410084240481,0x240481,0x410084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x8400210002100104000000201080022000804a4,0x0,0x408040240481,0x408904240502,0x408040240481],
[0x408904240502,0x410080240481,0x240481,0x410080240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x0,0x6098c8240481,0x40890e741d02,0x6098c8240481,0x40890e741d02,0x411088240481,0x8240481,0x411088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x842108240501,0x8240481,0x842108240501,0x8240481,0x0,0x408842240481],
[0x408908640d02,0x408842240481,0x408908640d02,0x410084240481,0x240481,0x410084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501,0x240481,0x8400210004100104004022001080422000804e4,0x0,0x0,0x408908640d02,0x0,0x408908640d02,0x410080240481,0x240481,0x410080240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x842108240501,0x240481,0x842108240501],
[0x240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7379 : TreeBound (n := 4) 107 (programCode 0x4e2b077a59) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x6090d0240481,0x10008200181a0002408048200108040e00010104,0x6090d0240481,0x0,0xf3001e9cc0079bcc012fd02300003cc0007d4cf344d1bcc1e6000001e9cc1e688b00003cc0003cc3cb6,0x0,0x0,0x0,0xf3001e9cc0079bcc015a8ebb003cfcc0007d4d9e4411b9097e01e601e9cc33c7d7001e9cc0003ee68b6,0x3cc00f6cc003cfcc00f307d4c22c7ac0007d4c00799e607b6ec7c799e9cc1e73ef000408c0003eed936,0x0,0x400001001000001010000010010000010020020000002080000200800000020800002000100002000800020200000020008040000010100008000400000101000000410020f13a8,0x0,0x3cc00f6cc003cfcc00f307d4c00222c0007d4c03cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0xf3001e9cc0079bcc012fd7bb000222c0007d4d023811bcc1e6003cc1e9cc1e6c5700012fc0003cc3cb6,0x3cc00f6cc001e9cc00f307d4c0003cc0007d4c07981e60f4e6007981e9cc1e60f300003cc0003cc3326,0xf3001e9cc0079bcc015a8ebb00003cc0007d4d9e4411c099e6000001e9cc33c7d700003cc0003cc3cb6,0x3cc00f6cc003cfcc00f307d4c224e2c0007d4c1e601e7e61edd6a601e9cc1e64bf001e9cc0003ee5fb6,0x0,0x3cc00f6cc003cfcc00f307d4c2db22c0007d4c3cc01e6f31edd88c01e9cc1e64bf0079bcc0003f9c3b6,0x411090240481,0x100202004fe2000840807f20010807f200042b04,0x411090240481,0x0,0x0,0x0,0x0,0x0,0x431082240481,0x21000240481,0x431082240481],
[0x21004240481,0x21004240481,0x21000240481,0x21004240481,0x21004240481,0x21008240481,0x21000240481,0x21008240481,0x21004240481,0x21010240481,0x1010240481,0x21010240481,0x21010240481,0x841110240501,0x1010240481,0x841110240501,0x1010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7428 : TreeBound (n := 4) 107 (programCode 0x4e2b077a5a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x6098d0240481,0x8004200108100204080042001080402001028e4,0x6098d0240481,0x0,0x79801e6f30079bcc00f4e679803ccf300f33ccf3001e9cc00799e601e9cc1e60f3001e9cc0079a266a6,0x0,0x10ca89ad901e60079801362a59420000001e601e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x3cc007a730079bcc00f3f33cc03ccf300f33cc03cc1e60079f99e601e9cc1e60f3001e9cc0079a25ad6,0x409102240d02,0x4091042408e2,0x409102240d02,0x0,0x4091042408e2,0x4091042408e2,0x4091042408e2,0x40910c2408e2,0x4091082408e2,0x0,0x4091082408e2,0x411090240481,0x801020040810020408004200108040200102ae4,0x411090240481,0x802020080810020408004200108040200102ce4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x842110240501,0x10240481,0x842110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7461 : TreeBound (n := 4) 107 (programCode 0x4e2b077a5b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x6090d0240481,0x8004200108100204080042001080402001028e4,0x6090d0240481,0x0,0x79801e6f30079bcc00f3f379803ccf300f33ccf3001e9cc00799e601e9cc1e60f3001e9cc0079a266a6,0x0,0x10ca89ad901e60079800f6ce19427980001e601e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x3cc007a730079bcc00f3f33cc03ccf300f33cc03cc1e60079f99e601e9cc1e60f3001e9cc0079a25ad6,0x409102240d02,0x4091042408e2,0x409102240d02,0x0,0x4091042408e2,0x4091042408e2,0x4091042408e2,0x40910c2408e2,0x4091082408e2,0x0,0x4091082408e2,0x411090240481,0x801020040810020408004200108040200102ae4,0x411090240481,0x802020080810020408004200108040200102ce4,0x21010240481,0x1010240481,0x21010240481,0x21010240481,0x841110240501,0x1010240481,0x841110240501],
[0x1010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7494 : TreeBound (n := 4) 107 (programCode 0x4e2b077a5c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1e671010c8f5de8140000ee89e3d028ee6b639aca0eea6c2ca00165a13702761fe66500ee6b2800003d797d26500ee6b2801dcd73e6b29dd11eaca001ddc4bb2801dce536b2801dd4d8594001dd4d8d075940077536165001dd4d8594001deb3265000eee25d94000ee70d51879189,0x0,0x0,0x0,0x408842240481,0x6098c6240481,0x408842240481,0x408040240481,0x6090c4240481,0x6098c6240481,0x6090c4240481,0x408040240481,0x80430010c06080082004080208001200080ca3,0x408842240481,0x80430010c06080082004100208001200080ca3,0x420010002000080004200208001200080ca3,0x8004200110100404080082001080402002030e4,0x0,0x77447ab281dcda09aca0077359b7359b7394daca007735b1cd65ee6b45cd653b9b41359403b9ae7cd653b9ae7cd6503b9ae7cd82cd65003ba23d59407735a2e6b283ba23d59407736be05f203ba23d5940773770d65ee6b2f735940773770d65003ba23d59401dcda18965c1bfa,0x0,0x0,0x0,0x408842240481,0x6098c6240481,0x408842240481,0x408040240481,0x6090c4240481,0x6098c6240481,0x6090c4240481,0x408040240481],
[0x150085002340a0d00820080802080022000814e3,0x408842240481,0x1e60f307a73000f30003cc0000f4e6003d3980799e601e63cc03cfcc003db3000f6cc001e722395,0x8400200000000800082002080022000814e3,0x0,0x773594077536165001dcddc359401dd4d859401dcddc359401ddc4bb45cd653b9b41359403b9ae7cd653b9ae7cd6503b9ae7cd82cd65003ba23d59407735a2e6b283ba23d59407736be05f203ba23d5940773770d65ee6b2f735940773770d65003ba23d59401dcdb0e7897089a,0x0,0x0,0x0,0x3cc007a730079bcc00f3f33cc0f30f301e63cc03cc1e6007b661e605b5cc1e60f3001e9cc0352b922d6,0x409102240d02,0x4091042408e2,0x409102240d02,0x0,0x4091042408e2,0x4091042408e2,0x4091042408e2,0x40910c2408e2,0x4091082408e2,0x0,0x4091082408e2,0x410090240481,0x801020041010040408008200108040200203ae4,0x410090240481,0x8020200810100404080082001080402002034e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x842110240501,0x10240481,0x842110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7559 : TreeBound (n := 4) 107 (programCode 0x4e2b077a5d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x50a050240481,0x8004200120100004080042001080402000000e4,0x50a050240481,0x0,0x16c80005b21023000811801e7e679f9f99e7e600f6cc003ea6000f6cfcc001f53000f6cc001e703885,0x0,0x44580011161023001ed9803cde67a73799e9cc03d39800f4e6001e9cfcc003db3000f6cc001e722395,0x0,0xf3001e9cc0079bcc0152dff301e63cc00f33cd9e431be0079f99e601e9cc2ff073001e9cc0079a268b6,0x40a902341502,0x40b10c6418e2,0x40a902341502,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x40b10c6418e2,0x40b1086418e2,0x0,0x40b1086418e2,0x612090240481,0x801020042010020408004200108040200102ae4,0x612090240481,0x802020082010020408004200108040200102ce4,0x422010240481,0x2010240481,0x422010240481,0x2010240481,0x842110240501,0x2010240481,0x842110240501],
[0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7592 : TreeBound (n := 4) 107 (programCode 0x4e2b077a5e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x408850240481,0x8004200120100804080042001080402004020e4,0x408850240481,0x0,0x0,0x0,0x109cf9adae7e6007980130782bb200000003cc1e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x3cc007a730079bcc00fa983cc1e60f307983cc03cc1e60079f99e601e9cc1e60f3001e9cc03cc225ad6,0x40a102241502,0x40a10c2418e2,0x40a102241502,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x40a10c2418e2,0x40a1082418e2,0x0,0x40a1082418e2,0x411090240481,0x801020042010080408004200108040200402ae4,0x411090240481,0x802020082010080408004200108040200402ce4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x842110240501,0x10240481,0x842110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7625 : TreeBound (n := 4) 107 (programCode 0x4e2b077a5f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x50a050240481,0x0,0x632090204481,0x422010210481,0x632090204481,0x0,0x422010208481,0x1000820010620008408048200100443008042b04,0x422010208481,0x0,0x422010210481,0x422010210481,0x422010210481,0x422010210481,0x422010220481,0x422010200481,0x422010220481,0x422010220481,0x50a050240481,0x0,0xf307983cc2e846c8811801ed9879fa731e7f53001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x8008200200900024080006001000c00020100e4,0x1e60f30f308a1cf980f3001ed987aed731ebc13003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x0,0x0,0x0,0x0,0x8008200200100004080002001000400040000e4,0x0,0x8008200200100004080002001000400200000e4],
[0x0,0x0,0x0,0x8008200200100004080002001000400000000e4,0x0,0x612090240481,0x0,0x632081240481,0x10020200401a0002400148002108040e00010104,0x632081240481,0x0,0x422002240481,0x2000240481,0x422002240481,0x2008240481,0x2004240481,0x2000240481,0x2004240481,0x2000240481,0x2008240481,0x2000240481,0x2008240481,0x2000240481,0x612090240481,0x0,0x0,0x0,0x0,0x0,0xe521c2240501,0x842108240501,0xe521c2240501],
[0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x422010240481,0x2010240481,0x422010240481,0x2010240481,0x842110240501,0x2010240481,0x842110240501,0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7706 : TreeBound (n := 4) 107 (programCode 0x4e2b077a60) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0xf379803cc00003cc001e60f303cc3cc0f303ccf30079bcc01e6f3001e9cc2d9000079800007983cddc6,0x4400100000400880082002000020400814e3,0x0,0x0,0x408850208481,0x4400100000000880082002080020000814e3,0x408850208481,0x4400100000000880082002080020000814e3,0xf379803cc00003cc001e60f303cc3cc0f303ccf30079bcc01e6f3001e9cc2d9000079800007983cddc6,0x4400100000400880082002000020400814e3,0x4400100000400880082002010020400814e3,0x0,0x50a050220481,0x408850208481,0x50a050220481,0x408050200481,0x8004200140101004080042001080402008040e4,0x0,0xf3bdd83cc00003cc799e60f303cc3cc0f303ccf30079bcc01e6f3001ebeeed9000079800007983cddc6,0x8400200000000880082002000020400814e3,0x0,0x0,0x408850208481,0x0,0x408850208481,0x0,0x0,0x8400200000000880082002000020400814e3,0x8400200000400880082002010020400814e3,0x8400200000000880082002000022000814e3],
[0x50a050220481,0x408850208481,0x50a050220481,0x408050200481,0x0,0x0,0x0,0x0,0x0,0x0,0x40a102241502,0x40a10c2418e2,0x40a102241502,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x40a10c2418e2,0x40a1082418e2,0x0,0x40a1082418e2,0x0,0x610481240481,0x10000400000402080080402080022000814e3,0x610481240481,0x0,0x410882240481,0x411084240481,0x410882240481,0x410080240481,0x411084240481,0x411084240481],
[0x411084240481,0x410080240481,0x612088240481,0x411084240481,0x612088240481,0x410080240481,0x801020044010100408004200108040200806ae4,0x0,0x610481240481,0x0,0x610481240481,0x0,0x410882240481,0x411084240481,0x410882240481,0x410080240481,0x411084240481,0x411084240481,0x411084240481,0x410080240481,0x612088240481,0x411084240481,0x612088240481,0x410080240481,0x802020084010100408004200108040200806ce4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x842110240501,0x10240481,0x842110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_6874 : TreeBound (n := 4) 107 (programCode 0x4e2b077a) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part103_6875 part103_6876 part103_6877 part103_6878 part103_7087 part103_7120 part103_7185 part103_7186 part103_7379 part103_7428 part103_7461 part103_7494 part103_7559 part103_7592 part103_7625 part103_7706

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7803 : TreeBound (n := 4) 107 (programCode 0x4e2b077b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x10400410080002010080082002080022000814e3]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7805 : TreeBound (n := 4) 107 (programCode 0x4e2b077c51) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c80003cde6016cf9805b3f53001e9cc01e6f3003cc003ccf300f3f3003cde703375,0xf379803cde60f307980003cc00016c80005b20f30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0x25f800097e0f307980003cfcc016c80005b20f30079bcc01e6f3003cc00f33cc03ccf300799e722395,0x0,0x480100204022,0x480501284222,0x480501284222,0x480501284222,0x0,0x0,0x480100204022,0x10400410004100104004020102001020040804e4,0x0,0x480104204022,0x480104204022,0x480104204022,0x0,0x0,0x0,0x0,0x0,0x0,0xacfec0000568213fb000015a084fec0000568a2fec00002b405cfec00002b405cfec00002b3fb00159fd80000000567f6185ea39a58bd8567f600acfec0000015aaa7ec00000000acfed59fd80acfec0567f6000159fed9fd80c2f51d1e756000567f759fd80000000567f600005680b9fd80acfec00acfec000000185ea3a52e11cc7f600000000159fd80acfec00567f6000002b3fb017c96e48ac,0x0,0x0,0x400081000400080004000800014000800012010000010400000100500000101004000002010000040040000020100000100001000020001000400010000200010001000e84b0a7,0x1020001004483200004200000000000000010040000048220000100000000100004000008010000020040000100100000100001000080004000200010001000010001002886aba7,0x400021000400400004000200015001000012010000010100000100540000101804000002010000040040000020100000100001000020001000400010000200010001000e84b0a7,0x0,0x1000801001502000004002000000008000012154000040100000040000000100004000010010000040040000080100000100001000100004000400004000800010001001887ba27,0xf307983cc1e607981ebeecf300f33cc1e603ccf30bddbcc01e6f3003d1eeef76f307981e601e688ce56],
[0x402301000008004000004008000000010000022110000080100000100000000100004000010010000040040000080100000100002000100008000400010000800010001001887fea7,0xf307983cc1e607983d1eecf300f33cc1e603ccf30bddbcc01e6f3003d1eeef76f307981e601e688ce56,0xf33cc03ccf300798005b20f307983cc1e603ccf30811bcc01e6f3003d1b22d90f307981e60f30799e56,0xf33cc03ccf300798f35b20f307983cc1e603ccf30811bcc01e6f3003d1b22d90f307981e60f30799e56,0x40200100044000000402000001410000001201000001100000010050000010900400000201000004004000002010000010000100002000100040001000020001000100ce84b0a7,0xf33cc03ccf300799e65b20f307983cc1e603ccf30811bcc01e6f3003d1b22d90f307981e60f30799e56,0x0,0x0,0x798007b660079f9800b6403cc079bcc5b203ccf3003cfcc1f53f3003cc02055301ed98001e6f3812d56,0x0,0x0,0x0,0x79803cde603cc7980408c03cc079bcc5b203ccf3003cfcc1f53f3003cc02055301ed98001e6f381a6d6,0x1e848d5de65d73e6b280f047fe6dcf41d74047fe8b9aca01dcda09aca7b0620c80681deb326500773770d650077539cffca077accb70d6503b9b41359401dcf41d6503b9b4135940773770d6500773d3519901475361650003b9bb86b2877536165000ee6c1847fe5ee6ee95aabf59,0x0,0x40001000800020080082002080020000814e3,0x7981e61e61e607981e9cc03cc079bcc5b203ccf3003cfcc1f53f3003cc02055301ed98001e6f3a35956,0x80002000800020080082002080020000814e3,0x800020080082002080020000814e3,0x100004000800024080082002080020000814e3,0x800020080082002080020000814e3,0x200008000800028080082002080020000814e3,0x800020080082002080020000814e3,0xfa98003ea60f409c80003ea60017491805d06f3001e9cc01e6f3003cc01e60f31e60f303cc1e703375,0x16c80005b20f307980003cde6016cf9805b20f3003cfcc01e6f3003cfcc001f53000f3003cde703885,0x0,0x8006200100c2002088004200200801020080ca3,0x420410210481,0x3cc01e6f30088b0000f303cfcc016c80003cfdb30079bcc01e6f3003cc0f303cc3cc0f30f301e722395,0x0,0x4000081000400080040000800104000800012010000010400000100500000101004000002010000040040000020100000100010000020010000400100000200100001000e84b0a7,0x10020001040080000040200000000000000010000000048000000100000000100004000008010000020040000100100000100010000080040000200100001000100001002086aba7],
[0x3cc0f30f303db30f379803ea60016cf9803ea6f30079bcc01e6f3003cc0f303cc3cc0f30f301e703d95,0xf300f31e601e679807f7667300003cc00003ccf30bececc0000f3003d1f687b2c00798003cc00001dc6,0x420410210481,0xf307981e61e607981ec777f30222fcc088b3ccf30d2bdcc053973003d277a4aea2339800f3445a249c6,0x420410210481,0x420410210481,0x440510210501,0x400410210481,0x440510210501,0x102381366f4e689a301ed99119cc044673003cdf530079bcc007a73003cc3cc03ccf3003ccf301e64dc35,0x0,0xf30f307aafc088fce307983cde60447df803d58d3003cfcc007a73003cfdefc1e60f303cd2fc1e64d3c5,0x80002000800020080082002004020000814e3,0x0,0x0,0x0,0x79803cde603cc7980408c03cc1e63cc3cde9ccf3003cfcc1f53f3003cc0f522c0f379800f33cca006d6,0x7a08b01e7e600798f33cc03cc1e63cc44583ccf3003cfcc1f53f3003cc0f522c0f379800f33cc1e7556,0x0,0x40001000800020080082002004020000814e3,0x7981e61e61e607981e9cc03cc1e63cc63ab3ccf3003cfcc32c973003cc0f62c88f379800f33cc224156,0x80002000800020080082002004020000814e3,0x800020080082002004020000814e3,0x20100004000900024080082002004020800834e3,0x800020080082002004020000814e3,0x40201008000a00028080082002004021000854e3,0x800020080082002004020000814e3,0x0,0x0,0x420410210481,0x0,0x0],
[0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100420030000080000000000200000200200010007ffa8,0x79803cfcc03cc7980408c03cc7983cc3cde9ccf3003cfcc1e60f3003cc1e7e60f3079801e6f3081a766,0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100420030000080000000000200000200200010007ffa8,0x0,0x420410210481,0x7981e63cc1e607981ec3ab3cc7983cc63ab3ccf3003cfcc32c973003cc1e92ca164b9801e6f309bc1e6,0x420410210481,0x420410210481,0x440510210501,0x400410210481,0x440510210501,0xf33cc01e67980799e65b20f307983cc1e603ccf30811bcc01e6f3003d008ed900f379801e6f30799dc6,0x0,0x0,0x20410200481,0x0,0x0,0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100020030000080000000200200000200200010007ffa8,0x79803cde603cc7980408c03cc7983cc3cde9ccf3003cfcc1f53f3003cc1e8d90079f9801e6f3081a6d6,0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100020030000080000000200200000200200010007ffa8,0x0,0x20410200481,0x7981e61e61e607981e9cc03cc7983cc63ab3ccf3003cfcc32c973003cc1e92c8879f9801e6f309bc156,0x20410200481,0x410200481,0x40510200501,0x410200481,0x40510200501,0x410200481,0x0,0x20006800100c0402098004200202001080080ca3,0x1e607987981e6f30fa98003ea60016cf9803ea6f30079bcc01e6f3003cc79803cde600f379801e703d95],
[0x1e6001ed98008a96000f303cc3cc16c8f303cfdb30079bcc01e6f3003cc79803cde600f379801e7241f5,0x0,0x40000081000000080400000800004000800012000000010400000100120000101004000004010000040040000040100000100100000040100000401000000401000001000ac5b1a7,0x79803cde603cc7980408c03cc79fd4c5d249ccf3003cfcc2e9323003cc1e8e92a9879801e6f3fb1a6d6,0x1e6003d39803dd16f379803cde6016cf9804031d3001e9cc01e6f3003cc79800f4e600f379801e703375,0x1e67980799e611160007983cc1e616c87985b3f53003cfcc01e6f3003cc79801e7e600f379801e703885,0x20042821000c6002108004200202001080080ca3,0x7981e61e61e607981e9cc03cc03cfcc62b83ccf3003cfcc324ff3003cc799fccf987980798079a24156,0x600301000800004000400008000000010000022110000080100000100000000100004000010010000040040000080100000100200000100800000401000000801000001001887fea7,0x840510220501,0x840510220501,0x800410220481,0x840510220501,0x840510220501,0x0,0xc006320100c6002188004200208c01030080ca3,0x20410200481,0x1e601e6798088b0f30f303ea60016cf9803cfdb30079bcc01e6f3003cc3cc03db3f30f307981e703d95,0x0,0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100200030000800000001000200001000200010007ffa8,0x79803cde603cc7980408c03cc007d4c3ea63ccf3003cfcc1e7023003cc799e60798798079800fb1a6d6,0xf300f33cc03db30f379803cc00016cf9803ea6f30079bcc01e6f3003cc00003db3f30f33cc01e703d95,0xf300f33cc03cc79807f76673000f6cc00003ccf30bececc0000f3003cde62fb3398798079801e611156,0x20410200481,0x7981e61e61e607981e9cc03cc03cfcc62b83ccf3003cfcc324ff3003cc799fccf987980798079a24156,0x20410200481,0x410200481,0x840510220501,0x410200481,0x840510220501,0x410200481,0x0],
[0x40007000100c0402098004200202001100080ca3,0x4000100300080002008004200202001100080ca3,0x3cc0010230008c7c000f303cc79816c9e603d1c13003cfcc01e6f3003ccf3001ed9800f3f3001e707545,0x3cc1e60f307992fc97e00044580018ae00062b8f3001e9cc01e6f3003cc79800fa9800f3f3001eacf375,0x0,0x0,0x3cc00f3f3003db30f379803cfcc016cf9803ea6f30079bcc01e6f3003cde6003d39800f3f3001e722395,0x0,0x40043021000c6002108004200202001100080ca3,0x3cc007a73001f8fd7491803cde6016cf9805d2553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x3cc01e6f301e72fcf6cc003ea60017491805d2553001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x840510220501,0x840510220501,0x800410220481,0x840510220501,0x840510220501,0x0,0x6000100c0002088004200208001000080ca3,0x200000100800000402000000802000000e2021000100004000000108000000008004000310110000040040000000100000100200031010800000002000200002000000200017ffa8,0x0,0x0,0x0,0x79803cde603cc7980408c03cc01e9cc3ea63ccf3003cfcc1e9db3003ccf31e603cc7980f3003d438cd6,0x0,0x0,0x842021000c2002088004200208081002080ca3,0x7981e61e61e607981e9cc03cc0f33cc44583ccf3003cfcc1f53f3003ccf320463cc7980f301e6317156,0xf4e6003ea6f30f6cc003cde6016cf9805b3f53001e9cc01e6f3003cc003cd0230f3f3003cde703375,0x410200481,0x40510200501,0x410200481,0x40510200501],
[0x410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7998 : TreeBound (n := 4) 107 (programCode 0x4e2b077c52) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x4000200010000800000082000100208000000820000002002000008208000c00800040000100100000400400000801000001000000401000001004000004008000010010010873227,0x10400410000900024080006002000c00020100e4,0x0,0x480501200222,0x480501200222,0x480500200222,0x480501200222,0x2e098007b660f3079800799e6111d9803cde6000f379801e7e60079bcc00f33cc03ccf300799e703f45,0x0,0x480501200222,0x10400410000900024004020102004020100904e4,0x0,0x480504200222,0x480504200222,0x480504200222,0x0,0x10400410000900024020004802000880020100e4,0x0,0x10400410000900024040005002000880020100e4,0x0,0x480501284222,0x480501284222,0x480501284222,0x480501284222,0x0,0x0,0x480501284222,0x10400410000900024004008102001020040305e4,0x0,0x480504284222,0x480505284222],
[0x480504284222,0x0,0x0,0x0,0x0,0x0,0x0,0x421010208481,0x0,0x0,0x411090208481,0x2000010002000008020000080020000080002100000001080000010800000010800400039521000001004000080010000010072a421418001001004000200004000000210857d3a8,0x411090208481,0x20000100020000100200001000200001000021000000010800000108000000108004000391410000010040000800100000100722821410002001004000200004000000210897d3a8,0x421010208481,0x401010208481,0x421010208481,0x421010208481,0x441110208501,0x401010208481,0x441110208501,0x421010208481,0x0,0x79f9801e7e60079f98000408c00408c000408c00003cc1e600f30003cc01e60001e601e61e607985216,0x10400410000900024000810022002010080100e4,0x0,0x0,0x0,0x0,0x8400410000900024002010022402010080100a4,0x0,0x0],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10400410000900024080006002080400020100e4,0x0,0x8400410000900024004020522802024100904a4,0x8400410000900024000820022802020100904a4,0x8400410000900024000020102802000100100a4,0x8400410000900024000820042802010100904a4,0x0,0x0,0x8400410000900024004020122802020100904a4,0x10400410000900024004020102004020100904e4,0x8400410000900024004822122802424100904a4,0x0,0x8400410000900024004020502802024100904a4,0x0,0x0,0x0,0x8400410000900024000822022802420100904a4,0x0,0x0,0x4000000030000000080080000300200000800820000002002000008208000c00001040000100100000400400000801000001000040001000100004000400008001000010010873227,0x421010210481,0x0,0x1000840020090002408000a002000c00040100e4,0x411090210481,0x0],
[0x411090210481,0x0,0x421010210481,0x401010210481,0x421010210481,0x421010210481,0xc43110210501,0x401010210481,0xc43110210501,0x421010210481,0x10400410000900024080042002008400200100e4,0x10400410000900024080082002010400400100e4,0x10400410000900024080082002010400400100e4,0x0,0x1e6000811bcc2f760007983ce04616c87f3201f53003cfcc01e6f3003cc79801e7e600f379801e703885,0x421010220481,0x1e6001e607988a96000f3079c08c25f8f6cc03db30079bcc01e6f3003cc79803cde600f379801e7241f5,0x0,0x20030000020000000200200000200200000021000000010800000108000000108004000310010000010040000000100000100600021011000000001000200000000000200017d3a8,0x10010400400900024080082002020400400100e4,0x4000001010000004000080008100200010000820000002002000008208000c00060040000100100000400400000801000001000400001001000004004000008010000010010873227,0x10020400800900024080002002020400000100e4,0x421010220481,0x401010220481,0x421010220481,0x421010220481,0xc43110220501,0x401010220481,0xc43110220501,0x421010220481,0x0,0x0],
[0x421010200481,0x0,0x0,0x411090210481,0x10010400400900024080102002020400802132e4,0x411090210481,0x10020400800900024080102002020400802134e4,0x421010200481,0x401010200481,0x421010200481,0x421010200481,0xc43110220501,0x401010200481,0xc43110220501,0x421010200481,0x0,0x3cc00088b3cc315c0007983ce04616c87f3201f53003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x421010220481,0x798001e60f309048000f30f344584459e9cc03db30079bcc01e6f3003cde6003d39800f3f3001e726055,0x10008400200900024080006002000c00020100e4,0x4110000410460002000080008004400008000801000044086000110218000800010040000080100000200400001001000001001000000804000002020000010020000010020866ba7,0x0,0x0,0x0,0x421010220481,0x401010220481,0x421010220481,0x421010220481,0xc43110220501,0x401010220481,0xc43110220501,0x421010220481],
[0x0,0x0,0x421010210481,0x0,0x0,0x0,0x10010400400900024080202002040401002132e4,0x10400402100900024080202002040401002130e4,0x10020400800900024080202002040401002174e4,0x421010210481,0x401010210481,0x421010210481,0x421010210481,0xc43110230501,0x401010210481,0xc43110230501,0x421010210481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_8175 : TreeBound (n := 4) 107 (programCode 0x4e2b077c53) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c80003cde60445f98097ff53001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x7980001e60f30798000f30000445800097e0f30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0x25f80011160f30798000799e60446730097e0f3003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x480501284222,0x480501284222,0x480501284222,0x480501284222,0x0,0x0,0x480501284222,0x10400410001100144004028102001020040a05e4,0x25f800097e0f6d398000f33cc0445800097e003cc7980f31e603cc3cc0079bcc01e6f30f301e722395,0x480504284222,0x480505284222,0x480504284222,0x0,0x0,0x7980001e60f30798000798000445800097e03cc03cde601e63cc03cc00001e60000f5d9001e703885,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10000100040000400100000800200000841001000104004000010008001040008004000008010000820040002080100000100600020801800082004000200004000020021206eea8,0x0,0x0,0x1000801004c02000004002000000008000022110000080100000100000000200004000010010000040040000080100000100001000100004000400004000800010001001887ba27,0xf307983cc1e607981ea08cf300f33cc408c3ccf30811bcc2046f3003d1b22046f307981e601e688ce56],
[0x10000800040082000100208000200010041000800104004000010008001040008004000008010000820040002080100000100600020801800082004000200004000020021006aea8,0xf307983cc1e607983d008cf300f33cc408c3ccf30811bcc2046f3003d1b22046f307981e601e688ce56,0xf33cc03ccf30079800408cf300f33cc408c3ccf30811bcc2046f3003d1b22046f307981e601e688ce56,0xf33cc03ccf300798f3408cf300f33cc408c3ccf30811bcc2046f3003d1b22046f307981e601e688ce56,0x2b40067f65680f022bbd8159fd82df3ab00000ad0019fd80000d8493fec0000ad0019fd8000003627f53af600afc85d8bfb0015aaa7ec000000ad09a58bd80056e0af4c00000c55293159fd800015a02e7f6000567f759fd8000acff167f600005680b9fd80002b40067f60000567f6002b3fb00567f6159fd8159fd800567f62b3fb00acfec0159fd80acfec0acfec0159fd8159fdd72e187e9e8b,0xf33cc03ccf300799e6408cf300f33cc408c3ccf30811bcc2046f3003d1b22046f307981e601e688ce56,0x0,0x10400410000100004010000002002000080000e4,0x79f9801e7e60079f98000408c0012fc002268c000f6cc00f311160f6cc01e61117e603cc1e601e61556,0x480100208022,0x0,0x0,0x0,0x480100208022,0x10400410004100104004020102002020080804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1ed98007b660f34458000f4e600446730097e0f30079bcc01e6f3003cc07983cc1e60f303cc1e703d95,0x0,0x8400410000100404000000402002000100000a4,0x8400410000900124000824022802020100904a4,0x480100208022,0x10400410001100144001028042004020100a05e4,0x0,0x0,0x480100208022],
[0x10400410004100104004020102004020100804e4,0x25f800097e0f6d398000f33cc0445800097e003cc7980f31e603cc3cc0079bcc01e6f300f31e722395,0x0,0x8400410000100404000000402002000100000a4,0x0,0x0,0x0,0x7980001e61c811e80003cc000447294097e01e601e7e601e63cc03cc00000f30000fa20295e703375,0x0,0x0,0x8006200100c2004088004200200801020080ca3,0x420410210481,0x3cc01e6f30088b0000f30f33cc0445800079bdb30079bcc01e6f3003cc0f303cc3cc0f30f301e722395,0xf3001e7e6003d398012fd02300003cc00003ccf30813a2c0000f3003cfcd11679807980007980001dc6,0x0,0x0,0x3cc0f30f303db33cc7980f4e60044673007b66f30079bcc01e6f3003cc0f303cc3cc0f30f301e703d95,0x0,0x420410210481,0xf307981e61e607981e9cc0f300003cc00003ccf30811bcc0000f3003d008de6000079800f3000001dc6,0x420410210481,0x420410210481,0x440510210501,0x400410210481,0x440510210501,0x799e603ccf300799e64272f3016cbcc42723ccf3084e7cc2139f3003ced9213a6c87980f302d9cd2146,0x1ed98007b660f34458000f4e600446730097e0f30079bcc01e6f3003cc07983cc1e60f708c01e703d95,0x3d39803cde60fa9f980003cc000445800097e0f3001e9cc01e6f3003cc0f300f3f300f31e601e703375,0x7980001e60f307980003cc000445800097e0f3001e9cc01e6f3003cc00000f30000f6cc001e703375,0x0,0x20006800100c0404098004200202001080080ca3,0x1e607987981e6f33d39800f4e60044673007b66f30079bcc01e6f3003cc79803cde600f379801e703d95],
[0x1e6001ed98008a96000f30f303cc4458f3079bdb30079bcc01e6f3003cc79803cde600f379801e7241f5,0x0,0x10000008100000008100000080000200080000a0000000804000000800600002010040000040100000400400000401000001001000000401000004010000004010000010008c5b1a7,0x79803cde603cc7980408c03cc079bcc3ea63ccf3003cfcc1f53f3003cc1e7f5379879801e60f381a6d6,0x1e6003d39803dd1ca579803cde6044729407cf1d3001e9cc01e6f3003cc79800f4e600f379801e703375,0x1e67980799e61116001e60f307984459e60981db30079bcc01e6f3003cc79803cde600f379801e726055,0x20042841000c5004108004200202001080080ca3,0x7981e61e61e607981e9cc03cc079bcc3ea63ccf3003cfcc1f53f3003cc799f5379879807980f3a35956,0x8021000080004000080210000200010042000800108002000020008001080008004000210010000040040002100100000100100020001400084001000200004000040012005b9a8,0x840510220501,0x840510220501,0x800410220481,0x840510220501,0x840510220501,0x0,0x0,0x20410200481,0x0,0x0,0x10cfc2f3222c3cc01e63cc11494201ea45807a73f30079bcc00f3f3003d032843cc88b0799e601e68a8c5,0xf307980001e600000000011160001e600007980f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x10cfc2f3222c1e601e679811494201ea45807a73f30079bcc00f3f3003d032843cc88b0799e601e68a8c5,0x0,0x20410200481,0x10d0485080001e6000000011494201e600007980f30079bcc00f3f3003d032843cc00007980001e68a8c5,0x20410200481,0x410200481,0x840510220501,0x410200481,0x840510220501,0x410200481,0x0],
[0x20007000100c0404098004200202001100080ca3,0x40000002001000040080082002040021000814e3,0x1e600097e00095fa000f303cc1e6445b52879ef0f001e9cc01e6f3003cc79800fa9800f3f3001e703375,0x3cc1e61e60f31a947980008118004a0a000aea8f3003cfcc01e6f3003ccf3001ed9800f3f3001f267885,0x0,0x0,0x3cc007b66003db35b27980799e60446ec807c59f3003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x0,0x20043041000c5004108004200202001100080ca3,0x3cc007b66003db36385080799e60446ec809b1513003cfcc01e6f3003ccf3001ed9800f3f3001e703885,0x7980799e601e6f33cfcc00f4e60044673009a03b30079bcc01e6f3003cde6003d39800f3f3001e703d95,0x840510220501,0x840510220501,0x800410220481,0x840510220501,0x840510220501,0x0,0x0,0xf372b8d40000f301e7e601151cd00f33cc07980f30079bcc007a73003cfcda97cc00003cc0799e64dc35,0x0,0x0,0xf33ccf300003cc01e63cc11382c01e679807a73f30079bcc00f3f3003cfcc003cc00007d4c001e68a8c5,0xf307980001e600000000011160001e600007980f30079bcc00f3f3003cfcc003cc00007980001e68a8c5,0xf35b2f300001e601e679811494201e679807a73f30079bcc00f3f3003cfcc003cc00007d4c001e68a8c5,0x0,0x40001001000040080082002000020040814e3,0xf36385080001e6000000011494201e600007980f30079bcc00f3f3003cfcd6cbcc00007980001e68a8c5,0x80002001000040080082002000020040814e3,0x410200481,0x40510200501,0x410200481,0x40510200501],
[0x410200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_8336 : TreeBound (n := 4) 107 (programCode 0x4e2b077c54) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0x0,0x80200000200800002002000002008000000088000000208000002080000002080000800008142080100008000081400801000010000100010a104001020490001000040002593a8,0x480501284222,0x10400410001100044004020102004020100a05e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0xf379803cde60f3079803cc0000f379801e7e6007987981e61e60f303cc01e63cc0798f301e61e703d95,0x0,0x480501284222,0x10400410001100044000820022004020100305e4,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x480501284222,0x480501284222,0x480500200222,0x480501284222,0x0,0x79f9801e7e60079f980007d4c00222c0007d4c00003cc07983cc1e63cc01e60001e600001e603cc33b6,0x480501284222,0x10400410001100044000020102004000100201e4,0x0,0x0,0x10400410001100044001000002000000400201e4,0x0,0x0,0x4000200010000800000002000100008000400000001000580004000a00000008800000004020000040200000201000000201000000000210000002040000010100000010020846ba7,0x0,0x4000200010000800000002000100008000400000001000580004000a00000008800000004020000040200000201000000201000000000210000002040000010100000010020846ba7,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0x10400410001100044001000042000000800201e4,0x0,0x480501284222,0x10400410001100044001020042004020100205e4,0x10400410001100044001000042000002000201e4,0x0,0x10400410001100044001000042000000400201e4],
[0x0,0x0,0x0,0x1040041000110004400100804200100a000201e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x77359407735cf9aca0773d075940ee6b639aca1dcd73e6b281dcd6577acc9940003c11ff94007823ff280003d77a050000f048002cd65ee6b28ee6b281dcf41d6503b9ad929c45ceca3b9aca0773d07597b9acbdcd650000f5de817b9acbdcd65218736e0be400007b7740fb776a,0x0,0x0,0x401000801004002000008004000000008040002100100400200401000000002000000010010000040040000080080000100100400000101000000404000000810000001001087ba67,0x773594ee6b2bb9acaee6b9f3595dcd653b9acdb9acaee6b2bb9aca077acc9940003c11ff94007823ff280003d77a050000f048002cd65ee6b28ee6b281dcf41d6503b9acec5e8e6aca3b9aca0773d07597b9acbdcd650000f5de817b9acbdcd6504310774be400007ca6dd70676a,0x0,0x0,0xf33cc01e6f30079800001023000222c0007d4d6c88119e61e6079803cfcc204e8b0079bcc000454ec26,0xf33cc01e6f300798f3001023000222c0007d4d6c88119e61e6079803cfcc204e8b0079bcc000454ec26,0x0,0xf33cc01e67980799e6001023000222c0007d4d6c88119e61e6079803cfcc204e8b0079bcc000454ec26,0x0,0x7983cc1e7e60079f9bcc07d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x798007b660079f98007987d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x79803cde7e60079f980007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x79800f4e6003d39800f307d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x0,0x79803cde603cc79803cc07d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x0,0x0,0x7980001e600f3798000007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536],
[0x7981e61e61e607981e6007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00046ff136,0x7983cc1e7e6007983cc007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x7983cc1e60f307983cc007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x7980001e6f300798000007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00044dc536,0x798f301e6f300798f30007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00046c2536,0x0,0x799e601e67980799e60007d4c00222c0007d4c0079bcc07b6600079bcfcc1e60f3000408c00048a8536,0x0,0x480501284222,0x480501284222,0x480501200222,0x480501284222,0x10400410001100044000000042000000800201e4,0x8400410000900044002010022402010080100a4,0x480501284222,0x10400410001100044004020142004020100a05e4,0x10400410001100044000000042000002000201e4,0x0,0x8400410000900044010000022000080400100a4,0xf379800f4e60079f9800102300012fc0007d4c13579981e6079800f6cc3cc26ae7cc3cc1e6001e61d36,0x0,0x0,0x1040041000110004400100804200100a000201e4,0x0,0x0,0x10400410001100044004000102000020100205e4,0x8400410000900044002004102100810020904a4,0x10400410001100044004020102004020100a05e4,0x10400410001100044004008102001020040205e4,0x10400410001100044004000102000020800205e4,0x0,0x10400410001100044004020102004020140a05e4],
[0x10400410001100044004020102004020100a05e4,0x10400410001100044004020102004022000a05e4,0x0,0x8400410000900044002000102000010400904a4,0x0,0x0,0x0,0x10400410001100044004008102001022000205e4,0x0,0x0,0xf3799e7e7e60079800001023000222c0007d4cf344d18001e6000003cfcc1e688b00003cc0003cc3c26,0x0,0x0,0x0,0x0,0x79803cde603cc79803cc07d4c00222c0007d4c0079bcc0204600079bcfcc1e60f3000408c00044dc536,0x0,0x7980799e601e6798079807d4c00222c0007d4c00f33cc001e6000f33cfcc1e60f300003cc0003cc33b6,0x7980001e60000798000007d4c00222c0007d4c00003cc001e6000003cfcc1e60f300003cc0003cc33b6,0x0,0x0,0x0,0x7980001e6f300798000007d4c00222c0007d4c00003cc001e6000003cfcc1e60f300003cc0003cc33b6,0x10008000040020000200080000200080000010800000042000000208000000208000002200014404820000802000010000100400000011000082024000004010000000400026aba8,0xf3799e7e6003d39800001023000222c0007d4cf344d18001e6000003cfcc1e688b00003cc0003cc3c26,0x0,0x79f9803cde60079f980008118003ea60007d4c079f9801e804603cc3cfcc00088b079b15c0007985426,0x0,0x480505284222,0x480505284222,0x480504200222,0x480505284222],
[0x0,0x0,0x480505284222,0x10400410001100044004020402004028100a05e4,0x1040041000110004400100840200100a000201e4,0x480504210222,0x480504210222,0x480504210222,0x0,0x0,0x1040041000110004400100840200100a000201e4,0x0,0xf379803cde60079f98000fa98003ea60007d4c0f379803ce04607983cfcc00088b079a22c0007985936,0x0,0x0,0x800000802000000820000008020000008000880000002080000020800000020800100020001000001001000200000008010040000040100008000400020401000000041082593a8,0x0,0x3b9aca0077447ab2801dd4d859400ee7a0eb2801dce536b2801dcd68c11ff94000f047fe500077536165000f047fe50000f047fe8b9ad8e6b28ee6b639aca0773597b9ad8e6b639acbdcd73e729bd075940001faa3b503b9b413597b9acbdcd65ee6b2f735940001e1076216c7aa,0x0,0x79803cde603cc79803cc07d4c00222c0007d4c07983cde61e6007983cfcc1e60f3003defc00044dc536,0x0,0x0,0x7980001e60f30798000007d4c00222c0007d4c79803cde61e6000003cfcc1e60f3003cfcc00044d4bb6,0x7983cc3cc0f307981e6008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007ebdc26,0x400001001000004000000008000000010060002000100000000600000000200000002000010008000040008000080010000100400000101000000404000000810000001001087fe67,0x7983cc3cc1e607983cc008118003ea60007d4c3cc7980f320463cc03cfcc01e6f30812afc0007e44426,0x799e603cc7980798000008118003ea60007d4c3cc7980f3204600003cfcc01e6f30812afc0007e44426,0x799e603cc7980798f30008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007e44426,0x0,0x799e603ccf300799e60008118003ea60007d4c3cc7982d9204679803cfcc02d9f3084f6fc0008655c26,0x0,0x79bcc01e7e60079fd4c007d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044d4bb6],
[0x798007b660079f98007987d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044d4bb6,0x79800f4e7e60079f980007d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044d4bb6,0x79800f6cc0079f9800f308118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007e44426,0x0,0x79803cde603cc79803cc07d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044dc536,0x0,0x0,0x7980001e60f30798000007d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044d4bb6,0x7983cc3cc0f307981e6008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007ebdc26,0x7983cc1e7e6007983cc007d4c00222c0007d4c1e603cde61e601e603cfcc1e60f3003cfcc00044d4bb6,0x7983cc3cc1e607983cc008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007e44426,0x799e603cc7980798000008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007e44426,0x799e603cc7980798f30008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc0007e44426,0x0,0x799e603ccf300799e60008118003ea60007d4c3cc7980f320461e603cfcc01e6f3084f6fc00085dc426,0x0,0x16c80005b216c87980003cde6016cfc591e603cc03cde601e63cc03cc003cde600f3f3003cde703885,0x8400410000900044000806042100c04020100a4,0x445800111616c8798000f33cc044581e61e607980799e601e63cc03cc00f33cc03ccf300799e722395,0x7980001e60f3079800000000007982d91e603cc03cde601e63cc03cc00001e60000f5d9001e703885,0x7980001e60f307980f300003cc7982d91e603cc03cde601e63cc03cc01e61e60798f301e61e703885,0x0,0x7980001e60f307980f300007987982d91e603cc03cde601e63cc03cc03cc1e61e60f303cc1e703885,0x7980001e60f3079800000000007982d91e603cc03cde601e63cc03cc00001e60000f300001e703885,0x7980001e60f307982d90000b647982d91e603cc03cde601e63cc03cc0f301e63cc0f30f301e703885,0x0,0x7980001e60f3079800000000007982d91e603cc03cde601e63cc03cc1e601e6f300f31e601e703885,0x0,0x0,0x0,0x7980001e60f3079800000000007982d91e603cc03cde601e63cc03ccf3001ed9800f3f3001e703885,0x0],
[0x0,0x79bcc01e7e60079fd4c007d4c00222c0007d4c3cc03ccf31e603cc03cfcc1e60f3003cfcc00044d4bb6,0x798007b660079f98007987d4c00222c0007d4c3cc03ccf31e603cc03cfcc1e60f3003cfcc00044d4bb6,0x79800f4e7e60079f980007d4c00222c0007d4c3cc03ccf31e603cc03cfcc1e60f3003cfcc00044d4bb6,0x79800f6cc0079f9800f308118003ea60007d4c3cc7981e620463cc03cfcc00f3f30812afc0007dcac26,0x0,0x79803cde603cc79803cc07d4c00222c0007d4c3cc03ccf31e603cc03cfcc1e60f3003cfcc00044dc536,0x0,0x0,0x7980001e60f30798000007d4c00222c0007d4c3cc03ccf31e603cc03cfcc1e60f3003cfcc00044d4bb6,0x7983cc3cc0f307981e6008118003ea60007d4c3cc7981e620463cc03cfcc00f3f30812afc0007dcac26,0x7983cc1e7e6007983cc007d4c00222c0007d4c3cc03ccf31e603cc03cfcc1e60f3003cfcc00044d4bb6,0x7983cc3cc1e607983cc008118003ea60007d4c3cc7981e620463cc03cfcc00f3f30812afc0007ebdc26,0x799e603cc7980798000008118003ea60007d4c3cc7981e620463cc03cfcc00f3f30812afc0007dcac26,0x799e603cc7980798f30008118003ea60007d4c3cc7981e620463cc03cfcc00f3f30812afc0007dcac26,0x0,0x799e603ccf300799e60008118003ea60007d4c3cc7981e620463cc03cfcc00f3f30812afc0008562c26]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_8577 : TreeBound (n := 4) 107 (programCode 0x4e2b077c55) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c8001e61e60811f982047e600f4e6003ea6000f6cfcc001023000f6cc001e703375,0x10400410000100804000880022080402000000e4,0x25f800097e0f34458001e63cc081273020460003d39800f4e6001e9cfcc003db3000f6cc001e722395,0x0,0x8400410000100804000880042000000000000a4,0x8400410000900824000884042100804020100a4,0x8400410000100804000880042000000000000a4,0x840041000090086400088c042200804040301a4,0x10400410000100804001080042000000800000e4,0x0,0x8400410000100804000880042000000000000a4,0x7980001e60f30798001e600008118002046000001e60001e600003cc00000f30000f301e61e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x10400410000100804001080042000002000000e4,0x0,0x0,0x2088c2240481,0xf3001e9cc001ed9800d87fef000102307983cd7c07cfdf83db31e603cfcc2f8071003cfcc0001e61df6,0x2088c2240481,0xf3001e9cc0079f98015b81bb0001f5307983cda210301907a731e603cfcc344157003cfcc0003f23456,0x210882240481,0x220882240481,0x210882240481,0x210882240481,0x220882240481,0x220882240481],
[0x220882240481,0x210882240481,0x240982240501,0x220882240481,0x240982240501,0x210882240481,0x0,0x6088c6240481,0x8004400110100c04002080082080012002432a4,0x6088c6240481,0x8004400210100c04002080082080012002433a4,0x610884240481,0x800240481,0x610884240481,0x610884240481,0x20800240481,0x20800240481,0x20800240481,0x800240481,0x840908240501,0x800240481,0x840908240501,0x800240481,0x8400410000100804000080002080002000000a4,0x0,0x2088c2240481,0x8004400110100c04002080102080012002834a4,0x2088c2240481,0x8004400210100c04002080102080012002837a4,0x210882240481,0x220882240481,0x210882240481],
[0x210882240481,0x220882240481,0x220882240481,0x220882240481,0x210882240481,0x240982240501,0x220882240481,0x240982240501,0x210882240481,0x0,0x408844240481,0x10004400100100804000880022080402000000e4,0x408844240481,0x0,0x610884240481,0x400804240481,0x610884240481,0x610884240481,0x420804240481,0x420804240481,0x420804240481,0x420804240481,0x440904240501,0x400804240481,0x440904240501,0x630884240481,0x0,0x408844240481,0x40a1042410a2,0x408844240481,0x40a1042410a2,0x610884240481],
[0x400804240481,0x610884240481,0x610884240481,0x420804240481,0x420804240481,0x420804240481,0x420804240481,0xc4090c240501,0x400804240481,0xc4090c240501,0x630884240481,0x0,0x408844240481,0x40a1042410a2,0x408844240481,0x40a1042410a2,0x610884240481,0x400804240481,0x610884240481,0x610884240481,0x420804240481,0x420804240481,0x420804240481,0x420804240481,0x440904240501,0x400804240481,0x440904240501,0x630884240481,0x0,0x8840240481,0x40a1042410a2,0x8840240481],
[0x40a1042410a2,0x210882240481,0x800240481,0x210882240481,0x210882240481,0x20800240481,0x20800240481,0x20800240481,0x800240481,0x40900240501,0x800240481,0x40900240501,0x800240481,0x0,0x2000680010240408092004080208001200080ca3,0x1e67980799e60f379f9801e7e6008154c0206461e607987981e61e603cfcc003db3000f6cc001e703d95,0x1e6001ed98008a96000f31e603cc8118f31e63cde607987981e61e603cfcc003db3000f6cc001e7241f5,0x1e67980799e60f300f3001e9cc00820b002082c1e603cc7981e61e603cfcc001f53000f6cc001e8e9885,0xa108c8240481,0x800808240481,0xa108c8240481,0xa509c8240501,0xa20888240481,0xa20888240481,0xa20888240481,0x840908240501,0x840908240501,0x800808240481,0x840908240501,0x840908240501,0x0,0x6088c6240481],
[0xf3001e9cc001ed9800d4b3ef000102307983cc79881187980f31e603cfcc307371003cfcc0001e61df6,0x6088c6240481,0xf3001e9cc0079f98014e37bb0001f5307983cc79881187980f31e603cfcc307557003cfcc0003f23456,0x610884240481,0x800240481,0x610884240481,0x610884240481,0x20800240481,0x20800240481,0x20800240481,0x800240481,0x840908240501,0x800240481,0x840908240501,0x800240481,0x0,0x4000780010240408092004100208001200080ca3,0x0,0x3cc0010230009414000f31e60798811ad91e65b5cc03cde601e63cc03cfcc001f53000f6cc001e707545,0x0,0xa108c8240481,0x800808240481,0xa108c8240481,0xa509c8240501,0xa20888240481,0xa20888240481,0xa20888240481,0x840908240501,0x840908240501,0x800808240481,0x840908240501,0x840908240501],
[0x0,0x0,0xf3001e9cc001ed9800d4b023000102307983cc7988119e600f33cc03cfcc2f7e8b0079bcc0001e61df6,0x0,0x79800f4e6003d398014e203cc00222c1e603cc3cc03ccf31f533cc03cfcc1e64bf003cfcc00044d4bb6,0x210880240481,0x800240481,0x210880240481,0x210880240481,0x220882240481,0x220882240481,0x220882240481,0x800240481,0x40900240501,0x800240481,0x40900240501,0x800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_8786 : TreeBound (n := 4) 107 (programCode 0x4e2b077c56) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108841240481,0x0,0x108841240481,0x0,0x6098c2240481,0x6098c6240481,0x6098c2240481,0x6098c6240481,0x408844240481,0x408844240481,0x408844240481,0x8840240481,0x0,0x6098c6240481,0x0,0x10400406002100084040201002080082002432e4,0x798007b660079f9800799e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d431356,0x0,0x108841240481,0x0,0x108841240481,0x0,0x6098c2240481,0x6098c6240481,0x6098c2240481,0x6098c6240481,0x408844240481,0x408844240481,0x408844240481,0x8840240481],
[0x0,0x6098c6240481,0x0,0x7980f31e7e600799f5301e9cc01e9cc001e9cc3cc03ccf307983cc03cfcc00f3f3003cfcc003d431356,0x0,0xf3001e9cc0079f9800f37a730007a73001e9cd09d04e7cc00f307983cfcc1eace3000408c000f56add6,0x0,0xf362bad9097e0001e6130782bb20f307983cc1e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x0,0x408902340502,0x408902340502,0x408902340502,0x0,0x408904240502,0x408904240502,0x408904240502,0x40890e741d02,0x408908640d02,0x0,0x408908640d02,0x0,0x7118c1240481,0x7980f31e7e9cc79bcc001e9cc01e9cc001e9cc000f6cc00f301e60f6cfcc1e60f307983cc003d431356,0x7118c1240481,0x0,0x411082240481,0x411084240481,0x411082240481,0x411084240481,0x411084240481,0x411084240481],
[0x411084240481,0x411084240481,0xe118c8240481,0x411084240481,0xe118c8240481,0x411084240481,0x79803cde603cc79803cc1e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d438cd6,0x0,0x7118c1240481,0x0,0x7118c1240481,0x0,0x411082240481,0x411084240481,0x411082240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0x411084240481,0xe118c8240481,0x411084240481,0xe118c8240481,0x411084240481,0x0,0xf300f33cc03cc79807987a730007a73001e9cd09d04e7cc00f307983cfcc1eace3000408c000f578276,0x7980799e601e679807981e9cc01e9cc001e9cc000f6cc00f301e60f6cfcc1e60f307983cc003d440656,0x10d048508463e000f307db2a59420f3445a22cf3003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x431082240481,0x240481,0x431082240481],
[0x240481,0x4240481,0x240481,0x4240481,0x240481,0x8240481,0x240481,0x8240481,0x240481,0x7980001e60f3079800001e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d431356,0x7981e61e61e607981e601e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d653f56,0x7983cc1e7e6007983cc01e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d431356,0x7983cc1e60f307983cc01e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d431356,0x7980001e6f30079800001e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d431356,0x798f301e6f300798f3001e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d617356,0x0,0x142941240501,0x798007b6603cc79f98001e9cc01e9cc001e9cc000f6cc00f301e60f6cfcc1e60f307983cc003d431356,0x142941240501,0x0,0xc43102240501,0x42108240501,0xc43102240501,0x42108240501,0x42104240501,0x42108240501,0x42104240501,0x42100240501,0x42108240501,0x42108240501,0x42108240501,0x42100240501],
[0x799e601e67980799e6001e9cc01e9cc001e9ccf3003cfcc1e60f3003cfcc1e60f307983cc003d7fd356]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_8915 : TreeBound (n := 4) 107 (programCode 0x4e2b077c57) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x16c80005b20f316c8001e61e61ed9f983ea7e600f4e6003ea6000f6cfcc001023000f6cc001e703375,0x0,0x480101200022,0x480501284222,0x480101200022,0x480501284222,0x0,0x0,0x480101200022,0x8400410004100104000804022102020100804a4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x25f80011160f362b8003cc1e61edaec83ea60001e9cc00f4e6001e9cfcc001f53000f6cc001e703885,0x0,0x480101200022,0x480501284222,0x480101200022,0x480501284222,0x10400410000100004001000042000000800000e4,0x0,0x480101200022,0x10400410004100104001008042004020100805e4,0x10400410000100004001000042000002000000e4,0x0,0x10400410000100004001000042000000400000e4],
[0x0,0x0,0x0,0x10400410000100004001000042000002000000e4,0x0,0x0,0x2088c2240481,0xf3001e9cc001ed9800bbf2f300798f301e63cda1fc3e4003db31e603cfcc2139f3003cfcc00f32615f6,0x2088c2240481,0xf3001e9cc0079f98013572f300798f301e63cda20b6e4007a731e603cfcc2139f3003cfcc00f3263456,0x210882240481,0x220882240481,0x210882240481,0x210882240481,0x220882240481,0x220882240481,0x220882240481,0x210882240481,0x240982240501,0x220882240481,0x240982240501,0x210882240481,0x0,0x6088c6240481,0x408902340502,0x6088c6240481,0x408902340502,0x610884240481,0x800240481,0x610884240481,0x610884240481,0x20800240481],
[0x20800240481,0x20800240481,0x800240481,0x840908240501,0x800240481,0x840908240501,0x800240481,0x480100240022,0x10400410004100104004020102080022000804e4,0x0,0x408844240481,0x0,0x408844240481,0x0,0x610884240481,0x400804240481,0x610884240481,0x610884240481,0x420804240481,0x420804240481,0x420804240481,0x420804240481,0x440904240501,0x400804240481,0x440904240501,0x630884240481,0x480104240022,0x480104240022,0x480104240022,0x0,0x2000680010240410092004080208001200080ca3,0x40910c2408e2],
[0x1e6001ed98008a96000f379803cded98f33cc3cde607987981e61e603cfcc003db3000f6cc001e7241f5,0x40910c2408e2,0xa108c8240481,0x800808240481,0xa108c8240481,0xa509c8240501,0xa20888240481,0xa20888240481,0xa20888240481,0x840908240501,0x840908240501,0x800808240481,0x840908240501,0x840908240501,0x0,0x6088c6240481,0x4091082408e2,0x6088c6240481,0x4091082408e2,0x610884240481,0x800240481,0x610884240481,0x610884240481,0x20800240481,0x20800240481,0x20800240481,0x800240481,0x840908240501,0x800240481,0x840908240501,0x800240481,0x0],
[0x2000780010240410092004100208001200080ca3,0x0,0x1e600097e00095fa000f31e601e7ed9b52bcc6e3a601e7e601e63cc03cfcc001023000f6cc001e703375,0x0,0xa108c8240481,0x800808240481,0xa108c8240481,0xa509c8240501,0xa20888240481,0xa20888240481,0xa20888240481,0x840908240501,0x840908240501,0x800808240481,0x840908240501,0x840908240501,0x0,0x4000104000100800082002080022000814e3,0x4091082408e2,0x8000204000100800082002080022000814e3,0x4091082408e2,0x210880240481,0x800240481,0x210880240481,0x210880240481,0x220882240481,0x220882240481,0x220882240481,0x800240481,0x40900240501,0x800240481,0x40900240501],
[0x800240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9076 : TreeBound (n := 4) 107 (programCode 0x4e2b077c58) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10400410004100104000000002000000000804e4,0x10400410004100104004020102000820020804e4,0x10400410004100104000000002000000000804e4,0x10400410004100104000000002001000040804e4,0x16c80005b20f316c8001e61e60811f982047e600f4e6003ea6000f6cc01e60f30798f301e61e703375,0x0,0x10400410004100104000000002000000100804e4,0x10400410004100104000000002004000100804e4,0x0,0x0,0x0,0x0,0x0,0x0,0x7980001e60f307980f300003cc7980f31e60000f4e6003ea6000f6cc79800fa9800f3f3001e703375,0x0,0x0,0x10400410004100104000804022004824120904e4,0x10400410004100104000804022000804020904e4,0x10400410004100104000804022000804020904e4,0x10400410004100104000804022001008040a05e4,0x7980001e60f3079800000000007980001e6007981e61e61e61a943cc01e60f30798f301e61e703375,0x0,0x10400410004100104000804022004020100804e4,0x10400410004100104000804022004020100804e4,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x10400410004100104000000002000000000804e4,0x10400410004100104000804022000804020904e4,0x10400410004100104000000002000000000804e4,0x10400410004100104001008042001008040a05e4,0x25f800097e0f34458001e63cc081273020460003d39800f4e6001e9cc01e63cc0798f301e61e722395,0x10400410004100104000000002002000080804e4,0x10400410004100104000000002000000100804e4,0x10400410004100104000000002004000100804e4,0x0,0x10400410004100104004020102008020200804e4,0x10400410004100104004020102004020400804e4,0x10400410004100104004020102010020400804e4,0x0,0x0,0x7980001e60f307980f300007987982d91e60001e9cc00f4e6001e9ccf3001ed9800f3f3001e703885,0x0,0x0,0x10400410004100104001008042000000040805e4,0x10400410004100104001008042000804020905e4,0x10400410004100104001008042000000040805e4,0x10400410004100104001008042001008040a05e4,0x10400410004100104001008042000000800805e4,0x0,0x10400410004100104001008042000000100805e4,0x10400410004100104001008042004020100805e4,0x1040041000410010400100804200100a000a05e4,0x0,0x10400410004100104001008042001008400a05e4],
[0x0,0x0,0x0,0x10400410004100104001008042004022000805e4,0x0,0x0,0x2088c2240481,0x798007b660079f980079bcfcc00f6cc003cfcc01026cc0408e0bf803cfcc1e813907dd0e4001e610856,0x2088c2240481,0x80000040800000400800000402000001000808000008008000008080000020080000000000000000400000200010400001004000000010000800040002100100000010000a5b1a8,0x210882240481,0x220882240481,0x210882240481,0x210882240481,0x220882240481,0x220882240481,0x220882240481,0x210882240481,0x240982240501,0x220882240481,0x240982240501,0x210882240481,0x0,0x6098c6240481,0x408902340502,0x6098c6240481,0x408902340502,0x10084240481,0x240481,0x10084240481,0x240481,0x20000240481],
[0x240481,0x20000240481,0x240481,0x40108240501,0x240481,0x40108240501,0x240481,0x10400410004100104000000102080002000804e4,0x10400410004100104004020102080022000804e4,0x10400410004100104000002002080402000804e4,0x0,0x408044240481,0x408904240502,0x408044240481,0x408904240502,0x10084240481,0x240481,0x10084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40108240501,0x240481,0x40108240501,0x240481,0x10400410004100104000000402080022000804e4,0x0,0x8040240481,0x408904240502,0x8040240481],
[0x408904240502,0x10080240481,0x240481,0x10080240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40100240501,0x240481,0x40100240501,0x240481,0x0,0x0,0x40890e741d02,0x24525318001dcd6500003ddfef318003b9aca00001deb32650001dcd6500000245253180009149501a44e74ce33e6fb2c1989403b9bb86b2877360b3594ee6b639aca0ee6c166b287735a2e6b28773d07594000f047fe5001dd4d8594001deb3265000eee25d94000ee6ee944c3129,0x40890e741d02,0x10088240481,0x8240481,0x10088240481,0x8240481,0x20008240481,0x8240481,0x20008240481,0x8240481,0x40108240501,0x8240481,0x40108240501,0x8240481,0x0,0x6098c6240481],
[0x408908640d02,0x6098c6240481,0x408908640d02,0x10084240481,0x240481,0x10084240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40108240501,0x240481,0x40108240501,0x240481,0x10400410004100104004022002080422000804e4,0x0,0x0,0x408908640d02,0x0,0x408908640d02,0x10080240481,0x240481,0x10080240481,0x240481,0x20000240481,0x240481,0x20000240481,0x240481,0x40100240501,0x240481,0x40100240501],
[0x240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9269 : TreeBound (n := 4) 107 (programCode 0x4e2b077c59) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x800620010842020088004200208001200080ca3,0x798007b660079f9800798408c0003cc000408cf3003cfcc1e60f3003cfcc1e60f307983cc0000001556,0x3cc01e6f30088b0000f3f303cc3d39800f303db30079bcc01e6f3003cfcc003db3000f6cc001e722395,0x0,0xf3001e9cc0079f98012fd02300003cc0007d4cf344d1bcc1e6000003cfcc1e688b00003cc0000001e56,0x0,0xf3001e9cc0079f98012fd02300003cc0007d4cf30811bcc1e6000003cfcc1e688b00003cc0000001e56,0x0,0x0,0x79800f4e6003d39800f307d4c81b3ac0007d4c0079bcc07c695fc79bcfcc2e96ef000408c10367dc536,0xf3001e6f3001ed98012fd02300003cc0007d4cf344d18001e6000003cfcc1e688b00003cc0000001d36,0x402000100000080004020001000000800100000000100800001002000001000000004000400040001000040010000400010040000004100000010400000101000000100208593a7,0x0,0x79800f4e6003d39800f307d4c00222c0007d4c03cc3cc3cde6003cc3cfcc1e60f300012fc0003cc33b6,0x79800f6cc0079f9800f307d4c0003cc0007d4c07983cfcc1e6007983cfcc1e60f300003cc00000015e6,0x79800f3f3001ed9800f307d4c0003cc0007d4c07983cc0f4e6007983cfcc1e60f300003cc0003cc3326,0xf3001e9cc0079f980151fc2300003cc0007d4d7bf89f8461e6000003cfcc2f7e8b00003cc0000001e56,0x79800f4e6003d39800f307d4c813a2c0007d4c1e603cde62e86ea603cfcc2e87bf003cfcc10274d4bb6,0x0,0x79800f4e6003d39800f307d4c813a2c0007d4c3cc03ccf32e8708c03cfcc2e87bf003cfcc10274d4bb6,0x411090240481,0x79803cde603cc79803cc1e9cc81954c001e9ccf3003cfcc2e9323003cfcc2e932307983cc1032b1a6d6,0x411090240481,0x0,0x0,0x0,0x0,0x0,0x431082240481,0x421000240481,0x431082240481],
[0x421004240481,0x421004240481,0x421000240481,0x421004240481,0x421004240481,0x421008240481,0x421000240481,0x421008240481,0x421004240481,0x421010240481,0x401010240481,0x421010240481,0x421010240481,0x441110240501,0x401010240481,0x441110240501,0x421010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9318 : TreeBound (n := 4) 107 (programCode 0x4e2b077c5a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x1041601e6f30088b0000ba87882c0fa9800f301f530079bcc007a73003cfcc003db3000408c001e64dc35,0x10004400108100204080042002080402001028e4,0x79f9801e7e6007981e60f33cc0f33cc00f33ccf3003cfcc007a73003cfcc007a7307983cc01e6317156,0x0,0xf3001e9cc0079f9800f4e679803ccf300f33ccf3001e9cc025f9e603cfcc1e60f3005b5cc016ca9fea6,0x0,0x10d03badb2c3e0001e61362a594288b4459e601e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x3cc007d4c0079f9800f3f33cc03ccf300f33cc07981e60079f99e605b5cc1e60f3003cfcc0079a9f2d6,0x409102240d02,0x4091042408e2,0x409102240d02,0x0,0x4091042408e2,0x4091042408e2,0x4091042408e2,0x40910c2408e2,0x4091082408e2,0x0,0x4091082408e2,0x411090240481,0x1001040040810020408004200208040200103ae4,0x411090240481,0x1002040080810020408004200208040200102ce4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x42110240501,0x10240481,0x42110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9351 : TreeBound (n := 4) 107 (programCode 0x4e2b077c5b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x10400410000100404080002002080402000000e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9352 : TreeBound (n := 4) 107 (programCode 0x4e2b077c5c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x0,0x0,0x0,0x0,0x2088c2240481,0x6098c6240481,0x2088c2240481,0x8040240481,0x409044240481,0x6098c6240481,0x409044240481,0x8040240481,0x0,0x6098c6240481,0x34000000200000000880000000800000001400080220000000028000001004000020040000200200001000200001004000000210000002040000010100000010020842ba7,0x400010000000080004200208001200080ca3,0x10004400110100404080082002080402002030e4,0x0,0x0,0x0,0x0,0x0,0x2088c2240481,0x6098c6240481,0x2088c2240481,0x8040240481,0x409044240481,0x6098c6240481,0x409044240481,0x8040240481],
[0x370000002000000010200000010000000017000802f0000000502000004008000020040000200100001000100001004000000210000002040000010100000010020846ba7,0x6098c6240481,0x1c7a001e60000222c00164e9ec86a000088b000fa980798798079bcc03cfcc003db3000408c001e6cedb5,0x8000200000000800082002080022000814e3,0x0,0x0,0x0,0x0,0x0,0x3cc007d4c0079f9800f3f33cc0f30f301e63cc07981e6007b661e603cfcc1e60f3003cfcc0352b922d6,0x409102240d02,0x4091042408e2,0x409102240d02,0x0,0x4091042408e2,0x4091042408e2,0x4091042408e2,0x40910c2408e2,0x4091082408e2,0x0,0x4091082408e2,0x10090240481,0x10010400410100404080082002080402002032e4,0x10090240481,0x10020400810100404080082002080402002034e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x40110240501,0x10240481,0x40110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9417 : TreeBound (n := 4) 107 (programCode 0x4e2b077c5d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10a041240481,0x0,0x10a041240481,0x0,0xacfec00000002b3fdb3fb0000acff829e9800567f759fd8000acff6cfec0000ad0019fd8159fd80159fd82b3fb0159fd81853d30159fd8567f600567f60159fd80acfec00000000acfed59fd8000567f6000002b3fb02323bf0ae023e200000002b3fbacfec00000000567f60005680b9fd80acfec0567f60000000159fd81197477b67f60000000159fd8000acff167f6002b3fb0c29e9a2a1e9a2c,0x800420012002080080804010208001200080ca3,0x2b3fc037e2000acfec00000002b3fbacfec0002b3fbacfec000acff6cfec0000acff6cfec206fc40567f60567f60159fd80567f602b3fb0567f600567f60159fd80acfec00000000acfee09b03bae58be175ee800567f6567f60aeaf3ce0000000159fd80acfec000000567f60005680b9fd8104d81dd67f604baf74159fd802b3fb0567f60000000159fd8000567fb67f6002b3fb06c1f3ab3f8572c,0x400012000080080004080208001200080ca3,0x40a044240481,0x50a045240481,0x40a044240481,0xa040240481,0x20030000080000000200200000200000060001000100004000100008000000008006000210010000040010000000000000100400031001000000004000000010000200010007ffa8,0x400012000080080004010208001200080ca3,0x20030000080000000200200000200000060001000100004000100008000000008006200210010000040010000000000000100400031001000000004000000010000200010007ffa8,0x400012000080080004200208001200080ca3,0x10004400120100804080082002080402004020e4,0x0,0x10a041240481,0x0,0x10a041240481,0x0,0x0,0x8000220000800800080002080022000814e3,0x0,0x8000220000800800080802080022000814e3,0x40a044240481,0x50a045240481,0x40a044240481,0xa040240481],
[0x0,0x8000220000800800080102080022000814e3,0x0,0x8000220000800800082002080022000814e3,0x0,0x0,0x0,0x4002a0010000200010000a00000002000120002014080008000100000040100000100002010000008040000008040000020100400000101000000404000000410000001000887fda7,0x0,0x0,0x40a902341502,0x40b10c6418e2,0x40a902341502,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x40b10c6418e2,0x40b1086418e2,0x0,0x40b1086418e2,0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100400030001000000004000200010000200010007ffa8,0x10010400420100404080182002080402006032e4,0x20030000080000000200200000200200060001000100004000100008000000008004000210010000040040000000100000100400030001000000004000200010000200010007ffa8,0x10020400820100c04080182002080402006034e4,0x22010240481,0x2010240481,0x22010240481,0x2010240481,0x42110240501,0x2010240481,0x42110240501],
[0x2010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9482 : TreeBound (n := 4) 107 (programCode 0x4e2b077c5e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x108841240481,0x0,0x108841240481,0x0,0x6098c2240481,0x6098c6240481,0x6098c2240481,0x6098c6240481,0x408844240481,0x408844240481,0x408844240481,0x8840240481,0x4000000030000000084000000310000000c0002000000010000c000600020020001004000100010000400040000800100001004000001010000004040000008100000010010873227,0x6098c6240481,0x4000000030000000090000000340000000c0002000000010000c000600020020001020000100080000400100000800200001004000001010000004040000008100000010010873227,0x400010000010080004200208001200080ca3,0x10004400120100804080082002080402004020e4,0x0,0x108841240481,0x0,0x108841240481,0x0,0x6098c2240481,0x6098c6240481,0x6098c2240481,0x6098c6240481,0x408844240481,0x408844240481,0x408844240481,0x8840240481],
[0x0,0x6098c6240481,0x0,0x8000200000100800082002080022000814e3,0x0,0x0,0x0,0xf362bad9097e0001e6130782bb20f307983cc1e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x3cc007d4c0079f9800fa983cc1e60f307983cc07983cc007a731e603cfcc1e60f3003cfcc03cc2626d6,0x40a102241502,0x40a10c2418e2,0x40a102241502,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x40a10c2418e2,0x40a1082418e2,0x0,0x40a1082418e2,0x411090240481,0x10010400420100804080082002080402004032e4,0x411090240481,0x10020400820100804080082002080402004034e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x42110240501,0x10240481,0x42110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9547 : TreeBound (n := 4) 107 (programCode 0x4e2b077c5f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x7980001e60f3079807980007987980f31e60f3001e9cc01e6f3003cfcc001023000f6cc001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9548 : TreeBound (n := 4) 107 (programCode 0x4e2b077c60) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x80600018040002088004200200081002080ca3,0x10200418040101004080082002000c00028040e4,0x80600018040004088004200200081004080ca3,0x0,0x0,0x0,0x0,0x0,0x800600018040020088004200200801020080ca3,0x79f9801e63cc0798f30f303cc3cc3cc0f303ccf3003cfcc00f3f3003cc0f37980f379800f37985b3556,0x0,0x0,0x0,0x0,0x600018040100088004200202001100080ca3,0x600018040000088004200208001000080ca3,0x10004400140101004080082002080402008040e4,0x0,0xf30000f303cc88b0000f303cdf5307980003d1c13003cfcc01e6f3003cc003cde600f3f3003cde703885,0x10004412040101004080082002000c00028040e4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10200412040101004080082002008400208040e4,0x10200412040101004080082002010400408040e4,0x10200412040101004080082002010400408040e4],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800000401000000810000008020000010800020001000400010000200020000800040000400020000800000808009000010040000400100008000400000401000028001480d0e28,0x40a102241502,0x40a10c2418e2,0x40a102241502,0x0,0x40a1042410a2,0x40a1042410a2,0x40a1042410a2,0x40a10c2418e2,0x40a1082418e2,0x0,0x40a1082418e2,0x0,0x0,0x10000400000402080080402080022000814e3,0x0,0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481],
[0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x10010400440101004080082002080402008072e4,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x10020400840101004080082002080402008074e4,0x20010240481,0x10240481,0x20010240481,0x10240481,0x40110240501,0x10240481,0x40110240501],
[0x10240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_7804 : TreeBound (n := 4) 107 (programCode 0x4e2b077c) := by
  conv in programCode _ => reduce
  exact branchFour (k := (2,1)) (by decide +kernel) part103_7805 part103_7998 part103_8175 part103_8336 part103_8577 part103_8786 part103_8915 part103_9076 part103_9269 part103_9318 part103_9351 part103_9352 part103_9417 part103_9482 part103_9547 part103_9548

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9645 : TreeBound (n := 4) 107 (programCode 0x4e2b077d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x80c070240481,0x20400802080082012080082002080022000814e3,0x80c070240481,0x0,0x20400800180006010800880022080022000814e3,0x0,0x83c0e6204481,0x20400800080002010000080402000020400814e3,0x83c0e6204481,0x20000800080002000000080402000020000814e3,0x824084208481,0x20000800080002000000080402000020000814e3,0x824084208481,0x0,0x0,0x0,0x20400800080002010000080402010020400814e3,0x0,0x86418c220501,0x20000800080002000000080402000020000814e3,0x86418c220501,0x20100800080002000000080402020020800814e3,0x2040080028000a010801080042080022000815e3,0x0,0x80c061204481,0x3cc12fc0003cc3cc12fc03ccf303cc3cc03cc001e61e6097e0001e61e605b20003cc1e603cc1e61556,0x80c061204481,0x804000200481,0x804000208481,0x804000200481,0x804000208481],
[0x0,0x0,0x0,0x0,0x0,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x20400800480012012002080082080022000816e3,0x20400800080002010000080002080022000814e3,0x20400800880022012004080102080022000814e3,0x0,0x0,0x0,0x0,0x0,0x208902140442,0x208902140442,0x208902140442,0x208902140442,0x1e601e7e61e601e601e60f4e600f301e60f30000f303cc0f30f30f303cfcc001f530007d4c001e6c6c55,0x2d00810020810020400404010088002200182de4,0x208902140442,0x35008100210100404004080100880022002835e4,0x208902140442,0x20a102140442,0x20400804040101014020081002080022000834e3,0x20a102140442,0x0,0x82c0e4204481,0x0],
[0x82c0e4204481,0x0,0x824084208481,0x0,0x824084208481,0x0,0x0,0x0,0x0,0x0,0x864184220501,0x0,0x864184220501,0x0,0x0,0x20400800800820032004082502080022000814e3,0x0,0x20400800801020052004082502080022000814e3,0x0,0x20400802002080092010082402080022000814e3,0x200808020210008400804020048001200142be4,0x8104040022,0x2d00810020410010400804020088002200182de4,0x0,0x29008200208100204008040201080042001029e4,0x8104040022,0x31008400210100404008080202080082002031e4,0x8104040022,0x1004800220100804008100204080102004021a4,0x0,0x3cc001023798408c00102303cc3cc3cc0f303cc03cde603cc79bcfcde63cc25fcbf01e63cc079c08f3b6,0x20400802080082012010080402080022000814e3],
[0x0,0x0,0x0,0x0,0x0,0x79800111679844580012fc7d4c7983cc0007d4c079bcc01e8d90079bcc3cc2d90f303cc3cc0f3079b3b6,0x2008080202100084010080400480012002433e4,0x8104040022,0x35008100204100104010080400880022002835e4,0x1e601e7e61e601e601e60f4e600f301e60f300003cc3cc0f30f3f3003cfcc001f530007d4c001e6c6c55,0x29008200208100204010040401080042001029e4,0x8104040022,0x31008400210100404010080402080082002031e4,0x8104040022,0x1004800220100804008100404080102004021a4,0x20400804040101014020082802080022000834e3,0x1c80a51e6079820460011160f301e63cc0f303cc0f3e405373003d398f33cc39023d00f33cc0b645b5b96,0x20400804080102014020080802080022000834e3,0x20400800080002010000082002080022000814e3,0x0,0x84c168204501,0x1e60f30799e601e63cc3cc0f30f303cc3cc315c7980799e601e63cc03ce5f803d39800f33cc01f081d95,0x84c168204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x1e60f30799e601e63cc3cc0f30f303cc3cc315c7980799e601e63cc03cc79803cde600f6cc001f081d95,0x0,0x0,0x0,0x0],
[0x844108220501,0x844108220501,0x844108220501,0x844108220501,0x20400804080102014020082802080022000834e3,0x8140d0240481,0x20400800080002010080082002080022000814e3,0x8140d0240481,0x0,0x20400800100804030880082002080022000814e3,0x0,0x20400800804020412080082002000820020814e3,0x20400800000000410080082002000020400814e3,0x20400800804020412080082002001020040814e3,0x0,0x20400802010080412080082002002020080814e3,0x0,0x20400802010080412080082002004020100814e3,0x0,0x0,0x2c020200800900024080042001008400200100e4,0x20400800000000410080082002010020400814e3,0x34020400800900024080082002010400400100e4,0x20400800000000410080082002020020800814e3,0x24020800800900024080102004020400804024e4,0x0,0x44021000800900024080202008040401008844e4,0x20400800201008050880082002080022000815e3,0x0,0x20400800100806010880082002000820020814e3,0x20400800000002010080082002000020400814e3,0x2040080020100a010880082002001020040815e3],
[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20400800000002010080082002010020400814e3,0x0,0x20400804020102014080082002020020800834e3,0x24020800801100044080102004020400804024e4,0x20400804020102014080082002040021000834e3,0x44021000801100044080202008040401008844e4,0x20400800402010092080082002080022000816e3,0x0,0x20400800804020112000880022080022000814e3,0x0,0x20400800804020112001080042080022000814e3,0x0,0x8318c2240481,0x800000240481,0x8318c2240481,0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x20400800804020112080082002080022000814e3],
[0x0,0x0,0x0,0x0,0x0,0x8108c2240481,0x800000240481,0x8108c2240481,0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x0,0x0,0x0,0x0,0x0,0x8310c2240481,0x821084240481,0x8310c2240481,0x821084240481,0x821084240481,0x821084240481,0x821084240481,0x821084240481,0x861188240501,0x821084240481],
[0x861188240501,0x86118c240501,0x2c02020080810020408004200108040200102ce4,0x20400802010080412080082002080022000814e3,0x34020400810100404080082002080402002034e4,0x20400804020100814080082002080022000834e3,0x20400800000002010080082002080022000814e3,0x0,0x0,0x0,0x0,0x0,0x8521c2240501,0x842108240501,0x8521c2240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x20400804020102814080082002080022000834e3,0x824090240481,0x780808010802020040807c20040807c200402904,0x824090240481,0x5008100208020200408068200808068200a05104,0x844110240501,0x804010240481,0x844110240501],
[0x844110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_9902 : TreeBound (n := 4) 107 (programCode 0x4e2b077e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 4)
    (a := List.flatten [
[0x0,0x60c0d0240481,0x4000880018020200408060200408060200402104,0x60c0d0240481,0x0,0x0,0x60c0c1204481,0x0,0x60c0c1204481,0x60c0c1204481,0x60c0c1208481,0x0,0x60c0c1208481,0x0,0x0,0x0,0x0,0x1e48552f0c1ddf6fab281dcd650ee6b9f3d07594000000ee6b28430e237c90aa5e165ee88fcd859400001dcd6500ee729b594001dcd651dd11eaca0077447ab2800ee7a0eb2801dd11eaca001dd4d8d0760b360b359400001dd4d8594001deb32650007735943b9ad8e6d0c853e6c9,0x63c0c1220481,0x432820018002080040100000080020000240002194100000010400000801000000100002010000008010000010080000010100432800100002000100100000800020001001087dea7,0x63c0c1220481,0x7980020460003ea60012fc0f30f303cc3cc03ccf3668400097e0001f531e635283cc1e60f303cc5b5c26,0x0,0x63c0c6204481,0xf3086ca001e600000003cc1e60f300003cc000109c879800007983cc3d027203cc00003ccf301e64dc35,0x63c0c6204481,0x80002000000080402000020000814e3,0x24004208481,0x24004200481,0x24004208481,0x0,0x1e60011160003ea60012fc03ccf303cc3cc03cc001023001116000102300097e0f30000f307d4c1e93b6],
[0x1e60011160003ea60012fc03ccf303cc3cc03cc001023001116000102300f4e600f301e60f33cc225fb6,0xf3084e4001e600000003cc1e60f300003cc000109c87980000f307983cc3cc03cc7980799e601e68a8c5,0x1e60011160003ea60012fc03ccf303cc3cc03cc001023001116000102301e7e6007983cc1e63cc9fabb6,0x24004220481,0x24004200481,0x24004220481,0x80002000000080402000020000814e3,0x10ca89adae7e6000f3012fc219513003cfcc001e603d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x60c0c1204481,0x0,0x60c0c1204481,0x4000200481,0x4000208481,0x4000200481,0x4000208481,0x0,0x0,0x1e60011160003ea60012fc03ccf303cc3cc03cc001f5300097e0001f5300f4e600f307980f33cc2dc3b6,0x0,0x1e60011160003ea60012fc03ccf303cc3cc03cc001f5300097e0001f5301e7e6007983cc1e63cc9fabb6,0x4000220481,0x4000200481,0x4000220481,0x4000200481,0x0,0x61c0c2204481,0x0,0x61c0c2204481,0x414082208481,0x414082208481,0x4200201000000804000000000004000020400021001000000004000000010000020000200100000800200001000800001001004200001000c0000200080000800000001001087eea7],
[0x414082208481,0x0,0x0,0x420020100000080400000000000400002040002100100000000400000001000002000020010000080020000100080000100100420000101000000204000000800000001001087eea7,0x0,0x0,0x434082220481,0x0,0x434082220481,0x100000004400000021000000101000000140000800100002000400008001000008000000a00014004a000200020000000208000800080004000a000200010000200008002400daba8,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x109cfaec801e60079807d4c2139f300003cc00f301e679803ccf300f33cfcc003db30007d4c001e68a8c5,0x0,0x0,0x0,0x0,0x0,0x0,0x8089025414c2,0x80a9025414c2,0x8089025414c2,0x400020001000000800000200000000008001002000001008000010000000010000000040010000400040000400040004000100400000101000000404000000410000001000887b1a7,0x809102641d02,0x80a1024414c2,0x809102641d02,0x0,0x80a1024414c2,0x1a94d4a0001e600000001e635283cc0000f30001a9407980000f33cc03cfcc003db30007d4c001e68a8c5,0x80a1024414c2,0x0,0x62c0c4204481,0x0],
[0x62c0c4204481,0x0,0x24004208481,0x24004200481,0x24004208481,0x0,0x0,0x400021000000084000000000000000020040002000100000000400000001000000000200010000800020001000080001000100400000101000000204000000800000001001087eea7,0x0,0x400021000000084000000000000000020040002000100000000400000001000000000200010000800020001000080001000100400000101000000204000000800000001001087eea7,0x24004220481,0x24004200481,0x24004220481,0x0,0x0,0x7980020460007b660014e37bb0f303cc0007d4c0f3b6403cde6003ccf33cc2d9c5700012fc03cc1e9cb6,0x1e60011160003ea6000f30408c00408c000408c03ccf303cde6003ccf33cc1e60f30000b6403cc1e93b6,0x109d0650801e600798079811439001e600007a740bae79803ccf300003cfcc003db30007d4c001e68a8c5,0x1e60011160003ea6000f307d4c00222c0007d4c03ccf303cde6003ccf33cc1e60f300012fc03cc1e93b6,0x1e60011160007b66001375fd4c1e63cc0007d4c03ccf303ce22c03ccf33cc2230bf00012fc03cc1e9446,0x808904641502,0x80a1044410a2,0x808904641502,0x1e60011160003ea6000f307d4c00222c0007d4c03ccf303cde6003ccf33cc1e60f300012fc03cc1e93b6,0x8091046418e2,0x80a1044410a2,0x8091046418e2,0x1e60011160003ea6000f3003cc00222c00003cc03ccf303cde6003ccf33cc1e60f300003cc03cc1e93b6,0x80a1044410a2,0x0,0x80a1044410a2,0xf3084e4001e6000003cfcc1e60f300003cc00000f307981e60f307983cfcc003db30007d4c001e68a8c5],
[0x0,0x0,0x0,0x0,0x1e60011160003ea6000f307d4c00222c0007d4c0798f301e7e600798f33cc1e60f300012fc03cc1e93b6,0x1e600111600020460012fc7d4c7983cc079fd4c0798f300f522c0798f33cc222cf303cc3cc03d0641326,0x808904641502,0x80a1044410a2,0x808904641502,0x1e60011160002046000f307d4c0003cc0007d4c0798f300f4e600798f33cc1e60f300003cc03cfea9326,0x8091046418e2,0x80a1044410a2,0x8091046418e2,0x1e60011160003ea6000f307d4c00222c0007d4c0798f301e7e600798f33cc1e60f300012fc03cc1e93b6,0x80a1044410a2,0xf307980001e600000001e61e603cc0000f30000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x80a1044410a2,0x7980020460007b660012fc0f30f303cc3cc03cd6cc82400097e00000f33cc2d90f300003cc03cc1e9cb6,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x0,0xf4c1e8204501,0x1c7ae3d079a22c1e60f33cc38f4f300f33cc03cc7980798798079bcc03d379a03cde6003d48b01e833c35,0xf4c1e8204501,0x844108220501,0x844108208501,0x844108220501,0x844108208501,0x1c7ae3d079a22c1e60f33cc38f4f300f33cc03cc7980798798079bcc03d31e803cde6004105801e833c35,0x0,0x0,0x0,0x0],
[0x844108220501,0x844108220501,0x844108220501,0x844108220501,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x414090240481,0x4002080048020200408060200408060200402304,0x414090240481,0x0,0x0,0x0,0x0,0x0,0x0,0x6184c2240481,0x6384c6240481,0x6184c2240481,0x0,0x6084c4240481,0x6384c6240481,0x6084c4240481,0x0,0x6384c8240481,0x6384c6240481,0x6384c8240481,0x0,0x0,0x79800f4e6003cde6007981023000408c000408cf30b7b04c001f5300f35bd919000fa98003cfcc1f7156,0x20020800800900024080006004000c00024124e4,0x109d0650801e600798079e2d93900f30001e60f3f30079bcc00f3f3003cc00f33cc01e67980799e68a8c5,0x0,0x1e6007b66001e7e6007980408c00408c000408cf300f33cc001f5300f3003ea60f30798003cfcc1f6856],
[0x4002080080120002408023200400460008406704,0x20020800800900024080102004080400804024e4,0x4002080080120002408022200400460010406504,0x3cc00f3f3003cde60079808118002046000408cf301026cc07b75300f35389e60205071003cfcc5e1576,0x2002080080090002408004200400840020412ce4,0x20020800800900024080102004020400804024e4,0x20020800800900024080082004010400404134e4,0x20020800800900024080002004004400004024e4,0x20020800800900024080102004020400804024e4,0x0,0x20020800800900024080202004040401004064e4,0x10ca89adae7e6000f300f311494201e9cc00799f530079bcc00f3f3003cfcc003db30007d4c001e68a8c5,0x0,0x79800f4e6001e7e6007981023000222c0007d4cf30b736cc0000f300f35b9c590000798003cfcc1f70c6,0x20020800801100044080006004000c00024124e4,0x10ca89adae7e6000f3012fd1494201e9cfcc001f530079bcc00f3f3003cc00f33cc01e67980799e68a8c5,0x0,0x0,0x4002080080120004408022200400460008406504,0x0,0x4002080080120004408022200400460010406504,0x0,0x4002080080120004408028200401060820407504,0x20020800801100044080002004000400804024e4,0x4002080080120004408028200401060840407504,0x4002080080120004408022200404460110406504,0x20020800801100044080102004020400804024e4,0x20020800801100044080102004020402004024e4,0x20020800801100044080202004040401004064e4,0x0,0x0,0x0],
[0x0,0x0,0x410882240481,0x410884240481,0x410882240481,0x410882240481,0x410884240481,0x410884240481,0x410884240481,0x410882240481,0x430888240481,0x410884240481,0x430888240481,0x410882240481,0x0,0x79800f4e6003cde6007987a73001e9cc001e9cd6e71736cc001e60f3f33cc2dcdb307983cc03cc1f7156,0x1e6007b66001e7e6007981e9cc01e9cc001e9cc001023000f301e610233cc1e60f307983cc03cc1f6856,0x109d0650801e60079807daed93900f30000000f3003d398007a73001e9cfcc003db30007d4c001e68a8c5,0x0,0x431082240481,0x240481,0x431082240481,0x240481,0x4240481,0x240481,0x4240481,0x240481,0x8240481,0x240481,0x8240481,0x240481,0x109cfaec801e60079807987b93900f300003ccf3f30079bcc00f3f3003cfcc003db30007d4c001e68a8c5],
[0x0,0x0,0x0,0x0,0x0,0x410882240481,0x240481,0x410882240481,0x240481,0x4240481,0x240481,0x4240481,0x240481,0x8240481,0x240481,0x8240481,0x240481,0x0,0x0,0x0,0x0,0x0,0x431082240481,0x21000240481,0x431082240481,0x21004240481,0x21004240481,0x21000240481,0x21004240481,0x21004240481,0x21008240481,0x21000240481],
[0x21008240481,0x21004240481,0x2002080080810020408004200408040200502ce4,0x20020800820100804080102004080402004024e4,0x20020800810100404080082004080402006034e4,0x79800f4e6003cde6007f39a73000f6cc00003ccf30b643cc0000f300f33cc2d90f307983cc03cc1f7156,0x20020800820100804080102004080402004024e4,0x0,0x0,0x0,0x0,0x0,0xe521c2240501,0x842108240501,0xe521c2240501,0x842108240501,0x842104240501,0x842108240501,0x842104240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x842108240501,0x20020800840101004080102004080402004024e4,0x24010240481,0x4008080108020200408060200408060200402904,0x24010240481,0x4008080208020200408060200408060200407104,0x844110240501,0x4010240481,0x844110240501],
[0x4010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10224 : TreeBound (n := 4) 107 (programCode 0x4e2b077f61) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80c070240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10225 : TreeBound (n := 4) 107 (programCode 0x4e2b077f62) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8340d0204481,0x824090210481,0x8340d0204481,0x0,0x8340c1204481,0x40001002080002000000080402000020000814e3,0x8340c1204481,0x824080200481,0x824082208481,0x40001002080002000000080002000020000814e3,0x824082208481,0x0,0x0,0x0,0x0,0x0,0x824088220481,0x40001002080002000000080002000020000814e3,0x824088220481,0x40001002080002000040082002040021000814e3,0x824090208481,0x0,0x824081218481,0x824084210481,0x824081218481,0x40001002080002000000080002000020000814e3,0x824082210481,0x824084210481,0x824082210481,0x0,0x824084210481],
[0x9c0080801802020040104e020040448008102904,0x824084210481,0x7980b826007987980b6403ccf303cc3cc03cc079803cde7e60079803cc2046001ed98001e6f3812d56,0x824088210481,0x824084210481,0x824088210481,0x0,0x824090208481,0x0,0x0,0x0,0x1e60001e61e603cc0d4dcc0000f307983cc21b2800f4e600f4e6001e9cc00000f30000f6cc001e703375,0x0,0x0,0x0,0x7980799e61e603cc079bcc01e6f307983cc204601e67980799e600f33cc07983cc1e60f6cc001e703d95,0x0,0x0,0xf300ba0c00798f300b6403ccf303cc3cc03cc03cc079bcde6003cc07983ea6000fa98003cde62da556,0x0,0xf300b82600798f300b6403ccf303cc3cc03cc07980799e7e60079807983ea6000fa98003ccf3812d56,0x0,0xf300981cc0798f300b6403ccf303cc3cc03cc1e6007b661e601e6007983ea6000f307983db30799556,0x1e60001e61e603cc0d4dcc0000f307983cc21b29e601e7e601e63cc03cc79800fa9800f7bf001e703375,0x0,0x824090210481,0x0,0x820490218481,0x821090210481,0x820490218481,0x0,0x820890210481],
[0x960082001042000840804b200101042020042b04,0x820890210481,0x0,0x821090210481,0x821090210481,0x821090210481,0x820090210481,0x822090210481,0x821090210481,0x822090210481,0x822090210481,0x824090210481,0x0,0x40001002000800020080082002000020000814e3,0x821090210481,0x40001002001000040080082002000020000814e3,0x0,0x0,0x79800b6b98079f9800799e9cc01e9cc001e9ccf3003cfcc1e60f3003cc1e7e60079f9801e603d431356,0x0,0x0,0x821090210481,0x821090210481,0x821090210481,0x820090200481,0x822090220481,0x821090210481,0x822090220481,0x822090220481,0x824090220481,0x824090210481,0x824090220481],
[0x1e60001e61e603cc0d4dcc0000f307983cc21b373001e9cc01e6f3003cc79800fa9800f7bf001e703375]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10322 : TreeBound (n := 4) 107 (programCode 0x4e2b077f63) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x80c070240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10323 : TreeBound (n := 4) 107 (programCode 0x4e2b077f64) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x40005010080006010880082002000820020814e3,0x7980001e61e603cc7983cc0000f307983cc1e60f30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0x4000901008000a010880082002001020040815e3,0x0,0x80c061204481,0x40001000080002000000080402000020000814e3,0x80c061204481,0x804000200481,0x8140c2208481,0x804000200481,0x8140c2208481,0x0,0x0,0x0,0x0,0x0,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x0,0x80c061208481,0x824084208481,0x80c061208481,0x804000208481,0x8140c2208481,0x804000208481,0x8140c2208481,0x0,0x824084208481,0x0],
[0x824084208481,0x0,0x844108208501,0x804000208481,0x844108208501,0x844108208501,0x0,0x40005000180006000800880022004020020814e3,0x40001000080002000000080402000020000814e3,0x4002900028002a002801080042004020140815e3,0x804000200481,0x0,0x804000200481,0x0,0x0,0x40001001080002000008080202000020000814e3,0x0,0x40001002080002000010080402000020000814e3,0x0,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x0,0x80c061208481,0x824084208481,0x80c061208481,0x804000208481,0x8140c2208481,0x804000208481,0x8140c2208481,0x0],
[0x824084208481,0x0,0x824084208481,0x0,0x844108208501,0x804000208481,0x844108208501,0x844108208501,0x0,0x0,0x0,0x1e60001e61e603cc0038f40000f307983cc1ed79a0f4e600f4e6001e9cc00000f30000f6cc001e703375,0x0,0x0,0x0,0x3cc007b661e9cfcc01704c001f5307a76cc213900f33cc0799e600f33cc03cc1e61e60f6cc001e703885,0x0,0x0,0x0,0x0,0x0,0x1e63cc1e62d903cc4bf3cc0f30f30b643cc315c1e601e67981e61e603ccf3000f6cc00f7bf001ee9b375,0x0,0x7983cc1e61e603cc3cc3cc0f30f307983cc2d907980799e601e63cc03cde6003d39800f6cc001ee9bd95,0x79800204d980799e6012fc0798f301e63cc03cc7987981e62dccfcc00f307a73001f173303db3079d936,0x0,0x40005010000804030880082002008020200814e3,0x40081010090080412080082002008020200814e3,0x40009010001008050880082002008020200815e3,0x0,0x40011010002010092080082002008020200816e3,0x40001010080000010080082002008020200814e3],
[0x40021010004020112080082002008020200814e3,0x0,0x0,0x0,0x40081010010080412080082002008020200814e3,0x0,0x0,0x0,0x40201010040201018080082002008020200854e3,0x0,0x0,0x0,0x8808200200900024080042001008400200100e4,0x0,0x0,0x0,0x0,0x3cc007b661ebb5cc798003cc1e61edaec83ed39f3003cfcc01e6f3003cc1e601e6f300f732841e703885,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40005010000804030880082002010020400814e3,0x40001010000000410080082002010020400814e3,0x40009010001008050880082002010020400815e3,0x40001010000002010080082002010020400814e3],
[0x40011010002010092080082002010020400816e3,0x0,0x40021010004020112080082002010020400814e3,0x0,0x1e67980f301e63cc7b660f30000f307980f4eda73001e9cc00f3f3003cc0f300f37980799e601e77cb45,0x0,0x40081010010080412080082002010020400814e3,0x0,0x0,0x40001010000002010080082002010020400814e3,0x40201010040201018080082002010020400854e3,0x40201010040203018080082002010020400854e3,0x0,0x0,0x10808400200900024080082002010400400100e4,0x1e60001e61e603cc7980003cc000445800097e0f3001e9cc01e6f3003cc00000f30000f6cc001e703375,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8400200100404080002002010400400000e4,0x0,0x1e63cc1e638f43ccb640798f301e6e3d079b8f4f3001e9cc01e6f3003ccf3000f6cc00fa1e801ee9b375,0x0,0x8400200100404080002002010400400000e4,0x0,0x40201010080202018080082002020020800854e3,0x0,0xee6b374245c7ec79400ee88f565000f047fe50000f047fe5000430e237d0918debad0003c11ff94000f047fe50000430e234000ee6b29dd11eaca00773770d6501dcddc359401dd4d8594001dd4d8d3522e04403594773597b9acbdcd65ee6b287736826b29dcd65ee6ee95ad5769],
[0x40001000080002000000080402000020000814e3,0x4000900028000a000801080042001020100815e3,0x804000200481,0x0,0x804000200481,0x0,0x0,0x40001001080002000008080202000020000814e3,0x0,0x40001002080002000010080402000020000814e3,0x0,0x844108220501,0x804000200481,0x844108220501,0x844108220501,0x40201010080202018080082002040021000854e3,0x7983cc1e62d903cc7983cc0f30f30b643cc2d90f30079bcc01e6f3003cde6003d39800f8b2001ee9bd95]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10500 : TreeBound (n := 4) 107 (programCode 0x4e2b077f65) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8140d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10501 : TreeBound (n := 4) 107 (programCode 0x4e2b077f66) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8340c1240481,0x0,0x824086204481,0x804004210481,0x824086204481,0x40001000080002000000080402000020000814e3,0x804004208481,0x804004200481,0x804004208481,0x0,0x804004210481,0x990200204802020040014c80201104c020102b04,0x804004210481,0xf340aa603cc00f3408c03ccf303cc3cc03cc000f307991160000f307b67e6007983cc1e60f381a6d6,0x804004220481,0x804004200481,0x804004220481,0x804004220481,0x8340c1240481,0x0,0x8340c1204481,0x0,0x8340c1204481,0x804000200481,0x804000208481,0x804000200481,0x804000208481,0x0,0x0,0x1e640c8c03cc01e6408c03ccf303cc3cc03cc001e60f3097e0001e60f3f4e600f307980f31e62e3d36,0x0],
[0x1e640aa603cc01e6408c03ccf303cc3cc03cc001e60f3097e0001e60f4e7e6007983cc1e60f381c536,0x804008220481,0x804000200481,0x804008220481,0x804008220481,0x824082240481,0x804000240481,0x824082240481,0x0,0x0,0x0,0x0,0x0,0x820882240481,0x800000240481,0x820882240481,0x800000240481,0x801004240481,0x800000240481,0x801004240481,0x800000240481,0x802008240481,0x800000240481,0x802008240481,0x802008240481,0x804004240481,0x0,0x820486240481,0x9182020040120002401048c20108040e00010104,0x820486240481,0x3cc0408c79bcc3cc03cc07d4c00222c0007d4c03cc1e63cde6003cc1e9cc1e60f300012fc0003cc33b6,0x800804240481],
[0x800000240481,0x800804240481,0x800000240481,0x801000240481,0x800000240481,0x801000240481,0x800000240481,0x802000240481,0x800000240481,0x802000240481,0x802000240481,0x804004240481,0x0,0x0,0x0,0x0,0xf33cc79bdb31e679803cc0fa98003ea60007d4c0f379803ce04d9f983cfcc00088b079a22c0007985936,0x800800240481,0x800000240481,0x800800240481,0x800000240481,0x801004240481,0x800000240481,0x801004240481,0x800000240481,0x802008240481,0x800000240481,0x802008240481,0x802008240481,0x804008240481,0x804000240481,0x804008240481],
[0x804008240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10598 : TreeBound (n := 4) 107 (programCode 0x4e2b077f67) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x8140d0240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10599 : TreeBound (n := 4) 107 (programCode 0x4e2b077f68) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x40005010080006010800880022000820020814e3,0x40081010080082012000880022010020400814e3,0x4000901008000a010800880022001020040815e3,0x40005010080006010800880022000820020814e3,0x40011010080012012000880022002020080816e3,0x40001010080002010000880022004020000814e3,0x40021010080022012000880022004020100814e3,0x0,0x0,0x0,0x40081010080082012000880022010020400814e3,0x0,0x0,0x0,0x40201010080202018000880022040021000854e3,0x0,0x0,0x1e6007b661e7e9cc79fd4c001f53079fd4c206460f31e603cde61b873cc003ccf300f3f3003cde703375,0x7980001e61e603cc7983cc0000f307983cc1e6000007980001e60f303cc00003cc0000f33cc01e703d95,0x3cc007b661e9cfcc7983cc001f5307a76cc213900f33cc0799e616c83cc00799e603ccf300799e703885,0x3cc0001e61e603cc7983cc0000f307983cc1e6000003cc0001e616c83cc00001e60000f300001e703885,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0,0x40005010080006010801080042000820020814e3,0x40001010080002010001080042000020400814e3,0x4000901008000a010801080042001020040815e3,0x40001010080002010001080042000020040814e3,0x40011010080012012001080042002020080816e3,0x40021010080022012001080042004020100814e3,0x40021010080022012001080042004020100814e3,0x40001010080002010001080042000022000814e3,0x1e67980f301e63cc7b69cc0000f30079bcc1ed9800f4e6007a73001e9cc0f300f3f300798f301e77cb45,0x0,0x40081010080082012001080042010020400814e3,0x0,0x0,0x40001010080002010001080042000022000814e3,0x40201010080202018001080042040021000854e3,0x40201010080202018001080042040023000854e3,0x0,0x40005010080006010800880022000820020814e3,0x0,0x4000901008000a010801080042001020040815e3,0x40001010080002010000080002000020000814e3,0x40001010080002010000080002002020080814e3,0x40001010080002010000080002000020000814e3,0x40001010080002010000080002004020100814e3,0x0,0x0,0x0,0x0],
[0x0,0x40201010080202018040081002020020800854e3,0x0,0x40201010080202018040081002040021000854e3,0x0,0x40011010080012012002080082080022000816e3,0x40001010080002010000080002080022000814e3,0x40021010080022012004080102080022000814e3,0x0,0x0,0x0,0x0,0x0,0x8108c2240481,0x800000240481,0x8108c2240481,0x800000240481,0x821084240481,0x800000240481,0x821084240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x0,0x808464240481,0x40081010080080412008080202080022000814e3,0x808464240481,0x3cc7980f301e63cc79803cc000f3007983cde6003cc3cc3cc0f303cc3cfcc001f530007d4c001e77d055,0x8108c4240481,0x800004240481],
[0x8108c4240481,0x800004240481,0x821084240481,0x800004240481,0x821084240481,0x800004240481,0x842104240501,0x800004240481,0x842104240501,0x842104240501,0x0,0x1e6007b66002082c0081183cde600f381183ec646f31e603cde610233cfcc001023000f6cc001e703375,0xf3007d4c3cde6f3007980408c00408c000408c03cc7983cde6003cc79bcc1e60f30000b640001e61556,0x3cc007b661ec6c0c002d90799e604471a109b1420f33cc0799e70cfc5cfcc001f53000f6cc001e703885,0xf33cc7d6b533cc798079808118003ea60007d4c079f9801e7f5a9bcc3cfcc00088b079b15c0007985426,0x8308c6240481,0x800000240481,0x8308c6240481,0x800000240481,0x821084240481,0x800000240481,0x821084240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x0,0x808464240481,0x0,0x808464240481,0x0],
[0x8108c4240481,0x800004240481,0x8108c4240481,0x800004240481,0x821084240481,0x800004240481,0x821084240481,0x800004240481,0x842104240501,0x800004240481,0x842104240501,0x842104240501,0x0,0x0,0x0,0x0,0xf33ccf33db33ccf3007980fa98003ea60007d4c0f379803ce04d9f9879bcc00088b079a22c0007985936,0x8108c2240481,0x800000240481,0x8108c2240481,0x800000240481,0x821084240481,0x800000240481,0x821084240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x40201010080202018020080802080022000854e3,0x0,0x40001000100800020800080102080022000814e3],
[0x0,0x40001000201000040800080102080022000814e3,0x0,0x8308c6240481,0x800000240481,0x8308c6240481,0x800000240481,0x821084240481,0x800000240481,0x821084240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x40201010080202018040081002080022000854e3,0x7983cc1e62d903cc7983cc0f30f30b643cc2d907980799e601e76c803cfcc003db3000f6cc001ee9bd95]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10776 : TreeBound (n := 4) 107 (programCode 0x4e2b077f69) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x824090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10777 : TreeBound (n := 4) 107 (programCode 0x4e2b077f6a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x8304d0240481,0x0,0x821890204481,0x801010210481,0x821890204481,0x0,0x801010208481,0x8708002100120002408043a00010442008040304,0x801010208481,0xf4e9cfcde6000f4e600408c00408c000408cf30000b64001f53000079bea6000fa98003cc1e610856,0x801010210481,0x801010200481,0x801010210481,0x801010210481,0x801010220481,0x801010200481,0x801010220481,0x801010220481,0x8304d0240481,0x0,0x1e6007b661e7e9cc8191803cde6016cfd4c5d2553001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x840041001100044080006000200c00020100e4,0x3cc007b661e9cfcc865080799e6044676cc219513003cfcc01e6f3003cc00799e603ccf300799e703885,0x0,0x0,0x0,0x0,0xf4e63cc088bf3001e7e600fa98003ea60007d4cf3000f6cc00454b0000f37b66001eda7303cc3cc20276,0x0,0x1108004100120004408008a00021048820205104,0x40041001100044080002000200400040000e4],
[0x1108004100120004408008a00021048840205104,0x0,0x4108004100120004408020a00024060880805104,0x40041001100044080002000200400040000e4,0x40040041001100044080202000240401008068e4,0x820890240481,0x0,0x821881240481,0x8588008100420008400142c02048040a00010104,0x821881240481,0x0,0x801002240481,0x800000240481,0x801002240481,0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x800008240481,0x800000240481,0x800008240481,0x800008240481,0x820890240481,0x0,0x0,0x0,0x0,0x0,0x820882240481,0x800000240481,0x820882240481],
[0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x802008240481,0x800000240481,0x802008240481,0x802008240481,0x801010240481,0x800010240481,0x801010240481,0x800010240481,0x802010240481,0x800010240481,0x802010240481,0x802010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10858 : TreeBound (n := 4) 107 (programCode 0x4e2b077f6b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x824090240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10859 : TreeBound (n := 4) 107 (programCode 0x4e2b077f6c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x40005010100804030880082002000820020814e3,0x40081010100880032880082002010020400814e3,0x40009010200808030880082002001020040815e3,0x0,0x40011010100810032880082002002020080816e3,0x40001000000800020080082002080020000814e3,0x40021010100820032880082002004020100814e3,0x40005010100804030880082002080020020814e3,0xee6b37225c6c4d4a00f233bb5281dce6251da80ee6d04d65000000007afea241c0bdcd68b9aca3ba23d94dad17394daca00773595dcd6503b9b4135940ee6d04d6503b9b41359403b9ca6d65007735b1cd65077360b35941dcd73e6b287735b1cd6507735b1cd650ee70c631e34e9,0x40001000000800020080082002004020000814e3,0x40081010100880032880082002010020400814e3,0x800410200481,0x840510220501,0x800410200481,0x840510220501,0x840510220501,0x0,0x0,0x821090210481,0x0,0x0,0x821090208481,0x0,0x821090208481,0xf4e63cfd41366001e9cc008118002046000408cf3000f6cc1ebfdf0000f33ea6001eda7303cc3cc1fd66,0x821090210481,0x821090210481,0x821090210481,0x821090210481,0x821090220481],
[0x821090210481,0x821090220481,0x821090230481,0x0,0x40005010101004050880082002000820020814e3,0x40001000001000040080082002000020400814e3,0x40009010201008050880082002001020040815e3,0x0,0x40011010201010052880082002002020080816e3,0x0,0x40021010201020052880082002004020100814e3,0x0,0x1e600088b01e63cc8314c83cc0001ed98009a6485001e9cc00f3f3003cc0f300f3f300798f301e77cb45,0x40021010201020052880082002004022500814e3,0x40081010201080052880082002010020400814e3,0x800410200481,0x840510220501,0x800410200481,0x840510220501,0x840510220501,0x0,0x1e600097e1e6222c7987983cc1e616c8b645b4139001e9cc01e6f3003cc003ccf300f3f3003cde703375,0x880042001100044080006000200c00020100e4,0x1e600097e1e67d4c79b5283cc1e6445a22c98588d001e9cc01e6f3003cc003ccf303ccf300799e703375,0x0,0x0,0x0,0x0,0xf4e6798088ce6003cfcc00fa98003ea60007d4cf3000f6cc00454b0001e67b66001eda7303cc3cc20276,0x0,0x1108004200120004408008a00021048820205104,0x80042001100044080002000200400040000e4],
[0x1108004200120004408008a00021048840205104,0x1e63cc1e62d903cce3d0f30f303ccb644bf38f4f3001e9cc01e6f3003cc79800f4e600f379801ee9b375,0x4108004200120004408020a00024060880805104,0x80042001100044080002000200400040000e4,0x40080042001100044080202000240401008070e4,0x0,0x40005010102004090800880022080022000814e3,0x40081000402080082080080402080022000814e3,0x40009010202008090801080042080022000815e3,0x0,0x8108c2240481,0x800800240481,0x8108c2240481,0x8108c2240481,0x8308c4240481,0x8308c6240481,0x8308c4240481,0x800800240481,0x840908240501,0x800800240481,0x840908240501,0x840908240501,0x0,0x1e600097e1e6222c79879bcc01e6fa98b682740460f4e6003ea6000f6cfcc001023000f6cc001e703375,0x1e63cfcc3db301e63cc01e9cc01e9cc001e9cc000f3f300f301e60f3f6cc1e60f307983cc0001e61556,0x1e600097e1e6d86c79b529e601e7ed9b90312179a0f4e600f4e6001e9cfcc001023000f6cc001e703375,0x0,0x821082240481,0x800000240481,0x821082240481,0x800000240481,0x800004240481],
[0x800000240481,0x800004240481,0x800000240481,0x800008240481,0x800000240481,0x800008240481,0x800008240481,0x0,0x40005010104004110800880022080022000814e3,0x0,0x40009010204008110801080042080022000815e3,0x0,0x8108c2240481,0x800800240481,0x8108c2240481,0x8108c2240481,0x8308c4240481,0x8308c6240481,0x8308c4240481,0x800800240481,0x840908240501,0x800800240481,0x840908240501,0x840908240501,0x0,0x0,0x0,0x0,0x0,0x8108c2240481,0x800000240481,0x8108c2240481],
[0x800000240481,0x800004240481,0x800000240481,0x800004240481,0x800000240481,0x842108240501,0x800000240481,0x842108240501,0x842108240501,0x821090240481,0x800010240481,0x821090240481,0x800010240481,0x842110240501,0x800010240481,0x842110240501,0x842110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11004 : TreeBound (n := 4) 107 (programCode 0x4e2b077f6d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x844110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11005 : TreeBound (n := 4) 107 (programCode 0x4e2b077f6e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x804010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11006 : TreeBound (n := 4) 107 (programCode 0x4e2b077f6f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x844110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11007 : TreeBound (n := 4) 107 (programCode 0x4e2b077f70) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x844110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_10223 : TreeBound (n := 4) 107 (programCode 0x4e2b077f) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part103_10224 part103_10225 part103_10322 part103_10323 part103_10500 part103_10501 part103_10598 part103_10599 part103_10776 part103_10777 part103_10858 part103_10859 part103_11004 part103_11005 part103_11006 part103_11007

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11009 : TreeBound (n := 4) 107 (programCode 0x4e2b078061) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10c050204481,0x0,0x80460010082002088004200200401060080ca3,0x4400100000400880082002000020400814e3,0x2000000008002000020c00000080020000000080040000100100000200104000010010000040040000080100000100000000100080000400020000800c000010032873227,0x4400100002000880082002000020400814e3,0x0,0x0,0x0,0x0,0x800460010802020088004200200401060080ca3,0x4400100000400880082002000020400814e3,0x1800460010802040088004200200401060080ca3,0x0,0x30004400120004800880082002014820400814e3,0x4400100000100880082002000020400814e3,0x40004400140005000880082002014820400814e3,0x1800460011802060088004200200401060080ca3,0x10c050204481,0x0,0x10c041204481,0x4000180002000800080402000020000814e3,0x10c041204481,0xc040200481,0x20c0c2208481,0x4000180002000800080002000020000814e3,0x20c0c2208481,0x0,0x0,0x0,0x0],
[0x0,0x80c068220481,0x4000180002000800080102000020000814e3,0x80c068220481,0xc040200481,0x0,0x30c0c1208481,0x4000000050a00000101080000400100000c00020481000002004000004810000001001000100004000400028000800040001000008001000020004000080008000100010010877667,0x30c0c1208481,0x20c0c0208481,0x20c0c2208481,0x42a0000110000000400800000200100000c00021501000001004000004010000001042a0010000200040000800080002000100002000100008000400004000800010001001887fe27,0x20c0c2208481,0x0,0x4000000030000000080400000200100000c00020001000000104000004010000001000400100001000400004000800010001000004001000010004000040008000100010010873227,0x4220000110000000081800000200100000c0002110100000100400000401000000104220010010000040040000080006000100002000100001000400004000800010001001887f227,0x4000000030000000080800000200100000c00020001000001004000004010000001002000100008000400010000800020001000004001000010004000040008000100010018873227,0x0,0xa0c0e8208481,0x4000000020200000080080000200100000c00020401000002004000004010000001040800100004000400008000800002001000004001000010004000040008000100010010873227,0xa0c0e8208481,0x20c0c2208481,0x4000180002000880082002080020000814e3,0x0,0x30c0c1208481,0x4000000030000000081000000200200000c000200010000000040000080100000010020001000080004000100008000c0001000020001000080004000100008000200010010873227,0x30c0c1208481,0x20c0c0208481,0x20c0c2208481,0x7980001e6f300b640000f30079bcc001e60003cc0001e60f303cc03cc1e61e60f303cc1e703885,0x20c0c2208481,0x0],
[0x4000000030000000080400000200200000c00020001000000104000008010000001000400100001000400004000800010001000020001000080004000100008000200010010873227,0x0,0x4000000030000000081000000200200000c00020001000000004000008010000001002000100008000400010000800020001000020001000080004000100008000200010010873227,0x0,0xa0c0e8208481,0x4000000030000000081000000200200000c00020001000000004000008010000001040000100000000400010000800002001000020001000080004000100008000200010010873227,0xa0c0e8208481,0x20c0c2208481,0x0,0x804020100820020880082002080020020814e3,0x3cc00f4e62deb5cc00f3008118002046000408cf3000f6cc0f8c1301e6003ea6001ef7e003db307b7d66,0x0,0x3cc007b662dccfcc0079808118003ea60007d4cf30007d4c0f6db301e6003ea6001ef7e003db307c7066,0x0,0x0,0x0,0x0,0x8004200108020200880082002080020200814e3,0x4000100000400880082002080020000814e3,0x10004400110000400880082002080020400814e3,0x0,0x20004800120004800880082002080020800814e3,0x4000100000100880082002080020000814e3,0x5000140005000880082002080021000814e3,0x4000100000000880082002080020000814e3,0x0,0x508450210481,0x4110000090440000202000000801000000c1100000104408220000800040080000104000008010000020040000100100000100010000080040000200100001000100001002086aba7,0x508450210481,0x0,0x4000000030000000080040000201000000800420000001001000004000400010001040000100100000400400000801000001000040001000100004000400008001000010018873227,0x4220000110000000401080000201000000c2202110100000200400000040042000104000010010000040040000080100000100020000100080000400040000800100001001087fe27],
[0x4000000030000000080080000201000000802020000008002000010000400020001040000100100000400400000801000001000040001000100004000400008001000010010873227,0x0,0x409050210481,0x800420010402020088004200200801020080ca3,0x409050210481,0x0,0xc0a070210481,0x4000000030000000080080000201000000c00020000040002000008000400020001040000100100000400400000801000001000040001000100004000400008001000010010873227,0xc0a070210481,0x409050210481,0x0,0x10804400100820020880082002004020400814e3,0x4400100000400880082002000020400814e3,0x0,0x0,0x42a40001100000000800400002060000008020215000010010000040040000100010400001001000004004000008010000010042a000100020000400080000800600001001887f227,0x0,0x0,0x0,0x8004400108020200880082002004020400814e3,0x800420010402020088004200200401020080ca3,0x10004400110000400880082002000020400814e3,0x0,0x223a5b106a931d28371aa4c74a0dc6a5fd51da8000ef1df85e000fd51de412f1f46f6a0000f224d4a077394dad904bc71eed4a00f047fe503b9b4135940ee6d04d6503b9b4135940773770d650077359400773d0759401dcf424e75e37220759401dce536df341780ee6ee959172c9,0x4400100000100880082002010020400814e3,0xee6b2800011f33c33febcf5476a0000eea6c2ca000f5de8140000ee6b280000fd51de45078b70cb40000f5de81400f047fe500773d075940ee6d04d6500ee729b5940773770d6500773594007736826b287737714ef0f07fcc0d6507736826c166b280ee6ee944cf479,0x4400100000400880082002000020400814e3,0x0,0x508450210481,0x440010000070088004200200801040080ca3,0x508450210481,0x440010000200088004200200801040080ca3],
[0x4000000030000000080040000202000000800420000001001000004000000010001040000100100000400400000801000001000200001000800004001000008002000010018873227,0x0,0x0,0x0,0x409050210481,0x4400100000400880082002010020400814e3,0x409050210481,0x0,0xc0a070210481,0x440010000010088004200200801040080ca3,0xc0a070210481,0x409050210481,0x0,0x804020180022000800880022080020020814e3,0x7980001e60000b640000f300003cc001f53007980001e60f303cfcc003db3000f300001e703d95,0x0,0x7980001e60000b640000f300003cc001f53007980001e6f3003cfcc003db3000f300001e703d95,0x0,0x4000180002000800080002080020000814e3,0xf4e601e63cc0798f300b642083b3003cfcc001e61e679803ccf300f33cfd3983db30007983cc1e68a8c5,0x0,0x0,0x0,0x0,0x0,0x20004800180006000820080802080020800814e3,0x4000180002000800080102080020000814e3,0x5000180006000840081002080021000814e3,0x4000180002000800080002080020000814e3,0x80c070220481,0x0,0x80410018004200080084002200801010080ca3],
[0x4000000030000000081000000200200000c000200010000000040000080100000010400001000000004000100008000c0001004000001000000004001000008000200010010873227,0x80410018004200080084004200801010080ca3,0x410018004200080004200200801010080ca3,0x2004100180082000802080082010020100814e3,0x7980001e6f300b640000f30079bcc001e60003cc0001e60f303cc00001e6f300f303cc1e703885,0x4004100180082000804080102010020100814e3,0x0,0x4000000030000000080400000200200000c00020001000000104000008010000001000400100001000400004000800010001004000001000020004001000008000200010010873227,0x0,0x4000000030000000081000000200200000c00020001000000004000008010000001002000100008000400010000800020001004000001000000004001000008000200010010873227,0x0,0x24004100180086000820080802010820100814e3,0x4000000030000000081000000200200000c00020001000000004000008010000001040000100000000400010000800002001004000001000000004001000008000200010010873227,0x40004100180086000840081002010820100814e3,0x410018004200080004010200801010080ca3,0x80c070220481,0xc050200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11186 : TreeBound (n := 4) 107 (programCode 0x4e2b078062) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1dcd66dcf7de84fcfa9b0d04d66e0adca05007736826b28eeb5a97c803f54fcbc4682d00b16d9a3b9e9293528773770d6500b3145c6b3e503b9b4135940ee6d04d6503b9b41359403b9ca6d650077359403b9b41359401dcf41d6503b9b413594077360b359407736826d0c83e14d9,0x110c17368f3000000f4e601141aa03cc79803cc0f30079bcc007a73003d041b43cc00003ccf301e64dc35,0x0,0x0,0x4000004010000010000040040000010600000060000000101000000400400001811040000100100000400400000801000001000004001000010004000040008000100010018873227,0x20000000220000000a00000008200000008800020010000080008000800100010800400010001000010004000200210000100000042000000108000001020000001040002000713a8,0x4000010010000040000080080000010600000060000000102000000400400001820040000100100000400400000801000001000020001000080004000100008000200010010873227,0x0,0x3cc00097e0007d4c000d4a408c7983cc5b2408cf301e63cc25fad901e60006a535296c80004bf07995e6,0xfa983cc1e6000fe64003cc0000f379803cdf53003cfcc01e6f3003cc03cc1e60f30f33cc01e703885,0x3cc00097e0007d4c000b64f6cc00408c3cc408cf301e63cc25f8f301e60f32d912fc7980f30f307995e6,0x3cc00097e0007d4c000bdd83cc7983cc3cc408cf301e63cc26ebf301e601e8d900f379801e6f307995e6,0x9204d0220481,0x798000000000fa98003cc0000f379803cc0f30079bcc01e6f3003cc00003cc0f30f300001e703d95,0x9204d0220481,0x3cc00097e0007d4c000b64408c00408c3cc408cf301e63cc25f8f301e60f32d907987980f30f307995e6,0x0,0x0,0x421010210481,0x0,0x0,0x421010208481,0x0,0x421010208481,0x0,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481],
[0x421010200481,0x421010220481,0x421010210481,0x0,0x0,0x3d39800f300003ccf3007980f30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0xf35be5700799e601e9cc011494201e67980799f530079bcc00f3f3003cc00f33cc01e67980799e68a8c5,0x0,0x0,0x0,0x0,0x0,0x1000000024000000220000000820000000f00142001c0052000000048001400108004000000030000e002c0002800300001000200060001c005e002e0016000000014000a00062ba8,0x0,0x10e06d734f300f301e7e601151cd00f33cc07980f30079bcc007a73003cc3cc03cc3cc03cde601e64dc35,0xf3543e4000000001e7e60111ca500f33cc07980f30079bcc007a73003cfcc003cc00003cc0001e64dc35,0x9204d0220481,0x798000000003d39800f300003ccf3007980f30079bcc01e6f3003cc00003cc1e60f300001e703d95,0x9204d0220481,0xf372b8d40000f301e7e601151cd00f33cc07980f30079bcc007a73003cfcda97cc00003cc0799e64dc35,0x0,0x400000141000005000000401400001050000006000100000500000040041000080104000010010000040040000040100000100000100100000100400001000400001001000887b1a7,0x2000002000080082002000020400814e3,0xf35be5700799e601e9cfcd1494201e67d4c001f530079bcc00f3f3003cc00f33cc01e67980799e68a8c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2000002000080082002010020400814e3],
[0x0,0x80002000002000080082002020020800814e3,0x2000002000080082002000020000814e3,0x2000002000080082002040021000814e3,0x2000002000080082002000020000814e3,0x0,0x1dcd65ee6b2f73597b9acbdcd6503b9aca000b2d05e000ee70be82f03bd664ca000ee6b2bb9acaf224d4a000ee6ee1aca00f224e386b2877712eca001ddc4bb28001e08ffca001dd4d8594001dd4d8d075940077536165001dd4d85940077536165000eee25d94000ee6ee959172c9,0x3cc00097e0007d4c000b6403cc7983cc000f6cc00111600111600011163cc1e60f307983cc0f307995e6,0x0,0x0,0x0,0x20000000220000000a00000008200000008800020010000080008000800000050800000410000001010000010200000010100040000002100008000400000021000040002000713a8,0x0,0x0,0x3cc00097e0007d4c000b6403cc7983cc000f6cc0011163cc1e600011163cc1e60f307983cc0f307995e6,0x3cc00097e0007d4c000bde76cc1e63cc000f6cc03cde603ce5f803cde63cc31648b000222c0f307995e6,0x0,0x3cc00097e0007d4c000bde76cc7983cc000f6cc0799e603ce5f80799e63cc31648b03cc3cc0f307995e6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8089025414c2,0x8089084410a2,0x8089025414c2,0x0],
[0x808904641502,0x8089084410a2,0x808904641502,0x40005000102100084000a01008080602008040e4,0x8089084410a2,0x0,0x8089084410a2,0x0,0x0,0x0,0x0,0x0,0x0,0x80a9025414c2,0x80a1084410a2,0x80a9025414c2,0x0,0x80a1044410a2,0x80a1084410a2,0x80a1044410a2,0x0,0x80a1084410a2,0x0,0x80a1084410a2,0x0,0x0,0x0,0x0,0x0,0x3cc00088b0007d4c00079bcfcc00f6cc003cfcc0001e60000000003ea63cc0000f307983cc07983d1216,0x8089025414c2,0x8089084410a2],
[0x8089025414c2,0x40005000104100104000000028080402008040e4,0x808904641502,0x8089084410a2,0x808904641502,0x0,0x8089084410a2,0x40005000104100104040202008080602008040e4,0x8089084410a2,0x3cc00097e0007d4c000798408c7983cc000408cf301e63cc1e60f301e63cc1e60f307983cc0f307995e6,0x40005000108100204080042008080402009068e4,0x40005000140101004080202008080402008040e4,0x4000500011010040408008200808040200a070e4,0x0,0x0,0x822090210481,0x0,0x0,0x822090208481,0x0,0x822090208481,0x0,0x822090210481,0x822090210481,0x822090210481,0x822090220481,0x822090220481,0x822090210481,0x822090220481,0x822090220481,0x40005000120100804080202008080402008040e4,0x3cc00097e0007d4c000c5703cc7983cc3cc03ccf301e63cc2d90f301e63cc25f8f307983cc0f307995e6],
[0x40005000140101004080202008080402008040e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11347 : TreeBound (n := 4) 107 (programCode 0x4e2b078063) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x10c050204481,0x8000280002000880082002000020400814e3,0x10c050204481,0x0,0x10c041204481,0x8000280002000800080402000020000814e3,0x10c041204481,0xc040200481,0x20c0c2208481,0x8000280002000800080002000020000814e3,0x20c0c2208481,0x0,0x0,0x0,0x0,0x0,0x80c068220481,0x8000280002000800080102000020000814e3,0x80c068220481,0xc040200481,0x0,0x30c0c1208481,0x0,0x30c0c1208481,0x20c0c0208481,0x20c0c2208481,0x1000400001000000010004000014000000010000004040000040100000040008001000000001000080010000200010000100010000100010001000100001000100208793a7,0x20c0c2208481,0x0,0x0,0x1000040004000a0002000000002000200040000800100002000400008001000008000100200000400a000010020000010010001000200014000a0000400200000000400028006aba8],
[0x4000000110000000400800000800100001400020001000001004000004010000006002000100008000400010000800020001000004001000010004000040008000100010018873227,0x0,0xa0c0e8208481,0xee6b2800003b9ad8e6b281dce536b281dcd73e6b282540be400001dcd6503b9b413594007753616500773d07594003b9aca0003b9acbdcd65ee6b283b9ad173597b9ad1735941dcd6c735943b9ad173594ee6b45cd650ee6b36e6b36e6b36e6b28ee6b36e765cb24fd99,0xa0c0e8208481,0x20c0c2208481,0x0,0xf300f30f30798f3012fc001f530079bcc003cc00f6cc00f4e6000f6cc03cc1e60f30f33cc01e7038e5,0x8000280002000800080402000020000814e3,0x50081002800a2000801080042004020500814e3,0x8000280002000800080002000020000814e3,0x0,0x8000280002000800080002000020000814e3,0x0,0x0,0x0,0x110cc000020000000100000000140000000100008660400000001000000404000010010cc00200400001000080001004000001010cc000200000001000000001002087aba7,0x8000280002000810080402000020000814e3,0x0,0x1008040280022000820080802001020100814e3,0x0,0x1008040280022000840081002001020100814e3,0x8000280002000800080002000020000814e3,0x0,0x30c0c1208481,0x0,0x30c0c1208481,0x20c0c0208481,0x20c0c2208481,0x1e60000799e6012fc0000f30079bcc003cc0007980001e60f303cc07983cc1e60f303cc1e703d95,0x20c0c2208481,0x0],
[0x0,0x0,0x0,0x0,0xa0c0e8208481,0x1e60000799e6012fc0000f30079bcc003cc0007983cc1e601e63cc07983cc1e60f303cc1e703d95,0xa0c0e8208481,0x20c0c2208481,0x0,0x0,0x0,0x8000280002000801080042000022000814e3,0x0,0x2008080280082000802080082002022000814e3,0x8000280002000800080002000022000814e3,0x4008100280082000804080102004022000814e3,0x0,0x0,0x0,0x0,0x0,0x8000280002000820080802000022000814e3,0x8000280002000800080102000022000814e3,0x8000280002000840081002000022000814e3,0x8000280002000800080002000022000814e3,0x0,0x508450210481,0x0,0x508450210481,0x0,0x0,0x1004000001000000010040000014000000000000004040000010000800040400001001000001004000010010000010001000010001000010010000100010000100208793a7],
[0x4000000110000000400080000801000001002020000008002000010001800020006040000100100000400400000801000001000040001000100004000400008001000010010873227,0x0,0x409050210481,0x1e9cc0079bcc00f30000000000f33cc03db30079bcc01e6f3003cc0f303cc3cc0f30f301e703d95,0x409050210481,0x0,0xc0a070210481,0x0,0xc0a070210481,0x409050210481,0x0,0x0,0x8000200000400880082002000020400814e3,0x0,0x0,0x4000000110000000400040000802000001000420000001001000004000000010006040000100100000400400000801000001000080001000200004000800008108000010018873227,0x3cc7980f3000f6cc97e001e9cc01e9cc001e9ccf301e63cc1e60f301e600f4e600f379800f37983d4ed6,0x0,0x0,0x0,0x8000200000400880082002000020400814e3,0x8000210000400880082002000020400814e3,0x0,0x1008040220020800880082002001020400814e3,0x8400200000100880082002010020400814e3,0x1008040240021000880082002001020400814e3,0x8000200000000880082002000020400814e3,0x0,0x508450210481,0x8400200000400880082002010020400814e3,0x508450210481,0x8400200002000880082002010020400814e3],
[0x0,0x0,0x0,0x0,0x409050210481,0x8400200000400880082002010020400814e3,0x409050210481,0x0,0xc0a070210481,0x8400200000100880082002010020400814e3,0xc0a070210481,0x409050210481,0x0,0x0,0x4000501a000900024080082008010400408140e4,0x8000201000040880082002000022000814e3,0x0,0x0,0x3cc7980f3003cfcc97e001e9cc01e9cc001e9ccf301e63cc1e60f301e601e7e60079f9801e67983ebb56,0x0,0x0,0x8008200208020200880082002008022000814e3,0x8000200000400880082002000022000814e3,0x10008400210000400880082002010022000814e3,0x0,0x8000220000800880082002000022000814e3,0x0,0x8000240001000880082002000022000814e3,0x8000200000000880082002000022000814e3,0x80c070220481,0x8000280002000880082002000020100814e3,0x80c070220481],
[0xc050200481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11508 : TreeBound (n := 4) 107 (programCode 0x4e2b078064) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x10c041204481,0x0,0x10c041204481,0x10c041204481,0x30c0c1208481,0x4000180002000800880022004020000814e3,0x30c0c1208481,0x0,0x0,0x420020011000000020000200000000000240002010100008000400000001000000400002010000008040000010040000010100420000100000000404000000400800001000887fda7,0x0,0x400220011000800020000200100000000240002010100008040400000001000000400002010000008040000010040000010100400200100000000404000000400008001000887fda7,0x84c161220501,0x432b20018002080040001000080020000240002194100000010400000801000000100002010000008010000010080000010100432800100002000100100000800020001001087dea7,0x84c161220501,0xc041200481,0x0,0x48041208800a2002804080402000820020814e3,0xf3086ca001e600000003cc1e60f300003cc000109c879800007983cc3d027203cc00003ccf301e64dc35,0x50081408800a2002804080402001020040814e3,0x80002000000080402000020000814e3,0x0,0x80002000000080402000020000814e3,0x0,0x0,0x3cc001023000408c0012fc03ccf303cc3cc03cc001116001116000111600097e0f30000f3081183cf3b6,0x7980020460007d4c0012fc0798f301e63cc03cc0025f8000a71000111601e60f307a38260f3f30be3136,0xf3084e4001e600000003cc1e60f300003cc000109c87980000f307983cc3cc03cc7980799e601e68a8c5,0x7980020460007d4c0012fc0798f301e63cc03cc0025f8000a71000111603cc1e60f3ba0c1e6f30c5c936,0x80002000000080402020020800814e3],
[0x80002000000080402000020000814e3,0x80002000000080402040021000814e3,0x80002000000080402000020000814e3,0x0,0x10c041204481,0x10d03bad901e600000012fc21951300003cc001e603d398007a73001e9d032843cc0000799e601e68a8c5,0x10c041204481,0x10c041204481,0x30c0c1208481,0x10d03bad9463e3ccf3012fc219513004494c001e603d398007a73001e9d032843cc0f3079a22c1e68a8c5,0x30c0c1208481,0xf3079ad901e600000012fc1ebc1300003cc001e603d398007a73001e9cfcc003cc00007d4c001e68a8c5,0x0,0x0,0x0,0x0,0x84c161220501,0x8000280002000801080042000020100814e3,0x84c161220501,0xc041200481,0x0,0x10c041204481,0x0,0x10c041204481,0x4000200481,0x4000208481,0x4000200481,0x4000208481,0x0,0x0,0x7980020460007d4c0012fc0798f301e63cc03cc004458001209000204601e60f307a3a0c0f3f30be3136,0x0],
[0x7980020460007d4c0012fc0798f301e63cc03cc004458001209000204603cc1e60f3bdd81e6f30c5c936,0x4000220481,0x4000200481,0x4000220481,0x4000200481,0x400020001000000200004200000010002040002000100008000400000401000004000010010000010040000100040000100100400000101000000404000000410000001000887b1a7,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0xf5e0aec83ea6000f307d4c2139f3003cfcc00f301e679803ccf300f33cfcc003db30007d4c001e68a8c5,0x0,0x0,0x0,0x0,0x0,0x0,0x8089025414c2,0x80a9025414c2,0x8089025414c2,0x400020001000000800040200000100008001002000001008000010000000010000000040010000400040000400040004000100400000101000000404000000410000001000887b1a7,0x809102641d02,0x80a1024414c2,0x809102641d02,0x0,0x80a1024414c2,0xf30d4a0001e600000001e635283cc0000f30001a9407980000f33cc03cfcc003db30007d4c001e68a8c5,0x80a1024414c2,0x0,0x0,0x0,0x0,0x0,0x0,0x400021001000002000000200000000020040002000000008000400000000000080000200010000800040001000040001000100400000101000000404000000410000001000887fda7],
[0x0,0xf308118001e600000798001e600000000001e600f307983cc0f303cc3cfcc003db30007d4c001e68a8c5,0x0,0x400021001000082000000200000000020040002000000008000400000001000080000200010000800020001000040001000100400000101000000204000000410000001000887eda7,0x0,0x400021001000082000000200000000020040002000000008000400000001000080000200010000800020001000040001000100400000101000000204000000410000001000887eda7,0x0,0x0,0x0,0x0,0x0,0x8200010c6486200008200000020001000010100000048620000101000000104000010008010c40020000080100008000100400000081000000204000001010000001002086aba7,0x3cc001023000408c000f30408c00408c000408c03cde603cde6003cde63cc1e60f30000b6407983cf3b6,0x10d0485083ea6000f3079811494201e9cc007a740ca179803ccf307983cfcc003db30007d4c001e68a8c5,0x7980020460007d4c000f30fa98003ea60007d4c079f9801e8d9003cde63cc00088b0b652fc0f3079d936,0x0,0x808904641502,0x80a1044410a2,0x808904641502,0x3cc001023000408c000f307d4c00222c0007d4c03cde603cde6003cde63cc1e60f300012fc07983cf3b6,0x8091046418e2,0x80a1044410a2,0x8091046418e2,0x7980020460007d4c000f30fa98003ea65b203cc079f9801e8d9003cde63cc00088b0b643cc0f3079d936,0x80a1044410a2,0x0,0x80a1044410a2,0x0,0x0,0x0,0x0,0x0],
[0x0,0x8089084410a2,0x80a1084410a2,0x8089084410a2,0x3cc0011160007d4c000f307d4c7983cc0007d4c3cc1e63cc1e603cc1e63cc1e60f303cc3cc0f3079b446,0x80910c6418e2,0x80a1084410a2,0x80910c6418e2,0x0,0x80a1084410a2,0x3cc0011160007d4c0013ef03cc7983cc3cc03cc3cc1e65b22d903cc1e63cc25f8f303cc3cc0f3079b446,0x80a1084410a2,0x0,0x0,0x0,0x0,0x7980020460007d4c000f30fa98003ea60007d4c0f379803ced900799e63cc00088b0b6622c0f3079d936,0x7980020460007d4c00102307992ffea6000f6cc0f3b6403ced900799e63cc0798f30d4c22c0f30b69936,0x808904641502,0x80a1044410a2,0x808904641502,0x3cc000fa9800222c000f307d4c0003cc0007d4c0799e600f4e600799e63cc1e60f300003cc03cfea9326,0x8091046418e2,0x80a1044410a2,0x8091046418e2,0x7980020460007d4c000f30fa98003ea65b2f6cc0f379803ced900799e63cc00088b0b6622c0f3079d936,0x80a1044410a2,0xf307980001e600000001e61e603cc0000f30000f3007980000f300003cfcc003db30007d4c001e68a8c5,0x80a1044410a2,0x0,0x14c168204501,0x0],
[0x14c168204501,0x44108220501,0x44108208501,0x44108220501,0x44108208501,0x0,0x0,0x0,0x0,0x0,0x44108220501,0x44108220501,0x44108220501,0x44108200501,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5,0xf30d4a0001e600001e63cc3528f300003cc1e607980798f300f33cc03cfcc003db30007d4c001e68a8c5,0xf307980001e600000003cc1e60f300003cc0000f3007980000f300003cfcc003db30007d4c001e68a8c5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11685 : TreeBound (n := 4) 107 (programCode 0x4e2b078065) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1140c1204481,0x400000081044400200200000800001000840000000100008220400000041000001000001008000004020000010100000010100000000081044000200000001000800001002086aba7,0x1140c1204481,0x1140c1204481,0x3140c1208481,0x4108400410421001001084002000010008400020841000002104000008410000010000008100000020400000040800000101000010001000020004041080008004200010010877627,0x3140c1208481,0x0,0x4000000210000000800400002000010008400020001000001004000000410000010000004100000010400000040800000101000040001000100004000400008001000010018873227,0x4108400410421000801084002000010008400020841000002104000008410000010000008100000010400000040800000101004000001010000004041080008004200010010877227,0x4000000210000000800800002000010008400020001000000104000000410000010000004100000010400000040800000101000200001000800004001000008002000010010873227,0x0,0x9140c1220481,0x4000000210000000800800002000010008400020001000000104000000410000010000004100000010400000040800000101004000001000020004000080008002000010010873227,0x9140c1220481,0x1140c1204481,0x0,0x400000021000000080000400200c0000080000600000001001000006004000010100400001001000004004000008000c0001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x12010400402080082080080402080022000814e3,0x0,0x0,0x0,0x8010400408080202080080402080022000814e3,0x10400400000002080080402080022000814e3,0x10010400410000402080080402080022000814e3,0x10400400000002080080402080022000814e3,0x30010400420010802080080402080022000816e3],
[0x10400400000402080080402080022000814e3,0x40010400440011002080080402080022000816e3,0x10400400000402080080402080022000814e3,0x0,0x1140c1204481,0x3cc0000f301e6408c0000f3000f6cc00f3003d39800f4e6001e9cc00003cc0000f33cc01e703d95,0x1140c1204481,0x1140c1204481,0x3140c1208481,0x201004048001200200084004200201058081ea3,0x3140c1208481,0x1004048001200200084004200001200081ea3,0x0,0x0,0x4000000210000000801000002000020008400020001000000004000000810000010000020100000080400000100800000201000200001000800004001000008002000010010873227,0x0,0x9140c1220481,0x201004048001200200084004200201040081ea3,0x9140c1220481,0x1140c1204481,0x0,0x1140c1204481,0x0,0x1140c1204481,0x14080200481,0x14080208481,0x10000480002002000080002000020000814e3,0x14080208481,0x0,0x0,0x3cc7980f301e63cc079bcc03ccf303cc3cc03cc00204600097e000204600f4e600f307980f37986a6556,0x0],
[0x0,0x14080220481,0x0,0x14080220481,0x14080200481,0x214082240481,0x10000480002002000080002080022000814e3,0x214082240481,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x0,0x4000000210000000800004002001000008000060000000100100000404000001010000400100001000400004000800010001004000001010000004040000008100000010010873227,0x400000041080000100180000400100000840002000100000300420000c000400010000800100002000400008000800010001004000001010000004040000008100000010018877667,0x0,0x8010200480080202008080202080022000814e3,0x610884240481,0x411084240481],
[0x610884240481,0x410084240481,0x411084240481,0x411084240481,0x411084240481,0x410084240481,0xc120c4240481,0x411084240481,0xc120c4240481,0x411084240481,0x10000480002002080080002080022000814e3,0x0,0x4000000210000000800004002002000008000060000000100100000400000001010002000100008000400010000800020001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x610884240481,0x411084240481,0x610884240481,0x410084240481,0x411084240481,0x411084240481,0x411084240481,0x410084240481,0xc120c4240481,0x411084240481,0xc120c4240481,0x411084240481,0x0,0x0,0x0,0x0],
[0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x8140c8240481,0x0,0x4000000210000000800004002002000008000060000000100100000400000001010040000100000200400000000800020001004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x610884240481,0x411084240481,0x610884240481,0x410084240481,0x411084240481,0x411084240481,0x411084240481,0x410084240481,0xe120c6240481,0x411084240481,0xe120c6240481,0x411084240481,0x8140c8240481],
[0x14080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11846 : TreeBound (n := 4) 107 (programCode 0x4e2b078066) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0xf307980001e600000003cc1e60f300003cc0000f30079bcc00f3f3003cfcc003db30007d4c001e68a8c5]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11847 : TreeBound (n := 4) 107 (programCode 0x4e2b078067) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x1140c1204481,0x0,0x1140c1204481,0x1140c1204481,0x3140c1208481,0x10000040010000000100000400104000000010000040040000004100000400000101000000101000001010000001010000080010000000010000800100002000100208793a7,0x3140c1208481,0x0,0x1000000004000a0002000200002000400040000400100002000400008001000008004000200014000a000000030000000010004000000014000a00040002000080004000200066ba8,0x1000040004000e000200010000200040004000080010000200040000800100000800100020001e000a000040020000200010000100040000400e0000100100000100400028006aba8,0x4000001010000004000800008000010010400020001000000104000000410000060000004100000010400000040800000101000200001000800004001000008002000010010873227,0x3cc7980f31e603cc7d4c00f3f30007d4c00f3000f6cc00f3f3000f6cc00f31f530007d4c001e68a055,0x9140c1220481,0x0,0x9140c1220481,0x1140c1204481,0x0,0x4020100880082002004080402000820020814e3,0x20000880002002000080402000020400814e3,0x4020100880082002004080402001020040814e3,0x20000880002002000080402000020000814e3,0x0,0x20000880002002000080402000020000814e3,0x0,0x0,0x0,0x3cc7980f30079bcc1e63cc03ccf303cc3cc03cc001116001116000111600f4e600f301e60f37985f0156,0x20000880002002000080402010020400814e3,0x0,0x4020100880082002004080402020020800814e3],
[0x20000880002002000080402000020400814e3,0x4020100880082002004080402040021000814e3,0x20000880002002000080402000020000814e3,0x0,0x1140c1204481,0xf300003cc03cc7d4c0000f3000f6cc01e6003d39800f4e6001e9cc00003cc0000f33cc01e703d95,0x1140c1204481,0x1140c1204481,0x3140c1208481,0x50200408800a2002001080042004020500814e3,0x3140c1208481,0x20040880022002001080042000022000814e3,0x0,0x0,0x0,0x0,0x9140c1220481,0xf300003cc03cc7d4c0000f3000f6cc01e6003d39800f4e6001e9cc00003cc1e60f33cc01e703d95,0x9140c1220481,0x1140c1204481,0x0,0x1140c1204481,0x0,0x1140c1204481,0x14080200481,0x14080208481,0x20000880002002000080002000020000814e3,0x14080208481,0x0,0x0,0x3cc7980f301e63cc1e63cc03ccf303cc3cc03cc00204600097e000204600f4e600f307980f37986a6556,0x0],
[0x0,0x14080220481,0x0,0x14080220481,0x14080200481,0x214082240481,0x20000880002002000080002080022000814e3,0x214082240481,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x0,0x4000001010000004000004008001000010000060000000100100000418000001060000400100001000400004000800010001004000001010000004040000008100000010010873227,0x0,0x0,0x8020200880080202008080202080022000814e3,0x610884240481,0x411084240481],
[0x610884240481,0x410084240481,0x411084240481,0x411084240481,0x411084240481,0x410084240481,0xc120c4240481,0x411084240481,0xc120c4240481,0x411084240481,0x0,0x4020100800880022004080402080022000814e3,0x3cc7980f3000222c1e6000408c00408c000408c03cde603cde6003cde63cc1e60f30000b6407983cd556,0x4020100801080042004080402080022000814e3,0x3cc0020462603a0c3cc0008118003ea60007d4c079f9801e8d9003cde63cc00088b098115c0f3079d426,0x610884240481,0x411084240481,0x610884240481,0x410084240481,0x411084240481,0x411084240481,0x411084240481,0x410084240481,0xe120c6240481,0x411084240481,0xe120c6240481,0x411084240481,0x0,0x400000101000000400000400800c000010000060000000100100000600400001060002000100008000400010000800020001004000001010000004040000008100000010010873227,0x0,0x0,0x0],
[0x610884240481,0x411084240481,0x610884240481,0x410084240481,0x411084240481,0x411084240481,0x411084240481,0x410084240481,0xc120c4240481,0x411084240481,0xc120c4240481,0x411084240481,0x0,0x0,0x0,0x0,0x7980020462d97d4c3cc000fa98003ea60007d4c0f379803ced900799e63cc00088b0b6622c0f3079d936,0x210882240481,0x411084240481,0x210882240481,0x10080240481,0x411084240481,0x411084240481,0x411084240481,0x10080240481,0x8120c8240481,0x411084240481,0x8120c8240481,0x10080240481,0x8140c8240481,0x20000880002002000080402080022000814e3,0x8140c8240481],
[0x14080240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12008 : TreeBound (n := 4) 107 (programCode 0x4e2b078068) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x400020001000000020000600000001000200012000000018000000100040000100404000010010000040040000040100000100000100100000100400001000400001001000887b1a7,0x0,0x0,0x0,0x0,0x422220011000000020000200000000000200022110000088000000100000000100404000010010000040040000040100000100422000100000000404000000400000001000887fda7,0x0,0x0,0x1dcd65ee6b2801dd11eacbdcd6500003b9acab2d05e0077359403b9acc18711a00007735cf9aca0b2d05e0000773770d6500773d093616503b9b41359401dcf41d6503b9b4135940773770d650077359b735947735b1cd6503b9ae7cd657735b1cd650ee6b45cd650ee6ee95860119,0x422220011000000020000200000000000200022110000088000000100000000100404000010010000040040000040100000100422000100000000400028000400800001000887fda7,0x0,0x400020011000000020000200000000000200022010000088000000100000000100404000010010000040040000040100000100400000100000000404000000410000001000887fda7,0x0,0x0,0x0,0x0,0x0,0x0,0x40021000800900024080006008000c00028144e4,0x0,0x0,0x3cc007a73001e9cc007980408c00408c000408cf301e63cc001f5301e6003ea60f30798003d3983dc856,0x4002100080120002408023200800460008804704,0x40021000800900024080202008080401008044e4,0x4002100080120002408022200800460010804504,0x79800f4e6003cfcc0079808118002046000408cf303db6cc0f4f5301e65b21e607b7164003db307b8276,0x4002100080090002408004200800840020816ce4,0x40021000800900024080202008040401008044e4,0x40021000800900024080082008010400408174e4,0x40021000800900024080002008004400008044e4],
[0x40021000800900024080102008020400808064e4,0x0,0x40021000800900024080202008040401008044e4,0x0,0x800000404000002020000010020000010080008001e0002000400008000200008004000200010000f00040001000100001000000820001e0e0f0002000200000020400020085aba8,0x10d03bad901e60000000f311494201e60000799f530079bcc00f3f3003d032843cc0000799e601e68a8c5,0xf362bad9097e0001e60f3111bb201e67980799f530079bcc00f3f3003cc00f33cc01e67980799e68a8c5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10a2abadaef7e0079800f3111bb201e67980799f530079bcc00f3f3003cc3cc03cc7980799e601e68a8c5,0xf3079ad901e60000000f3111bb201e60000799f530079bcc00f3f3003cfcc003cc00007d4c001e68a8c5,0x0,0x10d03bad901e60000000f311494201e60000799f530079bcc00f3f3003d032843cc00007983cc1e68a8c5,0x20001e00080070000200002000000400008000000048077000220000000200104000004010000020040000100100000100080000040400000202000001002000001002085aba7,0xf3079ad901e60000000f3111bb201e60000799f530079bcc00f3f3003cfcc003cc00007980001e68a8c5,0x0,0x79800f3f3001e9cc007981023000222c0007d4cf30b736cc0000f301e65b9c590000798003d3983dd0c6,0x40021000801100044080006008000c00028144e4,0xf362bad9097e0001e612fd11bb201e67d4c001f530079bcc00f3f3003cc00f33cc01e67980799e68a8c5,0x0,0x0,0x4002100080120004408022200800460008804504,0x0,0x4002100080120004408022200800460010804504,0x0,0x4002100080120004408028200801060820805504,0x40021000801100044080002008000401008044e4],
[0x4002100080120004408028200801060840805504,0x4002100080120004408022200804460110804504,0x40021000801100044080102008020400808064e4,0x40021000801100044080202008040402008044e4,0x40021000801100044080202008040401008044e4,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x610884240481,0x210882240481,0x210882240481,0x610884240481,0x610884240481,0x610884240481,0x210882240481,0x8509c8240501,0x610884240481,0x8509c8240501,0x10880240481,0x0,0x0,0x3cc007a73001e9cc007981e9cc01e9cc001e9cc001116000f301e611163cc1e60f307983cc07983dc856,0x0,0x0,0x631082240481,0x240481,0x631082240481,0x240481,0x4240481],
[0x240481,0x4240481,0x240481,0x8240481,0x240481,0x8240481,0x240481,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x610884240481,0x210882240481,0x210882240481,0x610884240481,0x610884240481,0x610884240481,0x210882240481,0x8509c8240501,0x610884240481,0x8509c8240501,0x10880240481,0x0,0x0,0x0,0x0,0x0,0x210882240481,0x240481,0x210882240481],
[0x240481,0x4240481,0x240481,0x4240481,0x240481,0x8240481,0x240481,0x8240481,0x240481,0x0,0x0,0x0,0x0,0x0,0x631082240481,0x421000240481,0x631082240481,0x421004240481,0x421004240481,0x421000240481,0x421004240481,0x421004240481,0x421008240481,0x421000240481,0x421008240481,0x421004240481,0x4002100080810020408004200808040200906ce4,0x40021000840101004080202008080402008044e4,0x4002100081010040408008200808040200a074e4,0x0,0x0,0x0],
[0x0,0x0,0x2521c2240501,0x42108240501,0x2521c2240501,0x42108240501,0x42104240501,0x42108240501,0x42104240501,0x42100240501,0x42108240501,0x42108240501,0x42108240501,0x42100240501,0x40021000820100804080202008080402008044e4,0xf30d4a0001e600001e61e635283cc0000f31e60f30079bcc00f3f3003cfcc003db30007d4c001e68a8c5,0x40021000840101004080202008080402008044e4]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12185 : TreeBound (n := 4) 107 (programCode 0x4e2b078069) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x120450204481,0x1804002100082002088004200200401060080ca3,0x120450204481,0x0,0x4000002010000008000040020000010080000060000000101000000400400001000040000100100000400400000801000001000004001000010004000040008000100010018873227,0x43188040104220100010840200000100800000a18c0000202100000400400001000040000100100000400400000801000001004000001010000004043180008004200010010877627,0x4000002010000008000080020000010080000060000000102000000400400001000040000100100000400400000801000001000020001000080004000100008000200010010873227,0x840021000820020080082002080020020814e3,0x520450210481,0x10840021000820020080082002004020400814e3,0x520450210481,0xf4e60001e6000f4e6003cc0003cc79803cc0f3003cfcc00f3f3003cfcc001f530007980001e68a055,0x9204d0220481,0x4002100082002008004200200401000080ca3,0x9204d0220481,0x120450204481,0x0,0x400000201000000800008002000c000080000820000002002000008208000c00000040000100100000400400000801000001000000401000001004000004008000010010010873227,0x421010210481,0x0,0x0,0x421010208481,0x0,0x421010208481,0x0,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481],
[0x421010200481,0x421010220481,0x421010210481,0x0,0x120450204481,0x1e6000079801e7e600f300003ccf3007980f30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0x120450204481,0x0,0x0,0x0,0x0,0x0,0x520450210481,0x0,0x520450210481,0x4004100081004008004200200001200080ca3,0x9204d0220481,0x0,0x9204d0220481,0x120450204481,0x0,0x0,0x0,0x0,0x0,0x2040081080080080002080082080022000814e3,0x40001080000000000080002080022000814e3,0x4040101080080100004080102080022000814e3,0x0,0x8040201080000200008080202080022000814e3,0x3cc0020462603a0c0000008118003ea60007d4c079f9801e8d9003cde63cc00088b098115c0f3079d426,0x0],
[0x7980020462d97d4c000000fa98003ea60007d4c0f379803ced900799e63cc00088b0b6622c0f3079d936,0x2004080108004080002008080208002200081ce3,0x40001080000000000080002080022000814e3,0x4100108004100004008100208002200081ce3,0x40001080000000000080002080022000814e3,0x0,0x4000002010000008000004020000100080000420000001000100004004000010000000004100000010400000040800000101004000001010000004040000008100000010010873227,0x12040081002080080080080402080022000814e3,0x0,0x0,0x220882240481,0x620884240481,0x220882240481,0x220882240481,0x620884240481,0x620884240481,0x620884240481,0x220882240481,0xa20888240481,0x620884240481,0xa20888240481,0x220882240481,0x40001080000000080082002080022000814e3,0x0,0x4000002010000008000004020000200080002020000008000100010008000020000000004100000010400000040800000101004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x220882240481,0x620884240481,0x220882240481,0x220882240481],
[0x620884240481,0x620884240481,0x620884240481,0x220882240481,0xa20888240481,0x620884240481,0xa20888240481,0x220882240481,0x0,0x0,0x0,0x0,0x0,0x220882240481,0x20000240481,0x220882240481,0x20000240481,0x20004240481,0x20000240481,0x20004240481,0x20000240481,0x20008240481,0x20000240481,0x20008240481,0x20000240481,0x421010240481,0x20010240481,0x421010240481,0x20010240481,0x822090240481,0x20010240481,0x822090240481],
[0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12314 : TreeBound (n := 4) 107 (programCode 0x4e2b07806a) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4008100108020200408060200808060200805104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12315 : TreeBound (n := 4) 107 (programCode 0x4e2b07806b) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x0,0x0,0x120450204481,0x1804002200082002088004200200401060080ca3,0x120450204481,0x0,0x4000010010000040000040080000010100000060000000101000000400400001811040000100100000400400000801000001000004001000010004000040008000100010018873227,0x100000040100000001000000401000001000000001000000010004000010010400001001000001004000010010000010040000010000000010400000100002000100208793a7,0x4000010010000040000080080000010100000060000000102000000400400001821040000100100000400400000801000001000020001000080004000100008000200010010873227,0x880022000820020880082002080020020814e3,0x520450210481,0x10880022000820020880082002004020400814e3,0x520450210481,0x0,0x9204d0220481,0x422201000000804000000008000004010000022110000080000000100100000100404000010010000040040000080100000100422000100000000400020000800080001001087fea7,0x9204d0220481,0x120450204481,0x0,0x0,0x421010210481,0x0,0x0,0x421010208481,0x4023100800120002408023200800460008804704,0x421010208481,0x4022100800120002408022200800460010804504,0x421010210481,0x421010200481,0x421010210481,0x421010210481,0x421010220481],
[0x421010200481,0x421010220481,0x421010210481,0x0,0x120450204481,0x7980001e6003cfcc00f300003ccf30079bdb30079bcc01e6f3003cc00003cc0000f33cc01e703d95,0x120450204481,0x0,0x0,0x0,0x0,0x0,0x520450210481,0x0,0x520450210481,0x80042001020040880082002000022000814e3,0x9204d0220481,0x7980001e6003cfcc00f300003ccf30079bdb30079bcc01e6f3003cc00003cc1e60f307981e703d95,0x9204d0220481,0x120450204481,0x0,0x880022000822000880082002000820020814e3,0x80002000002000080082002000020400814e3,0x1080042001022000880082002001020040814e3,0x0,0x0,0x4022100800120004408022200800460008804504,0x0,0x4022100800120004408022200800460010804504,0x0,0x4028100800120004408028200801060820805104,0x80002000002000080082002010020400814e3],
[0x4028100800120004408028200801060840805104,0x80002000002000080082002020020800814e3,0x80002000002000080082002000020000814e3,0x80002000002000080082002040021000814e3,0x80002000002000080082002000020000814e3,0x0,0x4000010010000040000004080000100100000420000001000100004004000010811000004100000010400000040800000101004000001010000004040000008100000010010873227,0x12080082002080082080080402080022000814e3,0x0,0x0,0x220882240481,0x620884240481,0x220882240481,0x220882240481,0x620884240481,0x620884240481,0x620884240481,0x220882240481,0xa20888240481,0x620884240481,0xa20888240481,0x220882240481,0x0,0x4000010010000040000004080000200100000820000002000100008008010420821000004100000010400000040800000101004000001010000004040000008100000010010873227,0x3cc1e60f3000222c1e6001e9cc01e9cc001e9cc001116000f301e611163cc1e60f307983cc07983cd556,0x0,0x0,0x421002240481,0x20000240481,0x421002240481,0x20000240481,0x20004240481],
[0x20000240481,0x20004240481,0x20000240481,0x421008240481,0x20000240481,0x421008240481,0x20000240481,0x0,0x4000010010000040000004080000c00100002020000008000100010010000020841000004100000010400000040800000101004000001010000004040000008100000010010873227,0x0,0x0,0x0,0x220882240481,0x620884240481,0x220882240481,0x220882240481,0x620884240481,0x620884240481,0x620884240481,0x220882240481,0xa20888240481,0x620884240481,0xa20888240481,0x220882240481,0x0,0x0,0x0,0x0,0x0,0x220882240481,0x20000240481,0x220882240481],
[0x20000240481,0x20004240481,0x20000240481,0x20004240481,0x20000240481,0x20008240481,0x20000240481,0x20008240481,0x20000240481,0x421010240481,0x20010240481,0x421010240481,0x20010240481,0x822090240481,0x20010240481,0x822090240481,0x20010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12460 : TreeBound (n := 4) 107 (programCode 0x4e2b07806c) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4008100208020200408060200808060200805104]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12461 : TreeBound (n := 4) 107 (programCode 0x4e2b07806d) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x44110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12462 : TreeBound (n := 4) 107 (programCode 0x4e2b07806e) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12463 : TreeBound (n := 4) 107 (programCode 0x4e2b07806f) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x44110240501]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_12464 : TreeBound (n := 4) 107 (programCode 0x4e2b078070) := by
  conv in programCode _ => reduce
  refine prepared_bound (fun _ _ => false) (by simp) (fuel := 3)
    (a := List.flatten [
[0x4010240481]
]) (b := []) (by decide) ?_
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_11008 : TreeBound (n := 4) 107 (programCode 0x4e2b0780) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,0)) (by decide +kernel) part103_11009 part103_11186 part103_11347 part103_11508 part103_11685 part103_11846 part103_11847 part103_12008 part103_12185 part103_12314 part103_12315 part103_12460 part103_12461 part103_12462 part103_12463 part103_12464

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem part103_0 : TreeBound (n := 4) 107 (programCode 0x4e2b07) := by
  conv in programCode _ => reduce
  exact branchFour (k := (3,1)) (by decide +kernel) part103_1 part103_2 part103_899 part103_900 part103_3013 part103_3014 part103_3815 part103_3816 part103_6057 part103_6874 part103_7803 part103_7804 part103_9645 part103_9902 part103_10223 part103_11008

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem partitioned103 : TreeBound (n := 4) 107 [((0,0),⟨1,1,false⟩),((1,0),⟨2,1,false⟩),((2,0),⟨3,0,true⟩)] := part103_0
open Turing Turing.BusyBeaver in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem one_zero_return_3_machine (M : Machine (Fin 2) (Fin 4))
    (h0 : M 0 0 = some (some 1, Stmt.write 1 .right))
    (h1 : M 1 0 = some (some 2, Stmt.write 1 .right))
    (h2 : M 2 0 = some (some 3, Stmt.write 0 .left))
    (halts : M.IsHalting) : M.HaltsAfter (Machine.init []) 107 := by
  have hm : Matches M
      [((0,0), ⟨1,1,false⟩),((1,0), ⟨2,1,false⟩),((2,0), ⟨3,0,true⟩)] := by
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
  rcases partitioned103 M hm with h | h
  · exact h
  · exact (h halts).elim

end BeaverBound


theorem OMA.solution : OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H2_R1_H3_R1.H3 := BeaverBound.one_zero_return_3_machine
