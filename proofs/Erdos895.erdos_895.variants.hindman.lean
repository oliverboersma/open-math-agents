import FormalConjectures.ErdosProblems.«895»
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Monotone.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Combinatorics.Hindman
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Filter.Cofinite

namespace Erdos895Type

inductive Letter where | A | B | C
  deriving DecidableEq, Repr

inductive Pair where | p12 | p13 | p23
  deriving DecidableEq, Repr

inductive Col where | one | two | three | oneTwo | twoThree | all
  deriving DecidableEq, Repr

open Letter Pair Col

def project : Pair → Col → Option Letter
  | p12, one => some A
  | p12, two => some B
  | p12, three => none
  | p12, oneTwo => some C
  | p12, twoThree => some B
  | p12, all => some C
  | p13, one => some A
  | p13, two => none
  | p13, three => some B
  | p13, oneTwo => some A
  | p13, twoThree => some B
  | p13, all => some C
  | p23, one => none
  | p23, two => some A
  | p23, three => some B
  | p23, oneTwo => some A
  | p23, twoThree => some C
  | p23, all => some C

def bigram : Letter → Letter → List Col
  | A, B => [one, two, three]
  | B, A => [three, two, one]
  | A, C => [one, oneTwo, all]
  | C, A => [all, oneTwo, one]
  | B, C => [three, twoThree, all]
  | C, B => [all, twoThree, three]
  | _, _ => []

def weave : List Letter → List Col
  | a :: b :: w => bigram a b ++ weave (b :: w)
  | _ => []

def eval {X : Type} (f : Letter → X → X) (w : List Letter) (x : X) : X :=
  w.foldr f x

def admissible : List Letter → Prop
  | a :: b :: w => a ≠ b ∧ admissible (b :: w)
  | _ => True

theorem eval_bigram {X : Type} (f : Letter → X → X)
    (idem : ∀ u x, f u (f u x) = f u x)
    (a b : Letter) (ab : a ≠ b) (p : Pair) (x : X) :
    eval f ((bigram a b).filterMap (project p)) x = f a (f b x) := by
  cases a <;> cases b <;> cases p <;> simp_all [bigram, project, eval, List.foldr, List.filterMap]

theorem eval_append {X : Type} (f : Letter → X → X)
    (a b : List Letter) (x : X) :
    eval f (a ++ b) x = eval f a (eval f b x) := by
  simp [eval, List.foldr_append]

theorem eval_weave {X : Type} (f : Letter → X → X)
    (idem : ∀ u x, f u (f u x) = f u x)
    (a b : Letter) (w : List Letter) (h : admissible (a :: b :: w))
    (p : Pair) (x : X) :
    eval f ((weave (a :: b :: w)).filterMap (project p)) x =
      eval f (a :: b :: w) x := by
  have hn : a ≠ b := h.1
  cases w with
  | nil =>
    simp only [weave, List.append_nil]
    exact eval_bigram f idem a b hn p x
  | cons c cs =>
    have ih := eval_weave f idem b c cs h.2 p x
    rw [show weave (a :: b :: c :: cs) =
          bigram a b ++ weave (b :: c :: cs) from rfl,
        List.filterMap_append, eval_append, eval_bigram f idem a b hn p, ih]
    change f a (f b (f b (eval f (c :: cs) x))) = f a (f b (eval f (c :: cs) x))
    rw [idem]
termination_by w.length

end Erdos895Type

namespace Erdos895Triangle
open Erdos895Type
open Letter Pair Col

abbrev State := Nat × Nat
abbrev Triple := Nat × Nat × Nat

def shift : Letter → Nat → State → State
  | A, t, (x,y) => (x+t,y)
  | B, t, (x,y) => (x,y+t)
  | C, t, (x,y) => (x+t,y+t)

def move : Col → Nat → Triple → Triple
  | one, t, (x,y,z) => (x+t,y,z)
  | two, t, (x,y,z) => (x,y+t,z)
  | three, t, (x,y,z) => (x,y,z+t)
  | oneTwo, t, (x,y,z) => (x+t,y+t,z)
  | twoThree, t, (x,y,z) => (x,y+t,z+t)
  | all, t, (x,y,z) => (x+t,y+t,z+t)

def pick : Pair → Triple → State
  | p12, (x,y,_) => (x,y)
  | p13, (x,_,z) => (x,z)
  | p23, (_,y,z) => (y,z)

def op (Q : (Nat → Prop) → Prop) (u : Letter)
    (H : State → Prop) (s : State) : Prop := Q (fun t => H (shift u t s))

theorem shift_shift (u : Letter) (t v : Nat) (s : State) :
    shift u v (shift u t s) = shift u (t+v) s := by
  cases s with | mk x y => cases u <;> simp [shift, Nat.add_assoc]

theorem op_idempotent (Q : (Nat → Prop) → Prop)
    (qadd : ∀ H, Q (fun x => Q (fun y => H (x+y))) ↔ Q H)
    (u : Letter) (H : State → Prop) : op Q u (op Q u H) = op Q u H := by
  funext s
  apply propext
  simp only [op, shift_shift]
  exact qadd (fun t => H (shift u t s))

theorem projected_step (Q : (Nat → Prop) → Prop)
    (qconst : ∀ P : Prop, Q (fun _ => P) ↔ P)
    (p : Pair) (c : Col) (tail : List Col) (H : State → Prop) (s : Triple) :
    Q (fun t => eval (op Q) (tail.filterMap (project p)) H (pick p (move c t s))) ↔
      eval (op Q) ((c :: tail).filterMap (project p)) H (pick p s) := by
  rcases s with ⟨x,y,z⟩
  cases p <;> cases c <;> simp [project, move, pick, shift, op, eval, List.filterMap, qconst]

def edgeAt (Q : (Nat → Prop) → Prop) (w : List Col) (H : State → Prop)
    (s : Triple) (p : Pair) : Prop :=
  eval (op Q) (w.filterMap (project p)) H (pick p s)

theorem some_projection (Q : (Nat → Prop) → Prop)
    (qall : ∀ P, (∀ t, P t) → Q P)
    (qconst : ∀ P : Prop, Q (fun _ => P) ↔ P)
    (qor : ∀ U V, Q (fun t => U t ∨ V t) ↔ Q U ∨ Q V)
    (H : State → Prop) (cover : ∀ x y z, H (x,y) ∨ H (x,z) ∨ H (y,z))
    (w : List Col) (s : Triple) :
    edgeAt Q w H s p12 ∨ edgeAt Q w H s p13 ∨ edgeAt Q w H s p23 := by
  induction w generalizing s with
  | nil => exact cover s.1 s.2.1 s.2.2
  | cons c cs ih =>
    let P := fun p t => edgeAt Q cs H (move c t s) p
    have h : Q (fun t => P p12 t ∨ P p13 t ∨ P p23 t) :=
      qall _ (fun t => ih (move c t s))
    have step (p : Pair) : Q (P p) → edgeAt Q (c::cs) H s p :=
      (projected_step Q qconst p c cs H s).1
    rcases (qor _ _).1 h with l | r
    · exact Or.inl (step p12 l)
    · rcases (qor _ _).1 r with m | n
      · exact Or.inr (Or.inl (step p13 m))
      · exact Or.inr (Or.inr (step p23 n))

theorem reduced_nonedge (Q : (Nat → Prop) → Prop)
    (qall : ∀ P, (∀ t, P t) → Q P)
    (qconst : ∀ P : Prop, Q (fun _ => P) ↔ P)
    (qor : ∀ U V, Q (fun t => U t ∨ V t) ↔ Q U ∨ Q V)
    (qadd : ∀ H, Q (fun x => Q (fun y => H (x+y))) ↔ Q H)
    (H : State → Prop) (cover : ∀ x y z, H (x,y) ∨ H (x,z) ∨ H (y,z))
    (a b : Letter) (w : List Letter) (h : admissible (a::b::w)) :
    eval (op Q) (a::b::w) H (0,0) := by
  have witness : ∃ p, edgeAt Q (weave (a::b::w)) H (0,0,0) p := by
    rcases some_projection Q qall qconst qor H cover (weave (a::b::w)) (0,0,0) with h₁ | h₂ | h₃
    · exact ⟨p12,h₁⟩
    · exact ⟨p13,h₂⟩
    · exact ⟨p23,h₃⟩
  obtain ⟨p, hp⟩ := witness
  change eval (op Q) ((weave (a::b::w)).filterMap (project p)) H
    (pick p (0,0,0)) at hp
  rw [eval_weave _ (op_idempotent Q qadd) a b w h p H] at hp
  cases p <;> exact hp

end Erdos895Triangle

namespace Erdos895Words

open Erdos895Type Letter

def push (u : Letter) : List Letter → List Letter
  | [] => [u]
  | v :: l => if u = v then v :: l else u :: v :: l

def reduce : List Letter → List Letter
  | [] => []
  | u :: l => push u (reduce l)

theorem mem_reduce (u : Letter) (l : List Letter) : u ∈ reduce l ↔ u ∈ l := by
  induction l with
  | nil => simp [reduce]
  | cons a l ih =>
    simp only [reduce, List.mem_cons]
    cases h : reduce l with
    | nil => simp [push, ← ih, h]
    | cons b t =>
      rw [← ih, h]
      by_cases ab : a = b
      · subst a
        simp [push, List.mem_cons]
      · simp [push, ab, List.mem_cons]

theorem reduced_admissible (l : List Letter) : admissible (reduce l) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    change admissible (push a (reduce l))
    cases h : reduce l with
    | nil => trivial
    | cons b t =>
      by_cases ab : a = b
      · simpa [push, ab, h] using ih
      · simp only [push, if_neg ab]
        exact ⟨ab, h ▸ ih⟩

theorem eval_reduce {X : Type} (f : Letter → X → X)
    (idem : ∀ u x, f u (f u x) = f u x) (l : List Letter) (x : X) :
    eval f (reduce l) x = eval f l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change eval f (push a (reduce l)) x = f a (eval f l x)
    rw [← ih]
    cases h : reduce l with
    | nil => rfl
    | cons b t =>
      by_cases ab : a = b
      · subst a
        change eval f (if b = b then b :: t else b :: b :: t) x = _
        simp [eval, List.foldr, idem]
      · simp [push, ab, eval]

def code : Bool → Bool → Option Letter
  | false, false => none
  | true, false => some A
  | false, true => some B
  | true, true => some C

def word {n : Nat} (s t : Fin n → Bool) : List Letter :=
  (List.ofFn fun i => code (s i) (t i)).filterMap id

theorem mem_word {n : Nat} (s t : Fin n → Bool) (i : Fin n) {u : Letter}
    (h : code (s i) (t i) = some u) : u ∈ word s t := by
  exact List.mem_filterMap.mpr ⟨some u, List.mem_ofFn.mpr ⟨i, h⟩, rfl⟩

theorem at_least_two {n : Nat} {s t : Fin n → Bool}
    (hs : ∃ i, s i = true) (ht : ∃ j, t j = true)
    (hd : ∃ i, s i ≠ t i) :
    ∃ a b l, reduce (word s t) = a :: b :: l := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  obtain ⟨d, hdiff⟩ := hd
  have aux (i : Fin n) {u : Letter} (h : code (s i) (t i) = some u) :
      u ∈ reduce (word s t) := (mem_reduce _ _).mpr (mem_word _ _ i h)
  cases he : reduce (word s t) with
  | nil =>
    cases ht' : t i
    · have z := aux i (u := A) (by simp [hi, ht', code])
      simp [he] at z
    · have z := aux i (u := C) (by simp [hi, ht', code])
      simp [he] at z
  | cons a l =>
    cases l with
    | cons b l => exact ⟨a,b,l,rfl⟩
    | nil =>
      have fixed (j : Fin n) {u : Letter} (hu : code (s j) (t j) = some u) : u = a := by
        simpa [he] using aux j hu
      cases a with
      | A =>
        cases hh : s j
        · have := fixed j (u := B) (by simp [code, hh, hj]); contradiction
        · have := fixed j (u := C) (by simp [code, hh, hj]); contradiction
      | B =>
        cases hh : t i
        · have := fixed i (u := A) (by simp [code, hh, hi]); contradiction
        · have := fixed i (u := C) (by simp [code, hh, hi]); contradiction
      | C =>
        cases hh : s d <;> cases hh' : t d
        · simp [hh, hh'] at hdiff
        · have := fixed d (u := B) (by simp [code, hh, hh']); contradiction
        · have := fixed d (u := A) (by simp [code, hh, hh']); contradiction
        · simp [hh, hh'] at hdiff

def maskedSum : {n : Nat} → (Fin n → Bool) → (Fin n → Nat) → Nat
  | 0, _, _ => 0
  | _ + 1, s, a => (if s 0 then a 0 else 0) +
      maskedSum (fun i => s i.succ) (fun i => a i.succ)

def dx : Letter → Nat → Nat
  | A, v | C, v => v
  | B, _ => 0

def dy : Letter → Nat → Nat
  | B, v | C, v => v
  | A, _ => 0


abbrev Quant := (Nat → Prop) → Prop
abbrev Pred := Nat × Nat → Prop
abbrev TupleQuant := (n : Nat) → ((Fin n → Nat) → Prop) → Prop

theorem typical_eval
    (Q : Quant) (Ty : TupleQuant)
    (zero : ∀ P, Ty 0 P ↔ P Fin.elim0)
    (succ : ∀ n P, Ty (n + 1) P ↔ Q (fun a => Ty n (fun v => P (Fin.cases a v))))
    (constant : ∀ p : Prop, Q (fun _ => p) ↔ p)
    (f : Letter → Pred → Pred)
    (step : ∀ u (H : Pred) (z : Nat × Nat),
      f u H z ↔ Q (fun v => H (z.1 + dx u v, z.2 + dy u v)))
    {n : Nat} (s t : Fin n → Bool) (H : Pred) (z : Nat × Nat) :
    Ty n (fun v => H (z.1 + maskedSum s v, z.2 + maskedSum t v)) ↔
      eval f (word s t) H z := by
  induction n generalizing z with
  | zero =>
    rw [zero]
    simp [maskedSum, word, eval]
  | succ n ih =>
    let ss := fun i : Fin n => s i.succ
    let tt := fun i : Fin n => t i.succ
    let tail := eval f (word ss tt) H
    have h (a : Nat) :
        Ty n (fun v => H (z.1 + maskedSum s (Fin.cases a v),
                          z.2 + maskedSum t (Fin.cases a v))) ↔
        tail (z.1 + (if s 0 then a else 0), z.2 + (if t 0 then a else 0)) := by
      simpa [ss, tt, tail, maskedSum, Nat.add_assoc] using
        ih ss tt (z.1 + (if s 0 then a else 0), z.2 + (if t 0 then a else 0))
    rw [succ, show (fun a => Ty n (fun v => H (z.1 + maskedSum s (Fin.cases a v),
                       z.2 + maskedSum t (Fin.cases a v)))) =
        (fun a => tail (z.1 + (if s 0 then a else 0), z.2 + (if t 0 then a else 0))) from
      funext (fun a => propext (h a))]
    have head : word s t =
        match code (s 0) (t 0) with
        | none => word ss tt
        | some u => u :: word ss tt := by
      simp only [word, List.ofFn_succ, List.filterMap_cons, id_eq, ss, tt]
      cases code (s 0) (t 0) <;> rfl
    rw [head]
    cases ha : s 0 <;> cases hb : t 0
    · simpa [ha, hb, code, tail] using constant (tail z)
    · simpa [ha, hb, code, eval, tail, dx, dy] using (step B tail z).symm
    · simpa [ha, hb, code, eval, tail, dx, dy] using (step A tail z).symm
    · simpa [ha, hb, code, eval, tail, dx, dy] using (step C tail z).symm

theorem pairs_typical
    (Q : Quant) (Ty : TupleQuant)
    (zero : ∀ P, Ty 0 P ↔ P Fin.elim0)
    (succ : ∀ n P, Ty (n + 1) P ↔ Q (fun a => Ty n (fun v => P (Fin.cases a v))))
    (constant : ∀ p : Prop, Q (fun _ => p) ↔ p)
    (f : Letter → Pred → Pred)
    (step : ∀ u (H : Pred) (z : Nat × Nat),
      f u H z ↔ Q (fun v => H (z.1 + dx u v, z.2 + dy u v)))
    (idem : ∀ u H, f u (f u H) = f u H)
    (H : Pred)
    (hom : ∀ a b l, admissible (a :: b :: l) → eval f (a :: b :: l) H (0,0))
    {n : Nat} (s t : Fin n → Bool) (hs : ∃ i, s i = true)
    (ht : ∃ i, t i = true) (hd : ∃ i, s i ≠ t i) :
    Ty n (fun v => H (maskedSum s v, maskedSum t v)) := by
  obtain ⟨a, b, l, he⟩ := at_least_two hs ht hd
  have reduced := reduced_admissible (word s t)
  rw [he] at reduced
  have val := hom a b l reduced
  rw [← he, eval_reduce f idem] at val
  simpa using (typical_eval Q Ty zero succ constant f step s t H (0,0)).mpr val

end Erdos895Words

namespace Erdos895Words

open Erdos895Type

theorem maskedSum_univ {n : Nat} (s : Fin n → Bool) (v : Fin n → Nat) :
    maskedSum s v = ∑ i, if s i then v i else 0 := by
  induction n with
  | zero => simp [maskedSum]
  | succ n ih =>
    rw [Fin.univ_succAbove n 0, Finset.sum_cons, Finset.sum_map, Fin.coe_succAboveEmb,
      Fin.succAbove_zero]
    change (if s 0 then v 0 else 0) + maskedSum (fun i => s i.succ) (fun i => v i.succ) = _
    rw [ih]

theorem maskedSum_finset {n : Nat} (S : Finset (Fin n)) (v : Fin n → Nat) :
    maskedSum (fun i => decide (i ∈ S)) v = ∑ i ∈ S, v i := by
  rw [maskedSum_univ]
  simp [Finset.sum_ite_mem]

theorem finset_pairs_typical
    (Q : Quant) (Ty : TupleQuant)
    (zero : ∀ P, Ty 0 P ↔ P Fin.elim0)
    (succ : ∀ n P, Ty (n + 1) P ↔ Q (fun a => Ty n (fun v => P (Fin.cases a v))))
    (constant : ∀ p : Prop, Q (fun _ => p) ↔ p)
    (f : Letter → Pred → Pred)
    (step : ∀ u (H : Pred) (z : Nat × Nat),
      f u H z ↔ Q (fun v => H (z.1 + dx u v, z.2 + dy u v)))
    (idem : ∀ u H, f u (f u H) = f u H)
    (H : Pred)
    (hom : ∀ a b l, admissible (a :: b :: l) → eval f (a :: b :: l) H (0,0))
    {n : Nat} (S T : Finset (Fin n)) (hs : S.Nonempty) (ht : T.Nonempty) (hd : S ≠ T) :
    Ty n (fun v => H (∑ i ∈ S, v i, ∑ i ∈ T, v i)) := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  have hne : ∃ i, decide (i ∈ S) ≠ decide (i ∈ T) := by
    apply Classical.byContradiction
    intro contra
    apply hd
    ext i
    have eq : decide (i ∈ S) = decide (i ∈ T) := by
      apply Classical.byContradiction
      intro h
      exact contra ⟨i, h⟩
    by_cases h : i ∈ S <;> by_cases h' : i ∈ T <;> simp_all
  have htup := pairs_typical Q Ty zero succ constant f step idem H hom
    (fun i => decide (i ∈ S)) (fun i => decide (i ∈ T)) ⟨i, by simpa using hi⟩
    ⟨j, by simpa using hj⟩ hne
  simpa only [maskedSum_finset] using htup

end Erdos895Words

namespace Erdos895Extract

/-- Successively quantify the coordinates of an increasing-index tuple. -/
def Typical (Q : (Nat → Prop) → Prop) :
    (k : Nat) → ((Fin k → Nat) → Prop) → Prop
  | 0, P => P Fin.elim0
  | k + 1, P => Q (fun t => Typical Q k (fun a => P (Fin.cases t a)))

/-- The finite-intersection, witness and cofinite properties used for extraction. -/
structure LargeQuantifier (Q : (Nat → Prop) → Prop) : Prop where
  true_mem : Q (fun _ => True)
  mono : ∀ {A B : Nat → Prop}, (∀ x, A x → B x) → Q A → Q B
  inter : ∀ {A B : Nat → Prop}, Q A → Q B → Q (fun x => A x ∧ B x)
  witness : ∀ {A : Nat → Prop}, Q A → ∃ x, A x
  tail : ∀ b : Nat, Q (fun t => b < t)

variable {Q : (Nat → Prop) → Prop}

theorem typical_mono (hQ : LargeQuantifier Q) {k : Nat}
    {P R : (Fin k → Nat) → Prop} (h : ∀ a, P a → R a)
    (hp : Typical Q k P) : Typical Q k R := by
  induction k with
  | zero => exact h _ hp
  | succ k ih => exact hQ.mono (fun t ht => ih (fun a => h (Fin.cases t a)) ht) hp

theorem typical_true (hQ : LargeQuantifier Q) (k : Nat) :
    Typical Q k (fun _ => True) := by
  induction k with
  | zero => trivial
  | succ k ih => exact hQ.mono (fun _ _ => ih) hQ.true_mem

theorem typical_and (hQ : LargeQuantifier Q) {k : Nat}
    {P R : (Fin k → Nat) → Prop} (hp : Typical Q k P) (hr : Typical Q k R) :
    Typical Q k (fun a => P a ∧ R a) := by
  induction k with
  | zero => exact ⟨hp, hr⟩
  | succ k ih =>
    exact hQ.mono (fun _ h => ih h.1 h.2) (hQ.inter hp hr)

theorem typical_list_all {ι : Type} (hQ : LargeQuantifier Q) {k : Nat}
    (L : List ι) (P : ι → (Fin k → Nat) → Prop)
    (hp : ∀ j ∈ L, Typical Q k (P j)) :
    Typical Q k (fun a => ∀ j ∈ L, P j a) := by
  induction L with
  | nil =>
    exact typical_mono hQ (fun _ _ _ hj => False.elim (List.not_mem_nil hj))
      (typical_true hQ k)
  | cons i is ih =>
    have hhead := hp i (by simp)
    have htail := ih (fun j hj => hp j (by simp [hj]))
    apply typical_mono hQ _ (typical_and hQ hhead htail)
    intro a h j hj
    rcases List.mem_cons.mp hj with hji | hji
    · exact hji ▸ h.1
    · exact h.2 j hji

theorem choose_increasing_above (hQ : LargeQuantifier Q) {k : Nat}
    (P : (Fin k → Nat) → Prop) (hP : Typical Q k P) (lower : Nat) :
    ∃ a, P a ∧ (∀ i, lower < a i) ∧ (∀ i j, i < j → a i < a j) := by
  induction k generalizing lower with
  | zero => exact ⟨Fin.elim0, hP, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨t, ht, hrest⟩ := hQ.witness (hQ.inter (hQ.tail lower) hP)
    obtain ⟨b, hb, htb, hinc⟩ := ih (fun a => P (Fin.cases t a)) hrest t
    refine ⟨Fin.cases t b, hb, ?_, ?_⟩
    · intro i
      refine Fin.cases ht (fun j => ?_) i
      exact Nat.lt_trans ht (htb j)
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro j
        refine Fin.cases (fun h => False.elim (Nat.lt_irrefl 0 h)) (fun j' _ => htb j') j
      · intro j
        refine Fin.cases (fun h => False.elim (Nat.not_lt_zero _ h)) (fun j' h => ?_) j
        exact hinc i' j' (Nat.lt_of_succ_lt_succ h)

/-- A single actual tuple meets every one of the finitely many typical constraints.
    Its entries are positive and strictly increasing. -/
theorem extract_family {ι : Type} (hQ : LargeQuantifier Q) {k : Nat}
    (L : List ι) (P : ι → (Fin k → Nat) → Prop)
    (hp : ∀ j ∈ L, Typical Q k (P j)) :
    ∃ a, (∀ i, 0 < a i) ∧ (∀ i j, i < j → a i < a j) ∧ ∀ j ∈ L, P j a := by
  obtain ⟨a, ha, hpos, hinc⟩ := choose_increasing_above hQ _ (typical_list_all hQ L P hp) 0
  exact ⟨a, hpos, hinc, ha⟩


/-- Specialization to all distinct eligible pairs in an enumerated finite index type. -/
theorem extract_pairs_of_cover {ι : Type} (hQ : LargeQuantifier Q) {k : Nat}
    (L : List ι) (covered : ∀ i, i ∈ L) (eligible : ι → Prop)
    (R : ι → ι → (Fin k → Nat) → Prop)
    (h : ∀ S T, eligible S → eligible T → S ≠ T → Typical Q k (R S T)) :
    ∃ a, (∀ i, 0 < a i) ∧ (∀ i j, i < j → a i < a j) ∧
      ∀ S T, eligible S → eligible T → S ≠ T → R S T a := by
  classical
  let P : ι → ι → (Fin k → Nat) → Prop := fun S T a =>
    eligible S → eligible T → S ≠ T → R S T a
  have hp : ∀ S T, Typical Q k (P S T) := by
    intro S T
    by_cases hs : eligible S ∧ eligible T ∧ S ≠ T
    · exact typical_mono hQ (fun _ z _ _ _ => z) (h S T hs.1 hs.2.1 hs.2.2)
    · exact typical_mono hQ (fun _ _ hS hT hn => False.elim (hs ⟨hS,hT,hn⟩))
        (typical_true hQ k)
  have hs : ∀ S ∈ L, Typical Q k (fun a => ∀ T ∈ L, P S T a) := by
    intro S _
    exact typical_list_all hQ L (P S) (fun T _ => hp S T)
  obtain ⟨a, pos, inc, h⟩ := extract_family hQ L _ hs
  exact ⟨a, pos, inc, fun S T => h S (covered S) T (covered T)⟩

/-- A uniform formulation for any subset-sum operation, with the independent-set statement
    written as pairwise nonadjacency of distinct images of eligible subsets. -/
theorem extract_independent_image {ι : Type} (hQ : LargeQuantifier Q) {k : Nat}
    (L : List ι) (covered : ∀ i, i ∈ L) (eligible : ι → Prop)
    (sum : (Fin k → Nat) → ι → Nat) (Adj : Nat → Nat → Prop)
    (h : ∀ S T, eligible S → eligible T → S ≠ T →
      Typical Q k (fun a => ¬Adj (sum a S) (sum a T))) :
    ∃ a, (∀ i, 0 < a i) ∧ (∀ i j, i < j → a i < a j) ∧
      ∀ x y, (∃ S, eligible S ∧ x = sum a S) → (∃ T, eligible T ∧ y = sum a T) →
        x ≠ y → ¬Adj x y := by
  obtain ⟨a, pos, inc, hp⟩ := extract_pairs_of_cover hQ L covered eligible _ h
  refine ⟨a, pos, inc, ?_⟩
  rintro _ _ ⟨S, hs, rfl⟩ ⟨T, ht, rfl⟩ hne
  exact hp S T hs ht (fun heq => hne (congrArg (sum a) heq))

end Erdos895Extract

namespace Erdos895Extract

/-- Extract the exact finite-subset-sum tuple needed for Erdős 895.
    This form is independent of how a triangle-free graph is represented. -/
theorem extract_finset_sums {Q : (Nat → Prop) → Prop} (hQ : LargeQuantifier Q)
    {k : Nat} (Adj : Nat → Nat → Prop)
    (h : ∀ S T : Finset (Fin k), S.Nonempty → T.Nonempty → S ≠ T →
      Typical Q k (fun a => ¬Adj (∑ i ∈ S, a i) (∑ i ∈ T, a i))) :
    ∃ a : Fin k → Nat, StrictMono a ∧ (∀ i, 0 < a i) ∧
      ∀ S T : Finset (Fin k), S.Nonempty → T.Nonempty → S ≠ T →
        ¬Adj (∑ i ∈ S, a i) (∑ i ∈ T, a i) := by
  classical
  let allSubsets : List (Finset (Fin k)) := Finset.univ.toList
  have covers (S : Finset (Fin k)) : S ∈ allSubsets :=
    Finset.mem_toList.mpr (Finset.mem_univ S)
  obtain ⟨a, pos, inc, independent⟩ :=
    extract_pairs_of_cover hQ allSubsets covers Finset.Nonempty _ h
  exact ⟨a, fun _ _ hij => inc _ _ hij, pos, independent⟩

/-- An extensional version matching the original finite-sums set, including collisions. -/
theorem extract_finset_image {Q : (Nat → Prop) → Prop} (hQ : LargeQuantifier Q)
    {k : Nat} (Adj : Nat → Nat → Prop)
    (h : ∀ S T : Finset (Fin k), S.Nonempty → T.Nonempty → S ≠ T →
      Typical Q k (fun a => ¬Adj (∑ i ∈ S, a i) (∑ i ∈ T, a i))) :
    ∃ a : Fin k → Nat, StrictMono a ∧ (∀ i, 0 < a i) ∧
      Set.Pairwise {m | ∃ S : Finset (Fin k), S.Nonempty ∧ m = ∑ i ∈ S, a i}
        (fun x y : Nat => ¬Adj x y) := by
  obtain ⟨a, inc, pos, hnon⟩ := extract_finset_sums hQ Adj h
  refine ⟨a, inc, pos, ?_⟩
  rintro x ⟨S, hs, rfl⟩ y ⟨T, ht, rfl⟩ hne
  apply hnon S T hs ht
  rintro rfl
  exact hne rfl

end Erdos895Extract

open Filter
open scoped BigOperators
namespace Erdos895Compactness

/-- The infinite-graph assertion needed to obtain the finite threshold. -/
def InfiniteAssertion (k : ℕ) : Prop :=
  ∀ G : SimpleGraph ℕ, G.CliqueFree 3 →
    ∃ a : Fin k → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
      ∀ S T : Finset (Fin k), S.Nonempty → T.Nonempty →
        (∑ i ∈ S, a i) ≠ (∑ i ∈ T, a i) →
          ¬ G.Adj (∑ i ∈ S, a i) (∑ i ∈ T, a i)

/-- The formulation in the fixed formal-conjectures problem. -/
def FiniteConclusion (k n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Set.Icc 1 n), G.CliqueFree 3 →
    ∃ a : Fin k → ℕ, StrictMono a ∧ ∃ I : Set (Set.Icc 1 n), G.IsIndepSet I ∧
      Subtype.val '' I = {m | ∃ S : Finset (Fin k), S.Nonempty ∧ m = ∑ i ∈ S, a i}

/-- Choose counterexamples arbitrarily far out and take their edgewise ultrafilter limit.
Only finitely many sums and pairs need to be transferred back to one counterexample. -/
theorem finite_of_infinite (k : ℕ) (hyp : InfiniteAssertion k) :
    ∀ᶠ n in atTop, FiniteConclusion k n := by
  classical
  by_contra hc
  rw [eventually_atTop] at hc
  push Not at hc
  obtain ⟨N, hN⟩ := Classical.axiomOfChoice (fun m : ℕ => hc (m+1))
  have Hbad (m : ℕ) := (hN m).2
  simp only [FiniteConclusion, not_forall] at Hbad
  choose gs htri hbad using Hbad
  let emb (m : ℕ) : Set.Icc 1 (N m) ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let gs' (m : ℕ) := (gs m).map (emb m)
  have htri' (m : ℕ) : (gs' m).CliqueFree 3 := by
    have : Nonempty (Set.Icc 1 (N m)) := ⟨⟨1, le_rfl, by have := (hN m).1; omega⟩⟩
    exact SimpleGraph.cliqueFree_map_iff.mpr (htri m)
  let u := Ultrafilter.of (atTop : Filter ℕ)
  let L : SimpleGraph ℕ := {
    Adj := fun x y => ∀ᶠ m in u, (gs' m).Adj x y
    symm := ⟨fun _ _ h => h.mono (fun _ e => e.symm)⟩
    loopless := ⟨fun x h => by obtain ⟨m, hm⟩ := h.exists; exact (gs' m).loopless.irrefl x hm⟩
  }
  have hL : L.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := L.is3Clique_iff.mp ht
    obtain ⟨m, he⟩ := (hxy.and (hxz.and hyz)).exists
    exact htri' m {x,y,z} ((gs' m).is3Clique_triple_iff.mpr he)
  obtain ⟨a, ha, hp, hi⟩ := hyp L hL
  let sm (S : Finset (Fin k)) := ∑ i ∈ S, a i
  have hb : ∀ᶠ m in u, ∀ S : Finset (Fin k), sm S ≤ N m := by
    apply eventually_all.mpr
    intro S
    have h : ∀ᶠ m : ℕ in atTop, sm S ≤ m := eventually_ge_atTop (sm S)
    exact (h.filter_mono (Ultrafilter.of_le _)).mono fun m hm => by
      have := (hN m).1
      omega
  have he : ∀ᶠ m in u, ∀ S T : Finset (Fin k), S.Nonempty → T.Nonempty →
      sm S ≠ sm T → ¬ (gs' m).Adj (sm S) (sm T) := by
    apply eventually_all.mpr
    intro S
    apply eventually_all.mpr
    intro T
    by_cases h : S.Nonempty ∧ T.Nonempty ∧ sm S ≠ sm T
    · have hn : ¬ ∀ᶠ m in u, (gs' m).Adj (sm S) (sm T) := hi S T h.1 h.2.1 h.2.2
      exact (u.eventually_not.mpr hn).mono fun m hm _ _ _ => hm
    · exact Eventually.of_forall fun _ hs ht hn => (h ⟨hs, ht, hn⟩).elim
  obtain ⟨m, hm, hne⟩ := (hb.and he).exists
  let fs : Set ℕ := {x | ∃ S : Finset (Fin k), S.Nonempty ∧ x = sm S}
  have hsub : fs ⊆ Set.Icc 1 (N m) := by
    rintro x ⟨S, hS, rfl⟩
    refine ⟨?_, hm S⟩
    obtain ⟨i, hiS⟩ := hS
    induction S using Finset.induction_on with
    | empty => simp at hiS
    | @insert x S hx _ =>
      change 1 ≤ ∑ j ∈ insert x S, a j
      rw [Finset.sum_insert hx]
      have := hp x
      omega
  apply hbad m
  refine ⟨a, ha, Subtype.val ⁻¹' fs, ?_, ?_⟩
  · apply (gs m).isIndepSet_iff.mpr
    intro x hx y hy hxy hAdj
    obtain ⟨S, hS, hs⟩ := hx
    obtain ⟨T, hT, ht⟩ := hy
    have hxy' : sm S ≠ sm T := by
      intro eqn
      exact hxy (Subtype.ext (hs.trans (eqn.trans ht.symm)))
    apply hne S T hS hT hxy'
    rw [← hs, ← ht]
    exact SimpleGraph.map_adj_apply.mpr hAdj
  · change Subtype.val '' (Subtype.val ⁻¹' fs : Set (Set.Icc 1 (N m))) = fs
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩

end Erdos895Compactness

/-! A positive shift-invariant-in-law quantifier from an additive idempotent
ultrafilter. No invariance under individual translations is assumed. -/

namespace Erdos895Ultrafilter

open Filter



private theorem existsPositiveIdempotent :
    ∃ u : Ultrafilter ℕ+, (Ultrafilter.add (M := ℕ+)).add u u = u := by
  obtain ⟨u, hu, _⟩ :=
    Hindman.exists_idempotent_ultrafilter_le_FS (Stream'.const (1 : ℕ+))
  exact ⟨u, hu⟩

private noncomputable def u : Ultrafilter ℕ+ :=
  Classical.choose existsPositiveIdempotent

private theorem u_add : (Ultrafilter.add (M := ℕ+)).add u u = u :=
  Classical.choose_spec existsPositiveIdempotent

/-- Eventual truth after pushing an additive idempotent on the positive
integers forward along the inclusion into all natural numbers. -/
def Q (P : ℕ → Prop) : Prop := ∀ᶠ (x : ℕ+) in u, P (x : ℕ)

theorem qall (P : ℕ → Prop) (h : ∀ t, P t) : Q P :=
  Filter.Eventually.of_forall fun x => h x

theorem qconst (P : Prop) : Q (fun _ => P) ↔ P :=
  Filter.eventually_const

theorem qor (P R : ℕ → Prop) : Q (fun t => P t ∨ R t) ↔ Q P ∨ Q R :=
  Ultrafilter.eventually_or

theorem qand (P R : ℕ → Prop) : Q (fun t => P t ∧ R t) ↔ Q P ∧ Q R :=
  Filter.eventually_and

theorem qnot (P : ℕ → Prop) : Q (fun t => ¬ P t) ↔ ¬ Q P :=
  Ultrafilter.eventually_not

theorem qmono (P R : ℕ → Prop) (h : ∀ t, P t → R t) (hp : Q P) : Q R :=
  Filter.Eventually.mono hp fun x hx => h x hx

theorem qexists (P : ℕ → Prop) (h : Q P) : ∃ t, P t := by
  obtain ⟨x, hx⟩ := Filter.Eventually.exists h
  exact ⟨(x : ℕ), hx⟩

/-- Nested quantification of a sum equals a single quantifier. -/
theorem qadd (P : ℕ → Prop) : Q (fun x => Q (fun y => P (x + y))) ↔ Q P := by
  change (∀ᶠ (x : ℕ+) in u, ∀ᶠ (y : ℕ+) in u, P (((x + y : ℕ+) : ℕ))) ↔ ∀ᶠ (x : ℕ+) in u, P (x : ℕ)
  rw [← Ultrafilter.eventually_add u u (fun z : ℕ+ => P (z : ℕ))]
  change (∀ᶠ (z : ℕ+) in ((Ultrafilter.add (M := ℕ+)).add u u), P (z : ℕ)) ↔ _
  rw [u_add]

theorem qpositive : Q (fun x => 0 < x) :=
  Filter.Eventually.of_forall fun x : ℕ+ => x.2

theorem qtail (b : ℕ) : Q (fun x => b < x) := by
  induction b with
  | zero => exact qpositive
  | succ b ih =>
    apply (qadd (fun t => b + 1 < t)).mp
    refine qmono _ _ (fun x hx => ?_) ih
    exact qmono _ _ (fun y hy => by omega) qpositive

theorem qcofinite (P : ℕ → Prop) (h : ∀ᶠ x in Filter.cofinite, P x) : Q P := by
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h
  obtain ⟨b, hb⟩ := h
  exact qmono _ _ (fun t ht => hb t (Nat.le_of_lt ht)) (qtail b)

end Erdos895Ultrafilter
open Filter
open scoped BigOperators

namespace Erdos895Verification

private theorem infiniteGraph (Q : (Nat → Prop) → Prop)
    (large : Erdos895Extract.LargeQuantifier Q)
    (qall : ∀ P, (∀ t, P t) → Q P)
    (qconst : ∀ P : Prop, Q (fun _ => P) ↔ P)
    (qor : ∀ U V, Q (fun t => U t ∨ V t) ↔ Q U ∨ Q V)
    (qadd : ∀ H, Q (fun x => Q (fun y => H (x+y))) ↔ Q H)
    (k : ℕ) : Erdos895Compactness.InfiniteAssertion k := by
  classical
  intro G hG
  let H : Erdos895Words.Pred := fun s => ¬ G.Adj s.1 s.2
  have cover (x y z : ℕ) : H (x,y) ∨ H (x,z) ∨ H (y,z) := by
    by_cases hxy : G.Adj x y
    · by_cases hxz : G.Adj x z
      · exact Or.inr (Or.inr (fun hyz =>
          hG {x,y,z} (G.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)))
      · exact Or.inr (Or.inl hxz)
    · exact Or.inl hxy
  have pairwise (S T : Finset (Fin k)) (hs : S.Nonempty) (ht : T.Nonempty) (hne : S ≠ T) :
      Erdos895Extract.Typical Q k
        (fun a => ¬G.Adj (∑ i ∈ S, a i) (∑ i ∈ T, a i)) := by
    apply Erdos895Words.finset_pairs_typical Q (Erdos895Extract.Typical Q)
      (fun _ => Iff.rfl) (fun _ _ => Iff.rfl) qconst
      (Erdos895Triangle.op Q) _ (Erdos895Triangle.op_idempotent Q qadd)
      H _ S T hs ht hne
    · intro u F z
      rcases z with ⟨x,y⟩
      cases u <;> simp [Erdos895Triangle.op, Erdos895Triangle.shift,
        Erdos895Words.dx, Erdos895Words.dy]
    · exact Erdos895Triangle.reduced_nonedge Q qall
        qconst qor qadd H cover
  obtain ⟨a, inc, pos, ind⟩ := Erdos895Extract.extract_finset_sums large G.Adj pairwise
  refine ⟨a, inc, pos, fun S T hs ht hn => ind S T hs ht ?_⟩
  intro heq
  exact hn (congrArg (fun s : Finset (Fin k) => ∑ i ∈ s, a i) heq)

private theorem largePositive : Erdos895Extract.LargeQuantifier Erdos895Ultrafilter.Q where
    true_mem := Erdos895Ultrafilter.qall _ (fun _ => True.intro)
    mono := fun {A B} => Erdos895Ultrafilter.qmono A B
    inter := fun {A B} ha hb => (Erdos895Ultrafilter.qand A B).2 ⟨ha,hb⟩
    witness := fun {A} => Erdos895Ultrafilter.qexists A
    tail := Erdos895Ultrafilter.qtail

theorem hindman :
    ∀ k : ℕ, ∀ᶠ n in atTop, ∀ G : SimpleGraph (Set.Icc 1 n), G.CliqueFree 3 →
      ∃ a : Fin k → ℕ, StrictMono a ∧ ∃ I : Set (Set.Icc 1 n), G.IsIndepSet I ∧
        Subtype.val '' I = {m | ∃ S : Finset (Fin k), S.Nonempty ∧ m = ∑ i ∈ S, a i} :=
  fun k => Erdos895Compactness.finite_of_infinite k (infiniteGraph Erdos895Ultrafilter.Q
    largePositive Erdos895Ultrafilter.qall Erdos895Ultrafilter.qconst Erdos895Ultrafilter.qor
    Erdos895Ultrafilter.qadd k)

end Erdos895Verification

theorem OMA.solution : type_of% @Erdos895.erdos_895.variants.hindman := Erdos895Verification.hindman
