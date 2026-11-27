import FormalConjectures.ErdosProblems.«473»
import Mathlib.Tactic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Basic

/- A boundary consists of disjoint prime-sum paths whose endpoints occupy the top of a prefix. Two reflection primes add paths and three reflection primes join them. Strong induction on the prefix size ends in an explicitly certified matching. For large prefixes the needed prime clusters follow from the ordinary prime count on (33N/34, N], bounded using a factorial ratio and an interval sieve. -/

section

namespace Erdos473Shell

/-- The strand starting at index r, with k further steps after its first pair. -/
def strand (L t d r : ℕ) : ℕ → List ℕ
  | 0 => [L + 2 * r + 1, L + 2 * (t - r)]
  | k + 1 => [L + 2 * r + 1, L + 2 * (t - r)] ++ strand L t d (r + d) k

theorem strand_mem (L t d r k x : ℕ) :
    x ∈ strand L t d r k ↔ ∃ j ≤ k,
      x = L + 2 * (r + j * d) + 1 ∨ x = L + 2 * (t - (r + j * d)) := by
  induction k generalizing r with
  | zero => simp [strand]
  | succ k ih =>
    simp only [strand, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, ih]
    constructor
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact ⟨0, by omega, by simpa using hx⟩
      · refine ⟨j + 1, by omega, ?_⟩
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx
    · rintro ⟨j, hj, hx⟩
      cases j with
      | zero => exact Or.inl (by simpa using hx)
      | succ j =>
        exact Or.inr ⟨j, by omega, by
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx⟩

theorem strand_head (L t d r k : ℕ) :
    (strand L t d r k).head? = some (L + 2 * r + 1) := by
  cases k <;> simp [strand]

theorem strand_last (L t d r k : ℕ) :
    (strand L t d r k).getLast? = some (L + 2 * (t - (r + k * d))) := by
  induction k generalizing r with
  | zero => simp [strand]
  | succ k ih =>
    rw [strand, List.getLast?_append, ih]
    simp only [Option.some_or, Option.some.injEq, Nat.succ_mul]
    omega

theorem strand_nodup (L t d r k : ℕ) (hd : 0 < d) (ht : r + k * d < t) :
    (strand L t d r k).Nodup := by
  induction k generalizing r with
  | zero =>
    simp only [strand, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, not_false_eq_true, and_self, and_true]
    omega
  | succ k ih =>
    rw [Nat.succ_mul] at ht
    rw [strand, List.nodup_append]
    refine ⟨by simp; omega, ih (r+d) (by omega), ?_⟩
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨j, hj, hy⟩ := (strand_mem ..).mp hy
    have hjd : j * d ≤ k * d := Nat.mul_le_mul_right _ hj
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega

theorem strand_chain (L t d r k : ℕ) (ht : r + k * d < t)
    (hp : (2 * L + 2 * t + 1).Prime)
    (hq : (2 * L + 2 * t + 1 + 2 * d).Prime) :
    (strand L t d r k).IsChain (fun a b => (a + b).Prime) := by
  induction k generalizing r with
  | zero =>
    rw [strand, List.isChain_pair]
    convert hp using 1
    simp at ht
    omega
  | succ k ih =>
    rw [Nat.succ_mul] at ht
    rw [strand, List.isChain_append, List.isChain_pair]
    refine ⟨?_, ih (r+d) (by omega), ?_⟩
    · convert hp using 1
      omega
    · intro a ha b hb
      rw [strand_head] at hb
      change some (L + 2 * (t - r)) = some a at ha
      simp only [Option.mem_def, Option.some.injEq] at ha hb
      convert hq using 1
      omega

/-- The complete shell splits into one strand for each residue modulo d. -/
def shellStrand (L t d r : ℕ) : List ℕ :=
  strand L t d r ((t - 1 - r) / d)

theorem shell_index {t d r i : ℕ} (hd : 0 < d) (hr : r < d) (hi : i < t) :
    (∃ j ≤ (t - 1 - r) / d, i = r + j * d) ↔ i % d = r := by
  constructor
  · rintro ⟨j, _, rfl⟩
    simp [Nat.mod_eq_of_lt hr]
  · intro h
    have hdiv := Nat.mod_add_div i d
    rw [h, Nat.mul_comm] at hdiv
    exact ⟨i / d, (Nat.le_div_iff_mul_le hd).mpr (by omega), hdiv.symm⟩

theorem shell_bound {t d r : ℕ} (hr : r < t) :
    r + (t-1-r) / d * d < t := by
  have h := Nat.div_mul_le_self (t-1-r) d
  omega

theorem shell_odd_mem {L t d r i : ℕ} (hd : 0 < d) (hr : r < d) (hi : i < t) :
    L + 2 * i + 1 ∈ shellStrand L t d r ↔ i % d = r := by
  rw [shellStrand, strand_mem, ← shell_index hd hr hi]
  constructor
  · rintro ⟨j, hj, h | h⟩ <;> exact ⟨j, hj, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, Or.inl rfl⟩

theorem shell_even_mem {L t d r i : ℕ} (hd : 0 < d) (hdt : d ≤ t) (hr : r < d)
    (hi : i < t) :
    L + 2 * (t - i) ∈ shellStrand L t d r ↔ i % d = r := by
  rw [shellStrand, strand_mem, ← shell_index hd hr hi]
  constructor
  · rintro ⟨j, hj, h | h⟩
    · omega
    · have hbound := shell_bound (d := d) (r := r) (t := t) (by omega)
      have hjd := Nat.mul_le_mul_right d hj
      exact ⟨j, hj, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, Or.inr rfl⟩

theorem shell_endpoints {L t d r : ℕ} (hr : r < t) :
    (shellStrand L t d r).head? = some (L + 2 * r + 1) ∧
      (shellStrand L t d r).getLast? = some (L + 2 + 2 * ((t - 1 - r) % d)) := by
  refine ⟨strand_head .., ?_⟩
  rw [shellStrand, strand_last]
  have h := Nat.mod_add_div (t-1-r) d
  rw [Nat.mul_comm] at h
  congr 1
  omega

theorem shell_properties {L t d : ℕ} (hd : 0 < d) (hdt : d ≤ t)
    (hp : (2 * L + 2 * t + 1).Prime) (hq : (2 * L + 2 * t + 1 + 2 * d).Prime)
    (r : Fin d) :
    (shellStrand L t d r).Nodup ∧
      (shellStrand L t d r).IsChain (fun a b => (a+b).Prime) := by
  have hr : r.val < t := lt_of_lt_of_le r.isLt hdt
  exact ⟨strand_nodup _ _ _ _ _ hd (shell_bound hr), strand_chain _ _ _ _ _ (shell_bound hr) hp hq⟩

theorem shell_mem_bounds {L t d r x : ℕ} (hr : r < t) (hx : x ∈ shellStrand L t d r) :
    L < x ∧ x ≤ L + 2 * t := by
  obtain ⟨j, hj, hx⟩ := (strand_mem ..).mp hx
  have hbound := shell_bound (d := d) hr
  have hjd := Nat.mul_le_mul_right d hj
  rcases hx with hx | hx <;> omega

theorem shell_unique {L t d x : ℕ} (hd : 0 < d) (hdt : d ≤ t) (hx : L < x ∧ x ≤ L + 2*t) :
    ∃! r : Fin d, x ∈ shellStrand L t d r := by
  by_cases ho : (x-L) % 2 = 1
  · let i := (x-L-1)/2
    have hi : i < t := by dsimp [i]; omega
    have hx' : x = L + 2 * i + 1 := by dsimp [i]; omega
    rw [hx']
    refine ⟨⟨i%d, Nat.mod_lt _ hd⟩, (shell_odd_mem hd (Nat.mod_lt _ hd) hi).mpr rfl, ?_⟩
    intro s hs
    exact Fin.ext ((shell_odd_mem hd s.isLt hi).mp hs).symm
  · let i := t - (x-L)/2
    have hi : i < t := by dsimp [i]; omega
    have hx' : x = L + 2 * (t - i) := by dsimp [i]; omega
    rw [hx']
    refine ⟨⟨i%d, Nat.mod_lt _ hd⟩, (shell_even_mem hd hdt (Nat.mod_lt _ hd) hi).mpr rfl, ?_⟩
    intro s hs
    exact Fin.ext ((shell_even_mem hd hdt s.isLt hi).mp hs).symm

/-- Two prime sums at distance 2d partition the whole interval into d disjoint paths.
The displayed endpoints all belong to the first 2d positions of the interval. -/
theorem shell_decomposition (L t d : ℕ) (hd : 0 < d) (hdt : d ≤ t)
    (hp : (2 * L + 2 * t + 1).Prime) (hq : (2 * L + 2 * t + 1 + 2 * d).Prime) :
    ∃ paths : Fin d → List ℕ,
      (∀ r : Fin d,
        (paths r).Nodup ∧ (paths r).IsChain (fun a b => (a+b).Prime) ∧
        (paths r).head? = some (L + 2*r + 1) ∧
        (paths r).getLast? = some (L + 2 + 2 * ((t - 1 - r) % d)) ∧
        ∀ x ∈ paths r, L < x ∧ x ≤ L + 2*t) ∧
      ∀ x, L < x ∧ x ≤ L + 2*t → ∃! r, x ∈ paths r := by
  refine ⟨fun r => shellStrand L t d r, ?_, fun _ => shell_unique hd hdt⟩
  intro r
  have hr := lt_of_lt_of_le r.isLt hdt
  obtain ⟨hnd, hchain⟩ := shell_properties hd hdt hp hq r
  obtain ⟨hfirst, hlast⟩ := shell_endpoints (L := L) (d := d) hr
  exact ⟨hnd, hchain, hfirst, hlast, fun _ => shell_mem_bounds hr⟩

end Erdos473Shell

namespace Erdos473CoinPaths
abbrev PathAt (n : ℕ) := ∃ e : Fin n ≃ Fin n, ∀ k : Fin n, ∀ h : k.val+1 < n,
  ((e k).val + 1 + ((e ⟨k.val+1,h⟩).val + 1)).Prime

abbrev ListPath (n : ℕ) := ∃ l : List ℕ, l.Nodup ∧
  (∀ x, x ∈ l ↔ 1 ≤ x ∧ x ≤ n) ∧ l.IsChain (fun x y => (x+y).Prime)

end Erdos473CoinPaths

namespace Erdos473Twin
theorem perm_of_list (n : ℕ) (l : List ℕ) (hnd : l.Nodup) (hmem : ∀ x, x ∈ l ↔ 1 ≤ x ∧ x ≤ n)
    (hch : l.IsChain (fun a b => (a + b).Prime)) :
    ∃ a : Fin n ≃ Fin n, ∀ k : Fin n, ∀ h : k.val + 1 < n,
      ((a k).val + 1 + ((a ⟨k.val + 1, h⟩).val + 1)).Prime := by
  have hlen : l.length = n := by
    have h1 : l.toFinset = Finset.Icc 1 n := by
      ext x
      simp [hmem]
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Nat.card_Icc] at h2
    omega
  subst hlen
  have hpos : ∀ i (hi : i < l.length), 1 ≤ l[i] ∧ l[i] ≤ l.length :=
    fun i hi => (hmem _).mp (List.getElem_mem hi)
  have hinj : Function.Injective
      (fun k : Fin l.length => (⟨l[k.val] - 1, by have := hpos k.val k.isLt; omega⟩ :
        Fin l.length)) := by
    intro i j hij
    have h := congrArg Fin.val hij
    simp only at h
    have hi := hpos i.val i.isLt
    have hj := hpos j.val j.isLt
    have hij' : l[i.val] = l[j.val] := by omega
    exact Fin.ext (hnd.getElem_inj_iff.mp hij')
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), ?_⟩
  intro k h
  have hc := (List.isChain_iff_getElem.mp hch) k.val h
  have hk := hpos k.val k.isLt
  have hk1 := hpos (k.val + 1) h
  show (l[k.val] - 1 + 1 + (l[k.val + 1] - 1 + 1)).Prime
  rw [Nat.sub_add_cancel hk.1, Nat.sub_add_cancel hk1.1]
  exact hc

end Erdos473Twin

end

section

/- Contract disjoint prescribed top links against a disjoint matching of central shell strands. -/

namespace Erdos473MatchingTransfer

variable {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C] [Fintype C]

/-- Left and right preimages of the two ends of each central strand. -/
structure Interface (A B C : Type) where
  top : A ≃ B
  left : C ↪ A
  right : C ↪ B
  apart : ∀ i j, top (left i) ≠ right j

abbrev Open {X : Type} (f : C ↪ X) := {x : X // ∀ i, x≠f i}

namespace Interface

variable (s : Interface A B C)

open Classical in
noncomputable def closeRight (b : B) : Option C :=
  if h : ∃ c, b=s.right c then some h.choose else none

lemma closeRight_some {b : B} {c : C} : s.closeRight b = some c ↔ b=s.right c := by
  classical
  unfold closeRight
  split_ifs with h
  · constructor
    · intro e; cases Option.some.inj e; exact h.choose_spec
    · intro e; rw [←s.right.injective (h.choose_spec.symm.trans e)]
  · simp [show ¬ _ by exact fun e => h ⟨c,e⟩]

lemma closeRight_none {b : B} : s.closeRight b = none ↔ ∀ c, b≠s.right c := by
  classical
  simp [closeRight]

open Classical in
noncomputable def closeLeft (a : A) : Option C :=
  if h : ∃ c, a=s.left c then some h.choose else none

lemma closeLeft_some {a : A} {c : C} : s.closeLeft a=some c ↔ a=s.left c := by
  classical
  unfold closeLeft
  split_ifs with h
  · constructor
    · intro e; cases Option.some.inj e; exact h.choose_spec
    · intro e; rw [←s.left.injective (h.choose_spec.symm.trans e)]
  · simp [show ¬ _ by exact fun e => h ⟨c,e⟩]

lemma closeLeft_none {a : A} : s.closeLeft a=none ↔ ∀ c, a≠s.left c := by
  classical
  simp [closeLeft]

noncomputable def next (i : Open s.left) : Open s.right :=
  match h : s.closeRight (s.top i.val) with
  | none => ⟨s.top i.val,s.closeRight_none.mp h⟩
  | some c => ⟨s.top (s.left c),s.apart c⟩

noncomputable def prev (j : Open s.right) : Open s.left :=
  match h : s.closeLeft (s.top.symm j.val) with
  | none => ⟨s.top.symm j.val,s.closeLeft_none.mp h⟩
  | some c => ⟨s.top.symm (s.right c),fun t he => s.apart t c (by rw [←he]; simp)⟩

lemma next_none (i : Open s.left) (h : s.closeRight (s.top i.val)=none) :
    (s.next i).val=s.top i.val := by unfold next; split <;> simp_all

lemma next_some (i : Open s.left) (c : C) (h : s.closeRight (s.top i.val)=some c) :
    (s.next i).val=s.top (s.left c) := by unfold next; split <;> simp_all

lemma prev_none (j : Open s.right) (h : s.closeLeft (s.top.symm j.val)=none) :
    (s.prev j).val=s.top.symm j.val := by unfold prev; split <;> simp_all

lemma prev_some (j : Open s.right) (c : C) (h : s.closeLeft (s.top.symm j.val)=some c) :
    (s.prev j).val=s.top.symm (s.right c) := by unfold prev; split <;> simp_all

theorem next_prev (j : Open s.right) : s.next (s.prev j)=j := by
  apply Subtype.ext
  cases hh : s.closeLeft (s.top.symm j.val) with
  | none =>
    have pv := s.prev_none j hh
    rw [s.next_none (s.prev j) (by rw [pv]; simpa using s.closeRight_none.mpr j.property),pv]
    simp
  | some c =>
    have pv := s.prev_some j c hh
    have he := s.closeLeft_some.mp hh
    rw [s.next_some (s.prev j) c (by rw [pv]; simpa using s.closeRight_some.mpr (rfl : s.right c=s.right c)),←he]
    simp

theorem prev_next (i : Open s.left) : s.prev (s.next i)=i := by
  apply Subtype.ext
  cases hh : s.closeRight (s.top i.val) with
  | none =>
    have nv := s.next_none i hh
    rw [s.prev_none (s.next i) (by rw [nv]; simpa using s.closeLeft_none.mpr i.property),nv]
    simp
  | some c =>
    have nv := s.next_some i c hh
    have he := s.closeRight_some.mp hh
    rw [s.prev_some (s.next i) c (by rw [nv]; simpa using s.closeLeft_some.mpr (rfl : s.left c=s.left c)),←he]
    simp

noncomputable def pairing : Open s.left ≃ Open s.right where
  toFun := s.next
  invFun := s.prev
  left_inv := s.prev_next
  right_inv := s.next_prev

/-- Atoms representing actual free terminals, old virtual words, and central genuine path words. -/
inductive Piece
  | start (i : Open s.left)
  | old (i : A)
  | central (c : C)
  | finish (j : Open s.right)
  deriving DecidableEq

open Piece in
noncomputable def trace (i : Open s.left) : List s.Piece :=
  match s.closeRight (s.top i.val) with
  | none => [start i,old i.val,finish (s.next i)]
  | some c => [start i,old i.val,central c,old (s.left c),finish (s.next i)]

lemma trace_nodup (i : Open s.left) : (s.trace i).Nodup := by
  unfold trace
  split
  · simp
  · simp [i.property]

/-- Every old prescribed word and every central strand occurs on exactly one new path. -/
theorem unique_piece (p : s.Piece) : ∃! i, p∈s.trace i := by
  classical
  cases p with
  | start i =>
    refine ⟨i,by dsimp only; unfold trace; split <;> simp,?_⟩
    intro j hj
    unfold trace at hj
    split at hj <;> simpa [eq_comm] using hj
  | finish b =>
    refine ⟨s.prev b,by dsimp only; unfold trace; split <;> simp [s.next_prev],?_⟩
    intro j hj
    have e : b=s.next j := by
      unfold trace at hj
      split at hj <;> simpa using hj
    rw [e,s.prev_next]
  | central c =>
    let i : Open s.left := ⟨s.top.symm (s.right c),fun t he => s.apart t c (by rw [←he]; simp)⟩
    have hit : s.closeRight (s.top i.val) = some c := s.closeRight_some.mpr (by simp [i])
    refine ⟨i,by simp [trace,hit],?_⟩
    intro j hj
    unfold trace at hj
    split at hj
    next => simp at hj
    next c' h =>
      have e : c=c' := by simpa using hj
      subst c'
      apply Subtype.ext
      exact s.top.injective (by simpa [i] using s.closeRight_some.mp h)
  | old a =>
    by_cases ha : ∃ c, a=s.left c
    · obtain ⟨c,rfl⟩ := ha
      let i : Open s.left := ⟨s.top.symm (s.right c),fun t he => s.apart t c (by rw [←he]; simp)⟩
      have hit : s.closeRight (s.top i.val)=some c := s.closeRight_some.mpr (by simp [i])
      refine ⟨i,by simp [trace,hit],?_⟩
      intro j hj
      unfold trace at hj
      split at hj
      next => simp [Ne.symm (j.property c)] at hj
      next c' h =>
        have e : c=c' := by simpa [Ne.symm (j.property c),Function.Embedding.apply_eq_iff_eq] using hj
        subst c'
        apply Subtype.ext
        exact s.top.injective (by simpa [i] using s.closeRight_some.mp h)
    · let i : Open s.left := ⟨a,fun c e => ha ⟨c,e⟩⟩
      refine ⟨i,by dsimp only; unfold trace; split <;> simp [i],?_⟩
      intro j hj
      apply Subtype.ext
      unfold trace at hj
      split at hj
      next => simpa [i,eq_comm] using hj
      next c h =>
        have no : a≠s.left c := i.property c
        exact (show a=j.val by simpa [no] using hj).symm

/-- A transition between two words is justified by their actual endpoint labels. -/
def Link (x y : List ℕ) : Prop :=
  ∀ a ∈ x.getLast?, ∀ b ∈ y.head?, (a+b).Prime

/-- Disjoint constituent words and the four sorts of prime-sum joins. -/
structure Words (s : Interface A B C) where
  word : s.Piece → List ℕ
  nonempty : ∀ p, word p ≠ []
  simple : ∀ p, (word p).Nodup
  separate : ∀ p q, p≠q → (word p).Disjoint (word q)
  edges : ∀ p, (word p).IsChain (fun x y => (x+y).Prime)
  firstEdge : ∀ i : Open s.left, Link (word (.start i)) (word (.old i.val))
  directEdge : ∀ i : Open s.left, s.closeRight (s.top i.val)=none →
    Link (word (.old i.val)) (word (.finish (s.next i)))
  enterEdge : ∀ (i : Open s.left) (c : C), s.closeRight (s.top i.val)=some c →
    Link (word (.old i.val)) (word (.central c))
  exitEdge : ∀ c, Link (word (.central c)) (word (.old (s.left c)))
  lastEdge : ∀ (i : Open s.left) (c : C), s.closeRight (s.top i.val)=some c →
    Link (word (.old (s.left c))) (word (.finish (s.next i)))

variable {s}

noncomputable def Words.row (w : Words s) (i : Open s.left) : List ℕ :=
  (s.trace i).flatMap w.word

theorem Words.row_nodup (w : Words s) (i : Open s.left) : (w.row i).Nodup :=
  List.nodup_flatMap.mpr ⟨fun p _ => w.simple p,
    (s.trace_nodup i).imp fun {p q} h => w.separate p q h⟩

theorem Words.row_chain (w : Words s) (i : Open s.left) :
    (w.row i).IsChain (fun x y => (x+y).Prime) := by
  change (((s.trace i).map w.word).flatten).IsChain _
  apply (List.isChain_flatten (by
    intro he
    obtain ⟨p,_,eq⟩ := List.mem_map.mp he
    exact w.nonempty p eq)).mpr
  constructor
  · intro l hl
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hl
    exact w.edges p
  · change ((s.trace i).map w.word).IsChain Link
    unfold trace
    split
    next h => simpa using And.intro (w.firstEdge i) (w.directEdge i h)
    next c h => simpa using And.intro (w.firstEdge i) ⟨w.enterEdge i c h,w.exitEdge c,w.lastEdge i c h⟩

theorem Words.row_head (w : Words s) (i : Open s.left) :
    (w.row i).head? = (w.word (.start i)).head? := by
  cases e : w.word (.start i) with
  | nil => exact False.elim (w.nonempty _ e)
  | cons x xs => unfold row trace; split <;> simp [e]

theorem Words.row_last (w : Words s) (i : Open s.left) :
    (w.row i).getLast? = (w.word (.finish (s.next i))).getLast? := by
  cases e : (w.word (.finish (s.next i))).getLast? with
  | none => exact False.elim (w.nonempty _ (List.getLast?_eq_none_iff.mp e))
  | some x => unfold row trace; split <;> simp [List.getLast?_append,e]

/-- The realized contraction covers all constituent vertices exactly once. -/
theorem Words.rows_cover (w : Words s) (x : ℕ) (hx : ∃ p, x∈w.word p) :
    ∃! i, x∈w.row i := by
  obtain ⟨p,hp⟩ := hx
  obtain ⟨i,hi,huniq⟩ := s.unique_piece p
  refine ⟨i,List.mem_flatMap.mpr ⟨p,hi,hp⟩,?_⟩
  intro j hj
  obtain ⟨q,hq,hxq⟩ := List.mem_flatMap.mp hj
  have e : p=q := by
    by_contra ne
    exact w.separate p q ne hp hxq
  subst q
  exact huniq j hq

end Interface

end Erdos473MatchingTransfer

end

section

/- The three-center tile repairing the prime-shell contraction. -/

namespace Erdos473RepairPermutation

def tile (k d e : ℕ) (hk : d+e≤k) : Fin k ≃ Fin k where
  toFun i := ⟨if i.val<k-d-e then i.val else if i.val<k-e then i.val+e else i.val-d, by
    split_ifs <;> omega⟩
  invFun j := ⟨if j.val<k-d-e then j.val else if j.val<k-d then j.val+d else j.val-e, by
    split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    split <;> repeat' split
    all_goals omega
  right_inv j := by
    apply Fin.ext
    dsimp
    split <;> repeat' split
    all_goals omega

def high {k d : ℕ} (h : d≤k) (i : Fin d) : Fin k := ⟨k-d+i.val,by omega⟩

lemma tile_preimage {k d e : ℕ} (hk : d+e≤k) (i : Fin d) :
    ((tile k d e hk).symm (high (by omega) i)).val=k-d-e+i.val := by
  change (if k-d+i.val<k-d-e then k-d+i.val else if k-d+i.val<k-d then k-d+i.val+d else k-d+i.val-e) = _
  split_ifs <;> omega

/-- Every edge of the repair tile is one of the three available prime reflections. -/
theorem left_edges {n u k d e : ℕ} (hn : 2*k≤n) (hk : d+e≤k)
    (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime) (r : (n+u+1+2*d+2*e).Prime) (i : Fin k) :
    (n-2*i.val+(u+1+2*d+2*((tile k d e hk) i).val)).Prime := by
  change (n-2*i.val+(u+1+2*d+2*(if i.val<k-d-e then i.val else if i.val<k-e then i.val+e else i.val-d))).Prime
  split
  · convert q using 1 <;> omega
  · split
    · convert r using 1 <;> omega
    · convert p using 1 <;> omega

lemma right_edges {n u k d : ℕ} (hn : 2*k≤n) (q : (n+u+1+2*d).Prime) (j : Fin k) :
    (n-(2*j.val+1)+(u+2+2*d+2*j.val)).Prime := by
  convert q using 1 <;> omega

/-- Among d+1 disjoint options, one avoids every mate of the d fixed terminals. -/
theorem avoiding_repair {k d : ℕ} (e : Fin (d+1) → ℕ) (bound : ∀ a, d+e a≤k)
    (sep : ∀ a b, a<b → e a+d≤e b) (M : Fin k ≃ Fin k) :
    ∃ a, ∀ i j : Fin d, M ((tile k d (e a) (bound a)).symm (high (by have := bound a; omega) i))
      ≠ high (by have := bound a; omega) j := by
  classical
  by_contra! h
  choose i j eq using h
  have inj : Function.Injective j := by
    intro a b eqj
    have he : ((tile k d (e a) (bound a)).symm (high (by have := bound a; omega) (i a))).val =
        ((tile k d (e b) (bound b)).symm (high (by have := bound b; omega) (i b))).val := by
      apply congrArg Fin.val
      apply M.injective
      rw [eq a,eq b,eqj]
    rw [tile_preimage,tile_preimage] at he
    have ha := bound a
    have hb := bound b
    have ia := (i a).isLt
    have ib := (i b).isLt
    rcases lt_trichotomy a b with ab | ab | ba
    · have s := sep a b ab; omega
    · exact ab
    · have s := sep b a ba; omega
  have z := Fintype.card_le_of_injective j inj
  simp at z

end Erdos473RepairPermutation

end

section

/- Geometric realization and iteration interface for the repaired shell contraction. -/

namespace Erdos473CleanShell

open Erdos473MatchingTransfer Erdos473RepairPermutation

/-- Paths occupying everything above the unoccupied prefix, with the prescribed top endpoints. -/
structure Boundary (N n k : ℕ) where
  pairing : Fin k ≃ Fin k
  word : Fin k → List ℕ
  head : ∀ i, (word i).head? = some (n-2*i.val)
  tail : ∀ i, (word i).getLast? = some (n-(2*(pairing i).val+1))
  simple : ∀ i, (word i).Nodup
  edges : ∀ i, (word i).IsChain (fun x y => (x+y).Prime)
  disjoint : ∀ i j, i≠j → (word i).Disjoint (word j)
  covers : ∀ x, (∃ i, x∈word i) ↔ n-2*k<x ∧ x≤N

def low {k d : ℕ} (i : Fin (k-d)) : Fin k := ⟨i.val,by omega⟩

def highEmb {k d : ℕ} (h : d≤k) : Fin d ↪ Fin k where
  toFun := high h
  inj' := fun x y e => by apply Fin.ext; have z := congrArg Fin.val e; dsimp [high] at z; omega

/-- Arrange the high targets of one parity by an arbitrary permutation of the central labels. -/
noncomputable def coords {k d : ℕ} (hd : d≤k) (π ρ M : Equiv.Perm (Fin k)) (σ : Equiv.Perm (Fin d))
    (apart : ∀ r j, M (π.symm (high hd r))≠ρ.symm (high hd j)) : Interface (Fin k) (Fin k) (Fin d) where
  top := M
  left := (highEmb hd).trans π.symm.toEmbedding
  right := (σ.toEmbedding.trans (highEmb hd)).trans ρ.symm.toEmbedding
  apart i j := apart i (σ j)

section

variable {k d : ℕ} {hd : d≤k} {π ρ M : Equiv.Perm (Fin k)} {σ : Equiv.Perm (Fin d)}
  {apart : ∀ r j, M (π.symm (high hd r))≠ρ.symm (high hd j)}


lemma left_lo (i : Open (coords hd π ρ M σ apart).left) : (π i.val).val<k-d := by
  by_contra! he
  let r : Fin d := ⟨(π i.val).val-(k-d),by have := (π i.val).isLt; omega⟩
  apply i.property r
  apply π.injective
  change π i.val=π (π.symm (high hd r))
  rw [π.apply_symm_apply]
  apply Fin.ext
  dsimp [r,high]
  omega

lemma right_lo (j : Open (coords hd π ρ M σ apart).right) : (ρ j.val).val<k-d := by
  by_contra! he
  let r : Fin d := ⟨(ρ j.val).val-(k-d),by have := (ρ j.val).isLt; omega⟩
  apply j.property (σ.symm r)
  apply ρ.injective
  change ρ j.val=ρ (ρ.symm (high hd (σ (σ.symm r))))
  rw [ρ.apply_symm_apply,σ.apply_symm_apply]
  apply Fin.ext
  dsimp [r,high]
  omega

noncomputable def leftCoords : Open (coords hd π ρ M σ apart).left ≃ Fin (k-d) where
  toFun i := ⟨(π i.val).val,left_lo i⟩
  invFun i := ⟨π.symm (low i),by
    intro r e
    change π.symm (low i)=π.symm (high hd r) at e
    have z := congrArg Fin.val (π.symm.injective e)
    dsimp [low,high] at z
    omega⟩
  left_inv i := by apply Subtype.ext; exact π.symm_apply_apply i.val
  right_inv i := by
    apply Fin.ext
    change (π (π.symm (low i))).val=i.val
    rw [π.apply_symm_apply]
    rfl

noncomputable def rightCoords : Open (coords hd π ρ M σ apart).right ≃ Fin (k-d) where
  toFun j := ⟨(ρ j.val).val,right_lo j⟩
  invFun i := ⟨ρ.symm (low i),by
    intro r e
    change ρ.symm (low i)=ρ.symm (high hd (σ r)) at e
    have z := congrArg Fin.val (ρ.symm.injective e)
    dsimp [low,high] at z
    omega⟩
  left_inv i := by apply Subtype.ext; exact ρ.symm_apply_apply i.val
  right_inv i := by
    apply Fin.ext
    change (ρ (ρ.symm (low i))).val=i.val
    rw [ρ.apply_symm_apply]
    rfl

end

/-- Natural labels of the destinations after choosing a permutation for the left repairs. -/
def L (u d : ℕ) {k : ℕ} (π : Equiv.Perm (Fin k)) (i : Fin k) := u+1+2*d+2*(π i).val
def R (u d : ℕ) {k : ℕ} (ρ : Equiv.Perm (Fin k)) (j : Fin k) := u+2+2*d+2*(ρ j).val

lemma link_of {a b : ℕ} {x y : List ℕ} (ha : x.getLast?=some a) (hb : y.head?=some b)
    (pr : (a+b).Prime) : Interface.Link x y := by
  intro c hc d hd
  rw [ha] at hc
  rw [hb] at hd
  rw [Option.mem_some_iff.mp hc,Option.mem_some_iff.mp hd] at pr
  exact pr

section

variable {N n u k d : ℕ} {hd : d≤k} (π ρ : Equiv.Perm (Fin k))
  (M : Boundary N n k) (σ : Equiv.Perm (Fin d))
  (apart : ∀ r j, M.pairing (π.symm (high hd r))≠ρ.symm (high hd j))

def sw (G : Fin d → List ℕ) : (coords hd π ρ M.pairing σ apart).Piece → List ℕ
  | .start i => [L u d π i.val]
  | .old i => M.word i
  | .central c => (G c).reverse
  | .finish j => [R u d ρ j.val]

lemma left_target (r : Fin d) : L u d π ((coords hd π ρ M.pairing σ apart).left r)=u+2*k+2*r.val+1 := by
  change u+1+2*d+2*(π (π.symm (high hd r))).val=_
  rw [π.apply_symm_apply]
  dsimp [high]
  omega

lemma right_target (r : Fin d) : R u d ρ ((coords hd π ρ M.pairing σ apart).right r)=u+2*k+2+2*(σ r).val := by
  change u+2+2*d+2*(ρ (ρ.symm (high hd (σ r)))).val=_
  rw [ρ.apply_symm_apply]
  dsimp [high]
  omega

lemma left_bounds (i : Open (coords hd π ρ M.pairing σ apart).left) : u+2*d<L u d π i.val ∧ L u d π i.val≤u+2*k := by
  have h := left_lo i
  dsimp [L]
  omega

lemma right_bounds (j : Open (coords hd π ρ M.pairing σ apart).right) : u+2*d<R u d ρ j.val ∧ R u d ρ j.val≤u+2*k := by
  have h := right_lo j
  dsimp [R]
  omega

variable (G : Fin d → List ℕ)
  (gstarts : ∀ r, (G r).head?=some (u+2*k+2*r.val+1))
  (gends : ∀ r, (G r).getLast?=some (u+2*k+2+2*(σ r).val))
  (gsimple : ∀ r, (G r).Nodup) (gedges : ∀ r, (G r).IsChain (fun x y => (x+y).Prime))
  (gbounds : ∀ r x, x∈G r → u+2*k<x ∧ x≤n-2*k)
  (guniq : ∀ r s x, x∈G r → x∈G s → r=s)
  (lpr : ∀ i, (n-2*i.val+L u d π i).Prime)
  (rpr : ∀ j, (n-(2*j.val+1)+R u d ρ j).Prime)

include gbounds guniq in
private lemma inject_word (order : u+2*k≤n-2*k) (p q : (coords hd π ρ M.pairing σ apart).Piece) (x : ℕ)
    (hp : x∈sw (u:=u) π ρ M σ apart G p) (hq : x∈sw (u:=u) π ρ M σ apart G q) : p=q := by
  have freshL (i : Open (coords hd π ρ M.pairing σ apart).left) (h : x=L u d π i.val) : x≤u+2*k := h ▸ (left_bounds (u:=u) π ρ M σ apart i).2
  have freshR (j : Open (coords hd π ρ M.pairing σ apart).right) (h : x=R u d ρ j.val) : x≤u+2*k := h ▸ (right_bounds (u:=u) π ρ M σ apart j).2
  have oldB (i : Fin k) (h : x∈M.word i) : n-2*k<x := ((M.covers x).mp ⟨i,h⟩).1
  have nc (i : Fin d) (h : x∈G i) := gbounds i x h
  cases p <;> cases q <;> simp only [sw,List.mem_singleton,List.mem_reverse] at hp hq
  case start.start i j =>
    congr 1
    apply Subtype.ext
    apply π.injective
    apply Fin.ext
    dsimp [L] at hp hq
    omega
  case start.old i j => have := freshL i hp; have := oldB j hq; omega
  case start.central i j => have := freshL i hp; have := nc j hq; omega
  case start.finish i j => dsimp [L] at hp; dsimp [R] at hq; omega
  case old.start i j => have := oldB i hp; have := freshL j hq; omega
  case old.old i j =>
    congr 1
    by_contra h
    exact M.disjoint i j h hp hq
  case old.central i j => have := oldB i hp; have := nc j hq; omega
  case old.finish i j => have := oldB i hp; have := freshR j hq; omega
  case central.start i j => have := nc i hp; have := freshL j hq; omega
  case central.old i j => have := nc i hp; have := oldB j hq; omega
  case central.central i j => exact congrArg Interface.Piece.central (guniq i j x hp hq)
  case central.finish i j => have := nc i hp; have := freshR j hq; omega
  case finish.start i j => dsimp [R] at hp; dsimp [L] at hq; omega
  case finish.old i j => have := freshR i hp; have := oldB j hq; omega
  case finish.central i j => have := freshR i hp; have := nc j hq; omega
  case finish.finish i j =>
    congr 1
    apply Subtype.ext
    apply ρ.injective
    apply Fin.ext
    dsimp [R] at hp hq
    omega

noncomputable def words (order : u+2*k≤n-2*k) : Interface.Words (coords hd π ρ M.pairing σ apart) where
  word := sw (u:=u) π ρ M σ apart G
  nonempty p := by
    cases p with
    | start i => simp [sw]
    | finish j => simp [sw]
    | old i => intro e; have h := M.head i; change M.word i=[] at e; simp [e] at h
    | central r => intro e; have h := gstarts r; simp [sw] at e; simp [e] at h
  simple p := by
    cases p with
    | start i => simp [sw]
    | finish j => simp [sw]
    | old i => exact M.simple i
    | central r => simpa [sw] using gsimple r
  separate p q ne x hp hq := ne (inject_word π ρ M σ apart G gbounds guniq order p q x hp hq)
  edges p := by
    cases p with
    | start i => simp [sw]
    | finish j => simp [sw]
    | old i => exact M.edges i
    | central r =>
      change (G r).reverse.IsChain _
      rw [List.isChain_reverse]
      simpa only [Nat.add_comm] using gedges r
  firstEdge i := link_of (a:=L u d π i.val) rfl (M.head i.val) (by rw [Nat.add_comm]; exact lpr i.val)
  directEdge i h := link_of (b:=R u d ρ ((coords hd π ρ M.pairing σ apart).next i).val) (M.tail i.val) rfl (by
    change (n-(2*(M.pairing i.val).val+1)+R u d ρ ((coords hd π ρ M.pairing σ apart).next i).val).Prime
    rw [(coords hd π ρ M.pairing σ apart).next_none i h]
    exact rpr _)
  enterEdge i c h := link_of (M.tail i.val) (by simpa [sw] using gends c) (by
    have eq := (coords hd π ρ M.pairing σ apart).closeRight_some.mp h
    change M.pairing i.val=(coords hd π ρ M.pairing σ apart).right c at eq
    rw [←right_target π ρ M σ apart c,←eq]
    exact rpr _)
  exitEdge c := link_of (by simpa [sw] using gstarts c) (M.head ((coords hd π ρ M.pairing σ apart).left c)) (by
    rw [←left_target π ρ M σ apart c,Nat.add_comm]
    exact lpr _)
  lastEdge i c h := link_of (b:=R u d ρ ((coords hd π ρ M.pairing σ apart).next i).val) (M.tail ((coords hd π ρ M.pairing σ apart).left c)) rfl (by
    change (n-(2*(M.pairing ((coords hd π ρ M.pairing σ apart).left c)).val+1)+R u d ρ ((coords hd π ρ M.pairing σ apart).next i).val).Prime
    rw [(coords hd π ρ M.pairing σ apart).next_some i c h]
    exact rpr _)

include gbounds in
lemma support (hN : n≤N) (order : u+2*k≤n-2*k)
    (gcover : ∀ x, u+2*k<x ∧ x≤n-2*k → ∃ r, x∈G r) (x : ℕ) :
    (∃ p : (coords hd π ρ M.pairing σ apart).Piece, x∈sw (u:=u) π ρ M σ apart G p) ↔ u+2*d<x ∧ x≤N := by
  constructor
  · rintro ⟨p,hp⟩
    cases p with
    | start i => obtain rfl := List.mem_singleton.mp hp; have := left_bounds (u:=u) π ρ M σ apart i; omega
    | finish j => obtain rfl := List.mem_singleton.mp hp; have := right_bounds (u:=u) π ρ M σ apart j; omega
    | old i => have := (M.covers _).mp ⟨i,hp⟩; omega
    | central r => have := gbounds r x (List.mem_reverse.mp hp); omega
  · intro hx
    by_cases small : x≤u+2*k
    · let i : Fin (k-d) := ⟨(x-(u+2*d+1))/2,by omega⟩
      by_cases even : (x-(u+2*d+1))%2=0
      · let l := (leftCoords (hd:=hd) (π:=π) (ρ:=ρ) (M:=M.pairing) (σ:=σ) (apart:=apart)).symm i
        refine ⟨.start l,List.mem_singleton.mpr ?_⟩
        have e : (π l.val).val=i.val := congrArg Fin.val (leftCoords.apply_symm_apply i)
        dsimp [L]
        rw [e]
        dsimp [i]
        omega
      · let j := (rightCoords (hd:=hd) (π:=π) (ρ:=ρ) (M:=M.pairing) (σ:=σ) (apart:=apart)).symm i
        refine ⟨.finish j,List.mem_singleton.mpr ?_⟩
        have e : (ρ j.val).val=i.val := congrArg Fin.val (rightCoords.apply_symm_apply i)
        dsimp [R]
        rw [e]
        dsimp [i]
        omega
    by_cases central : x≤n-2*k
    · obtain ⟨r,hr⟩ := gcover x ⟨by omega,central⟩
      exact ⟨.central r,List.mem_reverse.mpr hr⟩
    · obtain ⟨i,hi⟩ := (M.covers x).mpr ⟨by omega,hx.2⟩
      exact ⟨.old i,hi⟩

noncomputable def assemble (hN : n≤N) (order : u+2*k≤n-2*k)
    (gcover : ∀ x, u+2*k<x ∧ x≤n-2*k → ∃ r, x∈G r) : Boundary N (u+2*k) (k-d) := by
  let w := words π ρ M σ apart G gstarts gends gsimple gedges gbounds guniq lpr rpr order
  let lc := leftCoords (hd:=hd) (π:=π) (ρ:=ρ) (M:=M.pairing) (σ:=σ) (apart:=apart)
  let rc := rightCoords (hd:=hd) (π:=π) (ρ:=ρ) (M:=M.pairing) (σ:=σ) (apart:=apart)
  let ξ := Fin.revPerm.trans (rc.symm.trans (coords hd π ρ M.pairing σ apart).pairing.symm)
  let perm := ξ.trans (lc.trans Fin.revPerm)
  refine ⟨perm,fun i => (w.row (ξ i)).reverse,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [List.head?_reverse,w.row_last]
    change some (R u d ρ ((coords hd π ρ M.pairing σ apart).next (ξ i)).val)=some (u+2*k-2*i.val)
    apply congrArg some
    have a : rc ((coords hd π ρ M.pairing σ apart).next (ξ i))=i.rev := by
      change rc ((coords hd π ρ M.pairing σ apart).pairing ((coords hd π ρ M.pairing σ apart).pairing.symm (rc.symm i.rev)))=i.rev
      simp
    have b : (ρ ((coords hd π ρ M.pairing σ apart).next (ξ i)).val).val=i.rev.val := congrArg Fin.val a
    dsimp [R]
    rw [b]
    change u+2+2*d+2*(k-d-(i.val+1))=_
    omega
  · intro i
    rw [List.getLast?_reverse,w.row_head]
    change some (L u d π (ξ i).val) = some (u+2*k-(2*(perm i).val+1))
    apply congrArg some
    have a : (perm i).val=k-d-((π (ξ i).val).val+1) := rfl
    have b := left_lo (ξ i)
    dsimp [L]
    rw [a]
    omega
  · intro i
    simpa only [List.nodup_reverse] using w.row_nodup (ξ i)
  · intro i
    rw [List.isChain_reverse]
    simpa only [Nat.add_comm] using w.row_chain (ξ i)
  · intro i j ne x hi hj
    have hi' := List.mem_reverse.mp hi
    have hj' := List.mem_reverse.mp hj
    obtain ⟨p,_,hx⟩ := List.mem_flatMap.mp hi'
    have uq := w.rows_cover x ⟨p,hx⟩
    exact ne (ξ.injective (uq.unique hi' hj'))
  · intro x
    have hsup := support π ρ M σ apart G gbounds hN order gcover x
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨p,_,hx⟩ := List.mem_flatMap.mp (List.mem_reverse.mp hi)
      have h := hsup.mp ⟨p,hx⟩
      omega
    · intro h
      obtain ⟨p,hp⟩ := hsup.mpr (by omega)
      obtain ⟨i,hi,_⟩ := w.rows_cover x ⟨p,hp⟩
      exact ⟨ξ.symm i,List.mem_reverse.mpr (by simpa using hi)⟩

end

/-- Clean contraction for any permutation of the left attachments whose central preimages avoid
the old mates of the right central preimages. Identity gives the unrepaired all-q transfer. -/
theorem contract_permuted {N n u t k d : ℕ} (old : Boundary N n k) (hN : n≤N)
    (size : n=u+2*t) (hd : 0<d) (dk : d≤k) (room : 2*k+d≤t)
    (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime) (π ρ : Equiv.Perm (Fin k))
    (lpr : ∀ i, (n-2*i.val+L u d π i).Prime)
    (rpr : ∀ j, (n-(2*j.val+1)+R u d ρ j).Prime)
    (away : ∀ r j, old.pairing (π.symm (high dk r))≠ρ.symm (high dk j)) :
    Nonempty (Boundary N (u+2*k) (k-d)) := by
  let length := t-2*k
  have rh : d≤length := by dsimp [length]; omega
  have eq : u+2*k+2*length=n-2*k := by dsimp [length]; omega
  have pe : 2*(u+2*k)+2*length+1=n+u+1 := by dsimp [length]; omega
  obtain ⟨g,hs,hu⟩ := Erdos473Shell.shell_decomposition (u+2*k) length d hd rh
    (pe ▸ p) (by simpa only [pe] using q)
  let f (r : Fin d) : Fin d := ⟨(length-1-r.val)%d,Nat.mod_lt _ hd⟩
  have boundG (r : Fin d) (x : ℕ) (h : x∈g r) : u+2*k<x ∧ x≤n-2*k := by
    simpa only [←eq] using (hs r).2.2.2.2 x h
  have uniqueG (a b : Fin d) (x : ℕ) (ha : x∈g a) (hb : x∈g b) : a=b :=
    (hu x ((hs a).2.2.2.2 x ha)).unique ha hb
  have inj : Function.Injective f := by
    intro a b h
    have e := congrArg Fin.val h
    change (length-1-a.val)%d=(length-1-b.val)%d at e
    have la := List.mem_of_getLast? (hs a).2.2.2.1
    have lb := List.mem_of_getLast? (hs b).2.2.2.1
    rw [e] at la
    exact uniqueG a b _ la lb
  let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj)
  exact ⟨assemble π ρ old σ away g (fun r => (hs r).2.2.1) (fun r => (hs r).2.2.2.1)
    (fun r => (hs r).1) (fun r => (hs r).2.1) boundG uniqueG lpr
    rpr hN (by omega) (fun x hx => by
      have h := hu x (by simpa only [eq] using hx)
      exact h.exists)⟩

/-- The d+1 genuine repair centers give clean contraction for every input boundary. -/
theorem contract {N n u t k d : ℕ} (old : Boundary N n k) (hN : n≤N)
    (size : n=u+2*t) (hd : 0<d) (room : 2*k+d≤t)
    (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime)
    (e : Fin (d+1) → ℕ) (bound : ∀ a, d+e a≤k)
    (separated : ∀ a b, a<b → e a+d≤e b) (r : ∀ a, (n+u+1+2*d+2*e a).Prime) :
    Nonempty (Boundary N (u+2*k) (k-d)) := by
  obtain ⟨a,away⟩ := avoiding_repair e bound separated old.pairing
  have dk : d≤k := by have := bound a; omega
  exact contract_permuted old hN size hd dk room p q (tile k d (e a) (bound a)) (Equiv.refl _)
    (left_edges (by omega : 2*k≤n) (bound a) p q (r a)) (right_edges (by omega : 2*k≤n) q) away

end Erdos473CleanShell

end

section

/- Compressed schedules for arbitrary virtual matchings with two or three strands. -/

namespace Erdos473MatchingSchedule

def ends (n : ℕ) (pm : List ℕ) (i : ℕ) : ℕ × ℕ :=
  let u := n-2*pm.length
  if i<u then (i+1,i+1)
  else (n-2*(i-u),n-(2*pm[i-u]?.getD 0+1))

def first (n : ℕ) (pm : List ℕ) (i : ℕ × Bool) : ℕ :=
  if i.2 then (ends n pm i.1).2 else (ends n pm i.1).1

def last (n : ℕ) (pm : List ℕ) (i : ℕ × Bool) : ℕ :=
  if i.2 then (ends n pm i.1).1 else (ends n pm i.1).2

def Schedule (n : ℕ) (pm : List ℕ) (s : List (ℕ × Bool)) : Prop :=
  (s.map Prod.fst).Perm (List.range (n-pm.length)) ∧
    s.IsChain (fun x y => (last n pm x + first n pm y).Prime)

instance (n : ℕ) (pm : List ℕ) (s : List (ℕ × Bool)) : Decidable (Schedule n pm s) := by
  unfold Schedule; infer_instance


def choices : Array (List ℕ) := #[[],[0],[0,1],[1,0],[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]

def packed : Array (Array ℕ) := #[
#[0,0,0,0,0,0,0,0,0,0],
#[0,0,0,0,0,0,0,0,0,0],
#[256,1,0,0,0,0,0,0,0,0],
#[65792,384,0,0,0,0,0,0,0,0],
#[4260608,82176,131,385,0,0,0,0,0,0],
#[2151744256,14745856,49792,49792,0,0,0,0,0,0],
#[207236498688,2420179712,10518535,14762240,17027,17027,49285,82051,82305,49793],
#[35531203346688,139072766208,1897988352,2430664960,6374272,14729856,10535808,6406784,10535808,14762368],
#[7916553525986560,57381841143040,312194695936,69812273920,1889681664,1361166592,1357005056,2430681344,1898004736,2430681344],
#[296182253644546304,8479780504666368,48517588582656,57313677410560,312205181184,243489898752,311139827968,379855110400,380387787008,312205181184],
#[19603061353427962112,439175800282023168,7384527328642304,7344879143355648,39963869643520,39652235100928,48691243188992,40032052249344,48448323928832,57554981946112],
#[23704650494982320554240,148008612182446178560,1090469590980428032,582156809884729600,2278637753729280,2278706469011712,7336151788683520,8462051158655232,7336151788683520,8462051158655232],
#[325972706205587820645120,2509770596646465374464,157810643481334580480,129704813417774384384,1090460586048963840,937910392506795264,1088257233990583552,1226140631219553536,148693761757758720,1084259787144905984],
#[158081384330940293780406528,625824684826390109094144,22542653726538479042816,24903835842073394807040,111121289788358983936,176112203776712048896,157379467865151832320,139218733221478990080,139580107645526278400,176477527579390181632],
#[15322242330026231838869162752,486304634540485885839936256,3185348538401237573372160,3175940047093844142000384,20126274306431904957696,20126274381127304217856,22487457613766033802496,24848639729300949566720,22487457547867545273600,20199762365679545926912],
#[1332180359452527966407256113408,67159158677679181323546460416,80105559801893122054816000,80121063061974325179711744,3187691269295965810589952,2876051471668108255691008,621139210701817671450880,2898390340190021030641920,621167958809535966216448,2876051981635105104986368],
#[90018359521011523443842017726208,3218916112960605185127454280448,15168875140573421143981165312,5340736818477474853561699072,409681857718304155057195264,445205878179365072729737472,407110704412450333479078144,445205952256788220648556800,447009786138536475147569408,445796137956960304506276096],
#[42598165514328357857976476666167552,1258841731128138149002287780397312,3847597147918501991472351740160,9220526204300141311603119554816,10253511654868115189427077376,10253511673313733363229786368,10253511655145623472337846528,66928867681205690570595631360,10253511655154093765765103872,66928867681214160864022888704],
#[14684227507956235468754286466231046400,52906987859273799209131762876878592,1179598442234020685753205714520832,86235061813142437348259752250112,7994811413308605629841681877760,7928156388715778649365302938368,8628925970083051765945174526720,683614312765252408665467718400,683614312765261987026116479744,1941131706107391078789296622336],
#[2736984859785728257352255962929368072448,2814717439199855028422906725800608000,21826443009292666881465452239192320,171674801375277887797295375188427008,331520694330112035719884573049088,331520691312539738801539842900224,1258811866446770661241608009482496,1266096096330589594021484254527744,1105084586303667679279847422886144,1266105768950757215408710532530432],
#[24169456909148223851740536423972231057664,191601198674237674358847076744663535872,21964070483044995941795235507424268032,1474860812141030766986322740716310272,162139543465066637159899154497014528,161212279701143362911878750838852352,161212222581206978417372502570781440,172605266974093958665413847790603008,32133071590294085327448564262488832,172079781353386022747075861364738816],
#[5990693792354967391243301459390205033840896,45789361045083299337834468858624603521280,3161018897049291690317312694389196718336,697866695103031701731925361906600640768,2794879336373532289978266715607728384,5389774725209066317206031826847990016,2794885322937018894766329865959833856,23422780133894236026803602011145568512,23433006261539293650879416200757444864,2793784705189763592282481544453882112],
#[5385829034762956437383090854322441862724587776,8758274106239747592021392279723228782530816,403085934017659095484649639336950884339968,24526442731506585017545294832827071860992,2830622825576572237748722795314614963968,2808804713743322443757285109815580888832,188921969702106843003952667668101795584,2831931769915139606583484779397338173184,188922134496684258746175588103645892352,2999414494838757519010447376805657644800],
#[372210915456054938629045438008097960390593872128,3615597668199321211672084722363675412091502848,54804874492073483262795786104598599360250112,54533825057724111893980922470597672292516096,46116331054397117632296395513387094114560,219678209783363833017794491823366349521152,219660336848642964859356332235059028820224,219678250832455280169261820216207124988160,46132914478544038166031248219145775874304,403254606271406937577454024751260440723712],
#[76638584867542946597536179244696192977899989701888,1029430299485955609637587609135541460063893197056,7691187469841073317431917654939894429960769792,2525583582574473284320283905830337033814806784,54382591555691092141734296194728133279224064,52017115281162443693820570146674029856674048,54761152365820646720047618185978324713607424,57548745437829219355881187765084853902102784,54805718541217164596415049702277282139345152,54805718541217164596415049702277282139345152],
#[18047176397095950700851249452517924959262931709198592,105738927673353137546659687264339490382713159418112,989991605491981709990331858138711749194286760192,984112766349418047075160689241692526307430760704,7331699978336690818631286162680574766607696128,2183113175354111740058733900623555925484437760,6974886780295968644794711839411777813577400576,6974886780467669071599813000703835042365243648,7015240354571414066640001171209081906054758656,7018213246038549833680512821700156576510705920],
#[687005334724094343504567651872589645273271014466458880,5354991307588571588897299221407639399572367682508032,132224533476230921062316670573821404819804502757632,138070540028606460484543456676522287048053038911744,937395589056851335546137657481769753982154182912,689369394218683094191965815328550477710091227392,938103618318027192520832139724598211336346931456,143501442704377982925967007176766852508581761280,1029447468617571889852303201966266686128257110272,143501442687632499867739162355790624256228987136],
#[26929507050244195893381214428626703111905264355225960704,400428666201574789199957974414171194334669444408279296,1550270057618791388776608870873958437143970467807488,18450686780676286243975362910198089782926192172073216,138414495265942460382401455748242212748431444279552,138113700224534628793487723087659755338062019297536,93765928378671178559660028229707109864988947906816,93772909522785086813558134702294351831390376034560,138113700224561702155010857628711967336737377222912,138371173301036667224452796714683916007338714726656],
#[14344451668739030146911116151745445646659539755434846064896,87936683943614753343946537358212750633360897705804764416,685438887787972596874494653686158382573499701484786944,1831817381471059952773387154738772481991840238846285056,6839969732526742777477074465771221219239375389085952,2327400036020779094946153856636565524685466978357504,6840788922701335427339135792119969657159310969164032,865531580290287703711493318030617949109143749742848,17591550406989800878816860253813662763498467661844736,16980415408629931689863807468898967949678207740023040],
#[444203708454433609682050886299603628354480833344186736312576,9698783446307062663819411287865122298650827392740028645632,221737491289057809330427465423347060342782058322675237120,148765896274272553070672402577626252937897156027517370624,1350805499124072133641121055638962371384376935294959872,2457469356281298204750985116731674139970522501186322688,2455948554964020628279527294522429711293238283564744960,2455948554964020628279527294522429711293238283564744960,1350708997787739833757121835906048957505550016087326976,198440413381754621375079384036497771336227924897956096],
#[31371582605704190657068954684285135611653231611973970759452928,2645861982322483977876567139401563031055277212333175239741696,11255895544782688428025156862980870481622189198697696531712,43243011113628114330056697981382588168426043432712435602688,325384463710401396505490594409766162275336216347058312448,13237680334229556471082167298708447261661529474805323008,13237621600132416751709478758136423267918787942860133632,160725826009360216235114117468263757200928432703807476992,234472624828298461548143372140156573492159521199417922816,87736177678459635248867166764091772717610652064555406592],
#[59830768123796475352073478008504013429398181427594904697217876224,107890986127336006977868134758193850537384302029953086098637056,1621088449700705148560787164975693872443820584410667656478976,441164383761879930660754492249530348100922969950328351162624,40342574851310961266212421514903865216056013852567029809408,41637053866210556100422526133491549589356969690170479214848,40312208501566545581745237689521551882372526924344196727040,25269897459947376041452964947777868124954488920216024252672,12814108264756040565709122441541840427689842074278873923840,28384364691614931152041938530682996680817691853730997731584],
#[3041693482238363327124938556716605060808397580663296697812652264192,89166421788026947850940014249664566585922879093616171924586563840,738691221516467303161000645229165166294510346416744507587825920,30954229483682168200040107022553657626808260287832849853583616,5367891864256717063942436877554167334501310508630532130280704,640400982042684480137742635612304871285120129419188401018112,1440754630767254312737287880582881950491775426244255743677696,5748427859047907354706934981825601512251469237758487481750784,1440754611727746542452853418927309656317014390228665464198400,5742199797193035934837958744662010397842697634205716780881152],
#[1193412852320198476203139726800175101489254350350056251559161415729408,8494305658509885859693959511997412841150347003716984183074948251904,7282357743714396187225576224033049194260127349301970551161356544,7282189035000019769747709821428247409752627029260991575232479488,738717714629688197327784714161438265634160196951536857881837824,158932416992859612129867244567899020556913132863953909920366848,158932514505728124580508086934279010952339647749840444685353216,708294398981712436957803410121478824909360212270567950857863424,104296523488054039770969596331648445884576561768078402374140160,158932416992860732808169667738784944069293780633349814846554368],
#[91132696054130798549484893890833594894589173979344773674246147288731392,389277373695156641469421990612557520173154178558194306907330941422336,513732518083866134961969373118949806886290612110937911752690698496,13312234957656957470101387536281552261787453367888780101218742765824,30087322786403588314491477555545755494419909670193159661635457280,30087634917818897322732361072760965397681537211342725428462670080,94028816974131409797302023641106520665615792166458729450225750272,69474190035830341812432666882956994137297517615678758090986934528,62943195202717377362567935434871055537187190165836902593976209664,43352602644852148677578767035762227798418255516546881912922312960],
#[23073298419193864209955660535163229095638867987558460178282346215998357760,84277659335370716916107279958244064582023144992927642987731348857159936,442840094143595172554327296046847446734383469038110220051079551123712,335775161613198581315900892382546951932194820801402978438565868732672,12466937528105573492494491022874693901574960910847347930132237910272,2557427280799103611049123777467305738565901782018276543083020419328,13289328650866905495723595531442617017905685293976947850336040517888,13369880621208460811038702139866755216622109699641005797895639531776,13366589612091391610611901419423540528666078146262249954680375214336,13329128064960996799231565618404959837994433422207539468496622452992],
#[1040777743632782971070713543399803460013644649151417245413024759261654357248,11664985094928742214334066418026700146813353418011529746165523903437737728,132333126069718967254190696049640274560086525551031989254291061756594944,215032988962073242383318652886751744199124329407745903821953779735137024,65757762515602120807505864201972166052086308627152031949032247200000,1757885967914391835762311634839856022339008381642304674008617913092352,65757762515602120807505864201972203611915665384773715380672596740352,1752910112391126820834577122022502133297900973258359761266070232697088,65738115370813811101922324067175247969672731331646791363687826524416,1752910112391126069552586990631387120917706217155216119994318730758400],
#[292998188373419108031077028955969013747527823451010142839617534566899768623360,932082205673959582994561256463103157926120985069068119574949811049097462016,17813844163220739489431967946324297495369569926631080916411001986133917952,17813844163220739489452528209026308787089884687638953029186524443392737536,217740785080634243140083815737814327552169703628746795127215669208023296,125484881631758782588506878526968438234723945655719307489623771729232128,42979220470973038804634642866033915315618998062606819267951750628114688,42979220470973038818032245126642162496544618785437199972898376065614080,166566208848007380584625533594889205340973726508948245551174680956502272,42979220317933190972248166806318989941673385788830114597537672705474816],
#[17112258393903005392881681235994029718654585418824551048558224598855656795413248,249250151938015186910142762484462858125326294969311451510439821333683742840064,1493159184191721921451697864478923040312681576373643368554837048125550563072,2168012483686725226719943975183364919121247487756741309684314327227383746304,13418803419800338074306222323853985596218552028402188289894844564242565888,30514242073160387508111253227270209894187657072191814397808031801479924480,29699510813402804727374159772930043601618503809641046408879416748957371136,29833617509614437185234244251344936280167805042388612228678996675061222144,29754293424674116291780585811102350992310126385734232473863537858692909824,4624989071006228790471406976274364939720835089870956228973306558613162752],
#[2417971681385217565706647094840246707707812988694538129952693876111939943910736128,26299510829437246076005287388108913395566051833765969615967882868846098857328896,321053897689308455568294614081598831261065254009414096194179827523575410721024,321053897689308455568294614080351012558729163010240825961473092998344563360000,1156554174019971934711026755318187158782763931109155079004679660981095104768,1156554173923577965521686517536262160012736341596129450416280703665764696320,3797155686265657968210511764056451864141172626624690064831463403898912243968,3797155686368633955482227868662351518200029919545710913850931164152966545664,479769568552054470012583698552023212381518037350152318161094781506549580032,4033829730105754957607729011850876437430027482859925621326711613916082733312],
#[279414909238758871396346337484147609173995995803065294313769501444945692659013588224,778428863419770138906248429714870183443822088652210150373246417460616472056699648,67666935968959862705152529575372282271198975952764341161410138307068903532598528,28137824214789086740136332510191053741222185137767873734278290415792320550606080,133689057193202776289835172759497370951606719487829477617540665162891266494208,277505598418765622603194616632039017705981154178152005228310450966650098683648,499721021350380281942063077903453768061041588361757085596613751720543191961344,499720980153910248036564868578656958335321321174993548548725926766776628416256,503379326352197510703177454443060860414664701345409384644630668196153013964544,47052200702016752254619698336102063054966140191484896072176742521570597408512],
#[70275699420939290789417302437525995951093883013127568230881150712084490614181523685632,69497966901360344537458413298980315735764285634484224527657481783065283724959154432,2896286733407493963954842227286020162069005999857892013875314889120231811652780288,3366337386169390118562569228373070133801594328542162656504665652049950082794520832,15274128511545837861808204743258357923077791884206883651025960397644808344699136,4184354373787856584164868485100554968328467945691342050448764126787546169082112,68000606080522664201692815873701146046071688854371390987889473593085797016928512,67712736758322248764652915829611445366648359863483267507850411580382807606296832,52122067270587403864062243048901581552459382375615206675094344360514240402555136,69565387540789885685465055345065498153716201716189975326573917646654388524679424],
#[1640439714225309989117078982304712565502888269433734402541409468383964926393603189772544,20527299259149768673756784003570200092787532796455862242514644644202819764721851503872,584342841659718884080135285115240354056310571603786780863149617436980537813807209216,584342841659718884080135285118452957357931481833562633530089785484413720073896794880,1241713461699031121717703704323470012159068550083592577889437618344607205221274880,9132320261898491792933638188692579805264996630771893671153388383286854595511915776,8669123619670075835341435459188576042895113157867605540338167488746295883926672640,1719556174483796764748211593620336865045709826816046537417841452287404128405624064,9132320261898489213094630585912693212182714305978036726007233770698107205859218688,1241713461699031121115291955919151900815397896917912259647297152127095230117254400],
#[145747798882672874430218298979882613292980502776169398741977045088355349784158574860108032,11055004689557625759475798837515693020038381454105775135702955048395975472249812588232960,39621841384110665700484273771909547031485047002269733477051999541712472328922320208128,109492853280323063625419994246718233792785261705407547667787875095987668588468776861952,245920270398337109606291339833710160890169861427315642729527854842247538041124552960,310430735946721834692705657380158389617050268071603536134509619157019815393171603712,430891186303142796713604469303277343355887730491447604818667237031669676863161630976,310430734586207865884882953942495065127437385727705544746763241453292896985050251520,430891185429688836922355651795540411882466351079134766966991548700674272176300884224,129735732387792226464964998154518497062408079870614671314550457015209963001641173248],
#[10576675053959082514882711538438050364892632862415774098700907638135870536707572661242893568,209976283420839678606986090241241052740270866978515240226296530478744696134686301472559360,20231439818510765941883725653391630746570095996215801556473565791551872859987676261192960,20146631595559895059217371478441268216294755565000042265516152180354353041525357293016320,12750955055787231951776974154475780707505284837147114377423397761510255832940652600064,12750954682593620226304739147735256594239845677872422237076303349546405246406113172224,12750955055790972698316268104420400237874910180045821188665598607642779275732489673472,35888276443126391585588938954496977978587359034007269255044921616902751955218151840512,12750955053597383911456786768245665055705399030753111853718907517652829105703032003328,35888276443126391585589284265621234168075872728848445173479888602024596668675430882048],
#[4475510880901517539907599382002583271921348787573681629575592055186958855024169954654033412352,213827269589491158147789131957906270372996444736695045982400342454447581172944894511195160832,273163263117897301057018907388248963919405193631025910253002145004209502875380653935624448,1797956300270403633082086537719349770224783843709210743968561354174653248023035992647467264,5070488926519031010131374309884631943410527001762954849389992367663475865784586533994752,5070488948576302061953975612145746902080895307945997405262802060916866725685664202490112,19806667811184905917281288714710336470637262240626624029880885070788166348737866373923072,14015085219881352152539898520553057623114788026079751434273532661017057107798765809041664,19792550070967121390081544356303259036945363628782183013468687211738734234200034341683456,5070488926519031010131374309884631971266981187465995162202386018648614110725833704997120],
#[1245665079548497369153274147316974292915855171840510981297425253006600541475307375360630665580800,26335263617708253559847374850687272657050286046858594492770102699281265026940454566005853197568,173025360024382358908427226803394040542064383143145623696582988244522047598031937041760129280,26873972567795335943750863514012867592985957785354422113999088737852375798408096130156073216,2109750446853309291467344235296878324908478352132339319912994112817338666837012637158675712,2642426218455155354147390929761383315604452237711727934390317882451369141280168761176036608,2366292194233135263528309425753492475687275934809653304845344112303940837970850240117544192,2642426218492118372705087095347952720460413451582160772481056905999112022318461842977133824,2645395524302809057339364916888502539172475916168569139243620452364234064960747343588824320,2653281671029830730590938430215768595847545625205381042041291862218213235438052937337869568],
#[38589960815597727808343549497202734094678487458785477216182717589332768816545832248342901522039040,312059222670674219578944547796576191557837124679455240647805735943709732052334623123122809078016,2387931959535123435226003924608079898646027100189861641192717176985318913501346223819733401856,2387931959533689293677553849804517517622128100159597487797097278325282629902528821489745068288,147368955320675617705779907753056364614896221071363915119414391601285892773174217051447558400,34961944209636254613622288377129707787577012798000876672457513029659866632925262213397938432,355595656941513248373806945869979978142969148330504962842667742102287419406198034958010614016,147378824544668103801596503683530067574929337526170457185264764114018552308927245351260061952,349066358542506204814495059617791683061425202873954392325902388267351825277701143875120070912,346442904497039034708915668535629135123022295594767772690844171717482828254642069509721882880],
#[94496235488897628789890103245585975253886960523913729992656175028024229625763983289156534360764451072,430682075084998790279791764170493917425577063657873076976352037847649818127039814355383791586251008,173190975616492563897612591823815835277157432729878409285133935161690248766381348819639779005696,173190975617222487582670793245872298319332422840742688068020471623190090352639155596406901249280,22147246083120941940278685085175579690359749378448342117936565571848691319231429348570721030400,1370105720576790488228983947007826312337607107897676860944025938353229848939193196862219079936,9680204982028254788617482448217835734266799577315449967113081417321249941754048190143795433728,13771580744506821532089665205698411600735758099489370858121745863016588942667541654205346730240,5494088107860861516453233706159358918130021562537654186101955391319596285265637002244081717504,3440251560972075826877474678555298443184385886935352406097409577705351419471294296373386678528],
#[1222849549393660172865690857576265570483934226422683848047753080979637153565884117331516826458978124032,4939514984396509159467974335436204209958483636271884997771313229856795680714799955574275401839935744,39930983097466807994701057814972784315574501107285328236396634303392569370404316244017577828155648,210308973438982365105055992987602189299938636112321578309857789013805506406652663605351843464872192,2431391203550533032164297792357327420916380792682876269314539069672480697821901131481293612187904,3503475345453136329126985092665034001814154426008567655331096411592714928444442085221149933895936,5813791465419249363012049856798181032197465686422014838245960618317573997825560034179128585421056,2431341671435388080691481810133073422386523417707380255369250431897232049108463166626868432535808,305655290820312188975529413324694373615609316226467262001361945915728179047615502725621042184448,577122481186452907587422738466819845578741991450556716095561180147105516785372804231422232559872],
#[830396881921271536642103859219680104374234367122297746402562302613030001839977529237368784628015897645312,13651042291782787374942468249764255877140753035123522272752356968932547469294599399241644955583254235392,2942482865147562743939524167228269878412076747884394545480017467135239795336436124387749369473470720,102137840777495053273601145325139887406347955456814772593474752442634069883523324071390603011020099840,22168446019863979000127526724090459094052578321708454352499754705819356451374069221138905352967424,22168444878934724455557521894191842289806955962192841589038260981770775332849465739183882045560064,22168444878911048178894434231528412410454364660816329452544366198079614317240791938275109063169280,22168444878911048178894434231528412410454364660816329451601586326739500704347975331538082443367680,22168444878911048178894434396944549404148920851472589997591111964466247621500412275144843185427712,124155601906023772198846426139373264325164079637480745426541824595847887997467689907119997091124480],
#[47565522898108482331387382007814955727245007217162518506018945515958721185551647698601717887810760101921024,727720554105233136055673122745767017271410927499337796464352889504048554460602592481471305891927523983616,2836933505563327144232152307988965278168022887216776474091041677702537954481431582891329749336810979584,2836933499175182276545074054888873201493917181272826607158049943229354527285403265116041463926690808064,44108690327652149671044858067887243861284920820546822477055152908174886103045034626526600300779143424,5114373841072566277740675555665737760285971143784947361362879677709529907773291719901566486959227136,5114373841059889171966315138777468511449459664957909314840020317569977218319600466441186222254981376,52957033639649706974220309680917346037004804820835985467476553833134859465726522829336383918532067584,44108953168823156698340227122076731110109080851142352221454202015974788505255252227401760841884107008,9385826692301148806120024209279592625338585903738751900930795217896426005799086636521910084211966208],
#[5506229356213549852712293442651112122341767487992924862583536036391309139540188096531172667411957044727715072,88595124314713694928342608486179338513856382339026624296186177184591425021572086770792094183494561602801920,549356972901595414493382097525117640865365971473535447224703173241284797394575873934256211597642474850560,1743952133342156966786196425434148998208520083765606955136893506454631061181839117787578954606977619462400,5958127339323499685158878927970747689498879310032813292208325473923896625478998809580816112648492486912,10428932171398836028716041021608382166601806760544757712651077121835167901791717491269769084754402545920,13038925290571794760120215773705276424718100257479599504664612038606148278441148829114511215240128565504,3167229052157834141287318787169061428968401771231951476269807343340433846899843764586997966516318179584,3167162025035654493676721191175063794912261957353746767423327699142498576646234098617233478721590595840,3167162025035654493676721191175063794912261910670090911992394438156324191137035620637426440841846132992],
#[630171611389945703682026805832735321068599564871655721610646803017137388012318755627385578004406963975717716224,4894411507007181723461567504748293539445468876952068854528245497366294110179340154236718091537391474443878656,93148230942557737702493440370618351860099523535893570972498382573776399080131000625253334159439825898701056,56658335605040022334059980325966321405751582320648667183752319244384577322505429953314379872590699685085440,298782977599602569571823522727133440335439250424441567664546892534461576848698242053097259854524663070976,298730896870619620023862196652528432539134365003757124137315765250705465056294214001768416796843917574400,1011546882729013132705085382510045845346307943030451443872216987303687818838297486095052525710298829947136,1011560421966526089500813999799329187058813539490843072434485592888949812747578380720837990345432355963136,1708393805652191757979722624350772736088317400480694192323201935605127201928979548502920171434698513711360,363193176162647988039769585688497057344995687749930103216641420973553867084331582840269591090648088707328],
#[185779773900215754730950261199783166702153887824419877078988694083061494486268374186186452319982942259605521243392,551913891165111075022328569002204964030833899135275191870294214705442756951122639194422278073828761210550686976,11340175912283352950827853886230955329780518685742198473699265435549894432364933007290230640076561450600304896,11340175912283352950827853886230955329782420701039890171900456749604448939962437109869430601012169518491177216,232832671373324455429928675819626615659435969687277524949511936776431788345090276685676983921814572234311936,106800841405422254974642384590811384336386112316902167464978384892637818611309798107259812237699568961718528,198172969248012639119910550767120706272277931644808929400659386445755157066110967794123826525978412318329088,134032843978007731118294227733841553816760041661948466553272145372324638016198638678198853025766481708321024,5817514095456200363638241860872638097411388880611888520466608447306348854405433643339049666545894568888576,14056971295889349761482907640407099009994853385631824800667001994940335972340664493528209561405696246417664],
#[15151090089138060468165714560299425049528246260892882994537514742634331178304911427750617162963178539569002468409600,515579883431026322821459324628528371191978579840160443625392762048109938166105011194777615260205826934612931707136,2270564885800461720411380475663236368005642393019013223826075586277234403380357348589284822786971512542559011072,2270564894212114604812923125406958028410116507953676492818874916794190738209530045085456139603648997495232069888,29877563047462128152551936331979603234115813335722919185073627487270375069700174522924761150390816478462345472,6060008867564528005745817480629390256491557856756485233326837365894573310946693123006482478138410288534651136,29807205134824731353428769831571204687778883754154558364233904158590524652691384490432049677575787377621074176,6060008867564528005745817480629390256491557856764071432358663323174033983599023566443034924687832744958755072,29807205134357618869803153929379053645922529267027656602042249990182646901139521978176723482026280082887540992,6059579920405531673483932572985851107689807392175347665611504209060735064622661412894519921668839762277302528],
#[3989753301283700881245294840674060776404751271392816324539597843413337344015996880165513253776133562379634575600198400,4062430435094115622660167990122577096824850071487942904989072322126486182502146287204096476562735920637522187984128,508874029940351392894914417670464414953164347869254917423524220308929491760027126819700314622078366319105110381824,90214061772202800786838215764031029877078641063924426821281398431894891964957387044406815639783176836797438301440,1451404201934508726617863668810010276383701035383656562268228033407392214315397798846594940802684919356726776064,1451542528569579486476768487154306998780234429960027773006829478776426037490334856295626657625807779106241450240,1451542516772370898011187385140089616197624704298346723481850942097733877868787140134707205041020211201839534336,1451542516772370898011187385140089616197624704298346723481850942097733877868787140134707205041020211201839534336,1451542516772370898011187385140140721359234849754848607346515538233160080403044292059480482307278304273141928192,1451542516772370898011187385140374330756244350218710562113638995304855840950976457820071708669830734426067505408]]

def decode : ℕ → ℕ → List (ℕ × Bool)
  | 0,_ => []
  | len+1,v => ((v%128)/2,decide (v%2=1)) :: decode len (v/128)

def choice (i : ℕ) : List ℕ := choices[i]?.getD []
def path (n i : ℕ) : List (ℕ × Bool) :=
  decode (n-(choice i).length) ((packed[n]?.getD #[])[i]?.getD 0)

def mask : List ℕ → ℕ
  | [] => 0
  | x::xs => (2^x) ||| mask xs

lemma bit_mask (xs : List ℕ) (i : ℕ) : (mask xs).testBit i = true ↔ i∈xs := by
  induction xs with
  | nil => simp [mask]
  | cons x xs ih =>
    simp only [mask,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true_iff,decide_eq_true_eq,ih,List.mem_cons]
    rw [eq_comm (a := x) (b := i)]

def MaskSchedule (n : ℕ) (pm : List ℕ) (s : List (ℕ × Bool)) : Prop :=
  s.length=n-pm.length ∧ mask (s.map Prod.fst) = 2^(n-pm.length)-1 ∧
    s.IsChain (fun x y => (last n pm x + first n pm y).Prime)

instance (n : ℕ) (pm : List ℕ) (s : List (ℕ × Bool)) : Decidable (MaskSchedule n pm s) := by
  unfold MaskSchedule; infer_instance

lemma mask_sound {n : ℕ} {pm : List ℕ} {s : List (ℕ × Bool)} (h : MaskSchedule n pm s) :
    Schedule n pm s := by
  obtain ⟨len,m,ch⟩ := h
  refine ⟨?_,ch⟩
  apply List.Perm.symm
  apply List.Subperm.perm_of_length_le
  · apply List.subperm_of_subset List.nodup_range
    intro x hx
    apply (bit_mask _ _).mp
    rw [m,Nat.testBit_two_pow_sub_one]
    simpa using List.mem_range.mp hx
  · simp [len]

set_option maxRecDepth 4096 in
def checkedRow0 : ∀ j : Fin 10, 2*(choice j.val).length≤0 →
    MaskSchedule 0 (choice j.val) (path 0 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow1 : ∀ j : Fin 10, 2*(choice j.val).length≤1 →
    MaskSchedule 1 (choice j.val) (path 1 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow2 : ∀ j : Fin 10, 2*(choice j.val).length≤2 →
    MaskSchedule 2 (choice j.val) (path 2 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow3 : ∀ j : Fin 10, 2*(choice j.val).length≤3 →
    MaskSchedule 3 (choice j.val) (path 3 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow4 : ∀ j : Fin 10, 2*(choice j.val).length≤4 →
    MaskSchedule 4 (choice j.val) (path 4 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow5 : ∀ j : Fin 10, 2*(choice j.val).length≤5 →
    MaskSchedule 5 (choice j.val) (path 5 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow6 : ∀ j : Fin 10, 2*(choice j.val).length≤6 →
    MaskSchedule 6 (choice j.val) (path 6 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow7 : ∀ j : Fin 10, 2*(choice j.val).length≤7 →
    MaskSchedule 7 (choice j.val) (path 7 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow8 : ∀ j : Fin 10, 2*(choice j.val).length≤8 →
    MaskSchedule 8 (choice j.val) (path 8 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow9 : ∀ j : Fin 10, 2*(choice j.val).length≤9 →
    MaskSchedule 9 (choice j.val) (path 9 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow10 : ∀ j : Fin 10, 2*(choice j.val).length≤10 →
    MaskSchedule 10 (choice j.val) (path 10 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow11 : ∀ j : Fin 10, 2*(choice j.val).length≤11 →
    MaskSchedule 11 (choice j.val) (path 11 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow12 : ∀ j : Fin 10, 2*(choice j.val).length≤12 →
    MaskSchedule 12 (choice j.val) (path 12 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow13 : ∀ j : Fin 10, 2*(choice j.val).length≤13 →
    MaskSchedule 13 (choice j.val) (path 13 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow14 : ∀ j : Fin 10, 2*(choice j.val).length≤14 →
    MaskSchedule 14 (choice j.val) (path 14 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow15 : ∀ j : Fin 10, 2*(choice j.val).length≤15 →
    MaskSchedule 15 (choice j.val) (path 15 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow16 : ∀ j : Fin 10, 2*(choice j.val).length≤16 →
    MaskSchedule 16 (choice j.val) (path 16 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow17 : ∀ j : Fin 10, 2*(choice j.val).length≤17 →
    MaskSchedule 17 (choice j.val) (path 17 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow18 : ∀ j : Fin 10, 2*(choice j.val).length≤18 →
    MaskSchedule 18 (choice j.val) (path 18 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow19 : ∀ j : Fin 10, 2*(choice j.val).length≤19 →
    MaskSchedule 19 (choice j.val) (path 19 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow20 : ∀ j : Fin 10, 2*(choice j.val).length≤20 →
    MaskSchedule 20 (choice j.val) (path 20 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow21 : ∀ j : Fin 10, 2*(choice j.val).length≤21 →
    MaskSchedule 21 (choice j.val) (path 21 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow22 : ∀ j : Fin 10, 2*(choice j.val).length≤22 →
    MaskSchedule 22 (choice j.val) (path 22 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow23 : ∀ j : Fin 10, 2*(choice j.val).length≤23 →
    MaskSchedule 23 (choice j.val) (path 23 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow24 : ∀ j : Fin 10, 2*(choice j.val).length≤24 →
    MaskSchedule 24 (choice j.val) (path 24 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow25 : ∀ j : Fin 10, 2*(choice j.val).length≤25 →
    MaskSchedule 25 (choice j.val) (path 25 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow26 : ∀ j : Fin 10, 2*(choice j.val).length≤26 →
    MaskSchedule 26 (choice j.val) (path 26 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow27 : ∀ j : Fin 10, 2*(choice j.val).length≤27 →
    MaskSchedule 27 (choice j.val) (path 27 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow28 : ∀ j : Fin 10, 2*(choice j.val).length≤28 →
    MaskSchedule 28 (choice j.val) (path 28 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow29 : ∀ j : Fin 10, 2*(choice j.val).length≤29 →
    MaskSchedule 29 (choice j.val) (path 29 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow30 : ∀ j : Fin 10, 2*(choice j.val).length≤30 →
    MaskSchedule 30 (choice j.val) (path 30 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow31 : ∀ j : Fin 10, 2*(choice j.val).length≤31 →
    MaskSchedule 31 (choice j.val) (path 31 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow32 : ∀ j : Fin 10, 2*(choice j.val).length≤32 →
    MaskSchedule 32 (choice j.val) (path 32 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow33 : ∀ j : Fin 10, 2*(choice j.val).length≤33 →
    MaskSchedule 33 (choice j.val) (path 33 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow34 : ∀ j : Fin 10, 2*(choice j.val).length≤34 →
    MaskSchedule 34 (choice j.val) (path 34 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow35 : ∀ j : Fin 10, 2*(choice j.val).length≤35 →
    MaskSchedule 35 (choice j.val) (path 35 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow36 : ∀ j : Fin 10, 2*(choice j.val).length≤36 →
    MaskSchedule 36 (choice j.val) (path 36 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow37 : ∀ j : Fin 10, 2*(choice j.val).length≤37 →
    MaskSchedule 37 (choice j.val) (path 37 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow38 : ∀ j : Fin 10, 2*(choice j.val).length≤38 →
    MaskSchedule 38 (choice j.val) (path 38 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow39 : ∀ j : Fin 10, 2*(choice j.val).length≤39 →
    MaskSchedule 39 (choice j.val) (path 39 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow40 : ∀ j : Fin 10, 2*(choice j.val).length≤40 →
    MaskSchedule 40 (choice j.val) (path 40 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow41 : ∀ j : Fin 10, 2*(choice j.val).length≤41 →
    MaskSchedule 41 (choice j.val) (path 41 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow42 : ∀ j : Fin 10, 2*(choice j.val).length≤42 →
    MaskSchedule 42 (choice j.val) (path 42 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow43 : ∀ j : Fin 10, 2*(choice j.val).length≤43 →
    MaskSchedule 43 (choice j.val) (path 43 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow44 : ∀ j : Fin 10, 2*(choice j.val).length≤44 →
    MaskSchedule 44 (choice j.val) (path 44 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow45 : ∀ j : Fin 10, 2*(choice j.val).length≤45 →
    MaskSchedule 45 (choice j.val) (path 45 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow46 : ∀ j : Fin 10, 2*(choice j.val).length≤46 →
    MaskSchedule 46 (choice j.val) (path 46 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow47 : ∀ j : Fin 10, 2*(choice j.val).length≤47 →
    MaskSchedule 47 (choice j.val) (path 47 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow48 : ∀ j : Fin 10, 2*(choice j.val).length≤48 →
    MaskSchedule 48 (choice j.val) (path 48 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow49 : ∀ j : Fin 10, 2*(choice j.val).length≤49 →
    MaskSchedule 49 (choice j.val) (path 49 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow50 : ∀ j : Fin 10, 2*(choice j.val).length≤50 →
    MaskSchedule 50 (choice j.val) (path 50 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow51 : ∀ j : Fin 10, 2*(choice j.val).length≤51 →
    MaskSchedule 51 (choice j.val) (path 51 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow52 : ∀ j : Fin 10, 2*(choice j.val).length≤52 →
    MaskSchedule 52 (choice j.val) (path 52 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow53 : ∀ j : Fin 10, 2*(choice j.val).length≤53 →
    MaskSchedule 53 (choice j.val) (path 53 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow54 : ∀ j : Fin 10, 2*(choice j.val).length≤54 →
    MaskSchedule 54 (choice j.val) (path 54 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow55 : ∀ j : Fin 10, 2*(choice j.val).length≤55 →
    MaskSchedule 55 (choice j.val) (path 55 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
def checkedRow56 : ∀ j : Fin 10, 2*(choice j.val).length≤56 →
    MaskSchedule 56 (choice j.val) (path 56 j.val) := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem checked : ∀ n : Fin 57, ∀ j : Fin 10, 2*(choice j.val).length≤n.val →
    Schedule n.val (choice j.val) (path n.val j.val) := by
  intro n j h
  apply mask_sound
  fin_cases n
  · exact checkedRow0 j h
  · exact checkedRow1 j h
  · exact checkedRow2 j h
  · exact checkedRow3 j h
  · exact checkedRow4 j h
  · exact checkedRow5 j h
  · exact checkedRow6 j h
  · exact checkedRow7 j h
  · exact checkedRow8 j h
  · exact checkedRow9 j h
  · exact checkedRow10 j h
  · exact checkedRow11 j h
  · exact checkedRow12 j h
  · exact checkedRow13 j h
  · exact checkedRow14 j h
  · exact checkedRow15 j h
  · exact checkedRow16 j h
  · exact checkedRow17 j h
  · exact checkedRow18 j h
  · exact checkedRow19 j h
  · exact checkedRow20 j h
  · exact checkedRow21 j h
  · exact checkedRow22 j h
  · exact checkedRow23 j h
  · exact checkedRow24 j h
  · exact checkedRow25 j h
  · exact checkedRow26 j h
  · exact checkedRow27 j h
  · exact checkedRow28 j h
  · exact checkedRow29 j h
  · exact checkedRow30 j h
  · exact checkedRow31 j h
  · exact checkedRow32 j h
  · exact checkedRow33 j h
  · exact checkedRow34 j h
  · exact checkedRow35 j h
  · exact checkedRow36 j h
  · exact checkedRow37 j h
  · exact checkedRow38 j h
  · exact checkedRow39 j h
  · exact checkedRow40 j h
  · exact checkedRow41 j h
  · exact checkedRow42 j h
  · exact checkedRow43 j h
  · exact checkedRow44 j h
  · exact checkedRow45 j h
  · exact checkedRow46 j h
  · exact checkedRow47 j h
  · exact checkedRow48 j h
  · exact checkedRow49 j h
  · exact checkedRow50 j h
  · exact checkedRow51 j h
  · exact checkedRow52 j h
  · exact checkedRow53 j h
  · exact checkedRow54 j h
  · exact checkedRow55 j h
  · exact checkedRow56 j h

theorem permutation_upto_three {n k : ℕ} (hn : n≤56) (hk : k≤3) (h : 2*k≤n)
    (pm : Equiv.Perm (Fin k)) : ∃ p, Schedule n (List.ofFn (fun i => (pm i).val)) p := by
  have hp := pm.ofFn_comp_perm (fun i => i.val)
  have mh : List.ofFn (fun i => (pm i).val) ∈ (List.range k).permutations' := by
    apply List.mem_permutations'.mpr
    have en : List.ofFn (fun i : Fin k => i.val) = List.range k := by interval_cases k <;> rfl
    change (List.ofFn (fun i => (pm i).val)).Perm (List.ofFn (fun i : Fin k => i.val)) at hp
    rw [en] at hp
    exact hp
  have sub : ∀ m∈(List.range k).permutations', ∃ i : Fin 10, choice i.val = m := by
    interval_cases k <;> decide
  obtain ⟨i,hi⟩ := sub _ mh
  refine ⟨path n i.val,?_⟩
  rw [←hi]
  exact checked ⟨n,by omega⟩ i (by simpa [hi])

theorem permutation_tiny {n k : ℕ} (hn : n≤56) (hk : k=2 ∨ k=3) (h : 2*k≤n)
    (pm : Equiv.Perm (Fin k)) : ∃ p, Schedule n (List.ofFn (fun i => (pm i).val)) p :=
  permutation_upto_three hn (by omega) h pm

end Erdos473MatchingSchedule

end

section

/- Substitute actual prime-sum boundary words into a finite compressed schedule. -/

namespace Erdos473CleanShell

open Erdos473MatchingSchedule

namespace Boundary

variable {N n k : ℕ} (B : Boundary N n k)

def matchingList := List.ofFn fun i : Fin k => (B.pairing i).val

def baseWord (i : ℕ) : List ℕ :=
  if i < n-2*k then [i+1] else if h : i-(n-2*k) < k then B.word ⟨i-(n-2*k),h⟩ else []

def oriented (a : ℕ × Bool) := if a.2 then (B.baseWord a.1).reverse else B.baseWord a.1

lemma baseEnds (hk : 2*k ≤ n) {i : ℕ} (hi : i < n-k) :
    (B.baseWord i).head?=some (ends n B.matchingList i).1 ∧
    (B.baseWord i).getLast?=some (ends n B.matchingList i).2 := by
  by_cases h : i < n-2*k
  · simp [baseWord,matchingList,ends,h]
  · have h' : i-(n-2*k) < k := by omega
    have h1 := B.head ⟨i-(n-2*k),h'⟩
    have h2 := B.tail ⟨i-(n-2*k),h'⟩
    simpa [baseWord,matchingList,ends,h,h',List.getElem?_eq_getElem] using And.intro h1 h2

lemma oriented_ends (hk : 2*k ≤ n) (a : ℕ × Bool) (ha : a.1 < n-k) :
    (B.oriented a).head?=some (first n B.matchingList a) ∧
    (B.oriented a).getLast?=some (last n B.matchingList a) := by
  cases a with
  | mk i b =>
    have e := B.baseEnds hk ha
    cases b <;> simp_all [oriented,first,last]

lemma base_unique (hk : 2*k ≤ n) {i j x : ℕ} (hi : i < n-k) (hj : j < n-k)
    (hx : x∈B.baseWord i) (hy : x∈B.baseWord j) : i=j := by
  by_cases a : i < n-2*k <;> by_cases b : j < n-2*k
  · simp [baseWord,a] at hx; simp [baseWord,b] at hy; omega
  · have hj' : j-(n-2*k) < k := by omega
    simp [baseWord,a] at hx; simp [baseWord,b,hj'] at hy
    have := (B.covers x).mp ⟨_,hy⟩
    omega
  · have hi' : i-(n-2*k) < k := by omega
    simp [baseWord,a,hi'] at hx; simp [baseWord,b] at hy
    have := (B.covers x).mp ⟨_,hx⟩
    omega
  · have hi' : i-(n-2*k) < k := by omega
    have hj' : j-(n-2*k) < k := by omega
    simp [baseWord,a,hi'] at hx; simp [baseWord,b,hj'] at hy
    by_contra ne
    exact B.disjoint _ _ (fun eq => by have z := congrArg Fin.val eq; simp at z; omega) hx hy

lemma oriented_mem (a : ℕ × Bool) (x : ℕ) : x∈B.oriented a ↔ x∈B.baseWord a.1 := by
  unfold oriented; split <;> simp

lemma base_props (hk : 2*k ≤ n) (i : ℕ) (hi : i < n-k) :
    (B.baseWord i).Nodup ∧ (B.baseWord i).IsChain (fun x y => (x+y).Prime) := by
  by_cases a : i < n-2*k
  · simp [baseWord,a]
  · have h : i-(n-2*k) < k := by omega
    simpa only [baseWord,if_neg a,dif_pos h] using And.intro (B.simple ⟨_,h⟩) (B.edges ⟨_,h⟩)

theorem realize (hN : n ≤ N) (hk : 2*k ≤ n) (l : List (ℕ × Bool))
    (cert : Schedule n B.matchingList l) : Erdos473CoinPaths.ListPath N := by
  have pm : (l.map Prod.fst).Perm (List.range (n-k)) := by simpa [matchingList] using cert.1
  have valid {a : ℕ × Bool} (ha : a∈l) : a.1 < n-k :=
    List.mem_range.mp (pm.mem_iff.mp (List.mem_map.mpr ⟨a,ha,rfl⟩))
  have covers (i : ℕ) (hi : i < n-k) : ∃ a∈l, a.1=i :=
    List.mem_map.mp (pm.mem_iff.mpr (List.mem_range.mpr hi))
  refine ⟨l.flatMap B.oriented,List.nodup_flatMap.mpr ⟨?_,?_⟩,?_,?_⟩
  · intro a ha
    have e := (B.base_props hk _ (valid ha)).1
    unfold oriented
    split <;> simpa using e
  · have p := (List.pairwise_map.mp (show (l.map Prod.fst).Nodup from pm.symm.nodup List.nodup_range))
    apply p.imp_of_mem
    intro a b ha hb diff x xh yh
    exact diff (B.base_unique hk (valid ha) (valid hb) ((B.oriented_mem _ _).mp xh) ((B.oriented_mem _ _).mp yh))
  · intro x
    constructor
    · intro h
      obtain ⟨a,ha,hx⟩ := List.mem_flatMap.mp h
      have h := (B.oriented_mem _ _).mp hx
      have v := valid ha
      by_cases sm : a.1 < n-2*k
      · simp [baseWord,sm] at h; omega
      · have e : a.1-(n-2*k) < k := by omega
        simp [baseWord,sm,e] at h
        have := (B.covers x).mp ⟨_,h⟩
        omega
    · intro hx
      by_cases sm : x ≤ n-2*k
      · obtain ⟨a,ha,e⟩ := covers (x-1) (by omega)
        refine List.mem_flatMap.mpr ⟨a,ha,(B.oriented_mem _ _).mpr ?_⟩
        simp [e,baseWord,show x-1 < n-2*k by omega,show x-1+1=x by omega]
      · obtain ⟨i,hi⟩ := (B.covers x).mpr ⟨by omega,hx.2⟩
        obtain ⟨a,ha,e⟩ := covers (n-2*k+i.val) (by have := i.isLt; omega)
        refine List.mem_flatMap.mpr ⟨a,ha,(B.oriented_mem _ _).mpr ?_⟩
        simpa [e,baseWord,show ¬n-2*k+i.val < n-2*k by omega] using hi
  · change ((l.map B.oriented).flatten).IsChain _
    apply (List.isChain_flatten (by
      intro he
      obtain ⟨a,ha,e⟩ := List.mem_map.mp he
      have h := (B.oriented_ends hk a (valid ha)).1
      simp [e] at h)).mpr
    constructor
    · intro w hw
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
      have e := (B.base_props hk _ (valid ha)).2
      unfold oriented
      split
      · rw [List.isChain_reverse]; simpa only [Nat.add_comm] using e
      · exact e
    · rw [List.isChain_map]
      rw [List.isChain_iff_getElem]
      intro i hi
      have e := (List.isChain_iff_getElem.mp cert.2) i hi
      exact link_of (B.oriented_ends hk _ (valid (List.getElem_mem _))).2
        (B.oriented_ends hk _ (valid (List.getElem_mem _))).1 e

theorem finite_of_schedule (hN : n≤N) (hk : 2*k≤n) (l : List (ℕ × Bool))
    (cert : Schedule n B.matchingList l) : Erdos473CoinPaths.PathAt N := by
  obtain ⟨w,wd,wm,we⟩ := B.realize hN hk l cert
  exact Erdos473Twin.perm_of_list N w wd wm we

include B in
theorem tiny_path (hN : n≤N) (hn : n≤56) (hk : 2*k≤n) (ks : k=2 ∨ k=3) :
    Erdos473CoinPaths.PathAt N := by
  obtain ⟨l,h⟩ := Erdos473MatchingSchedule.permutation_tiny hn ks hk B.pairing
  exact B.finite_of_schedule hN hk l h

theorem zero_order {N n : ℕ} (B : Boundary N n 0) (hN : n≤N) : N=n := by
  by_contra ne
  obtain ⟨i,_⟩ := (B.covers N).mpr (by omega)
  exact Fin.elim0 i

end Boundary
end Erdos473CleanShell

end

section

/- Arithmetic step interface for the prescribed-matching induction. -/

namespace Erdos473MatchingInduction

def SizeBound (C : ℝ) (n k : ℕ) : Prop :=
  (k:ℝ) ≤ C*(Real.log (2*(n:ℝ)))^3

def Next (C : ℝ) (n m j : ℕ) : Prop :=
  m<n ∧ 2≤ m ∧ SizeBound C m j ∧ 10000*j≤ m

inductive BigStep (C : ℝ) (n k : ℕ) : Prop
  | grow (u t d : ℕ) (size : n=u+2*t) (hd : 0<d) (room : 2*k+d≤t)
      (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime)
      (next : Next C n (u+2*k+2*d) (k+d))
  | shrink (u t d e : ℕ) (size : n=u+2*t) (hd : 0<d) (room : 2*k+d≤t)
      (space : 2*d+e≤k) (de : d≤e)
      (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime) (r : (n+u+1+2*d+2*e).Prime)
      (next : Next C n (u+2*k) (k-d))

end Erdos473MatchingInduction

end

section

/- Independently switching each marked top preimage while using only three prime sums. -/

namespace Erdos473IndependentTile

open Erdos473RepairPermutation

def swapNat (k d e : ℕ) (bits : ℕ → Bool) (i : ℕ) : ℕ :=
  if k-d ≤ i then if bits (i-(k-d)) then i-(d+e) else i
  else if k-2*d-e ≤ i ∧ i < k-d-e then if bits (i-(k-2*d-e)) then i+d+e else i
  else i

lemma swap_high {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) {r : ℕ} (hr : r < d) :
    swapNat k d e bits (k-d+r) = if bits r then k-2*d-e+r else k-d+r := by
  unfold swapNat
  rw [if_pos (by omega),show k-d+r-(k-d)=r by omega]
  split <;> omega

lemma swap_low {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) {r : ℕ} (hr : r < d) :
    swapNat k d e bits (k-2*d-e+r) = if bits r then k-d+r else k-2*d-e+r := by
  unfold swapNat
  rw [if_neg (by omega),if_pos (by constructor <;> omega),show k-2*d-e+r-(k-2*d-e)=r by omega]
  split <;> omega

lemma swap_mid {k d e i : ℕ} (bits : ℕ → Bool) (h₁ : i < k-d)
    (h₂ : i < k-2*d-e ∨ k-d-e ≤ i) : swapNat k d e bits i=i := by
  unfold swapNat
  rw [if_neg (by omega),if_neg (by omega)]

lemma swap_invol {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool)
    {i : ℕ} (hi : i < k) : swapNat k d e bits (swapNat k d e bits i)=i := by
  by_cases a : k-d ≤ i
  · let r := i-(k-d)
    have hr : r < d := by dsimp [r]; omega
    have eq : i=k-d+r := by dsimp [r]; omega
    rw [eq,swap_high room de bits hr]
    cases h : bits r <;> simp [h,swap_high room de bits hr,swap_low room de bits hr]
  by_cases b : k-2*d-e ≤ i ∧ i < k-d-e
  · let r := i-(k-2*d-e)
    have hr : r < d := by dsimp [r]; omega
    have eq : i=k-2*d-e+r := by dsimp [r]; omega
    rw [eq,swap_low room de bits hr]
    cases h : bits r <;> simp [h,swap_high room de bits hr,swap_low room de bits hr]
  rw [swap_mid bits (by omega : i < k-d) (by omega),swap_mid bits (by omega : i < k-d) (by omega)]

def swapFin {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) (i : Fin k) : Fin k :=
  ⟨swapNat k d e bits i.val, by unfold swapNat; split_ifs <;> omega⟩

def swapEquiv {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) : Equiv.Perm (Fin k) where
  toFun := swapFin room de bits
  invFun := swapFin room de bits
  left_inv i := Fin.ext (swap_invol room de bits i.isLt)
  right_inv i := Fin.ext (swap_invol room de bits i.isLt)

def perm {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) : Equiv.Perm (Fin k) :=
  (swapEquiv room de bits).trans ((tile k d e (by omega)).trans (swapEquiv room de bits))

lemma preimage {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) (r : Fin d) :
    ((perm room de bits).symm (high (by omega) r)).val =
      if bits r.val then k-d+r.val else k-d-e+r.val := by
  change swapNat k d e bits
    (if swapNat k d e bits (k-d+r.val) < k-d-e then swapNat k d e bits (k-d+r.val)
     else if swapNat k d e bits (k-d+r.val) < k-d then swapNat k d e bits (k-d+r.val)+d
     else swapNat k d e bits (k-d+r.val)-e) = _
  rw [swap_high room de bits r.isLt]
  cases h : bits r.val
  · simp only [Bool.false_eq_true,if_false]
    rw [if_neg (by omega),if_neg (by omega),swap_mid bits (by omega) (by omega)]
    omega
  · simp only [if_true]
    rw [if_pos (by omega),swap_low room de bits r.isLt,h]
    rfl

lemma displacement {k d e : ℕ} (room : 2*d+e ≤ k) (de : d ≤ e) (bits : ℕ → Bool) (i : Fin k) :
    let j := ((perm room de bits) i).val
    j=i.val ∨ j=i.val+e ∨ j+d=i.val := by
  let x := i.val
  let T := fun i : ℕ => if i < k-d-e then i else if i < k-e then i+e else i-d
  change swapNat k d e bits (T (swapNat k d e bits x))=x ∨
    swapNat k d e bits (T (swapNat k d e bits x))=x+e ∨ swapNat k d e bits (T (swapNat k d e bits x))+d=x
  have hx : x < k := i.isLt
  by_cases a : k-d ≤ x
  · let r := x-(k-d)
    have hr : r < d := by dsimp [r]; omega
    have eq : x=k-d+r := by dsimp [r]; omega
    rw [eq,swap_high room de bits hr]
    have lo : T (k-2*d-e+r)=k-2*d-e+r := by dsimp [T]; split_ifs <;> omega
    have hi : T (k-d+r)=k-d+r-d := by dsimp [T]; split_ifs <;> omega
    cases h : bits r <;> simp only [Bool.false_eq_true,if_false,if_true,lo,hi]
    · rw [swap_mid bits (by omega) (by omega)]; omega
    · rw [swap_low room de bits hr,h]; simp
  by_cases b : k-2*d-e ≤ x ∧ x < k-d-e
  · let r := x-(k-2*d-e)
    have hr : r < d := by dsimp [r]; omega
    have eq : x=k-2*d-e+r := by dsimp [r]; omega
    rw [eq,swap_low room de bits hr]
    have lo : T (k-2*d-e+r)=k-2*d-e+r := by dsimp [T]; split_ifs <;> omega
    have hi : T (k-d+r)=k-d+r-d := by dsimp [T]; split_ifs <;> omega
    cases h : bits r <;> simp only [Bool.false_eq_true,if_false,if_true,lo,hi]
    · rw [swap_low room de bits hr,h]; simp
    · rw [swap_mid bits (by omega) (by omega)]; omega
  rw [swap_mid bits (by omega : x < k-d) (by omega)]
  by_cases l : x < k-d-e
  · rw [show T x=x by simp [T,l],swap_mid bits (by omega) (by omega)]
    exact Or.inl rfl
  by_cases m : x < k-e
  · rw [show T x=x+e by simp [T,l,m]]
    let r := x+e-(k-d)
    have hr : r < d := by dsimp [r]; omega
    have eq : x+e=k-d+r := by dsimp [r]; omega
    rw [eq,swap_high room de bits hr]
    split <;> omega
  · rw [show T x=x-d by simp [T,l,m],swap_mid bits (by omega) (by omega)]
    omega

theorem prime_edge {n u k d e : ℕ} (hn : 2*k ≤ n) (room : 2*d+e ≤ k) (de : d ≤ e)
    (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime) (r : (n+u+1+2*d+2*e).Prime)
    (bits : ℕ → Bool) (i : Fin k) :
    (n-2*i.val+(u+1+2*d+2*((perm room de bits) i).val)).Prime := by
  rcases displacement room de bits i with h | h | h
  · convert q using 1 <;> omega
  · convert r using 1 <;> omega
  · convert p using 1 <;> omega

end Erdos473IndependentTile

end

section

/- Two disjoint systems of pairs admit independent, noncolliding representatives. -/

namespace Erdos473RepairMasks

open Finset

lemma double_le {ι α : Type*} [DecidableEq α] (s : Finset ι) (U : Finset α)
    (f g : ι ↪ α) (apart : ∀ i j, f i ≠ g j)
    (hf : ∀ i∈s, f i ∈ U) (hg : ∀ i∈s, g i ∈ U) : s.card+s.card ≤ U.card := by
  classical
  have d : Disjoint (s.map f) (s.map g) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,_,eq⟩ := Finset.mem_map.mp hy
    exact apart i j eq.symm
  have sub : s.map f ∪ s.map g ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with ha|ha
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      exact hf i hi
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      exact hg i hi
  simpa [Finset.card_union_of_disjoint d] using Finset.card_le_card sub

theorem independent_masks {d k : ℕ} (L0 L1 R0 R1 : Fin d ↪ Fin k) (M : Fin k ≃ Fin k)
    (hL : ∀ i j, L0 i ≠ L1 j) (hR : ∀ i j, R0 i ≠ R1 j) :
    ∃ bl br : Fin d → Bool, ∀ i j, M (if bl i then L1 i else L0 i) ≠
      (if br j then R1 j else R0 j) := by
  classical
  let t : Fin d ⊕ Fin d → Finset (Fin k) :=
    Sum.elim (fun i => {M (L0 i), M (L1 i)}) (fun j => {R0 j,R1 j})
  have hall (s : Finset (Fin d ⊕ Fin d)) : s.card ≤ (s.biUnion t).card := by
    have left := double_le s.toLeft (s.biUnion t) (L0.trans M.toEmbedding) (L1.trans M.toEmbedding)
      (fun i j h => hL i j (M.injective h))
      (fun i hi => Finset.mem_biUnion.mpr ⟨Sum.inl i,Finset.mem_toLeft.mp hi,by simp [t]⟩)
      (fun i hi => Finset.mem_biUnion.mpr ⟨Sum.inl i,Finset.mem_toLeft.mp hi,by simp [t]⟩)
    have right := double_le s.toRight (s.biUnion t) R0 R1 hR
      (fun i hi => Finset.mem_biUnion.mpr ⟨Sum.inr i,Finset.mem_toRight.mp hi,by simp [t]⟩)
      (fun i hi => Finset.mem_biUnion.mpr ⟨Sum.inr i,Finset.mem_toRight.mp hi,by simp [t]⟩)
    have eq := Finset.card_toLeft_add_card_toRight (u := s)
    omega
  obtain ⟨f,hf,hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  let bl := fun i => decide (f (Sum.inl i) = M (L1 i))
  let br := fun j => decide (f (Sum.inr j) = R1 j)
  have left (i) : M (if bl i then L1 i else L0 i) = f (Sum.inl i) := by
    have mem := hm (Sum.inl i)
    simp only [t,Sum.elim_inl,Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with e|e
    · have ne : f (Sum.inl i) ≠ M (L1 i) := fun eq => hL i i (M.injective (e.symm.trans eq))
      simp [bl,ne,e.symm]
    · simp [bl,e]
  have right (j) : (if br j then R1 j else R0 j) = f (Sum.inr j) := by
    have mem := hm (Sum.inr j)
    simp only [t,Sum.elim_inr,Finset.mem_insert,Finset.mem_singleton] at mem
    rcases mem with e|e
    · have ne : f (Sum.inr j) ≠ R1 j := fun eq => hR j j (e.symm.trans eq)
      simp [br,ne,e.symm]
    · simp [br,e]
  refine ⟨bl,br,?_⟩
  intro i j eq
  have bad := hf ((left i).symm.trans (eq.trans (right j)))
  cases bad

end Erdos473RepairMasks

end

section

/- Every arbitrary prescribed matching contracts using a single suitable triple of primes. -/

namespace Erdos473CleanShell

open Erdos473IndependentTile Erdos473RepairPermutation

def nearEmb {k d e : ℕ} (room : 2*d+e≤k) : Fin d ↪ Fin k where
  toFun r := ⟨k-d-e+r.val,by omega⟩
  inj' r s eq := by apply Fin.ext; have h := congrArg Fin.val eq; dsimp at h; omega

def extendMask {d : ℕ} (b : Fin d → Bool) (i : ℕ) := if h : i<d then b ⟨i,h⟩ else false

lemma mask_pre {k d e : ℕ} (room : 2*d+e≤k) (de : d≤e) (b : Fin d → Bool) (i : Fin d) :
    (perm room de (extendMask b)).symm (high (by omega) i) =
      if b i then high (by omega) i else nearEmb room i := by
  apply Fin.ext
  rw [preimage]
  simp only [extendMask,dif_pos i.isLt,Fin.eta]
  cases b i <;> rfl

theorem triple_contract {N n u t k d e : ℕ} (old : Boundary N n k) (hN : n≤N)
    (size : n=u+2*t) (hd : 0<d) (room : 2*k+d≤t)
    (space : 2*d+e≤k) (de : d≤e)
    (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime) (r : (n+u+1+2*d+2*e).Prime) :
    Nonempty (Boundary N (u+2*k) (k-d)) := by
  have dk : d≤k := by omega
  have dis : ∀ i j : Fin d, nearEmb space i≠highEmb dk j := by
    intro i j he
    have z := congrArg Fin.val he
    change k-d-e+i.val=k-d+j.val at z
    omega
  obtain ⟨bl,br,sep⟩ := Erdos473RepairMasks.independent_masks (nearEmb space) (highEmb dk)
    (nearEmb space) (highEmb dk) old.pairing dis dis
  let π := perm space de (extendMask bl)
  let ρ := perm space de (extendMask br)
  apply contract_permuted old hN size hd dk room p q π ρ
  · exact prime_edge (by omega : 2*k≤n) space de p q r (extendMask bl)
  · intro j
    have h := prime_edge (by omega : 2*k≤n) space de p q r (extendMask br) j
    change (n-2*j.val+(u+1+2*d+2*(ρ j).val)).Prime at h
    change (n-(2*j.val+1)+(u+2+2*d+2*(ρ j).val)).Prime
    convert h using 1 <;> omega
  · intro i j
    change old.pairing ((perm space de (extendMask bl)).symm (high dk i))≠
      (perm space de (extendMask br)).symm (high dk j)
    rw [mask_pre,mask_pre]
    exact sep i j

end Erdos473CleanShell

end

section

/- The all-p expansion of an arbitrary prescribed boundary. -/

namespace Erdos473CleanShell

def emptyBoundary (n : ℕ) : Boundary n n 0 where
  pairing := Equiv.refl _
  word := Fin.elim0
  head i := Fin.elim0 i
  tail i := Fin.elim0 i
  simple i := Fin.elim0 i
  edges i := Fin.elim0 i
  disjoint i := Fin.elim0 i
  covers x := by simp

def descending {N s m : ℕ} (mu : Equiv.Perm (Fin m)) (row : Fin m → List ℕ)
    (hd : ∀ i, (row i).head?=some (s+2*i.val+1))
    (tl : ∀ i, (row i).getLast?=some (s+2*(mu i).val+2))
    (nd : ∀ i, (row i).Nodup) (ed : ∀ i, (row i).IsChain (fun x y => (x+y).Prime))
    (sep : ∀ i j, i≠j → (row i).Disjoint (row j))
    (cov : ∀ x, (∃ i, x∈row i) ↔ s < x ∧ x ≤ N) : Boundary N (s+2*m) m where
  pairing := (Fin.revPerm.trans mu.symm).trans Fin.revPerm
  word i := (row (mu.symm i.rev)).reverse
  head i := by
    rw [List.head?_reverse,tl,mu.apply_symm_apply]
    apply congrArg some
    change s+2*(m-(i.val+1))+2=_
    omega
  tail i := by
    rw [List.getLast?_reverse,hd]
    apply congrArg some
    change _=s+2*m-(2*(m-((mu.symm i.rev).val+1))+1)
    omega
  simple i := by simpa only [List.nodup_reverse] using nd (mu.symm i.rev)
  edges i := by rw [List.isChain_reverse]; simpa only [Nat.add_comm] using ed (mu.symm i.rev)
  disjoint i j ne x hi hj := sep _ _ (fun e => ne (Fin.rev_injective (mu.symm.injective e)))
    (List.mem_reverse.mp hi) (List.mem_reverse.mp hj)
  covers x := by
    simp only [Nat.add_sub_cancel,List.mem_reverse]
    rw [←cov]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨_,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨(mu i).rev,by simpa using hi⟩

theorem expand {N n u t k d : ℕ} (old : Boundary N n k) (hN : n≤N)
    (size : n=u+2*t) (hd : 0<d) (room : 2*k+d≤t)
    (p : (n+u+1).Prime) (q : (n+u+1+2*d).Prime) :
    Nonempty (Boundary N (u+2*k+2*d) (k+d)) := by
  let len := t-2*k
  have eq : u+2*k+2*len=n-2*k := by dsimp [len]; omega
  have pe : 2*(u+2*k)+2*len+1=n+u+1 := by dsimp [len]; omega
  obtain ⟨G,hs,hu⟩ := Erdos473Shell.shell_decomposition (u+2*k) len d hd (by dsimp [len]; omega)
    (pe ▸ p) (by simpa only [pe] using q)
  let f (r : Fin d) : Fin d := ⟨(len-1-r.val)%d,Nat.mod_lt _ hd⟩
  have inj : Function.Injective f := by
    intro a b h
    have e := congrArg Fin.val h
    change (len-1-a.val)%d=(len-1-b.val)%d at e
    have ha := List.mem_of_getLast? (hs a).2.2.2.1
    have hb := List.mem_of_getLast? (hs b).2.2.2.1
    rw [e] at ha
    exact (hu _ ((hs b).2.2.2.2 _ hb)).unique ha hb
  let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj)
  let mu := (finSumFinEquiv.symm.trans (old.pairing.sumCongr σ)).trans finSumFinEquiv
  let LL (i : Fin k) := u+2*i.val+1
  let RR (j : Fin k) := u+2*j.val+2
  let H (i : Fin k) := LL i :: (old.word i ++ [RR (old.pairing i)])
  let F : Fin (k+d) → List ℕ := Fin.addCases H G
  have fl (i : Fin k) : F (Fin.castAdd d i)=H i := Fin.addCases_left _
  have fr (r : Fin d) : F (Fin.natAdd k r)=G r := Fin.addCases_right _
  have ml (i : Fin k) : mu (Fin.castAdd d i)=Fin.castAdd d (old.pairing i) := by simp [mu]
  have mr (r : Fin d) : mu (Fin.natAdd k r)=Fin.natAdd k (σ r) := by simp [mu]
  have lb (i : Fin k) : u<LL i ∧ LL i≤u+2*k := by dsimp [LL]; omega
  have rb (j : Fin k) : u<RR j ∧ RR j≤u+2*k := by dsimp [RR]; omega
  have ob (a : Fin k) {x : ℕ} (hx : x∈old.word a) := (old.covers x).mp ⟨a,hx⟩
  have gb (r : Fin d) {x : ℕ} (hx : x∈G r) : u+2*k<x ∧ x≤n-2*k := by
    simpa only [eq] using (hs r).2.2.2.2 x hx
  have memH (i : Fin k) (x : ℕ) : x∈H i ↔ x=LL i ∨ x∈old.word i ∨ x=RR (old.pairing i) := by simp [H]
  have disHG (i : Fin k) (r : Fin d) : (H i).Disjoint (G r) := by
    intro x hx gx
    have g := gb r gx
    rcases (memH i x).mp hx with a|a|a
    · have := lb i; omega
    · have := ob i a; omega
    · have := rb (old.pairing i); omega
  have LL_RR (i j : Fin k) : LL i≠RR j := by dsimp [LL,RR]; omega
  rw [show u+2*k+2*d=u+2*(k+d) by omega]
  refine ⟨descending mu F ?_ ?_ ?_ ?_ ?_ ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun r => ?_)
    · rw [fl]; rfl
    · rw [fr]; simpa [Nat.mul_add,Nat.add_assoc] using (hs r).2.2.1
  · refine Fin.addCases (fun i => ?_) (fun r => ?_)
    · rw [fl,ml]; simp [H,RR,List.getLast?_cons,List.getLast?_append]
    · rw [fr,mr]; convert (hs r).2.2.2.1 using 2; dsimp [σ,f]; omega
  · refine Fin.addCases (fun i => ?_) (fun r => ?_)
    · rw [fl,List.nodup_cons,List.nodup_append]
      have a : LL i ∉ old.word i := by intro e; have := ob i e; have := lb i; omega
      have b : RR (old.pairing i) ∉ old.word i := by intro e; have := ob i e; have := rb (old.pairing i); omega
      simp [a,LL_RR,old.simple]
      rintro _ h rfl
      exact b h
    · rw [fr]; exact (hs r).1
  · refine Fin.addCases (fun i => ?_) (fun r => ?_)
    · rw [fl]
      change (([LL i]++old.word i)++[RR (old.pairing i)]).IsChain _
      apply List.IsChain.append_overlap _ _ (by intro ne; have a := old.head i; simp [ne] at a)
      · exact List.isChain_append.mpr ⟨by simp,old.edges i,link_of (a:=LL i) rfl (old.head i)
          (by convert p using 1 <;> dsimp [LL] <;> omega)⟩
      · exact List.isChain_append.mpr ⟨old.edges i,by simp,link_of (b:=RR (old.pairing i)) (old.tail i) rfl
          (by convert p using 1 <;> dsimp [RR] <;> have := (old.pairing i).isLt <;> omega)⟩
    · rw [fr]; exact (hs r).2.1
  · refine Fin.addCases (fun i => ?_) (fun r => ?_)
    · refine Fin.addCases (fun j => ?_) (fun s => ?_)
      · rw [fl,fl]; intro ne x h g
        have ij : i≠j := fun e => ne (congrArg (Fin.castAdd d) e)
        rcases (memH i x).mp h with a|a|a <;> rcases (memH j x).mp g with b|b|b
        · apply ij; apply Fin.ext; dsimp [LL] at a b; omega
        · have := lb i; have := ob j b; omega
        · exact LL_RR i (old.pairing j) (a.symm.trans b)
        · have := ob i a; have := lb j; omega
        · exact old.disjoint i j ij a b
        · have := ob i a; have := rb (old.pairing j); omega
        · exact LL_RR j (old.pairing i) (b.symm.trans a)
        · have := rb (old.pairing i); have := ob j b; omega
        · apply ij; apply old.pairing.injective; apply Fin.ext; dsimp [RR] at a b; omega
      · rw [fl,fr]; exact fun _ => disHG i s
    · refine Fin.addCases (fun j => ?_) (fun s => ?_)
      · rw [fr,fl]; exact fun _ => (disHG j r).symm
      · rw [fr,fr]; intro ne x h g
        exact ne (congrArg (Fin.natAdd k) ((hu _ ((hs r).2.2.2.2 x h)).unique h g))
  · intro x
    constructor
    · rintro ⟨i,hi⟩
      refine Fin.addCases (fun j hj => ?_) (fun r hr => ?_) i hi
      · rcases (memH j x).mp (fl j ▸ hj) with a|a|a
        · have := lb j; omega
        · have := ob j a; omega
        · have := rb (old.pairing j); omega
      · have := gb r (fr r ▸ hr); omega
    · intro hx
      by_cases small : x≤u+2*k
      · let i : Fin k := ⟨(x-u-1)/2,by omega⟩
        by_cases odd : (x-u-1)%2=0
        · refine ⟨Fin.castAdd d i,(fl i).symm ▸ (memH i x).mpr (Or.inl ?_)⟩
          dsimp [LL,i]; omega
        · let j := old.pairing.symm i
          refine ⟨Fin.castAdd d j,(fl j).symm ▸ (memH j x).mpr (Or.inr (Or.inr ?_))⟩
          dsimp [RR,j]; rw [old.pairing.apply_symm_apply]; dsimp [i]; omega
      by_cases middle : x≤n-2*k
      · obtain ⟨r,hr,_⟩ := hu x (by rw [eq]; omega)
        exact ⟨Fin.natAdd k r,(fr r).symm ▸ hr⟩
      · obtain ⟨i,hi⟩ := (old.covers x).mpr (by omega)
        exact ⟨Fin.castAdd d i,(fl i).symm ▸ (memH i x).mpr (Or.inr (Or.inl hi))⟩

end Erdos473CleanShell

end

section

/- Strong induction for the finite prime-sum Hamilton path from arithmetic shell steps. -/

namespace Erdos473MatchingInduction

open Erdos473CleanShell Erdos473CoinPaths

def Solvable (n k : ℕ) : Prop := ∀ N, n≤N → Boundary N n k → PathAt N

theorem solve_of_steps {B : ℕ} {C : ℝ}
    (small : ∀ n k, 2≤n → n≤B → 2*k≤n → (k≤3 ∨ 10000*k≤n) → Solvable n k)
    (big : ∀ n k, B<n → 2≤n → SizeBound C n k → 10000*k≤n → BigStep C n k)
    (n k : ℕ) (hn : 2≤n) (cap : SizeBound C n k) (thin : 10000*k≤n) :
    Solvable n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases low : n≤B
    · exact small n k hn low (by omega) (Or.inr thin)
    intro N hN old
    cases big n k (by omega) hn cap thin with
    | grow u t d size hd room p q step =>
      obtain ⟨lt,lo,cap',thin'⟩ := step
      obtain ⟨out⟩ := expand old hN size hd room p q
      exact ih _ lt _ lo cap' thin' N (by omega) out
    | shrink u t d e size hd room space de p q r step =>
      obtain ⟨lt,lo,cap',thin'⟩ := step
      obtain ⟨out⟩ := triple_contract old hN size hd room space de p q r
      exact ih _ lt _ lo cap' thin' N (by omega) out

theorem finite_of_steps {B : ℕ} {C : ℝ} (positive : 0≤C)
    (small : ∀ n k, 2≤n → n≤B → 2*k≤n → (k≤3 ∨ 10000*k≤n) → Solvable n k)
    (big : ∀ n k, B<n → 2≤n → SizeBound C n k → 10000*k≤n → BigStep C n k) :
    type_of% @Erdos473.erdos_473.variants.finite := by
  intro n hn
  have c : SizeBound C n 0 := by
    unfold SizeBound
    have h : 1≤2*(n:ℝ) := by exact_mod_cast (show 1≤2*n by omega)
    simpa using mul_nonneg positive (pow_nonneg (Real.log_nonneg h) 3)
  exact solve_of_steps small big n 0 hn c (by omega) n le_rfl (emptyBoundary n)

end Erdos473MatchingInduction

end

section

/- Interpret each verified finite-state move as an actual prime-sum Hamiltonian construction. -/

namespace Erdos473MatchingInduction

open Erdos473CleanShell Erdos473CoinPaths

/-- Recover shell parameters from the more compact p/2 room inequality. -/
lemma parameters {n k p d : ℕ} (np : n<p) (room : p/2+2*k+d≤n) (dp : 0<d) (pr : p.Prime) :
    let u := p-n-1
    let t := n-p/2
    n=u+2*t ∧ 2*k+d≤t ∧ n+u+1=p := by
  have odd := pr.eq_two_or_odd.resolve_left (by rintro rfl; omega)
  dsimp
  omega

theorem finite_expand (n k p : ℕ) (np : n<p) (room : p/2+2*k+1≤n)
    (pr : p.Prime) (q : (p+2).Prime) (ih : Solvable (p-n-1+2*k+2) (k+1)) :
    Solvable n k := by
  obtain ⟨size,width,pe⟩ := parameters np room (by decide : 0<1) pr
  intro N hN old
  obtain ⟨out⟩ := expand old hN size (by decide : 0<1) width (by simpa [pe]) (by simpa [pe])
  exact ih N (by omega) out

theorem finite_three (n p : ℕ) (np : n<p) (room : p/2+7≤n)
    (pr : p.Prime) (q : (p+2).Prime) (r : (p+6).Prime)
    (ih : Solvable (p-n-1+6) 2) : Solvable n 3 := by
  have room' : p/2+2*3+1≤n := by omega
  obtain ⟨size,width,pe⟩ := parameters np room' (by decide : 0<1) pr
  intro N hN old
  let off (a : Fin (1+1)) := 2*a.val
  obtain ⟨out⟩ := contract old hN size (by decide : 0<1) width (by simpa [pe]) (by simpa [pe]) off
    (fun i => by dsimp [off]; omega) (fun a b h => by dsimp [off]; omega)
    (fun a => by
      rcases a with ⟨a,ha⟩
      interval_cases a <;> simp [off,pe,q,r])
  exact ih N (by omega) out

theorem finite_contract (n k p d e : ℕ) (np : n<p) (room : p/2+2*k+d≤n)
    (hd : 0<d) (de : d≤e) (space : 2*d+e≤k) (pr : p.Prime)
    (q : (p+2*d).Prime) (r : (p+2*d+2*e).Prime)
    (ih : Solvable (p-n-1+2*k) (k-d)) : Solvable n k := by
  obtain ⟨size,width,pe⟩ := parameters np room hd pr
  intro N hN old
  obtain ⟨out⟩ := triple_contract old hN size hd width space de
    (by simpa [pe]) (by simpa [pe]) (by simpa [pe])
  exact ih N (by omega) out

end Erdos473MatchingInduction

end

section

/- Every small boundary can be joined using the certified schedule for its endpoint pairing. -/
namespace Erdos473SmallSeed
open Erdos473CleanShell Erdos473MatchingInduction

theorem all (n k : ℕ) (hn : n≤56) (hk : k≤3) (room : 2*k≤n) : Solvable n k := by
  intro N hN old
  obtain ⟨s, hs⟩ := Erdos473MatchingSchedule.permutation_upto_three hn hk room old.pairing
  exact old.finite_of_schedule hN room s hs

end Erdos473SmallSeed

end

section

/- Numeric conditions for the finite cover by matching transfer prime tuples. -/

namespace Erdos473MatchingFiniteCore

def Small (n : ℕ) : Prop :=
  ∃ p : ℕ, n<p ∧ p/2+7≤n ∧ p.Prime ∧ (p+2).Prime ∧ (p+6).Prime

def Drop (n k : ℕ) : Prop :=
  ∃ p d e : ℕ, n<p ∧ p/2+2*k+d≤n ∧ 0<d ∧ d≤e ∧ 2*d+e≤k ∧
    p.Prime ∧ (p+2*d).Prime ∧ (p+2*d+2*e).Prime ∧
    10000*(k-d) ≤ p-n-1+2*k

def Covers (lo hi : ℕ) : Prop :=
  ∀ n, lo≤n → n≤hi → Small n ∧ ∀ k, 4≤k → 10000*k≤n → Drop n k

lemma join {lo m hi : ℕ} (A : Covers lo m) (B : Covers (m+1) hi) : Covers lo hi := by
  intro n hl hh
  by_cases h : n ≤ m
  · exact A n hl h
  · exact B n (by omega) hh

def Feasible (lo hi p d e : ℕ) : Prop :=
  0<d ∧ d≤e ∧ 40000≤lo ∧ lo≤hi ∧ hi<p ∧ p/2+2*(hi/10000)+d≤lo ∧
    2*hi+1≤p+10000*d ∧ hi+9998*(2*d+e-1)≤p+9999

instance (lo hi p d e : ℕ) : Decidable (Feasible lo hi p d e) := by
  unfold Feasible; infer_instance

theorem one {lo hi p d e : ℕ} (h : Feasible lo hi p d e)
    (hp : p.Prime) (hq : (p+2).Prime) (hr : (p+6).Prime)
    (hlg : (p+2*d).Prime) (hrg : (p+2*d+2*e).Prime) : Covers lo hi := by
  obtain ⟨hd,he,hlo,lh,hp',ht,hLg,hSm⟩ := h
  intro n low high
  have small : Small n := ⟨p,by omega,by omega,hp,hq,hr⟩
  refine ⟨small,?_⟩
  intro k hk kn
  have m : k≤hi/10000 := by omega
  by_cases use : 2*d+e≤k
  · exact ⟨p,d,e,by omega,by omega,hd,he,use,hp,hlg,hrg,by omega⟩
  · exact ⟨p,1,2,by omega,by omega,by decide,by decide,hk,hp,hq,hr,by omega⟩

end Erdos473MatchingFiniteCore

end

section

/- A binary modular-power check for the finite collection of Pratt certificates. -/

namespace Erdos473CompactPratt

def residue (m a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1%m
  | k+1, e =>
    if e=0 then 1%m else
    ((residue m a k (e/2))^2 * (if e%2=1 then a else 1))%m

theorem cast_residue (m a : ℕ) : ∀ k e, e<2^k →
    (residue m a k e : ZMod m) = (a : ZMod m)^e := by
  intro k
  induction k with
  | zero =>
    intro e he
    have hz : e=0 := by simpa using he
    simp [residue,hz,ZMod.natCast_mod]
  | succ k ih =>
    intro e he
    rw [pow_succ] at he
    have hd : e/2 < 2^k := by omega
    by_cases hz : e=0
    · simp [residue,hz,ZMod.natCast_mod]
    rw [residue,if_neg hz,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow,ih _ hd,← pow_mul]
    by_cases h : e%2=1
    · rw [if_pos h,← pow_succ,show e/2*2+1=e by omega]
    · rw [if_neg h,Nat.cast_one,mul_one,show e/2*2=e by omega]

theorem certify (p a : ℕ) (fs : List ℕ) (hprod : fs.prod = p-1)
    (hfs : ∀ r ∈ fs, r.Prime) (hbound : p-1<2^96)
    (hmain : residue p a 96 (p-1)=1)
    (hparts : fs.all (fun q => decide (residue p a 96 ((p-1)/q)%p ≠ 1%p)) = true) : p.Prime := by
  apply lucas_primality p (a:ZMod p)
  · rw [← cast_residue _ _ _ _ hbound,hmain,Nat.cast_one]
  · intro q hq hd
    rw [← hprod] at hd
    obtain ⟨r,hr,hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    have eq := (Nat.prime_dvd_prime_iff_eq hq (hfs r hr)).mp hqr
    subst r
    have nh := of_decide_eq_true ((List.all_eq_true.mp hparts) q hr)
    intro one
    apply nh
    apply (ZMod.natCast_eq_natCast_iff' _ 1 p).mp
    rw [cast_residue _ _ _ _ ((Nat.div_le_self _ q).trans_lt hbound),one,Nat.cast_one]

lemma eachCons {P : ℕ → Prop} {x : ℕ} {xs : List ℕ} (h : P x ∧ ∀ y ∈ xs, P y) :
    ∀ y ∈ x::xs, P y := List.forall_mem_cons.mpr h

end Erdos473CompactPratt

end

section

/- A single soundness proof for a directed acyclic graph of primality certificates. -/

namespace Erdos473MatchingCertCore

abbrev Row := ℕ × ℕ × List ℕ
def row (xs : Array Row) (i : ℕ) : Row := xs[i]?.getD (0,0,[])
def value (xs : Array Row) (i : ℕ) : ℕ := (row xs i).1

def Correct (xs : Array Row) (i : ℕ) : Prop :=
  let x := row xs i
  let p := x.1
  let a := x.2.1
  let ids := x.2.2
  let fs := ids.map (value xs)
  p = 2 ∨ ((∀ j : ℕ, j ∈ ids → j < i) ∧ fs.prod = p-1 ∧ p-1 < 2^96 ∧
    Erdos473CompactPratt.residue p a 96 (p-1)=1 ∧
    fs.all (fun q => decide (Erdos473CompactPratt.residue p a 96 ((p-1)/q)%p ≠ 1%p)) = true)

instance (xs : Array Row) (i : ℕ) : Decidable (Correct xs i) := by unfold Correct; infer_instance

theorem prime_of_correct {xs : Array Row} (h : ∀ j < xs.size, Correct xs j)
    (i : ℕ) (hi : i<xs.size) : (value xs i).Prime := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain he|⟨hlt,prod,bound,full,parts⟩ := h i hi
    · change (row xs i).1.Prime
      rw [he]
      decide
    · refine Erdos473CompactPratt.certify _ _ _ prod ?_ bound full parts
      intro v hv
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      exact ih j (hlt j hj) (lt_trans (hlt j hj) hi)

end Erdos473MatchingCertCore

end

section

/- The sorted primality DAG for all bounded matching transfer certificates. -/

namespace Erdos473MatchingPrimeDAG
open Erdos473MatchingCertCore
def block0 : Array Row := #[
(2,0,[]),
(3,2,[0]),
(5,2,[0,0]),
(7,3,[0,1]),
(11,2,[0,2]),
(13,2,[0,0,1]),
(17,3,[0,0,0,0]),
(19,2,[0,1,1]),
(23,5,[0,4]),
(29,2,[0,0,3]),
(31,3,[0,1,2]),
(37,2,[0,0,1,1]),
(41,6,[0,0,0,2]),
(43,3,[0,1,3]),
(47,5,[0,8]),
(53,2,[0,0,5]),
(59,2,[0,9]),
(61,2,[0,0,1,2]),
(67,2,[0,1,4]),
(71,7,[0,2,3]),
(73,5,[0,0,0,1,1]),
(79,3,[0,1,5]),
(83,2,[0,12]),
(89,3,[0,0,0,4]),
(97,5,[0,0,0,0,0,1]),
(101,2,[0,0,2,2]),
(103,5,[0,1,6]),
(107,2,[0,15]),
(109,6,[0,0,1,1,1]),
(113,3,[0,0,0,0,3]),
(127,3,[0,1,1,3]),
(131,2,[0,2,5]),
(137,3,[0,0,0,6]),
(139,2,[0,1,8]),
(149,2,[0,0,11]),
(151,6,[0,1,2,2]),
(157,5,[0,0,1,5]),
(163,2,[0,1,1,1,1]),
(167,5,[0,22]),
(173,2,[0,0,13]),
(179,2,[0,23]),
(181,2,[0,0,1,1,2]),
(191,19,[0,2,7]),
(193,5,[0,0,0,0,0,0,1]),
(197,2,[0,0,3,3]),
(199,3,[0,1,1,4]),
(211,2,[0,1,2,3]),
(223,3,[0,1,11]),
(227,2,[0,29]),
(229,6,[0,0,1,7]),
(233,3,[0,0,0,9]),
(239,7,[0,3,6]),
(241,7,[0,0,0,0,1,2]),
(251,6,[0,2,2,2]),
(257,3,[0,0,0,0,0,0,0,0]),
(263,5,[0,31]),
(269,2,[0,0,18]),
(271,6,[0,1,1,1,2]),
(277,5,[0,0,1,8]),
(281,3,[0,0,0,2,3]),
(283,3,[0,1,14]),
(293,2,[0,0,20]),
(307,5,[0,1,1,6]),
(311,17,[0,2,10])]
def block1 : Array Row := #[
(313,10,[0,0,0,1,5]),
(317,2,[0,0,21]),
(331,3,[0,1,2,4]),
(337,10,[0,0,0,0,1,3]),
(347,2,[0,39]),
(349,2,[0,0,1,9]),
(353,3,[0,0,0,0,0,4]),
(359,7,[0,40]),
(367,6,[0,1,17]),
(373,2,[0,0,1,10]),
(379,2,[0,1,1,1,3]),
(383,5,[0,42]),
(389,2,[0,0,24]),
(397,5,[0,0,1,1,4]),
(401,3,[0,0,0,0,2,2]),
(409,21,[0,0,0,1,6]),
(419,2,[0,4,7]),
(421,2,[0,0,1,2,3]),
(431,7,[0,2,13]),
(433,5,[0,0,0,0,1,1,1]),
(439,15,[0,1,20]),
(443,2,[0,5,6]),
(449,3,[0,0,0,0,0,0,3]),
(457,13,[0,0,0,1,7]),
(461,2,[0,0,2,8]),
(463,3,[0,1,3,4]),
(467,2,[0,50]),
(479,13,[0,51]),
(487,3,[0,1,1,1,1,1]),
(491,2,[0,2,3,3]),
(499,7,[0,1,22]),
(503,5,[0,53]),
(509,2,[0,0,30]),
(521,3,[0,0,0,2,5]),
(523,2,[0,1,1,9]),
(541,2,[0,0,1,1,1,2]),
(547,2,[0,1,3,5]),
(557,2,[0,0,33]),
(563,2,[0,59]),
(569,3,[0,0,0,19]),
(571,3,[0,1,2,7]),
(577,5,[0,0,0,0,0,0,1,1]),
(587,2,[0,61]),
(593,3,[0,0,0,0,11]),
(599,7,[0,5,8]),
(601,7,[0,0,0,1,2,2]),
(607,3,[0,1,25]),
(613,2,[0,0,1,1,6]),
(617,3,[0,0,0,3,4]),
(619,2,[0,1,26]),
(631,3,[0,1,1,2,3]),
(641,3,[0,0,0,0,0,0,0,2]),
(643,11,[0,1,27]),
(647,5,[0,6,7]),
(653,2,[0,0,37]),
(659,2,[0,3,14]),
(661,2,[0,0,1,2,4]),
(673,5,[0,0,0,0,0,1,3]),
(677,2,[0,0,5,5]),
(683,5,[0,4,10]),
(691,3,[0,1,2,8]),
(701,2,[0,0,2,2,3]),
(709,2,[0,0,1,16]),
(719,11,[0,71])]
def block2 : Array Row := #[
(727,5,[0,1,4,4]),
(733,6,[0,0,1,17]),
(739,3,[0,1,1,12]),
(743,5,[0,3,15]),
(751,3,[0,1,2,2,2]),
(757,2,[0,0,1,1,1,3]),
(761,6,[0,0,0,2,7]),
(769,11,[0,0,0,0,0,0,0,0,1]),
(773,2,[0,0,43]),
(787,2,[0,1,31]),
(797,2,[0,0,45]),
(809,3,[0,0,0,25]),
(811,3,[0,1,1,1,1,2]),
(821,2,[0,0,2,12]),
(823,3,[0,1,32]),
(827,2,[0,3,16]),
(829,2,[0,0,1,1,8]),
(839,11,[0,80]),
(853,2,[0,0,1,19]),
(857,3,[0,0,0,27]),
(859,2,[0,1,4,5]),
(863,5,[0,82]),
(877,2,[0,0,1,20]),
(881,3,[0,0,0,0,2,4]),
(883,2,[0,1,1,3,3]),
(887,5,[0,85]),
(907,2,[0,1,35]),
(911,17,[0,2,3,5]),
(919,7,[0,1,1,1,6]),
(929,3,[0,0,0,0,0,9]),
(937,5,[0,0,0,1,1,5]),
(941,2,[0,0,2,14]),
(947,2,[0,4,13]),
(953,3,[0,0,0,3,6]),
(967,5,[0,1,3,8]),
(971,6,[0,2,24]),
(977,3,[0,0,0,0,17]),
(983,5,[0,93]),
(991,6,[0,1,1,2,4]),
(997,7,[0,0,1,22]),
(1009,11,[0,0,0,0,1,1,3]),
(1013,3,[0,0,4,8]),
(1019,2,[0,96]),
(1021,10,[0,0,1,2,6]),
(1031,14,[0,2,26]),
(1033,5,[0,0,0,1,13]),
(1039,3,[0,1,39]),
(1049,3,[0,0,0,31]),
(1051,7,[0,1,2,2,3]),
(1061,2,[0,0,2,15]),
(1063,3,[0,1,1,16]),
(1069,6,[0,0,1,23]),
(1087,3,[0,1,41]),
(1091,2,[0,2,28]),
(1093,5,[0,0,1,3,5]),
(1097,3,[0,0,0,32]),
(1103,5,[0,7,9]),
(1109,2,[0,0,58]),
(1117,2,[0,0,1,1,10]),
(1123,2,[0,1,4,6]),
(1129,11,[0,0,0,1,14]),
(1151,17,[0,2,2,8]),
(1153,5,[0,0,0,0,0,0,0,1,1]),
(1163,5,[0,3,22])]
def block3 : Array Row := #[
(1171,2,[0,1,1,2,5]),
(1181,7,[0,0,2,16]),
(1187,2,[0,107]),
(1193,3,[0,0,0,34]),
(1201,11,[0,0,0,0,1,2,2]),
(1213,2,[0,0,1,25]),
(1217,3,[0,0,0,0,0,0,7]),
(1223,5,[0,5,14]),
(1229,2,[0,0,62]),
(1231,3,[0,1,2,12]),
(1237,2,[0,0,1,26]),
(1249,7,[0,0,0,0,0,1,5]),
(1259,2,[0,6,11]),
(1277,2,[0,0,4,9]),
(1279,3,[0,1,1,19]),
(1283,2,[0,115]),
(1289,6,[0,0,0,3,8]),
(1291,2,[0,1,2,13]),
(1297,10,[0,0,0,0,1,1,1,1]),
(1301,2,[0,0,2,2,5]),
(1303,6,[0,1,3,10]),
(1307,2,[0,118]),
(1319,13,[0,119]),
(1321,13,[0,0,0,1,2,4]),
(1327,3,[0,1,5,6]),
(1361,3,[0,0,0,0,2,6]),
(1367,5,[0,123]),
(1373,2,[0,0,3,3,3]),
(1381,2,[0,0,1,2,8]),
(1399,13,[0,1,50]),
(1409,3,[0,0,0,0,0,0,0,4]),
(1423,3,[0,1,1,21]),
(1427,2,[0,8,10]),
(1429,6,[0,0,1,3,6]),
(1433,3,[0,0,0,40]),
(1439,7,[0,127]),
(1447,3,[0,1,52]),
(1451,2,[0,2,2,9]),
(1453,2,[0,0,1,4,4]),
(1471,6,[0,1,2,3,3]),
(1481,3,[0,0,0,2,11]),
(1483,2,[0,1,5,7]),
(1487,5,[0,131]),
(1489,14,[0,0,0,0,1,10]),
(1493,2,[0,0,73]),
(1499,2,[0,3,27]),
(1511,11,[0,2,35]),
(1523,2,[0,134]),
(1531,2,[0,1,1,2,6]),
(1543,5,[0,1,54]),
(1549,2,[0,0,1,1,13]),
(1553,3,[0,0,0,0,24]),
(1559,19,[0,7,12]),
(1567,3,[0,1,1,1,9]),
(1571,2,[0,2,36]),
(1579,3,[0,1,55]),
(1583,5,[0,3,29]),
(1597,11,[0,0,1,3,7]),
(1601,3,[0,0,0,0,0,0,2,2]),
(1607,5,[0,4,20]),
(1609,7,[0,0,0,1,18]),
(1613,3,[0,0,5,10]),
(1619,2,[0,139]),
(1621,2,[0,0,1,1,1,1,2])]
def block4 : Array Row := #[
(1627,3,[0,1,57]),
(1637,2,[0,0,79]),
(1657,11,[0,0,0,1,1,8]),
(1663,3,[0,1,58]),
(1667,2,[0,3,3,6]),
(1669,2,[0,0,1,33]),
(1693,2,[0,0,1,1,14]),
(1697,3,[0,0,0,0,0,15]),
(1699,3,[0,1,60]),
(1709,3,[0,0,3,17]),
(1721,3,[0,0,0,2,13]),
(1723,3,[0,1,3,12]),
(1733,2,[0,0,83]),
(1741,2,[0,0,1,2,9]),
(1747,2,[0,1,1,24]),
(1753,7,[0,0,0,1,20]),
(1777,5,[0,0,0,0,1,11]),
(1783,10,[0,1,1,1,1,4]),
(1787,2,[0,7,14]),
(1789,6,[0,0,1,34]),
(1811,6,[0,2,41]),
(1823,5,[0,155]),
(1831,3,[0,1,2,17]),
(1847,5,[0,5,19]),
(1861,2,[0,0,1,2,10]),
(1867,2,[0,1,63]),
(1871,14,[0,2,4,6]),
(1873,10,[0,0,0,0,1,1,5]),
(1877,2,[0,0,3,18]),
(1879,6,[0,1,64]),
(1889,3,[0,0,0,0,0,16]),
(1901,2,[0,0,2,2,7]),
(1907,2,[0,161]),
(1913,3,[0,0,0,51]),
(1931,2,[0,2,43]),
(1933,5,[0,0,1,3,8]),
(1949,2,[0,0,92]),
(1951,3,[0,1,2,2,5]),
(1973,2,[0,0,6,9]),
(1979,2,[0,8,13]),
(1987,2,[0,1,66]),
(1993,5,[0,0,0,1,22]),
(2003,5,[0,3,4,5]),
(2011,3,[0,1,2,18]),
(2017,5,[0,0,0,0,0,1,1,3]),
(2027,2,[0,169]),
(2029,2,[0,0,1,5,5]),
(2039,7,[0,170]),
(2053,2,[0,0,1,1,1,7]),
(2063,5,[0,172]),
(2069,2,[0,0,4,14]),
(2081,3,[0,0,0,0,0,2,5]),
(2083,2,[0,1,68]),
(2087,5,[0,3,34]),
(2089,7,[0,0,0,1,1,9]),
(2099,2,[0,175]),
(2113,5,[0,0,0,0,0,0,1,4]),
(2129,3,[0,0,0,0,3,7]),
(2131,2,[0,1,2,19]),
(2141,2,[0,0,2,27]),
(2143,3,[0,1,1,3,6]),
(2153,3,[0,0,0,56]),
(2161,23,[0,0,0,0,1,1,1,2]),
(2203,5,[0,1,72])]
def block5 : Array Row := #[
(2207,5,[0,184]),
(2213,2,[0,0,3,21]),
(2221,2,[0,0,1,2,11]),
(2237,2,[0,0,5,13]),
(2239,3,[0,1,73]),
(2243,2,[0,7,16]),
(2251,7,[0,1,1,2,2,2]),
(2269,2,[0,0,1,1,1,1,3]),
(2273,3,[0,0,0,0,0,19]),
(2281,7,[0,0,0,1,2,7]),
(2293,2,[0,0,1,42]),
(2297,5,[0,0,0,3,12]),
(2309,2,[0,0,105]),
(2311,3,[0,1,2,3,4]),
(2333,2,[0,0,4,15]),
(2341,7,[0,0,1,1,2,5]),
(2347,3,[0,1,6,8]),
(2351,13,[0,2,2,14]),
(2357,2,[0,0,7,10]),
(2371,2,[0,1,2,21]),
(2377,5,[0,0,0,1,1,1,4]),
(2381,3,[0,0,2,3,6]),
(2389,2,[0,0,1,45]),
(2393,3,[0,0,0,5,8]),
(2399,11,[0,4,28]),
(2417,3,[0,0,0,0,35]),
(2423,5,[0,3,39]),
(2441,6,[0,0,0,2,17]),
(2447,5,[0,199]),
(2467,2,[0,1,1,32]),
(2473,5,[0,0,0,1,26]),
(2503,3,[0,1,1,33]),
(2521,17,[0,0,0,1,1,2,3]),
(2531,2,[0,2,4,8]),
(2539,2,[0,1,1,1,14]),
(2543,5,[0,10,12]),
(2549,2,[0,0,3,3,5]),
(2551,6,[0,1,2,2,6]),
(2557,2,[0,0,1,1,19]),
(2579,2,[0,208]),
(2591,7,[0,2,3,11]),
(2593,7,[0,0,0,0,0,1,1,1,1]),
(2609,3,[0,0,0,0,37]),
(2621,2,[0,0,2,31]),
(2657,3,[0,0,0,0,0,22]),
(2659,2,[0,1,85]),
(2671,7,[0,1,2,23]),
(2677,2,[0,0,1,47]),
(2683,2,[0,1,1,34]),
(2687,5,[0,6,21]),
(2689,19,[0,0,0,0,0,0,0,1,3]),
(2693,2,[0,0,121]),
(2699,2,[0,7,19]),
(2707,2,[0,1,4,12]),
(2711,7,[0,2,57]),
(2729,3,[0,0,0,4,10]),
(2741,2,[0,0,2,32]),
(2749,6,[0,0,1,49]),
(2753,3,[0,0,0,0,0,0,13]),
(2777,3,[0,0,0,68]),
(2789,2,[0,0,6,12]),
(2791,6,[0,1,1,2,10]),
(2797,2,[0,0,1,50]),
(2801,3,[0,0,0,0,2,2,3])]
def block6 : Array Row := #[
(2803,2,[0,1,90]),
(2819,2,[0,222]),
(2833,5,[0,0,0,0,1,16]),
(2837,2,[0,0,126]),
(2843,2,[0,3,3,9]),
(2851,2,[0,1,2,2,7]),
(2857,11,[0,0,0,1,3,6]),
(2861,2,[0,0,2,4,5]),
(2897,3,[0,0,0,0,41]),
(2903,5,[0,229]),
(2909,2,[0,0,128]),
(2927,5,[0,3,4,7]),
(2939,2,[0,5,29]),
(2953,13,[0,0,0,1,1,12]),
(2957,2,[0,0,130]),
(2963,2,[0,232]),
(2969,3,[0,0,0,3,15]),
(2971,10,[0,1,1,1,2,4]),
(3001,14,[0,0,0,1,2,2,2]),
(3019,2,[0,1,95]),
(3023,5,[0,238]),
(3041,3,[0,0,0,0,0,2,7]),
(3049,11,[0,0,0,1,30]),
(3061,6,[0,0,1,1,2,6]),
(3067,2,[0,1,3,20]),
(3079,6,[0,1,1,1,1,7]),
(3083,2,[0,8,18]),
(3089,3,[0,0,0,0,43]),
(3109,6,[0,0,1,3,11]),
(3119,7,[0,244]),
(3137,3,[0,0,0,0,0,0,3,3]),
(3167,5,[0,248]),
(3169,7,[0,0,0,0,0,1,1,4]),
(3191,11,[0,2,4,9]),
(3203,2,[0,250]),
(3209,3,[0,0,0,78]),
(3217,5,[0,0,0,0,1,18]),
(3229,6,[0,0,1,56]),
(3251,6,[0,2,2,2,5]),
(3257,3,[0,0,0,4,11]),
(3259,3,[0,1,1,41]),
(3271,3,[0,1,2,28]),
(3299,2,[0,6,24]),
(3313,10,[0,0,0,0,1,1,8]),
(3319,6,[0,1,3,21]),
(3323,2,[0,4,35]),
(3329,3,[0,0,0,0,0,0,0,0,5]),
(3343,5,[0,1,101]),
(3347,2,[0,3,51]),
(3361,22,[0,0,0,0,0,1,2,3]),
(3389,3,[0,0,3,4,4]),
(3407,5,[0,5,31]),
(3413,2,[0,0,146]),
(3433,5,[0,0,0,1,4,5]),
(3449,3,[0,0,0,82]),
(3457,7,[0,0,0,0,0,0,0,1,1,1]),
(3461,2,[0,0,2,39]),
(3463,3,[0,1,105]),
(3469,2,[0,0,1,6,6]),
(3491,2,[0,2,69]),
(3499,2,[0,1,4,15]),
(3511,7,[0,1,1,1,2,5]),
(3529,17,[0,0,0,1,1,3,3]),
(3533,2,[0,0,152])]
def block7 : Array Row := #[
(3539,2,[0,9,17]),
(3557,2,[0,0,3,30]),
(3559,3,[0,1,107]),
(3571,2,[0,1,2,3,6]),
(3583,3,[0,1,1,45]),
(3613,2,[0,0,1,3,13]),
(3617,3,[0,0,0,0,0,29]),
(3631,15,[0,1,2,4,4]),
(3637,2,[0,0,1,1,25]),
(3643,2,[0,1,110]),
(3659,2,[0,10,16]),
(3677,2,[0,0,156]),
(3691,2,[0,1,1,2,12]),
(3709,2,[0,0,1,1,26]),
(3719,7,[0,4,5,5]),
(3727,3,[0,1,1,1,1,8]),
(3733,2,[0,0,1,63]),
(3769,7,[0,0,0,1,36]),
(3779,2,[0,286]),
(3793,5,[0,0,0,0,1,21]),
(3797,2,[0,0,5,20]),
(3821,3,[0,0,2,42]),
(3833,3,[0,0,0,91]),
(3847,5,[0,1,115]),
(3851,2,[0,2,2,3,4]),
(3863,5,[0,290]),
(3877,2,[0,0,1,6,7]),
(3881,13,[0,0,0,2,24]),
(3907,2,[0,1,1,3,10]),
(3923,2,[0,11,15]),
(3929,3,[0,0,0,93]),
(3931,2,[0,1,2,31]),
(3943,3,[0,1,1,1,20]),
(3989,2,[0,0,167]),
(4007,5,[0,298]),
(4021,2,[0,0,1,2,18]),
(4051,10,[0,1,1,1,1,2,2]),
(4073,3,[0,0,0,96]),
(4079,11,[0,303]),
(4091,2,[0,2,79]),
(4093,2,[0,0,1,4,10]),
(4111,12,[0,1,2,32]),
(4127,5,[0,305]),
(4129,13,[0,0,0,0,0,1,13]),
(4133,2,[0,0,173]),
(4139,2,[0,306]),
(4153,5,[0,0,0,1,39]),
(4157,2,[0,0,174]),
(4177,5,[0,0,0,0,1,1,9]),
(4211,6,[0,2,81]),
(4231,3,[0,1,1,2,14]),
(4241,3,[0,0,0,0,2,15]),
(4243,2,[0,1,3,25]),
(4253,2,[0,0,178]),
(4259,2,[0,313]),
(4271,7,[0,2,3,17]),
(4273,5,[0,0,0,0,1,23]),
(4283,2,[0,315]),
(4339,10,[0,1,1,52]),
(4349,2,[0,0,180]),
(4357,2,[0,0,1,1,4,4]),
(4391,14,[0,2,84]),
(4409,3,[0,0,0,7,9]),
(4421,3,[0,0,2,5,6])]
def block8 : Array Row := #[
(4441,21,[0,0,0,1,2,11]),
(4447,3,[0,1,1,5,7]),
(4457,3,[0,0,0,101]),
(4483,2,[0,1,1,1,22]),
(4493,2,[0,0,187]),
(4513,7,[0,0,0,0,0,1,14]),
(4517,2,[0,0,188]),
(4519,3,[0,1,1,53]),
(4547,2,[0,328]),
(4549,6,[0,0,1,74]),
(4561,11,[0,0,0,0,1,2,7]),
(4591,11,[0,1,1,1,2,6]),
(4621,2,[0,0,1,2,3,4]),
(4637,2,[0,0,7,17]),
(4639,3,[0,1,136]),
(4651,3,[0,1,2,2,10]),
(4657,15,[0,0,0,0,1,24]),
(4703,5,[0,337]),
(4721,6,[0,0,0,0,2,16]),
(4723,2,[0,1,137]),
(4729,17,[0,0,0,1,44]),
(4751,19,[0,2,2,2,7]),
(4759,3,[0,1,5,17]),
(4783,6,[0,1,138]),
(4789,2,[0,0,1,1,3,7]),
(4793,3,[0,0,0,108]),
(4813,2,[0,0,1,78]),
(4817,3,[0,0,0,0,3,13]),
(4861,11,[0,0,1,1,1,1,1,2]),
(4871,11,[0,2,92]),
(4877,2,[0,0,8,15]),
(4889,3,[0,0,0,5,14]),
(4931,6,[0,2,6,9]),
(4937,3,[0,0,0,112]),
(4957,2,[0,0,1,3,16]),
(4967,5,[0,5,42]),
(4969,11,[0,0,0,1,1,1,8]),
(5021,3,[0,0,2,53]),
(5023,3,[0,1,1,1,1,10]),
(5051,2,[0,2,2,25]),
(5059,2,[0,1,1,59]),
(5077,2,[0,0,1,1,1,14]),
(5081,3,[0,0,0,2,30]),
(5099,2,[0,356]),
(5101,6,[0,0,1,2,2,6]),
(5119,3,[0,1,146]),
(5147,2,[0,10,22]),
(5167,6,[0,1,1,3,12]),
(5179,2,[0,1,149]),
(5189,2,[0,0,210]),
(5227,2,[0,1,5,18]),
(5351,11,[0,2,2,27]),
(5387,2,[0,371]),
(5393,3,[0,0,0,0,67]),
(5407,3,[0,1,6,15]),
(5417,3,[0,0,0,122]),
(5419,3,[0,1,1,3,13]),
(5437,5,[0,0,1,1,35]),
(5441,3,[0,0,0,0,0,0,2,6]),
(5449,7,[0,0,0,1,48]),
(5471,7,[0,2,100]),
(5477,2,[0,0,11,11]),
(5483,2,[0,376]),
(5503,3,[0,1,3,31])]
def block9 : Array Row := #[
(5507,2,[0,378]),
(5527,5,[0,1,1,62]),
(5557,2,[0,0,1,89]),
(5569,13,[0,0,0,0,0,0,1,9]),
(5573,2,[0,0,3,45]),
(5581,6,[0,0,1,1,2,10]),
(5591,11,[0,2,5,13]),
(5639,7,[0,385]),
(5647,3,[0,1,159]),
(5653,5,[0,0,1,1,36]),
(5683,2,[0,1,160]),
(5689,11,[0,0,0,1,1,21]),
(5693,2,[0,0,223]),
(5701,2,[0,0,1,2,2,7]),
(5711,19,[0,2,104]),
(5741,2,[0,0,2,3,12]),
(5743,10,[0,1,1,4,9]),
(5779,2,[0,1,1,1,27]),
(5783,7,[0,3,3,16]),
(5801,3,[0,0,0,2,2,9]),
(5807,5,[0,393]),
(5813,2,[0,0,230]),
(5839,6,[0,1,3,33]),
(5843,2,[0,8,30]),
(5867,5,[0,3,80]),
(5869,2,[0,0,1,1,37]),
(5879,11,[0,396]),
(5923,2,[0,1,1,3,14]),
(5939,2,[0,400]),
(5953,7,[0,0,0,0,0,0,1,10]),
(5987,2,[0,12,20]),
(6007,3,[0,1,3,4,5]),
(6043,5,[0,1,7,15]),
(6053,2,[0,0,6,23]),
(6067,2,[0,1,1,67]),
(6089,3,[0,0,0,134]),
(6101,2,[0,0,2,2,17]),
(6113,3,[0,0,0,0,0,42]),
(6151,3,[0,1,2,2,12]),
(6173,2,[0,0,241]),
(6197,2,[0,0,242]),
(6203,2,[0,3,85]),
(6257,3,[0,0,0,0,6,8]),
(6263,5,[0,10,25]),
(6269,2,[0,0,245]),
(6271,11,[0,1,2,4,7]),
(6277,2,[0,0,1,98]),
(6287,7,[0,3,86]),
(6299,2,[0,14,18]),
(6329,3,[0,0,0,3,29]),
(6337,10,[0,0,0,0,0,0,1,1,4]),
(6353,3,[0,0,0,0,77]),
(6367,3,[0,1,177]),
(6373,2,[0,0,1,1,1,16]),
(6449,3,[0,0,0,0,5,10]),
(6451,3,[0,1,2,2,13]),
(6481,7,[0,0,0,0,1,1,1,1,2]),
(6529,7,[0,0,0,0,0,0,0,1,6]),
(6553,10,[0,0,0,1,1,3,5]),
(6563,5,[0,6,43]),
(6577,5,[0,0,0,0,1,32]),
(6581,14,[0,0,2,3,14]),
(6599,13,[0,426]),
(6619,2,[0,1,184])]
def block10 : Array Row := #[
(6637,2,[0,0,1,3,21]),
(6659,2,[0,430]),
(6689,3,[0,0,0,0,0,4,7]),
(6709,2,[0,0,1,5,13]),
(6779,2,[0,434]),
(6781,2,[0,0,1,2,29]),
(6793,10,[0,0,0,1,60]),
(6863,5,[0,14,20]),
(6869,2,[0,0,6,25]),
(6899,2,[0,438]),
(6907,2,[0,1,189]),
(6911,7,[0,2,124]),
(6947,2,[0,8,35]),
(6959,7,[0,3,3,19]),
(6977,3,[0,0,0,0,0,0,28]),
(6997,5,[0,0,1,4,15]),
(7019,2,[0,4,4,9]),
(7039,3,[0,1,1,6,8]),
(7043,2,[0,3,95]),
(7069,2,[0,0,1,7,10]),
(7103,5,[0,15,18]),
(7127,5,[0,3,96]),
(7129,7,[0,0,0,1,1,1,1,4]),
(7151,7,[0,2,2,4,5]),
(7159,3,[0,1,195]),
(7193,3,[0,0,0,9,10]),
(7229,2,[0,0,5,33]),
(7237,2,[0,0,1,1,1,18]),
(7283,2,[0,4,66]),
(7309,6,[0,0,1,1,3,9]),
(7321,7,[0,0,0,1,2,17]),
(7333,6,[0,0,1,5,14]),
(7369,7,[0,0,0,1,62]),
(7433,3,[0,0,0,157]),
(7481,6,[0,0,0,2,4,6]),
(7507,2,[0,1,1,1,33]),
(7529,3,[0,0,0,159]),
(7537,7,[0,0,0,0,1,36]),
(7559,13,[0,466]),
(7561,13,[0,0,0,1,1,1,2,3]),
(7577,3,[0,0,0,160]),
(7589,2,[0,0,3,57]),
(7603,2,[0,1,3,41]),
(7643,2,[0,469]),
(7649,3,[0,0,0,0,0,51]),
(7699,3,[0,1,207]),
(7759,3,[0,1,1,82]),
(7789,2,[0,0,1,4,16]),
(7877,2,[0,0,4,40]),
(7883,2,[0,3,102]),
(7901,2,[0,0,2,2,21]),
(7933,2,[0,0,1,120]),
(7949,2,[0,0,296]),
(7993,5,[0,0,0,1,1,1,11]),
(8009,3,[0,0,0,3,4,5]),
(8011,14,[0,1,1,2,23]),
(8069,2,[0,0,300]),
(8093,2,[0,0,3,6,6]),
(8117,2,[0,0,302]),
(8167,3,[0,1,217]),
(8171,2,[0,2,7,13]),
(8179,2,[0,1,9,14]),
(8191,17,[0,1,1,2,3,5]),
(8231,11,[0,2,142])]
def block11 : Array Row := #[
(8233,10,[0,0,0,1,3,3,3]),
(8237,2,[0,0,9,19]),
(8243,2,[0,5,65]),
(8263,3,[0,1,1,1,1,1,6]),
(8369,3,[0,0,0,0,98]),
(8431,3,[0,1,2,59]),
(8447,5,[0,12,26]),
(8461,6,[0,0,1,1,2,14]),
(8513,5,[0,0,0,0,0,0,3,7]),
(8527,5,[0,1,3,3,9]),
(8581,6,[0,0,1,2,4,5]),
(8599,3,[0,1,226]),
(8609,3,[0,0,0,0,0,56]),
(8627,2,[0,7,48]),
(8641,17,[0,0,0,0,0,0,1,1,1,2]),
(8663,5,[0,17,19]),
(8689,13,[0,0,0,0,1,41]),
(8707,5,[0,1,229]),
(8737,5,[0,0,0,0,0,1,3,5]),
(8779,11,[0,1,3,4,7]),
(8807,5,[0,3,6,11]),
(8819,2,[0,510]),
(8839,3,[0,1,1,93]),
(8861,2,[0,0,2,85]),
(8923,2,[0,1,234]),
(8941,6,[0,0,1,2,34]),
(8951,13,[0,2,2,40]),
(8969,3,[0,0,0,7,16]),
(8971,2,[0,1,2,5,8]),
(9013,5,[0,0,1,132]),
(9049,7,[0,0,0,1,5,9]),
(9067,3,[0,1,238]),
(9091,3,[0,1,1,2,25]),
(9103,6,[0,1,11,12]),
(9137,3,[0,0,0,0,104]),
(9157,6,[0,0,1,3,28]),
(9221,2,[0,0,2,88]),
(9241,13,[0,0,0,1,2,3,4]),
(9277,5,[0,0,1,136]),
(9281,3,[0,0,0,0,0,0,2,9]),
(9293,2,[0,0,8,25]),
(9343,5,[0,1,1,1,39]),
(9377,3,[0,0,0,0,0,61]),
(9397,2,[0,0,1,1,1,1,9]),
(9413,3,[0,0,5,41]),
(9419,2,[0,6,58]),
(9431,7,[0,2,8,12]),
(9491,2,[0,2,5,20]),
(9521,3,[0,0,0,0,2,3,6]),
(9547,2,[0,1,11,13]),
(9613,2,[0,0,1,1,1,23]),
(9623,5,[0,6,60]),
(9629,2,[0,0,9,22]),
(9643,2,[0,1,251]),
(9679,3,[0,1,253]),
(9689,3,[0,0,0,3,39]),
(9767,5,[0,7,54]),
(9787,3,[0,1,3,50]),
(9811,3,[0,1,1,2,28]),
(9859,2,[0,1,10,15]),
(9871,3,[0,1,2,3,14]),
(9929,3,[0,0,0,6,20]),
(9931,10,[0,1,2,66]),
(9941,2,[0,0,2,3,19])]
def block12 : Array Row := #[
(9949,2,[0,0,1,144]),
(10093,2,[0,0,1,9,9]),
(10141,2,[0,0,1,2,5,5]),
(10159,3,[0,1,262]),
(10177,7,[0,0,0,0,0,0,1,15]),
(10193,3,[0,0,0,0,3,3,5]),
(10223,5,[0,7,56]),
(10243,7,[0,1,1,103]),
(10253,2,[0,0,4,50]),
(10303,3,[0,1,6,25]),
(10357,2,[0,0,1,149]),
(10427,2,[0,5,78]),
(10433,3,[0,0,0,0,0,0,37]),
(10459,2,[0,1,1,3,22]),
(10487,5,[0,3,3,27]),
(10499,2,[0,9,41]),
(10613,2,[0,0,3,74]),
(10663,3,[0,1,272]),
(10709,2,[0,0,367]),
(10753,11,[0,0,0,0,0,0,0,0,0,1,3]),
(10781,10,[0,0,2,3,3,4]),
(10883,2,[0,570]),
(10973,2,[0,0,5,46]),
(11027,2,[0,11,34]),
(11071,3,[0,1,1,1,2,12]),
(11087,5,[0,8,52]),
(11131,2,[0,1,2,3,15]),
(11171,2,[0,2,186]),
(11197,2,[0,0,1,1,63]),
(11261,2,[0,0,2,102]),
(11279,7,[0,583]),
(11299,3,[0,1,3,56]),
(11353,7,[0,0,0,1,4,13]),
(11369,3,[0,0,0,3,3,9]),
(11393,3,[0,0,0,0,0,0,0,23]),
(11411,7,[0,2,3,37]),
(11467,5,[0,1,1,3,3,5]),
(11471,11,[0,2,10,11]),
(11491,3,[0,1,2,75]),
(11519,7,[0,5,85]),
(11597,3,[0,0,5,47]),
(11633,3,[0,0,0,0,128]),
(11719,6,[0,1,1,1,3,10]),
(11783,5,[0,13,32]),
(11831,7,[0,2,3,5,5]),
(11903,5,[0,4,99]),
(11909,2,[0,0,5,49]),
(11939,2,[0,14,30]),
(11959,3,[0,1,297]),
(11987,2,[0,5,88]),
(12097,5,[0,0,0,0,0,0,1,1,1,3]),
(12107,2,[0,609]),
(12161,3,[0,0,0,0,0,0,0,2,7]),
(12163,5,[0,1,301]),
(12197,2,[0,0,406]),
(12227,2,[0,613]),
(12239,13,[0,9,46]),
(12281,3,[0,0,0,2,62]),
(12343,7,[0,1,4,4,6]),
(12379,2,[0,1,305]),
(12421,7,[0,0,1,1,1,2,8]),
(12491,2,[0,2,203]),
(12539,2,[0,620]),
(12619,2,[0,1,1,125])]
def block13 : Array Row := #[
(12641,3,[0,0,0,0,0,2,21]),
(12703,3,[0,1,9,20]),
(12713,3,[0,0,0,3,48]),
(12721,13,[0,0,0,0,1,2,15]),
(12757,2,[0,0,1,178]),
(12763,2,[0,1,1,126]),
(12841,21,[0,0,0,1,2,27]),
(12889,13,[0,0,0,1,1,40]),
(12893,3,[0,0,4,61]),
(13007,5,[0,3,157]),
(13049,3,[0,0,0,3,50]),
(13127,5,[0,635]),
(13183,3,[0,1,5,5,5]),
(13187,2,[0,7,68]),
(13217,3,[0,0,0,0,0,3,16]),
(13219,3,[0,1,319]),
(13399,3,[0,1,3,4,9]),
(13499,6,[0,6,77]),
(13553,3,[0,0,0,0,3,4,4]),
(13577,3,[0,0,0,263]),
(13597,5,[0,0,1,4,26]),
(13649,3,[0,0,0,0,146]),
(13669,6,[0,0,1,6,18]),
(13751,11,[0,2,2,2,2,4]),
(13757,2,[0,0,7,41]),
(13759,6,[0,1,330]),
(13789,7,[0,0,1,1,75]),
(13799,7,[0,649]),
(13859,2,[0,5,5,12]),
(13877,2,[0,0,442]),
(13879,6,[0,1,1,1,54]),
(14081,3,[0,0,0,0,0,0,0,0,2,4]),
(14177,3,[0,0,0,0,0,85]),
(14207,5,[0,660]),
(14251,3,[0,1,2,2,2,7]),
(14293,6,[0,0,1,1,77]),
(14369,3,[0,0,0,0,0,86]),
(14401,11,[0,0,0,0,0,0,1,1,2,2]),
(14411,2,[0,2,4,31]),
(14461,2,[0,0,1,2,52]),
(14489,3,[0,0,0,276]),
(14503,3,[0,1,345]),
(14551,3,[0,1,2,2,24]),
(14561,6,[0,0,0,0,0,2,3,5]),
(14593,5,[0,0,0,0,0,0,0,0,1,7]),
(14621,2,[0,0,2,6,13]),
(14669,2,[0,0,7,43]),
(14683,3,[0,1,348]),
(14723,2,[0,6,83]),
(14731,10,[0,1,2,93]),
(14753,3,[0,0,0,0,0,88]),
(14767,3,[0,1,8,27]),
(14797,2,[0,0,1,1,1,32]),
(14831,11,[0,2,233]),
(14867,2,[0,673]),
(14887,3,[0,1,1,143]),
(14939,2,[0,3,4,24]),
(15013,2,[0,0,1,1,1,33]),
(15061,2,[0,0,1,2,53]),
(15073,5,[0,0,0,0,0,1,36]),
(15199,6,[0,1,6,34]),
(15287,5,[0,683]),
(15307,3,[0,1,357]),
(15359,11,[0,3,183])]
def block14 : Array Row := #[
(15361,7,[0,0,0,0,0,0,0,0,0,0,1,2]),
(15373,2,[0,0,1,1,3,17]),
(15377,3,[0,0,0,0,10,10]),
(15467,5,[0,4,7,11]),
(15497,3,[0,0,0,5,34]),
(15581,2,[0,0,2,7,12]),
(15739,2,[0,1,13,17]),
(15797,2,[0,0,4,71]),
(15803,2,[0,690]),
(15859,2,[0,1,1,151]),
(15887,5,[0,5,5,14]),
(15919,6,[0,1,3,74]),
(15923,2,[0,7,80]),
(15937,7,[0,0,0,0,0,0,1,22]),
(15971,2,[0,2,249]),
(16067,2,[0,9,58]),
(16139,2,[0,696]),
(16187,2,[0,697]),
(16189,2,[0,0,1,7,19]),
(16193,5,[0,0,0,0,0,0,4,8]),
(16231,3,[0,1,2,99]),
(16253,2,[0,0,6,51]),
(16333,2,[0,0,1,217]),
(16421,2,[0,0,2,141]),
(16529,3,[0,0,0,0,173]),
(16553,3,[0,0,0,306]),
(16573,2,[0,0,1,220]),
(16651,2,[0,1,1,2,2,11]),
(16657,5,[0,0,0,0,1,68]),
(16699,3,[0,1,4,4,8]),
(16741,6,[0,0,1,1,1,2,10]),
(16811,7,[0,2,12,12]),
(16823,5,[0,5,117]),
(16831,6,[0,1,1,2,4,6]),
(16901,2,[0,0,2,2,5,5]),
(16927,6,[0,1,3,5,10]),
(16937,3,[0,0,0,9,20]),
(16943,5,[0,13,44]),
(16993,10,[0,0,0,0,0,1,1,16]),
(17077,2,[0,0,1,223]),
(17093,2,[0,0,504]),
(17117,3,[0,0,4,76]),
(17167,3,[0,1,391]),
(17341,6,[0,0,1,2,6,6]),
(17359,3,[0,1,4,55]),
(17539,3,[0,1,11,21]),
(17569,11,[0,0,0,0,0,1,1,17]),
(17573,2,[0,0,8,42]),
(17627,2,[0,3,204]),
(17659,3,[0,1,1,1,1,28]),
(17761,19,[0,0,0,0,0,1,2,11]),
(17783,5,[0,6,98]),
(17891,2,[0,2,275]),
(17909,2,[0,0,4,4,11]),
(17911,3,[0,1,1,2,45]),
(17939,2,[0,731]),
(17971,3,[0,1,2,108]),
(17987,5,[0,6,8,8]),
(18041,3,[0,0,0,2,4,12]),
(18133,5,[0,0,1,238]),
(18217,7,[0,0,0,1,1,4,8]),
(18257,5,[0,0,0,0,3,37]),
(18427,2,[0,1,11,22]),
(18481,13,[0,0,0,0,1,2,3,4])]
def block15 : Array Row := #[
(18541,6,[0,0,1,1,2,26]),
(18617,3,[0,0,0,5,40]),
(18701,2,[0,0,2,2,4,6]),
(18719,7,[0,3,3,42]),
(18803,5,[0,3,6,21]),
(18839,7,[0,749]),
(18911,14,[0,2,10,17]),
(18917,2,[0,0,532]),
(19037,2,[0,0,534]),
(19081,17,[0,0,0,1,1,2,15]),
(19207,5,[0,1,1,4,24]),
(19219,2,[0,1,418]),
(19237,2,[0,0,1,3,49]),
(19259,2,[0,756]),
(19309,6,[0,0,1,252]),
(19471,11,[0,1,2,4,16]),
(19501,2,[0,0,1,2,2,2,5]),
(19597,2,[0,0,1,8,19]),
(19709,2,[0,0,5,74]),
(19763,2,[0,12,52]),
(19801,13,[0,0,0,1,1,2,2,4]),
(19867,2,[0,1,3,4,13]),
(20071,3,[0,1,1,2,47]),
(20147,6,[0,3,227]),
(20149,2,[0,0,1,8,20]),
(20201,6,[0,0,0,2,2,25]),
(20297,3,[0,0,0,13,16]),
(20411,6,[0,2,5,36]),
(20443,2,[0,1,435]),
(20563,3,[0,1,8,34]),
(20641,7,[0,0,0,0,0,1,2,13]),
(20749,2,[0,0,1,3,5,7]),
(20753,3,[0,0,0,0,210]),
(20759,7,[0,24,27]),
(20921,3,[0,0,0,2,98]),
(20947,3,[0,1,443]),
(20983,3,[0,1,5,56]),
(21089,3,[0,0,0,0,0,119]),
(21139,2,[0,1,5,57]),
(21227,2,[0,784]),
(21277,6,[0,0,1,1,1,44]),
(21419,2,[0,786]),
(21433,5,[0,0,0,1,7,14]),
(21523,2,[0,1,6,46]),
(21563,2,[0,788]),
(21589,2,[0,0,1,3,54]),
(21661,2,[0,0,1,2,7,7]),
(21673,10,[0,0,0,1,1,3,13]),
(21713,3,[0,0,0,0,8,16]),
(21803,2,[0,4,166]),
(21817,7,[0,0,0,1,1,1,25]),
(21893,2,[0,0,5,81]),
(21991,3,[0,1,2,129]),
(22037,2,[0,0,3,137]),
(22093,6,[0,0,1,3,55]),
(22109,2,[0,0,577]),
(22157,2,[0,0,9,42]),
(22171,2,[0,1,2,130]),
(22277,2,[0,0,579]),
(22469,2,[0,0,12,32]),
(22481,3,[0,0,0,0,2,59]),
(22511,11,[0,2,326]),
(22651,3,[0,1,2,2,35]),
(22679,13,[0,6,8,9])]
def block16 : Array Row := #[
(22699,12,[0,1,1,5,24]),
(22717,2,[0,0,1,1,114]),
(22741,7,[0,0,1,2,74]),
(22853,2,[0,0,9,44]),
(22901,2,[0,0,2,2,49]),
(22937,3,[0,0,0,14,17]),
(22943,5,[0,805]),
(22963,3,[0,1,13,23]),
(23003,2,[0,3,10,15]),
(23057,5,[0,0,0,0,4,31]),
(23209,31,[0,0,0,1,162]),
(23291,6,[0,2,6,32]),
(23311,3,[0,1,1,2,3,11]),
(23321,3,[0,0,0,2,4,15]),
(23327,5,[0,27,28]),
(23497,5,[0,0,0,1,4,23]),
(23687,5,[0,5,155]),
(23773,5,[0,0,1,3,60]),
(23819,2,[0,814]),
(23879,7,[0,815]),
(24113,3,[0,0,0,0,4,32]),
(24137,3,[0,0,0,3,82]),
(24229,2,[0,0,1,1,121]),
(24281,3,[0,0,0,2,110]),
(24391,3,[0,1,1,2,57]),
(24413,2,[0,0,6,71]),
(24509,2,[0,0,4,101]),
(24611,13,[0,2,8,27]),
(24623,5,[0,5,160]),
(24691,2,[0,1,2,142]),
(24697,5,[0,0,0,1,1,3,3,3]),
(24749,2,[0,0,8,56]),
(24781,2,[0,0,1,2,3,16]),
(25073,3,[0,0,0,0,245]),
(25163,2,[0,8,100]),
(25183,5,[0,1,1,221]),
(25253,2,[0,0,16,27]),
(25261,7,[0,0,1,2,81]),
(25349,2,[0,0,626]),
(25391,7,[0,2,354]),
(25411,7,[0,1,2,3,4,4]),
(25423,3,[0,1,7,47]),
(25469,2,[0,0,628]),
(25561,11,[0,0,0,1,1,2,19]),
(25703,5,[0,19,41]),
(25733,2,[0,0,3,156]),
(25913,3,[0,0,0,12,21]),
(25931,2,[0,2,361]),
(25999,7,[0,1,3,113]),
(26041,13,[0,0,0,1,2,3,10]),
(26099,2,[0,842]),
(26153,3,[0,0,0,3,90]),
(26423,5,[0,4,196]),
(26713,10,[0,0,0,1,1,3,15]),
(26729,3,[0,0,0,5,54]),
(26731,3,[0,1,1,1,1,1,2,4]),
(26861,2,[0,0,2,6,21]),
(27017,5,[0,0,0,4,62]),
(27397,2,[0,0,1,1,134]),
(27541,19,[0,0,1,1,1,1,2,6]),
(27653,2,[0,0,10,47]),
(27689,3,[0,0,0,440]),
(27799,7,[0,1,12,29]),
(27809,3,[0,0,0,0,0,4,21])]
def block17 : Array Row := #[
(27883,3,[0,1,1,242]),
(27893,2,[0,0,7,72]),
(27967,3,[0,1,16,21]),
(27997,5,[0,0,1,334]),
(28163,2,[0,863]),
(28277,2,[0,0,659]),
(28297,5,[0,0,0,1,1,1,31]),
(28349,2,[0,0,7,73]),
(28403,5,[0,4,209]),
(28411,2,[0,1,2,160]),
(28513,5,[0,0,0,0,0,1,1,1,1,4]),
(28537,5,[0,0,0,1,9,12]),
(28541,2,[0,0,2,224]),
(28573,2,[0,0,1,341]),
(28603,2,[0,1,1,3,48]),
(28621,13,[0,0,1,1,1,2,15]),
(28759,3,[0,1,537]),
(28843,2,[0,1,4,7,8]),
(28859,2,[0,14,62]),
(28909,2,[0,0,1,1,4,20]),
(28927,3,[0,1,1,251]),
(28949,2,[0,0,667]),
(28979,2,[0,872]),
(29059,2,[0,1,9,38]),
(29167,3,[0,1,540]),
(29173,2,[0,0,1,4,5,6]),
(29179,13,[0,1,1,255]),
(29209,7,[0,0,0,1,198]),
(29269,6,[0,0,1,1,1,57]),
(29339,2,[0,878]),
(29437,2,[0,0,1,4,47]),
(29453,2,[0,0,11,45]),
(29531,2,[0,2,397]),
(29611,3,[0,1,1,2,3,14]),
(29663,5,[0,885]),
(29873,3,[0,0,0,0,281]),
(29879,11,[0,888]),
(30029,2,[0,0,675]),
(30071,13,[0,2,10,24]),
(30269,3,[0,0,3,8,14]),
(30341,2,[0,0,2,11,12]),
(30403,5,[0,1,1,1,102]),
(30427,5,[0,1,4,88]),
(30637,2,[0,0,1,1,8,11]),
(30649,7,[0,0,0,1,205]),
(30697,10,[0,0,0,1,206]),
(30713,3,[0,0,0,4,69]),
(30809,3,[0,0,0,472]),
(31079,11,[0,12,74]),
(31159,3,[0,1,1,1,105]),
(31307,2,[0,4,223]),
(31573,5,[0,0,1,1,150]),
(31607,5,[0,904]),
(31741,6,[0,0,1,2,8,8]),
(31817,3,[0,0,0,12,24]),
(31847,5,[0,908]),
(31883,2,[0,7,145]),
(31907,2,[0,3,13,15]),
(32233,5,[0,0,0,1,6,21]),
(32321,6,[0,0,0,0,0,0,2,25]),
(32323,2,[0,1,564]),
(32327,5,[0,3,332]),
(32371,2,[0,1,2,5,22]),
(32507,2,[0,917])]
def block18 : Array Row := #[
(32579,6,[0,3,5,40]),
(32621,3,[0,0,2,3,50]),
(32717,2,[0,0,701]),
(32917,2,[0,0,1,5,46]),
(32939,2,[0,13,75]),
(33053,2,[0,0,707]),
(33073,5,[0,0,0,0,1,5,15]),
(33113,3,[0,0,0,493]),
(33119,7,[0,9,104]),
(33287,5,[0,4,6,23]),
(33469,2,[0,0,1,380]),
(33581,2,[0,0,2,8,20]),
(33613,5,[0,0,1,383]),
(33623,5,[0,927]),
(33641,3,[0,0,0,2,9,9]),
(33679,3,[0,1,1,282]),
(33937,5,[0,0,0,0,1,3,25]),
(34019,2,[0,20,50]),
(34267,2,[0,1,590]),
(34283,2,[0,17,59]),
(34297,5,[0,0,0,1,225]),
(34327,5,[0,1,1,288]),
(34403,2,[0,26,38]),
(35081,3,[0,0,0,2,150]),
(35129,3,[0,0,0,509]),
(35153,3,[0,0,0,0,5,5,5]),
(35257,7,[0,0,0,1,5,29]),
(35267,2,[0,3,4,49]),
(35291,2,[0,2,446]),
(35327,5,[0,6,174]),
(35401,13,[0,0,0,1,2,2,16]),
(35509,2,[0,0,1,4,56]),
(35531,6,[0,2,4,6,7]),
(35803,14,[0,1,1,1,1,5,6]),
(35837,2,[0,0,6,6,10]),
(35899,2,[0,1,10,43]),
(36107,2,[0,3,359]),
(36293,2,[0,0,13,46]),
(36629,2,[0,0,739]),
(37039,3,[0,1,615]),
(37057,5,[0,0,0,0,0,0,1,43]),
(37171,3,[0,1,1,2,3,16]),
(37379,2,[0,4,264]),
(37489,19,[0,0,0,0,1,4,19]),
(37517,2,[0,0,22,29]),
(37549,2,[0,0,1,1,3,34]),
(37589,2,[0,0,747]),
(37633,5,[0,0,0,0,0,0,0,0,1,3,3]),
(37663,3,[0,1,622]),
(37783,3,[0,1,1,311]),
(37991,7,[0,2,9,31]),
(38273,3,[0,0,0,0,0,0,0,5,8]),
(38447,5,[0,14,79]),
(38557,2,[0,0,1,1,1,1,3,6]),
(38723,2,[0,7,170]),
(39047,5,[0,3,380]),
(39157,6,[0,0,1,5,53]),
(39161,3,[0,0,0,2,4,23]),
(39419,2,[0,978]),
(39749,2,[0,0,7,98]),
(40189,2,[0,0,1,6,44]),
(40343,5,[0,8,150]),
(40529,3,[0,0,0,0,6,34]),
(40559,7,[0,3,392])]
def block19 : Array Row := #[
(40577,3,[0,0,0,0,0,0,0,65]),
(40709,2,[0,0,772]),
(40823,5,[0,987]),
(40879,6,[0,1,1,1,133]),
(41177,3,[0,0,0,558]),
(41513,3,[0,0,0,561]),
(41843,2,[0,994]),
(41903,5,[0,3,12,20]),
(41983,6,[0,1,655]),
(42083,2,[0,15,77]),
(42139,2,[0,1,1,335]),
(42257,3,[0,0,0,0,7,33]),
(42397,2,[0,0,1,447]),
(42773,3,[0,0,6,6,11]),
(43159,3,[0,1,665]),
(43411,3,[0,1,2,228]),
(43577,3,[0,0,0,5,80]),
(43661,2,[0,0,2,11,16]),
(43691,6,[0,2,6,54]),
(43717,5,[0,0,1,457]),
(43753,7,[0,0,0,1,277]),
(43801,31,[0,0,0,1,2,2,20]),
(43853,2,[0,0,7,105]),
(44041,11,[0,0,0,1,2,72]),
(44101,6,[0,0,1,1,2,2,3,3]),
(44371,2,[0,1,1,2,6,9]),
(44809,11,[0,0,0,1,281]),
(44851,10,[0,1,2,2,5,8]),
(44963,2,[0,1020]),
(44971,3,[0,1,2,237]),
(45077,2,[0,0,16,42]),
(45233,3,[0,0,0,0,4,54]),
(45413,2,[0,0,800]),
(45707,2,[0,1027]),
(45751,3,[0,1,2,2,2,17]),
(45887,5,[0,1030]),
(46061,2,[0,0,2,3,3,14]),
(46091,2,[0,2,4,80]),
(46103,10,[0,3,11,23]),
(46441,7,[0,0,0,1,1,1,2,13]),
(46457,3,[0,0,0,596]),
(46723,2,[0,1,5,108]),
(46769,3,[0,0,0,0,11,21]),
(46811,2,[0,2,10,35]),
(46817,3,[0,0,0,0,0,3,4,7]),
(46993,5,[0,0,0,0,1,4,23]),
(47057,3,[0,0,0,0,6,39]),
(47161,17,[0,0,0,1,1,2,31]),
(47251,10,[0,1,1,1,2,2,2,3]),
(47317,6,[0,0,1,480]),
(47381,2,[0,0,2,8,26]),
(47491,2,[0,1,2,248]),
(47569,17,[0,0,0,0,1,166]),
(47639,7,[0,1042]),
(47653,13,[0,0,1,4,7,7]),
(47711,11,[0,2,5,72]),
(47777,3,[0,0,0,0,0,236]),
(47981,2,[0,0,2,344]),
(48109,2,[0,0,1,7,46]),
(48131,6,[0,2,538]),
(48239,7,[0,23,57]),
(48497,3,[0,0,0,0,3,83]),
(48563,2,[0,1047]),
(48571,2,[0,1,2,254])]
def block20 : Array Row := #[
(48619,2,[0,1,1,11,20]),
(48679,3,[0,1,3,7,17]),
(48991,6,[0,1,2,8,19]),
(49003,13,[0,1,699]),
(49019,2,[0,1050]),
(49459,3,[0,1,706]),
(49681,17,[0,0,0,0,1,1,1,2,8]),
(49711,7,[0,1,2,258]),
(49757,2,[0,0,3,272]),
(49919,7,[0,4,327]),
(50291,2,[0,2,14,27]),
(50411,2,[0,2,19,19]),
(50591,7,[0,2,552]),
(50891,2,[0,2,3,128]),
(50971,2,[0,1,2,264]),
(51109,10,[0,0,1,502]),
(51487,3,[0,1,714]),
(51803,2,[0,16,84]),
(51859,3,[0,1,1,13,18]),
(51899,2,[0,3,4,67]),
(52177,5,[0,0,0,0,1,180]),
(52289,3,[0,0,0,0,0,0,7,13]),
(52667,2,[0,6,242]),
(52883,2,[0,32,43]),
(52937,5,[0,0,0,5,96]),
(53549,2,[0,0,4,198]),
(53591,13,[0,2,8,50]),
(53813,2,[0,0,4,199]),
(53819,2,[0,19,74]),
(53923,5,[0,1,4,7,13]),
(54011,2,[0,2,4,93]),
(54101,3,[0,0,2,2,99]),
(54403,2,[0,1,735]),
(54443,2,[0,37,38]),
(54493,2,[0,0,1,7,51]),
(54539,2,[0,4,11,18]),
(54547,3,[0,1,736]),
(54631,6,[0,1,1,2,110]),
(54941,2,[0,0,2,12,18]),
(55291,11,[0,1,2,7,24]),
(55339,2,[0,1,8,78]),
(55667,2,[0,5,315]),
(55721,3,[0,0,0,2,3,45]),
(55763,2,[0,3,3,103]),
(55787,2,[0,1089]),
(55813,2,[0,0,1,527]),
(55819,2,[0,1,1,3,85]),
(55829,2,[0,0,6,141]),
(55897,5,[0,0,0,1,6,32]),
(55921,21,[0,0,0,0,1,2,50]),
(55927,3,[0,1,1,5,51]),
(56171,2,[0,2,12,32]),
(56263,3,[0,1,746]),
(56807,5,[0,1096]),
(57097,7,[0,0,0,1,1,5,17]),
(57601,7,[0,0,0,0,0,0,0,0,1,1,2,2]),
(57899,2,[0,1109]),
(58189,6,[0,0,1,5,73]),
(58309,6,[0,0,1,13,29]),
(58411,2,[0,1,1,2,4,16]),
(58907,2,[0,1119]),
(59119,3,[0,1,16,38]),
(59123,2,[0,3,12,26]),
(59417,3,[0,0,0,3,177])]
def block21 : Array Row := #[
(59617,7,[0,0,0,0,0,1,1,1,1,8]),
(59669,2,[0,0,3,314]),
(60217,5,[0,0,0,1,5,43]),
(60811,2,[0,1,2,301]),
(60961,7,[0,0,0,0,0,1,2,30]),
(61261,2,[0,0,1,2,171]),
(61511,7,[0,2,614]),
(61519,3,[0,1,776]),
(61751,7,[0,2,2,2,5,7]),
(61861,2,[0,0,1,2,172]),
(62141,2,[0,0,2,5,51]),
(62233,7,[0,0,0,1,361]),
(62417,3,[0,0,0,0,14,22]),
(62563,3,[0,1,779]),
(62581,2,[0,0,1,2,3,34]),
(62927,5,[0,20,82]),
(63313,5,[0,0,0,0,1,214]),
(63391,3,[0,1,2,312]),
(63533,3,[0,0,3,327]),
(63671,11,[0,2,628]),
(63691,15,[0,1,2,4,43]),
(63901,7,[0,0,1,1,2,2,19]),
(64067,5,[0,26,63]),
(64151,17,[0,2,2,207]),
(64153,5,[0,0,0,1,1,1,1,1,1,4]),
(64157,2,[0,0,13,73]),
(65011,2,[0,1,2,4,44]),
(65323,2,[0,1,1,7,42]),
(65557,5,[0,0,1,1,1,110]),
(66239,17,[0,1160]),
(66523,2,[0,1,793]),
(66643,2,[0,1,9,75]),
(66721,13,[0,0,0,0,0,1,2,33]),
(66763,3,[0,1,1,461]),
(67247,5,[0,1165]),
(67273,7,[0,0,0,1,384]),
(67493,2,[0,0,14,71]),
(67601,3,[0,0,0,0,2,2,5,5]),
(67651,11,[0,1,2,2,4,12]),
(67763,2,[0,6,297]),
(67777,5,[0,0,0,0,0,0,1,70]),
(67993,5,[0,0,0,1,386]),
(68209,13,[0,0,0,0,1,3,3,9]),
(68917,5,[0,0,1,592]),
(69313,10,[0,0,0,0,0,0,1,7,7]),
(70121,6,[0,0,0,2,271]),
(70163,2,[0,1175]),
(70181,7,[0,0,2,4,4,9]),
(70657,7,[0,0,0,0,0,0,0,0,0,0,1,8]),
(71153,3,[0,0,0,0,513]),
(71389,11,[0,0,1,1,1,120]),
(71789,2,[0,0,31,32]),
(71849,3,[0,0,0,3,207]),
(72313,5,[0,0,0,1,8,31]),
(72701,2,[0,0,2,2,128]),
(72869,2,[0,0,956]),
(73043,2,[0,16,113]),
(73681,14,[0,0,0,0,1,2,62]),
(73943,5,[0,4,433]),
(74527,3,[0,1,828]),
(74869,2,[0,0,1,6,72]),
(75617,3,[0,0,0,0,0,6,33]),
(75941,2,[0,0,2,468]),
(75983,5,[0,1202])]
def block22 : Array Row := #[
(76103,5,[0,5,395]),
(76829,2,[0,0,970]),
(77201,3,[0,0,0,0,2,2,43]),
(77261,2,[0,0,2,473]),
(77447,5,[0,1206]),
(77513,3,[0,0,0,759]),
(77611,2,[0,1,2,5,45]),
(78301,6,[0,0,1,1,1,2,2,9]),
(78311,14,[0,2,12,42]),
(78653,3,[0,0,3,15,15]),
(78721,7,[0,0,0,0,0,0,0,1,2,12]),
(78889,11,[0,0,0,1,7,39]),
(79481,6,[0,0,0,2,296]),
(79601,3,[0,0,0,0,2,2,45]),
(79687,3,[0,1,1,7,50]),
(79841,3,[0,0,0,0,0,2,94]),
(79843,2,[0,1,3,287]),
(79847,5,[0,5,11,22]),
(80167,3,[0,1,10,82]),
(80407,3,[0,1,1,1,235]),
(80621,2,[0,0,2,9,33]),
(80687,5,[0,1213]),
(80963,5,[0,3,594]),
(81299,2,[0,3,596]),
(81563,2,[0,5,414]),
(81817,5,[0,0,0,1,3,92]),
(81883,3,[0,1,1,521]),
(82507,2,[0,1,855]),
(82591,6,[0,1,2,378]),
(82837,2,[0,0,1,1,1,5,16]),
(83417,3,[0,0,0,779]),
(83471,11,[0,2,6,93]),
(83497,10,[0,0,0,1,3,3,19]),
(83537,3,[0,0,0,0,8,48]),
(83609,3,[0,0,0,3,236]),
(83639,19,[0,7,10,19]),
(83969,3,[0,0,0,0,0,0,0,0,0,0,0,12]),
(84229,2,[0,0,1,656]),
(85303,5,[0,1,1,3,122]),
(85381,6,[0,0,1,2,223]),
(85661,2,[0,0,2,505]),
(86029,2,[0,0,1,18,27]),
(86353,10,[0,0,0,0,1,3,54]),
(87041,3,[0,0,0,0,0,0,0,0,0,0,2,6]),
(87323,2,[0,1233]),
(87383,5,[0,1234]),
(87473,5,[0,0,0,0,3,4,19]),
(88301,2,[0,0,2,2,152]),
(88607,5,[0,3,625]),
(89203,2,[0,1,886]),
(89597,2,[0,0,5,267]),
(89599,3,[0,1,28,32]),
(89603,2,[0,19,114]),
(90353,3,[0,0,0,0,584]),
(90529,7,[0,0,0,0,0,1,8,12]),
(90793,5,[0,0,0,1,1,5,24]),
(91837,2,[0,0,1,1,357]),
(91951,3,[0,1,2,2,111]),
(92009,3,[0,0,0,3,10,15]),
(92177,6,[0,0,0,0,3,142]),
(92569,31,[0,0,0,1,3,7,9]),
(92821,6,[0,0,1,2,3,5,6]),
(93941,2,[0,0,2,3,4,17]),
(94427,2,[0,10,239])]
def block23 : Array Row := #[
(94597,5,[0,0,1,689]),
(94651,2,[0,1,2,2,114]),
(94811,2,[0,2,7,94]),
(94819,2,[0,1,904]),
(95311,3,[0,1,1,1,2,70]),
(95891,2,[0,2,13,47]),
(96013,2,[0,0,1,1,1,3,30]),
(96263,5,[0,1275]),
(96479,11,[0,1276]),
(96589,6,[0,0,1,1,368]),
(96997,2,[0,0,1,16,32]),
(97021,2,[0,0,1,1,2,3,3,4]),
(97127,5,[0,1278]),
(97397,2,[0,0,5,283]),
(97501,7,[0,0,1,2,2,2,2,5]),
(97649,3,[0,0,0,0,6,71]),
(98269,2,[0,0,1,7,82]),
(99131,6,[0,2,8,82]),
(99133,2,[0,0,1,4,132]),
(99137,3,[0,0,0,0,0,0,242]),
(99431,13,[0,2,17,37]),
(99839,11,[0,1289]),
(99991,6,[0,1,1,2,4,25]),
(100591,6,[0,1,2,3,91]),
(101581,2,[0,0,1,2,262]),
(101723,2,[0,41,59]),
(101879,7,[0,3,7,75]),
(102701,2,[0,0,2,2,5,21]),
(103307,2,[0,3,14,36]),
(103409,3,[0,0,0,0,8,59]),
(104711,43,[0,2,11,60]),
(105367,3,[0,1,6,173]),
(105691,2,[0,1,2,5,57]),
(105761,3,[0,0,0,0,0,2,120]),
(105907,5,[0,1,7,157]),
(106129,23,[0,0,0,0,1,1,4,18]),
(106699,3,[0,1,947]),
(106921,14,[0,0,0,1,1,1,1,1,2,4]),
(106957,5,[0,0,1,1,401]),
(107137,10,[0,0,0,0,0,0,0,1,1,1,10]),
(108343,3,[0,1,1,5,89]),
(108869,2,[0,0,6,250]),
(108881,3,[0,0,0,0,2,217]),
(108883,2,[0,1,1,8,55]),
(108887,5,[0,1313]),
(109541,2,[0,0,2,573]),
(109883,2,[0,1318]),
(109987,3,[0,1,8,138]),
(110563,2,[0,1,958]),
(110951,11,[0,2,2,3,65]),
(111187,3,[0,1,1,1,9,19]),
(111317,2,[0,0,6,257]),
(111373,2,[0,0,1,743]),
(111443,2,[0,1322]),
(111623,5,[0,3,3,6,18]),
(111659,2,[0,1327]),
(111959,7,[0,3,4,128]),
(112331,2,[0,2,14,51]),
(113189,2,[0,0,1094]),
(113417,3,[0,0,0,864]),
(115637,2,[0,0,1107]),
(116141,2,[0,0,2,596]),
(116293,2,[0,0,1,4,151]),
(116371,10,[0,1,1,1,2,82])]
def block24 : Array Row := #[
(117133,2,[0,0,1,13,48]),
(117839,7,[0,3,7,85]),
(118247,5,[0,1342]),
(118249,17,[0,0,0,1,5,74]),
(118253,3,[0,0,6,11,14]),
(118751,17,[0,2,2,2,2,2,7]),
(119389,6,[0,0,1,768]),
(120977,3,[0,0,0,0,679]),
(121369,7,[0,0,0,1,5,76]),
(121727,5,[0,4,4,95]),
(121889,3,[0,0,0,0,0,5,61]),
(121909,6,[0,0,1,771]),
(122231,7,[0,2,6,127]),
(122789,2,[0,0,1133]),
(123017,3,[0,0,0,898]),
(123077,2,[0,0,9,177]),
(124477,2,[0,0,1,4,8,12]),
(124489,11,[0,0,0,1,1,3,5,7]),
(124979,2,[0,3,21,29]),
(125399,7,[0,3,5,5,15]),
(125591,11,[0,2,7,120]),
(125621,2,[0,0,2,4,104]),
(125737,5,[0,0,0,1,5,5,10]),
(126041,3,[0,0,0,2,8,32]),
(127031,7,[0,2,833]),
(127033,5,[0,0,0,1,18,21]),
(127037,2,[0,0,3,5,69]),
(127139,2,[0,4,593]),
(127649,3,[0,0,0,0,0,481]),
(128321,3,[0,0,0,0,0,0,2,78]),
(128563,5,[0,1,3,407]),
(129223,5,[0,1,1,1,343]),
(129277,2,[0,0,1,1,1,1,1,3,7]),
(129449,3,[0,0,0,4,231]),
(129757,2,[0,0,1,4,165]),
(130469,2,[0,0,5,5,43]),
(130489,22,[0,0,0,1,569]),
(130783,6,[0,1,19,62]),
(131899,2,[0,1,5,7,23]),
(134093,2,[0,0,3,536]),
(134359,3,[0,1,3,3,87]),
(134591,13,[0,2,13,64]),
(135589,2,[0,0,1,799]),
(136447,3,[0,1,1026]),
(136537,5,[0,0,0,1,587]),
(136601,3,[0,0,0,2,2,123]),
(136603,2,[0,1,1,681]),
(136607,5,[0,38,79]),
(139297,13,[0,0,0,0,0,1,229]),
(139303,6,[0,1,1,19,28]),
(139483,5,[0,1,1,1,1,1,3,12]),
(139663,5,[0,1,1,686]),
(140351,28,[0,2,2,3,78]),
(140363,2,[0,1391]),
(140453,2,[0,0,5,11,20]),
(142123,2,[0,1,1040]),
(142237,5,[0,0,1,1,1,1,84]),
(143699,2,[0,1396]),
(144451,2,[0,1,1,1,2,2,27]),
(144829,6,[0,0,1,1,1,1,1,34]),
(145547,2,[0,17,195]),
(146057,3,[0,0,0,957]),
(146059,2,[0,1,4,321]),
(146063,5,[0,3,780])]
def block25 : Array Row := #[
(147793,5,[0,0,0,0,1,409]),
(148147,19,[0,1,1053]),
(148201,17,[0,0,0,1,2,2,5,7]),
(148549,6,[0,0,1,827]),
(149629,2,[0,0,1,11,67]),
(150131,2,[0,2,889]),
(151883,2,[0,1406]),
(152093,2,[0,0,14,139]),
(152297,3,[0,0,0,968]),
(152441,3,[0,0,0,2,11,26]),
(154523,2,[0,1411]),
(155717,2,[0,0,4,448]),
(155719,7,[0,1,1,12,46]),
(155723,2,[0,3,3,3,48]),
(156157,6,[0,0,1,3,4,5,5]),
(156257,3,[0,0,0,0,0,7,54]),
(159167,5,[0,3,801]),
(159671,7,[0,2,3,329]),
(159739,22,[0,1,21,67]),
(162649,26,[0,0,0,1,1,1,1,53]),
(162709,2,[0,0,1,3,5,34]),
(163601,6,[0,0,0,0,2,2,79]),
(163633,5,[0,0,0,0,1,3,92]),
(163819,2,[0,1,1,7,91]),
(164621,2,[0,0,2,703]),
(164821,2,[0,0,1,2,12,18]),
(165311,19,[0,2,17,57]),
(165313,5,[0,0,0,0,0,0,1,1,3,12]),
(165317,2,[0,0,11,186]),
(165947,2,[0,4,7,77]),
(168673,5,[0,0,0,0,0,1,3,53]),
(169957,2,[0,0,1,1,530]),
(171091,2,[0,1,1,2,287]),
(171679,15,[0,1,5,10,19]),
(172973,2,[0,0,22,97]),
(173629,6,[0,0,1,1,3,5,15]),
(174761,3,[0,0,0,2,6,54]),
(174763,17,[0,1,1,3,7,20]),
(174767,5,[0,1453]),
(174773,2,[0,0,5,433]),
(175291,2,[0,1,2,599]),
(176021,2,[0,0,2,5,122]),
(176789,2,[0,0,43,49]),
(177907,2,[0,1,34,45]),
(177929,3,[0,0,0,8,162]),
(178439,7,[0,5,647]),
(180793,10,[0,0,0,1,1,1,1,1,1,10]),
(182353,7,[0,0,0,0,1,9,31]),
(182389,6,[0,0,1,892]),
(183397,5,[0,0,1,6,9,10]),
(185527,5,[0,1,1,4,158]),
(185569,7,[0,0,0,0,0,1,291]),
(187573,2,[0,0,1,3,3,4,9]),
(188189,10,[0,0,3,4,5,14]),
(188891,6,[0,2,5,230]),
(190391,11,[0,2,21,52]),
(190613,2,[0,0,1270]),
(190711,3,[0,1,1,2,5,37]),
(191119,6,[0,1,15,109]),
(191903,5,[0,49,80]),
(192263,7,[0,3,10,85]),
(194057,3,[0,0,0,30,42]),
(194899,2,[0,1,4,397]),
(195137,3,[0,0,0,0,0,0,406])]
def block26 : Array Row := #[
(196459,2,[0,1,32,51]),
(199261,6,[0,0,1,1,1,1,1,2,12]),
(199457,3,[0,0,0,0,0,8,57]),
(200041,11,[0,0,0,1,2,260]),
(200689,7,[0,0,0,0,1,11,29]),
(204233,3,[0,0,0,3,3,97]),
(204431,17,[0,2,988]),
(204437,2,[0,0,1295]),
(204439,6,[0,1,5,363]),
(204443,5,[0,3,6,148]),
(205237,5,[0,0,1,1,589]),
(205463,5,[0,6,608]),
(206027,2,[0,10,429]),
(206191,12,[0,1,1,2,9,21]),
(206369,3,[0,0,0,0,0,630]),
(206779,11,[0,1,4,5,52]),
(207121,7,[0,0,0,0,1,2,149]),
(208409,3,[0,0,0,28,51]),
(212081,3,[0,0,0,0,2,4,52]),
(213383,5,[0,5,9,60]),
(213391,3,[0,1,1,2,339]),
(213751,3,[0,1,1,2,2,2,2,7]),
(213947,2,[0,8,527]),
(213949,2,[0,0,1,1,1,3,60]),
(213953,3,[0,0,0,0,0,0,431]),
(214399,3,[0,1,1,13,58]),
(217369,17,[0,0,0,1,1,403]),
(217733,2,[0,0,9,284]),
(217739,2,[0,1513]),
(218083,2,[0,1,7,289]),
(218171,2,[0,2,1010]),
(219083,2,[0,1517]),
(219767,5,[0,1518]),
(220141,6,[0,0,1,1,2,199]),
(220301,2,[0,0,2,2,319]),
(220361,3,[0,0,0,2,3,137]),
(221909,2,[0,0,9,289]),
(222419,2,[0,3,906]),
(223103,5,[0,4,770]),
(223241,6,[0,0,0,2,581]),
(223243,2,[0,1,9,207]),
(223247,5,[0,1526]),
(223253,2,[0,0,1325]),
(223277,2,[0,0,1326]),
(223319,13,[0,1527]),
(223441,17,[0,0,0,0,1,2,3,3,7]),
(226549,18,[0,0,1,1,3,9,10]),
(229181,2,[0,0,2,3,257]),
(229981,2,[0,0,1,2,470]),
(232871,7,[0,2,4,9,20]),
(235679,11,[0,1537]),
(237683,2,[0,8,559]),
(238439,11,[0,9,489]),
(238481,3,[0,0,0,0,2,4,57]),
(238853,2,[0,0,46,60]),
(239201,3,[0,0,0,0,0,2,2,5,8]),
(240049,7,[0,0,0,0,1,1,260]),
(241169,3,[0,0,0,0,891]),
(241867,2,[0,1,1,1,1,236]),
(241877,2,[0,0,6,449]),
(241979,2,[0,4,6,117]),
(243197,2,[0,0,37,73]),
(243829,2,[0,0,1,1,5,97]),
(243911,13,[0,2,1048])]
def block27 : Array Row := #[
(244939,2,[0,1,1218]),
(245983,5,[0,1,4,463]),
(246097,5,[0,0,0,0,1,1,265]),
(246473,3,[0,0,0,1135]),
(247343,13,[0,7,8,60]),
(250753,5,[0,0,0,0,0,0,0,1,118]),
(251057,3,[0,0,0,0,5,6,19]),
(251059,2,[0,1,1222]),
(251063,5,[0,3,21,48]),
(251071,6,[0,1,2,708]),
(251393,3,[0,0,0,0,0,0,0,0,0,93]),
(251621,2,[0,0,2,8,100]),
(251831,13,[0,2,1059]),
(253343,5,[0,44,116]),
(253481,3,[0,0,0,2,626]),
(253819,3,[0,1,1,16,51]),
(254537,3,[0,0,0,1142]),
(256639,6,[0,1,1229]),
(256643,2,[0,1565]),
(257437,2,[0,0,1,1,663]),
(260411,2,[0,2,1073]),
(260983,3,[0,1,1,1,1,1,1,40]),
(261463,5,[0,1,1232]),
(261641,3,[0,0,0,2,10,46]),
(263621,2,[0,0,2,3,3,56]),
(263881,11,[0,0,0,1,1,2,129]),
(265169,3,[0,0,0,0,922]),
(266083,2,[0,1,17,128]),
(267133,5,[0,0,1,29,44]),
(267541,11,[0,0,1,2,3,3,3,5]),
(267877,2,[0,0,1,1,3,178]),
(269701,7,[0,0,1,2,2,9,10]),
(269779,2,[0,1,1244]),
(270539,2,[0,6,20,28]),
(271471,3,[0,1,2,734]),
(274117,2,[0,0,1,15,82]),
(275129,6,[0,0,0,3,6,6,6]),
(276499,3,[0,1,1,896]),
(276869,2,[0,0,7,457]),
(278111,7,[0,2,3,9,32]),
(280697,3,[0,0,0,5,372]),
(280699,2,[0,1,4,501]),
(280703,5,[0,1588]),
(280711,3,[0,1,1,2,413]),
(281959,3,[0,1,1261]),
(282071,11,[0,2,18,81]),
(282127,3,[0,1,5,454]),
(282907,3,[0,1,1,1,5,5,10]),
(283277,2,[0,0,3,18,35]),
(283637,2,[0,0,8,410]),
(285451,10,[0,1,2,2,4,39]),
(285559,6,[0,1,3,5,98]),
(285781,22,[0,0,1,2,4,83]),
(286697,3,[0,0,0,1186]),
(289253,2,[0,0,1397]),
(289771,10,[0,1,2,5,131]),
(290447,5,[0,5,795]),
(293351,7,[0,2,2,600]),
(293729,3,[0,0,0,0,0,18,32]),
(295283,2,[0,5,12,58]),
(296363,5,[0,4,7,126]),
(298157,2,[0,0,31,103]),
(299239,3,[0,1,15,159]),
(300973,2,[0,0,1,3,452])]
def block28 : Array Row := #[
(301211,7,[0,2,3,5,66]),
(303139,2,[0,1,1,4,240]),
(303547,2,[0,1,1292]),
(304883,2,[0,1609]),
(304943,5,[0,4,22,38]),
(305243,2,[0,3,1009]),
(309851,2,[0,2,2,616]),
(309853,2,[0,0,1,1,1,7,35]),
(309857,3,[0,0,0,0,0,8,81]),
(309877,2,[0,0,1,3,3,6,10]),
(310223,7,[0,4,16,51]),
(310711,7,[0,1,2,778]),
(311677,2,[0,0,1,7,218]),
(316097,3,[0,0,0,0,0,0,4,86]),
(317077,5,[0,0,1,1076]),
(317321,3,[0,0,0,2,691]),
(318749,2,[0,0,1422]),
(318809,3,[0,0,0,3,588]),
(318841,7,[0,0,0,1,2,364]),
(319001,3,[0,0,0,2,2,2,4,9]),
(320669,2,[0,0,1426]),
(323149,2,[0,0,1,3,471]),
(326941,19,[0,0,1,2,571]),
(329243,2,[0,1624]),
(329551,3,[0,1,2,2,5,5,5]),
(329873,3,[0,0,0,0,15,76]),
(330731,2,[0,2,1158]),
(337583,5,[0,3,1044]),
(337901,3,[0,0,2,2,10,28]),
(337903,3,[0,1,45,60]),
(337907,2,[0,27,247]),
(337919,7,[0,3,1045]),
(339211,2,[0,1,1,2,465]),
(343963,2,[0,1,1,24,44]),
(345607,3,[0,1,1335]),
(352043,2,[0,1641]),
(352193,3,[0,0,0,0,0,0,575]),
(356869,2,[0,0,1,1,8,82]),
(357517,2,[0,0,1,1,766]),
(359753,5,[0,0,0,43,50]),
(361033,5,[0,0,0,1,3,3,62]),
(364349,2,[0,0,21,190]),
(367307,2,[0,13,503]),
(367309,6,[0,0,1,1,1,7,40]),
(367313,3,[0,0,0,0,4,309]),
(367321,7,[0,0,0,1,2,407]),
(369709,2,[0,0,1,1135]),
(372289,17,[0,0,0,0,0,0,1,3,58]),
(372497,3,[0,0,0,0,10,132]),
(375367,3,[0,1,20,147]),
(375899,2,[0,9,632]),
(377393,3,[0,0,0,0,26,49]),
(380503,3,[0,1,1,998]),
(382087,5,[0,1,1,999]),
(383807,5,[0,1659]),
(383839,11,[0,1,3,5,7,11]),
(386963,2,[0,37,194]),
(387509,2,[0,0,4,724]),
(389083,2,[0,1,7,436]),
(389567,5,[0,28,274]),
(391337,3,[0,0,0,4,513]),
(394861,6,[0,0,1,2,637]),
(395677,2,[0,0,1,1,9,74]),
(396881,3,[0,0,0,0,2,4,4,12])]
def block29 : Array Row := #[
(396883,2,[0,1,1,6,210]),
(396887,5,[0,3,1095]),
(400753,7,[0,0,0,0,1,1,4,4,8]),
(401309,2,[0,0,12,348]),
(403483,2,[0,1,1378]),
(403721,6,[0,0,0,2,769]),
(406577,3,[0,0,0,0,1064]),
(406579,10,[0,1,1383]),
(406583,5,[0,4,959]),
(406591,6,[0,1,2,850]),
(411347,2,[0,5,5,198]),
(415517,2,[0,0,20,223]),
(415879,7,[0,1,1388]),
(418553,3,[0,0,0,29,89]),
(419291,6,[0,2,8,277]),
(420593,3,[0,0,0,0,24,57]),
(427717,2,[0,0,1,1,28,28]),
(432511,6,[0,1,2,5,185]),
(433261,10,[0,0,1,1,2,9,22]),
(433681,7,[0,0,0,0,1,2,5,33]),
(434561,3,[0,0,0,0,0,0,0,2,3,24]),
(434933,2,[0,0,48,91]),
(436307,2,[0,5,24,39]),
(436309,2,[0,0,1,26,70]),
(436313,3,[0,0,0,1315]),
(436343,5,[0,1694]),
(438409,7,[0,0,0,1,1,611]),
(439427,2,[0,5,930]),
(440723,2,[0,1699]),
(441827,2,[0,3,4,7,35]),
(442991,17,[0,2,10,225]),
(444293,2,[0,0,10,452]),
(444649,11,[0,0,0,1,24,42]),
(445541,2,[0,0,2,1018]),
(446657,5,[0,0,0,0,0,0,3,167]),
(451837,2,[0,0,1,1,3,4,37]),
(455537,3,[0,0,0,0,19,78]),
(457403,2,[0,4,6,199]),
(457987,2,[0,1,11,305]),
(465167,5,[0,5,948]),
(465169,7,[0,0,0,0,1,4,151]),
(465173,2,[0,0,1534]),
(465187,3,[0,1,10,12,17]),
(465743,5,[0,1713]),
(466673,3,[0,0,0,0,1112]),
(467633,3,[0,0,0,0,4,364]),
(468113,3,[0,0,0,0,6,266]),
(468239,7,[0,26,328]),
(468841,11,[0,0,0,1,2,476]),
(469279,6,[0,1,1,9,9,10]),
(469891,2,[0,1,1,2,8,48]),
(471853,2,[0,0,1,1,1,6,54]),
(472019,6,[0,15,17,20]),
(475367,5,[0,1715]),
(478403,2,[0,1719]),
(486971,2,[0,2,4,7,50]),
(488879,17,[0,5,964]),
(489299,2,[0,69,125]),
(491299,2,[0,1,1434]),
(494353,5,[0,0,0,0,1,1,437]),
(494561,3,[0,0,0,0,0,2,4,59]),
(494563,3,[0,1,33,107]),
(494567,5,[0,9,713]),
(494587,2,[0,1,1,1,1,13,19])]
def block30 : Array Row := #[
(494687,5,[0,1732]),
(497141,3,[0,0,2,3,15,18]),
(497309,2,[0,0,3,946]),
(498493,2,[0,0,1,1,17,48]),
(504011,2,[0,2,5,474]),
(505321,13,[0,0,0,1,2,497]),
(511151,7,[0,2,2,774]),
(512353,5,[0,0,0,0,0,1,1,1,107]),
(512579,2,[0,4,8,169]),
(514651,2,[0,1,2,2,14,20]),
(520721,3,[0,0,0,0,2,8,60]),
(523307,2,[0,3,1194]),
(523667,2,[0,4,5,278]),
(523669,6,[0,0,1,6,6,35]),
(523673,3,[0,0,0,18,164]),
(523681,13,[0,0,0,0,0,1,2,181]),
(528811,3,[0,1,2,944]),
(531911,7,[0,2,13,202]),
(533831,7,[0,2,4,8,46]),
(535757,2,[0,0,5,777]),
(539323,2,[0,1,3,838]),
(541951,7,[0,1,2,2,453]),
(542923,2,[0,1,12,320]),
(544613,3,[0,0,6,694]),
(545789,2,[0,0,1579]),
(550139,2,[0,12,643]),
(553097,3,[0,0,0,14,231]),
(553099,12,[0,1,3,5,169]),
(553103,5,[0,4,10,140]),
(553123,2,[0,1,1,1,775]),
(554011,2,[0,1,2,16,64]),
(556271,7,[0,2,4,5,76]),
(560863,5,[0,1,1,1137]),
(565651,2,[0,1,1,1,2,2,80]),
(567673,10,[0,0,0,1,3,10,28]),
(571541,7,[0,0,2,6,12,12]),
(575243,2,[0,19,484]),
(581891,2,[0,2,1337]),
(582761,3,[0,0,0,2,6,147]),
(582763,5,[0,1,1484]),
(582767,5,[0,18,507]),
(582773,2,[0,0,23,257]),
(582793,10,[0,0,0,1,3,442]),
(587263,3,[0,1,5,676]),
(588229,2,[0,0,1,1284]),
(589241,3,[0,0,0,2,881]),
(591079,3,[0,1,9,13,21]),
(592727,5,[0,1788]),
(600307,7,[0,1,3,867]),
(600641,3,[0,0,0,0,0,0,2,284]),
(603457,5,[0,0,0,0,0,0,1,3,86]),
(604759,11,[0,1,3,3,4,4,6]),
(605629,2,[0,0,1,1,928]),
(606899,6,[0,7,910]),
(609887,5,[0,1796]),
(612049,19,[0,0,0,0,1,12,63]),
(612797,2,[0,0,51,115]),
(614609,3,[0,0,0,0,27,71]),
(616207,3,[0,1,1499]),
(616789,6,[0,0,1,1,1,590]),
(617189,2,[0,0,4,5,5,22]),
(618301,6,[0,0,1,1,1,2,2,49]),
(618349,2,[0,0,1,48,48]),
(621139,2,[0,1,3,8,116])]
def block31 : Array Row := #[
(621583,5,[0,1,5,5,111]),
(622399,6,[0,1,3,3,9,20]),
(623401,31,[0,0,0,1,2,2,174]),
(634643,2,[0,1807]),
(636761,3,[0,0,0,2,907]),
(637781,2,[0,0,2,4,5,47]),
(639851,7,[0,2,2,18,42]),
(639853,2,[0,0,1,19,132]),
(639857,5,[0,0,0,0,3,9,44]),
(639907,2,[0,1,8,525]),
(641873,5,[0,0,0,0,3,4,97]),
(643583,5,[0,22,474]),
(649801,7,[0,0,0,1,1,2,2,7,7]),
(653357,2,[0,0,4,10,91]),
(654149,2,[0,0,4,886]),
(654767,5,[0,3,1258]),
(656651,2,[0,2,2,8,104]),
(658639,7,[0,1,1,1,822]),
(668273,3,[0,0,0,0,4,468]),
(668867,2,[0,4,1129]),
(668869,2,[0,0,1,33,78]),
(668873,3,[0,0,0,1442]),
(668879,7,[0,3,1272]),
(668903,5,[0,5,5,295]),
(669971,7,[0,2,3,6,102]),
(673781,2,[0,0,2,16,104]),
(679223,5,[0,91,126]),
(681931,2,[0,1,1,2,680]),
(691363,2,[0,1,1,1,3,10,16]),
(691381,2,[0,0,1,1,2,8,38]),
(692347,2,[0,1,8,9,39]),
(700933,2,[0,0,1,1339]),
(702869,2,[0,0,45,152]),
(704087,5,[0,1827]),
(712507,3,[0,1,1541]),
(712837,5,[0,0,1,1,980]),
(715811,2,[0,2,14,239]),
(717001,7,[0,0,0,1,2,2,2,51]),
(718183,5,[0,1,1,6,336]),
(725861,2,[0,0,2,1189]),
(725863,3,[0,1,1543]),
(725867,2,[0,6,11,105]),
(728699,2,[0,1833]),
(735107,2,[0,45,279]),
(735109,2,[0,0,1,4,579]),
(735113,3,[0,0,0,3,843]),
(737857,11,[0,0,0,0,0,0,1,1,1,3,17]),
(738923,2,[0,6,26,46]),
(741677,2,[0,0,5,6,145]),
(741679,3,[0,1,3,945]),
(741683,2,[0,15,655]),
(741691,2,[0,1,1,1,2,12,18]),
(741709,13,[0,0,1,1,4,283]),
(743423,5,[0,67,184]),
(752581,2,[0,0,1,1,2,11,29]),
(766813,5,[0,0,1,1365]),
(768479,17,[0,17,624]),
(771739,2,[0,1,4,4,178]),
(773029,2,[0,0,1,1,28,44]),
(773063,5,[0,22,528]),
(774217,5,[0,0,0,1,1,787]),
(779039,14,[0,5,7,7,22]),
(780049,11,[0,0,0,0,1,1,567]),
(790201,7,[0,0,0,1,1,2,2,84])]
def block32 : Array Row := #[
(791677,5,[0,0,1,1,1012]),
(801379,2,[0,1,1,46,46]),
(801403,3,[0,1,3,969]),
(803893,2,[0,0,1,10,318]),
(806951,26,[0,2,2,912]),
(810581,3,[0,0,2,1214]),
(810583,3,[0,1,15,356]),
(810587,2,[0,3,1336]),
(813343,3,[0,1,60,91]),
(814859,2,[0,4,1191]),
(816377,3,[0,0,0,4,742]),
(817721,6,[0,0,0,2,988]),
(817723,2,[0,1,1,1,7,138]),
(817727,7,[0,3,5,516]),
(818689,17,[0,0,0,0,0,0,0,0,0,1,5,12]),
(823541,2,[0,0,2,1220]),
(826667,2,[0,8,952]),
(826669,10,[0,0,1,1,1031]),
(826673,3,[0,0,0,0,3,4,4,17]),
(826681,17,[0,0,0,1,2,22,22]),
(826697,3,[0,0,0,5,692]),
(828587,2,[0,4,1200]),
(832681,13,[0,0,0,1,1,1,1,2,54]),
(837979,7,[0,1,1587]),
(839921,3,[0,0,0,0,2,783]),
(845983,13,[0,1,1,13,182]),
(846259,2,[0,1,3,984]),
(849763,2,[0,1,1,6,379]),
(852301,2,[0,0,1,1,2,2,160]),
(869273,3,[0,0,0,43,102]),
(876041,3,[0,0,0,2,4,4,41]),
(886759,3,[0,1,1600]),
(895627,2,[0,1,1,1288]),
(895667,2,[0,8,975]),
(895669,2,[0,0,1,25,130]),
(895673,3,[0,0,0,1528]),
(895691,2,[0,2,13,308]),
(895721,6,[0,0,0,2,3,3,87]),
(903613,5,[0,0,1,54,61]),
(912559,6,[0,1,1607]),
(914971,2,[0,1,2,3,508]),
(915727,3,[0,1,3,1009]),
(921821,2,[0,0,2,1253]),
(923561,6,[0,0,0,2,4,311]),
(924431,7,[0,2,5,5,100]),
(931123,2,[0,1,1,1,13,78]),
(942167,5,[0,82,182]),
(947197,5,[0,0,1,1,22,65]),
(960373,2,[0,0,1,1,3,11,26]),
(962413,2,[0,0,1,4,8,65]),
(965773,2,[0,0,1,1,33,43]),
(977803,2,[0,1,3,10,132]),
(981151,6,[0,1,2,2,10,46]),
(985993,5,[0,0,0,1,3,601]),
(991883,2,[0,6,1113]),
(1000579,2,[0,1,7,18,31]),
(1006147,2,[0,1,1,1328]),
(1014257,3,[0,0,0,0,1361]),
(1014259,2,[0,1,3,7,10,12]),
(1014263,5,[0,20,652]),
(1014287,5,[0,3,5,580]),
(1014317,2,[0,0,51,177]),
(1027051,3,[0,1,2,2,12,38]),
(1029751,3,[0,1,2,2,2,219])]
def block33 : Array Row := #[
(1040803,3,[0,1,3,1056]),
(1043873,3,[0,0,0,0,0,1153]),
(1052473,5,[0,0,0,1,1238]),
(1059103,3,[0,1,1,1,4,273]),
(1059703,3,[0,1,3,8,183]),
(1064159,13,[0,34,451]),
(1067893,5,[0,0,1,3,834]),
(1069979,2,[0,3,5,602]),
(1070009,3,[0,0,0,31,171]),
(1072397,2,[0,0,5,12,95]),
(1089227,2,[0,1943]),
(1096399,3,[0,1,1,6,452]),
(1101641,3,[0,0,0,2,1083]),
(1105427,2,[0,3,8,437]),
(1108229,7,[0,0,4,23,60]),
(1115029,2,[0,0,1,1,14,119]),
(1126963,3,[0,1,1,32,87]),
(1127813,2,[0,0,3,14,147]),
(1130431,3,[0,1,2,3,3,135]),
(1140137,3,[0,0,0,15,370]),
(1140619,2,[0,1,13,511]),
(1142777,3,[0,0,0,46,122]),
(1163711,17,[0,2,1535]),
(1163713,5,[0,0,0,0,0,0,1,4,7,9]),
(1163717,2,[0,0,16,544]),
(1163737,5,[0,0,0,1,1,3,332]),
(1163783,5,[0,1957]),
(1167623,5,[0,13,851]),
(1187701,2,[0,0,1,2,2,11,27]),
(1201283,2,[0,1969]),
(1203893,2,[0,0,1791]),
(1206869,2,[0,0,5,1034]),
(1211701,2,[0,0,1,2,2,3,105]),
(1214189,2,[0,0,1794]),
(1220803,2,[0,1,4,15,69]),
(1227871,6,[0,1,1,2,3,292]),
(1229461,2,[0,0,1,2,10,120]),
(1235807,10,[0,4,5,9,34]),
(1237231,6,[0,1,1,2,16,50]),
(1244401,13,[0,0,0,0,1,2,2,6,17]),
(1248103,6,[0,1,1,1,9,138]),
(1251037,5,[0,0,1,1,7,10,16]),
(1255313,3,[0,0,0,0,18,192]),
(1258219,2,[0,1,1,5,7,60]),
(1265857,11,[0,0,0,0,0,0,1,7,68]),
(1269847,5,[0,1,1,7,14,21]),
(1280833,5,[0,0,0,0,0,0,1,3,161]),
(1286981,2,[0,0,2,49,59]),
(1292591,11,[0,2,5,17,37]),
(1292593,20,[0,0,0,0,1,3,471]),
(1292597,2,[0,0,1813]),
(1301387,2,[0,7,8,235]),
(1301389,13,[0,0,1,4,763]),
(1301393,3,[0,0,0,0,37,94]),
(1301423,5,[0,12,16,56]),
(1301459,2,[0,97,203]),
(1301929,7,[0,0,0,1,6,417]),
(1308299,2,[0,1998]),
(1309067,5,[0,4,36,74]),
(1309129,11,[0,0,0,1,1316]),
(1314361,17,[0,0,0,1,1,1,2,198]),
(1323499,3,[0,1,4,4,277]),
(1326683,2,[0,3,43,93]),
(1327577,3,[0,0,0,1629])]
def block34 : Array Row := #[
(1328003,2,[0,5,5,478]),
(1329499,2,[0,1,1,50,65]),
(1347053,2,[0,0,3,1274]),
(1353269,2,[0,0,3,6,388]),
(1360981,2,[0,0,1,1,2,679]),
(1361441,3,[0,0,0,0,0,2,18,30]),
(1363559,7,[0,3,1485]),
(1370459,2,[0,115,179]),
(1379857,5,[0,0,0,0,1,6,7,23]),
(1379887,5,[0,1,1712]),
(1382651,6,[0,2,2,1084]),
(1389469,2,[0,0,1,23,211]),
(1395743,5,[0,92,226]),
(1396999,3,[0,1,1,1414]),
(1403617,5,[0,0,0,0,0,1,877]),
(1419679,3,[0,1,1,5,610]),
(1422601,13,[0,0,0,1,2,2,339]),
(1423061,2,[0,0,2,1393]),
(1427401,7,[0,0,0,1,1,2,2,5,17]),
(1454021,3,[0,0,2,1398]),
(1454041,11,[0,0,0,1,1,2,3,105]),
(1475899,2,[0,1,1729]),
(1476983,5,[0,5,1333]),
(1478837,2,[0,0,1838]),
(1478839,3,[0,1,1731]),
(1478843,2,[0,25,670]),
(1486841,3,[0,0,0,2,1193]),
(1486843,2,[0,1,3,1182]),
(1486847,5,[0,2037]),
(1486873,5,[0,0,0,1,1,27,43]),
(1486907,2,[0,12,955]),
(1505521,7,[0,0,0,0,1,1,1,2,6,12]),
(1507789,2,[0,0,1,1,1,8,110]),
(1520887,3,[0,1,1742]),
(1536959,7,[0,2040]),
(1538837,2,[0,0,5,25,61]),
(1540813,2,[0,0,1,3,5,6,22]),
(1546199,7,[0,8,1164]),
(1556927,5,[0,3,3,906]),
(1560203,2,[0,3,1525]),
(1569541,6,[0,0,1,2,3,11,25]),
(1577377,5,[0,0,0,0,0,1,1,573]),
(1583287,3,[0,1,1753]),
(1600153,10,[0,0,0,1,17,182]),
(1606763,2,[0,11,1008]),
(1631261,2,[0,0,2,1432]),
(1646147,2,[0,17,26,31]),
(1646149,2,[0,0,1,3,977]),
(1646153,3,[0,0,0,34,220]),
(1646189,2,[0,0,85,157]),
(1646237,3,[0,0,7,1006]),
(1648217,3,[0,0,0,1676]),
(1663091,2,[0,2,4,5,191]),
(1665701,2,[0,0,2,2,924]),
(1681807,5,[0,1,3,8,269]),
(1724389,2,[0,0,1,1593]),
(1726859,2,[0,3,3,18,55]),
(1736599,7,[0,1,13,15,30]),
(1737161,3,[0,0,0,2,32,65]),
(1753637,2,[0,0,1882]),
(1761049,7,[0,0,0,1,1,1,10,55]),
(1765831,3,[0,1,2,4,563]),
(1768673,3,[0,0,0,0,0,7,394]),
(1775273,3,[0,0,0,1700])]
def block35 : Array Row := #[
(1778597,2,[0,0,1888]),
(1781203,2,[0,1,60,175]),
(1784441,3,[0,0,0,2,3,629]),
(1785599,7,[0,112,228]),
(1796759,17,[0,122,216]),
(1798309,6,[0,0,1,1,1,923]),
(1816141,2,[0,0,1,2,1127]),
(1818631,3,[0,1,1,2,4,4,38]),
(1824499,2,[0,1,1,1,5,8,29]),
(1826047,5,[0,1,1,49,85]),
(1848863,5,[0,2092]),
(1852241,3,[0,0,0,0,2,5,5,32]),
(1852243,3,[0,1,3,1240]),
(1852247,5,[0,4,16,224]),
(1852283,2,[0,8,18,109]),
(1852327,3,[0,1,1,3,17,52]),
(1854277,6,[0,0,1,1610]),
(1864267,2,[0,1,1803]),
(1864859,2,[0,15,20,52]),
(1871641,11,[0,0,0,1,1,1,2,268]),
(1873217,3,[0,0,0,0,0,0,1116]),
(1877303,5,[0,3,1575]),
(1894229,2,[0,0,3,1382]),
(1899119,31,[0,5,1400]),
(1913651,2,[0,2,2,1203]),
(1948909,2,[0,0,1,5,5,10,10]),
(1959961,7,[0,0,0,1,2,918]),
(1960121,6,[0,0,0,2,1283]),
(1995031,6,[0,1,1,1,1,1,2,141]),
(2007199,3,[0,1,1,7,601]),
(2027587,2,[0,1,4,10,166]),
(2028371,2,[0,2,8,725]),
(2035723,2,[0,1,5,1074]),
(2044979,2,[0,5,1417]),
(2045851,14,[0,1,2,2,8,107]),
(2060447,7,[0,10,38,45]),
(2060449,7,[0,0,0,0,0,1,5,5,30]),
(2060453,2,[0,0,73,220]),
(2060503,3,[0,1,6,985]),
(2060561,3,[0,0,0,0,2,13,108]),
(2075761,11,[0,0,0,0,1,1,1,2,10,10]),
(2100893,2,[0,0,119,138]),
(2128319,7,[0,2117]),
(2135851,2,[0,1,2,2,9,93]),
(2145103,5,[0,1,1830]),
(2174063,5,[0,4,6,597]),
(2201599,3,[0,1,1,3,25,39]),
(2203519,6,[0,1,54,225]),
(2243453,2,[0,0,1952]),
(2245681,19,[0,0,0,0,1,1,2,413]),
(2248373,3,[0,0,3,16,217]),
(2249179,2,[0,1,12,12,47]),
(2249861,2,[0,0,2,8,18,20]),
(2275657,5,[0,0,0,1,1475]),
(2292523,2,[0,1,1845]),
(2324381,2,[0,0,2,8,10,37]),
(2328413,2,[0,0,7,1131]),
(2335241,3,[0,0,0,2,21,130]),
(2335243,2,[0,1,3,3,5,5,14]),
(2335247,5,[0,2139]),
(2335303,3,[0,1,1,32,160]),
(2335367,11,[0,4,7,11,35]),
(2347379,2,[0,4,1508]),
(2400143,5,[0,8,1300])]
def block36 : Array Row := #[
(2402567,5,[0,2141]),
(2411287,3,[0,1,91,145]),
(2411821,2,[0,0,1,1,2,848]),
(2422327,3,[0,1,1861]),
(2437777,5,[0,0,0,0,1,1,1,1,1,1,4,7]),
(2444621,2,[0,0,2,1548]),
(2450387,2,[0,181,187]),
(2524531,7,[0,1,2,7,13,26]),
(2556101,2,[0,0,2,2,1067]),
(2568061,2,[0,0,1,1,2,4,210]),
(2577857,3,[0,0,0,0,0,0,14,147]),
(2578799,11,[0,6,20,174]),
(2590079,7,[0,23,874]),
(2595601,11,[0,0,0,0,1,1,2,2,3,26]),
(2644151,11,[0,2,2,1303]),
(2644153,5,[0,0,0,1,3,902]),
(2644157,2,[0,0,13,897]),
(2644219,2,[0,1,1,1,8,313]),
(2644339,2,[0,1,1884]),
(2656499,2,[0,5,22,201]),
(2664197,2,[0,0,21,709]),
(2713981,6,[0,0,1,2,1247]),
(2734481,6,[0,0,0,0,2,3,7,54]),
(2740919,11,[0,2183]),
(2765297,3,[0,0,0,0,78,82]),
(2765299,2,[0,1,7,30,42]),
(2765303,5,[0,2186]),
(2765369,3,[0,0,0,12,709]),
(2765453,2,[0,0,2012]),
(2773019,2,[0,8,8,363]),
(2791123,2,[0,1,1898]),
(2807551,13,[0,1,1,2,2,6,72]),
(2843689,17,[0,0,0,1,14,352]),
(2889787,5,[0,1,7,1062]),
(2945333,2,[0,0,5,5,508]),
(3009637,2,[0,0,1,1,1,1,3,216]),
(3039269,2,[0,0,121,188]),
(3054673,5,[0,0,0,0,1,1,1,1,338]),
(3076039,3,[0,1,1,3,1049]),
(3086957,2,[0,0,2041]),
(3087907,2,[0,1,1929]),
(3120317,2,[0,0,6,1251]),
(3120319,3,[0,1,1,8,677]),
(3120323,2,[0,15,1118]),
(3120407,5,[0,2215]),
(3120497,3,[0,0,0,0,25,290]),
(3200941,6,[0,0,1,1,2,947]),
(3254183,5,[0,26,903]),
(3273811,3,[0,1,2,9,15,19]),
(3279949,2,[0,0,1,3,1207]),
(3284441,3,[0,0,0,2,36,98]),
(3301777,5,[0,0,0,0,1,1,1,683]),
(3360563,2,[0,11,1248]),
(3390217,5,[0,0,0,1,9,541]),
(3391537,10,[0,0,0,0,1,1392]),
(3436831,3,[0,1,1,1,1,2,500]),
(3474323,2,[0,2234]),
(3517541,3,[0,0,2,5,22,37]),
(3535447,3,[0,1,1965]),
(3559519,3,[0,1,1,1,9,328]),
(3563519,7,[0,3,1744]),
(3568781,3,[0,0,2,1645]),
(3568783,3,[0,1,3,10,376]),
(3568787,2,[0,5,65,83])]
def block37 : Array Row := #[
(3568883,2,[0,2242]),
(3568991,17,[0,2,39,305]),
(3574111,3,[0,1,2,28,182]),
(3576217,5,[0,0,0,1,3,3,405]),
(3581971,2,[0,1,2,3,11,88]),
(3597197,2,[0,0,128,202]),
(3610331,2,[0,2,1832]),
(3617639,11,[0,7,10,11,22]),
(3625619,2,[0,7,20,213]),
(3662917,5,[0,0,1,1797]),
(3729499,2,[0,1,1984]),
(3753671,11,[0,2,1841]),
(3754607,5,[0,2261]),
(3764003,2,[0,4,1632]),
(3819943,6,[0,1,1,3,3,17,19]),
(3838391,7,[0,2,1847]),
(3851807,5,[0,3,1764]),
(3857941,2,[0,0,1,1,2,1002]),
(3861547,2,[0,1,5,10,249]),
(3876979,10,[0,1,3,3,845]),
(3886951,3,[0,1,2,2,1070]),
(3918149,2,[0,0,5,35,94]),
(3941923,5,[0,1,64,311]),
(3970529,3,[0,0,0,0,0,30,164]),
(3985297,11,[0,0,0,0,1,3,9,79]),
(3998629,2,[0,0,1,1,10,452]),
(3999389,2,[0,0,90,315]),
(4011827,2,[0,3,3,5,14,18]),
(4020691,11,[0,1,2,47,109]),
(4027279,7,[0,1,7,1181]),
(4044751,12,[0,1,2,2,2,565]),
(4056737,3,[0,0,0,0,0,66,75]),
(4056739,2,[0,1,3,1481]),
(4056743,5,[0,2271]),
(4056853,5,[0,0,1,14,665]),
(4056971,2,[0,2,8,10,103]),
(4057423,3,[0,1,49,397]),
(4089209,3,[0,0,0,1926]),
(4091587,5,[0,1,2011]),
(4105181,3,[0,0,2,22,350]),
(4128307,12,[0,1,3,5,679]),
(4150169,3,[0,0,0,4,1263]),
(4154083,2,[0,1,2014]),
(4161119,7,[0,5,5,5,160]),
(4202911,6,[0,1,1,2,6,12,18]),
(4206439,6,[0,1,1,1,17,205]),
(4215191,7,[0,2,3,1346]),
(4225589,2,[0,0,6,1354]),
(4256639,7,[0,2282]),
(4262653,2,[0,0,1,1,1,9,217]),
(4275043,3,[0,1,2018]),
(4277171,2,[0,2,1872]),
(4286251,2,[0,1,1,1,2,2,2,2,30]),
(4294441,13,[0,0,0,1,1,2,21,35]),
(4343299,7,[0,1,37,512]),
(4392853,5,[0,0,1,15,650]),
(4393153,5,[0,0,0,0,0,0,1,1,9,55]),
(4413349,2,[0,0,1,1,13,389]),
(4430221,2,[0,0,1,2,14,246]),
(4450169,3,[0,0,0,1951]),
(4483123,2,[0,1,3,39,112]),
(4497151,7,[0,1,2,2,3,505]),
(4514023,3,[0,1,1,1,40,90]),
(4542331,12,[0,1,2,5,7,111])]
def block38 : Array Row := #[
(4549351,3,[0,1,2,2,5,334]),
(4555241,3,[0,0,0,2,14,346]),
(4562923,3,[0,1,3,5,17,32]),
(4585523,2,[0,12,1329]),
(4602443,2,[0,5,49,136]),
(4630601,3,[0,0,0,2,2,5,5,32]),
(4630603,2,[0,1,111,204]),
(4630607,5,[0,46,790]),
(4630723,2,[0,1,14,919]),
(4630849,14,[0,0,0,0,0,0,1,23,57]),
(4635847,6,[0,1,1,1,61,61]),
(4643339,2,[0,3,3,1266]),
(4650109,2,[0,0,1,1849]),
(4727501,2,[0,0,2,2,2,2,10,17]),
(4772459,2,[0,7,1556]),
(4798889,3,[0,0,0,14,837]),
(4800287,5,[0,2303]),
(4865137,5,[0,0,0,0,1,21,207]),
(4889243,2,[0,2309]),
(4936649,3,[0,0,0,16,781]),
(4944949,2,[0,0,1,35,375]),
(4992677,2,[0,0,5,1478]),
(5010751,3,[0,1,1,2,2,2,6,31]),
(5052373,2,[0,0,1,5,33,50]),
(5085779,2,[0,93,560]),
(5101043,2,[0,9,11,340]),
(5140781,11,[0,0,2,11,652]),
(5161267,2,[0,1,1,1,4,720]),
(5180159,31,[0,2316]),
(5238137,3,[0,0,0,1999]),
(5238139,2,[0,1,16,884]),
(5238143,5,[0,3,5,6,262]),
(5238293,2,[0,0,27,824]),
(5238449,3,[0,0,0,0,6,973]),
(5243593,5,[0,0,0,1,13,554]),
(5269007,5,[0,22,1141]),
(5341381,7,[0,0,1,2,4,697]),
(5359769,3,[0,0,0,2008]),
(5441573,2,[0,0,33,761]),
(5534351,7,[0,2,2,6,6,75]),
(5546039,7,[0,2333]),
(5656379,6,[0,3,5,1136]),
(5725133,2,[0,0,3,33,231]),
(5735963,2,[0,11,1413]),
(5794109,2,[0,0,192,202]),
(5835251,2,[0,2,2,2,6,219]),
(5835253,2,[0,0,1,50,309]),
(5835257,3,[0,0,0,3,21,214]),
(5835421,6,[0,0,1,1,2,6,288]),
(5835601,11,[0,0,0,0,1,1,2,2,255]),
(5843441,3,[0,0,0,0,2,1400]),
(5869411,2,[0,1,2,40,182]),
(5890667,2,[0,2338]),
(5910397,2,[0,0,1,12,12,61]),
(5982877,2,[0,0,1,1,1,10,274]),
(5985029,3,[0,0,3,1685]),
(6086351,13,[0,2,2,1545]),
(6120253,2,[0,0,1,1,1,17,157]),
(6167891,2,[0,2,1979]),
(6195341,7,[0,0,2,25,408]),
(6199153,5,[0,0,0,0,1,6,19,27]),
(6200167,3,[0,1,3,3,997]),
(6267841,11,[0,0,0,0,0,0,1,2,633]),
(6421561,7,[0,0,0,1,2,16,154])]
def block39 : Array Row := #[
(6479831,13,[0,2,3,1468]),
(6508361,3,[0,0,0,2,1620]),
(6508363,2,[0,1,3,22,281]),
(6508367,5,[0,2351]),
(6508549,2,[0,0,1,1,1646]),
(6508741,6,[0,0,1,2,3,900]),
(6520487,5,[0,3,6,1082]),
(6620951,7,[0,2,2,3,967]),
(6652301,2,[0,0,2,2,1374]),
(6729607,3,[0,1,1,5,1104]),
(6735581,2,[0,0,2,62,183]),
(6796631,7,[0,2,40,468]),
(6834407,5,[0,20,1259]),
(6892271,7,[0,2,3,4,730]),
(6895303,3,[0,1,6,1381]),
(6921637,6,[0,0,1,18,716]),
(6939083,2,[0,13,1429]),
(7181831,13,[0,2,2022]),
(7235279,7,[0,2375]),
(7243837,6,[0,0,1,6,1183]),
(7265983,3,[0,1,15,20,64]),
(7368601,26,[0,0,0,1,2,2,825]),
(7374161,3,[0,0,0,0,2,1467]),
(7374163,2,[0,1,32,732]),
(7374167,5,[0,7,1661]),
(7374361,13,[0,0,0,1,2,3,723]),
(7374569,3,[0,0,0,2090]),
(7378571,2,[0,2,2030]),
(7479233,3,[0,0,0,0,0,0,8,554]),
(7528007,5,[0,2381]),
(7528111,3,[0,1,2,6,9,96]),
(7638509,2,[0,0,6,1529]),
(7755619,3,[0,1,5,1492]),
(7800491,6,[0,2,2046]),
(7859777,3,[0,0,0,0,0,0,30,162]),
(7912651,3,[0,1,2,2,6,9,27]),
(8007143,7,[0,4,5,1091]),
(8244793,10,[0,0,0,1,1,62,73]),
(8278619,2,[0,13,1479]),
(8371061,7,[0,0,2,1869]),
(8371063,5,[0,1,1,3,3,751]),
(8371067,5,[0,4,1844]),
(8371331,2,[0,2,4,1408]),
(8371613,2,[0,0,10,41,73]),
(8400011,2,[0,2,19,812]),
(8406847,10,[0,1,1,3,1376]),
(8458039,3,[0,1,1,1906]),
(8513731,7,[0,1,1,2,1472]),
(8559827,2,[0,4,1850]),
(8559829,6,[0,0,1,1,14,552]),
(8559833,3,[0,0,0,2119]),
(8560073,3,[0,0,0,2120]),
(8560319,11,[0,5,1815]),
(8580413,2,[0,0,2284]),
(8607943,3,[0,1,1,3,15,208]),
(8710313,5,[0,0,0,5,17,219]),
(9007861,2,[0,0,1,2,1605]),
(9091429,2,[0,0,1,16,838]),
(9100501,2,[0,0,1,2,2,2,610]),
(9125323,2,[0,1,2209]),
(9204887,5,[0,2436]),
(9341599,6,[0,1,3,1701]),
(9357317,2,[0,0,13,1312]),
(9382103,5,[0,112,682])]
def block40 : Array Row := #[
(9455003,2,[0,2445]),
(9597779,2,[0,2447]),
(9646717,5,[0,0,1,2051]),
(9667711,7,[0,1,1,2,5,707]),
(9778031,7,[0,2,2099]),
(9778033,5,[0,0,0,0,1,1,4,615]),
(9778037,2,[0,0,8,8,524]),
(9778309,11,[0,0,1,2057]),
(9778589,2,[0,0,8,36,122]),
(9811001,6,[0,0,0,2,2,2,762]),
(9820541,2,[0,0,2,8,11,105]),
(9976067,5,[0,8,32,248]),
(10013431,7,[0,1,2,3,12,191]),
(10061039,7,[0,5,1848]),
(10151797,2,[0,0,1,2073]),
(10212011,6,[0,2,17,926]),
(10234151,7,[0,2,2,44,174]),
(10313899,2,[0,1,3,11,640]),
(10360319,7,[0,2460]),
(10375199,7,[0,20,40,77]),
(10421441,6,[0,0,0,0,0,0,2,9,187]),
(10681147,3,[0,1,1,1,1,3,749]),
(10689083,2,[0,30,1225]),
(11047273,5,[0,0,0,1,61,246]),
(11048813,2,[0,0,16,1260]),
(11068703,5,[0,2471]),
(11093179,10,[0,1,2250]),
(11097761,7,[0,0,0,0,0,2,33,94]),
(11163851,6,[0,2,2,1707]),
(11163853,5,[0,0,1,1,1,3,883]),
(11163857,3,[0,0,0,0,4,32,89]),
(11164171,3,[0,1,2,26,453]),
(11164493,2,[0,0,2334]),
(11222539,14,[0,1,15,1180]),
(11282683,11,[0,1,9,17,178]),
(11285431,3,[0,1,2,5,7,239]),
(11318603,2,[0,280,405]),
(11324473,5,[0,0,0,1,1907]),
(11450267,2,[0,2474]),
(11475767,5,[0,10,57,123]),
(11588219,2,[0,2476]),
(11684609,3,[0,0,0,0,0,0,0,0,5,445]),
(11714707,2,[0,1,1,1,1,1397]),
(11819719,3,[0,1,1,2000]),
(11864473,10,[0,0,0,1,1915]),
(11893913,3,[0,0,0,55,585]),
(11943641,3,[0,0,0,2,14,627]),
(11990483,2,[0,3,7,1246]),
(12214339,2,[0,1,2272]),
(12274763,2,[0,86,854]),
(12274937,3,[0,0,0,18,1028]),
(12559369,34,[0,0,0,1,1931]),
(12651437,2,[0,0,3,1891]),
(12651643,2,[0,1,1,2016]),
(12672119,11,[0,10,64,118]),
(12704999,13,[0,12,12,466]),
(12745361,3,[0,0,0,0,2,64,96]),
(12745363,5,[0,1,3,20,495]),
(12745367,5,[0,14,1578]),
(12745721,3,[0,0,0,2,5,30,43]),
(12746081,7,[0,0,0,0,0,2,9,12,18]),
(12772553,3,[0,0,0,5,42,116]),
(12836933,2,[0,0,7,18,352]),
(12895837,2,[0,0,1,9,1192])]
def block41 : Array Row := #[
(12932789,2,[0,0,4,39,264]),
(12959663,5,[0,2496]),
(13091291,2,[0,2,2171]),
(13493413,2,[0,0,1,1,1,26,197]),
(13784543,5,[0,2509]),
(13814873,3,[0,0,0,2232]),
(13876501,6,[0,0,1,2,2,2,4,9,9]),
(14206321,14,[0,0,0,0,1,1,1,2,636]),
(14293003,2,[0,1,90,556]),
(14535097,7,[0,0,0,1,1972]),
(14540411,2,[0,2,2196]),
(14540413,2,[0,0,1,2144]),
(14540417,3,[0,0,0,0,0,0,0,4,8,86]),
(14540821,2,[0,0,1,2,3,23,76]),
(14541257,3,[0,0,0,6,1509]),
(14584667,2,[0,7,1846]),
(15194041,26,[0,0,0,1,2,15,342]),
(15209731,2,[0,1,1,2,6,767]),
(15290897,3,[0,0,0,0,7,40,59]),
(15772333,2,[0,0,1,2172]),
(15810661,2,[0,0,1,1,1,2,7,8,18]),
(15855263,5,[0,14,1630]),
(16373671,6,[0,1,2,1944]),
(16498103,5,[0,181,679]),
(16506227,2,[0,4,8,1153]),
(16556777,3,[0,0,0,6,15,331]),
(16556779,2,[0,1,1,1,3,1237]),
(16556783,5,[0,4,2038]),
(16557239,29,[0,2534]),
(16557707,2,[0,4,24,686]),
(16944887,5,[0,3,3,3,6,230]),
(17000443,2,[0,1,1,1,1,6,615]),
(17100173,2,[0,0,2418]),
(17340923,2,[0,287,522]),
(17433457,7,[0,0,0,0,1,53,228]),
(17455337,3,[0,0,0,29,974]),
(17566291,2,[0,1,1,2,3,1088]),
(17607211,2,[0,1,2,13,853]),
(17932493,2,[0,0,2428]),
(17952509,2,[0,0,3,9,1015]),
(18392683,3,[0,1,3,4,12,163]),
(18625613,2,[0,0,25,1254]),
(18858737,3,[0,0,0,0,5,19,205]),
(18858739,10,[0,1,30,1055]),
(18858743,5,[0,3,2178]),
(18859271,13,[0,2,11,1294]),
(18859823,5,[0,16,58,105]),
(19058203,2,[0,1,1,13,1052]),
(19647763,2,[0,1,29,1110]),
(19803067,2,[0,1,11,1457]),
(20152819,2,[0,1,1,3,3,20,64]),
(20428549,2,[0,0,1,3,1725]),
(20592259,2,[0,1,17,1332]),
(20611883,2,[0,321,528]),
(20756053,7,[0,0,1,1,72,246]),
(21038291,2,[0,2,3,5,17,74]),
(21054403,2,[0,1,1,12,14,110]),
(21197653,5,[0,0,1,3,79,112]),
(21302527,6,[0,1,3,93,173]),
(21482789,2,[0,0,81,836]),
(21519581,2,[0,0,2,10,17,103]),
(21519583,5,[0,1,3,8,1018]),
(21519587,5,[0,4,6,37,70]),
(21520189,2,[0,0,1,1,1,1665])]
def block42 : Array Row := #[
(21520799,11,[0,5,5,1363]),
(21708151,6,[0,1,2,2,6,712]),
(21962179,2,[0,1,1,1,1,3,27,41]),
(22150741,6,[0,0,1,2,10,814]),
(22289807,10,[0,3,3,4,8,9,10]),
(22376537,6,[0,0,0,3,3,5,509]),
(22578293,2,[0,0,4,10,921]),
(22624271,13,[0,2,142,377]),
(23072963,2,[0,4,84,342]),
(23135153,3,[0,0,0,0,12,1179]),
(23381233,5,[0,0,0,0,1,3,3,767]),
(23826497,3,[0,0,0,0,0,0,1839]),
(24024727,5,[0,1,1,4,18,276]),
(24257099,2,[0,159,839]),
(24549521,3,[0,0,0,0,2,7,10,97]),
(24549523,2,[0,1,2406]),
(24549527,5,[0,2609]),
(24550213,5,[0,0,1,2274]),
(24550919,7,[0,3,2235]),
(24946781,2,[0,0,2,18,961]),
(25578269,3,[0,0,6,96,130]),
(25619189,2,[0,0,3,2088]),
(25750771,3,[0,1,2,10,1085]),
(25956011,6,[0,2,2317]),
(25990907,2,[0,14,1765]),
(26161771,2,[0,1,2,9,1126]),
(26236723,2,[0,1,185,480]),
(26581327,3,[0,1,2426]),
(26610917,2,[0,0,6,1852]),
(27033707,5,[0,3,6,24,192]),
(27084667,2,[0,1,3,9,11,109]),
(27380993,3,[0,0,0,0,0,0,0,0,1510]),
(27667207,5,[0,1,1,3,8,753]),
(27999611,6,[0,2,17,44,50]),
(27999613,2,[0,0,1,1,6,1250]),
(27999617,3,[0,0,0,0,0,0,0,7,9,77]),
(28000381,10,[0,0,1,2,1900]),
(28001161,7,[0,0,0,1,1,1,2,4,338]),
(28001921,7,[0,0,0,0,0,0,0,2,1236]),
(28062313,7,[0,0,0,1,71,423]),
(28149103,3,[0,1,1,8,1385]),
(28259969,3,[0,0,0,0,0,0,0,4,982]),
(28319381,2,[0,0,2,14,14,115]),
(29000617,5,[0,0,0,1,132,252]),
(29282633,3,[0,0,0,28,1163]),
(29291593,5,[0,0,0,1,4,41,111]),
(29510179,3,[0,1,55,962]),
(29820239,7,[0,3,15,1212]),
(30029369,3,[0,0,0,2379]),
(30095479,3,[0,1,1,3,1718]),
(30430069,6,[0,0,1,6,13,442]),
(30441527,5,[0,6,6,1302]),
(30707129,3,[0,0,0,2383]),
(30760391,7,[0,2,2342]),
(30892753,7,[0,0,0,0,1,1,1,1,4,4,44]),
(31838561,3,[0,0,0,0,0,2,5,894]),
(31838563,2,[0,1,1,1,3,1445]),
(31838567,5,[0,7,48,460]),
(31839469,2,[0,0,1,16,1245]),
(31840381,2,[0,0,1,1,2,4,5,202]),
(31842137,3,[0,0,0,112,631]),
(31937333,2,[0,0,3,2132]),
(32361893,2,[0,0,10,1749]),
(32910379,3,[0,1,8,1717])]
def block43 : Array Row := #[
(32996471,14,[0,2,5,1743]),
(33450871,21,[0,1,2,2127]),
(33469193,3,[0,0,0,6,1730]),
(33559129,11,[0,0,0,1,1,14,14,46]),
(33635939,2,[0,3,2304]),
(33891943,5,[0,1,3,2052]),
(34438543,3,[0,1,45,1105]),
(34808297,3,[0,0,0,219,416]),
(34977169,14,[0,0,0,0,1,1,61,144]),
(35028311,13,[0,2,8,1608]),
(35574083,2,[0,193,890]),
(35864987,2,[0,2662]),
(36365711,7,[0,2,9,1555]),
(36365713,5,[0,0,0,0,1,16,838]),
(36365717,2,[0,0,2553]),
(36366731,2,[0,2,212,381]),
(36367033,5,[0,0,0,1,5,49,96]),
(36367819,3,[0,1,11,1623]),
(36629081,3,[0,0,0,2,2089]),
(36999587,2,[0,5,2193]),
(37134833,3,[0,0,0,0,3,31,353]),
(37297181,3,[0,0,2,2258]),
(37309411,2,[0,1,1,1,1,2,1252]),
(38000497,7,[0,0,0,0,1,2048]),
(38107469,2,[0,0,3,2180]),
(38265719,7,[0,10,1980]),
(38328397,2,[0,0,1,7,8,669]),
(38469203,2,[0,8,10,15,96]),
(38769791,7,[0,2,2387]),
(39215611,3,[0,1,1,1,2,3,991]),
(39631937,3,[0,0,0,0,0,0,51,360]),
(39795373,2,[0,0,1,1,2125]),
(40492607,5,[0,3,4,6,899]),
(40509961,11,[0,0,0,1,2,1819]),
(40843729,17,[0,0,0,0,1,1,1777]),
(40846063,5,[0,1,31,36,66]),
(40913161,53,[0,0,0,1,2,72,157]),
(40955359,3,[0,1,18,1498]),
(41339863,3,[0,1,1,1,45,471]),
(41453057,3,[0,0,0,0,0,0,0,0,0,1430]),
(41453059,2,[0,1,153,687]),
(41453063,5,[0,3,197,347]),
(41454241,7,[0,0,0,0,0,1,2,18,208]),
(41455439,7,[0,27,62,114]),
(41624431,31,[0,1,2,12,13,137]),
(42215141,2,[0,0,2,4,63,112]),
(42235111,6,[0,1,1,2,1905]),
(42877249,11,[0,0,0,0,0,0,1,1708]),
(43304609,3,[0,0,0,0,0,2179]),
(43309909,2,[0,0,1,1,116,282]),
(44091097,11,[0,0,0,1,3,7,7,128]),
(44222719,3,[0,1,31,1332]),
(44372717,2,[0,0,2586]),
(45275099,2,[0,4,43,785]),
(45485729,3,[0,0,0,0,0,11,12,158]),
(45564901,6,[0,0,1,2,2,1606]),
(45726041,6,[0,0,0,2,9,1210]),
(46270307,2,[0,2697]),
(46482049,7,[0,0,0,0,0,0,0,1,1,36,54]),
(46558361,6,[0,0,0,2,7,1349]),
(46855309,6,[0,0,1,221,381]),
(47278871,23,[0,2,6,1767]),
(47278873,5,[0,0,0,1,1,2000]),
(47278877,2,[0,0,2603])]
def block44 : Array Row := #[
(47280209,3,[0,0,0,0,7,9,10,39]),
(47281561,7,[0,0,0,1,2,8,11,89]),
(47955547,2,[0,1,1,2324]),
(48155567,5,[0,12,1963]),
(48242023,3,[0,1,6,9,14,68]),
(49049249,3,[0,0,0,0,0,8,1375]),
(49198477,6,[0,0,1,6,1721]),
(49205669,2,[0,0,7,40,454]),
(49309373,5,[0,0,3,2236]),
(49639769,3,[0,0,0,16,53,80]),
(50605601,11,[0,0,0,0,0,2,2,6,17,17]),
(50810339,2,[0,33,43,160]),
(52048831,6,[0,1,2,48,683]),
(53241523,5,[0,1,86,979]),
(53680639,6,[0,1,4,2056]),
(53950511,19,[0,2,297,373]),
(53950513,5,[0,0,0,0,1,3,4,4,216]),
(53950517,2,[0,0,31,34,124]),
(53952029,2,[0,0,5,10,1162]),
(53953567,5,[0,1,41,1286]),
(56733953,3,[0,0,0,0,0,0,0,0,4,983]),
(57929713,5,[0,0,0,0,1,2143]),
(58565267,2,[0,2732]),
(59457091,29,[0,1,2,3,3,4,459]),
(61520777,3,[0,0,0,21,63,64]),
(61520779,2,[0,1,1,4,1803]),
(61520783,5,[0,2741]),
(61522469,13,[0,0,3,12,1306]),
(61524161,3,[0,0,0,0,0,0,2,1660]),
(61689373,5,[0,0,1,2458]),
(62678411,2,[0,2,2494]),
(62720153,3,[0,0,0,4,139,151]),
(62962267,5,[0,1,47,1262]),
(63874667,2,[0,2749]),
(64723787,2,[0,2750]),
(65356433,3,[0,0,0,0,6,8,10,67]),
(67271879,11,[0,2756]),
(67625309,2,[0,0,102,1125]),
(68563793,3,[0,0,0,0,4,1851]),
(69087113,3,[0,0,0,16,44,131]),
(69452897,3,[0,0,0,0,0,10,15,215]),
(69959441,3,[0,0,0,0,2,119,216]),
(69959443,2,[0,1,3,2229]),
(69959447,5,[0,59,59,85]),
(69961429,2,[0,0,1,1,1,101,191]),
(69963431,13,[0,2,84,909]),
(70292477,2,[0,0,7,7,1281]),
(71148167,5,[0,2762]),
(71223389,2,[0,0,77,1243]),
(71566613,2,[0,0,5,62,515]),
(72023843,2,[0,4,2352]),
(74594363,2,[0,2773]),
(74654053,6,[0,0,1,4,21,664]),
(74683603,2,[0,1,1,3,1967]),
(75092141,2,[0,0,2,2380]),
(75194681,3,[0,0,0,2,4,9,19,22]),
(75418111,15,[0,1,1,2,2071]),
(75741311,7,[0,2,50,1151]),
(76439989,2,[0,0,1,1,109,447]),
(76584317,2,[0,0,244,825]),
(77856269,2,[0,0,3,70,688]),
(77945783,5,[0,6,2294]),
(79872047,5,[0,34,83,113]),
(79872049,7,[0,0,0,0,1,1,1,7,11,55])]
def block45 : Array Row := #[
(79872053,2,[0,0,5,6,1461]),
(79874329,13,[0,0,0,1,7,28,251]),
(79876613,2,[0,0,106,1169]),
(80421311,11,[0,2,44,1218]),
(80837969,3,[0,0,0,0,2455]),
(80960479,6,[0,1,2627]),
(80994997,11,[0,0,1,1,2292]),
(82183177,5,[0,0,0,1,1,159,197]),
(82889239,3,[0,1,2629]),
(84439337,3,[0,0,0,12,1747]),
(86078431,6,[0,1,1,1,2,1809]),
(86839877,2,[0,0,6,6,13,270]),
(87142301,14,[0,0,2,2,3,1553]),
(88984523,2,[0,4,2398]),
(89054309,2,[0,0,3,28,1114]),
(90225041,3,[0,0,0,0,2,2129]),
(90550199,11,[0,2805]),
(91253231,11,[0,2,2555]),
(91253233,10,[0,0,0,0,1,1,3,1462]),
(91253237,2,[0,0,8,2102]),
(91255807,3,[0,1,1,27,1266]),
(91258393,10,[0,0,0,1,179,449]),
(93524933,2,[0,0,2698]),
(95475661,10,[0,0,1,2,3,10,671]),
(97580887,3,[0,1,5,2153]),
(97703317,2,[0,0,1,1,2325]),
(98618747,2,[0,2824]),
(104101031,11,[0,2,4,6,40,63]),
(104101033,15,[0,0,0,1,3,58,323]),
(104101037,2,[0,0,5,8,1451]),
(104103947,2,[0,13,100,321]),
(104106883,2,[0,1,4,2217]),
(104401963,3,[0,1,1,3,2069]),
(104762131,2,[0,1,2,4,98,110]),
(104901079,6,[0,1,72,1269]),
(104946893,2,[0,0,2714]),
(108242773,5,[0,0,1,4,7,1230]),
(108293233,10,[0,0,0,0,1,33,916]),
(109010711,19,[0,2,9,1842]),
(110869573,2,[0,0,1,4,2072]),
(111805021,2,[0,0,1,1,2,1983]),
(113161819,2,[0,1,3,4,1728]),
(114534683,2,[0,426,940]),
(116793569,3,[0,0,0,0,0,16,1353]),
(118073867,2,[0,7,263,278]),
(118181939,2,[0,3,7,1887]),
(118644731,6,[0,2,2604]),
(118644733,15,[0,0,1,1,14,1389]),
(118644737,5,[0,0,0,0,0,0,0,0,0,0,0,0,0,3,306]),
(118648121,3,[0,0,0,2,137,465]),
(118651513,5,[0,0,0,1,3,33,554]),
(118918109,2,[0,0,10,43,548]),
(119625049,13,[0,0,0,1,1,37,773]),
(120208229,3,[0,0,3,12,1502]),
(120765761,3,[0,0,0,0,0,0,2,1843]),
(120766873,5,[0,0,0,1,188,514]),
(121358329,37,[0,0,0,1,3,5,41,62]),
(122039129,3,[0,0,0,7,121,195]),
(122774581,7,[0,0,1,1,2,7,1187]),
(123573773,2,[0,0,3,2425]),
(127033547,2,[0,179,1343]),
(131916689,3,[0,0,0,0,2533]),
(132589901,2,[0,0,2,2,12,20,85]),
(132848363,2,[0,9,17,1197])]
def block46 : Array Row := #[
(134236517,2,[0,0,2755]),
(135551411,2,[0,2,29,33,149]),
(135551413,2,[0,0,1,1,12,1464]),
(135551417,3,[0,0,0,3,4,5,931]),
(135555247,3,[0,1,1,6,1886]),
(135559097,3,[0,0,0,2654]),
(138763171,3,[0,1,1,2,3,5,933]),
(139226491,2,[0,1,1,2,5,7,619]),
(139442591,7,[0,2,3,60,657]),
(139908677,2,[0,0,2760]),
(140192449,7,[0,0,0,0,0,0,1,4,12,254]),
(140997377,5,[0,0,0,0,0,0,0,0,5,5,424]),
(144359993,3,[0,0,0,3,2314]),
(144544249,13,[0,0,0,1,1,7,36,121]),
(144747461,2,[0,0,2,4,4,5,13,27]),
(145549909,2,[0,0,1,1,3,31,510]),
(149188727,5,[0,2867]),
(149367203,2,[0,6,2424]),
(149407229,2,[0,0,10,137,240]),
(150389363,2,[0,2871]),
(154683377,3,[0,0,0,0,2563]),
(154683379,2,[0,1,1,1,24,1120]),
(154683383,5,[0,3,2584]),
(154687723,3,[0,1,3,35,1048]),
(154692103,3,[0,1,19,39,311]),
(155945443,2,[0,1,2712]),
(156010703,5,[0,8,2358]),
(160303739,2,[0,3,2598]),
(162313027,2,[0,1,51,1530]),
(162744929,3,[0,0,0,0,0,2456]),
(162907259,2,[0,28,88,255]),
(165045709,2,[0,0,1,1,1,139,286]),
(166949351,7,[0,2,2,6,16,430]),
(166981609,13,[0,0,0,1,1,1,2043]),
(168286663,5,[0,1,1,10,42,247]),
(169418861,2,[0,0,2,5,131,150]),
(169872821,2,[0,0,2,5,1997]),
(170898353,3,[0,0,0,0,2581]),
(171845081,3,[0,0,0,2,4,15,672]),
(173122967,5,[0,67,77,117]),
(174860353,10,[0,0,0,0,0,0,1,1,8,18,44]),
(175423841,3,[0,0,0,0,0,2,2123]),
(176270249,6,[0,0,0,3,3,4,1219]),
(176359451,2,[0,2,2,12,1449]),
(176359453,2,[0,0,1,114,1035]),
(176359457,3,[0,0,0,0,0,3,5,19,146]),
(176364389,2,[0,0,2802]),
(176369327,5,[0,3,3,18,1080]),
(176890877,2,[0,0,2803]),
(178499441,6,[0,0,0,0,2,3,1808]),
(179936831,7,[0,2,359,654]),
(180746593,5,[0,0,0,0,0,1,5,1595]),
(181386593,3,[0,0,0,0,0,79,860]),
(183006713,3,[0,0,0,3,71,737]),
(184783297,5,[0,0,0,0,0,0,1,2097]),
(186076859,2,[0,4,2542]),
(189664309,6,[0,0,1,1,1,6,7,569]),
(191595317,3,[0,0,4,7,1711]),
(193198199,19,[0,24,122,231]),
(195066649,11,[0,0,0,1,1,3,3,1319]),
(199103963,2,[0,8,8,1653]),
(200987051,2,[0,2,2,4,4,33,51]),
(200987053,2,[0,0,1,3,9,1435]),
(200987057,3,[0,0,0,0,6,2031])]
def block47 : Array Row := #[
(200992679,19,[0,7,9,1648]),
(200998307,2,[0,43,1930]),
(206746157,2,[0,0,29,1893]),
(209117939,2,[0,97,1668]),
(209163887,5,[0,6,8,11,666]),
(209893787,2,[0,2915]),
(210169867,3,[0,1,2761]),
(211422521,3,[0,0,0,2,18,1419]),
(212580619,3,[0,1,479,733]),
(212694529,7,[0,0,0,0,0,0,0,0,0,1,16,336]),
(214259491,3,[0,1,1,2,8,23,191]),
(215420069,2,[0,0,11,12,31,57]),
(220709789,2,[0,0,5,91,727]),
(229056257,3,[0,0,0,0,0,0,0,0,4,5,618]),
(229056259,10,[0,1,12,2093]),
(229056263,5,[0,22,2184]),
(229061243,2,[0,22,2185]),
(229062809,6,[0,0,0,5,17,1188]),
(229069367,5,[0,2922]),
(236205829,7,[0,0,1,1,1,85,545]),
(236507189,2,[0,0,12,124,309]),
(237979517,2,[0,0,517,844]),
(238513339,2,[0,1,1,3,20,1071]),
(238559927,5,[0,4,155,813]),
(248329121,15,[0,0,0,0,0,2,5,1542]),
(250954681,7,[0,0,0,1,2,6,1550]),
(252322459,2,[0,1,623,642]),
(252371491,7,[0,1,2,3,7,7,430]),
(254371837,5,[0,0,1,2681]),
(261118373,2,[0,0,20,64,390]),
(261483581,3,[0,0,2,18,1663]),
(261483583,3,[0,1,29,29,436]),
(261483587,2,[0,3,5,7,1405]),
(261491051,2,[0,2,2,74,859]),
(261498527,5,[0,58,1908]),
(262063999,3,[0,1,1,1,1,3,7,821]),
(265184603,2,[0,10,2419]),
(274083737,3,[0,0,0,17,44,389]),
(276145823,5,[0,85,1804]),
(277618643,2,[0,3,117,1132]),
(278053297,5,[0,0,0,0,1,7,1795]),
(280700687,5,[0,3,9,2013]),
(294533539,2,[0,1,5,5,8,20,39]),
(295996697,3,[0,0,0,2771]),
(298436393,3,[0,0,0,510,711]),
(298734407,5,[0,2961]),
(298734409,17,[0,0,0,1,1,3,1967]),
(298734413,2,[0,0,2869]),
(298742957,2,[0,0,100,1580]),
(298751521,7,[0,0,0,0,0,1,2,1985]),
(301393819,2,[0,1,1,1,4,4,43,51]),
(318253157,2,[0,0,5,2489]),
(327930661,2,[0,0,1,1,1,2,82,222]),
(328011797,2,[0,0,3,2602]),
(329567317,5,[0,0,1,5,50,735]),
(333898703,5,[0,2976]),
(340816121,3,[0,0,0,2,9,49,207]),
(340816123,2,[0,1,1,20,41,226]),
(340816127,5,[0,3,76,1358]),
(340825889,3,[0,0,0,0,0,5,22,764]),
(340835657,3,[0,0,0,3,2488]),
(342170659,3,[0,1,1,7,98,289]),
(349533997,6,[0,0,1,3,2411]),
(352571743,5,[0,1,1,10,11,935])]
def block48 : Array Row := #[
(354569023,5,[0,1,1,1,9,54,151]),
(359812927,19,[0,1,1,4,21,1032]),
(366145543,5,[0,1,1,1,3,3,7,668]),
(368925287,5,[0,42,2098]),
(377538173,2,[0,0,4,2549]),
(386396399,7,[0,3002]),
(388573181,2,[0,0,2,7,7,1308]),
(388573183,6,[0,1,1,6,2157]),
(388573187,2,[0,11,136,646]),
(388584307,2,[0,1,1,4,12,35,65]),
(388595443,2,[0,1,8,217,306]),
(389822123,2,[0,124,1773]),
(391711361,3,[0,0,0,0,0,0,0,2,1975]),
(396535423,3,[0,1,13,2210]),
(398346163,2,[0,1,42,59,202]),
(403583647,3,[0,1,49,1786]),
(405412057,13,[0,0,0,1,1,3,6,1265]),
(406339267,17,[0,1,527,875]),
(409988687,5,[0,17,2356]),
(417483347,2,[0,3,2735]),
(418061983,5,[0,1,5,2469]),
(430379843,2,[0,408,1390]),
(440456839,6,[0,1,104,1566]),
(443239547,2,[0,328,1486]),
(443239549,2,[0,0,1,31,1772]),
(443239553,3,[0,0,0,0,0,0,0,3,1920]),
(443252221,2,[0,0,1,2,6,1876]),
(443264897,3,[0,0,0,0,0,0,0,14,1401]),
(450570557,2,[0,0,447,1144]),
(464820491,6,[0,2,2810]),
(468672073,5,[0,0,0,1,4,2239]),
(471286477,2,[0,0,1,1,2626]),
(475139053,2,[0,0,1,1,6,11,996]),
(488749577,3,[0,0,0,3,11,33,263]),
(494366087,5,[0,6,15,53,182]),
(498019331,2,[0,2,555,760]),
(500365783,3,[0,1,1,1,3,8,18,148]),
(500663831,13,[0,2,9,211,216]),
(506202701,10,[0,0,2,2,41,1090]),
(506202703,6,[0,1,529,951]),
(506202707,2,[0,70,2021]),
(506217163,2,[0,1,4,17,1558]),
(506231657,3,[0,0,0,3,8,9,850]),
(511601003,5,[0,4,378,710]),
(527092297,5,[0,0,0,1,2690]),
(528284321,6,[0,0,0,0,0,2,2355]),
(535197877,6,[0,0,1,6,18,1208]),
(535321867,3,[0,1,111,1596]),
(541718623,3,[0,1,1,2737]),
(544921541,2,[0,0,2,17,1890]),
(553419553,5,[0,0,0,0,0,1,3,2063]),
(556127027,2,[0,3,5,9,1503]),
(566387621,2,[0,0,2,2730]),
(571682381,2,[0,0,2,15,1940]),
(575458727,5,[0,66,2077]),
(578176997,2,[0,0,2957]),
(578176999,3,[0,1,3,12,19,532]),
(578177003,2,[0,5,9,2039]),
(578193533,2,[0,0,3,3,9,1497]),
(578210081,3,[0,0,0,0,0,2,3,109,148]),
(588280859,2,[0,4,14,16,757]),
(595494881,3,[0,0,0,0,0,2,163,470]),
(620850443,2,[0,483,1410]),
(638627651,2,[0,2,2,2621])]
def block49 : Array Row := #[
(638742509,2,[0,0,249,1494]),
(641058611,2,[0,2,6,10,26,193]),
(653656121,11,[0,0,0,2,5,6,1402]),
(659323459,2,[0,1,1,2770]),
(660089537,3,[0,0,0,0,0,0,2577]),
(660089539,2,[0,1,1,22,1885]),
(660089543,5,[0,3,422,873]),
(660108401,3,[0,0,0,0,2,2,3,3,1167]),
(660127283,2,[0,16,18,1440]),
(662038753,5,[0,0,0,0,0,1,6,20,578]),
(692539819,3,[0,1,306,1324]),
(694076311,3,[0,1,1,1,2,44,842]),
(694750051,10,[0,1,1,2,2,6,44,88]),
(698059669,2,[0,0,1,33,82,163]),
(713092979,2,[0,5,24,83,118]),
(725741129,3,[0,0,0,3,2625]),
(730173539,2,[0,17,2487]),
(739133189,2,[0,0,2998]),
(754005377,3,[0,0,0,0,0,0,0,2484]),
(754005379,2,[0,1,3,2663]),
(754005383,5,[0,5,29,1745]),
(754026947,2,[0,22,2431]),
(754048523,2,[0,21,2446]),
(772177361,3,[0,0,0,0,2,40,1309]),
(778212059,2,[0,5,30,1714]),
(779644247,5,[0,3083]),
(855244561,7,[0,0,0,0,1,2,2364]),
(860759687,5,[0,3093]),
(860759689,7,[0,0,0,1,2763]),
(860759693,2,[0,0,5,14,1828]),
(860784311,21,[0,2,2890]),
(860808941,2,[0,0,2,6,12,1352]),
(864799447,5,[0,1,3,11,75,230]),
(866172413,2,[0,0,3,3,3,64,300]),
(867673841,3,[0,0,0,0,2,4,2101]),
(871262089,7,[0,0,0,1,11,2100]),
(890819053,2,[0,0,1,16,2155]),
(904948829,2,[0,0,3,6,9,1372]),
(919765897,11,[0,0,0,1,3,52,1025]),
(923405089,7,[0,0,0,0,0,1,21,64,76]),
(927625843,2,[0,1,1,4,5,6,6,9,13]),
(940818773,2,[0,0,8,305,546]),
(964856681,3,[0,0,0,2,9,134,182]),
(982631717,2,[0,0,4,386,689]),
(982631719,3,[0,1,1,11,27,858]),
(982631723,2,[0,6,159,1134]),
(982659817,5,[0,0,0,1,1,1,2432]),
(982687919,11,[0,12,17,1664]),
(1011746363,2,[0,4,15,53,439]),
(1021007327,5,[0,467,1577]),
(1025133661,2,[0,0,1,1,2,6,12,700]),
(1026787519,3,[0,1,1,10,11,12,197]),
(1062927599,13,[0,16,2552]),
(1068651709,2,[0,0,1,2894]),
(1073786093,2,[0,0,50,54,515]),
(1075864787,2,[0,82,2152]),
(1103560981,18,[0,0,1,2,2664]),
(1122112757,2,[0,0,48,2149]),
(1122112759,3,[0,1,5,41,1420]),
(1122112763,2,[0,176,1938]),
(1122144817,5,[0,0,0,0,1,5,2245]),
(1122176893,2,[0,0,1,321,1227]),
(1132775243,2,[0,3124]),
(1146750053,2,[0,0,3,2789])]
def block50 : Array Row := #[
(1151620963,2,[0,1,152,1690]),
(1179116131,2,[0,1,2,12,43,547]),
(1214419639,6,[0,1,42,2116]),
(1234775431,12,[0,1,1,2,3,2266]),
(1247711273,3,[0,0,0,50,85,238]),
(1248133919,7,[0,227,1875]),
(1255163279,13,[0,6,10,15,1019]),
(1277485019,2,[0,3136]),
(1282021001,3,[0,0,0,2,2,2,5,6,595]),
(1282021003,2,[0,1,1,2864]),
(1282021007,5,[0,3,3,13,21,472]),
(1282057639,3,[0,1,10,23,1412]),
(1282094291,6,[0,2,8,93,800]),
(1282429913,3,[0,0,0,2971]),
(1292978303,5,[0,3,4,19,1540]),
(1318806119,7,[0,3,68,1762]),
(1322671093,2,[0,0,1,7,9,1667]),
(1323750761,3,[0,0,0,2,133,1235]),
(1325993791,13,[0,1,2,4,11,31,144]),
(1410286973,2,[0,0,3071]),
(1430157667,3,[0,1,3,539,659]),
(1464582167,5,[0,10,60,1439]),
(1464582169,11,[0,0,0,1,1,1,3,3,7,668]),
(1464582173,2,[0,0,3074]),
(1464624019,2,[0,1,1,1,1,4,5,6,462]),
(1464665879,17,[0,5,5,12,1504]),
(1480514039,7,[0,94,114,337]),
(1517411743,3,[0,1,3,4,2354]),
(1538882647,5,[0,1,3,211,1092]),
(1544354723,2,[0,3159]),
(1552063649,3,[0,0,0,0,0,189,1226]),
(1635141239,7,[0,458,1709]),
(1669816091,2,[0,2,2977]),
(1673311091,2,[0,2,4,266,726]),
(1673311093,6,[0,0,1,2952]),
(1673311097,3,[0,0,0,3012]),
(1673358901,2,[0,0,1,2,2,193,531]),
(1673406743,5,[0,3,3,186,893]),
(1715439641,3,[0,0,0,2,137,1314]),
(1755787793,3,[0,0,0,0,4,2571]),
(1817893939,7,[0,1,3,58,1615]),
(1827104891,2,[0,2,5,21,1643]),
(1879360297,5,[0,0,0,1,4,12,1635]),
(1881637547,2,[0,3177]),
(1911753521,3,[0,0,0,0,2,334,775]),
(1911753523,2,[0,1,1,1,3,3,112,192]),
(1911753527,5,[0,19,79,1155]),
(1911808141,6,[0,0,1,2,4,115,519]),
(1911862807,7,[0,1,3,6,34,952]),
(1925706667,5,[0,1,5,5,2263]),
(2013437593,5,[0,0,0,1,1,541,591]),
(2056649863,5,[0,1,22,60,876]),
(2068645519,15,[0,1,1,67,77,148]),
(2068745951,17,[0,2,2,22,1923]),
(2074769621,3,[0,0,2,3,4,9,1256]),
(2094188651,6,[0,2,2,93,1446]),
(2117272477,6,[0,0,1,4,161,929]),
(2154096779,2,[0,1023,1267]),
(2158877563,3,[0,1,3073]),
(2184149837,2,[0,0,4,2825]),
(2184149839,6,[0,1,5,2726]),
(2184149843,2,[0,3,2970]),
(2184212249,3,[0,0,0,911,934]),
(2184274679,11,[0,76,2335])]
def block51 : Array Row := #[
(2201081791,3,[0,1,2,7,2386]),
(2205441083,2,[0,5,24,34,601]),
(2267116373,2,[0,0,359,1696]),
(2341124839,3,[0,1,1,5,16,35,187]),
(2349754663,3,[0,1,7,2677]),
(2365180589,2,[0,0,10,99,1178]),
(2405875909,2,[0,0,1,685,1073]),
(2421501883,2,[0,1,3087]),
(2495422541,2,[0,0,2,5,2561]),
(2495422543,3,[0,1,27,2388]),
(2495422547,2,[0,3204]),
(2495493857,3,[0,0,0,0,0,63,1733]),
(2495565187,2,[0,1,56,2213]),
(2546818327,3,[0,1,1,5,33,1415]),
(2558360221,2,[0,0,1,2,5,2353]),
(2559087217,13,[0,0,0,0,1,1,1,3,2074]),
(2564859827,2,[0,3213]),
(2573710193,3,[0,0,0,0,20,2287]),
(2586105869,2,[0,0,582,1532]),
(2643771821,2,[0,0,2,356,1298]),
(2646789137,3,[0,0,0,0,63,1937]),
(2665597139,2,[0,817,1522]),
(2749452463,5,[0,1,1,11,2408]),
(2775521453,2,[0,0,4,187,1331]),
(2796331451,2,[0,2,2,4,19,25,126]),
(2833084607,5,[0,4,10,2410]),
(2850834317,2,[0,0,4,19,2087]),
(2850834319,6,[0,1,3104]),
(2850834323,2,[0,3,18,2340]),
(2850915773,2,[0,0,106,2145]),
(2850997229,2,[0,0,24,300,457]),
(3041779007,5,[0,3,175,1680]),
(3237955603,2,[0,1,3,629,818]),
(3251593463,5,[0,5,5,7,23,587]),
(3257134547,2,[0,7,12,55,692]),
(3257134549,2,[0,0,1,587,1271]),
(3257134553,3,[0,0,0,3,414,960]),
(3257227609,7,[0,0,0,1,6,7,32,408]),
(3257320721,3,[0,0,0,0,2,8,118,374]),
(3268061639,13,[0,66,2451]),
(3326263909,2,[0,0,1,4,12,1977]),
(3358481981,2,[0,0,2,3,30,1654]),
(3391278503,5,[0,9,26,1954]),
(3450047119,3,[0,1,3,9,158,404]),
(3451886561,3,[0,0,0,0,0,2,7,51,533]),
(3605707951,6,[0,1,2,2,5,5,1592]),
(3640620689,3,[0,0,0,0,8,64,1140]),
(3721324487,5,[0,4,9,163,607]),
(3721324489,19,[0,0,0,1,3,2691]),
(3721324493,2,[0,0,12,26,1698]),
(3721430827,2,[0,1,1,3010]),
(3721537181,2,[0,0,2,2999]),
(3843759233,3,[0,0,0,0,0,0,0,2736]),
(3897512551,3,[0,1,1,2,2,258,562]),
(3910565753,3,[0,0,0,50,158,324]),
(3942211619,2,[0,7,260,1355]),
(4117269791,13,[0,2,7,8,2094]),
(4197260311,6,[0,1,2,2953]),
(4237480409,6,[0,0,0,3,3,13,1738]),
(4251704921,3,[0,0,0,2,12,27,1046]),
(4251704923,5,[0,1,1,3027]),
(4251704927,5,[0,3,455,1443]),
(4251826417,15,[0,0,0,0,1,9,131,489]),
(4251947929,7,[0,0,0,1,6,2580])]
def block52 : Array Row := #[
(4294078687,3,[0,1,1,3031]),
(4342511681,3,[0,0,0,0,0,0,2,5,2113]),
(4582892101,2,[0,0,1,2,2,98,1115]),
(4600943629,2,[0,0,1,28,2361]),
(4748827781,2,[0,0,2,370,1455]),
(4857678557,2,[0,0,3202]),
(4857678559,3,[0,1,1,21,239,325]),
(4857678563,2,[0,4,23,153,382]),
(4857817421,2,[0,0,2,617,1208]),
(4857956291,10,[0,2,4,7,2295]),
(4985414773,6,[0,0,1,5,8,2187]),
(5000624393,3,[0,0,0,6,20,28,524]),
(5114095967,5,[0,3,44,2256]),
(5328969677,2,[0,0,25,322,604]),
(5407643653,5,[0,0,1,66,2181]),
(5465558039,7,[0,6,354,1360]),
(5548584911,11,[0,2,4,10,31,828]),
(5548584913,10,[0,0,0,0,1,5,399,402]),
(5548584917,2,[0,0,3,6,53,1255]),
(5548743457,7,[0,0,0,0,0,1,331,1058]),
(5548902031,15,[0,1,1,1,2,3,8,1564]),
(5802383183,5,[0,899,1652]),
(5812637231,19,[0,2,13,19,1655]),
(5830928897,3,[0,0,0,0,0,0,0,0,0,5,2078]),
(5905894541,2,[0,0,2,3,3,5,94,157]),
(5923169653,5,[0,0,1,23,2472]),
(6026994317,2,[0,0,3,3,3,2423]),
(6089740351,3,[0,1,2,2,7,48,748]),
(6154982333,2,[0,0,13,19,1924]),
(6255903991,3,[0,1,2,3,3,102,678]),
(6339411851,2,[0,2,2,38,62,350]),
(6339411853,2,[0,0,1,3117]),
(6339411857,3,[0,0,0,0,64,2156]),
(6339593021,3,[0,0,2,12,20,1506]),
(6339774223,3,[0,1,1,339,1603]),
(6486229051,3,[0,1,2,2,3,53,1051]),
(6578009689,7,[0,0,0,1,3045]),
(6782557007,5,[0,3306]),
(6789077699,2,[0,5,3037]),
(6804529841,3,[0,0,0,0,2,9,13,1386]),
(6854196809,3,[0,0,0,74,97,506]),
(6861746473,10,[0,0,0,1,3,2786]),
(6957822653,2,[0,0,4,10,2457]),
(7001729153,3,[0,0,0,0,0,0,0,4,322,324]),
(7051273153,5,[0,0,0,0,0,0,1,3,4,12,809]),
(7242356417,3,[0,0,0,0,0,0,2921]),
(7242356419,3,[0,1,4,27,91,315]),
(7242356423,5,[0,3,6,2738]),
(7242563359,6,[0,1,1,13,2558]),
(7242770309,2,[0,0,167,2246]),
(7271575757,2,[0,0,3240]),
(7480784807,5,[0,4,12,102,881]),
(7528111001,7,[0,0,0,2,2,2,2526]),
(7590793817,3,[0,0,0,7,42,1750]),
(7633921271,7,[0,2,7,35,1755]),
(7665966557,2,[0,0,7,13,29,993]),
(7683155663,7,[0,3,5,2797]),
(7754119829,10,[0,0,3,5,2682]),
(7789133777,3,[0,0,0,0,18,2516]),
(7900982489,3,[0,0,0,3,9,2449]),
(8133016751,19,[0,2,2,2,6,2264]),
(8274582077,2,[0,0,3252]),
(8274582079,7,[0,1,3,3,3,2396]),
(8274582083,2,[0,5,3059])]
def block53 : Array Row := #[
(8274818551,3,[0,1,2,2,261,1157]),
(8275055027,2,[0,3,3,2889]),
(8819741011,2,[0,1,2,20,2397]),
(9453541967,5,[0,4,4,4,96,654]),
(9453541969,31,[0,0,0,0,1,1,1,5,6,22,195]),
(9453541973,2,[0,0,3,3,8,32,894]),
(9453812099,2,[0,6,3048]),
(9454082243,2,[0,4,8,14,66,196]),
(9943049423,5,[0,943,1775]),
(10083338021,2,[0,0,2,3,2866]),
(10174873481,3,[0,0,0,2,3036]),
(10228942939,3,[0,1,20,126,1156]),
(10236348869,2,[0,0,3279]),
(10422587339,2,[0,24,249,1166]),
(10513948559,7,[0,48,251,870]),
(10628766523,2,[0,1,1,4,2830]),
(10741403639,13,[0,3,857,1323]),
(10800955337,3,[0,0,0,22,131,1011]),
(10800955339,2,[0,1,6,315,1285]),
(10800955343,5,[0,8,500,1320]),
(10801263997,2,[0,0,1,1,39,65,572]),
(10801572697,5,[0,0,0,1,1,1,9,2231]),
(10953827221,6,[0,0,1,2,3,9,65,387]),
(11315776081,47,[0,0,0,0,1,2,3,2506]),
(11334264499,2,[0,1,1,1,3013]),
(11492360431,12,[0,1,2,16,103,803]),
(11691869533,5,[0,0,1,3,166,1590]),
(11817343877,2,[0,0,5,16,2384]),
(12339899177,5,[0,0,0,4,151,1616]),
(12339899179,10,[0,1,3251]),
(12339899183,5,[0,5,7,42,1573]),
(12340251751,3,[0,1,2,2,2,12,1859]),
(12340604333,2,[0,0,3,3,2848]),
(12362043403,2,[0,1,1,391,1720]),
(12419833297,19,[0,0,0,0,1,5,8,56,420]),
(12565131907,2,[0,1,3255]),
(12811431119,7,[0,70,101,1152]),
(12842525753,3,[0,0,0,3,7,16,34,219]),
(12938770177,13,[0,0,0,0,0,0,0,0,1,6,7,13,197]),
(12986994991,12,[0,1,2,26,2412]),
(13186617491,2,[0,2,29,55,1241]),
(14098527977,5,[0,0,0,5,12,191,388]),
(14098527979,2,[0,1,3268]),
(14098527983,5,[0,3,4,534,972]),
(14098930819,3,[0,1,3,3,2818]),
(14099333669,2,[0,0,3,965,1078]),
(14131475117,2,[0,0,4,10,2578]),
(14441297593,5,[0,0,0,1,8,2713]),
(15157837099,3,[0,1,1,1,3049]),
(15561267511,3,[0,1,2,12,2612]),
(15722050049,3,[0,0,0,0,0,0,0,0,0,2740]),
(15801964979,2,[0,3387]),
(15934850483,2,[0,6,3102]),
(16107902687,5,[0,18,2933]),
(16107902689,11,[0,0,0,0,0,1,7,33,1362]),
(16107902693,2,[0,0,3,3,2887]),
(16108362967,3,[0,1,36,2656]),
(16108823249,3,[0,0,0,0,3,12,169,441]),
(16492409497,10,[0,0,0,1,1,3024]),
(16600550467,2,[0,1,1024,1546]),
(16630435951,3,[0,1,2,2,2919]),
(17153413177,7,[0,0,0,1,26,2512]),
(17564311397,2,[0,0,6,6,2640]),
(17704507253,2,[0,0,11,2932])]
def block54 : Array Row := #[
(17724128791,3,[0,1,2,10,2671]),
(18070325197,2,[0,0,1,3,4,10,15,813]),
(18403774511,22,[0,2,4,4,2641]),
(18403774513,5,[0,0,0,0,1,28,2361]),
(18403774517,2,[0,0,3331]),
(18404300359,3,[0,1,1,1,19,2448]),
(18404826227,2,[0,191,2531]),
(18802715933,2,[0,0,3,4,5,7,84,102]),
(18852330589,2,[0,0,1,3,5,5,2176]),
(18958645019,2,[0,7,20,2508]),
(19064882783,5,[0,4,17,2631]),
(19453722187,3,[0,1,15,104,1511]),
(19756406897,3,[0,0,0,0,3203]),
(19901293739,2,[0,23,2920]),
(20220014393,3,[0,0,0,55,79,1039]),
(20279594141,2,[0,0,2,5,7,2407]),
(20314435201,13,[0,0,0,0,0,0,0,1,2,2,7,1524]),
(20467466543,5,[0,13,15,20,32,86]),
(21026695577,3,[0,0,0,28,29,1684]),
(21026695579,2,[0,1,3,76,2159]),
(21026695583,5,[0,6,19,2551]),
(21027296341,6,[0,0,1,1,2,488,1100]),
(21027897119,11,[0,3406]),
(21823385191,3,[0,1,2,79,2240]),
(23183783941,7,[0,0,1,2,3077]),
(23351066441,3,[0,0,0,2,5,101,1428]),
(23423581229,2,[0,0,145,166,658]),
(24023303747,2,[0,5,15,2658]),
(24023303749,10,[0,0,1,1,97,2158]),
(24023303753,3,[0,0,0,3,7,2694]),
(24023990131,2,[0,1,2,3,6,8,8,835]),
(24024676523,2,[0,3,4,6,22,1520]),
(24347491523,2,[0,1072,1903]),
(24902785889,3,[0,0,0,0,0,3160]),
(25200976897,7,[0,0,0,0,0,0,0,0,0,0,1,1,2326]),
(26005713089,3,[0,0,0,0,0,0,3089]),
(26373234983,5,[0,3432]),
(27255912301,10,[0,0,1,1,2,2,7,33,804]),
(27446985887,5,[0,19,41,2118]),
(27446985889,17,[0,0,0,0,0,1,3,2786]),
(27446985893,2,[0,0,3369]),
(27447770111,11,[0,2,333,2140]),
(27448554337,5,[0,0,0,0,0,1,3,2787]),
(28101136703,5,[0,122,187,959]),
(28193786567,5,[0,4,10,2790]),
(28432762487,5,[0,36,2896]),
(28858275583,6,[0,1,8,3011]),
(29051294507,2,[0,5,43,317,370]),
(29519749289,3,[0,0,0,63,105,989]),
(30051378449,3,[0,0,0,0,3,5,6,45,612]),
(30508647809,3,[0,0,0,0,0,0,0,186,1683]),
(31358684711,7,[0,2,7,2975]),
(31358684713,5,[0,0,0,1,109,2285]),
(31358684717,2,[0,0,117,166,823]),
(31359580673,3,[0,0,0,0,0,0,0,0,0,3,6,31,478]),
(31360476647,5,[0,29,2950]),
(31401110861,2,[0,0,2,3,10,2514]),
(32204133673,7,[0,0,0,1,9,2809]),
(32408566621,10,[0,0,1,2,9,2665]),
(32704596877,2,[0,0,1,3,10,2611]),
(32927897311,6,[0,1,2,3,4,36,1463]),
(33286582673,3,[0,0,0,0,3,86,114,175]),
(34420984223,5,[0,228,2605]),
(34824746059,2,[0,1,6,57,175,196])]
def block55 : Array Row := #[
(35662507117,2,[0,0,1,82,2510]),
(35827741847,5,[0,5,9,259,1101]),
(35827741849,17,[0,0,0,1,10,2819]),
(35827741853,2,[0,0,3,518,1776]),
(35828765509,2,[0,0,1,16,2826]),
(35829789179,2,[0,19,3034]),
(36817546399,3,[0,1,24,66,1658]),
(37478849827,2,[0,1,4,311,1761]),
(37605431867,2,[0,3463]),
(38458158521,3,[0,0,0,2,869,1377]),
(39164601953,3,[0,0,0,0,0,3,19,42,840]),
(39233796311,13,[0,2,30,2742]),
(40308059657,3,[0,0,0,7,3044]),
(40741046833,10,[0,0,0,0,1,26,168,699]),
(40933763537,3,[0,0,0,0,3278]),
(40933763539,3,[0,1,468,2244]),
(40933763543,5,[0,3,22,60,1552]),
(40934933087,5,[0,3473]),
(40936102637,2,[0,0,4,5,2865]),
(41308894499,2,[0,7,23,2608]),
(41446236119,13,[0,3,8,216,1482]),
(41601177953,3,[0,0,0,0,0,136,2230]),
(42034296653,2,[0,0,23,2924]),
(43710066139,3,[0,1,13,2979]),
(44260852709,2,[0,0,13,862,960]),
(45522308483,2,[0,3,3297]),
(45545743127,5,[0,5,21,52,1466]),
(46419663527,5,[0,722,2323]),
(46701723637,5,[0,0,1,1,1,40,192,305]),
(46767478127,5,[0,21,3051]),
(46767478129,13,[0,0,0,0,1,3,166,1590]),
(46767478133,2,[0,0,3418]),
(46768814357,2,[0,0,4,3188]),
(46768977721,13,[0,0,0,1,1,1,2,2800]),
(46770150613,2,[0,0,1,3317]),
(48976969681,7,[0,0,0,0,1,1,1,2,26,1697]),
(49398713731,2,[0,1,1,1,2,6,24,1521]),
(49557283211,2,[0,2,939,1780]),
(49805571779,2,[0,3489]),
(50931503989,2,[0,0,1,36,2717]),
(51394462261,2,[0,0,1,2,1069,1161]),
(52011426179,2,[0,3491]),
(52037265661,2,[0,0,1,2,880,1340]),
(52749799637,2,[0,0,7,3147]),
(53344442531,2,[0,2,11,736,905]),
(53432588267,2,[0,118,2788]),
(53432588269,2,[0,0,1,1,1012,1380]),
(53432588273,3,[0,0,0,0,3,7,20,1825]),
(53434114913,3,[0,0,0,0,0,3232]),
(53435641579,2,[0,1,4,6,365,950]),
(54194171177,3,[0,0,0,8,3050]),
(54926753473,5,[0,0,0,0,0,0,1,1,253,1341]),
(59603359369,13,[0,0,0,1,3,41,2267]),
(61047496667,2,[0,5,10,2873]),
(61047496669,2,[0,0,1,9,2985]),
(61047496673,3,[0,0,0,0,0,6,226,1416]),
(61049240887,3,[0,1,3402]),
(61050985139,6,[0,4,5,12,109,719]),
(61327732457,3,[0,0,0,3383]),
(68078611873,5,[0,0,0,0,0,1,1,702,1106]),
(69747661097,3,[0,0,0,797,2044]),
(69747661099,2,[0,1,1,6,9,2530]),
(69747661103,7,[0,3,25,40,51,190]),
(69749653921,7,[0,0,0,0,0,1,2,9,2454])]
def block56 : Array Row := #[
(69751646773,5,[0,0,1,3350]),
(70746967861,6,[0,0,1,2,3201]),
(73939135091,2,[0,2,10,3030]),
(77671017773,2,[0,0,429,2482]),
(78844232381,2,[0,0,2,3319]),
(79687861991,17,[0,2,4,9,12,31,527]),
(79687861993,7,[0,0,0,1,1,1,3075]),
(79687861997,2,[0,0,8,3169]),
(79690138807,3,[0,1,13,627,1280]),
(79692415633,5,[0,0,0,0,1,1,3122]),
(80570165353,5,[0,0,0,1,10,2917]),
(80820181951,3,[0,1,2,2,6,12,2042]),
(83809146593,3,[0,0,0,0,0,58,2560]),
(85158576497,3,[0,0,0,0,3,28,93,865]),
(85752099551,23,[0,2,2,5,6,9,19,465]),
(85992934259,2,[0,3,3,4,226,1321]),
(86141036803,2,[0,1,23,674,1004]),
(86260976869,2,[0,0,1,4,487,1618]),
(88722287993,3,[0,0,0,5,638,1568]),
(90399964817,3,[0,0,0,0,3,901,1297]),
(91044616967,5,[0,3545]),
(91044616969,7,[0,0,0,1,1,6,10,22,1107]),
(91044616973,2,[0,0,69,669,728]),
(91047218263,6,[0,1,3,4,5,187,849]),
(91049819591,11,[0,2,40,399,938]),
(93214922753,3,[0,0,0,0,0,0,0,0,0,0,0,3,10,32,240]),
(94533720179,2,[0,846,2371]),
(95571092423,5,[0,5,6,761,1014]),
(98024208143,5,[0,3,3371]),
(99114566423,5,[0,3557]),
(101253316739,2,[0,3,97,116,1005]),
(102083927063,5,[0,5,6,481,1336]),
(104019880331,2,[0,2,6,82,2191]),
(104019880333,2,[0,0,1,12,3015]),
(104019880337,3,[0,0,0,0,7,3069]),
(104022852359,19,[0,3561]),
(104025824387,2,[0,4,283,2311]),
(107286656951,11,[0,2,2,4,3003]),
(113960354707,2,[0,1,1,1,4,14,111,641]),
(114813451999,6,[0,1,1,1,3,28,81,639]),
(115433102333,2,[0,0,3502]),
(115528288399,3,[0,1,54,200,1348]),
(118844355317,2,[0,0,18,603,1404]),
(118844355319,3,[0,1,5,33,131,882]),
(118844355323,2,[0,3,4,9,2716]),
(118847750909,2,[0,0,27,36,2238]),
(118851146501,3,[0,0,2,2,2,7,55,1268]),
(122747315269,2,[0,0,1,3403]),
(122774581001,3,[0,0,0,2,2,2,2938]),
(124254621083,2,[0,23,3149]),
(124402018513,5,[0,0,0,0,1,253,2220]),
(127169129209,13,[0,0,0,1,4,477,1549]),
(128175114983,5,[0,6,14,214,1347]),
(132496303507,3,[0,1,3,3,83,2112]),
(135586393633,10,[0,0,0,0,0,1,1,750,1289]),
(135781553981,2,[0,0,2,3366]),
(135781553983,3,[0,1,7,23,76,1174]),
(135781553987,2,[0,5,18,2877]),
(135785433473,3,[0,0,0,0,0,0,0,5,14,65,573]),
(135789312973,2,[0,0,1,3415]),
(136705740361,37,[0,0,0,1,2,3,2973]),
(141553805629,10,[0,0,1,25,2923]),
(142774414333,2,[0,0,1,4,486,1754]),
(146371552127,5,[0,125,2912])]
def block57 : Array Row := #[
(155132458847,5,[0,10,11,2853]),
(155132458849,31,[0,0,0,0,0,1,1,1,20,27,30,41]),
(155132458853,2,[0,0,3,3,6,2811]),
(155136891251,2,[0,2,2,2,2,4,2594]),
(155141323663,3,[0,1,5,5,496,1190]),
(157324335461,2,[0,0,2,82,130,1054]),
(161621788331,2,[0,2,498,2382]),
(170471002957,2,[0,0,1,330,2491]),
(171985868519,11,[0,3599]),
(172662116239,3,[0,1,1,1,7,2978]),
(177241287911,7,[0,2,3456]),
(177241287913,5,[0,0,0,1,5,362,1692]),
(177241287917,2,[0,0,3,4,3126]),
(177246351977,3,[0,0,0,15,25,85,745]),
(177251416087,5,[0,1,57,2918]),
(185686871939,2,[0,44,3103]),
(189238805881,13,[0,0,0,1,2,26,60,1311]),
(190265909203,5,[0,1,1,1,1,6,2855]),
(191142184847,5,[0,3611]),
(200447011903,3,[0,1,8,10,2812]),
(202500847727,5,[0,7,3341]),
(202500847729,13,[0,0,0,0,1,1,30,316,559]),
(202500847733,2,[0,0,8,87,149,581]),
(202506633479,13,[0,3614]),
(202512419257,13,[0,0,0,1,3,977,1350]),
(204960533663,5,[0,1273,2283]),
(221923145179,2,[0,1,1,3,798,1614]),
(226460910967,6,[0,1,7,40,2587]),
(228778593397,2,[0,0,1,3466]),
(230748951127,3,[0,1,3529]),
(231360171851,2,[0,2,2,7,10,22,1473]),
(231360171853,2,[0,0,1,33,44,2017]),
(231360171857,3,[0,0,0,0,4,4,14,28,1038]),
(231366782203,5,[0,1,48,2980]),
(231373392581,3,[0,0,2,4,14,2693]),
(248069083417,20,[0,0,0,1,3,4,2944]),
(260743899553,5,[0,0,0,0,0,1,16,310,1013]),
(263878551953,3,[0,0,0,0,3450]),
(264332606267,2,[0,695,2647]),
(264332606269,2,[0,0,1,22,114,1871]),
(264332606273,3,[0,0,0,0,0,0,3,55,2288]),
(264340158631,3,[0,1,2,28,2884]),
(264347711009,3,[0,0,0,0,0,18,66,1840]),
(273274458763,2,[0,1,3546]),
(302003796707,2,[0,6,28,149,1471]),
(302003796709,6,[0,0,1,1,1,3288]),
(302003796713,3,[0,0,0,11,14,2689]),
(302012425439,7,[0,12,30,2731]),
(302021054173,2,[0,0,1,1,14,2993]),
(323450428519,7,[0,1,1,3,35,2655]),
(325030963217,3,[0,0,0,0,3472]),
(340165420487,5,[0,14,976,1651]),
(345043907471,7,[0,2,651,2453]),
(345043907473,7,[0,0,0,0,1,4,487,1618]),
(345043907477,2,[0,0,3601]),
(345053765873,3,[0,0,0,0,11,61,91,494]),
(345063624281,3,[0,0,0,2,14,342,1409]),
(362194377137,3,[0,0,0,0,47,173,1488]),
(373071927821,2,[0,0,2,1357,1789]),
(386263537327,3,[0,1,1,1,1,1,12,50,57,62]),
(394217611217,3,[0,0,0,0,4,5,6,10,1814]),
(394217611219,2,[0,1,1,23,64,149,155]),
(394217611223,5,[0,66,3133]),
(394228874597,2,[0,0,8,9,17,2307])]
def block58 : Array Row := #[
(394240138009,31,[0,0,0,1,23,160,1662]),
(405708086507,2,[0,8,3394]),
(410627549417,3,[0,0,0,3,28,2852]),
(429774881281,13,[0,0,0,0,0,0,0,0,0,1,2,234,1199]),
(432169252763,2,[0,5,12,3088]),
(450399350237,2,[0,0,4,3404]),
(450399350239,6,[0,1,10,3271]),
(450399350243,2,[0,6,13,21,63,830]),
(450412218791,13,[0,2,941,2313]),
(450425087353,5,[0,0,0,1,1,3357]),
(462806494957,2,[0,0,1,1,5,6,44,1787]),
(462859271617,5,[0,0,0,0,0,0,1,3,3,2822]),
(483393105607,3,[0,1,28,3153]),
(490002801733,2,[0,0,1,1,1,28,2796]),
(503000564291,7,[0,2,3,7,17,19,1452]),
(511789724767,3,[0,1,1,3501]),
(514013511371,2,[0,2,13,36,206,605]),
(514587692807,5,[0,4,421,2515]),
(514587692809,13,[0,0,0,1,1,3,3185]),
(514587692813,2,[0,0,1810,1860]),
(514602395311,3,[0,1,2,3453]),
(514617097823,5,[0,53,3186]),
(515266138769,3,[0,0,0,0,3513]),
(536739814517,2,[0,0,1727,1945]),
(549602662937,3,[0,0,0,6,7,3017]),
(562022734061,2,[0,0,2,3499]),
(564897666587,2,[0,4,38,46,2026]),
(572438349229,2,[0,0,1,25,26,2435]),
(587923777157,2,[0,0,20,3250]),
(587923777159,3,[0,1,51,3090]),
(587923777163,2,[0,47,106,2289]),
(587940574981,10,[0,0,1,2,4,3172]),
(587957372809,37,[0,0,0,1,5,15,134,1257]),
(603150975893,2,[0,0,12,1108,1563]),
(649762677859,2,[0,1,3,17,218,1650]),
(664515459527,5,[0,6,157,2679]),
(667215914819,2,[0,12,14,2983]),
(671711287277,2,[0,0,19,3269]),
(671711287279,3,[0,1,9,1277,1421]),
(671711287283,2,[0,3,3,3368]),
(671730479029,6,[0,0,1,1,3,3285]),
(671749670923,2,[0,1,4,7,169,1936]),
(741479128373,2,[0,0,6,36,2856]),
(746819964827,2,[0,5,351,2599]),
(767439736601,3,[0,0,0,2,2,31,2733]),
(767439736603,2,[0,1,3,4,4,339,1364]),
(767439736607,5,[0,6,832,2243]),
(767461663471,3,[0,1,2,7,563,1739]),
(767483590351,3,[0,1,2,2,6,47,165,219]),
(770474677403,2,[0,1123,2623]),
(803960039873,3,[0,0,0,0,0,0,4,71,101,590]),
(818886955729,7,[0,0,0,0,1,9,3132]),
(876810958481,3,[0,0,0,0,2,754,2131]),
(876810958483,2,[0,1,216,435,1148]),
(876810958487,5,[0,597,2872]),
(876836010221,2,[0,0,2,146,485,831]),
(876861061961,3,[0,0,0,2,5,13,2781]),
(883645351229,2,[0,0,23,110,2405]),
(892787164751,17,[0,2,2,2,5,8,2606]),
(904026331963,3,[0,1,1,5,8,25,2228]),
(923878465997,2,[0,0,24,698,1785]),
(937980285467,2,[0,3,8,1216,1395]),
(965358394613,2,[0,0,58,3171]),
(973416513763,5,[0,1,1,3,3,4,10,11,1454])]
def block59 : Array Row := #[
(975092889653,2,[0,0,3,3519]),
(1001769036347,2,[0,5,5,9,22,88,366]),
(1001769036349,2,[0,0,1,78,163,1689]),
(1001769036353,3,[0,0,0,0,0,0,3,3,14,2507]),
(1001797658353,10,[0,0,0,0,1,1,1,16,16,17,18,37]),
(1001826280361,3,[0,0,0,2,67,395,1063]),
(1030532277539,2,[0,3734]),
(1116138353857,10,[0,0,0,0,0,0,1,1022,1746]),
(1144535599841,3,[0,0,0,0,0,2,6,23,110,687]),
(1144535599843,2,[0,1,25,1098,1373]),
(1144535599847,5,[0,17,99,2657]),
(1144568300857,5,[0,0,0,1,18,27,2504]),
(1144601001899,2,[0,33,3320]),
(1176290497717,2,[0,0,1,3612]),
(1197304789403,2,[0,8,10,10,2718]),
(1238932080289,11,[0,0,0,0,0,1,1,1,3,6,9,1867]),
(1307648261831,13,[0,2,6,6,355,1644]),
(1307648261833,5,[0,0,0,1,4,7,369,1483]),
(1307648261837,2,[0,0,3,3548]),
(1307685623219,2,[0,5,12,499,1782]),
(1307722984639,3,[0,1,3,9,24,2585]),
(1319095223113,5,[0,0,0,1,247,2759]),
(1320798124159,3,[0,1,9,3381]),
(1327365058237,2,[0,0,1,3,3443]),
(1355310541729,29,[0,0,0,0,0,1,1,4,4,5,33,1003]),
(1372671560383,3,[0,1,3676]),
(1373726659939,2,[0,1,72,165,1987]),
(1393791111677,2,[0,0,16,3352]),
(1415497613503,5,[0,1,3,3,281,2315]),
(1428279079847,5,[0,1702,2350]),
(1485505060939,2,[0,1,1,606,2628]),
(1494006856031,7,[0,2,5,3417]),
(1494006856033,5,[0,0,0,0,0,1,23,2984]),
(1494006856037,2,[0,0,542,2875]),
(1494049542031,6,[0,1,1,2,3451]),
(1494092228039,11,[0,236,3108]),
(1607920079747,2,[0,3762]),
(1706924622311,19,[0,2,1571,2169]),
(1706924622313,5,[0,0,0,1,1,1,3,5,2891]),
(1706924622317,2,[0,0,1477,2427]),
(1706973391589,2,[0,0,211,3061]),
(1707022160993,3,[0,0,0,0,0,3564]),
(1718123465263,6,[0,1,22,3307]),
(1734694335523,2,[0,1,1,6,337,2305]),
(1798984791697,5,[0,0,0,0,1,3527]),
(1864104426553,5,[0,0,0,1,3587]),
(1950185779301,10,[0,0,2,2,4,15,2753]),
(1950185779303,3,[0,1,3698]),
(1950185779307,2,[0,3776]),
(1950241498901,2,[0,0,2,2,11,3116]),
(1950297218509,6,[0,0,1,1209,2409]),
(1961689815551,7,[0,2,2,3531]),
(2217580605523,3,[0,1,1,12,16,20,72,287]),
(2228115142271,7,[0,2,9,3384]),
(2228115142273,5,[0,0,0,0,0,0,0,1,3349]),
(2228115142277,2,[0,0,1647,2341]),
(2228178802711,6,[0,1,2,3,3,107,2312]),
(2228242463269,6,[0,0,1,3663]),
(2317581223963,2,[0,1,3707]),
(2332545659149,2,[0,0,1,211,2962]),
(2407802159267,5,[0,3,3656]),
(2441467712647,6,[0,1,1,1,82,2914]),
(2545653411527,5,[0,1531,2593]),
(2545653411529,22,[0,0,0,1,16,95,2370])]
def block60 : Array Row := #[
(2545653411533,2,[0,0,3,4,15,2969]),
(2545726144483,2,[0,1,1,27,1017,1344]),
(2545798877473,10,[0,0,0,0,0,1,47,2931]),
(2599050711437,2,[0,0,3746]),
(2668182674999,7,[0,79,134,2420]),
(2740042029677,2,[0,0,3,7,608,2076]),
(2761713803293,14,[0,0,1,7,33,2892]),
(2908445395547,2,[0,83,3305]),
(2908445395549,13,[0,0,1,3,4,791,1778]),
(2908445395553,3,[0,0,0,0,0,1033,2390]),
(2908528493993,3,[0,0,0,4,11,480,1710]),
(2908611592463,5,[0,10,1622,1781]),
(2945816805803,2,[0,5,20,3230]),
(3088466486429,2,[0,0,37,39,2719]),
(3130204201483,2,[0,1,442,2963]),
(3191562018167,5,[0,52,245,2415]),
(3192139106027,2,[0,5,3632]),
(3262563864083,2,[0,18,3488]),
(3322940440241,3,[0,0,0,0,2,6,191,2281]),
(3322940440243,3,[0,1,7,187,2711]),
(3322940440247,5,[0,3,40,3218]),
(3323035381417,5,[0,0,0,1,8,111,2570]),
(3323130322657,5,[0,0,0,0,0,1,8,38,55,1170]),
(3367422500929,19,[0,0,0,0,0,0,1,10,11,2642]),
(3435230130469,10,[0,0,1,208,490,1307]),
(3478311401443,2,[0,1,6,23,676,1293]),
(3577107049381,2,[0,0,1,1,2,10,3137]),
(3590568587101,19,[0,0,1,2,2,4,8,9,2221]),
(3767137307023,3,[0,1,32,3330]),
(3796507020197,2,[0,0,4,4,4,3150]),
(3796507020199,3,[0,1,1437,2527]),
(3796507020203,2,[0,5,7,19,2916]),
(3796615491841,11,[0,0,0,0,0,0,0,0,1,1,2,3062]),
(3796723963499,2,[0,174,3241]),
(3965763366827,2,[0,11,101,209,1403]),
(4199589097463,5,[0,4,358,2868]),
(4337563565477,2,[0,0,105,3242]),
(4337563565479,6,[0,1,4,5,10,26,2218]),
(4337563565483,2,[0,3,3,3544]),
(4337687495863,3,[0,1,1,3,57,2940]),
(4337811426253,6,[0,0,1,346,2960]),
(4395737962489,7,[0,0,0,1,400,2845]),
(4413466922429,2,[0,0,34,614,2142]),
(4740769561301,2,[0,0,2,2,70,81,1811]),
(4955728321151,11,[0,2,2,3613]),
(4955728321153,5,[0,0,0,0,0,0,0,1,1,1,3,6,9,1867]),
(4955728321157,2,[0,0,3791]),
(4955869913399,11,[0,34,3452]),
(4956011505647,5,[0,12,1145,2262]),
(5020248760837,5,[0,0,1,1805,2173]),
(5082844216603,2,[0,1,1726,2360]),
(5452768303573,2,[0,0,1,8,3468]),
(5499898861949,2,[0,0,8,693,2524]),
(5661990454007,5,[0,47,1448,1602]),
(5661990454009,33,[0,0,0,1,3,3,281,2315]),
(5661990454013,2,[0,0,3804]),
(5662152225161,6,[0,0,0,2,3645]),
(5662313996323,2,[0,1,1617,2485]),
(5975811096967,3,[0,1,1,81,98,2208]),
(6175756488043,2,[0,1,1,8,8,25,2495]),
(6212724619811,2,[0,2,1925,2148]),
(6239557567057,10,[0,0,0,0,1,4,3419]),
(6405913566727,3,[0,1,8,3547]),
(6468904962671,7,[0,2,42,146,2391])]
def block61 : Array Row := #[
(6468904962673,5,[0,0,0,0,1,9,489,2130]),
(6468904962677,3,[0,0,5,3634]),
(6469089788573,2,[0,0,11,3543]),
(6469274614483,2,[0,1,1,128,3106]),
(6962136199153,15,[0,0,0,0,1,7,3382]),
(7058367726301,6,[0,0,1,1,1,1,2,2,4,55,1792]),
(7382261852353,5,[0,0,0,0,0,0,1,1,8,77,2190]),
(7390816561757,2,[0,0,10,3572]),
(7390816561759,3,[0,1,3,52,3152]),
(7390816561763,2,[0,16,17,3187]),
(7391027727977,3,[0,0,0,3772]),
(7391238894203,2,[0,29,3515]),
(7734735873889,7,[0,0,0,0,0,1,3594]),
(8383603110469,6,[0,0,1,7,26,195,1790]),
(8444113662497,3,[0,0,0,0,0,3685]),
(8444113662499,2,[0,1,72,216,2337]),
(8444113662503,5,[0,3,3745]),
(8444354922889,13,[0,0,0,1,12,23,416,1130]),
(8444596183297,10,[0,0,0,0,0,0,0,0,1,3,5,659,936]),
(8948701979779,7,[0,1,4,3638]),
(9047931047339,2,[0,8,9,3365]),
(9647520478481,6,[0,0,0,0,2,13,491,2010]),
(9647520478483,3,[0,1,3812]),
(9647520478487,5,[0,4,937,2709]),
(9647796121937,3,[0,0,0,0,3,3600]),
(9648071765401,7,[0,0,0,1,2,2,324,2513]),
(9953097681301,2,[0,0,1,2,2,920,2269]),
(10729522251029,2,[0,0,3,8,117,2710]),
(11022430035311,13,[0,2,41,3355]),
(11022430035313,5,[0,0,0,0,1,1,1,1,1,27,33,1656]),
(11022430035317,3,[0,0,3,8,11,48,69,598]),
(11022744961909,2,[0,0,1,1,1,15,3249]),
(11023059888539,2,[0,13,3636]),
(11546949800219,2,[0,3,1264,2659]),
(12257932046861,10,[0,0,2,89,3217]),
(12359387332067,2,[0,826,3109]),
(12593283874901,3,[0,0,2,2,9,3329]),
(12593283874903,5,[0,1,1,6,11,553,1695]),
(12593283874907,2,[0,3,1456,2574]),
(12593643683039,11,[0,4,3739]),
(12594003491189,2,[0,0,3,3,121,2903]),
(12839831602921,61,[0,0,0,1,1,2,3,7,15,108,710]),
(13649867675473,10,[0,0,0,0,1,3,10,35,101,901]),
(14388006838187,2,[0,9,3683]),
(14388006838189,10,[0,0,1,24,32,2895]),
(14388006838193,3,[0,0,0,0,5,8,101,300,367]),
(14388417924131,2,[0,2,61,574,2080]),
(14388829010077,5,[0,0,1,7,329,2720]),
(14486341897273,10,[0,0,0,1,3,1427,2121]),
(15409493548061,2,[0,0,2,3761]),
(16139082608423,5,[0,2047,2575]),
(16438503511427,2,[0,18,29,98,2280]),
(16438503511429,7,[0,0,1,117,3256]),
(16438503511433,3,[0,0,0,228,406,1899]),
(16438973182979,2,[0,412,3283]),
(16439442854533,2,[0,0,1,13,13,47,77,708]),
(17320424700329,3,[0,0,0,6,56,990,1029]),
(18781225208897,3,[0,0,0,0,0,0,1228,2511]),
(18781225208899,2,[0,1,3854]),
(18781225208903,5,[0,5,22,87,295,755]),
(18781761815381,2,[0,0,2,246,995,1099]),
(18782298421871,31,[0,2,176,580,1812]),
(18934992742199,7,[0,5,1724,2339]),
(20062929315997,5,[0,0,1,1,1,3,73,2863])]
def block62 : Array Row := #[
(20213226115057,15,[0,0,0,0,1,1,5,1201,1780]),
(20905974433627,2,[0,1,6,3673]),
(21457818340961,3,[0,0,0,0,0,2,8,3351]),
(21457818340963,7,[0,1,9,133,2974]),
(21457818340967,5,[0,3,81,3310]),
(21458431421509,2,[0,0,1,8,91,2972]),
(21459044502059,2,[0,3931]),
(22000635228787,3,[0,1,6,10,3370]),
(24515864093717,2,[0,0,44,1533,1758]),
(24515864093719,3,[0,1,1,1,1154,2630]),
(24515864093723,2,[0,3938]),
(24516564547003,2,[0,1,4,6,37,224,1470]),
(24517265000311,3,[0,1,1,2,66,645,1544]),
(25009701881221,10,[0,0,1,1,1,1,2,3,3265]),
(25150028214551,7,[0,2,2,3726]),
(25197534584779,2,[0,1,3875]),
(25448392165723,2,[0,1,1231,2905]),
(26385864138527,5,[0,282,3372]),
(28009725062087,5,[0,820,3200]),
(28009725062089,29,[0,0,0,1,3,4,232,2576]),
(28009725062093,2,[0,0,9,10,3386]),
(28010525339977,5,[0,0,0,1,450,3060]),
(28011325617881,3,[0,0,0,2,4,13,3226]),
(28470849983101,6,[0,0,1,1,1,1,1,1,1,1,2,2,3,2492]),
(29997592555487,5,[0,25,43,135,2103]),
(30685633208651,2,[0,2,2,3,14,481,1901]),
(30736269588407,5,[0,8,8,3503]),
(31879189727713,31,[0,0,0,0,0,1,1,1,1,1,23,223,1150]),
(32001511165451,2,[0,2,2,121,245,1973]),
(32001511165453,2,[0,0,1,1,1,12,12,2986]),
(32001511165457,3,[0,0,0,0,3,8,183,2597]),
(32002425494341,2,[0,0,1,2,3,925,2434]),
(32003339823271,3,[0,1,1,2,16,3354]),
(33319187306989,2,[0,0,1,4,1793,2070]),
(35588552994983,5,[0,5,7,601,2610]),
(36562183664141,2,[0,0,2,109,3295]),
(36562183664143,6,[0,1,6,42,971,1487]),
(36562183664147,2,[0,3,3,11,3401]),
(36563228297971,3,[0,1,2,4,111,2995]),
(36564272931803,2,[0,3,4,12,349,2302]),
(38419950863341,2,[0,0,1,1,2,13,1128,1621]),
(38870826682819,2,[0,1,5,22,270,2359]),
(41243536570091,2,[0,2,9,11,3316]),
(41461028622917,2,[0,0,3,3,44,3190]),
(41772817194917,2,[0,0,12,277,463,1195]),
(41772817194919,15,[0,1,3908]),
(41772817194923,2,[0,4,138,861,1633]),
(41774010703991,11,[0,2,1922,2540]),
(41775204213073,5,[0,0,0,0,1,1,4,3492]),
(42644559737179,3,[0,1,1,1,1,3,3528]),
(45187051247837,2,[0,0,6,3747]),
(46468948101559,3,[0,1,27,231,2823]),
(47726040449537,3,[0,0,0,0,0,0,0,0,0,3609]),
(47726040449539,11,[0,1,1,4,1351,2389]),
(47726040449543,5,[0,3,5,12,21,2885]),
(47727404050699,2,[0,1,1,13,94,2939]),
(47728767651871,3,[0,1,2,7,310,419,829]),
(49945464418151,7,[0,2,2,3,228,2906]),
(52526895986153,3,[0,0,0,3,3773]),
(54527683035731,2,[0,2,3891]),
(54527683035733,2,[0,0,1,87,3400]),
(54527683035737,3,[0,0,0,6,11,42,2836]),
(54529240969543,3,[0,1,12,52,3174]),
(54530798903411,6,[0,2,214,767,1868])]
def block63 : Array Row := #[
(55166933016451,2,[0,1,1,1,2,2,6,9,2888]),
(55923132796591,6,[0,1,2,3821]),
(56578086714713,3,[0,0,0,11,3666]),
(59272322608907,2,[0,4,14,15,22,50,1330]),
(61769329728581,2,[0,0,2,3853]),
(62298656880827,2,[0,15,895,2777]),
(62298656880829,2,[0,0,1,35,717,2392]),
(62298656880833,3,[0,0,0,0,0,0,3775]),
(62300436842557,2,[0,0,1,1,4,3653]),
(62302216804291,2,[0,1,1,1,2,3677]),
(71177105989961,3,[0,0,0,2,1802,2475]),
(71177105989963,2,[0,1,1,3,3738]),
(71177105989967,5,[0,4002]),
(71179139621591,7,[0,2,3,4,5,66,2683]),
(71181173253233,3,[0,0,0,0,3,3,524,2672]),
(71749777994099,2,[0,19,127,143,2075]),
(72623463296773,2,[0,0,1,10,56,3151]),
(72973838316529,7,[0,0,0,0,1,1,1,1816,1928]),
(75864728443477,11,[0,0,1,3,2050,2128]),
(77561190855613,2,[0,0,1,1,1,12,87,2778]),
(78301532737993,5,[0,0,0,1,3857]),
(81320860559327,5,[0,9,11,35,3033]),
(81320860559329,7,[0,0,0,0,0,1,5,8,3289]),
(81320860559333,2,[0,0,1590,2958]),
(81323184012487,3,[0,1,5,18,3441]),
(81325507465649,3,[0,0,0,0,3890]),
(84316579382729,3,[0,0,0,3,4,4,87,324,820]),
(84385738647349,2,[0,0,1,82,1559,1569]),
(84550809237899,2,[0,6,963,2943]),
(86160178009091,2,[0,2,752,3173]),
(92910244919561,3,[0,0,0,2,6,819,2595]),
(92910244919563,2,[0,1,1,1,3,3,37,3019]),
(92910244919567,5,[0,83,3621]),
(92912899498057,10,[0,0,0,1,1,1,4,1441,1902]),
(92915554076591,7,[0,2,3,3799]),
(93301826365961,3,[0,0,0,2,3835]),
(99506468695001,3,[0,0,0,2,2,2,2,3469]),
(106151282449937,3,[0,0,0,0,11,1042,2525]),
(106151282449939,2,[0,1,1,4,49,3267]),
(106151282449943,5,[0,9,1093,2850]),
(106154315343733,5,[0,0,1,54,3518]),
(106157348237573,2,[0,0,1282,3120]),
(114154458737927,5,[0,33,3714]),
(121279356690341,2,[0,0,2,742,3138]),
(121279356690343,3,[0,1,3968]),
(121279356690347,2,[0,7,3855]),
(121282821814829,2,[0,0,557,3353]),
(121286286939331,10,[0,1,1,2,2122,2150]),
(123538659457163,2,[0,4036]),
(125834085364681,17,[0,0,0,1,1,2,3,4,662,1988]),
(134873530612913,3,[0,0,0,0,3,5,12,13,82,1547]),
(138563397602627,2,[0,9,146,154,2344]),
(138563397602629,2,[0,0,1,3937]),
(138563397602633,3,[0,0,0,3960]),
(138567356556931,7,[0,1,1,2,3,17,3309]),
(138571315511269,14,[0,0,1,6,7,7,3243]),
(143409144754151,11,[0,2,2,4,3684]),
(144321848570161,13,[0,0,0,0,1,1,2,3667]),
(149026247377807,3,[0,1,1196,3145]),
(153152727746203,2,[0,1,1,36,3570]),
(157192359677459,2,[0,3,10,3705]),
(158310661669331,2,[0,2,22,1242,2416]),
(158310661669333,2,[0,0,1,84,3505]),
(158310661669337,3,[0,0,0,4,3820])]
def block64 : Array Row := #[
(158315184831163,2,[0,1,3985]),
(158319707993039,13,[0,9,18,3533]),
(173836102767277,2,[0,0,1,3952]),
(176065725643649,3,[0,0,0,0,0,0,0,11,11,103,2237]),
(180872192875037,2,[0,0,5,3865]),
(180872192875039,3,[0,1,3,1305,2883]),
(180872192875043,5,[0,21,25,3416]),
(180877360651987,2,[0,1,209,3481]),
(180882528428981,10,[0,0,2,3,3,200,387,1304]),
(181193129659007,5,[0,541,765,2260]),
(206649064296791,7,[0,2,170,3471]),
(206649064296793,5,[0,0,0,1,1,5,6,3431]),
(206649064296797,2,[0,0,4,17,22,3176]),
(206654968555831,3,[0,1,1,1,2,15,3439]),
(206660872814881,31,[0,0,0,0,0,1,2,4,520,2550]),
(209095172995441,7,[0,0,0,0,1,2,131,644,1634]),
(216937054475563,3,[0,1,327,3444]),
(223283762839073,5,[0,0,0,0,0,5,3735]),
(224639506300987,2,[0,1,1,3,15,36,3018]),
(225350383422839,11,[0,15,1763,2528]),
(236099508385877,2,[0,0,13,3801]),
(236099508385879,3,[0,1,1,1,10,29,3205]),
(236099508385883,2,[0,15,2146,2248]),
(236106254086133,2,[0,0,10,11,12,3206]),
(236112999786401,3,[0,0,0,0,0,2,2,4,1570,1679]),
(254101238146837,2,[0,0,1,1,3909]),
(256603606357339,3,[0,1,1,1,1,1,20,37,2804]),
(269747061225821,2,[0,0,2,15,90,3121]),
(269747061225823,5,[0,1,1,98,258,299,715]),
(269747061225827,2,[0,4082]),
(269754768284713,5,[0,0,0,1,1883,2708]),
(269762475343619,2,[0,358,3563]),
(290314294625317,26,[0,0,1,5,6,12,352,2115]),
(291579984230713,5,[0,0,0,1,170,235,2532]),
(308189870961221,2,[0,0,2,3953]),
(308189870961223,5,[0,1,35,3699]),
(308189870961227,2,[0,92,631,2821]),
(308198676386177,3,[0,0,0,0,0,0,0,3836]),
(308207481811183,3,[0,1,1,6,13,3482]),
(331688228983337,3,[0,0,0,4011]),
(333487268643671,14,[0,2,6,3827]),
(352111330639697,3,[0,0,0,0,13,3727]),
(352111330639699,2,[0,1,3,3917]),
(352111330639703,5,[0,721,3470]),
(352121390963471,41,[0,2,13,3763]),
(352131451287299,2,[0,4099]),
(359071741377079,3,[0,1,2376,2648]),
(369971707373407,10,[0,1,1,16,22,3321]),
(399830247683869,2,[0,0,1,4001]),
(402292225618181,2,[0,0,2,1625,2937]),
(402292225618183,3,[0,1,1,14,1748,2249]),
(402292225618187,2,[0,1784,3146]),
(402303719681827,2,[0,1,7,9,1756,1892]),
(402315213745477,2,[0,0,1,1,456,802,1759]),
(422675970921283,2,[0,1,5,173,230,2374]),
(433780313735849,3,[0,0,0,2241,2739]),
(459624615075467,2,[0,27,124,138,149,519]),
(459624615075469,2,[0,0,1,1,1,2154,2357]),
(459624615075473,3,[0,0,0,0,3,4,3706]),
(459637747207333,2,[0,0,1,9,3798]),
(459650879339207,5,[0,2470,2798]),
(459679342613149,6,[0,0,1,1,1,1,3,18,1102,1505]),
(465310377904453,2,[0,0,1,7,224,3220]),
(502671777448769,3,[0,0,0,0,0,0,12,425,2838])]
def block65 : Array Row := #[
(525127688805227,2,[0,5,1970,2754]),
(525127688805229,2,[0,0,1,731,1041,1674]),
(525127688805233,3,[0,0,0,0,24,1399,2443]),
(525142692453551,14,[0,2,2,19,25,810,1554]),
(525157696101877,6,[0,0,1,7,7,10,3318]),
(529975191549541,6,[0,0,1,2,4,4,6,3328]),
(599965886633147,2,[0,4,47,62,3086]),
(599965886633149,14,[0,0,1,1,3,8,36,3139]),
(599965886633153,3,[0,0,0,0,0,0,5,1239,2646]),
(599983028515669,2,[0,0,1,3,8,30,102,2422]),
(600000170398207,5,[0,1,9,13,789,2517]),
(646707883969157,2,[0,0,2505,2700]),
(685469596641497,3,[0,0,0,154,1221,2293]),
(685469596641499,2,[0,1,1,1,1,29,1567,1783]),
(685469596641503,5,[0,7,1371,3046]),
(685489181487137,3,[0,0,0,0,0,5,1338,2729]),
(685508766332791,6,[0,1,2,18,65,3191]),
(703031919630487,3,[0,1,40,1507,2490]),
(716249189604821,2,[0,0,2,2363,2573]),
(718109218846141,10,[0,0,1,2,4,1043,2807]),
(783158806690571,2,[0,2,8,123,3338]),
(783158806690573,2,[0,0,1,5,3889]),
(783158806690577,3,[0,0,0,0,13,1912,2296]),
(783181182656503,3,[0,1,1,3,8,1037,2600]),
(783203558622437,2,[0,0,3,48,271,2862]),
(861216793432999,3,[0,1,2554,2643]),
(894770124745457,3,[0,0,0,0,4033]),
(894770124745459,10,[0,1,5,9,21,1299,1480]),
(894770124745463,7,[0,3,328,1370,1873]),
(894795689606177,3,[0,0,0,0,0,1666,2954]),
(894821254466911,3,[0,1,2,707,832,1779]),
(940687923972647,5,[0,27,3881]),
(1022287650015701,2,[0,0,2,2,16,18,3282]),
(1022287650015703,3,[0,1,3,13,20,3385]),
(1022287650015707,2,[0,566,3610]),
(1022316858234299,2,[0,4,4019]),
(1022346066452993,3,[0,0,0,0,0,0,0,0,0,23,58,2886]),
(1131561734294261,2,[0,0,2,4034]),
(1167978244359461,2,[0,0,2,6,3864]),
(1167978244359463,3,[0,1,25,61,3364]),
(1167978244359467,2,[0,7,3994]),
(1168011615166457,3,[0,0,0,1077,3343]),
(1168044985973461,6,[0,0,1,2,3,7,3647]),
(1214446039795057,5,[0,0,0,0,1,14,154,232,1858]),
(1222278458217829,7,[0,0,1,4,122,159,2633]),
(1298896637131451,2,[0,2,2,3,1356,2839]),
(1332537189653333,3,[0,0,5,9,3769]),
(1334431829638001,3,[0,0,0,0,2,2,2,3748]),
(1334431829638003,2,[0,1,6,6,201,407,1669]),
(1334431829638007,5,[0,4,7,142,1185,1512]),
(1334469956261747,2,[0,16,22,1287,2327]),
(1334508082885561,35,[0,0,0,1,2,4,24,3405]),
(1524607428881021,2,[0,0,2,4,29,3578]),
(1524607428881023,6,[0,1,4121]),
(1524607428881027,5,[0,3,6,3902]),
(1524650989093307,2,[0,285,3713]),
(1524694549305617,3,[0,0,0,0,5,325,3303]),
(1741885767751901,2,[0,0,2,2,8,8,3516]),
(1741885767751903,3,[0,1,4128]),
(1741885767751907,2,[0,3,3,3,72,1217,1631]),
(1741935535916731,2,[0,1,2,3,4,17,3425]),
(1741985304081571,2,[0,1,1,2,90,3540]),
(1767517709094911,7,[0,2,33,1087,2808]),
(1835312946507343,6,[0,1,1,1,1,1198,3058])]
def block66 : Array Row := #[
(1900295077232309,2,[0,0,11,3945]),
(1990129373900021,2,[0,0,2,4068]),
(1990129373900023,3,[0,1,4135]),
(1990129373900027,2,[0,59,199,1215,1394]),
(1990186234739291,2,[0,2,3,606,3332]),
(1990243095578719,3,[0,1,39,871,2942]),
(2231481958923379,10,[0,1,3,19,119,681,1604]),
(2254992893575267,2,[0,1,5,16,3725]),
(2273751240132917,2,[0,0,10,26,75,3101]),
(2273751240132919,3,[0,1,3,5,50,88,2780]),
(2273751240132923,5,[0,4,4,1740,2774]),
(2273816204454121,7,[0,0,0,1,2,18,31,3258]),
(2273881168775329,29,[0,0,0,0,0,1,3,3,3724]),
(2344013515739743,3,[0,1,3,4,807,3094]),
(2370330212801833,15,[0,0,0,1,1,128,1418,1956]),
(2597793274262897,3,[0,0,0,0,6,23,856,2529]),
(2597793274262899,2,[0,1,1,4089]),
(2597793274262903,5,[0,4205]),
(2597867496927881,3,[0,0,0,2,80,486,2775]),
(2597941719592949,2,[0,0,32,3883]),
(2926067152123673,3,[0,0,0,526,3588]),
(2968015927186097,3,[0,0,0,0,251,3624]),
(2968015927186099,2,[0,1,1,7,552,3238]),
(2968015927186103,5,[0,5,4074]),
(2968100727641173,2,[0,0,1,1,7,18,37,653,1334]),
(2968185528096281,3,[0,0,0,2,275,511,2559]),
(2992086391115033,3,[0,0,0,6,3975]),
(3109657104172259,2,[0,36,252,3356]),
(3218053891512413,2,[0,0,1722,3304]),
(3273188969772349,6,[0,0,1,4,11,13,165,2645]),
(3391000597081841,3,[0,0,0,0,2,162,1433,1939]),
(3391000597081843,3,[0,1,294,1911,1964]),
(3391000597081847,5,[0,3,1982,3084]),
(3391097482813189,2,[0,0,1,21,3866]),
(3391194368544557,2,[0,0,3,3,7,9,3512]),
(3798212110240217,3,[0,0,0,2268,3029]),
(3874266625017011,6,[0,2,123,1474,2486]),
(3874266625017013,2,[0,0,1,3,14,145,214,2079]),
(3874266625017017,3,[0,0,0,259,1431,2372]),
(3874377318349157,2,[0,0,19,2306,2473]),
(3874488011681347,2,[0,1,1,1,4047]),
(3929215546213981,2,[0,0,1,2,4,11,383,623,738]),
(4251302770076519,11,[0,5,293,3596]),
(4426404965760977,3,[0,0,0,0,4,3982]),
(4426404965760979,2,[0,1,1,1,1,264,408,2466]),
(4426404965760983,5,[0,9,67,3675]),
(4426531434474319,3,[0,1,1,1,1,5,217,3229]),
(4426657903187669,2,[0,0,8,15,55,3308]),
(4470787421334211,2,[0,1,2,4090]),
(4713649893618293,2,[0,0,4,87,1291,2444]),
(5057230907903891,2,[0,2,6,102,535,2583]),
(5057230907903893,2,[0,0,1,13,57,105,2846]),
(5057230907903897,3,[0,0,0,17,22,498,2734]),
(5057375400215557,5,[0,0,1,4,7,33,1519,1574]),
(5057519892527239,7,[0,1,278,801,2784]),
(5131648327381259,2,[0,316,3790]),
(5777958558476831,11,[0,2,4,4026]),
(5777958558476833,5,[0,0,0,0,0,1,3,3,5,48,546,1444]),
(5777958558476837,2,[0,0,19,248,808,2126]),
(5778123643007137,10,[0,0,0,0,0,1,1,3967]),
(5778288727537471,3,[0,1,2,2114,2997]),
(6601400195615801,3,[0,0,0,2,2,269,3465]),
(6601400195615803,2,[0,1,1,1,482,3506]),
(6601400195615807,5,[0,3,28,29,65,2934])]
def block67 : Array Row := #[
(6601588807049981,2,[0,0,2,30,3843]),
(6601777418484169,14,[0,0,0,1,1001,3429]),
(7387753888032839,19,[0,220,1649,2639]),
(7542194029300031,19,[0,2,29,1066,3043]),
(7542194029300033,5,[0,0,0,0,0,0,1,8,487,3091]),
(7542194029300037,2,[0,0,51,2259,2414]),
(7542409520558053,2,[0,0,1,1,3,3,432,3207]),
(7542625011816077,3,[0,0,3,3,5,1741,2601]),
(7609572831410911,6,[0,1,1,2,4060]),
(8133827889238577,3,[0,0,0,0,3,4048]),
(8617064424312977,3,[0,0,0,0,2212,3070]),
(8617064424312979,3,[0,1,1,1,13,39,882,2195]),
(8617064424312983,5,[0,4,6,6,3800]),
(8617310626153693,5,[0,0,1,4179]),
(8617556827994419,3,[0,1,1,7,3983]),
(8621380421229439,3,[0,1,1,393,692,2678]),
(8910857503065787,5,[0,1,2020,3254]),
(9845119205800031,17,[0,2,27,122,191,294,603]),
(9845119205800033,5,[0,0,0,0,0,1,3,3,4,3665]),
(9845119205800037,2,[0,0,6,18,19,108,2827]),
(9845400494920213,6,[0,0,1,1,2194,3001]),
(9845681784040433,3,[0,0,0,0,4,1495,3123]),
(10373899433359481,3,[0,0,0,2,7,3946]),
(11248189337249567,5,[0,5,6,3984]),
(11248189337249569,17,[0,0,0,0,0,1,1,4,4,9,17,312,1450]),
(11248189337249573,2,[0,0,54,364,1117,1589]),
(11248510714087793,3,[0,0,0,0,4177]),
(11248832090926097,3,[0,0,0,0,19,24,3615]),
(12106168745994313,15,[0,0,0,1,4,56,3655]),
(12851217006309497,3,[0,0,0,72,428,3215]),
(12851217006309499,2,[0,1,7,25,3783]),
(12851217006309503,5,[0,1097,1290,2429]),
(12851584183938343,3,[0,1,2045,3286]),
(12851951361567193,5,[0,0,0,1,1,3,1021,3198]),
(13029220082341117,2,[0,0,1,1,6,32,1536,2174]),
(13895543865159449,3,[0,0,0,11,47,1670,2111]),
(13911126370701673,5,[0,0,0,1,3,13,60,3367]),
(14682699018952397,2,[0,0,23,4010]),
(14682699018952399,3,[0,1,1,3,7,15,111,304,1465]),
(14682699018952403,2,[0,488,2133,2216]),
(14683118524638727,3,[0,1,9,4059]),
(14683538030325113,3,[0,0,0,5,11,27,3520]),
(16775193382363217,3,[0,0,0,0,8,1000,1143,1379]),
(16775193382363219,11,[0,1,4,7,7,78,3239]),
(16775193382363223,5,[0,20,314,1345,2086]),
(16775672673602743,3,[0,1,806,1853,1978]),
(16776151964842313,3,[0,0,0,3,3,6,7,3637]),
(18655520655146663,5,[0,3,4206]),
(18967641075890821,7,[0,0,1,1,2,6,34,3541]),
(19165898085077957,2,[0,0,6,13,1310,2936]),
(19165898085077959,3,[0,1,38,2207,2615]),
(19165898085077963,2,[0,7,23,634,3168]),
(19166445682166131,3,[0,1,2,6,6,50,226,2503]),
(19166993279254351,11,[0,1,1,2,2,68,3631]),
(19962080275964947,2,[0,1,3,75,229,3162]),
(20194796315539889,3,[0,0,0,0,3,1086,3363]),
(21897312360872801,3,[0,0,0,0,0,2,2,6,15,17,3107]),
(21897312360872803,2,[0,1,3,3,58,621,2799]),
(21897312360872807,11,[0,4,5,1889,2982]),
(21897937998368879,17,[0,9,427,3622]),
(21898563635864969,3,[0,0,0,5,6,52,3560]),
(22200613514167657,5,[0,0,0,1,9,22,113,3134]),
(25017992191276157,2,[0,0,1760,3480]),
(25017992191276159,11,[0,1,33,3992])]
def block68 : Array Row := #[
(25017992191276163,2,[0,5,7,2211,2751]),
(25018706991053059,2,[0,1,10,1824,3085]),
(25019421790829969,3,[0,0,0,0,82,644,3118]),
(25667408044551737,3,[0,0,0,7,251,464,2728]),
(26360199393975287,5,[0,3,1640,3408]),
(28583413478446481,3,[0,0,0,0,2,1585,3280]),
(28583413478446483,2,[0,1,1,1,1657,3287]),
(28583413478446487,5,[0,4,1387,3464]),
(28584230147403059,2,[0,14,25,1572,2696]),
(28585046816359643,2,[0,3,151,3834]),
(28814280866799653,2,[0,0,3,2695,2806]),
(32656958233839851,2,[0,2,2,6,4008]),
(32656958233839853,5,[0,0,1,4,26,1774,2543]),
(32656958233839857,3,[0,0,0,0,3,4129]),
(32657891289789421,6,[0,0,1,1,1,1,2,47,3603]),
(32658824345738993,3,[0,0,0,0,11,4032]),
(33485014104081511,3,[0,1,2,50,312,3266]),
(37311041310293321,3,[0,0,0,2,58,3863]),
(37311041310293323,5,[0,1,1,4,5,1279,3052]),
(37311041310293327,5,[0,4335]),
(37312107340045067,2,[0,14,2582,2772]),
(37313173369796837,2,[0,0,13,4112]),
(39497132642632363,2,[0,1,1,507,887,2757]),
(42628397711996711,17,[0,2,8,310,3602]),
(42628397711996713,10,[0,0,0,1,3,4,56,3598]),
(42628397711996717,2,[0,0,1469,3623]),
(42629615666217053,2,[0,0,4,2468,2996]),
(42630833620437397,2,[0,0,1,9,161,1751,1914]),
(46906532406490489,14,[0,0,0,1,13,1177,3214]),
(48229292773239769,19,[0,0,0,1,1,1,4113]),
(48354539544749441,3,[0,0,0,0,0,0,0,2,10,16,3539]),
(48703553363031641,3,[0,0,0,2,8,18,62,3281]),
(48703553363031643,2,[0,1,1,9,4067]),
(48703553363031647,5,[0,63,4052]),
(48704944893127829,2,[0,0,6,4178]),
(48706336423224017,3,[0,0,0,0,13,15,2104,2175]),
(54164270106128243,2,[0,50,2483,2673]),
(55644505482806687,5,[0,24,436,1642,1909]),
(55644505482806689,17,[0,0,0,0,0,1,3,13,60,3367]),
(55644505482806693,2,[0,0,4324]),
(55646095325820487,5,[0,1,16,4092]),
(55647685168834303,3,[0,1,1,68,2091,2562]),
(63574642435633727,5,[0,80,4050]),
(63574642435633729,23,[0,0,0,0,0,0,1,3,3,3,3774]),
(63574642435633733,2,[0,0,5,75,3856]),
(63576458853989069,2,[0,0,5,8,15,93,356,2049]),
(63578275272344419,3,[0,1,549,1500,2675]),
(72505273334365601,3,[0,0,0,0,0,2,2,398,1366,1910]),
(72634937192046107,2,[0,65,475,3504]),
(72634937192046109,2,[0,0,1,1,4,4,87,268,2680]),
(72634937192046113,3,[0,0,0,0,0,5,219,3635]),
(72637012475965879,3,[0,1,4316]),
(72639087759885679,6,[0,1,97,198,1138,1974]),
(76095728314109111,11,[0,2,4296]),
(82986453383825207,5,[0,49,4105]),
(82986453383825209,23,[0,0,0,1,3,10,10,3728]),
(82986453383825213,2,[0,0,5,2596,2955]),
(82988824425350521,13,[0,0,0,1,2,43,94,242,2442]),
(82991195466875849,3,[0,0,0,4310]),
(86937972809594513,3,[0,0,0,0,9,28,264,3184]),
(87707122331518379,2,[0,5,23,2404,2557]),
(94813208512073321,6,[0,0,0,2,4238]),
(94813208512073323,2,[0,1,24,215,1171,2373]),
(94813208512073327,5,[0,4,83,3930])]
def block69 : Array Row := #[
(94815917460887969,3,[0,0,0,0,0,992,3646]),
(94818626409702623,5,[0,3,3,292,307,316,1523]),
(105446822764334081,3,[0,0,0,0,0,0,0,0,0,0,2,20,371,2913]),
(108325445199536441,3,[0,0,0,2,9,18,3803]),
(108325445199536443,3,[0,1,62,404,3467]),
(108325445199536447,7,[0,3,6,7,1223,3125]),
(108328540212256487,5,[0,4388]),
(108331635224976547,2,[0,1,13,164,3715]),
(123763368647071841,3,[0,0,0,0,0,2,11,3969]),
(123763368647071843,5,[0,1,5,19,27,175,3004]),
(123763368647071847,7,[0,3,4,99,3806]),
(123766904743318939,2,[0,1,261,3939]),
(123770440839566051,6,[0,2,2,224,3819]),
(130438314545807557,5,[0,0,1,1,18,621,1146,1757]),
(133199875374280963,5,[0,1,5,10,14,27,3414]),
(141401416727592881,3,[0,0,0,0,2,4222]),
(141401416727592883,2,[0,1,1,1,3,80,3770]),
(141401416727592887,5,[0,6,9,4088]),
(141405456768070819,3,[0,1,46,47,1675,2308]),
(141409496808548791,6,[0,1,2,4273]),
(145010546668731203,2,[0,4399]),
(161553138631527887,5,[0,2707,3296]),
(161553138631527889,17,[0,0,0,0,1,1,3,512,1296,2015]),
(161553138631527893,2,[0,0,8,17,23,3697]),
(161557754435488793,3,[0,0,0,62,2182,2820]),
(161562370239449717,2,[0,0,7,14,17,3754]),
(168847936039286719,6,[0,1,15,45,3844]),
(173875945619189027,2,[0,4411]),
(184576768788514007,5,[0,1068,3867]),
(184576768788514009,7,[0,0,0,1,18,65,1103,2613]),
(184576768788514013,2,[0,0,31,2188,3035]),
(184582042410479393,3,[0,0,0,0,0,3,74,1941,2395]),
(184587316032445021,6,[0,0,1,1,2,568,3664]),
(199944369877072823,5,[0,1168,3852]),
(210881595151802291,2,[0,2,126,2197,2674]),
(210881595151802293,5,[0,0,1,7,1953,3231]),
(210881595151802297,3,[0,0,0,4356]),
(210887620340235199,6,[0,1,6,46,86,3479]),
(210893645528668163,2,[0,4418]),
(223470840354937477,2,[0,0,1,3,3,1057,3440]),
(234519260931827771,6,[0,2,20,868,1384,1817]),
(240935235055146881,3,[0,0,0,0,0,0,0,2,2385,2904]),
(240935235055146883,5,[0,1,1,2095,3438]),
(240935235055146887,5,[0,89,2286,2925]),
(240942118919005633,19,[0,0,0,0,0,0,1,17,1121,3148]),
(240949002782864459,2,[0,18,1204,3553]),
(275271947982583037,2,[0,0,8,4250]),
(275271947982583039,3,[0,1,1,1551,3633]),
(275271947982583043,2,[0,87,744,3514]),
(275279812895382553,5,[0,0,0,1,1,9,32,66,122,2421]),
(275287677808182101,2,[0,0,2,2,147,2227,2265]),
(314502133026524117,2,[0,0,2854,3199]),
(314502133026524119,3,[0,1,5,14,29,1981,2147]),
(314502133026524123,2,[0,23,2541,3014]),
(314511118801753481,3,[0,0,0,2,23,543,3457]),
(314520104576982847,3,[0,1,2782,3216]),
(359323179870588797,2,[0,0,201,4049]),
(359323179870588799,3,[0,1,29,4165]),
(359323179870588803,2,[0,4,7,72,1601,2644]),
(359333446247156543,5,[0,3,415,953,3100]),
(359343712623724319,7,[0,3,4355]),
(385718591883261859,12,[0,1,5,368,1407,2701]),
(410531866190500721,3,[0,0,0,0,2,4279]),
(410531866190500723,2,[0,1,11,80,3882])]
def block70 : Array Row := #[
(410531866190500727,5,[0,3,103,133,3579]),
(410543595672391891,3,[0,1,1,2,1065,1211,2430]),
(410555325154283117,2,[0,0,7,8,966,3426]),
(444403346137843333,2,[0,0,1,10,27,85,1224,1968]),
(469038521863655537,3,[0,0,0,0,5,4231]),
(469038521863655539,10,[0,1,10,348,3782]),
(469038521863655543,5,[0,4456]),
(469051922964280213,2,[0,0,1,1,4322]),
(469065324064904891,2,[0,2,4380]),
(535883211779511137,3,[0,0,0,0,0,6,30,101,586,2310]),
(535883211779511139,2,[0,1,14,4224]),
(535883211779511143,5,[0,9,12,4115]),
(535898522728419143,5,[0,59,98,754,3000]),
(535913833677327233,3,[0,0,0,0,0,0,0,12,18,986,2870]),
(612254224932600641,3,[0,0,0,0,0,0,2,5,189,1075,2450]),
(612254224932600643,2,[0,1,3,9,4159]),
(612254224932600647,5,[0,4,6,7,4061]),
(612271717910455879,3,[0,1,1,4,24,3995]),
(612289210888311163,2,[0,1,9,2177,3284]),
(699509198474517617,3,[0,0,0,0,28,2632,2727]),
(699509198474517619,2,[0,1,1,4,84,179,3380]),
(699509198474517623,5,[0,13,4297]),
(699529184451616889,3,[0,0,0,6,11,2247,2874]),
(699549170428716163,2,[0,1,6,351,3845]),
(741226261355623369,11,[0,0,0,1,1,5,5,6,91,3379]),
(749171302536790979,2,[0,5,4362]),
(799199252245685777,3,[0,0,0,0,56,648,1159,2058]),
(799199252245685779,10,[0,1,4430]),
(799199252245685783,5,[0,59,1966,3270]),
(799222086510035653,2,[0,0,1,1,4349]),
(799244920774385573,2,[0,0,14,4266]),
(879355678517445133,26,[0,0,1,1,21,67,555,2994]),
(913096562822862287,5,[0,4,57,4091]),
(913096562822862289,17,[0,0,0,0,1,5,123,1874,2452]),
(913096562822862293,3,[0,0,3,9,41,3900]),
(913122651296085809,3,[0,0,0,0,741,3899]),
(913148739769309333,5,[0,0,1,4405]),
(1043225867261783627,2,[0,7,16,4158]),
(1043225867261783629,2,[0,0,1,1,1,13,4114]),
(1043225867261783633,5,[0,0,0,0,3,11,14,26,484,2622]),
(1043255673715134163,3,[0,1,4443]),
(1043285480168484757,2,[0,0,1,3,9,715,3558]),
(1191900456574258427,2,[0,684,1678,3076]),
(1191900456574258429,7,[0,0,1,1,1,1682,3562]),
(1191900456574258433,3,[0,0,0,0,0,0,0,0,11,4081]),
(1191934510873017727,3,[0,1,17,21,336,3454]),
(1191968565171777053,2,[0,0,4,118,973,3257]),
(1361763298785625997,2,[0,0,5,372,1111,3063]),
(1361763298785625999,3,[0,1,31,1262,3526]),
(1361763298785626003,2,[0,3,3,4323]),
(1361802206308448507,5,[0,3,15,4223]),
(1361841113831271083,2,[0,2801,3442]),
(1388576213866674193,5,[0,0,0,0,1,412,1723,2779]),
(1494321080133912677,2,[0,0,114,1950,3189]),
(1555834022624305427,2,[0,22,1172,3691]),
(1555834022624305429,2,[0,0,1,9,4272]),
(1555834022624305433,3,[0,0,0,8,550,661,674,1139]),
(1555878475024951843,5,[0,1,1,1,103,2459,2569]),
(1555922927425598317,6,[0,0,1,1,5,7,12,1866,2579]),
(1777562597048600501,2,[0,0,2,2,2,235,1716,2572]),
(1777562597048600503,6,[0,1,1,3,3,6,7,3901]),
(1777562597048600507,2,[0,2009,3797]),
(1777613384551373333,2,[0,0,4483]),
(1777664172054146171,2,[0,2,15,793,1436,2377])]
def block71 : Array Row := #[
(2030890660879476521,3,[0,0,0,2,9,170,3818]),
(2030890660879476523,5,[0,1,3,4382]),
(2030890660879476527,5,[0,5,1591,3736]),
(2030948686326930257,3,[0,0,0,0,30,2273,3105]),
(2031006711774384013,2,[0,0,1,782,3954]),
(2320321592778684497,3,[0,0,0,0,32,2417,3032]),
(2320321592778684499,2,[0,1,1,71,4142]),
(2320321592778684503,5,[0,3,3016,3161]),
(2320387887681335317,2,[0,0,1,5,8,4171]),
(2320454182583986157,2,[0,0,7,1986,3555]),
(2631213669945551371,10,[0,1,2,4412]),
(2651000567200974251,2,[0,2,2,2,17,4098]),
(2651000567200974253,2,[0,0,1,1,1,4,4230]),
(2651000567200974257,3,[0,0,0,0,2624,3428]),
(2651076310074322849,14,[0,0,0,0,0,1,8,2151,3178]),
(2651152052947671467,2,[0,69,4259]),
(3028806019463780261,3,[0,0,2,211,1870,3047]),
(3028806019463780263,13,[0,1,3,16,4204]),
(3028806019463780267,2,[0,92,4251]),
(3028892556778622119,6,[0,1,1,1,1,5,11,4009]),
(3028979094093463991,14,[0,2,12,4290]),
(3106317890020271497,5,[0,0,0,1,113,4111]),
(3332582913280018063,3,[0,1,3,14,1576,3427]),
(3460454145894944351,31,[0,2,2,9,9,46,162,852,1122]),
(3460454145894944353,5,[0,0,0,0,0,1,3,4,85,799,2902]),
(3460454145894944357,2,[0,0,7,11,365,3722]),
(3460553016013398511,3,[0,1,1,2,25,32,2219,2233]),
(3460651886131852693,2,[0,0,1,3,37,2019,3072]),
(3953618296744280531,2,[0,2,7,23,99,3716]),
(3953618296744280533,2,[0,0,1,2785,3388]),
(3953618296744280537,3,[0,0,0,1831,3802]),
(3953731257267044653,2,[0,0,1,1,3,30,4080]),
(3953844217789808809,7,[0,0,0,1,2413,3530]),
(4517065384291710137,3,[0,0,0,8,1016,1359,2661]),
(4517065384291710139,3,[0,1,3,3,11,15,64,75,2851]),
(4517065384291710143,5,[0,7,9,1249,1677,1877]),
(4517194443302689913,3,[0,0,0,94,4197]),
(4517323502313669739,10,[0,1,2951,3342]),
(4861475191090639697,3,[0,0,0,0,6,7,4191]),
(5160811731058801967,5,[0,8,10,10,1693,3119]),
(5160811731058801969,11,[0,0,0,0,1,80,4122]),
(5160811731058801973,2,[0,0,3,4,153,225,1081,1913]),
(5160959182822546513,5,[0,0,0,0,1,1,1,1501,3625]),
(5161106634586291163,2,[0,12,109,1976,2981]),
(5896301128616569337,3,[0,0,0,1493,3910]),
(5896301128616569339,7,[0,1,1,12,168,1691,2768]),
(5896301128616569343,5,[0,3,34,112,113,1079,1766]),
(5896469594363101249,7,[0,0,0,0,0,0,1,4,14,523,3430]),
(5896638060109633183,5,[0,1,3135,3228]),
(6736608272317734971,6,[0,2,243,4151]),
(6736608272317734973,2,[0,0,1,1,1,3,4304]),
(6736608272317734977,3,[0,0,0,0,0,0,4,24,51,637,2847]),
(6736800746839801219,2,[0,1,3,3,3,14,41,256,3028]),
(6736993221361867523,2,[0,6,50,1668,3322]),
(7696671188384160551,14,[0,2,2,312,2062,2893]),
(7696671188384160553,15,[0,0,0,1,1186,3923]),
(7696671188384160557,2,[0,0,3,3,3,3,13,18,1927,1942]),
(7696891093275257243,2,[0,2828,3586]),
(7697110998166354213,6,[0,0,1,3,18,2660,2876]),
(8793556785174451331,2,[0,2,4511]),
(8793556785174451333,2,[0,0,1,3,14,44,151,720,2198]),
(8793556785174451337,3,[0,0,0,10,729,3874]),
(8793808029654027781,13,[0,0,1,2,6,4303]),
(8794059274133604271,11,[0,1,1,2,61,4136])]
def block72 : Array Row := #[
(10046764249301753381,2,[0,0,2,4,281,1994,2776]),
(10046764249301753383,3,[0,1,6,949,3892]),
(10046764249301753387,2,[0,3,47,4252]),
(10047051299708876339,2,[0,519,2556,2935]),
(10047338350115999299,2,[0,1,3192,3227]),
(11478571680031065017,3,[0,0,0,4,4429]),
(11478571680031065019,7,[0,1,1,133,1124,3500]),
(11478571680031065023,5,[0,3,6,4381]),
(11478899639221923049,13,[0,0,0,1,3,3,11,758,3493]),
(11479227598412781089,3,[0,0,0,0,0,3,1806,3654]),
(13114432124030903201,3,[0,0,0,0,0,2,2,12,4144]),
(13114432124030903203,5,[0,1,1,718,4058]),
(13114432124030903207,5,[0,6,4477]),
(13114806822091589837,2,[0,0,5,8,879,3755]),
(13115181520152276479,13,[0,8,28,2110,3277]),
(14983426050735819581,3,[0,0,2,4505]),
(14983426050735819583,3,[0,1,1,1584,3898]),
(14983426050735819587,5,[0,3,5,2783,3253]),
(14983854148622983501,6,[0,0,1,1,1,1,2,2,2,4143]),
(14984282246510147447,5,[0,1854,3966]),
(17118778311909385271,29,[0,2,98,4253]),
(17118778311909385273,5,[0,0,0,1,1,3,1007,2124,2192]),
(17118778311909385277,2,[0,0,4,10,79,3993]),
(17119267419861154123,7,[0,1,427,4185]),
(17119756527812923091,6,[0,2,235,932,1496,2002]),
(19037617933748798963,2,[0,9,27,2362,3170]),
(19558448775332415587,5,[0,4,66,401,3771]),
(19558448775332415589,2,[0,0,1,320,942,3542]),
(19558448775332415593,3,[0,0,0,3,34,4237]),
(19559007588154568081,3,[0,0,0,0,2,120,148,1818,2168]),
(19559566400976720581,2,[0,0,2,3,4,19,52,1036,2748]),
(21751371905291498231,11,[0,2,29,87,143,3559]),
(22345807132229048801,3,[0,0,0,0,0,2,2,8,4203]),
(22345807132229048803,2,[0,1,1,36,311,3868]),
(22345807132229048807,5,[0,5,9,285,1894,2758]),
(22346445583861398239,7,[0,163,1619,3585]),
(22347084035493747701,2,[0,0,2,2,4455]),
(25530403874388021221,10,[0,0,2,13,194,3981]),
(25530403874388021223,3,[0,1,6,46,70,1989,2467]),
(25530403874388021227,2,[0,174,325,796,866,1173]),
(25531133314498718057,3,[0,0,0,48,1060,1447,2502]),
(25531862754609414893,2,[0,0,5,2336,3657]),
(29168851146543838181,2,[0,0,2,4,2214,3597]),
(29168851146543838183,3,[0,1,4582]),
(29168851146543838187,2,[0,23,2270,3595]),
(29169684542290882363,2,[0,1,60,322,3916]),
(29170517938037926609,7,[0,0,0,0,1,776,4035]),
(33325829132800180631,7,[0,2,4566]),
(33325829132800180633,5,[0,0,0,1,4532]),
(33325829132800180637,2,[0,0,4,6,9,26,2378,2394]),
(33326781299346832079,17,[0,740,847,3644]),
(33327733465893483649,17,[0,0,0,0,0,0,0,1,1,73,4051]),
(36074390480154136573,13,[0,0,1,3,4,2992,3020]),
(37063430857099327391,7,[0,2,1557,2393,2523]),
(38075235867497597927,5,[0,4633]),
(38075235867497597929,23,[0,0,0,1,1996,3837]),
(38075235867497597933,2,[0,0,52,4374]),
(38076323731379526433,10,[0,0,0,0,0,1,3,2290,3490]),
(38077411595261455357,2,[0,0,1,6,12,36,106,3556]),
(43501500910556980547,2,[0,1752,1955,2956]),
(43501500910556980549,7,[0,0,1,15,15,2343,3092]),
(43501500910556980553,3,[0,0,0,3115,3407]),
(43502743810582996463,5,[0,4639]),
(43503986710609012409,3,[0,0,0,444,1205,3532])]
def block73 : Array Row := #[
(49701086240324343947,2,[0,4,9,1176,3828]),
(49701086240324343949,2,[0,0,1,1,155,1681,3378]),
(49701086240324343953,3,[0,0,0,0,4565]),
(49702506271359781867,2,[0,1,5,7,19,1184,1476,1586]),
(49703926302395219891,6,[0,2,3,1921,3805]),
(56784201045088681727,5,[0,7,4533]),
(56784201045088681729,13,[0,0,0,0,0,0,0,0,1,1,85,2096,2837]),
(56784201045088681733,2,[0,0,19,4449]),
(56785823450832827159,7,[0,6,1971,3846]),
(56787445856576972591,13,[0,2,411,425,3737]),
(64876760896886077751,17,[0,2,2,2,5,4342]),
(64876760896886077753,7,[0,0,0,1,1,954,4025]),
(64876760896886077757,2,[0,0,8,52,4244]),
(64878614518625988793,5,[0,0,0,1,30,110,2001,2829]),
(64880468140365899843,2,[0,28,551,811,3339]),
(74122626135562336901,2,[0,0,2,2,4504]),
(74122626135562336903,3,[0,1,6,1061,2189,2676]),
(74122626135562336907,2,[0,3,3,9,18,154,841,2752]),
(74124743924880495823,3,[0,1,74,792,2170,2291]),
(74126861714198654783,5,[0,4661]),
(84686159254539022547,2,[0,80,333,981,3264]),
(84686159254539022549,7,[0,0,1,13,58,2692,2715]),
(84686159254539022553,3,[0,0,0,20,4436]),
(84688578859089152267,2,[0,4,1149,2257,2849]),
(84690998463639282017,3,[0,0,0,0,0,41,100,562,3340]),
(96755146750586054117,2,[0,0,25,97,4157]),
(96755146750586054119,3,[0,1,1829,4018]),
(96755146750586054123,2,[0,3,6,1826,3789]),
(96757911183350356601,3,[0,0,0,2,2,10,1904,3517]),
(96760675616114659103,5,[0,518,816,1594,2493]),
(110544137378926828121,3,[0,0,0,2,10,14,73,576,3175]),
(110544137378926828123,3,[0,1,3,5,91,4150]),
(110544137378926828127,5,[0,4,6,16,47,79,3571]),
(110547295782851940319,3,[0,1,1,13,1995,3674]),
(110550454186777052521,14,[0,0,0,1,2,12,42,1438,3219]),
(126298256157386465807,5,[0,15,16,4343]),
(126298256157386465809,7,[0,0,0,0,1,4554]),
(126298256157386465813,3,[0,0,4,6,4442]),
(126301864678990962617,3,[0,0,0,1301,2614,2699]),
(126305473200595459493,2,[0,0,8,12,4368]),
(144297561920616546287,10,[0,5,2607,3723]),
(144297561920616546289,31,[0,0,0,0,1,3,4,2992,3020]),
(144297561920616546293,2,[0,0,4660]),
(144301684708099992497,3,[0,0,0,0,7,794,4017]),
(144305807495583438713,3,[0,0,0,3,2959,3455]),
(164862025888046214797,2,[0,0,2433,3924]),
(164862025888046214799,13,[0,1,1,1,1,3,11,4265]),
(164862025888046214803,2,[0,67,159,190,265,2941]),
(164866736231643016133,2,[0,0,12,15,4336]),
(164871446575239817487,5,[0,15,1317,3991])]
def blocks : Array (Array Row) := #[block0,block1,block2,block3,block4,block5,block6,block7,block8,block9,block10,block11,block12,block13,block14,block15,block16,block17,block18,block19,block20,block21,block22,block23,block24,block25,block26,block27,block28,block29,block30,block31,block32,block33,block34,block35,block36,block37,block38,block39,block40,block41,block42,block43,block44,block45,block46,block47,block48,block49,block50,block51,block52,block53,block54,block55,block56,block57,block58,block59,block60,block61,block62,block63,block64,block65,block66,block67,block68,block69,block70,block71,block72,block73]
def size : ℕ := 4722
def rows (i : ℕ) : Row := ((blocks[i/64]?.getD #[])[i%64]?).getD (0,0,[])
def v (i : ℕ) : ℕ := (rows i).1

def Test (i : ℕ) : Prop :=
  let x := rows i
  let p := x.1
  let a := x.2.1
  let ids := x.2.2
  let fs := ids.map v
  p = 2 ∨ ((∀ j : ℕ, j ∈ ids → j < i) ∧ fs.prod = p-1 ∧ p-1 < 2^96 ∧
    Erdos473CompactPratt.residue p a 96 (p-1)=1 ∧
    fs.all (fun q => decide (Erdos473CompactPratt.residue p a 96 ((p-1)/q)%p ≠ 1%p)) = true)

instance (i : ℕ) : Decidable (Test i) := by unfold Test; infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check0 : ∀ j : Fin 128, Test (0+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check128 : ∀ j : Fin 128, Test (128+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check256 : ∀ j : Fin 128, Test (256+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check384 : ∀ j : Fin 128, Test (384+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check512 : ∀ j : Fin 128, Test (512+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check640 : ∀ j : Fin 128, Test (640+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check768 : ∀ j : Fin 128, Test (768+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check896 : ∀ j : Fin 128, Test (896+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1024 : ∀ j : Fin 128, Test (1024+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1152 : ∀ j : Fin 128, Test (1152+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1280 : ∀ j : Fin 128, Test (1280+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1408 : ∀ j : Fin 128, Test (1408+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1536 : ∀ j : Fin 128, Test (1536+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1664 : ∀ j : Fin 128, Test (1664+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1792 : ∀ j : Fin 128, Test (1792+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check1920 : ∀ j : Fin 128, Test (1920+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2048 : ∀ j : Fin 128, Test (2048+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2176 : ∀ j : Fin 128, Test (2176+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2304 : ∀ j : Fin 128, Test (2304+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2432 : ∀ j : Fin 128, Test (2432+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2560 : ∀ j : Fin 128, Test (2560+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2688 : ∀ j : Fin 128, Test (2688+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2816 : ∀ j : Fin 128, Test (2816+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check2944 : ∀ j : Fin 128, Test (2944+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3072 : ∀ j : Fin 128, Test (3072+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3200 : ∀ j : Fin 128, Test (3200+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3328 : ∀ j : Fin 128, Test (3328+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3456 : ∀ j : Fin 128, Test (3456+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3584 : ∀ j : Fin 128, Test (3584+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3712 : ∀ j : Fin 128, Test (3712+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3840 : ∀ j : Fin 128, Test (3840+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check3968 : ∀ j : Fin 128, Test (3968+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check4096 : ∀ j : Fin 128, Test (4096+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check4224 : ∀ j : Fin 128, Test (4224+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check4352 : ∀ j : Fin 128, Test (4352+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check4480 : ∀ j : Fin 128, Test (4480+j.val) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def check4608 : ∀ j : Fin 114, Test (4608+j.val) := by decide +kernel
theorem allCorrect (i : ℕ) (hi : i<size) : Test i := by
  change i<4722 at hi
  by_cases h0 : i<128
  · simpa only [show 0+(i-0)=i by omega] using check0 ⟨i-0,by omega⟩
  by_cases h128 : i<256
  · simpa only [show 128+(i-128)=i by omega] using check128 ⟨i-128,by omega⟩
  by_cases h256 : i<384
  · simpa only [show 256+(i-256)=i by omega] using check256 ⟨i-256,by omega⟩
  by_cases h384 : i<512
  · simpa only [show 384+(i-384)=i by omega] using check384 ⟨i-384,by omega⟩
  by_cases h512 : i<640
  · simpa only [show 512+(i-512)=i by omega] using check512 ⟨i-512,by omega⟩
  by_cases h640 : i<768
  · simpa only [show 640+(i-640)=i by omega] using check640 ⟨i-640,by omega⟩
  by_cases h768 : i<896
  · simpa only [show 768+(i-768)=i by omega] using check768 ⟨i-768,by omega⟩
  by_cases h896 : i<1024
  · simpa only [show 896+(i-896)=i by omega] using check896 ⟨i-896,by omega⟩
  by_cases h1024 : i<1152
  · simpa only [show 1024+(i-1024)=i by omega] using check1024 ⟨i-1024,by omega⟩
  by_cases h1152 : i<1280
  · simpa only [show 1152+(i-1152)=i by omega] using check1152 ⟨i-1152,by omega⟩
  by_cases h1280 : i<1408
  · simpa only [show 1280+(i-1280)=i by omega] using check1280 ⟨i-1280,by omega⟩
  by_cases h1408 : i<1536
  · simpa only [show 1408+(i-1408)=i by omega] using check1408 ⟨i-1408,by omega⟩
  by_cases h1536 : i<1664
  · simpa only [show 1536+(i-1536)=i by omega] using check1536 ⟨i-1536,by omega⟩
  by_cases h1664 : i<1792
  · simpa only [show 1664+(i-1664)=i by omega] using check1664 ⟨i-1664,by omega⟩
  by_cases h1792 : i<1920
  · simpa only [show 1792+(i-1792)=i by omega] using check1792 ⟨i-1792,by omega⟩
  by_cases h1920 : i<2048
  · simpa only [show 1920+(i-1920)=i by omega] using check1920 ⟨i-1920,by omega⟩
  by_cases h2048 : i<2176
  · simpa only [show 2048+(i-2048)=i by omega] using check2048 ⟨i-2048,by omega⟩
  by_cases h2176 : i<2304
  · simpa only [show 2176+(i-2176)=i by omega] using check2176 ⟨i-2176,by omega⟩
  by_cases h2304 : i<2432
  · simpa only [show 2304+(i-2304)=i by omega] using check2304 ⟨i-2304,by omega⟩
  by_cases h2432 : i<2560
  · simpa only [show 2432+(i-2432)=i by omega] using check2432 ⟨i-2432,by omega⟩
  by_cases h2560 : i<2688
  · simpa only [show 2560+(i-2560)=i by omega] using check2560 ⟨i-2560,by omega⟩
  by_cases h2688 : i<2816
  · simpa only [show 2688+(i-2688)=i by omega] using check2688 ⟨i-2688,by omega⟩
  by_cases h2816 : i<2944
  · simpa only [show 2816+(i-2816)=i by omega] using check2816 ⟨i-2816,by omega⟩
  by_cases h2944 : i<3072
  · simpa only [show 2944+(i-2944)=i by omega] using check2944 ⟨i-2944,by omega⟩
  by_cases h3072 : i<3200
  · simpa only [show 3072+(i-3072)=i by omega] using check3072 ⟨i-3072,by omega⟩
  by_cases h3200 : i<3328
  · simpa only [show 3200+(i-3200)=i by omega] using check3200 ⟨i-3200,by omega⟩
  by_cases h3328 : i<3456
  · simpa only [show 3328+(i-3328)=i by omega] using check3328 ⟨i-3328,by omega⟩
  by_cases h3456 : i<3584
  · simpa only [show 3456+(i-3456)=i by omega] using check3456 ⟨i-3456,by omega⟩
  by_cases h3584 : i<3712
  · simpa only [show 3584+(i-3584)=i by omega] using check3584 ⟨i-3584,by omega⟩
  by_cases h3712 : i<3840
  · simpa only [show 3712+(i-3712)=i by omega] using check3712 ⟨i-3712,by omega⟩
  by_cases h3840 : i<3968
  · simpa only [show 3840+(i-3840)=i by omega] using check3840 ⟨i-3840,by omega⟩
  by_cases h3968 : i<4096
  · simpa only [show 3968+(i-3968)=i by omega] using check3968 ⟨i-3968,by omega⟩
  by_cases h4096 : i<4224
  · simpa only [show 4096+(i-4096)=i by omega] using check4096 ⟨i-4096,by omega⟩
  by_cases h4224 : i<4352
  · simpa only [show 4224+(i-4224)=i by omega] using check4224 ⟨i-4224,by omega⟩
  by_cases h4352 : i<4480
  · simpa only [show 4352+(i-4352)=i by omega] using check4352 ⟨i-4352,by omega⟩
  by_cases h4480 : i<4608
  · simpa only [show 4480+(i-4480)=i by omega] using check4480 ⟨i-4480,by omega⟩
  simpa only [show 4608+(i-4608)=i by omega] using check4608 ⟨i-4608,by omega⟩
theorem certified (i : ℕ) (hi : i<size) : (v i).Prime := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain he|⟨hlt,prod,bound,full,parts⟩ := allCorrect i hi
    · change (rows i).1.Prime
      rw [he]
      decide
    · refine Erdos473CompactPratt.certify _ _ _ prod ?_ bound full parts
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      exact ih j (hlt j hj) (lt_trans (hlt j hj) hi)

end Erdos473MatchingPrimeDAG

end

section

/- Packed geometric groups for every matching state within the verified finite cutoff. -/

namespace Erdos473MatchingFiniteData
open Erdos473MatchingFiniteCore Erdos473MatchingCertCore Erdos473MatchingPrimeDAG

structure Group where
  hi : ℕ
  p : ℕ
  two : ℕ
  six : ℕ
  q : ℕ
  r : ℕ

instance : Inhabited Group := ⟨⟨0,0,0,0,0,0⟩⟩

set_option maxRecDepth 8192 in
def groups : Array Group := #[
⟨44920,1423,1424,1425,1424,1425⟩,
⟨49798,1458,1459,1460,1459,1460⟩,
⟨54565,1489,1490,1491,1490,1491⟩,
⟨59440,1514,1515,1516,1515,1516⟩,
⟨64123,1538,1539,1540,1539,1540⟩,
⟨68515,1560,1561,1562,1561,1562⟩,
⟨73300,1581,1582,1583,1582,1583⟩,
⟨78028,1597,1598,1599,1598,1599⟩,
⟨82858,1611,1612,1613,1612,1613⟩,
⟨87655,1626,1627,1628,1627,1628⟩,
⟨102380,1636,1637,1638,1638,1639⟩,
⟨107218,1671,1672,1673,1672,1673⟩,
⟨111973,1686,1687,1688,1687,1688⟩,
⟨126620,1703,1704,1705,1705,1706⟩,
⟨140528,1734,1735,1736,1736,1737⟩,
⟨155348,1768,1769,1770,1770,1771⟩,
⟨169880,1798,1799,1800,1800,1801⟩,
⟨183950,1820,1821,1822,1822,1823⟩,
⟨198653,1834,1835,1836,1836,1837⟩,
⟨203440,1855,1856,1857,1856,1857⟩,
⟨218288,1862,1863,1864,1864,1865⟩,
⟨233153,1878,1879,1880,1880,1881⟩,
⟨247583,1895,1896,1897,1897,1898⟩,
⟨262280,1916,1917,1918,1918,1919⟩,
⟨276833,1932,1933,1934,1934,1935⟩,
⟨291548,1946,1947,1948,1948,1949⟩,
⟨321380,1958,1959,1960,1961,1962⟩,
⟨334925,1990,1991,1992,1992,1993⟩,
⟨364433,2003,2004,2005,2006,2007⟩,
⟨367930,2023,2024,2025,2024,2025⟩,
⟨372553,2027,2028,2029,2028,2029⟩,
⟨405838,2032,2033,2034,2035,2036⟩,
⟨410290,2053,2054,2055,2054,2055⟩,
⟨413860,2059,2060,2061,2060,2061⟩,
⟨448333,2064,2065,2066,2067,2068⟩,
⟨507833,2081,2082,2083,2084,2085⟩,
⟨582128,2105,2106,2107,2108,2109⟩,
⟨646855,2134,2135,2136,2137,2138⟩,
⟨651295,2160,2161,2162,2161,2162⟩,
⟨740693,2163,2164,2165,2166,2167⟩,
⟨744418,2199,2200,2201,2200,2201⟩,
⟨823420,2202,2203,2204,2205,2206⟩,
⟨928073,2222,2223,2224,2225,2226⟩,
⟨1031120,2251,2252,2253,2254,2255⟩,
⟨1170223,2275,2276,2277,2278,2279⟩,
⟨1322620,2297,2298,2299,2300,2301⟩,
⟨1384404,2318,2319,2320,2321,2322⟩,
⟨1562648,2328,2329,2330,2331,2332⟩,
⟨1785158,2345,2346,2347,2348,2349⟩,
⟨2029090,2365,2366,2367,2368,2369⟩,
⟨2318368,2399,2400,2401,2402,2403⟩,
⟨2620300,2437,2438,2439,2440,2441⟩,
⟨2918602,2461,2462,2463,2464,2465⟩,
⟨3255768,2477,2478,2479,2480,2481⟩,
⟨3688926,2497,2498,2499,2500,2501⟩,
⟨4187080,2518,2519,2520,2521,2522⟩,
⟨4281880,2535,2536,2537,2538,2539⟩,
⟨4890562,2544,2545,2546,2547,2548⟩,
⟨5584015,2564,2565,2566,2567,2568⟩,
⟨6374810,2588,2589,2590,2591,2592⟩,
⟨7272680,2616,2617,2618,2619,2620⟩,
⟨8281664,2634,2635,2636,2637,2638⟩,
⟨9433388,2649,2650,2651,2652,2653⟩,
⟨10764368,2666,2667,2668,2669,2670⟩,
⟨12279790,2684,2685,2686,2687,2688⟩,
⟨14004760,2702,2703,2704,2705,2706⟩,
⟨15924805,2721,2722,2723,2724,2725⟩,
⟨18189280,2743,2744,2745,2746,2747⟩,
⟨20732855,2764,2765,2766,2767,2769⟩,
⟨23646620,2791,2792,2793,2794,2795⟩,
⟨26984435,2813,2814,2815,2816,2817⟩,
⟨30770255,2831,2832,2833,2834,2835⟩,
⟨34990388,2840,2841,2842,2843,2844⟩,
⟨39949720,2857,2858,2859,2860,2861⟩,
⟨45641023,2878,2879,2880,2881,2882⟩,
⟨52066615,2897,2898,2899,2900,2901⟩,
⟨59340515,2907,2908,2909,2910,2911⟩,
⟨67797365,2926,2927,2928,2929,2930⟩,
⟨77365705,2945,2946,2947,2948,2949⟩,
⟨88206688,2964,2965,2966,2967,2968⟩,
⟨100524725,2987,2988,2989,2990,2991⟩,
⟨114563525,3005,3006,3007,3008,3009⟩,
⟨130785916,3021,3022,3023,3025,3026⟩,
⟨149416790,3038,3039,3040,3041,3042⟩,
⟨170460068,3053,3054,3055,3056,3057⟩,
⟨194345422,3064,3065,3066,3067,3068⟩,
⟨221686566,3078,3079,3080,3081,3082⟩,
⟨253177568,3095,3096,3097,3098,3099⟩,
⟨289176116,3110,3111,3112,3113,3114⟩,
⟨330146614,3127,3128,3129,3130,3131⟩,
⟨377116144,3140,3141,3142,3143,3144⟩,
⟨430510090,3154,3155,3156,3157,3158⟩,
⟨491463562,3163,3164,3165,3166,3167⟩,
⟨561226016,3179,3180,3181,3182,3183⟩,
⟨641206378,3193,3194,3195,3196,3197⟩,
⟨732510926,3208,3209,3210,3211,3212⟩,
⟨836907728,3221,3222,3223,3224,3225⟩,
⟨956164550,3233,3234,3235,3236,3237⟩,
⟨1092407424,3244,3245,3246,3247,3248⟩,
⟨1248087088,3259,3260,3261,3262,3263⟩,
⟨1425846500,3272,3273,3274,3275,3276⟩,
⟨1629057158,3290,3291,3292,3293,3294⟩,
⟨1861222273,3298,3299,3300,3301,3302⟩,
⟨2126493518,3311,3312,3313,3314,3315⟩,
⟨2429569422,3323,3324,3325,3326,3327⟩,
⟨2775125152,3333,3334,3335,3336,3337⟩,
⟨3170657455,3344,3345,3346,3347,3348⟩,
⟨3622265390,3358,3359,3360,3361,3362⟩,
⟨4138533208,3373,3374,3375,3376,3377⟩,
⟨4728191498,3389,3390,3391,3392,3393⟩,
⟨5402100983,3395,3396,3397,3398,3399⟩,
⟨6171801354,3409,3410,3411,3412,3413⟩,
⟨7051384588,3420,3421,3422,3423,3424⟩,
⟨8056368988,3433,3434,3435,3436,3437⟩,
⟨9204651343,3445,3446,3447,3448,3449⟩,
⟨10516507255,3458,3459,3460,3461,3462⟩,
⟨12015257788,3474,3475,3476,3477,3478⟩,
⟨13727611873,3483,3484,3485,3486,3487⟩,
⟨15684052943,3494,3495,3496,3497,3498⟩,
⟨17919247355,3507,3508,3509,3510,3511⟩,
⟨20473025923,3521,3522,3523,3524,3525⟩,
⟨23390756768,3534,3535,3536,3537,3538⟩,
⟨26724314063,3549,3550,3551,3552,3554⟩,
⟨30532909133,3565,3566,3567,3568,3569⟩,
⟨34884298333,3573,3574,3575,3576,3577⟩,
⟨39855890548,3580,3581,3582,3583,3584⟩,
⟨45535970995,3589,3590,3591,3592,3593⟩,
⟨52025548483,3604,3605,3606,3607,3608⟩,
⟨59440010165,3616,3617,3618,3619,3620⟩,
⟨67911157658,3626,3627,3628,3629,3630⟩,
⟨77589506990,3639,3640,3641,3642,3643⟩,
⟨88647239423,3648,3649,3650,3651,3652⟩,
⟨101280808955,3658,3659,3660,3661,3662⟩,
⟨115714803863,3668,3669,3670,3671,3672⟩,
⟨132205965925,3678,3679,3680,3681,3682⟩,
⟨151047213133,3686,3687,3688,3689,3690⟩,
⟨172573728353,3692,3693,3694,3695,3696⟩,
⟨197167958735,3700,3701,3702,3703,3704⟩,
⟨225267255608,3708,3709,3710,3711,3712⟩,
⟨257371060118,3717,3718,3719,3720,3721⟩,
⟨294050106403,3729,3730,3731,3732,3733⟩,
⟨335956448578,3740,3741,3742,3743,3744⟩,
⟨383835023638,3749,3750,3751,3752,3753⟩,
⟨438537043300,3756,3757,3758,3759,3760⟩,
⟨501034829240,3764,3765,3766,3767,3768⟩,
⟨572439533173,3777,3778,3779,3780,3781⟩,
⟨654020339920,3784,3785,3786,3787,3788⟩,
⟨747227600915,3792,3793,3794,3795,3796⟩,
⟨853718428015,3807,3808,3809,3810,3811⟩,
⟨975385506155,3813,3814,3815,3816,3817⟩,
⟨1114391889650,3822,3823,3824,3825,3826⟩,
⟨1273208671135,3829,3830,3831,3832,3833⟩,
⟨1454659095763,3838,3839,3840,3841,3842⟩,
⟨1661968812773,3847,3848,3849,3850,3851⟩,
⟨1898823160120,3858,3859,3860,3861,3862⟩,
⟨2169432620098,3869,3870,3871,3872,3873⟩,
⟨2478607747738,3876,3877,3878,3879,3880⟩,
⟨2831844780575,3884,3885,3886,3887,3888⟩,
⟨3235423112003,3893,3894,3895,3896,3897⟩,
⟨3696517236335,3903,3904,3905,3906,3907⟩,
⟨4223323830878,3911,3912,3913,3914,3915⟩,
⟨4825207811248,3918,3919,3920,3921,3922⟩,
⟨5512868879240,3925,3926,3927,3928,3929⟩,
⟨6298531512655,3932,3933,3934,3935,3936⟩,
⟨7196162282450,3940,3941,3942,3943,3944⟩,
⟨8221718279093,3947,3948,3949,3950,3951⟩,
⟨9393430635713,3955,3956,3957,3958,3959⟩,
⟨10732128814448,3961,3962,3963,3964,3965⟩,
⟨12261610540480,3970,3971,3972,3973,3974⟩,
⟨14009065261858,3976,3977,3978,3979,3980⟩,
⟨16005557256043,3986,3987,3988,3989,3990⟩,
⟨18286577807725,3996,3997,3998,3999,4000⟩,
⟨20892676407070,4003,4004,4005,4006,4007⟩,
⟨23870181282458,4012,4013,4014,4015,4016⟩,
⟨27272023129768,4020,4021,4022,4023,4024⟩,
⟨31158676047865,4027,4028,4029,4030,4031⟩,
⟨35599232765413,4037,4038,4039,4040,4041⟩,
⟨40672632069980,4042,4043,4044,4045,4046⟩,
⟨46469063179663,4053,4054,4055,4056,4057⟩,
⟨53091568699780,4062,4063,4064,4065,4066⟩,
⟨60657875714968,4069,4070,4071,4072,4073⟩,
⟨69302489565170,4075,4076,4077,4078,4079⟩,
⟨79179084561313,4083,4084,4085,4086,4087⟩,
⟨90463235414665,4093,4094,4095,4096,4097⟩,
⟨103355538812518,4100,4101,4102,4103,4104⟩,
⟨118085179748395,4106,4107,4108,4109,4110⟩,
⟨134914004832938,4116,4117,4118,4119,4120⟩,
⟨154141177842910,4123,4124,4125,4126,4127⟩,
⟨176108497870610,4130,4131,4132,4133,4134⟩,
⟨201206474754848,4137,4138,4139,4140,4141⟩,
⟨229881271924090,4145,4146,4147,4148,4149⟩,
⟨262642637202733,4152,4153,4154,4155,4156⟩,
⟨300072965212613,4160,4161,4162,4163,4164⟩,
⟨342837649621573,4166,4167,4168,4169,4170⟩,
⟨391696912420748,4172,4173,4174,4175,4176⟩,
⟨447519318175285,4180,4181,4182,4183,4184⟩,
⟨511297214172728,4186,4187,4188,4189,4190⟩,
⟨584164371502850,4192,4193,4194,4195,4196⟩,
⟨667416139669730,4198,4199,4200,4201,4202⟩,
⟨762532474184000,4207,4208,4209,4210,4211⟩,
⟨871204245155510,4212,4213,4214,4215,4216⟩,
⟨995363295950950,4217,4218,4219,4220,4221⟩,
⟨1137216785125010,4225,4226,4227,4228,4229⟩,
⟨1299286423076458,4232,4233,4234,4235,4236⟩,
⟨1484453299591448,4239,4240,4241,4242,4243⟩,
⟨1696009101283048,4245,4246,4247,4248,4249⟩,
⟨1937714626910920,4254,4255,4256,4257,4258⟩,
⟨2213866642873505,4260,4261,4262,4263,4264⟩,
⟨2529374266235488,4267,4268,4269,4270,4271⟩,
⟨2889846233116945,4274,4275,4276,4277,4278⟩,
⟨3301690605003415,4280,4281,4282,4283,4284⟩,
⟨3772228683257900,4285,4286,4287,4288,4289⟩,
⟨4309825159705015,4291,4292,4293,4294,4295⟩,
⟨4924036813946488,4298,4299,4300,4301,4302⟩,
⟨5625782403355015,4305,4306,4307,4308,4309⟩,
⟨6427536764189783,4311,4312,4313,4314,4315⟩,
⟨7343552575269748,4317,4318,4319,4320,4321⟩,
⟨8390113725301198,4325,4326,4327,4328,4329⟩,
⟨9585824789996608,4330,4331,4332,4333,4334⟩,
⟨10951941762973978,4337,4338,4339,4340,4341⟩,
⟨12512749920631400,4344,4345,4346,4347,4348⟩,
⟨14295995537893078,4350,4351,4352,4353,4354⟩,
⟨16333379130668240,4357,4358,4359,4360,4361⟩,
⟨18661118990844925,4363,4364,4365,4366,4367⟩,
⟨21320595034511660,4369,4370,4371,4372,4373⟩,
⟨24359084406853355,4375,4376,4377,4378,4379⟩,
⟨27830601921985820,4383,4384,4385,4386,4387⟩,
⟨31796860275903343,4389,4390,4391,4392,4393⟩,
⟨36328367106171863,4394,4395,4396,4397,4398⟩,
⟨41505678395453053,4400,4401,4402,4403,4404⟩,
⟨47420830505197603,4406,4407,4408,4409,4410⟩,
⟨54178976292656660,4413,4414,4415,4416,4417⟩,
⟨61900254399883220,4419,4420,4421,4422,4423⟩,
⟨70721924941280920,4424,4425,4426,4427,4428⟩,
⟨80800809558641440,4431,4432,4433,4434,4435⟩,
⟨92316079218028943,4437,4438,4439,4440,4441⟩,
⟨105472439307722003,4444,4445,4446,4447,4448⟩,
⟨120503768658171145,4450,4451,4452,4453,4454⟩,
⟨137677277174453440,4457,4458,4459,4460,4461⟩,
⟨157298255990081518,4462,4463,4464,4465,4466⟩,
⟨179715504586672058,4467,4468,4469,4470,4471⟩,
⟨205327531354659398,4472,4473,4474,4475,4476⟩,
⟨234589637823175360,4478,4479,4480,4481,4482⟩,
⟨268022012493517768,4484,4485,4486,4487,4488⟩,
⟨306218978159770568,4489,4490,4491,4492,4493⟩,
⟨349859557104395320,4494,4495,4496,4497,4498⟩,
⟨399719541985438808,4499,4500,4501,4502,4503⟩,
⟨456685286997532888,4506,4507,4508,4509,4510⟩,
⟨521769464470236143,4512,4513,4514,4515,4516⟩,
⟨596129067007231813,4517,4518,4519,4520,4521⟩,
⟨681085975185379213,4522,4523,4524,4525,4526⟩,
⟨778150456449087998,4527,4528,4529,4530,4531⟩,
⟨889048012928192713,4534,4535,4536,4537,4538⟩,
⟨1015750055456380250,4539,4540,4541,4542,4543⟩,
⟨1160508949074078260,4544,4545,4546,4547,4548⟩,
⟨1325898053016392248,4549,4550,4551,4552,4553⟩,
⟨1514857466971982125,4555,4556,4557,4558,4559⟩,
⟨1730746296836535130,4560,4561,4562,4563,4564⟩,
⟨1977402369082872175,4567,4568,4569,4570,4571⟩,
⟨2259210455282445265,4572,4573,4574,4575,4576⟩,
⟨2581180219595295068,4577,4578,4579,4580,4581⟩,
⟨2949035274890765983,4583,4584,4585,4586,4587⟩,
⟨3369314930638064668,4588,4589,4590,4591,4592⟩,
⟨3849490441324487485,4593,4594,4595,4596,4597⟩,
⟨4398097821933810275,4598,4599,4600,4601,4602⟩,
⟨5024889591528350665,4603,4604,4605,4606,4607⟩,
⟨5741008142458271690,4608,4609,4610,4611,4612⟩,
⟨6559183817160612508,4613,4614,4615,4616,4617⟩,
⟨7493961213732041600,4618,4619,4620,4621,4622⟩,
⟨8561957743277709790,4623,4624,4625,4626,4627⟩,
⟨9782159035376822635,4628,4629,4630,4631,4632⟩,
⟨11176256443047442793,4634,4635,4636,4637,4638⟩,
⟨12769032646988119400,4640,4641,4642,4643,4644⟩,
⟨14588802213936100610,4645,4646,4647,4648,4649⟩,
⟨16667914940882374090,4650,4651,4652,4653,4654⟩,
⟨19043330933028710315,4655,4656,4657,4658,4659⟩,
⟨21757277638570063963,4662,4663,4664,4665,4666⟩,
⟨24858000520318280273,4667,4668,4669,4670,4671⟩,
⟨28400620708756971973,4672,4673,4674,4675,4676⟩,
⟨32448114882907920863,4677,4678,4679,4680,4681⟩,
⟨37072434798220643875,4682,4683,4684,4685,4686⟩,
⟨42355786363178473450,4687,4688,4689,4690,4691⟩,
⟨48392091002593811273,4692,4693,4694,4695,4696⟩,
⟨55288655286049237058,4697,4698,4699,4700,4701⟩,
⟨63168078502243909060,4702,4703,4704,4705,4706⟩,
⟨72170432089935257903,4707,4708,4709,4710,4711⟩,
⟨82455749668923798143,4712,4713,4714,4715,4716⟩,
⟨90953418231753380142,4717,4718,4719,4720,4721⟩]
def g (i : ℕ) : Group := groups[i]?.getD default
def lower (i : ℕ) := if i=0 then 40000 else (g (i-1)).hi+1

def Valid (i : ℕ) : Prop :=
  let a := g i
  let p := v a.p
  let q := v a.q
  let r := v a.r
  let d := (q-p)/2
  let e := (r-q)/2
  a.p<size ∧ a.two<size ∧ a.six<size ∧ a.q<size ∧ a.r<size ∧
  v a.two=p+2 ∧ v a.six=p+6 ∧ q=p+2*d ∧ r=p+2*d+2*e ∧
  Feasible (lower i) a.hi p d e

instance (i : ℕ) : Decidable (Valid i) := by unfold Valid; infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
def validated : ∀ i : Fin groups.size, Valid i.val := by decide +kernel

theorem interval (i : ℕ) (h : i<groups.size) : Covers (lower i) (g i).hi := by
  obtain ⟨hp,ht,hs,hq,hr,et,es,eq,er,hgeom⟩ := validated ⟨i,h⟩
  refine one hgeom (certified _ hp) (et ▸ certified _ ht) (es ▸ certified _ hs)
    (eq ▸ certified _ hq) (er ▸ certified _ hr)

theorem collected (i : ℕ) (h : i<groups.size) : Covers 40000 (g i).hi := by
  induction i with
  | zero => exact interval 0 h
  | succ i ih =>
    apply join (ih (by omega))
    simpa [lower] using interval (i+1) h

set_option maxRecDepth 8192 in
theorem covered : Covers 40000 90953418231753380142 := collected 287 (by decide)

set_option maxRecDepth 8192 in
theorem small {n : ℕ} (lo : 57≤n) (hi : n≤90953418231753380142) : Small n := by
  by_cases hn : 40000≤n
  · exact (covered n hn hi).1
  obtain h|h := Nat.lt_or_ge n 101
  · exact ⟨101,by omega,by omega,(show Nat.Prime 101 from certified 25 (by decide)),(show Nat.Prime 103 from certified 26 (by decide)),(show Nat.Prime 107 from certified 27 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 107
  · exact ⟨107,by omega,by omega,(show Nat.Prime 107 from certified 27 (by decide)),(show Nat.Prime 109 from certified 28 (by decide)),(show Nat.Prime 113 from certified 29 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 191
  · exact ⟨191,by omega,by omega,(show Nat.Prime 191 from certified 42 (by decide)),(show Nat.Prime 193 from certified 43 (by decide)),(show Nat.Prime 197 from certified 44 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 347
  · exact ⟨347,by omega,by omega,(show Nat.Prime 347 from certified 68 (by decide)),(show Nat.Prime 349 from certified 69 (by decide)),(show Nat.Prime 353 from certified 70 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 641
  · exact ⟨641,by omega,by omega,(show Nat.Prime 641 from certified 115 (by decide)),(show Nat.Prime 643 from certified 116 (by decide)),(show Nat.Prime 647 from certified 117 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 1091
  · exact ⟨1091,by omega,by omega,(show Nat.Prime 1091 from certified 181 (by decide)),(show Nat.Prime 1093 from certified 182 (by decide)),(show Nat.Prime 1097 from certified 183 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 2081
  · exact ⟨2081,by omega,by omega,(show Nat.Prime 2081 from certified 307 (by decide)),(show Nat.Prime 2083 from certified 308 (by decide)),(show Nat.Prime 2087 from certified 309 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 4127
  · exact ⟨4127,by omega,by omega,(show Nat.Prime 4127 from certified 490 (by decide)),(show Nat.Prime 4129 from certified 491 (by decide)),(show Nat.Prime 4133 from certified 492 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 8231
  · exact ⟨8231,by omega,by omega,(show Nat.Prime 8231 from certified 703 (by decide)),(show Nat.Prime 8233 from certified 704 (by decide)),(show Nat.Prime 8237 from certified 705 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 16187
  · exact ⟨16187,by omega,by omega,(show Nat.Prime 16187 from certified 913 (by decide)),(show Nat.Prime 16189 from certified 914 (by decide)),(show Nat.Prime 16193 from certified 915 (by decide))⟩
  obtain h|h := Nat.lt_or_ge n 32321
  · exact ⟨32321,by omega,by omega,(show Nat.Prime 32321 from certified 1147 (by decide)),(show Nat.Prime 32323 from certified 1148 (by decide)),(show Nat.Prime 32327 from certified 1149 (by decide))⟩
  exact ⟨64151,by omega,by omega,(show Nat.Prime 64151 from certified 1367 (by decide)),(show Nat.Prime 64153 from certified 1368 (by decide)),(show Nat.Prime 64157 from certified 1369 (by decide))⟩
end Erdos473MatchingFiniteData

end

section

/- Complete numerical descent for virtual matching states below the finite cutoff. -/

namespace Erdos473MatchingFiniteInduction

open Erdos473MatchingFiniteCore Erdos473MatchingFiniteData

theorem descend (A : ℕ → ℕ → Prop)
    (seed : ∀ n k, n≤56 → k≤3 → 2*k≤n → A n k)
    (expand : ∀ n k p : ℕ, n<p → p/2+2*k+1≤n → p.Prime → (p+2).Prime →
      A (p-n-1+2*k+2) (k+1) → A n k)
    (three : ∀ n p : ℕ, n<p → p/2+7≤n → p.Prime → (p+2).Prime → (p+6).Prime →
      A (p-n-1+6) 2 → A n 3)
    (contract : ∀ n k p d e : ℕ, n<p → p/2+2*k+d≤n → 0<d → d≤e → 2*d+e≤k →
      p.Prime → (p+2*d).Prime → (p+2*d+2*e).Prime → A (p-n-1+2*k) (k-d) → A n k)
    (n k : ℕ) (cap : n≤90953418231753380142) (space : 2*k≤n)
    (hk : k≤3 ∨ 10000*k≤n) : A n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    by_cases smallN : n≤56
    · exact seed n k smallN (by omega) space
    by_cases smallK : k≤3
    · obtain ⟨p,lo,room,hp,hq,hr⟩ := small (by omega : 57≤n) cap
      by_cases tk : k=3
      · subst k
        exact three n p lo room hp hq hr
          (ih _ (by omega) 2 (by omega) (by omega) (Or.inl (by decide)))
      · exact expand n k p lo (by omega) hp hq
          (ih _ (by omega) (k+1) (by omega) (by omega) (Or.inl (by omega)))
    · have linear : 10000*k≤n := by omega
      obtain ⟨p,d,e,hp0,hroom,hd,he,depth,hp,hq,hr,child⟩ :=
        (covered n (by omega) cap).2 k (by omega) linear
      exact contract n k p d e hp0 hroom hd he depth hp hq hr
        (ih _ (by omega) (k-d) (by omega) (by omega) (Or.inr child))

end Erdos473MatchingFiniteInduction

end

section

/- Explicit numerical bounds for prime-count intervals in the conductor construction. -/

namespace Erdos473LogBounds

open Real

lemma log_constant {c δ : ℝ} (k : ℕ) (hc : 0 < c) (hd : 0 ≤ δ)
    (h : c ≤ (2.718:ℝ)^k * (1+δ+δ^2/2+δ^3/6+δ^4/24)) :
    log c ≤ k+δ := by
  have e1 : (2.718:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have ek : exp (k:ℝ) = (exp 1)^k := by simp
  have er : 1+δ+δ^2/2+δ^3/6+δ^4/24 ≤ exp δ := by
    have hs := sum_le_exp_of_nonneg hd 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at hs
    linarith
  apply (log_le_iff_le_exp hc).mpr
  rw [exp_add,ek]
  exact h.trans (mul_le_mul (pow_le_pow_left₀ (by norm_num) e1 k) er (by positivity) (by positivity))

lemma log_log_bound {H : ℝ} (hH : 45 ≤ H) : log H ≤ 0.085*H := by
  have hc : log 45 ≤ (3:ℝ)+0.825 := log_constant 3 (by norm_num) (by norm_num) (by norm_num)
  have h := log_le_sub_one_of_pos (show 0 < H/45 by positivity)
  rw [log_div (by linarith) (by norm_num)] at h
  linarith

lemma endpoint_bounds {n x : ℝ} (hn : 0 < n) (hH : 45 ≤ log n)
    (hx : n-0.11*(n/log n) ≤ x ∧ x ≤ n+0.105*(n/log n)) :
    0 < x ∧ log n ≤ 1.001*log x ∧ log x ≤ 1.001*log n ∧
      x/log x ≤ 1.007*(n/log n) := by
  have hp : 0 < log n := by linarith
  have hL : n/log n ≤ n/45 := (div_le_div_iff₀ hp (by norm_num)).mpr (by nlinarith)
  have hl : 0.9975*n ≤ x := by linarith
  have hu : x ≤ 1.0025*n := by linarith
  have hxp : 0 < x := by linarith
  have h₁ := log_le_sub_one_of_pos (div_pos hxp hn)
  have h₂ := log_le_sub_one_of_pos (div_pos hn hxp)
  rw [log_div hxp.ne' hn.ne'] at h₁
  rw [log_div hn.ne' hxp.ne'] at h₂
  have q₁ : x/n ≤ 1.0025 := (div_le_iff₀ hn).mpr (by linarith)
  have q₂ : n/x ≤ 1.003 := (div_le_iff₀ hxp).mpr (by linarith)
  have hlx : log n ≤ 1.001*log x := by linarith
  refine ⟨hxp,hlx,by linarith,?_⟩
  have hlogx : 0 < log x := by linarith
  rw [div_le_iff₀ hlogx, mul_div_assoc', div_mul_eq_mul_div,
    le_div_iff₀ hp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) hp.le, mul_nonneg hn.le (sub_nonneg.mpr hlx)]

lemma theta_errors {n x y : ℝ} (hn : 0 < n) (hH : 45 ≤ log n)
    (hx : n-0.11*(n/log n) ≤ x ∧ x ≤ n+0.105*(n/log n))
    (hy : n-0.11*(n/log n) ≤ y ∧ y ≤ n+0.105*(n/log n)) :
    (x/log x+y/log y)/840 < 0.0024*(n/log n) := by
  have ax := (endpoint_bounds hn hH hx).2.2.2
  have ay := (endpoint_bounds hn hH hy).2.2.2
  have : 0 < n/log n := div_pos hn (by linarith)
  linarith

lemma bt_fixed {n ℓ B C β : ℝ} (hn : 0 < n) (hH : 45 ≤ log n)
    (hℓ : 0 < ℓ) (hB : ℓ ≤ B) (hC : 0 < C) (hβ : 0 ≤ 1-0.085-β)
    (hb : log (B/C) ≤ (1-0.085-β)*45) :
    β*log n ≤ log (C*(n/log n)/ℓ) := by
  have hp : 0 < log n := by linarith
  have hBp : 0 < B := by linarith
  have hlog := log_le_log hℓ hB
  rw [log_div hBp.ne' hC.ne'] at hb
  rw [log_div (by positivity) hℓ.ne',log_mul hC.ne' (by positivity),
    log_div hn.ne' hp.ne']
  linarith [log_log_bound hH, mul_le_mul_of_nonneg_left hH hβ]

lemma bt_small {n ℓ : ℝ} (hn : 0 < n) (hH : 45 ≤ log n) (hℓ : 0 < ℓ) (hb : ℓ ≤ 97) :
    0.70*log n ≤ log (0.09*(n/log n)/(12*ℓ)) ∧
    0.75*log n ≤ log (0.11*(n/log n)/ℓ) := by
  constructor
  · rw [show 0.09*(n/log n)/(12*ℓ) = (0.09/12)*(n/log n)/ℓ by ring]
    exact bt_fixed hn hH hℓ hb (by norm_num) (by norm_num)
      ((log_constant (c := 97/(0.09/12)) (δ := 0.675) 9 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
  · exact bt_fixed hn hH hℓ hb (by norm_num) (by norm_num)
      ((log_constant (c := 97/0.11) (δ := 0.425) 7 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))

lemma bt_medium {n ℓ : ℝ} (hn : 0 < n) (hH : 45 ≤ log n) (hℓ : 0 < ℓ) (hb : ℓ ≤ 100000) :
    0.55*log n ≤ log (0.09*(n/log n)/(12*ℓ)) ∧
    0.60*log n ≤ log (0.11*(n/log n)/ℓ) := by
  constructor
  · rw [show 0.09*(n/log n)/(12*ℓ) = (0.09/12)*(n/log n)/ℓ by ring]
    exact bt_fixed hn hH hℓ hb (by norm_num) (by norm_num)
      ((log_constant (c := 100000/(0.09/12)) (δ := 0.425) 16 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
  · exact bt_fixed hn hH hℓ hb (by norm_num) (by norm_num)
      ((log_constant (c := 100000/0.11) (δ := 0.175) 14 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))

lemma bt_root_aux {n ℓ C β : ℝ} (hn : 0 < n) (hH : 45 ≤ log n)
    (hℓ : 0 < ℓ) (hb : ℓ ≤ sqrt n) (hC : 0 < C) (hβ : 0 ≤ 0.5-0.085-β)
    (hbound : log (1/C) ≤ (0.5-0.085-β)*45) :
    β*log n ≤ log (C*(n/log n)/ℓ) := by
  have hp : 0 < log n := by linarith
  have hlog := log_le_log hℓ hb
  rw [log_sqrt hn.le] at hlog
  rw [one_div,log_inv] at hbound
  rw [log_div (by positivity) hℓ.ne',log_mul hC.ne' (by positivity),log_div hn.ne' hp.ne']
  linarith [log_log_bound hH,mul_le_mul_of_nonneg_left hH hβ]

lemma bt_root {n ℓ : ℝ} (hn : 0 < n) (hH : 45 ≤ log n) (hℓ : 0 < ℓ) (hb : ℓ ≤ sqrt n) :
    0.30*log n ≤ log (0.09*(n/log n)/(12*ℓ)) ∧
    0.36*log n ≤ log (0.11*(n/log n)/ℓ) := by
  constructor
  · rw [show 0.09*(n/log n)/(12*ℓ) = (0.09/12)*(n/log n)/ℓ by ring]
    exact bt_root_aux hn hH hℓ hb (by norm_num) (by norm_num)
      ((log_constant (c := 1/(0.09/12)) (δ := 0.175) 5 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
  · exact bt_root_aux hn hH hℓ hb (by norm_num) (by norm_num)
      ((log_constant (c := 1/0.11) (δ := 0.475) 2 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))

lemma large_prime_error {n : ℝ} (hn : 0 < n) (hH : 45 ≤ log n) :
    log n / sqrt n + (log n)^2/(0.11*n) < 0.0001 := by
  have hp : 0 < log n := by linarith
  have hroot := sqrt_pos.mpr hn
  have hlog : log 100000 ≤ (12:ℝ)+0 := log_constant 12 (by norm_num) (by norm_num) (by norm_num)
  have gain : 100000*log n ≤ sqrt n := by
    apply (log_le_log_iff (by positivity) hroot).mp
    rw [log_mul (by norm_num) hp.ne',log_sqrt hn.le]
    linarith [log_log_bound hH]
  have q₁ : log n / sqrt n ≤ 0.00001 := (div_le_iff₀ hroot).mpr (by linarith)
  have sq := mul_self_le_mul_self (by positivity : 0 ≤ 100000*log n) gain
  have eq := sq_sqrt hn.le
  have q₂ : (log n)^2/(0.11*n) ≤ 0.00001 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  linarith


/-- The earlier certificate range extends beyond the input scale of the
explicit logarithmic estimates. -/
theorem checked_range_log {n : ℝ} (hn : 90953418231753380142 ≤ n) : 45 ≤ log n := by
  apply (le_log_iff_exp_le (by linarith)).mpr
  have he : exp 45 = (exp 1)^45 := by
    simp
  rw [he]
  calc
    (exp 1)^45 ≤ (2.72:ℝ)^45 :=
      pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) 45
    _ ≤ 90953418231753380142 := by norm_num
    _ ≤ n := hn

end Erdos473LogBounds

end

section

/- Explicit scales for the matching transfer on a near-dyadic prime interval. -/

namespace Erdos473TripleConstants

open Real

abbrev C : ℝ := 1000000

noncomputable def gap (H : ℝ) : ℕ := ⌈0.368*C*H^2⌉₊
noncomputable def width (H : ℝ) : ℕ := ⌊1.31*C*H^3⌋₊

/-- At a bucket of width 1.31 C H³ the available prime density beats the
cost of sieving one short interval for each dyadic annulus. -/
lemma scales {H : ℝ} (hh : 45≤H) :
    ∃ j : ℕ, ∃ z : ℝ, 1<z ∧ z≤16*H ∧ width H < 2^j*gap H ∧
      ((j:ℝ)+1)*((gap H:ℝ)/log z+z^2) < 0.558*C*H^2 := by
  let L := log (16*H)
  let z := exp (0.97*L)
  let j := ⌈log (3.6*H)/log 2⌉₊
  have lh : 0<L := log_pos (by linarith)
  have logz : log z=0.97*L := log_exp _
  have ez : 1<z := (one_lt_exp_iff).mpr (by dsimp [L] at *; linarith)
  have eL : exp L=16*H := exp_log (by linarith)
  have zle : z≤16*H := by rw [←eL]; apply exp_le_exp.mpr; linarith
  have gaplo : 0.368*C*H^2 ≤ (gap H:ℝ) := Nat.le_ceil _
  have gaphi : (gap H:ℝ) ≤ 0.368001*C*H^2 := by
    have h := Nat.ceil_lt_add_one (show 0≤0.368*C*H^2 by dsimp [C]; positivity)
    change (⌈0.368*C*H^2⌉₊:ℝ) ≤ _
    dsimp [C] at *; nlinarith [sq_nonneg (H-1)]
  have wle : (width H:ℝ) ≤ 1.31*C*H^3 := Nat.floor_le (by positivity)
  have lg : 0<log 2 := log_pos (by norm_num)
  have lg' : 0.69<log 2 := by linarith [log_two_gt_d9]
  have arg : 0<log (3.6*H) := log_pos (by linarith)
  have jlo := (div_le_iff₀ lg).mp (Nat.le_ceil (log (3.6*H)/log 2))
  have jhi := Nat.ceil_lt_add_one (div_nonneg arg.le lg.le)
  have jhi' : ((j:ℝ)+1)*log 2 ≤ L := by
    have h₁ : ((j:ℝ)+1)*log 2 < log (3.6*H)+2*log 2 := by
      have h := (lt_div_iff₀ lg).mp (show (j:ℝ)-1 < log (3.6*H)/log 2 by dsimp [j]; linarith)
      linarith
    have h₂ : log (3.6*H)+2*log 2 ≤ L := by
      rw [show 2*log 2=log (2*2) by rw [log_mul (by norm_num) (by norm_num)]; ring,
          ←log_mul (by linarith) (by norm_num)]
      apply log_le_log (by positivity)
      norm_num; linarith
    exact h₁.le.trans h₂
  have powj : 3.6*H ≤ (2:ℝ)^j := by
    apply (log_le_log_iff (by linarith) (by positivity)).mp
    rw [log_pow]; exact jlo
  have wlt : (width H:ℝ) < (2:ℝ)^j*(gap H:ℝ) := by
    have h := mul_le_mul powj gaplo (by dsimp [C]; linarith) (by positivity)
    dsimp [C] at h wle ⊢
    have hc : 0<H^3 := by positivity
    nlinarith
  refine ⟨j,z,ez,zle,by exact_mod_cast wlt,?_⟩
  have js : ((j:ℝ)+1)*0.69 ≤ L := by
    have hs : 0≤(j:ℝ)+1 := by positivity
    linarith [mul_le_mul_of_nonneg_left lg'.le hs]
  have main : ((j:ℝ)+1)*((gap H:ℝ)/log z) ≤ 0.551*C*H^2 := by
    rw [logz,mul_div_assoc',div_le_iff₀ (by linarith)]
    have h₁ := mul_le_mul_of_nonneg_left gaphi (show 0≤(j:ℝ)+1 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right js (sq_nonneg H)
    dsimp [C] at *
    nlinarith
  have zz : z^2=exp (1.94*L) := by
    rw [sq,← exp_add]; congr 1; ring
  have ep : exp (0.06*L)*exp (1.94*L)=(16*H)*(16*H) := by
    rw [←exp_add,show 0.06*L+1.94*L=L+L by ring,exp_add,eL]
  have ie := mul_le_mul_of_nonneg_right (add_one_le_exp (0.06*L)) (exp_pos (1.94*L)).le
  have er : L*z^2 ≤ 4267*H^2 := by
    rw [zz]
    rw [ep] at ie
    nlinarith [exp_pos (1.94*L),sq_nonneg H]
  have jsz := mul_le_mul_of_nonneg_right js (sq_nonneg z)
  dsimp [C] at *
  rw [mul_add]
  have sqp : 0<H^2 := by positivity
  nlinarith only [main,er,jsz,sqp]

/-- The upper band may discard a polylogarithmic cap to leave room for ports. -/
lemma power_budget {n H : ℝ} (hn : 90953418231753380142≤n) (hH : H=log (2*n)) :
    45≤H ∧ 1000000000000*H^4≤n := by
  have hp : 0<n := by linarith
  have ht := Erdos473LogBounds.checked_range_log (n:=2*n) (by linarith)
  rw [←hH] at ht
  refine ⟨ht,?_⟩
  have hc : log 1000000000000 ≤ (28:ℝ)+0.1 :=
    Erdos473LogBounds.log_constant 28 (by norm_num) (by norm_num) (by norm_num)
  have eq : H=log 2+log n := by rw [hH,log_mul (by norm_num) hp.ne']
  apply (log_le_log_iff (by positivity) hp).mp
  rw [log_mul (by norm_num) (by positivity),log_pow]
  norm_num only [Nat.cast_ofNat]
  have hv := Erdos473LogBounds.log_log_bound ht
  have lt₂ : log (2:ℝ)<1 := by linarith [log_two_lt_d9]
  linarith

end Erdos473TripleConstants

end

section

/- Finite Selberg weights with an interval discrepancy of at most one. -/

namespace Erdos473Selberg

open Finset Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius

/-- Mobius inversion on the multiples of a divisor in a squarefree number. -/
lemma mobius_multiples (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) =
    if l = m then (μ l : ℤ) else 0 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hmpos hm
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, zsmul_eq_mul]
      change μ (m/l) * μ l = μ m
      have hc : (m/l).Coprime l := Nat.coprime_of_squarefree_mul (by rwa [hmul])
      rw [← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc, hmul]
    · intro d _ hdl
      rw [if_neg hdl.symm, smul_zero]
    · intro h
      exact (h (Nat.mem_divisors.mpr ⟨hl, by omega⟩)).elim
  · rw [if_neg hl, sum_eq_zero]
    intro d hd
    rw [if_neg, smul_zero]
    rintro rfl
    exact hl (Nat.dvd_of_mem_divisors hd)

lemma mobius_divisor_interval {P l m : ℕ} (hs : Squarefree P) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  have h := mobius_multiples l m (hs.squarefree_of_dvd hm)
  have he : (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℤ) else 0) =
      ∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0 := by
    rw [← Nat.divisors_filter_dvd_of_dvd hs.ne_zero hm, Finset.sum_filter]
    congr! 1 with d
    by_cases h₁ : l ∣ d <;> by_cases h₂ : d ∣ m <;> simp [h₁,h₂]
  exact_mod_cast he.trans h

/-- The sum of squares weight on all divisors of a squarefree sieve support has
total absolute mass at most the square of the l1 norm of the coefficients. -/
theorem lambda_error_le (s : BoundingSieve) (w : ℕ → ℝ)
    (hr : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ 1) :
    s.errSum (lambdaSquared w) ≤ (∑ d ∈ s.prodPrimes.divisors, |w d|)^2 := by
  let P := s.prodPrimes
  have triangle (d : ℕ) : |lambdaSquared w d| ≤ lambdaSquared (fun t => |w t|) d := by
    unfold lambdaSquared
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i hi
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j hj
    split_ifs <;> simp [abs_mul]
  calc s.errSum (lambdaSquared w)
      ≤ ∑ d ∈ P.divisors, lambdaSquared (fun t => |w t|) d := by
          apply sum_le_sum
          intro d hd
          exact (mul_le_of_le_one_right (abs_nonneg _) (hr d hd)).trans (triangle d)
    _ = ∑ d ∈ P.divisors, ∑ i ∈ P.divisors, ∑ j ∈ P.divisors,
          if d = Nat.lcm i j then |w i| * |w j| else 0 := by
          unfold lambdaSquared
          congr! 1 with d hd
          rw [Nat.mem_divisors] at hd
          have h (i j : ℕ) : (i ∣ d ∧ j ∣ d ∧ d = i.lcm j) = (d = i.lcm j) := by
            simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
          simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero,
            ← ite_and, h]
    _ = (∑ d ∈ P.divisors, |w d|)^2 := by
          rw [sq, sum_mul, sum_comm]
          congr! 1 with i hi
          rw [mul_sum, sum_comm]
          congr! 1 with j hj
          rw [sum_ite_eq_of_mem']
          exact Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hi)
            (Nat.dvd_of_mem_divisors hj), s.prodPrimes_ne_zero⟩

/-- The truncated Selberg mass and the numerator of the optimal weights. -/
noncomputable def truncMass (s : BoundingSieve) (z d : ℕ) : ℝ :=
  ∑ k ∈ s.prodPrimes.divisors, if d ∣ k ∧ k ≤ z then s.selbergTerms k else 0

noncomputable def sieveWeight (s : BoundingSieve) (z d : ℕ) : ℝ :=
  (μ d : ℝ) * truncMass s z d / (s.nu d * truncMass s z 1)

lemma truncMass_pos (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) : 0 < truncMass s z 1 := by
  unfold truncMass
  apply Finset.sum_pos'
  · intro k hk
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk)).le
    · rfl
  · refine ⟨1, Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero, ?_⟩
    rw [if_pos ⟨dvd_refl 1,hz⟩]
    exact s.selbergTerms_pos (one_dvd _)

lemma sieveWeight_one (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) : sieveWeight s z 1 = 1 := by
  simp [sieveWeight, s.nu_mult.map_one, (truncMass_pos s hz).ne']

lemma diagonal_optimal (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) (l : ℕ)
    (hl : l ∈ s.prodPrimes.divisors) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * sieveWeight s z d else 0) =
      (if l ≤ z then s.selbergTerms l * (μ l : ℝ) else 0) / truncMass s z 1 := by
  let P := s.prodPrimes
  have pos := truncMass_pos s hz
  have swap (d : ℕ) (hd : d ∈ P.divisors) :
      s.nu d * sieveWeight s z d =
       ((μ d : ℝ) * truncMass s z d) / truncMass s z 1 := by
    unfold sieveWeight
    field_simp [s.nu_ne_zero (Nat.dvd_of_mem_divisors hd)]
  calc _ = (∑ d ∈ P.divisors, ∑ k ∈ P.divisors,
        if l ∣ d ∧ d ∣ k ∧ k ≤ z then (μ d : ℝ) * s.selbergTerms k else 0) / truncMass s z 1 := by
          rw [Finset.sum_div]
          apply sum_congr rfl
          intro d hd
          rw [swap d hd, truncMass, mul_sum]
          by_cases h : l ∣ d
          · simp only [h,true_and,if_true,mul_ite,mul_zero,P]
          · simp [h]
    _ = (∑ k ∈ P.divisors, if k ≤ z then
         (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ k then (μ d : ℝ) else 0) * s.selbergTerms k
         else 0) / truncMass s z 1 := by
          rw [Finset.sum_comm]
          congr! 1
          apply sum_congr rfl
          intro k hk
          by_cases h : k ≤ z
          · simp only [h, and_true, if_true, Finset.sum_mul, ite_mul, zero_mul]
          · simp [h]
    _ = _ := by
          congr 1
          rw [Finset.sum_eq_single l]
          · rw [mobius_divisor_interval s.prodPrimes_squarefree (Nat.dvd_of_mem_divisors hl)]
            simp [mul_comm]
          · intro k hk hkl
            rw [mobius_divisor_interval s.prodPrimes_squarefree (Nat.dvd_of_mem_divisors hk)]
            simp [hkl.symm]
          · exact fun hn => (hn hl).elim

theorem optimal_main (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    s.mainSum (lambdaSquared (sieveWeight s z)) = (truncMass s z 1)⁻¹ := by
  rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  let G := truncMass s z 1
  have hG : 0 < G := truncMass_pos s hz
  calc _ = (∑ l ∈ s.prodPrimes.divisors, if 1 ∣ l ∧ l ≤ z then s.selbergTerms l else 0) / G^2 := by
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro l hl
        rw [diagonal_optimal s hz l hl]
        by_cases h : l ≤ z
        · simp only [h, if_true, one_dvd, and_self]
          have hsq : (μ l : ℝ)^2 = 1 := by
            exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
              (s.squarefree_of_mem_divisors_prodPrimes hl)
          have hg := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne'
          change (s.selbergTerms l)⁻¹ * ((s.selbergTerms l * (μ l : ℝ))/G)^2 = _
          rw [div_pow,mul_pow,hsq]
          field_simp
        · simp [h]
    _ = _ := by
      change G / G^2 = G⁻¹
      field_simp

lemma divisor_lcm_recover {d k e : ℕ} (hk : Squarefree k) (hd : d ∣ k) (he : e ∣ d) :
    Nat.lcm d (k/e) = k := by
  have hek := he.trans hd
  have heq := Nat.div_mul_cancel hek
  have hcop : (k/e).Coprime e := Nat.coprime_of_squarefree_mul (by rwa [heq])
  apply Nat.dvd_antisymm
  · exact Nat.lcm_dvd hd (Nat.div_dvd_of_dvd hek)
  · have hm : k/e * e ∣ d.lcm (k/e) :=
      hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right ..) (he.trans (Nat.dvd_lcm_left ..))
    rwa [heq] at hm

/-- Removing a divisor of d from each multiple of d gives distinct divisors,
and their Selberg terms majorize the weight numerator. -/
theorem truncMass_bound (s : BoundingSieve) (z d : ℕ) (hd : d ∣ s.prodPrimes) :
    (s.nu d)⁻¹ * truncMass s z d ≤ truncMass s z 1 := by
  let P := s.prodPrimes
  let M := P.divisors.filter (fun k => d ∣ k ∧ k ≤ z)
  let D := P.divisors.filter (fun k => k ≤ z)
  let f (t : ℕ × ℕ) := t.1 / t.2
  have hm (k : ℕ) (h : k ∈ M) : k ∣ P ∧ d ∣ k ∧ k ≤ z :=
    ⟨Nat.dvd_of_mem_divisors (Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2⟩
  have input (v : ℕ × ℕ) (hv : v ∈ M ×ˢ d.divisors) :
      v.1 ∣ P ∧ d ∣ v.1 ∧ v.1 ≤ z ∧ v.2 ∣ d := by
    obtain ⟨hk, he⟩ := Finset.mem_product.mp hv
    exact ⟨(hm _ hk).1,(hm _ hk).2.1,(hm _ hk).2.2,Nat.dvd_of_mem_divisors he⟩
  have recover (v : ℕ × ℕ) (hv : v ∈ M ×ˢ d.divisors) :
      d.lcm (f v) = v.1 := by
    obtain ⟨hk, hdk, _, he⟩ := input v hv
    exact divisor_lcm_recover (s.squarefree_of_dvd_prodPrimes hk) hdk he
  have inj : Set.InjOn f ↑(M ×ˢ d.divisors) := by
    intro v hv w hw h
    have hk : v.1 = w.1 := (recover v hv).symm.trans ((congrArg (Nat.lcm d) h).trans (recover w hw))
    obtain ⟨hkv, hdv, _, hev⟩ := input v hv
    obtain ⟨hkw, hdw, _, hew⟩ := input w hw
    have h₁ : f v * v.2 = v.1 := Nat.div_mul_cancel (hev.trans hdv)
    have h₂ : f w * w.2 = w.1 := Nat.div_mul_cancel (hew.trans hdw)
    have hy : f w ≠ 0 := by
      intro z
      rw [z, zero_mul] at h₂
      exact (s.squarefree_of_dvd_prodPrimes hkw).ne_zero h₂.symm
    rw [h] at h₁
    exact Prod.ext hk (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hy) (h₁.trans (hk.trans h₂.symm)))
  have sub : (M ×ˢ d.divisors).image f ⊆ D := by
    intro j hj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hk, hdk, hz, he⟩ := input v hv
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Nat.div_dvd_of_dvd (he.trans hdk)).trans hk,s.prodPrimes_ne_zero⟩,
      (Nat.div_le_self ..).trans hz⟩
  have terms (k : ℕ) (hk : k ∈ M) (e : ℕ) (he : e ∈ d.divisors) :
      (s.selbergTerms e)⁻¹ * s.selbergTerms k = s.selbergTerms (k/e) := by
    have hek := (Nat.dvd_of_mem_divisors he).trans (hm k hk).2.1
    have hmk := Nat.div_mul_cancel hek
    have hc : (k/e).Coprime e := Nat.coprime_of_squarefree_mul (by
      rw [hmk]
      exact s.squarefree_of_dvd_prodPrimes (hm k hk).1)
    have eq := s.selbergTerms_isMultiplicative.map_mul_of_coprime hc
    rw [hmk] at eq
    calc _ = (s.selbergTerms e)⁻¹ * (s.selbergTerms (k/e) * s.selbergTerms e) := congrArg _ eq
         _ = _ := by
           have gne := (s.selbergTerms_pos ((Nat.dvd_of_mem_divisors he).trans hd)).ne'
           field_simp
  calc _ = (∑ e ∈ d.divisors, (s.selbergTerms e)⁻¹) * ∑ k ∈ M, s.selbergTerms k := by
          rw [s.nu_inv_eq_sum_divisors_inv_selbergTerms hd, ← Finset.sum_filter,
            Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd, truncMass, ← Finset.sum_filter]
    _ = ∑ v ∈ M ×ˢ d.divisors, s.selbergTerms (f v) := by
          rw [Finset.sum_mul, Finset.sum_product, Finset.sum_comm]
          apply sum_congr rfl
          intro e he
          rw [Finset.mul_sum]
          exact sum_congr rfl fun k hk => terms k hk e he
    _ = ∑ j ∈ (M ×ˢ d.divisors).image f, s.selbergTerms j := (Finset.sum_image inj).symm
    _ ≤ ∑ j ∈ D, s.selbergTerms j :=
          Finset.sum_le_sum_of_subset_of_nonneg sub fun j hj _ =>
            (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hj).1)).le
    _ = _ := by simp [D, truncMass, Finset.sum_filter, P]

theorem sieveWeight_abs_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) (d : ℕ)
    (hd : d ∣ s.prodPrimes) : |sieveWeight s z d| ≤ 1 := by
  have den := s.nu_pos_of_dvd_prodPrimes hd
  have G := truncMass_pos s hz
  have num : 0 ≤ truncMass s z d := by
    apply sum_nonneg
    intro k hk
    split_ifs
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hk)).le
    · rfl
  have mu : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  rw [sieveWeight, abs_div, abs_mul, mu, one_mul, abs_of_nonneg num,
    abs_of_pos (mul_pos den G), div_le_one (mul_pos den G)]
  have h := truncMass_bound s z d hd
  rwa [← div_eq_inv_mul, div_le_iff₀ den, mul_comm] at h

lemma sieveWeight_vanish (s : BoundingSieve) {z d : ℕ} (hz : z < d) : sieveWeight s z d = 0 := by
  have num : truncMass s z d = 0 := by
    unfold truncMass
    apply sum_eq_zero
    intro k hk
    apply if_neg
    rintro ⟨hdk, hkz⟩
    exact hz.not_ge ((Nat.le_of_dvd (Nat.pos_of_mem_divisors hk) hdk).trans hkz)
  simp [sieveWeight, num]

theorem optimal_sieve (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hr : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ 1) :
    s.siftedSum ≤ s.totalMass / truncMass s z 1 + (z : ℝ)^2 := by
  let F := s.prodPrimes.divisors.filter (· ≤ z)
  have sub : F ⊆ Finset.Icc 1 z := by
    intro d hd
    obtain ⟨h,k⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors h,k⟩
  have card : F.card ≤ z := by simpa using Finset.card_le_card sub
  have bound : (∑ d ∈ s.prodPrimes.divisors, |sieveWeight s z d|) ≤ z := by
    calc _ = ∑ d ∈ F, |sieveWeight s z d| := by
                rw [Finset.sum_subset (Finset.filter_subset _ _)]
                intro d hd hn
                rw [sieveWeight_vanish s (by simpa [F,hd] using hn),abs_zero]
         _ ≤ ∑ d ∈ F, (1 : ℝ) := sum_le_sum fun d hd =>
                sieveWeight_abs_le s hz d (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
         _ = (F.card : ℝ) := by simp
         _ ≤ _ := by exact_mod_cast card
  calc _ ≤ s.totalMass * s.mainSum (lambdaSquared (sieveWeight s z)) + s.errSum (lambdaSquared (sieveWeight s z)) :=
          s.siftedSum_le_mainSum_errSum_of_upperMoebius _ (upperMoebius_lambdaSquared _ (sieveWeight_one s hz))
       _ ≤ _ := by
          rw [optimal_main s hz, ←div_eq_mul_inv]
          apply add_le_add_right
          exact (lambda_error_le s _ hr).trans (by gcongr)


end Erdos473Selberg

end

section

namespace Erdos473Progressions

/-- The count in a single progression on a real interval differs from its length
divided by the modulus by strictly less than one. -/
theorem discrepancy {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {q : ℕ} (hq : 0 < q) (v : ℕ) :
    |((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq q n v)).card -
      (y-x)/(q : ℝ)| < 1 := by
  let Q := (q : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast hq
  have floor_eq (z : ℝ) (hz : 0 ≤ z) :
      ⌊((⌊z⌋₊ : ℚ)-v)/(q : ℚ)⌋ = ⌊(z-v)/Q⌋ := by
    dsimp [Q]
    simp only [Int.floor_div_natCast,Int.floor_sub_natCast,Int.floor_natCast,
      Int.natCast_floor_eq_floor hz]
  have dc := Nat.Ioc_filter_modEq_card ⌊x⌋₊ ⌊y⌋₊ hq v
  rw [floor_eq y (hx.trans hxy),floor_eq x hx] at dc
  have mono : ⌊(x-v)/Q⌋ ≤ ⌊(y-v)/Q⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hxy _) hQ.le)
  rw [max_eq_left (sub_nonneg.mpr mono)] at dc
  have eqreal : (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq q n v)).card : ℝ) =
      (⌊(y-v)/Q⌋ : ℝ) - (⌊(x-v)/Q⌋ : ℝ) := by exact_mod_cast dc
  rw [eqreal,abs_lt]
  have diff : (y-x)/(q : ℝ) = (y-v)/Q-(x-v)/Q := by dsimp [Q]; ring
  rw [diff]
  constructor <;> linarith [Int.floor_le ((x-v)/Q),Int.lt_floor_add_one ((x-v)/Q),
    Int.floor_le ((y-v)/Q),Int.lt_floor_add_one ((y-v)/Q)]

theorem crt_discrepancy {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) (hc : q.Coprime d) (c : ℕ) :
    |((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq q n c ∧ d ∣ n)).card -
      (y-x)/((q*d : ℕ) : ℝ)| < 1 := by
  let v := Nat.chineseRemainder hc c 0
  have hf : ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq q n c ∧ d ∣ n)) =
      (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq (q*d) n v.val) := by
    apply Finset.filter_congr
    intro n _
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hc,← Nat.modEq_zero_iff_dvd]
    exact and_congr ⟨(·.trans v.prop.1.symm),(·.trans v.prop.1)⟩
      ⟨(·.trans v.prop.2.symm),(·.trans v.prop.2)⟩
  rw [hf]
  exact discrepancy hx hxy (Nat.mul_pos hq hd) _

end Erdos473Progressions

end

section

namespace Erdos473Selberg

open Finset Nat BoundingSieve

def sievePrimes (z q : ℕ) : Finset ℕ := (Nat.primesLE z).filter (fun p => ¬p ∣ q)

def sieveProduct (z q : ℕ) : ℕ := ∏ p ∈ sievePrimes z q, p

lemma mem_sievePrimes {z q p : ℕ} : p ∈ sievePrimes z q ↔ p.Prime ∧ p ≤ z ∧ ¬p ∣ q := by
  simp [sievePrimes, Nat.mem_primesLE, and_assoc, _root_.and_comm]

lemma sieveProduct_sqfree (z q : ℕ) : Squarefree (sieveProduct z q) := by
  apply (squarefree_primorial z).squarefree_of_dvd
  rw [sieveProduct, primorial_eq_prod_primesLE]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

lemma sieveProduct_primes (z q : ℕ) : (sieveProduct z q).primeFactors = sievePrimes z q :=
  Nat.primeFactors_prod fun _ h => (mem_sievePrimes.mp h).1

lemma sieveProduct_coprime (z q : ℕ) : (sieveProduct z q).Coprime q := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p h
  obtain ⟨hp,_,hq⟩ := mem_sievePrimes.mp h
  exact hp.coprime_iff_not_dvd.mpr hq

lemma sieveProduct_divides_iff {z q d : ℕ} (hd : d ≤ z) :
    d ∣ sieveProduct z q ↔ Squarefree d ∧ d.Coprime q := by
  constructor
  · exact fun h => ⟨(sieveProduct_sqfree z q).squarefree_of_dvd h,
      (sieveProduct_coprime z q).of_dvd_left h⟩
  · rintro ⟨hs,hc⟩
    rw [← Nat.prod_primeFactors_of_squarefree hs, Nat.prod_primeFactors_dvd_iff (sieveProduct_sqfree z q).ne_zero,
      sieveProduct_primes]
    intro p hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact mem_sievePrimes.mpr ⟨hp',(Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hpd).trans hd,
      hp'.coprime_iff_not_dvd.mp (hc.of_dvd_left hpd)⟩

noncomputable def intervalSieve (x y : ℝ) (q c z : ℕ) : BoundingSieve where
  support := (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq q n c)
  prodPrimes := sieveProduct z q
  prodPrimes_squarefree := sieveProduct_sqfree z q
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (y-x)/q
  nu := ⟨fun d => (d : ℝ)⁻¹, by simp⟩
  nu_mult := ⟨by simp, fun _ => by simp [mul_comm]⟩
  nu_pos_of_prime := fun p hp _ => by
    change 0 < (p : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => by
    change (p : ℝ)⁻¹ < 1
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

lemma intervalTerms (x y : ℝ) (q c z d : ℕ) :
    (intervalSieve x y q c z).selbergTerms d = (d.totient : ℝ)⁻¹ := by
  have h : (d.totient : ℝ) = d * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have e := congrArg (fun a : ℚ => (a : ℝ)) (Nat.totient_eq_mul_prod_factors d)
    simpa using e
  rw [selbergTerms_apply,h,mul_inv,Finset.prod_inv_distrib]
  rfl

noncomputable def divisorMass (q z : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ d.Coprime q), (d.totient : ℝ)⁻¹

lemma intervalMass (x y : ℝ) (q c z : ℕ) :
    truncMass (intervalSieve x y q c z) z 1 = divisorMass q z := by
  unfold truncMass divisorMass
  simp only [one_dvd,true_and,← Finset.sum_filter,intervalTerms]
  congr 1
  ext d
  change (d ∈ (sieveProduct z q).divisors.filter (· ≤ z)) ↔ _
  simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors,
    (sieveProduct_sqfree z q).ne_zero,ne_eq,not_false_eq_true,and_true]
  constructor
  · rintro ⟨h,dz⟩
    have h' := (sieveProduct_divides_iff dz).mp h
    exact ⟨⟨Nat.pos_of_ne_zero h'.1.ne_zero,dz⟩,h'⟩
  · rintro ⟨⟨_,dz⟩,hs⟩
    exact ⟨(sieveProduct_divides_iff dz).mpr hs,dz⟩

theorem progression_sieve {x y : ℝ} {q z : ℕ} (c : ℕ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hzx : (z : ℝ) ≤ x) (hq : 0 < q) (hz : 1 ≤ z) :
    (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.ModEq q p c ∧ p.Prime)).card : ℝ)
      ≤ ((y-x)/q) / divisorMass q z + (z:ℝ)^2 := by
  let s := intervalSieve x y q c z
  have err (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) : |s.rem d| ≤ 1 := by
    have hdiv : d ∣ sieveProduct z q := Nat.dvd_of_mem_divisors hd
    have hc := ((sieveProduct_coprime z q).of_dvd_left hdiv).symm
    have ht := (Erdos473Progressions.crt_discrepancy hx hxy hq (Nat.pos_of_mem_divisors hd) hc c).le
    have m : s.multSum d = (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun n => Nat.ModEq q n c ∧ d ∣ n)).card : ℝ) := by
      simp [s, intervalSieve, multSum, Finset.filter_filter]
    rw [rem,m]
    change abs (_ - (d : ℝ)⁻¹ * ((y-x)/q)) ≤ 1
    have eq' : (d : ℝ)⁻¹ * ((y-x)/q) = (y-x)/((q*d:ℕ):ℝ) := by push_cast; ring
    rwa [eq']
  have count :
      (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.ModEq q p c ∧ p.Prime)).card : ℝ) ≤ s.siftedSum := by
    have sub : ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.ModEq q p c ∧ p.Prime)) ⊆
      s.support.filter (fun p => s.prodPrimes.Coprime p) := by
      intro p hp
      obtain ⟨hpI, hc, hPrime⟩ := Finset.mem_filter.mp hp
      have xp : x < p := (Nat.floor_lt hx).mp (Finset.mem_Ioc.mp hpI).1
      have zp : z < p := by exact_mod_cast hzx.trans_lt xp
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hpI,hc⟩, ?_⟩
      apply Nat.Coprime.symm
      apply hPrime.coprime_iff_not_dvd.mpr
      intro hpP
      have hx' := Nat.mem_primeFactors.mpr ⟨hPrime,hpP,s.prodPrimes_ne_zero⟩
      change p ∈ (sieveProduct z q).primeFactors at hx'
      rw [sieveProduct_primes] at hx'
      exact zp.not_ge (mem_sievePrimes.mp hx').2.1
    have hs : s.siftedSum = ((s.support.filter (fun p => s.prodPrimes.Coprime p)).card : ℝ) := by
      simp [siftedSum, s, intervalSieve]
    rw [hs]
    exact_mod_cast Finset.card_le_card sub
  have upper := count.trans (optimal_sieve s hz err)
  rw [← intervalMass x y q c z]
  exact upper

end Erdos473Selberg

end

section

namespace Erdos473Selberg

open Finset Nat

noncomputable def reciprocalHom : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm]

/-- A finite sum of reciprocals of positive integers supported on the primes of k. -/
lemma sum_reciprocals_smooth {k : ℕ} (hk : k ≠ 0) (A : Finset ℕ)
    (hA : ∀ m ∈ A, m ∈ Nat.factoredNumbers k.primeFactors) :
    (∑ m ∈ A, (m : ℝ)⁻¹) ≤ (k : ℝ)/k.totient := by
  have hprime {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have ev := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f:=reciprocalHom) hprime k.primeFactors).2
  let E := Nat.factoredNumbers k.primeFactors
  let f : {m // m ∈ A} → E := fun m => ⟨m.val,hA m.val m.prop⟩
  have inj : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun v : E => v.val) h)
  have hsum : (∑ m ∈ A, (m:ℝ)⁻¹) = ∑ m ∈ A.attach.image f, reciprocalHom m.val := by
    rw [Finset.sum_image (fun _ _ _ _ h => inj h)]
    exact (Finset.sum_attach _ _).symm
  rw [hsum]
  apply (ev.summable.sum_le_tsum _ (fun _ _ => by change 0 ≤ (_:ℝ)⁻¹; positivity)).trans
  rw [ev.tsum_eq]
  have hf : k.primeFactors.filter Nat.Prime = k.primeFactors :=
    Finset.filter_eq_self.mpr fun _ h => Nat.prime_of_mem_primeFactors h
  rw [hf]
  change ∏ p ∈ k.primeFactors, (1 - (p:ℝ)⁻¹)⁻¹ ≤ _
  rw [Finset.prod_inv_distrib]
  have ht : (k.totient : ℝ) = k * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (fun a : ℚ => (a : ℝ)) (Nat.totient_eq_mul_prod_factors k)
  rw [ht]
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  rw [div_mul_eq_div_div,div_self hk',one_div]

theorem harmonic_le_divisorMass {q z : ℕ} (hq : 0 < q) :
    (harmonic z : ℝ) ≤ (q : ℝ)/q.totient * divisorMass q z := by
  classical
  let I := Finset.Icc 1 z
  let P := sieveProduct z q
  let D := I.filter (fun d => Squarefree d ∧ d.Coprime q)
  let F (n : ℕ) := n.gcd P
  have npos {n : ℕ} (hn : n ∈ I) : 0 < n := (Finset.mem_Icc.mp hn).1
  have dm {n : ℕ} (hn : n ∈ I) : F n ∈ D := by
    have hd := Nat.gcd_dvd_right n P
    have hp : 0 < F n := Nat.gcd_pos_of_pos_left _ (npos hn)
    have hz : F n ≤ z := (Nat.le_of_dvd (npos hn) (Nat.gcd_dvd_left n P)).trans (Finset.mem_Icc.mp hn).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp,hz⟩,(sieveProduct_divides_iff hz).mp hd⟩
  have fiber (d : ℕ) (hd : d ∈ D) :
      (∑ n ∈ I with F n = d, (n:ℝ)⁻¹) ≤ (q:ℝ)/q.totient * (d.totient:ℝ)⁻¹ := by
    let T := I.filter (fun n => F n = d)
    let f (n : ℕ) := n/d
    have info (n : ℕ) (hn : n ∈ T) : n ∈ I ∧ F n = d := Finset.mem_filter.mp hn
    have fac (n : ℕ) (hn : n ∈ T) : f n * d = n := by
      obtain ⟨_,hh⟩ := info n hn
      exact Nat.div_mul_cancel (hh ▸ Nat.gcd_dvd_left n P)
    have inj : Set.InjOn f ↑T := by
      intro n hn m hm h
      exact (fac n hn).symm.trans ((congrArg (· * d) h).trans (fac m hm))
    have smooth (m : ℕ) (hm : m ∈ T.image f) : m ∈ Nat.factoredNumbers (q*d).primeFactors := by
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
      have hnI := (info n hn).1
      have hd0 := (Finset.mem_filter.mp hd).2.1.ne_zero
      have hmq : q*d ≠ 0 := Nat.mul_ne_zero hq.ne' hd0
      have hfd : f n ∣ n := ⟨d,(fac n hn).symm⟩
      refine Nat.mem_factoredNumbers_of_primeFactors_subset ?_ ?_
      · exact ne_zero_of_dvd_ne_zero (npos hnI).ne' hfd
      · intro p hp
        have hpr := Nat.prime_of_mem_primeFactors hp
        have hpn := (Nat.dvd_of_mem_primeFactors hp).trans hfd
        apply Nat.mem_primeFactors.mpr
        refine ⟨hpr,?_,hmq⟩
        by_cases hpq : p ∣ q
        · exact dvd_mul_of_dvd_left hpq _
        · have hpz : p ≤ z := (Nat.le_of_dvd (npos hnI) hpn).trans (Finset.mem_Icc.mp hnI).2
          have hpp : p ∈ P.primeFactors := by
            rw [show P = sieveProduct z q from rfl,sieveProduct_primes]
            exact mem_sievePrimes.mpr ⟨hpr,hpz,hpq⟩
          have hpd : p ∣ d := (info n hn).2 ▸ Nat.dvd_gcd hpn (Nat.dvd_of_mem_primeFactors hpp)
          exact dvd_mul_of_dvd_right hpd _
    have hd0 := (Finset.mem_filter.mp hd).2.1.ne_zero
    have dto := (Finset.mem_filter.mp hd).2.2
    have ht := sum_reciprocals_smooth (Nat.mul_ne_zero hq.ne' hd0) (T.image f) smooth
    calc _ = (d : ℝ)⁻¹ * ∑ m ∈ T.image f, (m:ℝ)⁻¹ := by
                rw [Finset.mul_sum, Finset.sum_image inj]
                apply Finset.sum_congr rfl
                intro n hn
                nth_rw 1 [←fac n hn]
                simp
         _ ≤ (d : ℝ)⁻¹ * ((q*d : ℕ):ℝ)/(q*d).totient := by
                rw [mul_div_assoc]
                exact mul_le_mul_of_nonneg_left ht (by positivity)
         _ = _ := by
                rw [Nat.totient_mul dto.symm,Nat.cast_mul,Nat.cast_mul]
                have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd0
                field_simp
  calc (harmonic z : ℝ) = ∑ n ∈ I, (n:ℝ)⁻¹ := by simp [I,harmonic_eq_sum_Icc]
       _ = ∑ d ∈ D, ∑ n ∈ I with F n = d, (n:ℝ)⁻¹ :=
              (Finset.sum_fiberwise_of_maps_to (fun _ hn => dm hn) _).symm
       _ ≤ ∑ d ∈ D, (q:ℝ)/q.totient * (d.totient:ℝ)⁻¹ := Finset.sum_le_sum fiber
       _ = _ := by rw [← Finset.mul_sum]; rfl

theorem log_le_divisorMass {q : ℕ} (hq : 0 < q) (z : ℕ) :
    Real.log (z+1 : ℕ) ≤ (q:ℝ)/q.totient * divisorMass q z :=
  (log_add_one_le_harmonic z).trans (harmonic_le_divisorMass hq)

/-- An upper bound for primes in one residue class in an interval, with an arbitrary
real sieve cutoff between one and the left endpoint. -/
theorem interval_prime_upper {x y t : ℝ} {q : ℕ} (c : ℕ) (hx : 0 ≤ x)
    (hxy : x ≤ y) (htx : t ≤ x) (hq : 0 < q) (ht : 1 < t) :
    (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.ModEq q p c ∧ p.Prime)).card : ℝ)
      ≤ (y-x) / ((q.totient : ℝ) * Real.log t) + t^2 := by
  let z := ⌊t⌋₊
  have hz : 1 ≤ z := Nat.le_floor (by simpa using ht.le)
  have hzt : (z : ℝ) ≤ t := Nat.floor_le (by linarith)
  have H := progression_sieve c hx hxy (hzt.trans htx) hq hz
  apply H.trans
  apply _root_.add_le_add
  · have htq : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    have hlog : 0 < Real.log t := Real.log_pos ht
    have hl : Real.log t ≤ (q:ℝ)/q.totient * divisorMass q z := by
      apply le_trans _ (log_le_divisorMass hq z)
      apply Real.log_le_log (by linarith)
      simp only [Nat.cast_add,Nat.cast_one]
      exact (Nat.lt_floor_add_one t).le
    have hl' : (q.totient:ℝ) * Real.log t ≤ q * divisorMass q z := by
      rw [div_mul_eq_mul_div,le_div_iff₀ htq] at hl
      linarith
    have hleft : 0 < (q.totient:ℝ) * Real.log t := mul_pos htq hlog
    rw [div_div]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hleft hl'
  · gcongr


end Erdos473Selberg

end

section

/- Explicit constants for the real cutoff in the interval Selberg sieve. -/
namespace Erdos473Selberg

open Real

/-- An explicit constant for every interval whose logarithmic length exceeds βH. -/
lemma envelope {H S β u C : ℝ} (hH : 45 ≤ H) (hβ : 0 < β) (hS : β*H ≤ S)
    (hu : 1 ≤ u) (hlog : log (45*β) ≤ u)
    (hpos : 0 < 1/2 - u/(45*β))
    (hcap : 1/((1/2-u/(45*β))*β) + 1/(45*β^2) ≤ C) :
    0 < S/2-log S ∧ 1/(S/2-log S) + 1/S^2 ≤ C/H := by
  let D := 1/2-u/(45*β)
  have hD : 0 < D := hpos
  have hH' : 0 < H := by linarith
  have h0 : 0 < 45*β := by positivity
  have hbase : 45*β ≤ S := (by nlinarith [mul_le_mul_of_nonneg_left hH hβ.le] : 45*β ≤ β*H).trans hS
  have hS' := h0.trans_le hbase
  have hlogS := log_le_sub_one_of_pos (div_pos hS' h0)
  rw [log_div hS'.ne' h0.ne'] at hlogS
  have hR : 1 ≤ S/(45*β) := (one_le_div h0).mpr hbase
  have hlin : log S ≤ u/(45*β)*S := by
    have hr := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hR)
    rw [show u/(45*β)*S = u*(S/(45*β)) by ring]
    nlinarith
  have hden : (D*β)*H ≤ S/2-log S := by
    have v := mul_le_mul_of_nonneg_left hS hD.le
    dsimp [D] at v ⊢
    linarith
  have hden' := (mul_pos (mul_pos hD hβ) hH').trans_le hden
  refine ⟨hden',?_⟩
  have hsquare : (45*β^2)*H ≤ S^2 := by
    have v := mul_le_mul hS hbase h0.le hS'.le
    nlinarith
  calc 1/(S/2-log S)+1/S^2 ≤ 1/((D*β)*H) + 1/((45*β^2)*H) :=
         _root_.add_le_add (one_div_le_one_div_of_le (by positivity) hden)
           (one_div_le_one_div_of_le (by positivity) hsquare)
       _ = (1/(D*β)+1/(45*β^2))/H := by ring
       _ ≤ _ := div_le_div_of_nonneg_right hcap hH'.le

lemma envelope_small {H S : ℝ} (hH : 45 ≤ H) :
    (0.70*H ≤ S → 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ 3.72/H) ∧
    (0.75*H ≤ S → 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ 3.42/H) := by
  constructor
  · intro hS
    exact envelope (β:=0.70) (u:=3.46) hH (by norm_num) hS (by norm_num)
      ((Erdos473LogBounds.log_constant (c:=45*0.70) (δ:=0.46) 3 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
      (by norm_num) (by norm_num)
  · intro hS
    exact envelope (β:=0.75) (u:=3.53) hH (by norm_num) hS (by norm_num)
      ((Erdos473LogBounds.log_constant (c:=45*0.75) (δ:=0.53) 3 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
      (by norm_num) (by norm_num)

lemma envelope_medium {H S : ℝ} (hH : 45 ≤ H) :
    (0.55*H ≤ S → 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ 5.1/H) ∧
    (0.60*H ≤ S → 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ 4.7/H) := by
  constructor
  · intro hS
    exact envelope (β:=0.55) (u:=3.22) hH (by norm_num) hS (by norm_num)
      ((Erdos473LogBounds.log_constant (c:=45*0.55) (δ:=0.22) 3 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
      (by norm_num) (by norm_num)
  · intro hS
    exact envelope (β:=0.60) (u:=3.30) hH (by norm_num) hS (by norm_num)
      ((Erdos473LogBounds.log_constant (c:=45*0.60) (δ:=0.30) 3 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
      (by norm_num) (by norm_num)

lemma envelope_root {H S : ℝ} (hH : 45 ≤ H) :
    (0.30*H ≤ S → 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ 11.3/H) ∧
    (0.36*H ≤ S → 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ 8.9/H) := by
  constructor
  · intro hS
    exact envelope (β:=0.30) (u:=2.61) hH (by norm_num) hS (by norm_num)
      ((Erdos473LogBounds.log_constant (c:=45*0.30) (δ:=0.61) 2 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
      (by norm_num) (by norm_num)
  · intro hS
    exact envelope (β:=0.36) (u:=2.79) hH (by norm_num) hS (by norm_num)
      ((Erdos473LogBounds.log_constant (c:=45*0.36) (δ:=0.79) 2 (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num))
      (by norm_num) (by norm_num)

theorem interval_prime_envelope {x y H C : ℝ} {q : ℕ} (c : ℕ) (hxy : x < y) (hq : 0 < q)
    (hroot : sqrt ((y-x)/q) ≤ x) (hs : 1 ≤ log ((y-x)/q))
    (h : let S := log ((y-x)/q); 0 < S/2-log S ∧ 1/(S/2-log S)+1/S^2 ≤ C/H) :
    (((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.ModEq q p c ∧ p.Prime)).card : ℝ)
      ≤ C * (y-x) / ((q.totient:ℝ)*H) := by
  let N := (y-x)/q
  let S := log N
  let t := sqrt N/S
  have hN : 0 < N := div_pos (sub_pos.mpr hxy) (by exact_mod_cast hq)
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one hs
  have ht : 0 < t := div_pos (sqrt_pos.mpr hN) hS
  have ident : log t = S/2-log S := by
    rw [show t = sqrt N/S from rfl,log_div (sqrt_pos.mpr hN).ne' hS.ne',log_sqrt hN.le]
  have ht1 : 1 < t := (log_pos_iff ht.le).mp (by rw [ident]; exact h.1)
  have hx := (sqrt_nonneg N).trans hroot
  have tx : t ≤ x := (div_le_self (sqrt_nonneg N) hs).trans hroot
  have sieve := interval_prime_upper c hx hxy.le tx hq ht1
  have sqt : t^2 = N/S^2 := by rw [show t = sqrt N/S from rfl,div_pow,sq_sqrt hN.le]
  have htot : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hq' : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hN' : N ≤ (y-x)/q.totient := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy.le) htot hq'
  apply sieve.trans
  rw [ident,sqt]
  calc _ ≤ (y-x)/((q.totient:ℝ)*(S/2-log S)) + ((y-x)/q.totient)/S^2 :=
            _root_.add_le_add le_rfl (div_le_div_of_nonneg_right hN' (sq_nonneg _))
       _ = ((y-x)/q.totient) * (1/(S/2-log S)+1/S^2) := by rw [← div_div]; ring
       _ ≤ ((y-x)/q.totient) * (C/H) := mul_le_mul_of_nonneg_left h.2 (by positivity)
       _ = _ := by ring

lemma root_of_window {n x y : ℝ} {q : ℕ} (hn : 0 < n) (hH : 45 ≤ log n)
    (hx : n-0.11*(n/log n) ≤ x) (hy : y ≤ n+0.105*(n/log n))
    (hxy : x ≤ y) (hq : 0 < q) : sqrt ((y-x)/q) ≤ x := by
  have hp : 1 ≤ log n := by linarith
  have hL := div_le_self hn.le hp
  have hx' : n/2 ≤ x := by linarith
  have hn4 : 4 ≤ n := by linarith [log_le_sub_one_of_pos hn]
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hu : (y-x)/q ≤ n := (div_le_self (sub_nonneg.mpr hxy) hq').trans (by linarith)
  have hs : sqrt n ≤ n/2 := (sqrt_le_iff).mpr ⟨by positivity, by nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hn4)]⟩
  exact (sqrt_le_sqrt hu).trans (hs.trans hx')

end Erdos473Selberg

end

section

/- A dense set of ordinary primes contains an oriented three-prime pattern.
If it has no such pattern, partition by distance from its largest element
into dyadic annuli. The occupied part of each annulus is short. -/

namespace Erdos473TripleSupply

open Real Finset

def Pattern (A : Finset ℕ) (D : ℕ) : Prop :=
  ∃ p∈A, ∃ q∈A, ∃ r∈A, p<q ∧ q<r ∧ D≤q-p ∧ q-p≤r-q

def near (A : Finset ℕ) (r t : ℕ) := A.filter (fun p => r-p<t)

/-- In the absence of a pattern, every annulus costs at most one short cell. -/
theorem annuli {A : Finset ℕ} {r D : ℕ} (hr : r∈A) (top : ∀ p∈A, p≤r)
    (hd : 0<D) (none : ¬ Pattern A D) {U : ℝ}
    (cap : ∀ S ⊆ A, (∀ p∈S, ∀ q∈S, q-p<D) → (S.card:ℝ)≤U) (j : ℕ) :
    ((near A r (2^j*D)).card:ℝ) ≤ (j+1)*U := by
  have sub (t : ℕ) : near A r t ⊆ A := filter_subset _ _
  induction j with
  | zero =>
    simp only [pow_zero,one_mul,Nat.cast_zero,zero_add]
    apply cap _ (sub _)
    intro p hp q hq
    have hl := (mem_filter.mp hp).2
    have hq' := top q (sub _ hq)
    omega
  | succ j ih =>
    let t := 2^j*D
    let inner := near A r t
    let outer := near A r (2*t) \ inner
    have hcap : (outer.card:ℝ) ≤ U := by
      apply cap _ (sdiff_subset.trans (sub _))
      intro p hp q hq
      obtain ⟨hpa,hpi⟩ := mem_sdiff.mp hp
      obtain ⟨hqa,hqi⟩ := mem_sdiff.mp hq
      obtain ⟨pA,pr⟩ := mem_filter.mp hpa
      obtain ⟨qA,qr⟩ := mem_filter.mp hqa
      have pbelow := top p pA
      have qbelow := top q qA
      have gap : t≤r-q := by
        by_contra! hh
        exact hqi (mem_filter.mpr ⟨qA,hh⟩)
      by_contra! dist
      exact none ⟨p,pA,q,qA,r,hr,by omega,by omega,dist,by omega⟩
    have inc : inner ⊆ near A r (2*t) := by
      intro p hp
      obtain ⟨a,b⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨a,by omega⟩
    have eq : outer.card + inner.card = (near A r (2*t)).card :=
      card_sdiff_add_card_eq_card inc
    have eq' : (outer.card:ℝ) + inner.card = (near A r (2*t)).card := by exact_mod_cast eq
    have ih' : (inner.card:ℝ) ≤ (j+1)*U := ih
    rw [pow_succ,show 2^j*2*D=2*t by dsimp [t]; ring,Nat.cast_succ]
    linarith

theorem pattern_of_density {A : Finset ℕ} (ne : A.Nonempty) {D j : ℕ} (hd : 0<D)
    (diam : ∀ p∈A, ∀ q∈A, q-p<2^j*D) {U : ℝ}
    (cap : ∀ S ⊆ A, (∀ p∈S, ∀ q∈S, q-p<D) → (S.card:ℝ)≤U)
    (dense : (j+1)*U < (A.card:ℝ)) : Pattern A D := by
  by_contra no
  let r := A.max' ne
  have hr : r∈A := A.max'_mem ne
  have e : near A r (2^j*D)=A := filter_true_of_mem (fun p hp => diam p hp r hr)
  have h := annuli hr (fun p hp => A.le_max' p hp) hd no cap j
  rw [e] at h
  linarith

theorem dense_piece {A : Finset ℕ} {L len w : ℕ} (hw : 0<w)
    (inside : ∀ p∈A, L≤p ∧ p≤L+len) (T : ℝ)
    (dense : ((len/w+1:ℕ):ℝ)*T < A.card) :
    ∃ S ⊆ A, T<(S.card:ℝ) ∧ ∀ p∈S, ∀ q∈S, q-p<w := by
  let idx := fun p : ℕ => (p-L)/w
  let I := range (len/w+1)
  let fiber := fun i : ℕ => A.filter (fun p => idx p=i)
  have eq : A.card = ∑ i∈I, (fiber i).card := by
    apply card_eq_sum_card_fiberwise
    intro p hp
    apply mem_range.mpr
    have h := Nat.div_le_div_right (c:=w) (show p-L≤len by have := inside p hp; omega)
    exact Nat.lt_succ_of_le h
  by_contra! no
  have cap (i : ℕ) (hi : i∈I) : ((fiber i).card:ℝ)≤T := by
    by_contra! big
    obtain ⟨p,hp,q,hq,hfar⟩ := no (fiber i) (filter_subset _ _) big
    obtain ⟨pA,pi⟩ := mem_filter.mp hp
    obtain ⟨qA,qi⟩ := mem_filter.mp hq
    have pL := (inside p pA).1
    have qL := (inside q qA).1
    change (p-L)/w=i at pi
    change (q-L)/w=i at qi
    have ep := Nat.div_add_mod (p-L) w
    have eq' := Nat.div_add_mod (q-L) w
    rw [pi] at ep
    rw [qi] at eq'
    have := Nat.mod_lt (q-L) hw
    omega
  have sum := sum_le_sum cap
  have e : (A.card:ℝ)=∑ i∈I, ((fiber i).card:ℝ) := by exact_mod_cast eq
  rw [←e] at sum
  simpa [I] using (lt_irrefl _ (dense.trans_le' (by simpa [I] using sum)))

/-- Any set of primes contained in a short cell obeys the checked interval sieve. -/
lemma short_capacity {S : Finset ℕ} {D n : ℕ} (hd : 0<D) {z : ℝ} (hz : 1<z)
    (hzn : z≤n) (primes : ∀ p∈S, n<p ∧ p.Prime) (short : ∀ p∈S, ∀ q∈S, q-p<D) :
    (S.card:ℝ) ≤ D/log z+z^2 := by
  have logp := log_pos hz
  by_cases ne : S.Nonempty
  · let p := S.min' ne
    let a := p-1
    have hp : p∈S := S.min'_mem ne
    have hu := primes p hp
    have base : n≤a := by dsimp [a]; omega
    have sub : S ⊆ (Ioc a (a+D)).filter Nat.Prime := by
      intro q hq
      have above := S.min'_le q hq
      have dd := short p hp q hq
      change p≤q at above
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by dsimp [a]; omega,by dsimp [a]; omega⟩,(primes q hq).2⟩
    have e := Erdos473Selberg.interval_prime_upper (x:=(a:ℝ)) (y:=((a+D:ℕ):ℝ))
      (q:=1) 0 (by positivity) (by exact_mod_cast Nat.le_add_right a D)
      (hzn.trans (by exact_mod_cast base)) (by decide) hz
    have hsub : (S.card:ℝ) ≤ (((Ioc a (a+D)).filter Nat.Prime).card:ℝ) := by exact_mod_cast card_le_card sub
    apply hsub.trans
    simp only [Nat.floor_natCast] at e
    simpa [Nat.ModEq,Nat.mod_one] using e
  · rw [not_nonempty_iff_eq_empty.mp ne]
    simp only [card_empty,Nat.cast_zero]
    positivity

end Erdos473TripleSupply

end

section

/- A small cluster of suitable primes inside the upper part of an ordinary
dyadic interval. Only the total number of primes enters the lower bound. -/

namespace Erdos473MatchingBand

open Real Finset Erdos473TripleConstants Erdos473TripleSupply

abbrev base := 90953418231753380142

def CountInput : Prop := ∀ N : ℕ, base≤N →
  0.0127*(N:ℝ)/log N < (((Ioc (33*N/34) N).filter Nat.Prime).card:ℝ)

def left (n : ℕ) := 33*(2*n)/34
noncomputable def reserve (H : ℝ) := 8*⌈C*H^3⌉₊+8
noncomputable def band (n : ℕ) (H : ℝ) :=
  (Ioc (left n) (2*n-reserve H)).filter Nat.Prime

lemma retained (count : CountInput) {n : ℕ} (hn : base≤n) {H : ℝ} (hH : H=log (2*(n:ℝ))) :
    0.02538*(n:ℝ)/H < ((band n H).card:ℝ) := by
  have nr : (90953418231753380142:ℝ)≤n := by exact_mod_cast hn
  obtain ⟨hh,hpow⟩ := power_budget nr hH
  have hp : 0<H := by linarith
  let A := (Ioc (left n) (2*n)).filter Nat.Prime
  have full : 0.0254*(n:ℝ)/H < (A.card:ℝ) := by
    have z := count (2*n) (by omega)
    push_cast at z
    simpa only [A,left,hH,show (0.0254:ℝ)*n=0.0127*(2*n) by ring] using z
  let B := band n H
  have sub : A ⊆ B ∪ Ioc (2*n-reserve H) (2*n) := by
    intro p hp
    obtain ⟨⟨low,hi⟩,pr⟩ := (show (left n<p ∧ p≤2*n) ∧ p.Prime by simpa [A] using hp)
    by_cases u : p≤2*n-reserve H
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨low,u⟩,pr⟩)
    · exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hi⟩)
  have t := (card_le_card sub).trans (card_union_le _ _)
  rw [Nat.card_Ioc] at t
  have lost : (A.card:ℝ) ≤ B.card + (reserve H:ℝ) := by
    exact_mod_cast (show A.card ≤ B.card + reserve H by omega)
  have cap : (reserve H:ℝ) ≤ 9*C*H^3 := by
    have ceil := Nat.ceil_lt_add_one (show 0≤C*H^3 by dsimp [C]; positivity)
    simp only [reserve,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have hcube : 1≤H^3 := one_le_pow₀ (by linarith : 1 ≤ H)
    dsimp [C] at *
    linarith
  apply (div_lt_iff₀ hp).mpr
  have raw := (div_lt_iff₀ hp).mp full
  have e₁ := mul_le_mul_of_nonneg_right lost hp.le
  have e₂ := mul_le_mul_of_nonneg_right cap hp.le
  change 0.02538*(n:ℝ)<(B.card:ℝ)*H
  dsimp [C] at *
  nlinarith only [raw,e₁,e₂,hpow,nr]

lemma prime_bucket (count : CountInput) {n : ℕ} (hn : base≤n) {H : ℝ} (hH : H=log (2*(n:ℝ))) :
    ∃ S ⊆ band n H, 0.56*C*H^2<(S.card:ℝ) ∧ ∀ p∈S, ∀ q∈S, q-p<width H := by
  have nr : (90953418231753380142:ℝ)≤n := by exact_mod_cast hn
  obtain ⟨hh,hpow⟩ := power_budget nr hH
  have hp : 0<H := by linarith
  have hc1 : 1≤H^3 := one_le_pow₀ (by linarith : 1 ≤ H)
  have hc4 : H^3≤H^4 := by nlinarith only [mul_nonneg (show 0≤H^3 by positivity) (show 0≤H-1 by linarith)]
  have wlo : 1.309*C*H^3 ≤ (width H:ℝ) := by
    have h := Nat.lt_floor_add_one (1.31*C*H^3)
    change _ ≤ (⌊1.31*C*H^3⌋₊:ℝ)
    dsimp [C] at *; linarith
  have wp : 0<width H := by exact_mod_cast (show 0<(width H:ℝ) by dsimp [C] at wlo; linarith)
  let len := 2*n-left n
  have hl : 17*len ≤ n+17 := by dsimp [len,left]; omega
  have hl' : 17*(len:ℝ)≤n+17 := by exact_mod_cast hl
  have inside (p : ℕ) (h : p∈band n H) : left n≤p ∧ p≤left n+len := by
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp (mem_filter.mp h).1
    dsimp [len]; omega
  apply dense_piece wp inside
  let bins := len/width H+1
  have nb : bins*width H≤len+width H := by
    dsimp [bins]; rw [Nat.add_mul,one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have nb' : (bins:ℝ)*width H≤len+width H := by exact_mod_cast nb
  have wb := Nat.floor_le (show 0≤1.31*C*H^3 by dsimp [C]; positivity)
  change (width H:ℝ)≤_ at wb
  have wd : 0.56*C*H^2*H ≤ 0.428*(width H:ℝ) := by
    dsimp [C] at *; nlinarith only [wlo,hc1]
  have prod := mul_le_mul_of_nonneg_left wd (Nat.cast_nonneg (α:=ℝ) bins)
  have bound : (bins:ℝ)*(0.56*C*H^2)*H < 0.02538*(n:ℝ) := by
    dsimp [C] at *
    nlinarith only [prod,nb',hl',wb,hpow,hc4,nr]
  exact ((lt_div_iff₀ hp).mpr bound).trans (retained count hn hH)

/-- A small gap for expansion and a three-prime repair with a large first
gap both lie in the same buffered interval. -/
theorem supply (count : CountInput) {n : ℕ} (hn : base≤n) {H : ℝ} (hH : H=log (2*(n:ℝ))) :
    (∃ p∈band n H, ∃ q∈band n H, p<q ∧ (q:ℝ)-p≤10*H) ∧
    ∃ p∈band n H, ∃ q∈band n H, ∃ r∈band n H, p<q ∧ q<r ∧
      0.368*C*H^2≤(q:ℝ)-p ∧ q-p≤r-q ∧ r-p<width H := by
  have nr : (90953418231753380142:ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hh,hpow⟩ := power_budget nr hH
  obtain ⟨S,sub,many,diam⟩ := prime_bucket count hn hH
  have pos : 0<H := by linarith
  have sqp : 0<H^2 := by positivity
  have ne : S.Nonempty := card_pos.mp (by
    exact_mod_cast (show 0<(S.card:ℝ) by dsimp [C] at many; linarith))
  have wle : (width H:ℝ) ≤ 1.31*C*H^3 := Nat.floor_le (by dsimp [C]; positivity)
  constructor
  · let L := S.min' ne
    let w := ⌈9*H⌉₊
    have lo : 9*H≤(w:ℝ) := Nat.le_ceil _
    have hi : (w:ℝ)<9*H+1 := Nat.ceil_lt_add_one (by linarith)
    have wp : 0<w := by exact_mod_cast (show 0<(w:ℝ) by linarith)
    have inside (p : ℕ) (hp : p∈S) : L≤p ∧ p≤L+width H := by
      have dl := diam L (S.min'_mem ne) p hp
      exact ⟨S.min'_le p hp,by omega⟩
    have hsmall : (((width H)/w+1:ℕ):ℝ) * 1 < (S.card:ℝ) := by
      let b := (width H)/w
      have eq : (b:ℝ)*w ≤ width H := by exact_mod_cast Nat.div_mul_le_self (width H) w
      have v := mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg (α:=ℝ) b)
      change ((b+1:ℕ):ℝ)*1 < _
      push_cast
      have big : 1≤H^2 := one_le_pow₀ (by linarith : 1 ≤ H)
      have z := mul_lt_mul_of_pos_right many pos
      dsimp [C] at *
      by_contra! small
      have bad := mul_le_mul_of_nonneg_right small pos.le
      nlinarith only [eq,v,wle,z,bad,hh,big,mul_nonneg (sub_nonneg.mpr big) pos.le]
    obtain ⟨V,vS,cnt,dia⟩ := dense_piece wp inside 1 hsmall
    obtain ⟨p,hp,q,hq,neq⟩ := one_lt_card.mp (by exact_mod_cast (show (1:ℝ)<V.card from cnt))
    have order {p q : ℕ} (hp : p∈V) (hq : q∈V) (lt : p<q) :
        (q:ℝ)-p≤10*H := by
      have e : ((q-p:ℕ):ℝ)<w := by exact_mod_cast dia p hp q hq
      rw [Nat.cast_sub lt.le] at e
      linarith
    rcases lt_or_gt_of_ne neq with lt|lt
    · exact ⟨p,sub (vS hp),q,sub (vS hq),lt,order hp hq lt⟩
    · exact ⟨q,sub (vS hq),p,sub (vS hp),lt,order hq hp lt⟩
  · obtain ⟨j,z,zp,zu,sz,cost⟩ := scales hh
    have dlo : 0.368*C*H^2≤(gap H:ℝ) := Nat.le_ceil _
    have dp : 0<gap H := by exact_mod_cast (show 0<(gap H:ℝ) by dsimp [C] at dlo; linarith)
    have zle : z≤n := by
      have he : H≤H^4 := by nlinarith only [mul_nonneg (show 0≤H^3-1 from sub_nonneg.mpr
        (one_le_pow₀ (by linarith : 1≤H))) pos.le]
      linarith
    have cap (V : Finset ℕ) (vS : V⊆S) (span : ∀ p∈V, ∀ q∈V, q-p<gap H) :
        (V.card:ℝ) ≤ (gap H:ℝ)/log z+z^2 := by
      apply short_capacity dp zp zle _ span
      intro p hp
      have e := mem_filter.mp (sub (vS hp))
      have l := (mem_Ioc.mp e.1).1
      dsimp [left] at l
      exact ⟨by omega,e.2⟩
    obtain ⟨p,hp,q,hq,r,hr,pq,qr,large,sl⟩ := pattern_of_density ne dp
      (fun p hp q hq => (diam p hp q hq).trans sz) cap
      (by dsimp [C] at many cost ⊢; linarith)
    have ge : (gap H:ℝ)≤((q-p:ℕ):ℝ) := by exact_mod_cast large
    rw [Nat.cast_sub pq.le] at ge
    exact ⟨p,sub hp,q,sub hq,r,sub hr,pq,qr,dlo.trans ge,sl,diam p hp r hr⟩

end Erdos473MatchingBand

end

section

/- Control of the cubic boundary size under a reflection-shell step. -/

namespace Erdos473MatchingScale

open Real Erdos473TripleConstants

lemma child_budget {n m : ℕ} {H : ℝ} (hn : 90953418231753380142 ≤ n)
    (hH : H = log (2*(n:ℝ))) (low : 16*n ≤ 17*m+17) :
    C*(H^3-0.183*H^2) ≤ C*(log (2*(m:ℝ)))^3 := by
  have nr : (90953418231753380142:ℝ) ≤ n := by exact_mod_cast hn
  have mr : 16*(n:ℝ) ≤ 17*m+17 := by exact_mod_cast low
  have hh := (power_budget nr hH).1
  have mp : 0 < (m:ℝ) := by linarith
  have hl := log_le_log (show 0 < 2*(n:ℝ) by linarith)
    (show 2*(n:ℝ) ≤ 1.0628*(2*(m:ℝ)) by linarith)
  rw [←hH,log_mul (by norm_num : (1.0628:ℝ) ≠ 0) (by positivity)] at hl
  have c : log (1.0628:ℝ) ≤ (0:ℕ)+0.061 :=
    Erdos473LogBounds.log_constant 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num at c
  have h := pow_le_pow_left₀ (show 0 ≤ H-0.061 by linarith)
    (show H-0.061 ≤ log (2*(m:ℝ)) by linarith) 3
  apply mul_le_mul_of_nonneg_left _ (by norm_num [C])
  nlinarith only [h,hh]

lemma grow_budget {k d : ℕ} {H : ℝ} (hh : 45 ≤ H)
    (hk : (k:ℝ) ≤ 0.99*C*H^3) (hd : (d:ℝ) ≤ 5*H) :
    ((k+d:ℕ):ℝ) ≤ C*(H^3-0.183*H^2) := by
  push_cast
  have h2 := mul_nonneg (sq_nonneg H) (show 0 ≤ H-40 by linarith)
  have h1 := mul_nonneg (show 0 ≤ H by linarith) (show 0 ≤ H-1 by linarith)
  dsimp [C] at *
  nlinarith only [hk,hd,h2,h1,hh]

lemma shrink_budget {k d : ℕ} {H : ℝ} (dk : d≤k) (hk : (k:ℝ) ≤ C*H^3)
    (hd : 0.368*C*H^2 ≤ 2*(d:ℝ)) :
    ((k-d:ℕ):ℝ) ≤ C*(H^3-0.183*H^2) := by
  rw [Nat.cast_sub dk]
  dsimp [C] at *
  nlinarith [sq_nonneg H]

lemma child_ratio {n m j : ℕ} {H : ℝ} (hh : 45≤H) (hn : 1000000000000*H^4 ≤ n)
    (low : 16*n ≤ 17*m+17) (hj : (j:ℝ) ≤ 2*C*H^3) :
    10000*j ≤ m := by
  have mr : 16*(n:ℝ) ≤ 17*m+17 := by exact_mod_cast low
  have h4 := mul_nonneg (show 0 ≤ H^3 by positivity) (show 0 ≤ H-1 by linarith)
  have h3 : 1≤H^3 := one_le_pow₀ (by linarith : 1 ≤ H)
  dsimp [C] at *
  exact_mod_cast (show 10000*(j:ℝ) ≤ m by nlinarith only [mr,hj,hn,h4,h3])

end Erdos473MatchingScale

end

section

/- The buffered prime cluster supplies the two operations of the boundary induction. -/

namespace Erdos473LargeMatching

open Real Erdos473TripleConstants Erdos473MatchingBand Erdos473MatchingScale
open Erdos473MatchingInduction

lemma odd_label {p n : ℕ} {H : ℝ} (hn : base ≤ n) (hp : p ∈ band n H) :
    p.Prime ∧ p%2 = 1 := by
  obtain ⟨hit,pr⟩ := Finset.mem_filter.mp hp
  have low := (Finset.mem_Ioc.mp hit).1
  dsimp [base] at hn
  dsimp [left] at low
  obtain ⟨a,ha⟩ := pr.odd_of_ne_two (by omega)
  exact ⟨pr,by omega⟩

lemma coordinates {p n : ℕ} {H : ℝ} (hn : base ≤ n) (hp : p ∈ band n H) :
    ∃ u t : ℕ, n=u+2*t ∧ p=n+u+1 ∧ 16*n ≤ 17*u+17 ∧
      u+8*⌈C*H^3⌉₊+8 ≤ n := by
  obtain ⟨hit,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp hit
  have odd := (odd_label hn hp).2
  dsimp [base] at hn
  dsimp [left] at lo
  dsimp [reserve] at hi
  refine ⟨p-n-1,(2*n+1-p)/2,?_,?_,?_,?_⟩ <;> omega

theorem big_step (count : CountInput) (n k : ℕ) (hn : base < n) (_ : 2 ≤ n)
    (bound : SizeBound C n k) (_ : 10000*k ≤ n) : BigStep C n k := by
  let H := log (2*(n:ℝ))
  have eqH : H=log (2*(n:ℝ)) := rfl
  have nr : (90953418231753380142:ℝ) ≤ n := by exact_mod_cast hn.le
  obtain ⟨hh,power⟩ := power_budget nr eqH
  have hk : (k:ℝ) ≤ C*H^3 := bound
  have cap : k ≤ ⌈C*H^3⌉₊ := by exact_mod_cast hk.trans (Nat.le_ceil _)
  have cube : 0 ≤ H^3 := by positivity
  have cp : 0 ≤ C*H^3 := by positivity
  have nbase : 90953418231753380142 ≤ n := hn.le
  obtain ⟨pair,triple⟩ := supply count hn.le eqH
  by_cases slack : (k:ℝ) ≤ 0.99*C*H^3
  · obtain ⟨p,hp,q,hq,pq,small⟩ := pair
    obtain ⟨u,t,nsize,pval,low,buf⟩ := coordinates hn.le hp
    obtain ⟨pp,op⟩ := odd_label hn.le hp
    obtain ⟨qp,oq⟩ := odd_label hn.le hq
    let d := (q-p)/2
    have qval : q=p+2*d := by dsimp [d]; omega
    have hd : 0<d := by omega
    have qr : (q:ℝ)=p+2*(d:ℝ) := by exact_mod_cast qval
    have ds : (d:ℝ) ≤ 5*H := by linarith
    have dc : (d:ℝ) ≤ C*H^3 := by
      have hv := mul_nonneg (show 0 ≤ H^2-1 from sub_nonneg.mpr
        (one_le_pow₀ (by linarith : 1≤H))) (show 0 ≤ H by linarith)
      dsimp [C] at *; nlinarith only [ds,hv,hh]
    have capd : d ≤ ⌈C*H^3⌉₊ := by exact_mod_cast dc.trans (Nat.le_ceil _)
    let m := u+2*k+2*d
    have lm : 16*n ≤ 17*m+17 := by dsimp [m]; omega
    have nextB := child_budget nbase eqH lm
    have bud := grow_budget hh slack ds
    have sz : ((k+d:ℕ):ℝ) ≤ 2*C*H^3 := by push_cast; linarith
    refine BigStep.grow u t d nsize hd (by omega) (by simpa [←pval] using pp)
      (by simpa [←pval,←qval] using qp) ?_
    exact ⟨by dsimp [m] at *; omega,by dsimp [m] at *; omega,
      bud.trans nextB,child_ratio hh power lm sz⟩
  · obtain ⟨p,hp,q,hq,r,hr,pq,qr,gap,order,w⟩ := triple
    obtain ⟨u,t,nsize,pval,low,buf⟩ := coordinates hn.le hp
    obtain ⟨pp,op⟩ := odd_label hn.le hp
    obtain ⟨qp,oq⟩ := odd_label hn.le hq
    obtain ⟨rp,orp⟩ := odd_label hn.le hr
    let d := (q-p)/2
    let e := (r-q)/2
    have qval : q=p+2*d := by dsimp [d]; omega
    have rval : r=q+2*e := by dsimp [e]; omega
    have hd : 0<d := by omega
    have de : d≤e := by omega
    have qr' : (q:ℝ) = p+2*(d:ℝ) := by exact_mod_cast qval
    have width_le : (width H:ℝ) ≤ 1.31*C*H^3 := Nat.floor_le (by positivity)
    have dist : 2*d+2*e < width H := by omega
    have dr : 2*(d:ℝ)+2*(e:ℝ) < width H := by exact_mod_cast dist
    have de' : (d:ℝ) ≤ e := by exact_mod_cast de
    have space : 2*d+e≤k := by
      have h : 2*(d:ℝ)+e ≤ k := by dsimp [C] at *; nlinarith only [slack,width_le,dr,de',cube]
      exact_mod_cast h
    let m := u+2*k
    have lm : 16*n ≤ 17*m+17 := by dsimp [m]; omega
    have bud := shrink_budget (show d≤k by omega) hk (by linarith : 0.368*C*H^2 ≤ 2*(d:ℝ))
    have sz : ((k-d:ℕ):ℝ) ≤ 2*C*H^3 := by
      rw [Nat.cast_sub (by omega : d≤k)]
      linarith [Nat.cast_nonneg (α:=ℝ) d]
    refine BigStep.shrink u t d e nsize hd (by omega) space de
      (by simpa [←pval] using pp) (by simpa [←pval,←qval] using qp)
      (by simpa [←pval,←qval,←rval] using rp) ?_
    exact ⟨by dsimp [m] at *; omega,by dsimp [m] at *; omega,
      bud.trans (child_budget nbase eqH lm),child_ratio hh power lm sz⟩

end Erdos473LargeMatching

end

section

/- A quantitative prime interval bound from a period-30 factorial ratio. -/
namespace Erdos473Chebyshev30

open Real Finset Chebyshev
open scoped ArithmeticFunction

noncomputable section

def logFac (n : ℕ) := log (n.factorial : ℝ)

lemma logFac_sum (n : ℕ) : logFac n = ∑ k ∈ Ioc 0 n, log (k:ℝ) := by
  induction n with
  | zero => simp [logFac]
  | succ n ih =>
    rw [sum_Ioc_succ_top (by omega : 0 ≤ n),←ih]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp only [logFac, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    rw [Real.log_mul (by positivity) hn,add_comm]

lemma logFac_weights (n M : ℕ) (hn : n≤M) :
    logFac n = ∑ d ∈ Ioc 0 M, (↑(n/d):ℝ)*Λ d := by
  rw [logFac_sum]
  calc
    _ = ∑ k ∈ Ioc 0 n, ∑ d ∈ Ioc 0 M, if d ∣ k then Λ d else 0 := by
      apply sum_congr rfl
      intro k hmem
      obtain ⟨hk,hkn⟩ := mem_Ioc.mp hmem
      rw [←sum_filter,←ArithmeticFunction.vonMangoldt_sum]
      congr 1
      ext d
      simp only [Nat.mem_divisors,Finset.mem_filter,Finset.mem_Ioc]
      constructor
      · intro h
        exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hk,(Nat.le_of_dvd hk h.1).trans (hkn.trans hn)⟩,h.1⟩
      · rintro ⟨_,hd⟩
        exact ⟨hd,hk.ne'⟩
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [←sum_filter,sum_const,Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]

def kernel (j : ℕ) : ℝ :=
  logFac (30*j) - logFac (15*j) - logFac (10*j) - logFac (6*j) + logFac j

lemma step_weights (v : ℕ) :
    v/2+v/3+v/5 ≤ v+v/30 ∧ v+v/30 ≤ v/2+v/3+v/5+1 := by
  omega

lemma quotient_swap (j d v f : ℕ) (h : f*v=30) :
    (v*j)/d = (30*j/d)/f := by
  have hf : 0 < f := by
    by_contra! hl
    have hz : f=0 := by omega
    rw [hz] at h
    simp at h
  rw [Nat.div_right_comm (30*j) d f, ←h,Nat.mul_assoc, Nat.mul_div_cancel_left _ hf]

lemma kernel_expand (j : ℕ) :
    kernel j = ∑ d ∈ Ioc 0 (30*j), ((↑(30*j/d):ℝ) - ↑(30*j/d/2) -
      ↑(30*j/d/3) - ↑(30*j/d/5) + ↑(30*j/d/30))*Λ d := by
  unfold kernel
  rw [logFac_weights (30*j) (30*j) le_rfl, logFac_weights (15*j) (30*j) (by omega),
    logFac_weights (10*j) (30*j) (by omega),logFac_weights (6*j) (30*j) (by omega),
    logFac_weights j (30*j) (by omega)]
  rw [←sum_sub_distrib,←sum_sub_distrib,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [quotient_swap j d 15 2 (by decide),quotient_swap j d 10 3 (by decide),
    quotient_swap j d 6 5 (by decide), show j/d=30*j/d/30 by simpa using quotient_swap j d 1 30 (by decide)]
  ring

lemma psi_kernel (j : ℕ) :
    kernel j ≤ psi (30*j:ℕ) ∧ psi (30*j:ℕ) ≤ kernel j + psi (5*j:ℕ) := by
  rw [kernel_expand]
  simp only [psi, Nat.floor_natCast]
  let v (d : ℕ) : ℝ := ↑(30*j/d) - ↑(30*j/d/2) - ↑(30*j/d/3) - ↑(30*j/d/5) + ↑(30*j/d/30)
  have hbound (d : ℕ) : 0 ≤ v d ∧ v d ≤ 1 := by
    let t := 30*j/d
    have hl : (↑(t/2):ℝ)+↑(t/3)+↑(t/5) ≤ ↑t+↑(t/30) := by exact_mod_cast (step_weights t).1
    have hu : (↑t:ℝ)+↑(t/30) ≤ ↑(t/2)+↑(t/3)+↑(t/5)+1 := by exact_mod_cast (step_weights t).2
    change 0 ≤ (↑t:ℝ)-↑(t/2)-↑(t/3)-↑(t/5)+↑(t/30) ∧ _ ≤ 1
    change _ ∧ (↑t:ℝ)-↑(t/2)-↑(t/3)-↑(t/5)+↑(t/30) ≤ 1
    constructor <;> linarith
  have pos (d : ℕ) := ArithmeticFunction.vonMangoldt_nonneg (n:=d)
  have s : Ioc 0 (5*j) ⊆ Ioc 0 (30*j) := by intro d hd; simp only [mem_Ioc] at *; omega
  constructor
  · apply sum_le_sum; intro d _
    simpa using mul_le_mul_of_nonneg_right (hbound d).2 (pos d)
  · change _ ≤ (∑ d ∈ Ioc 0 (30*j),v d*Λ d) + _
    rw [←sub_le_iff_le_add,←sum_sdiff_eq_sub s]
    calc
      _ = ∑ d ∈ Ioc 0 (30*j) \ Ioc 0 (5*j), v d*Λ d := by
        apply sum_congr rfl
        intro d hd
        obtain ⟨ha,hb⟩ := mem_sdiff.mp hd
        obtain ⟨hdp,hdu⟩ := mem_Ioc.mp ha
        have hlo : 5*j<d := by simp only [mem_Ioc] at hb; omega
        have hv : 1 ≤ 30*j/d := (Nat.one_le_div_iff hdp).mpr hdu
        have hw : 30*j/d < 6 := (Nat.div_lt_iff_lt_mul hdp).mpr (by omega)
        have val : v d=1 := by
          dsimp [v]
          have : 30*j/d=1 ∨ 30*j/d=2 ∨ 30*j/d=3 ∨ 30*j/d=4 ∨ 30*j/d=5 := by omega
          rcases this with h|h|h|h|h <;> norm_num [h]
        simp [val]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (by intro d _ _; exact mul_nonneg (hbound d).1 (pos d))

def mainTerm (x : ℝ) := x*log x - x

lemma logFac_stirling (m : ℕ) (hm : 0 < m) :
    mainTerm m ≤ logFac m ∧ logFac m ≤ mainTerm m + 1 + log (2*m) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hlow := Stirling.log_stirlingSeq_bounded_by_constant j
  have hu := Stirling.log_stirlingSeq'_antitone (show 0 ≤ j by omega)
  change log (Stirling.stirlingSeq (j+1)) ≤ log (Stirling.stirlingSeq 1) at hu
  rw [Stirling.stirlingSeq_one, Real.log_div (exp_pos _).ne' (by positivity),log_exp,
    log_sqrt (by norm_num)] at hu
  have hf := Stirling.log_stirlingSeq_formula (j+1)
  rw [log_div (by positivity) (exp_pos _).ne',log_exp] at hf
  have ht : 0 ≤ log (2*((j+1:ℕ):ℝ)) := log_nonneg (by push_cast; nlinarith)
  simp only [mainTerm,logFac]
  constructor <;> nlinarith [log_two_lt_d9, log_two_gt_d9]

abbrev slope : ℝ := (14*log 2+9*log 3+5*log 5)/30

lemma slope_bounds : 0.9212 < slope ∧ slope < 0.9214 := by
  unfold slope
  constructor <;> linarith [log_two_gt_d9,log_two_lt_d9,log_three_gt_d9,log_three_lt_d9,
    log_five_gt_d9,log_five_lt_d9]

lemma main_kernel (j : ℕ) (hj : 0 < j) :
    mainTerm (30*j) - mainTerm (15*j) - mainTerm (10*j) - mainTerm (6*j) + mainTerm j =
      slope*(30*j) := by
  have hj' : (j:ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have h30 : log (30:ℝ) = log 2 + log 3 + log 5 := by
    rw [show (30:ℝ) = 2*3*5 by norm_num,log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]
  have h15 : log (15:ℝ) = log 3+log 5 := by
    rw [show (15:ℝ)=3*5 by norm_num,log_mul (by norm_num) (by norm_num)]
  have h10 : log (10:ℝ) = log 2+log 5 := by
    rw [show (10:ℝ)=2*5 by norm_num,log_mul (by norm_num) (by norm_num)]
  have h6 : log (6:ℝ) = log 2+log 3 := by
    rw [show (6:ℝ)=2*3 by norm_num,log_mul (by norm_num) (by norm_num)]
  unfold mainTerm slope
  rw [log_mul (by norm_num : (30:ℝ)≠0) hj', log_mul (by norm_num : (15:ℝ)≠0) hj',
    log_mul (by norm_num : (10:ℝ)≠0) hj', log_mul (by norm_num : (6:ℝ)≠0) hj',h30,h15,h10,h6]
  ring

lemma kernel_est (j : ℕ) (hj : 10000000000 ≤ j) :
    0.921*(30*j:ℝ) ≤ kernel j ∧ kernel j ≤ 0.922*(30*j:ℝ) := by
  have jp : 0 < j := by omega
  have jreal : (10000000000:ℝ) ≤ j := by exact_mod_cast hj
  have hb (k : ℕ) (hk : 1 ≤ k) (hk30 : k ≤ 30) :
      mainTerm ((k:ℝ)*j) ≤ logFac (k*j) ∧
        logFac (k*j) ≤ mainTerm ((k:ℝ)*j) + 1 + log (60*j) := by
    have h := logFac_stirling (k*j) (Nat.mul_pos hk jp)
    push_cast at h
    have hk' : (k:ℝ) ≤ 30 := by exact_mod_cast hk30
    have hprod := mul_le_mul_of_nonneg_right hk' (show (0:ℝ) ≤ j by positivity)
    have hl : log (2*((k:ℝ)*j)) ≤ log (60*j) := log_le_log (by positivity) (by linarith)
    exact ⟨h.1,h.2.trans (by linarith)⟩
  have h30 := hb 30 (by decide) (by decide)
  have h15 := hb 15 (by decide) (by decide)
  have h10 := hb 10 (by decide) (by decide)
  have h6 := hb 6 (by decide) (by decide)
  have h1 := hb 1 (by decide) (by decide)
  norm_num only [Nat.cast_ofNat,Nat.cast_one,one_mul] at h30 h15 h10 h6 h1
  have hlog : log (60*(j:ℝ)) ≤ 0.001*(j:ℝ) := by
    have hsp : 0 < sqrt (60*(j:ℝ)) := sqrt_pos.mpr (by positivity)
    have h := log_le_sub_one_of_pos hsp
    rw [log_sqrt (by positivity)] at h
    have eq := sq_sqrt (by positivity : 0 ≤ 60*(j:ℝ))
    have hr : sqrt (60*(j:ℝ)) ≤ 0.0005*j := by
      apply (Real.sqrt_le_iff).2
      refine ⟨by positivity,?_⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr jreal) (by positivity : (0:ℝ)≤j)]
    linarith
  have hlow := mul_le_mul_of_nonneg_right slope_bounds.1.le (by positivity : (0:ℝ) ≤ 30*j)
  have hhigh := mul_le_mul_of_nonneg_right slope_bounds.2.le (by positivity : (0:ℝ) ≤ 30*j)
  unfold kernel
  constructor <;> linarith [main_kernel j jp]

lemma sqrt_error {x : ℝ} (hx : 10000000000 ≤ x) :
    2*sqrt x*log x ≤ 0.001*x := by
  have xp : 0 < x := by linarith
  have hr : 100000 ≤ sqrt x := le_sqrt_of_sq_le (by norm_num; exact hx)
  have h10 : log (10:ℝ) < 2.4 := by
    rw [show (10:ℝ)=2*5 by norm_num,log_mul (by norm_num) (by norm_num)]
    linarith [log_two_lt_d9,log_five_lt_d9]
  have hbase : log (100000:ℝ) ≤ 12 := by
    rw [show (100000:ℝ) = 10^5 by norm_num,log_pow]
    norm_num
    linarith
  have hl := log_le_sub_one_of_pos (div_pos (sqrt_pos.mpr xp) (by norm_num : (0:ℝ)<100000))
  rw [log_div (sqrt_pos.mpr xp).ne' (by norm_num),log_sqrt xp.le] at hl
  have hlog' : log x ≤ 0.0004*sqrt x := by linarith
  have t := mul_le_mul_of_nonneg_left hlog' (sqrt_nonneg x)
  nlinarith [sq_sqrt xp.le]

lemma psi_large_upper {x : ℝ} (hx : 10000000000 ≤ x) : psi x ≤ 1.4*x := by
  have h := psi_le (show 1 ≤ x by linarith)
  have h4 : log (4:ℝ) < 1.399 := by
    rw [show (4:ℝ)=2*2 by norm_num,log_mul (by norm_num) (by norm_num)]
    linarith [log_two_lt_d9]
  linarith [sqrt_error hx,mul_le_mul_of_nonneg_right h4.le (show 0 ≤ x by linarith)]

lemma psi_coarse (k : ℕ) (hk : 10000000000 ≤ k) :
    psi (6480*k:ℕ) ≤ 1.108 * (6480*(k:ℝ)) := by
  have s₁ := (psi_kernel (216*k)).2
  have s₂ := (psi_kernel (36*k)).2
  have s₃ := (psi_kernel (6*k)).2
  have e₁ := (kernel_est (216*k) (by omega)).2
  have e₂ := (kernel_est (36*k) (by omega)).2
  have e₃ := (kernel_est (6*k) (by omega)).2
  have e₄ := psi_large_upper (x:=(30*k:ℕ)) (by exact_mod_cast (show 10000000000 ≤ 30*k by omega))
  norm_num only [←Nat.mul_assoc] at s₁ s₂ s₃
  norm_num at s₁ s₂ s₃ e₁ e₂ e₃ e₄ ⊢
  linarith

/-- Uniform unconditional bounds at real arguments, including endpoint rounding. -/
theorem ordinary_bounds (x : ℝ) (hx : 100000000000000 ≤ x) :
    0.9209*x ≤ psi x ∧ psi x ≤ 1.1081*x ∧ 0.9199*x ≤ theta x ∧ theta x ≤ 1.1081*x := by
  let n := ⌊x⌋₊
  have hn : 100000000000000 ≤ n := (Nat.le_floor_iff (by linarith)).mpr (by norm_num;exact hx)
  have hlo : (n:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hhi : x < (n:ℝ)+1 := Nat.lt_floor_add_one _
  let k := n/6480+1
  let j := n/30
  have hk : 10000000000 ≤ k := by dsimp [k]; omega
  have hj : 10000000000 ≤ j := by dsimp [j]; omega
  have hku : 6480*k ≤ n+6480 := by dsimp [k]; omega
  have hkl : n+1 ≤ 6480*k := by dsimp [k]; omega
  have hju : 30*j ≤ n := by dsimp [j]; omega
  have hjl : n ≤ 30*j+30 := by dsimp [j]; omega
  have hku' : (6480:ℝ)*k ≤ n+6480 := by exact_mod_cast hku
  have hkl' : (n:ℝ)+1 ≤ 6480*k := by exact_mod_cast hkl
  have hju' : (30:ℝ)*j ≤ n := by exact_mod_cast hju
  have hjl' : (n:ℝ) ≤ 30*j+30 := by exact_mod_cast hjl
  have hu := psi_coarse k hk
  have hl := (psi_kernel j).1
  push_cast at hu hl
  have hp : psi x ≤ 1.1081*x := by
    linarith [psi_mono (le_trans hhi.le hkl')]
  have hl' : 0.9209*x ≤ psi x := by
    linarith [(kernel_est j hj).1,psi_mono (le_trans hju' hlo)]
  have diff := psi_sub_theta_le (show 1 ≤ x by linarith)
  exact ⟨hl',hp,by linarith [sqrt_error (show 10000000000 ≤ x by linarith)],(theta_le_psi x).trans hp⟩

/-- The prime mass in (n,1.21 n] exceeds .004 n throughout the uncertified range. -/
theorem theta_short (n : ℕ) (hn : 90953418231753380142 ≤ n) :
    0.004*(n:ℝ) < theta (1.21*n) - theta (n:ℝ) := by
  let k := n/6480+1
  let y := 121*n/3000
  have hk : 1000000000000000 ≤ k := by dsimp [k]; omega
  have hy : 10000000000 ≤ y := by dsimp [y]; omega
  have h1 : n ≤ 6480*k := by dsimp [k]; omega
  have h2 : 6480*k ≤ n+6480 := by dsimp [k]; omega
  have h3 : 3000*y ≤ 121*n := by dsimp [y]; omega
  have h4 : 121*n ≤ 3000*y+3000 := by dsimp [y]; omega
  have h3' : (30*y:ℝ) ≤ 1.21*(n:ℝ) := by
    have ht : (3000:ℝ)*y ≤ 121*n := by exact_mod_cast h3
    linarith
  have h4' : 1.21*(n:ℝ) ≤ 30*y+30 := by
    have ht : 121*(n:ℝ) ≤ 3000*y+3000 := by exact_mod_cast h4
    linarith
  have h2' : (6480:ℝ)*k ≤ n+6480 := by exact_mod_cast h2
  have hn' : (90953418231753380142:ℝ) ≤ n := by exact_mod_cast hn
  have h30y : (10000000000000000:ℝ) ≤ 30*y := by linarith
  have hθ₁ := theta_le_psi (n:ℝ)
  have hψ₁ := psi_mono (show (n:ℝ) ≤ (6480*k:ℕ) by exact_mod_cast h1)
  have hψ₂ := psi_coarse k (by omega)
  have hlo := (kernel_est y hy).1
  have hψ₃ := (psi_kernel y).1
  have hθ₂ := psi_sub_theta_le (x:=30*y) (by linarith : (1:ℝ) ≤ 30*y)
  have hθ₃ := theta_mono h3'
  push_cast at hψ₁ hψ₂ hψ₃
  linarith [sqrt_error (show 10000000000 ≤ 30*(y:ℝ) by linarith)]

/-- Every short interval in the certified range contains quantitatively many primes. -/
theorem prime_count (n : ℕ) (hn : 90953418231753380142 ≤ n) :
    0.004*(n:ℝ)/log (1.21*n) <
      (((Ioc n ⌊1.21*(n:ℝ)⌋₊).filter Nat.Prime).card : ℝ) := by
  let y := 1.21*(n:ℝ)
  have hn' : (90953418231753380142:ℝ) ≤ n := by exact_mod_cast hn
  have hny : (n:ℝ) ≤ y := by dsimp [y]; linarith
  have hnly : n ≤ ⌊y⌋₊ := (Nat.le_floor_iff (by dsimp [y]; positivity)).mpr hny
  let P := (Ioc n ⌊y⌋₊).filter Nat.Prime
  have sub : Nat.primesLE n ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hnly,(Nat.mem_primesLE.mp hp).2⟩
  have he : P = Nat.primesLE ⌊y⌋₊ \ Nat.primesLE n := by
    ext v
    simp only [P,mem_filter,mem_Ioc,mem_sdiff,Nat.mem_primesLE]
    grind
  have mass : theta y - theta (n:ℝ) = ∑ p ∈ P, log p := by
    rw [he,sum_sdiff_eq_sub sub,theta_eq_sum_primesLE,theta_eq_sum_primesLE_log]
  have upper : (∑ p ∈ P, log p) ≤ P.card*log y := by
    calc
      _ ≤ ∑ _p ∈ P,log y := by
        apply sum_le_sum
        intro v hv
        have hm := mem_filter.mp hv
        apply log_le_log (by exact_mod_cast hm.2.pos)
        exact (Nat.le_floor_iff (by dsimp [y]; positivity)).mp (mem_Ioc.mp hm.1).2
      _ = _ := by simp
  apply (div_lt_iff₀ (log_pos (by linarith : 1<y))).mpr
  exact (theta_short n hn).trans_le (mass ▸ upper)

end
end Erdos473Chebyshev30

end

section

/- Estimates for finite factorial ratios whose linear logarithmic terms cancel. -/
namespace Erdos473Balanced
open Finset Real Erdos473Chebyshev30
open scoped ArithmeticFunction
noncomputable section

def factorialSum (S : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) := ∑ j ∈ S,b j*logFac (N/j)
def floorSum (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) := ∑ j ∈ S,b j*(k/j:ℕ)
def growth (S : Finset ℕ) (b : ℕ → ℝ) := -(∑ j ∈ S,b j*log j/j)
def height (S : Finset ℕ) (b : ℕ → ℝ) := ∑ j ∈ S, |b j|

lemma factorial_expansion (S : Finset ℕ) (b : ℕ → ℝ) (N : ℕ) :
    factorialSum S b N=∑ d ∈ Ioc 0 N,floorSum S b (N/d)*ArithmeticFunction.vonMangoldt d := by
  unfold factorialSum floorSum
  simp only [sum_mul]
  calc
    _ = ∑ j ∈ S,∑ d ∈ Ioc 0 N,b j*((↑(N/j/d):ℝ)*ArithmeticFunction.vonMangoldt d) := by
      apply sum_congr rfl;intro j _
      rw [logFac_weights (N/j) N (Nat.div_le_self ..),mul_sum]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl;intro d _
      apply sum_congr rfl;intro j _
      rw [Nat.div_right_comm N j d,mul_assoc]

lemma logfac_floor {y : ℝ} (hy : 1≤y) : |logFac ⌊y⌋₊-mainTerm y| ≤ 2+log (2*y) := by
  let k := ⌊y⌋₊
  have k1 : 1≤k := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hy)
  have hp : (0:ℝ)<k := by exact_mod_cast k1
  have yp : 0<y := by linarith
  have lo : (k:ℝ)≤y := Nat.floor_le yp.le
  have hi : y<(k:ℝ)+1 := Nat.lt_floor_add_one y
  have lg := log_le_sub_one_of_pos (div_pos yp hp)
  rw [log_div yp.ne' hp.ne'] at lg
  have km := mul_le_mul_of_nonneg_right lg hp.le
  simp only [sub_mul,div_mul_cancel₀ _ hp.ne',one_mul] at km
  have lm := log_le_log hp lo
  have ly := log_nonneg hy
  have d := sub_nonneg.mpr lo
  have a := mul_nonneg d ly
  have e := mul_le_mul_of_nonneg_right (by linarith : y-(k:ℝ) ≤ 1) ly
  have st := logFac_stirling k k1
  have l2 := log_le_log (by positivity : (0:ℝ) < 2*k) (show 2*(k:ℝ) ≤ 2*y by linarith)
  have ly2 := log_le_log yp (show y≤2*y by linarith)
  change |logFac k-mainTerm y| ≤ _
  unfold mainTerm at st ⊢
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right lm hp.le]

lemma factorial_estimate {S : Finset ℕ} {b : ℕ → ℝ} {N : ℕ} (hp : 0<N)
    (hS : ∀ j∈S,0<j ∧ j≤N) (balance : ∑ j∈S,b j/j=0) :
    |factorialSum S b N - growth S b * N| ≤ height S b*(2+log (2*N)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hp
  have ideals : (∑ j∈S,b j*mainTerm ((N:ℝ)/j)) = growth S b*N := by
    calc
      _ = ∑ j∈S,(((N:ℝ)*log N-N)*(b j/j) - (N:ℝ)*(b j*log j/j)) := by
        apply sum_congr rfl;intro j hj
        have jp : (0:ℝ)<j := by exact_mod_cast (hS j hj).1
        simp only [mainTerm,log_div hn.ne' jp.ne']; ring
      _ = _ := by rw [sum_sub_distrib,←mul_sum,←mul_sum,balance];unfold growth;ring
  rw [←ideals,factorialSum,←sum_sub_distrib]
  calc
    _ ≤ ∑ j∈S,|b j * logFac (N/j) - b j*mainTerm ((N:ℝ)/j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈S,|b j| *(2+log (2*N)) := by
      apply sum_le_sum;intro j hj
      obtain ⟨jp,ju⟩ := hS j hj
      have jp' : (0:ℝ)<j := by exact_mod_cast jp
      have j1 : (1:ℝ)≤j := by exact_mod_cast jp
      have hdiv : (1:ℝ)≤(N:ℝ)/j := (le_div_iff₀ jp').mpr (by simpa using (show (j:ℝ)≤N by exact_mod_cast ju))
      have ub : (N:ℝ)/j ≤ N := div_le_self hn.le j1
      have l := logfac_floor hdiv
      rw [Nat.floor_div_natCast,Nat.floor_natCast] at l
      rw [←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (l.trans (by linarith [log_le_log (by positivity : 0<2*((N:ℝ)/j)) (show 2*((N:ℝ)/j)≤2*N by linarith)])) (abs_nonneg _)
    _ = _ := by rw [height,sum_mul]

lemma floorSum_gap (S : Finset ℕ) (b : ℕ → ℝ) (balance : ∑ j∈S,b j/j=0)
    (hs : ∀ j∈S,0<j) (u v : ℕ) :
    |floorSum S b u-floorSum S b v| ≤ height S b := by
  have zero (n : ℕ) : (∑ j∈S,b j*((n:ℝ)/j))=0 := by
    calc
      _ = (n:ℝ)*∑ j∈S,b j/j := by rw [mul_sum];apply sum_congr rfl;intro j _;ring
      _ = _ := by rw [balance,mul_zero]
  have move (n : ℕ) : floorSum S b n =
      ∑ j∈S,b j*((n/j:ℕ)-(n:ℝ)/j) := by
    simp_rw [mul_sub,sum_sub_distrib,zero,sub_zero,floorSum]
  rw [move,move,←sum_sub_distrib]
  calc
    _ ≤ ∑ j∈S,|b j*((u/j:ℕ)-(u:ℝ)/j)-b j*((v/j:ℕ)-(v:ℝ)/j)| := abs_sum_le_sum_abs _ _
    _ ≤ height S b := by
      apply sum_le_sum;intro j hj
      have jp : (0:ℝ)<j := by exact_mod_cast hs j hj
      have rem (n : ℕ) : (n/j:ℕ) ≤ (n:ℝ)/j ∧ (n:ℝ)/j < (n/j:ℕ)+1 := by
        have eq : ⌊(n:ℝ)/j⌋₊=n/j := by rw [Nat.floor_div_natCast,Nat.floor_natCast]
        rw [←eq]
        exact ⟨Nat.floor_le (by positivity),Nat.lt_floor_add_one _⟩
      rw [←mul_sub,abs_mul]
      apply mul_le_of_le_one_right (abs_nonneg _)
      obtain ⟨lu,uu⟩ := rem u
      obtain ⟨lv,uv⟩ := rem v
      exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma short_interval {S : Finset ℕ} {b : ℕ → ℝ} {M N : ℕ} (hm : 0<M) (hmn : M≤N)
    (hS : ∀ j∈S,0<j ∧ j≤M) (balance : ∑ j∈S,b j/j=0) {E : ℝ}
    (error :
      ∑ d∈Ioc 0 N, (floorSum S b (N/d)-floorSum S b (M/d)-(if M<d then 1 else 0))*
        ArithmeticFunction.vonMangoldt d ≤ E) :
    growth S b*((N:ℝ)-M)-2*height S b*(2+log (2*N))-E ≤ Chebyshev.psi N-Chebyshev.psi M := by
  have r1 := factorial_estimate (lt_of_lt_of_le hm hmn) (fun j hj => ⟨(hS j hj).1,(hS j hj).2.trans hmn⟩) balance
  have r2 := factorial_estimate hm hS balance
  have hlog := log_le_log (by positivity : (0:ℝ)<2*M) (show (2:ℝ)*M ≤ 2*N by exact_mod_cast Nat.mul_le_mul_left 2 hmn)
  have wh := mul_le_mul_of_nonneg_left hlog (show 0≤height S b from sum_nonneg (fun j _ =>abs_nonneg (b j)))
  have sumM : (∑ d∈Ioc 0 N,floorSum S b (M/d)*ArithmeticFunction.vonMangoldt d)=factorialSum S b M := by
    rw [factorial_expansion]
    symm
    apply sum_subset_zero_on_sdiff (fun d hd => by simp only [mem_Ioc] at *;omega) ?_ (fun _ _ =>rfl)
    intro d hd
    obtain ⟨hi,ho⟩ := mem_sdiff.mp hd
    have md : M<d := by simp only [mem_Ioc] at hi ho;omega
    simp [Nat.div_eq_of_lt md,floorSum]
  have select : (∑ d∈Ioc 0 N, (if M<d then (1:ℝ) else 0)*ArithmeticFunction.vonMangoldt d) =
      Chebyshev.psi N-Chebyshev.psi M := by
    rw [Chebyshev.psi,Chebyshev.psi,Nat.floor_natCast,Nat.floor_natCast]
    have eq := sum_Ioc_consecutive (fun d => ArithmeticFunction.vonMangoldt d) (Nat.zero_le M) hmn
    simp only [ite_mul,one_mul,zero_mul,←sum_filter]
    have f : (Ioc 0 N).filter (M<·)=Ioc M N := by ext d;simp only [mem_Ioc,mem_filter];omega
    rw [f,←eq];ring
  simp only [sub_mul,sum_sub_distrib,←factorial_expansion,sumM,select] at error
  obtain ⟨low,_⟩ := abs_le.mp r1
  obtain ⟨_,high⟩ := abs_le.mp r2
  linarith

end
end Erdos473Balanced

end

section

/- A finite one-dimensional criterion for prime mass in the final thirty-fourth part. -/
namespace Erdos473OrdinaryCriterion

open Finset Real Chebyshev Erdos473Balanced Erdos473Chebyshev30 Erdos473Selberg
noncomputable section

def bottom (N : ℕ) := 33*N/34
def shell (N m : ℕ) := (Ioc (N/(m+1)) (N/m)).filter Nat.Prime
def extend (w : ℕ → ℝ) (v : ℕ) := w v+(if v=0 then 1 else 0)
def excess (w : ℕ → ℝ) (m : ℕ) :=
  max 0 (w m - min (extend w (33*m/34)) (extend w ((33*(m+1)-1)/34)))

lemma quotient_envelope (w : ℕ → ℝ) (N d : ℕ) (dp : 0<d) :
    w (N/d) - w (bottom N/d) - (if bottom N<d then 1 else 0) ≤ excess w (N/d) := by
  let m:=N/d
  let z:=33*N/d
  have eq : bottom N/d=z/34 := Nat.div_right_comm (33*N) 34 d
  have low : 33*m ≤ z := (Nat.le_div_iff_mul_le dp).mpr (by
    have := Nat.mul_le_mul_left 33 (Nat.div_mul_le_self N d);simpa [m,Nat.mul_assoc] using this)
  have high : z < 33*(m+1) := (Nat.div_lt_iff_lt_mul dp).mpr (by
    have := Nat.mul_lt_mul_of_pos_left (Nat.lt_mul_div_succ N dp) (show 0<33 by decide)
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,m] using this)
  have choices : z/34=33*m/34 ∨ z/34=(33*(m+1)-1)/34 := by omega
  have zero : bottom N<d ↔ bottom N/d=0 := (Nat.div_eq_zero_iff_lt dp).symm
  change w m - _ - _ ≤ excess w m
  have sub : min (extend w (33*m/34)) (extend w ((33*(m+1)-1)/34)) ≤ extend w (bottom N/d) := by
    rw [eq]
    rcases choices with hh|hh <;> rw [hh] <;> first | exact min_le_left _ _ | exact min_le_right _ _
  simp only [zero]
  unfold excess
  apply le_trans _ (le_max_right _ _)
  unfold extend at sub ⊢
  linarith

lemma shell_cost {N m : ℕ} {C : ℝ} (hmpos : 0 < m) (hnpos : 1 < N)
    (hc : (∑ p ∈ shell N m,log p) ≤ C*(N:ℝ)/(m*(m+1)))
    (w : ℕ → ℝ) :
    (∑ p ∈ shell N m,(w (N/p)-w (bottom N/p)-(if bottom N<p then 1 else 0))*log p)
      ≤ excess w m * (C*(N:ℝ)/(m*(m+1))) := by
  calc
    _ ≤ ∑ p ∈ shell N m,excess w m * log p := by
      apply sum_le_sum;intro p hp
      obtain ⟨hi,pr⟩ := mem_filter.mp hp
      obtain ⟨lo,up⟩ := mem_Ioc.mp hi
      have sl := (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp lo
      have su := (Nat.le_div_iff_mul_le hmpos).mp up
      have h₁ : m≤N/p := (Nat.le_div_iff_mul_le pr.pos).mpr (by simpa [Nat.mul_comm] using su)
      have h₂ : N/p < m+1 := (Nat.div_lt_iff_lt_mul pr.pos).mpr (by simpa [Nat.mul_comm] using sl)
      have eq : N/p=m := by omega
      have val := quotient_envelope w N p pr.pos
      rw [eq] at val
      exact mul_le_mul_of_nonneg_right (by simpa only [eq] using val) (log_nonneg (by exact_mod_cast pr.one_le))
    _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left hc (le_max_left _ _)

lemma strip_sum (f : ℕ → ℝ) (N T : ℕ) :
    (∑ d ∈ (Ioc (N/(T+1)) N).filter Nat.Prime,f d)=∑ m ∈ Icc 1 T, ∑ d ∈ shell N m,f d := by
  induction T with
  | zero => simp [shell]
  | succ T ih =>
    have hmono : N/(T+2) ≤ N/(T+1) := Nat.div_le_div_left (by omega) (by omega)
    have hs := sum_Ioc_consecutive (fun d => if d.Prime then f d else 0) hmono (Nat.div_le_self N (T+1))
    simp only [←sum_filter] at hs
    rw [show T+1+1=T+2 by omega,←hs,ih,sum_Icc_succ_top (a:=1) (by omega)]
    simp only [shell]; rw [add_comm]

lemma weighted_primes_split (x : ℕ) (f : ℕ → ℝ) (cap : ℝ) (cap_f : ∀ d, f d≤cap) :
    (∑ d∈Ioc 0 x,f d*ArithmeticFunction.vonMangoldt d) ≤
    ∑ d∈(Ioc 0 x).filter Nat.Prime,f d*log d + cap*(psi x-theta x) := by
  rw [psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,mul_sum,
      ←sum_filter_add_sum_filter_not (Ioc 0 x) Nat.Prime (fun d => f d*ArithmeticFunction.vonMangoldt d)]
  apply add_le_add
  · apply sum_le_sum;intro d hd;rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hd).2]
  · exact sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (cap_f d) ArithmeticFunction.vonMangoldt_nonneg

lemma residual_bound {S : Finset ℕ} {b : ℕ → ℝ} {N T : ℕ} (np : 1<N)
    (hs : ∀ j∈S,0<j) (balance : ∑ j∈S,b j/j=0) (C : ℕ → ℝ)
    (hc : ∀ m∈Icc 1 T, (∑ p ∈ shell N m,log p) ≤ C m*(N:ℝ)/(m*(m+1))) :
    (∑ d∈Ioc 0 N, (floorSum S b (N/d)-floorSum S b (bottom N/d)-(if bottom N<d then 1 else 0))*
      ArithmeticFunction.vonMangoldt d) ≤
    (N:ℝ)*(∑ m∈Icc 1 T,(excess (floorSum S b) m*C m)/(m*(m+1))) +
       height S b*(psi (N/(T+1):ℕ)+psi N-theta N) := by
  let w := floorSum S b
  let f (d : ℕ) := w (N/d)-w (bottom N/d)-(if bottom N<d then 1 else 0)
  have cf (d : ℕ) : f d≤height S b := by
    have fg := (le_abs_self _).trans (floorSum_gap S b balance hs (N/d) (bottom N/d))
    dsimp [f,w];split_ifs <;> linarith
  have pq := weighted_primes_split N f (height S b) cf
  have divu := Nat.div_le_self N (T+1)
  have sp := sum_Ioc_consecutive (fun d => if d.Prime then f d*log d else 0) (Nat.zero_le (N/(T+1))) divu
  simp only [←sum_filter] at sp
  rw [←sp,strip_sum] at pq
  have tail : (∑ d∈(Ioc 0 (N/(T+1))).filter Nat.Prime,f d*log d) ≤ height S b*psi (N/(T+1):ℕ) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (theta_le_psi _) (sum_nonneg fun j _ => abs_nonneg (b j)))
    rw [theta,Nat.floor_natCast,mul_sum]
    apply sum_le_sum;intro d hd
    exact mul_le_mul_of_nonneg_right (cf d) (log_nonneg (by exact_mod_cast (mem_filter.mp hd).2.one_le))
  have body : (∑ m∈Icc 1 T,∑ d∈shell N m,f d*log d) ≤
      (N:ℝ)*∑ m∈Icc 1 T,(excess w m*C m)/(m*(m+1)) := by
    rw [mul_sum]
    apply sum_le_sum;intro m hm
    exact (shell_cost (mem_Icc.mp hm).1 np (hc m hm) w).trans_eq (by ring)
  change (∑ d∈Ioc 0 N,f d*ArithmeticFunction.vonMangoldt d) ≤ (N:ℝ)*_+_
  dsimp only [w] at body
  linarith

end
end Erdos473OrdinaryCriterion

end

section

/- Quantitative error budget for the thirty-fourth-part prime-interval criterion. -/
namespace Erdos473OrdinaryReduction
open Finset Real Erdos473Balanced Erdos473OrdinaryCriterion Erdos473Chebyshev30 Chebyshev
noncomputable section

lemma powers {x : ℝ} (hx : 90953418231753380142≤x) : psi x-theta x ≤ 0.000000002*x := by
  have h : 1≤x := by linarith
  have rt : 9000000000≤ sqrt x := le_sqrt_of_sq_le (by linarith)
  have lx : log 4<2 := by rw [show (4:ℝ)=2^2 by norm_num,log_pow];norm_num only [Nat.cast_ofNat];linarith [log_two_lt_d9]
  have one (m : ℕ) (hm : 2≤ m) : psi (x^(1/(m:ℝ))) ≤ (log 4+4)*sqrt x := by
    grw [psi_le_const_mul_self (by positivity),sqrt_eq_rpow x];gcongr;norm_cast
  have up := psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := one 2 (by decide)
  have h3 := one 3 (by decide)
  have h5 := one 5 (by decide)
  simp only [Nat.cast_ofNat,one_div] at h2 h3 h5
  have cap := mul_le_mul_of_nonneg_right lx.le (sqrt_nonneg x)
  nlinarith [sq_sqrt (by linarith : 0≤x),mul_nonneg (sub_nonneg.mpr rt) (sqrt_nonneg x)]

theorem from_envelope {N : ℕ} (hn : 90953418231753380142 ≤ N) {S : Finset ℕ} {b : ℕ → ℝ}
    (hs : ∀ j∈S,0<j ∧ j≤900) (bal : ∑ j∈S,b j/j=0) (ght : 0.99≤growth S b)
    (height_cap : height S b≤412) {C : ℕ → ℝ}
    (hc : ∀ m∈Icc 1 125000,(∑ p∈shell N m,log p) ≤ C m*(N:ℝ)/(m*(m+1)))
    (budget : ∑ m∈Icc 1 125000,(excess (floorSum S b) m*C m)/(m*(m+1)) ≤ 0.0124) :
    0.0127*(N:ℝ)<theta N-theta (33*N/34:ℕ) := by
  have hn' : (90953418231753380142:ℝ) ≤ N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have err := residual_bound (by omega : 1<N) (fun j hj => (hs j hj).1) bal C hc
  have hm : 900≤bottom N := by unfold bottom;omega
  have hu : bottom N≤N := by unfold bottom;omega
  have base := short_interval (by omega : 0<bottom N) hu (fun j hj => ⟨(hs j hj).1,(hs j hj).2.trans hm⟩) bal err
  have body := mul_le_mul_of_nonneg_left budget np.le
  have htail : (100000000000000:ℝ) ≤ (N/(125000+1):ℕ) := by exact_mod_cast (show 100000000000000 ≤ N/(125000+1) by omega)
  have tail := (ordinary_bounds (N/(125000+1):ℕ) htail).2.1
  have div : (N/(125000+1):ℕ)*(125001:ℝ) ≤ N := by exact_mod_cast (Nat.div_mul_le_self N 125001)
  have pwr := powers hn'
  have mid := theta_le_psi (bottom N:ℕ)
  have nonnegQ := theta_le_psi (N:ℝ)
  have whole := psi_nonneg (N/(125000+1):ℕ)
  have ce := mul_le_mul_of_nonneg_right height_cap (show 0≤psi (N/(125000+1):ℕ)+psi N-theta N by linarith)
  have rel : ((bottom N:ℕ):ℝ)*34≤33*N := by unfold bottom;exact_mod_cast Nat.div_mul_le_self (33*N) 34
  have gap := mul_le_mul_of_nonneg_right ght (show 0≤(N:ℝ)-bottom N from sub_nonneg.mpr (by exact_mod_cast hu))
  have lg := log_nonneg (show 1≤(N:ℝ) by linarith)
  have l2 := log_mul (by norm_num : (2:ℝ)≠0) np.ne'
  have hh := mul_le_mul_of_nonneg_right height_cap (show 0≤2+log (2*N) by rw [l2];linarith [log_two_gt_d9])
  have rt : (9000000000:ℝ)≤ sqrt N := le_sqrt_of_sq_le (by linarith)
  have logerr := sqrt_error (by linarith : (10000000000:ℝ) ≤ N)
  have sm := mul_nonneg (sub_nonneg.mpr rt) lg
  change _ < theta N-theta (bottom N)
  rw [l2] at hh base
  norm_num only [Nat.reduceAdd] at body base tail ce whole div
  nlinarith [log_two_lt_d9]

theorem count_from_mass {N : ℕ} (hN : 1 < N) (mass : 0.0127*(N:ℝ)<theta N-theta (33*N/34:ℕ)) :
    0.0127*(N:ℝ)/log N < ((Ioc (33*N/34) N).filter Nat.Prime).card := by
  let M:=33*N/34
  have hm : M≤N := by dsimp [M];omega
  have eq := sum_Ioc_consecutive (fun d => if d.Prime then log (d:ℝ) else 0) (Nat.zero_le M) hm
  simp only [←sum_filter] at eq
  simp only [theta,Nat.floor_natCast] at mass
  change 0.0127*(N:ℝ)<_-(∑ d∈(Ioc 0 M).filter Nat.Prime,log d) at mass
  rw [←eq,add_sub_cancel_left] at mass
  apply (div_lt_iff₀ (log_pos (by exact_mod_cast hN))).mpr
  calc
    _ < _ := mass
    _ ≤ ∑ _d∈(Ioc M N).filter Nat.Prime,log N := by
      apply sum_le_sum;intro d hd
      obtain ⟨hi,hp⟩ := mem_filter.mp hd
      exact log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (mem_Ioc.mp hi).2)
    _ = _ := by simp [M]

end
end Erdos473OrdinaryReduction

end

section

/- Pack a complete divisor-sum table in integer digits and certify it by geometric series. -/
namespace Erdos473Pack
open Finset

def pack (B : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => f n * B^n+pack B f n

lemma pack_eq (B : ℕ) (f : ℕ → ℕ) (n : ℕ) : pack B f n=∑ i∈range n,f i*B^i := by
  induction n with
  | zero => simp [pack]
  | succ n ih => simp [pack,ih,sum_range_succ,add_comm]

lemma pack_lt {B : ℕ} (_hB : 1<B) {f : ℕ → ℕ} {n : ℕ} (h : ∀ i<n,f i<B) :
    pack B f n < B^n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    have up := h n (Nat.lt_succ_self _)
    have low := ih (fun i hi => h i (by omega))
    rw [pack,pow_succ]
    nlinarith [Nat.mul_le_mul_right (B^n) (show f n+1≤B by omega)]

lemma pack_digit {B : ℕ} (hB : 1<B) {f : ℕ → ℕ} {n i : ℕ} (hi : i<n) (hf : ∀ k<n,f k<B) :
    (pack B f n/B^i)%B=f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    have bp : 0<B := by omega
    by_cases eq : i=n
    · subst i
      rw [pack,Nat.mul_comm (f n) (B^n),Nat.mul_add_div (by positivity),Nat.div_eq_of_lt (pack_lt hB (fun j hj =>hf j (by omega))),
        Nat.add_zero,Nat.mod_eq_of_lt (hf n (by omega))]
    · have lt : i<n := by omega
      have hn : n=i+((n-i-1)+1) := by omega
      rw [pack,show f n*B^n=B^i*(f n * B^(n-i-1)*B) by rw [show B^n=B^i*B^((n-i-1)+1) by rw [←pow_add,←hn],pow_succ];ring,
        Nat.mul_add_div (by positivity),Nat.mul_add_mod_self_right,ih lt (fun j hj =>hf j (by omega))]

def series (B j n : ℕ) := (B^(j*n)-1)/(B^j-1)

lemma series_eq {B j : ℕ} (hb : 1<B) (hj : 0<j) (n : ℕ) :
    series B j n=∑ t∈range n,B^(j*t) := by
  unfold series
  have one : 1<B^j := Nat.one_lt_pow hj.ne' hb
  simpa only [←pow_mul] using (Nat.geomSum_eq one n).symm

lemma multiples {B j : ℕ} (hb : 1<B) (hj : 0<j) (T : ℕ) :
    (∑ n∈range (T+1),if 0<n ∧ j∣n then (B:ℤ)^n else 0) =
       (series B j (T/j+1):ℤ)-1 := by
  have eqS : ((Icc 1 (T/j)).image (fun i=>i*j)) =
      (range (T+1)).filter (fun n=>0<n ∧ j∣n) := by
    ext n
    simp only [mem_image,mem_Icc,mem_filter,mem_range]
    constructor
    · rintro ⟨k,⟨kl,ku⟩,rfl⟩
      exact ⟨by have := (Nat.le_div_iff_mul_le hj).mp ku;omega, Nat.mul_pos kl hj, dvd_mul_left _ _⟩
    · rintro ⟨le,np,dvd⟩
      exact ⟨n/j,⟨(Nat.one_le_div_iff hj).mpr (Nat.le_of_dvd np dvd),Nat.div_le_div_right (by omega)⟩,
        Nat.div_mul_cancel dvd⟩
  rw [←sum_filter,←eqS,sum_image (fun i _ i' _ h => Nat.eq_of_mul_eq_mul_right hj h),series_eq hb hj,
    Nat.cast_sum]
  simp only [Nat.cast_pow]
  have sp := sum_eq_sum_Ico_succ_bot (show (0:ℕ)<T/j+1 from Nat.succ_pos _) (fun i=> (B:ℤ)^(j*i))
  rw [←range_eq_Ico] at sp
  simp only [Nat.mul_zero,pow_zero,zero_add] at sp
  rw [sp]
  rw [show Icc 1 (T/j)=Ico 1 (T/j+1) by ext i; simp]
  simp only [Nat.mul_comm];ring

def explicit (B O K T : ℕ) (b : ℕ → ℤ) : ℤ :=
  O*(series B 1 (T+1):ℤ) + ∑ j∈Icc 1 K,b j*((series B j (T/j+1):ℤ)-1)

def delta (K : ℕ) (b : ℕ → ℤ) (n : ℕ) : ℤ :=
   ∑ j∈Icc 1 K,if 0<n ∧ j∣n then b j else 0

lemma explicit_eq {B : ℕ} (hb : 1<B) (O K T : ℕ) (b : ℕ → ℤ) :
    explicit B O K T b = ∑ n∈range (T+1),((O:ℤ)+delta K b n)*(B:ℤ)^n := by
  unfold explicit delta
  simp only [add_mul,sum_add_distrib,←mul_sum]
  congr 1
  · congr 1
    rw [series_eq hb (by decide),Nat.cast_sum]
    simp only [one_mul,Nat.cast_pow]
  · simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl;intro j hj
    rw [←multiples hb (mem_Icc.mp hj).1,mul_sum]
    apply sum_congr rfl;intro n _
    split_ifs <;> simp

end Erdos473Pack

end

section

/- Integer quantities in the quotient-shell certificate. -/
namespace Erdos473FloorScan
open Finset
def total (K : ℕ) (b : ℕ → ℤ) (m : ℕ) : ℤ := ∑ j∈Icc 1 K,b j*(m/j:ℕ)

def deci (m : ℕ) : ℕ :=
  let n := m*(m+1)
  if n≤1 then 25 else if n≤10 then 26 else if n≤100 then 28 else if n≤1000 then 30
  else if n≤10000 then 32 else if n≤100000 then 35 else if n≤1000000 then 38
  else if n≤10000000 then 42 else if n≤100000000 then 46 else if n≤1000000000 then 52
  else if n≤10000000000 then 59 else 68

def D : ℕ := 10000
def extend (m : ℕ) (e : ℤ) : ℤ := e + if m=0 then (D:ℤ) else 0
def row (m : ℕ) (a l r : ℤ) : ℕ := (a-min l r).toNat
def credit (m h : ℕ) : ℕ := h*deci m*100000000/(10*m*(m+1))+1
def point (K : ℕ) (b : ℕ → ℤ) (m : ℕ) : ℕ :=
  let u := 33*m/34
  let v := (33*(m+1)-1)/34
  credit m (row m (total K b m) (extend u (total K b u)) (extend v (total K b v)))


end Erdos473FloorScan

end

section

/- Coefficients of a balanced factorial ratio and its elementary estimates. -/
namespace Erdos473RatioCoefficients
open Finset Real Erdos473Balanced
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
def K : ℕ := 900
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
def D : ℕ := 10000
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
def packed : ℕ := 0x27114e209c4138827104e209c4138827104e209c4138827104e209c4138827104e209c4138827104e229c45387a7104e209c3d38827104e229c45388a7104e209c45388a7104e1e9c45387a7104e1e9c45387a7104e209c3d387a7104e229c41388a7104e209c4138827104e249c4938827104e1c9c4938827104e249c3938827104e249c3938727104e1c9c3938827104e1c9c3938727104e209c4938927104e249c3938927104e1c9c4138727104e269c35386a7104e269c4d38827104e269c4d386a7104e1a9c4d389a7104e269c35389a7104e1a9c35389a7104e209c35389a7104e269c4d38627104e209c4138627104e289c5138627104e289c5138827104e289c3138627104e189c5138627104e289c3138a27104e189c4138a27104e209c5538aa7104e169c2d385a7104e169c4138aa7104e209c55385a7104e2a9c2d38827104e169c4138827104e2a9c4138b27104e149c5938b27104e149c5938b27104e209c2938527104e2c9c5938527104e2c9c4138527104e2c9c5938b27104e2e9c5d38827104e129c5d38ba7104e2e9c4138ba7104e129c2538ba7104e2e9c25384a7104e209c5d384a7104e309c2138c27104e309c4138427104e109c6138427104e109c2138827104e309c2138427104e109c4138ca7104e0e9c1d383a7104e0e9c1d383a7104e209c1d38827104e329c6538ca7104e0e9c4138d27104e0c9c6938827104e349c6938827104e0c9c1938327104e0c9c6938327104e369c15382a7104e0a9c1538827104e209c15382a7104e0a9c1538da7104e0a9c4138227104e389c1138e27104e089c7138827104e389c1138e27104e389c4138227104e209c0d38ea7104e069c75381a7104e209c7538ea7104e069c75381a7104e3c9c4138127104e049c7938f27104e3c9c4138827104e049c7938f27104e3e9c7d380a7104e209c7d38fa7104e3e9c0538fa7104e209c0138827104e409c8138827104e009c4138027104e409c0139027104e429c8538827104e429c8537fa7104e209bfd390a7104dfc9c8939127104dfc9bf939127104e209bf939127104dfa9c41391a7104dfa9c41391a7104dfa9c8d391a7104df89c9138827104e209bf139227104e489bf139227104df69c9537da7104df69c9537da7104e209c9537d27104df49c9939327104e4c9c4137d27104e4c9c9939327104df29be538827104df29be5393a7104df29be537ca7104df29be537ca7104e4e9be538827104e209ca137c27104df09be139427104e509c4139427104e509be137c27104e529bdd38827104e529bdd37ba7104dee9ca537ba7104e529ca5394a7104e549ca937b27104e209ca937b27104dec9ca939527104dec9c41395a7104e209bd537aa7104e569bd538827104dea9bd5395a7104e209cb138827104de89cb137a27104e589bd137a27104e209c41379a7104de69cb5379a7104e209c41396a7104e5a9c4137927104e5c9cb938827104de49cb939727104e5e9cbd38827104e5e9bc5397a7104e5e9bc537827104e209cc137827104de09bc139827104dde9c41398a7104e629cc5398a7104e629cc938827104e649c4137727104e649bb938827104e669bb5376a7104dda9bb537627104e209cd137627104e209cd1375a7104dd69c41375a7104e6a9ba939b27104dd49cd938827104e6e9ba5374a7104dd29cdd39c27104dd09c4139c27104e709b9d38827104e209c41373a7104dcc9b9939d27104e769c41372a7104dca9b9537227104dc89cf138827104dc69b8d39ea7104e7c9cf939f27104e7e9cfd39fa7104dc29d013a027104e209d053a0a7104e829d093a127104dbc9c4136ea7104dba9d1136e27104db89b6d38827104e8a9b693a327104e8e9b6536ca7104db09d213a427104e209b5d36b27104e209b5538827104da89d31369a7104da69c413a727104e9e9d3d36827104ea29b3d38827104d9c9c41366a7104e209d513aaa7104eac9d593aba7104d909b21363a7104e209d6d3ada7104d889b0d3af27104d829c4138827104ec29d8938827104ec89d9538827104ece9ae135c27104ed49ad535a27104d669db9358a7104d5e9ab9356a7104e209c41354a7104ef29de93be27104efc9c4135027104f069e113c327104d309e2938827104d229a413c927104e209e5d343a7104d069a053d0a7104cf699e13d527104e209ec533627104cce9ef13dfa7104f8c9c41329a7104fa89c4138827104c769fa538827104c4e988930e27105020a05d3012710505ca0d941fa7104b9a970d2dba7104e20a24538827104abaa35d47627104a049c4126227105356a769207a7104706abe1388271042f6b64cfa0271034164e227102710
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
def z (j : ℕ) : ℤ :=
  if j ≤ K then (((packed >>> (15*j))%32768:ℕ):ℤ) - 10000 else 0
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
def coeff (j : ℕ) : ℤ := z j*j
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
noncomputable def b (j : ℕ) : ℝ := (coeff j:ℝ)/D
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
def S := Icc 1 K
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma coeff_zero (j : ℕ) (hj : K<j) : coeff j=0 := by simp [coeff,z,not_le.mpr hj]
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma balance_int : (∑ j∈S,z j)=0 := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma height_int : (∑ j∈S,|coeff j|) ≤ (412*10000:ℤ) := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma growth_int : 27^D*(∏ j∈S,j^(z j).toNat) ≤ 10^D*(∏ j∈S,j^(-z j).toNat) := by decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma b_div {j : ℕ} (hj : j∈S) : b j/j = (z j:ℝ)/D := by
  have jp : (0:ℝ)<j := by exact_mod_cast (mem_Icc.mp hj).1
  simp only [b,coeff,Int.cast_mul,Int.cast_natCast]
  field_simp
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma balance : ∑ j∈S,b j/j=0 := by
  calc
    _ = ∑ j∈S,(z j:ℝ)/D := sum_congr rfl fun _ hj => b_div hj
    _ = _ := by rw [←sum_div,←Int.cast_sum,balance_int];simp
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma height_le : height S b ≤ 412 := by
  have t : (∑ j∈S,|(coeff j:ℝ)|) ≤ 412*10000 := by
    exact_mod_cast height_int
  simp only [height,b,abs_div, abs_of_nonneg (Nat.cast_nonneg D : (0:ℝ)≤D),←sum_div]
  rw [D,Nat.cast_ofNat]
  linarith
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
lemma growth_ge : 0.99 ≤ growth S b := by
  have jp (j : ℕ) (hj : j∈S) : (0:ℝ)<j := by exact_mod_cast (mem_Icc.mp hj).1
  have posZ (f : ℕ → ℕ) : (0:ℝ)<∏ j∈S,(j:ℝ)^(f j) := prod_pos (fun j hj => pow_pos (jp j hj) _)
  have gr : (27:ℝ)^D*(∏ j∈S,(j:ℝ)^(z j).toNat) ≤ 10^D*(∏ j∈S,(j:ℝ)^(-z j).toNat) := by exact_mod_cast growth_int
  have lg := log_le_log (mul_pos (by positivity) (posZ _)) gr
  rw [log_mul (by positivity) (posZ _).ne',log_mul (by positivity) (posZ _).ne',log_pow,log_pow,
    log_prod (fun j hj => (pow_pos (jp j hj) _).ne'),log_prod (fun j hj => (pow_pos (jp j hj) _).ne')] at lg
  simp only [log_pow] at lg
  have lc : 0.99 ≤ log 27-log 10 := by
    rw [show (27:ℝ)=3^3 by norm_num,log_pow,show (10:ℝ)=2*5 by norm_num,log_mul (by norm_num) (by norm_num)]
    linarith [log_two_lt_d9,log_five_lt_d9,log_three_gt_d9]
  have eq : (∑ j∈S,(↑(-z j).toNat:ℝ)*log j)-(∑ j∈S,(↑(z j).toNat:ℝ)*log j) =
      -(∑ j∈S,(z j:ℝ)*log j) := by
    rw [←sum_sub_distrib,←sum_neg_distrib]
    apply sum_congr rfl;intro j _
    have h : ((-z j).toNat:ℤ)-(z j).toNat = -(z j) := by omega
    have h' : ((-z j).toNat:ℝ)-(z j).toNat = -(z j:ℝ) := by exact_mod_cast h
    rw [←sub_mul,h',neg_mul]
  have gr' : growth S b = -(∑ j∈S,(z j:ℝ)*log j)/D := by
    rw [growth,neg_div,sum_div]
    congr 1
    apply sum_congr rfl;intro j hj
    calc
      _ = (b j/j)*log j := by ring
      _ = _ := by rw [b_div hj];ring
  rw [gr',D,Nat.cast_ofNat]
  norm_num [D] at lg
  linarith [eq]
end Erdos473RatioCoefficients

end

section

/- Packed values of a finite floor sum certified by geometric series and summation by parts. -/
namespace Erdos473PackedFloor
open Finset Erdos473Pack Erdos473FloorScan
lemma next_delta (K : ℕ) (b : ℕ → ℤ) (n : ℕ) :
    total K b (n+1)=total K b n+delta K b (n+1) := by
  unfold total delta
  simp only [Nat.succ_div,Nat.cast_add,mul_add,sum_add_distrib,Nat.succ_pos,true_and]
  congr 1
  apply sum_congr rfl;intro j _
  split_ifs <;> simp_all

lemma telescopes (B K T : ℕ) (b : ℕ → ℤ) :
    ((B:ℤ)-1)*(∑ i∈range (T+1),total K b i*(B:ℤ)^i) =
      (B:ℤ)^(T+1)*total K b T - ∑ i∈range (T+1),delta K b i*(B:ℤ)^i := by
  induction T with
  | zero => simp [total,delta]
  | succ T ih =>
    rw [sum_range_succ (f:=fun i => total K b i * (B:ℤ)^i),
       sum_range_succ (f:=fun i => delta K b i*(B:ℤ)^i),mul_add,ih,
       next_delta K b T,pow_succ (B:ℤ) (T+1)]
    ring

def encoded (B O K T : ℕ) (b : ℕ → ℤ) : ℤ :=
    O*(series B 1 (T+1):ℤ) +
       ((B:ℤ)^(T+1)*total K b T - explicit B 0 K T b)/(B-1:ℤ)

lemma encoded_eq {B : ℕ} (hb : 1<B) (O K T : ℕ) (b : ℕ → ℤ)
    (cap : ∀ i≤T,0≤(O:ℤ)+total K b i) :
    encoded B O K T b = (pack B (fun i=>((O:ℤ)+total K b i).toNat) (T+1):ℕ) := by
  rw [encoded, pack_eq,Nat.cast_sum,explicit_eq hb]
  simp only [Nat.cast_zero,zero_add]
  rw [←telescopes B K T b,Int.mul_ediv_cancel_left _ (by omega : (B:ℤ)-1≠0),series_eq hb (by decide),Nat.cast_sum]
  simp only [one_mul,Nat.cast_pow,mul_sum,←sum_add_distrib]
  apply sum_congr rfl;intro i hi
  have pos := cap i (by have := mem_range.mp hi;omega)
  simp [Int.toNat_of_nonneg pos];ring

def bits : ℕ := 24
def radix : ℕ := 2^bits
def offset : ℕ := 8388608
open Erdos473RatioCoefficients

lemma floor_cap (m : ℕ) : |total K coeff m| ≤ 412*10000 := by
  have terms : total K coeff m= -(∑ j∈S,z j*(m%j:ℕ)) := by
    have add : (total K coeff m)+(∑ j∈S,z j*(m%j:ℕ))=(∑ j∈S,z j)*m := by
      rw [total,show Icc 1 K=S by rfl,←sum_add_distrib,sum_mul]
      apply sum_congr rfl;intro j _
      have h : ((m%j:ℕ):ℤ)+(j:ℤ)*(m/j:ℕ)=m := by exact_mod_cast Nat.mod_add_div m j
      unfold coeff
      linear_combination (z j)*h
    rw [balance_int,zero_mul] at add
    omega
  rw [terms,abs_neg]
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply le_trans _ height_int
  apply sum_le_sum;intro j hj
  have jp : 0<j := (mem_Icc.mp hj).1
  simp only [coeff,abs_mul,Int.abs_natCast]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt m jp).le) (abs_nonneg _)

lemma cap (i : ℕ) : 0≤(offset:ℤ)+total K coeff i ∧ (offset:ℤ)+total K coeff i<radix := by
  have h := abs_le.mp (floor_cap i)
  norm_num [offset,radix,bits];omega

def table : ℕ := (encoded radix offset K 125000 coeff).toNat
lemma table_checked : table = (encoded radix offset K 125000 coeff).toNat := rfl

def digitAt (t m : ℕ) : ℤ := (((t >>> (bits*m))%radix:ℕ):ℤ)-offset
def val (m : ℕ) : ℤ := digitAt table m
lemma val_correct {m : ℕ} (hm : m≤125000) : val m = total K coeff m := by
  have pe := encoded_eq (B:=radix) (by decide) offset K 125000 coeff (fun i _ =>(cap i).1)
  have dp := pack_digit (B:=radix) (f:=fun i=>((offset:ℤ)+total K coeff i).toNat) (by decide)
    (show m<125000+1 by omega) (by
      intro i _
      exact_mod_cast (by simpa only [Int.toNat_of_nonneg (cap i).1] using (cap i).2 :
        ((((offset:ℤ)+total K coeff i).toNat:ℕ):ℤ)<radix))
  unfold val digitAt
  rw [table_checked,pe,Int.toNat_natCast,Nat.shiftRight_eq_div_pow,show 2^(bits*m)=radix^m by simp [radix,pow_mul],
    dp,Int.toNat_of_nonneg (cap m).1,add_sub_cancel_left]

def scoreWith (f : ℕ → ℤ) (m : ℕ) :=
  let u:=33*m/34
  let v:=(33*(m+1)-1)/34
  credit m (row m (f m) (extend u (f u)) (extend v (f v)))

def pointAt (t m : ℕ) := scoreWith (digitAt t) m
def pointFast (m : ℕ) := scoreWith val m
lemma point_fast_eq {m : ℕ} (hm : m≤125000) : pointFast m=point K coeff m := by
  simp only [pointFast,scoreWith,point,val_correct hm,val_correct (by omega : 33*m/34≤125000),
    val_correct (by omega : (33*(m+1)-1)/34≤125000)]

lemma pointAt_table : pointAt table = pointFast := rfl

end Erdos473PackedFloor

end

section

namespace Erdos473GroupedSum
open Finset

def accumulate (f : ℕ → ℕ) (m : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k+1, acc => accumulate f m k (acc+f (m+k))

lemma accumulate_sum (f : ℕ → ℕ) (m k acc : ℕ) :
    accumulate f m k acc = acc+∑ j∈Ico m (m+k),f j := by
  induction k generalizing acc with
  | zero => simp [accumulate]
  | succ k ih =>
    rw [accumulate,ih,show m+(k+1)=m+k+1 by omega,sum_Ico_succ_top (by omega : m ≤ m+k)]
    ac_rfl

def cumulative (f : ℕ → ℕ) (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => cumulative f w k+accumulate f (1+w*k) w 0

lemma cumulative_eq (f : ℕ → ℕ) (w k : ℕ) :
    cumulative f w k = ∑ m∈Ico 1 (1+w*k),f m := by
  induction k with
  | zero => simp [cumulative]
  | succ k ih =>
    rw [cumulative,ih,accumulate_sum,zero_add]
    have x := sum_Ico_consecutive f (Nat.le_add_right 1 _) (Nat.le_add_right (1+w*k) w)
    simpa only [Nat.mul_succ,←Nat.add_assoc] using x

end Erdos473GroupedSum

end

section

/- Evaluate one thousand consecutive shell costs from two bounded slices of the digit table. -/
namespace Erdos473PackedCredit
open Finset Erdos473PackedFloor Erdos473FloorScan Erdos473RatioCoefficients

def slice (x a w : ℕ) := (x >>> (bits*a)) % radix^w
def digit (x b : ℕ) : ℤ := (((x >>> (bits*b))%radix:ℕ):ℤ)-offset

lemma lookup (x a b w : ℕ) (hb : b<w) :
    digit (slice x a w) b = digit x (a+b) := by
  have dp (k : ℕ) : 2^(bits*k)=radix^k := by simp [radix,pow_mul]
  have ex : radix^w=radix^b*radix^(w-b) := by rw [←pow_add,show b+(w-b)=w by omega]
  have dvd : radix ∣ radix^(w-b) := dvd_pow_self _ (by omega)
  simp only [digit,slice,Nat.shiftRight_eq_div_pow,dp,ex,Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ dvd,Nat.div_div_eq_div_mul,pow_add]

def localPoint (a base full lower i : ℕ) :=
  let m := a+i
  let u := 33*m/34
  let v := (33*(m+1)-1)/34
  credit m (row m (digit full i) (extend u (digit lower (u-base))) (extend v (digit lower (v-base))))

lemma local_correct (a i : ℕ) (hi : i<1000) :
    localPoint a (33*a/34) (slice table a 1001) (slice table (33*a/34) 1001) i=pointFast (a+i) := by
  let b := 33*a/34
  let u := 33*(a+i)/34
  let v := (33*(a+i+1)-1)/34
  have hu : b≤u ∧ u-b<1001 := by dsimp [b,u];omega
  have hv : b≤v ∧ v-b<1001 := by dsimp [b,v];omega
  change credit _ (row _ (digit (slice table a 1001) i)
    (extend u (digit (slice table b 1001) (u-b))) (extend v (digit (slice table b 1001) (v-b))))=_
  rw [lookup _ _ _ _ (by omega),lookup _ _ _ _ hu.2,lookup _ _ _ _ hv.2,
    Nat.add_sub_of_le hu.1,Nat.add_sub_of_le hv.1]
  rfl

def forceNat (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n+1 => f (n+1)

lemma forceNat_eq (f : ℕ → ℕ) (n : ℕ) : forceNat f n = f n := by cases n <;> rfl

def slicedBlock (t a : ℕ) : ℕ :=
  let b := 33*a/34
  forceNat (fun full => forceNat (fun lower =>
    Erdos473GroupedSum.accumulate (localPoint a b full lower) 0 1000 0)
    (slice t b 1001)) (slice t a 1001)

lemma shift_acc (f g : ℕ → ℕ) (a k : ℕ) :
    (∀ i<k, f i = g (a+i)) → ∀ z,
    Erdos473GroupedSum.accumulate f 0 k z = Erdos473GroupedSum.accumulate g a k z := by
  induction k with
  | zero => intro h z; rfl
  | succ k ih =>
    intro h z
    simp only [Erdos473GroupedSum.accumulate,Nat.zero_add,h k (Nat.lt_succ_self k)]
    exact ih (fun i hi => h i (by omega)) _

lemma slicedBlock_eq (a : ℕ) : slicedBlock table a =
    Erdos473GroupedSum.accumulate pointFast a 1000 0 := by
  simp only [slicedBlock,forceNat_eq]
  exact shift_acc _ _ a 1000 (local_correct a) 0

abbrev cumulative := Erdos473GroupedSum.cumulative pointFast 1000

def portion (t a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => portion t a k + slicedBlock t (1+1000*(a+k))

lemma split_total (a k : ℕ) : cumulative (a+k) = cumulative a + portion table a k := by
  induction k with
  | zero => simp [portion]
  | succ k ih =>
    rw [Nat.add_succ,show cumulative ((a+k)+1) = cumulative (a+k) +
      Erdos473GroupedSum.accumulate pointFast (1+1000*(a+k)) 1000 0 by rfl,
      portion,slicedBlock_eq,ih,Nat.add_assoc]

def group (a k : ℕ) := forceNat (fun t => portion t a k) table

lemma split_group (a k : ℕ) : cumulative (a+k) = cumulative a + group a k := by
  rw [group,forceNat_eq,split_total]

def c0 : cumulative 0 = 0 := rfl
end Erdos473PackedCredit

end

section

namespace Erdos473PackedCredit
open Finset Erdos473PackedFloor Erdos473FloorScan Erdos473RatioCoefficients
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c5 : cumulative 5 = 9886727794 := by
  rw [show 5=0+5 by decide,split_group,c0]
  decide +kernel
end Erdos473PackedCredit

end

section

namespace Erdos473PackedCredit
open Finset Erdos473PackedFloor Erdos473FloorScan Erdos473RatioCoefficients
theorem certified_of (h : cumulative 125 = 12368280909) : (∑ m∈Icc 1 125000,point K coeff m) ≤ 12400000000 := by
  have cc (k : ℕ) : cumulative k = ∑ m∈Ico 1 (1+1000*k),pointFast m :=
    Erdos473GroupedSum.cumulative_eq pointFast 1000 k
  have eq : (∑ m∈Icc 1 125000,point K coeff m) = cumulative 125 := by
    rw [cc,show Ico 1 (1+1000*125)=Icc 1 125000 by ext i; simp only [mem_Icc,mem_Ico]; omega]
    exact sum_congr rfl fun m hm => (point_fast_eq (mem_Icc.mp hm).2).symm
  rw [eq,h]
  decide
end Erdos473PackedCredit

end

section

namespace Erdos473PackedCredit
open Finset Erdos473PackedFloor Erdos473FloorScan Erdos473RatioCoefficients
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c10 : cumulative 10 = 11331056000 := by
  rw [show 10=5+5 by decide,split_group,c5]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c15 : cumulative 15 = 11651415964 := by
  rw [show 15=10+5 by decide,split_group,c10]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c20 : cumulative 20 = 11836703713 := by
  rw [show 20=15+5 by decide,split_group,c15]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c25 : cumulative 25 = 11944671031 := by
  rw [show 25=20+5 by decide,split_group,c20]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c30 : cumulative 30 = 12019506218 := by
  rw [show 30=25+5 by decide,split_group,c25]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c35 : cumulative 35 = 12081225461 := by
  rw [show 35=30+5 by decide,split_group,c30]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c40 : cumulative 40 = 12136523616 := by
  rw [show 40=35+5 by decide,split_group,c35]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c45 : cumulative 45 = 12174933136 := by
  rw [show 45=40+5 by decide,split_group,c40]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c50 : cumulative 50 = 12203531204 := by
  rw [show 50=45+5 by decide,split_group,c45]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c55 : cumulative 55 = 12222321836 := by
  rw [show 55=50+5 by decide,split_group,c50]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c60 : cumulative 60 = 12247499029 := by
  rw [show 60=55+5 by decide,split_group,c55]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c65 : cumulative 65 = 12265968048 := by
  rw [show 65=60+5 by decide,split_group,c60]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c70 : cumulative 70 = 12279393673 := by
  rw [show 70=65+5 by decide,split_group,c65]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c75 : cumulative 75 = 12291921210 := by
  rw [show 75=70+5 by decide,split_group,c70]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c80 : cumulative 80 = 12303129422 := by
  rw [show 80=75+5 by decide,split_group,c75]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c85 : cumulative 85 = 12311879306 := by
  rw [show 85=80+5 by decide,split_group,c80]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c90 : cumulative 90 = 12320167382 := by
  rw [show 90=85+5 by decide,split_group,c85]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c95 : cumulative 95 = 12328667836 := by
  rw [show 95=90+5 by decide,split_group,c90]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c100 : cumulative 100 = 12335935302 := by
  rw [show 100=95+5 by decide,split_group,c95]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c105 : cumulative 105 = 12344107490 := by
  rw [show 105=100+5 by decide,split_group,c100]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c110 : cumulative 110 = 12351638987 := by
  rw [show 110=105+5 by decide,split_group,c105]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c115 : cumulative 115 = 12357080749 := by
  rw [show 115=110+5 by decide,split_group,c110]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c120 : cumulative 120 = 12363573318 := by
  rw [show 120=115+5 by decide,split_group,c115]
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
def c125 : cumulative 125 = 12368280909 := by
  rw [show 125=120+5 by decide,split_group,c120]
  decide +kernel
theorem certified : (∑ m∈Icc 1 125000,point K coeff m) ≤ 12400000000 := certified_of c125
end Erdos473PackedCredit

end

section

/- Twelve explicit interval-sieve bounds for the quotient shells up to 125000. -/
namespace Erdos473OrdinaryShells
open Real Finset Erdos473LogBounds Erdos473Selberg Erdos473OrdinaryCriterion
noncomputable section

def deci (m : ℕ) : ℕ :=
  let n := m*(m+1)
  if n≤1 then 25 else if n≤10 then 26 else if n≤100 then 28 else if n≤1000 then 30
  else if n≤10000 then 32 else if n≤100000 then 35 else if n≤1000000 then 38
  else if n≤10000000 then 42 else if n≤100000000 then 46 else if n≤1000000000 then 52
  else if n≤10000000000 then 59 else 68

lemma log_ten : log 10 ≤ 2.31 := by
  rw [show (10:ℝ)=2*5 by norm_num,log_mul (by norm_num) (by norm_num)]
  linarith [log_two_lt_d9,log_five_lt_d9]

lemma envelope_band {n den : ℝ} (hn : 0<n) (dp : 0<den) (hH : 45 ≤ log n) (k : ℕ) (hk : den≤10^k)
    (u C : ℝ) (hu : 1≤u) (u_bound : log (45*(1-2.31*k/45))≤u)
    (beta : 0<(1-2.31*(k:ℝ)/45)) (pos : 0<1/2-u/(45*(1-2.31*(k:ℝ)/45)))
    (cap : 1/((1/2-u/(45*(1-2.31*k/45)))*(1-2.31*k/45))+
        1/(45*(1-2.31*k/45)^2) ≤ C) :
    0<log (n/den)/2-log (log (n/den)) ∧
    1/(log (n/den)/2-log (log (n/den)))+1/(log (n/den))^2≤C/log n := by
  apply envelope hH beta _ hu u_bound pos cap
  have dh := log_le_log dp hk
  rw [log_pow] at dh
  rw [log_div hn.ne' dp.ne']
  nlinarith [mul_le_mul_of_nonneg_left log_ten (Nat.cast_nonneg k : (0:ℝ)≤k),
    mul_nonneg (sub_nonneg.mpr hH) (Nat.cast_nonneg k : (0:ℝ)≤k)]

set_option maxHeartbeats 4000000 in
lemma explicit_envelopes {n : ℝ} (hn : 0<n) (hH : 45≤log n) {m : ℕ}
    (hm : 1≤ m) (hu : m≤125000) :
    let den:ℝ := m*(m+1)
    let t := log (n/den)
    0<t/2-log t ∧ 1/(t/2-log t)+1/t^2≤((deci m:ℝ)/10)/log n := by
  dsimp only
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0< m by omega)
  have dp : 0<(m:ℝ)*(m+1) := by positivity
  have un : m*(m+1)≤10^11 := by
    have := Nat.mul_le_mul hu (show m+1≤125001 by omega)
    omega
  have one (k : ℕ) (h : m*(m+1) ≤ 10^k) (C u : ℝ)
      (u_bound : log (45*(1-2.31*k/45))≤u) (hu' : 1≤u)
      (b : 0<(1-2.31*(k:ℝ)/45)) (p : 0<1/2-u/(45*(1-2.31*(k:ℝ)/45)))
      (c : 1/((1/2-u/(45*(1-2.31*k/45)))*(1-2.31*k/45))+1/(45*(1-2.31*k/45)^2)≤C) :=
    envelope_band hn dp hH k (by exact_mod_cast h) u C hu' u_bound b p c
  unfold deci
  dsimp only
  split
  · rename_i h0
    exact one 0 (by simpa using h0) (25/10) 3.9 (by
      convert (log_constant (c:=45*(1-2.31*(0:ℝ)/45)) (δ:=0.9) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h1
    exact one 1 (by simpa using h1) (26/10) 3.8 (by
      convert (log_constant (c:=45*(1-2.31*(1:ℝ)/45)) (δ:=0.8) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h2
    exact one 2 (by simpa using h2) (28/10) 3.7 (by
      convert (log_constant (c:=45*(1-2.31*(2:ℝ)/45)) (δ:=0.7) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h3
    exact one 3 (by simpa using h3) (30/10) 3.7 (by
      convert (log_constant (c:=45*(1-2.31*(3:ℝ)/45)) (δ:=0.7) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h4
    exact one 4 (by simpa using h4) (32/10) 3.6 (by
      convert (log_constant (c:=45*(1-2.31*(4:ℝ)/45)) (δ:=0.6) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h5
    exact one 5 (by simpa using h5) (35/10) 3.6 (by
      convert (log_constant (c:=45*(1-2.31*(5:ℝ)/45)) (δ:=0.6) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h6
    exact one 6 (by simpa using h6) (38/10) 3.5 (by
      convert (log_constant (c:=45*(1-2.31*(6:ℝ)/45)) (δ:=0.5) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h7
    exact one 7 (by simpa using h7) (42/10) 3.4 (by
      convert (log_constant (c:=45*(1-2.31*(7:ℝ)/45)) (δ:=0.4) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h8
    exact one 8 (by simpa using h8) (46/10) 3.3 (by
      convert (log_constant (c:=45*(1-2.31*(8:ℝ)/45)) (δ:=0.3) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h9
    exact one 9 (by simpa using h9) (52/10) 3.2 (by
      convert (log_constant (c:=45*(1-2.31*(9:ℝ)/45)) (δ:=0.2) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  split
  · rename_i h10
    exact one 10 (by simpa using h10) (59/10) 3.1 (by
      convert (log_constant (c:=45*(1-2.31*(10:ℝ)/45)) (δ:=0.1) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact one 11 un (68/10) 3.0 (by
      convert (log_constant (c:=45*(1-2.31*(11:ℝ)/45)) (δ:=0.0) 3 (by norm_num) (by norm_num) (by norm_num)) using 1 <;> norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


theorem shell_bound {N m : ℕ} (hn : 90953418231753380142≤N) (hm : m∈Icc 1 125000) :
    (∑ p∈shell N m,log p) ≤ ((deci m:ℝ)/10)*(N:ℝ)/(m*(m+1)) := by
  obtain ⟨hl,hu⟩ := mem_Icc.mp hm
  have hn' : (90953418231753380142:ℝ)≤N := by exact_mod_cast hn
  have hH := checked_range_log hn'
  have hp : (0:ℝ)<N := by linarith
  have hlog : 0<log N := by linarith
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0< m by omega)
  let x := (N:ℝ)/(m+1)
  let y := (N:ℝ)/m
  let den := (m:ℝ)*(m+1)
  have dp : 0<den := by dsimp [den];positivity
  have xy : y-x=(N:ℝ)/den := by dsimp [x,y,den];field_simp;ring
  have hxy : x<y := sub_pos.mp (xy ▸ div_pos hp dp)
  have ub : den≤10^11 := by
    dsimp [den]
    have v := Nat.mul_le_mul hu (show m+1≤125001 by omega)
    exact_mod_cast (show m*(m+1) ≤ 10^11 by omega)
  have v := log_le_log dp ub
  rw [log_pow] at v
  norm_num only [Nat.cast_ofNat] at v
  have hlv : 1≤log (y-x) := by rw [xy,log_div hp.ne' dp.ne'];nlinarith [log_ten]
  have hroot : sqrt (y-x) ≤ x := by
    dsimp [x]
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [xy]
    dsimp [den]
    field_simp
    have mo : (1:ℝ) ≤ m := by exact_mod_cast hl
    nlinarith [mul_nonneg (show 0≤(N:ℝ)-2 by linarith) mp.le]
  have env := explicit_envelopes hp hH hl hu
  change _ ∧ _ ≤ ((deci m:ℝ)/10)/log N at env
  have count := interval_prime_envelope (H:=log N) (q:=1) 0 hxy (by decide)
    (by simpa using hroot) (by simpa using hlv) (by simpa [xy,den] using env)
  have fx : ⌊x⌋₊=N/(m+1) := by dsimp [x];rw [←Nat.cast_add_one,Nat.floor_div_natCast,Nat.floor_natCast]
  have fy : ⌊y⌋₊=N/m := by dsimp [y];rw [Nat.floor_div_natCast,Nat.floor_natCast]
  rw [fx,fy,xy] at count
  have mod1 (p : ℕ) : Nat.ModEq 1 p 0 := Nat.mod_one p
  simp only [mod1, true_and,Nat.totient_one,Nat.cast_one,one_mul] at count
  have c := mul_le_mul_of_nonneg_right count hlog.le
  calc
    _ ≤ ∑ _d∈shell N m,log N := by
      apply sum_le_sum;intro d hd
      obtain ⟨hi,pr⟩ := mem_filter.mp hd
      exact log_le_log (by exact_mod_cast pr.pos) (by exact_mod_cast (mem_Ioc.mp hi).2.trans (Nat.div_le_self ..))
    _ = (shell N m).card*log N := by simp
    _ ≤ _ := c.trans_eq (by dsimp [den]; field_simp)
end
end Erdos473OrdinaryShells

end

section

/- Transfer a summed integer credit certificate to the real shell budget. -/
namespace Erdos473CreditTransfer
open Finset Real
noncomputable section

lemma floor_eq (m : ℕ) : Erdos473Balanced.floorSum Erdos473RatioCoefficients.S Erdos473RatioCoefficients.b m = (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m:ℝ)/10000 := by
  unfold Erdos473Balanced.floorSum Erdos473FloorScan.total Erdos473RatioCoefficients.S
  rw [Int.cast_sum,Finset.sum_div]
  apply sum_congr rfl;intro j _
  simp only [Erdos473RatioCoefficients.b,Erdos473RatioCoefficients.D,Int.cast_mul,Int.cast_natCast,Nat.cast_ofNat]
  ring

lemma extend_eq (m : ℕ) : Erdos473OrdinaryCriterion.extend (Erdos473Balanced.floorSum Erdos473RatioCoefficients.S Erdos473RatioCoefficients.b) m =
    (Erdos473FloorScan.extend m (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m):ℝ)/10000 := by
  simp only [Erdos473OrdinaryCriterion.extend,Erdos473FloorScan.extend,Erdos473FloorScan.D,floor_eq,Int.cast_add,Int.cast_ite]
  split_ifs <;> push_cast <;> ring

lemma excess_le (m : ℕ) :
    Erdos473OrdinaryCriterion.excess (Erdos473Balanced.floorSum Erdos473RatioCoefficients.S Erdos473RatioCoefficients.b) m ≤
    (Erdos473FloorScan.row m (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m)
      (Erdos473FloorScan.extend (33*m/34) (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff (33*m/34)))
      (Erdos473FloorScan.extend ((33*(m+1)-1)/34) (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff ((33*(m+1)-1)/34))):ℝ)/10000 := by
  let x := Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m
  let y := Erdos473FloorScan.extend (33*m/34) (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff (33*m/34))
  let z := Erdos473FloorScan.extend ((33*(m+1)-1)/34) (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff ((33*(m+1)-1)/34))
  unfold Erdos473OrdinaryCriterion.excess
  rw [floor_eq,extend_eq,extend_eq]
  change max 0 ((x:ℝ)/10000-min ((y:ℝ)/10000) ((z:ℝ)/10000)) ≤ (((x-min y z).toNat:ℝ)/10000)
  apply max_le (by positivity)
  have e : (((x-min y z):ℤ):ℝ) ≤ ((x-min y z).toNat:ℝ) := by exact_mod_cast Int.self_le_toNat _
  by_cases h : y≤z
  · rw [min_eq_left h] at e ⊢
    rw [min_eq_left (div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num))]
    push_cast at e
    linarith
  · have h' := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h'] at e ⊢
    rw [min_eq_right (div_le_div_of_nonneg_right (by exact_mod_cast h') (by norm_num))]
    push_cast at e
    linarith

lemma value_le_credit {m : ℕ} (mp : 0< m) :
    (Erdos473OrdinaryCriterion.excess (Erdos473Balanced.floorSum Erdos473RatioCoefficients.S Erdos473RatioCoefficients.b) m*((Erdos473OrdinaryShells.deci m:ℝ)/10))/(m*(m+1)) ≤
    (Erdos473FloorScan.point Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m:ℝ)/1000000000000 := by
  let a := Erdos473FloorScan.row m (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m)
      (Erdos473FloorScan.extend (33*m/34) (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff (33*m/34)))
      (Erdos473FloorScan.extend ((33*(m+1)-1)/34) (Erdos473FloorScan.total Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff ((33*(m+1)-1)/34)))
  change _ ≤ (Erdos473FloorScan.credit m a:ℝ)/1000000000000
  have el : Erdos473OrdinaryCriterion.excess (Erdos473Balanced.floorSum Erdos473RatioCoefficients.S Erdos473RatioCoefficients.b) m ≤ (a:ℝ)/10000 := excess_le m
  have dp : 0<10*m*(m+1) := by positivity
  have h := Nat.lt_mul_div_succ (a*Erdos473FloorScan.deci m*100000000) dp
  have bnd : (a:ℝ)*(Erdos473OrdinaryShells.deci m:ℝ)*100000000 ≤
      (Erdos473FloorScan.credit m a:ℝ)*(10*(m:ℝ)*(m+1)) := by
    have eq : Erdos473FloorScan.deci m=Erdos473OrdinaryShells.deci m := rfl
    rw [←eq]
    unfold Erdos473FloorScan.credit
    exact_mod_cast (by simpa [Nat.mul_comm] using h.le)
  have mp' : (0:ℝ)< m := by exact_mod_cast mp
  have v := mul_le_mul_of_nonneg_right el (show (0:ℝ)≤(Erdos473OrdinaryShells.deci m:ℝ)/10 by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

theorem certified_budget (int_bound : ∑ m∈Icc 1 125000,Erdos473FloorScan.point Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m ≤ 12400000000) :
    ∑ m∈Icc 1 125000,(Erdos473OrdinaryCriterion.excess (Erdos473Balanced.floorSum Erdos473RatioCoefficients.S Erdos473RatioCoefficients.b) m*((Erdos473OrdinaryShells.deci m:ℝ)/10))/(m*(m+1)) ≤ 0.0124 := by
  calc
    _ ≤ ∑ m∈Icc 1 125000,(Erdos473FloorScan.point Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m:ℝ)/1000000000000 :=
      sum_le_sum fun m hm => value_le_credit (mem_Icc.mp hm).1
    _ ≤ _ := by
      rw [←sum_div,←Nat.cast_sum]
      have hh : (↑(∑ m∈Icc 1 125000,Erdos473FloorScan.point Erdos473RatioCoefficients.K Erdos473RatioCoefficients.coeff m):ℝ) ≤ 12400000000 := by exact_mod_cast int_bound
      linarith
end
end Erdos473CreditTransfer

end

section

/- Quantitative ordinary-prime density in the final thirty-fourth of every checked-range interval. -/
namespace Erdos473PackedCount

open Finset Real Chebyshev Erdos473RatioCoefficients

theorem mass {N : ℕ} (hn : 90953418231753380142 ≤ N) :
    0.0127*(N:ℝ)<theta N-theta (33*N/34:ℕ) := by
  apply Erdos473OrdinaryReduction.from_envelope hn (S:=S) (b:=b)
      (fun j hj => mem_Icc.mp hj) balance growth_ge height_le
      (fun _ hm => Erdos473OrdinaryShells.shell_bound hn hm)
  exact Erdos473CreditTransfer.certified_budget Erdos473PackedCredit.certified

theorem count (N : ℕ) (hn : 90953418231753380142 ≤ N) :
    0.0127*(N:ℝ)/log N < ((Ioc (33*N/34) N).filter Nat.Prime).card :=
  Erdos473OrdinaryReduction.count_from_mass (by omega) (mass hn)

end Erdos473PackedCount

end

section

theorem OMA.solution : type_of% @Erdos473.erdos_473.variants.finite := by
  apply Erdos473MatchingInduction.finite_of_steps (C:=Erdos473TripleConstants.C) (B:=90953418231753380142)
    (by norm_num [Erdos473TripleConstants.C])
  · intro n k _ hn room thin
    exact Erdos473MatchingFiniteInduction.descend _ Erdos473SmallSeed.all
      Erdos473MatchingInduction.finite_expand Erdos473MatchingInduction.finite_three
      Erdos473MatchingInduction.finite_contract n k hn room thin
  · exact Erdos473LargeMatching.big_step Erdos473PackedCount.count

end
