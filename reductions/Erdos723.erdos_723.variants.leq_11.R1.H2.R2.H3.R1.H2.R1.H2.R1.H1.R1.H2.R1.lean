import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases

/-! The exterior graph must be one of the forms compatible with the triple points. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H2_R1

open Finset
open scoped Classical

def H1 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ∀ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) →
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) →
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) →
    (∀ p ∉ S, 2 * A M p + B M p = 8) →
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) →
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true → M m p = true → M m q = true → l = m) →
    (∃ p q, p ∉ S ∧ q ∉ S ∧ A M p = 3 ∧ A M q = 3 ∧
      Disjoint (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true)
        (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true)) →
    ∃ e : Equiv.Perm (Fin 8),
      let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ x ∉ S, M (.inl (e a)) x = true ∧ M (.inl (e b)) x = true)
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      ((pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0) = 0x35a5807

def H2 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    (∀ p ∉ S, A M p ≤ 3) ∧
    (Finset.univ.filter fun p => p ∉ S ∧ A M p = 3).card = 2 ∧
    (∀ p q, p ≠ q → p ∉ S → q ∉ S → A M p = 3 → A M q = 3 →
      Disjoint (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true)
        (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true)) ∧
    ∃ e : Equiv.Perm (Fin 8),
      let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ x ∉ S, M (.inl (e a)) x = true ∧ M (.inl (e b)) x = true)
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      ((pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0) = 0x35a5807

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro chooseGraph impossible
  classical
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1.H2
  dsimp only
  rintro ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,maxTriple,pointCount,separated⟩
  let points := Finset.univ.filter fun q : Fin 111 => q ∉ S ∧
    (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true).card = 3
  have count : points.card = 2 := pointCount
  have hit : (∃ p q, p ∉ S ∧ q ∉ S ∧ (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 3 ∧ (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true).card = 3 ∧
      Disjoint (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true)
        (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true)) := by
    obtain ⟨p,q,ne,shape⟩ := Finset.card_eq_two.mp count
    have p_mem : p ∈ points := shape ▸ Finset.mem_insert_self _ _
    have q_mem : q ∈ points := shape ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨hp,cp⟩ := (Finset.mem_filter.mp p_mem).2
    obtain ⟨hq,cq⟩ := (Finset.mem_filter.mp q_mem).2
    exact ⟨p,q,hp,hq,cp,cq,separated p q ne hp hq cp cq⟩
  have graph := chooseGraph M S rows As inside outside rowPairs colPairs hit
  exact impossible ⟨M,S,cardS,rows,As,Bs,inside,outside,rowPairs,colPairs,maxTriple,pointCount,separated,graph⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H2_R1
