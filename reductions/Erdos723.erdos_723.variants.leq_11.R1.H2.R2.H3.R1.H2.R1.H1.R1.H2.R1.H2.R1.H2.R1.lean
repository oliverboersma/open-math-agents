import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Tauto

/-! Isolate Carter's fourth sparse starting matrix. -/
-- Credit: @avivorly
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1

open Finset
open scoped Classical BigOperators

def H1 : Prop :=
  let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  ¬ ∃ (S : Finset P) (A : Fin 8 → P → Bool),
    S.card = 16 ∧
    (∀ a, (S.filter fun p => A a p = true).card = 4) ∧
    (∀ a (q : Q), A a (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2)) ∧
    (∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b)) ∧
    (∀ a i, A a (.inr i) = false) ∧
    let C := S.powersetCard 2 \
      (Finset.univ : Finset (Fin 8)).biUnion (fun a => (S.filter fun p => A a p = true).powersetCard 2)
    ∃ B : ↥C → P → Bool,
      let M := Sum.elim A B
      let c (p : P) := (Finset.univ.filter fun a => A a p = true).card
      let d (p : P) := (Finset.univ.filter fun b => B b p = true).card
      (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
      (∀ b p, p ∈ S → (B b p = true ↔ p ∈ b.val)) ∧
      (∀ p ∈ S, c p = 2 ∧ d p = 9) ∧
      (∀ p ∉ S, 2*c p + d p = 8) ∧
      (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
      (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
        M m p = true → M m q = true → l = m) ∧
      (∀ p ∈ S, ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
      let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      let word := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
      word = 0x3da1087

def H2 : Prop :=
  let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  ¬ ∃ (S : Finset P) (A : Fin 8 → P → Bool),
    S.card = 16 ∧
    (∀ a, (S.filter fun p => A a p = true).card = 4) ∧
    (∀ a (q : Q), A a (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2)) ∧
    (∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b)) ∧
    (∀ a i, A a (.inr i) = false) ∧
    let C := S.powersetCard 2 \
      (Finset.univ : Finset (Fin 8)).biUnion (fun a => (S.filter fun p => A a p = true).powersetCard 2)
    ∃ B : ↥C → P → Bool,
      let M := Sum.elim A B
      let c (p : P) := (Finset.univ.filter fun a => A a p = true).card
      let d (p : P) := (Finset.univ.filter fun b => B b p = true).card
      (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
      (∀ b p, p ∈ S → (B b p = true ↔ p ∈ b.val)) ∧
      (∀ p ∈ S, c p = 2 ∧ d p = 9) ∧
      (∀ p ∉ S, 2*c p + d p = 8) ∧
      (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
      (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
        M m p = true → M m q = true → l = m) ∧
      (∀ p ∈ S, ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
      let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      let word := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
      word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0xfc02187] : List Nat)


theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro noFour noOther
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1.H2
  dsimp only
  rintro ⟨S,A,sCard,heavy,paired,private_,hidden,B,rows,secants,inside,outside,rowPairs,colPairs,codePairs,seen⟩
  classical
  let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
  let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
  let word := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
  by_cases four : word = 0x3da1087
  · exact noFour ⟨S,A,sCard,heavy,paired,private_,hidden,B,rows,secants,inside,outside,rowPairs,colPairs,codePairs,four⟩
  · have alternatives : word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0xfc02187] : List Nat) := by
      change word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187] : List Nat) at seen
      simp only [List.mem_cons,List.not_mem_nil,or_false] at seen ⊢
      tauto
    exact noOther ⟨S,A,sCard,heavy,paired,private_,hidden,B,rows,secants,inside,outside,rowPairs,colPairs,codePairs,alternatives⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1
