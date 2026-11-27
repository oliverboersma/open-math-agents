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
import Mathlib.Data.Nat.Choose.Basic

-- Credit: @avivorly
namespace WeightSixteenSecantIndexGeneric

open Finset

variable {P : Type} [DecidableEq P]

def insideRow {X : Type} (internal : Finset P) (M : X → P → Bool) (x : X) : Finset P :=
  internal.filter fun p => M x p = true

def freePairs (internal : Finset P) (A : Fin 8 → P → Bool) : Finset (Finset P) :=
  internal.powersetCard 2 \
    (Finset.univ : Finset (Fin 8)).biUnion (fun a => (insideRow internal A a).powersetCard 2)

lemma row_mem {X : Type} (internal : Finset P) (M : X → P → Bool) (x : X) (p : P) :
    p ∈ insideRow internal M x ↔ p ∈ internal ∧ M x p = true := by
  simp [insideRow]

lemma shared_pair_eq (internal : Finset P) (M : Fin 8 ⊕ Fin 72 → P → Bool)
    (col_pair : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (t : Finset P) (pairs : t.card = 2)
    (l m : Fin 8 ⊕ Fin 72) (on_l : t ⊆ insideRow internal M l) (on_m : t ⊆ insideRow internal M m) :
    l = m := by
  obtain ⟨p,q,ne,eq⟩ := Finset.card_eq_two.mp pairs
  have hp : p ∈ t := eq ▸ Finset.mem_insert_self _ _
  have hq : q ∈ t := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact col_pair p q ne l m ((row_mem internal M l p).mp (on_l hp) |>.2) ((row_mem internal M l q).mp (on_l hq) |>.2)
    ((row_mem internal M m p).mp (on_m hp) |>.2) ((row_mem internal M m q).mp (on_m hq) |>.2)

theorem secant_index (internal : Finset P) (cardS : internal.card = 16)
    (A : Fin 8 → P → Bool) (B : Fin 72 → P → Bool)
    (four : ∀ a, (insideRow internal A a).card = 4)
    (two : ∀ b, (insideRow internal B b).card = 2)
    (col_pair : ∀ p q, p ≠ q → ∀ l m : Fin 8 ⊕ Fin 72,
      Sum.elim A B l p = true → Sum.elim A B l q = true →
      Sum.elim A B m p = true → Sum.elim A B m q = true → l = m) :
    ∃ e : Fin 72 ≃ ↥(freePairs internal A), ∀ b, (e b).val = insideRow internal B b := by
  let by_row (a : Fin 8) := (insideRow internal A a).powersetCard 2
  let used := (Finset.univ : Finset (Fin 8)).biUnion by_row
  let possible := internal.powersetCard 2
  have unique := shared_pair_eq internal (Sum.elim A B) col_pair
  have by_row_disjoint : (↑(Finset.univ : Finset (Fin 8)) : Set (Fin 8)).PairwiseDisjoint by_row := by
    intro a _ b _ ne
    change Disjoint (by_row a) (by_row b)
    rw [Finset.disjoint_left]
    intro t ht hq
    obtain ⟨at_a,size⟩ := Finset.mem_powersetCard.mp ht
    obtain ⟨at_b,_⟩ := Finset.mem_powersetCard.mp hq
    exact ne (Sum.inl.inj (unique t size (.inl a) (.inl b) at_a at_b))
  have fact (a : Fin 8) : (by_row a).card = 6 := by
    change ((insideRow internal A a).powersetCard 2).card = 6
    rw [Finset.card_powersetCard,four]
    decide
  have used_count : used.card = 48 := by
    change ((Finset.univ : Finset (Fin 8)).biUnion by_row).card = 48
    rw [Finset.card_biUnion by_row_disjoint]
    simp [fact]
  have possible_count : possible.card = 120 := by
    change (internal.powersetCard 2).card = 120
    rw [Finset.card_powersetCard,cardS]
    decide
  have use_possible : used ⊆ possible := by
    intro t ht
    obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_powersetCard.mp ha).1.trans (Finset.filter_subset _ _),
      (Finset.mem_powersetCard.mp ha).2⟩
  have free_count : (freePairs internal A).card = 72 := by
    change (possible \ used).card = 72
    rw [Finset.card_sdiff_of_subset use_possible,possible_count,used_count]
  have free (b : Fin 72) : insideRow internal B b ∈ freePairs internal A := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _,two b⟩,?_⟩
    intro clash
    obtain ⟨a,_,inA⟩ := Finset.mem_biUnion.mp clash
    have at_a := (Finset.mem_powersetCard.mp inA).1
    have on_b : insideRow internal B b ⊆ insideRow internal B b := Finset.Subset.rfl
    have same := unique (insideRow internal B b) (two b) (.inl a) (.inr b) at_a on_b
    cases same
  let f (b : Fin 72) : ↥(freePairs internal A) := ⟨insideRow internal B b,free b⟩
  have one_to_one : Function.Injective f := by
    intro b c same
    have sameRows : insideRow internal B b = insideRow internal B c := congrArg Subtype.val same
    have here : insideRow internal B b ⊆ insideRow internal B b := Finset.Subset.rfl
    have there : insideRow internal B b ⊆ insideRow internal B c := sameRows ▸ here
    exact Sum.inr.inj (unique _ (two b) (.inr b) (.inr c) here there)
  have cardinal : Fintype.card (Fin 72) = Fintype.card ↥(freePairs internal A) := by
    rw [Fintype.card_fin,Fintype.card_coe,free_count]
  have both := (Fintype.bijective_iff_injective_and_card f).mpr ⟨one_to_one,cardinal⟩
  exact ⟨Equiv.ofBijective f both,fun _ => rfl⟩

end WeightSixteenSecantIndexGeneric


theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro P instance_ S size A B aSize bSize same
  exact WeightSixteenSecantIndexGeneric.secant_index S size A B aSize bSize same
