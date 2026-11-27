import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1
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

-- Credit: @avivorly
namespace WeightSixteenCubicGeometry

open Finset

def together (A : Fin 8 → Fin 111 → Bool) (p : Fin 111) (a b : Fin 8) : Prop :=
  A a p = true ∧ A b p = true

noncomputable def outer (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a : Fin 8) :
    Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∉ S, together A p a b

noncomputable def inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a : Fin 8) :
    Finset (Fin 8) := by
  classical
  exact Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∈ S, together A p a b

lemma mem_outer (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a b : Fin 8) :
    b ∈ outer A S a ↔ b ≠ a ∧ ∃ p ∉ S, together A p a b := by
  classical
  simp [outer]

lemma mem_inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a b : Fin 8) :
    b ∈ inner A S a ↔ b ≠ a ∧ ∃ p ∈ S, together A p a b := by
  classical
  simp [inner]

theorem outer_symm (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a b : Fin 8) :
    b ∈ outer A S a ↔ a ∈ outer A S b := by
  rw [mem_outer, mem_outer]
  constructor <;> rintro ⟨different, p, outside, on_a, on_b⟩
  · exact ⟨different.symm,p,outside,on_b,on_a⟩
  · exact ⟨different.symm,p,outside,on_b,on_a⟩

theorem outer_irrefl (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (a : Fin 8) :
    a ∉ outer A S a := by simp [mem_outer]

lemma second_row (A : Fin 8 → Fin 111 → Bool) (p : Fin 111)
    (rows : (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (on_a : A a p = true) : ∃! b, b ≠ a ∧ A b p = true := by
  let here : Finset (Fin 8) := Finset.univ.filter fun r => A r p = true
  have contains_a : a ∈ here := Finset.mem_filter.mpr ⟨Finset.mem_univ _,on_a⟩
  have residual : (here.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem contains_a]
    exact Nat.sub_eq_of_eq_add rows
  obtain ⟨b, represented⟩ := Finset.card_eq_one.mp residual
  have iff_mem (r : Fin 8) : r ∈ here.erase a ↔ r ≠ a ∧ A r p = true := by
    simp [here, Finset.mem_erase, Finset.mem_filter]
  have hb : b ∈ here.erase a := by rw [represented]; exact Finset.mem_singleton_self b
  refine ⟨b,(iff_mem b).mp hb,fun r hr => ?_⟩
  have h := (iff_mem r).mpr hr
  rw [represented] at h
  exact Finset.mem_singleton.mp h

lemma cardinal_inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (line_four : (S.filter fun p => A a p = true).card = 4) :
    (inner A S a).card = 4 := by
  classical
  let on_line := S.filter fun p => A a p = true
  have second (p : Fin 111) (hp : p ∈ on_line) : ∃! b, b ≠ a ∧ A b p = true := by
    obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
    exact second_row A p (degree_two p inS) a onA
  let other (p : Fin 111) (hp : p ∈ on_line) := Classical.choose (second p hp)
  have other_good (p : Fin 111) (hp : p ∈ on_line) :
      (other p hp ≠ a ∧ A (other p hp) p = true) ∧
      ∀ b, b ≠ a ∧ A b p = true → b = other p hp := Classical.choose_spec (second p hp)
  have bij : on_line.card = (inner A S a).card := by
    apply Finset.card_bij other
    · intro p hp
      obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
      obtain ⟨different, onB⟩ := (other_good p hp).1
      exact (mem_inner A S a _).mpr ⟨different,p,inS,onA,onB⟩
    · intro p hp q hq eq
      obtain ⟨_, _, unique⟩ := share a (other p hp) ((other_good p hp).1.1.symm)
      have one : together A p a (other p hp) :=
        ⟨(Finset.mem_filter.mp hp).2,(other_good p hp).1.2⟩
      have two : together A q a (other p hp) :=
        ⟨(Finset.mem_filter.mp hq).2,eq.symm ▸ (other_good q hq).1.2⟩
      exact (unique p one).trans (unique q two).symm
    · intro b hb
      obtain ⟨different,p,inS,onA,onB⟩ := (mem_inner A S a b).mp hb
      have hp : p ∈ on_line := Finset.mem_filter.mpr ⟨inS,onA⟩
      exact ⟨p,hp,((other_good p hp).2 b ⟨different,onB⟩).symm⟩
  exact bij.symm.trans line_four

theorem exterior_cubic (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4)
    (a : Fin 8) : (outer A S a).card = 3 := by
  classical
  have inner_four := cardinal_inner A S share degree_two a (line_four a)
  have separated : Disjoint (inner A S a) (outer A S a) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    obtain ⟨different,p,inside,hp⟩ := (mem_inner A S a b).mp hb
    obtain ⟨_,q,outside,hq⟩ := (mem_outer A S a b).mp hc
    obtain ⟨_, _, unique⟩ := share a b different.symm
    have same := (unique p hp).trans (unique q hq).symm
    exact outside (same ▸ inside)
  have total : inner A S a ∪ outer A S a = Finset.univ.erase a := by
    ext b
    simp only [Finset.mem_union, mem_inner, mem_outer, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨different,_⟩ | ⟨different,_⟩) <;> exact different
    · intro different
      obtain ⟨p,on_rows,_⟩ := share a b different.symm
      by_cases inside : p ∈ S
      · exact Or.inl ⟨different,p,inside,on_rows⟩
      · exact Or.inr ⟨different,p,inside,on_rows⟩
  have count := Finset.card_union_of_disjoint separated
  rw [total, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin, inner_four] at count
  omega

theorem normalize_first_neighbors (neighbors : Finset (Fin 8)) (size : neighbors.card = 3)
    (zero_outside : 0 ∉ neighbors) :
    ∃ e : Equiv.Perm (Fin 8), e 0 = 0 ∧
      ∀ j, e j ∈ neighbors ↔ j = 1 ∨ j = 2 ∨ j = 3 := by
  let wanted : Finset (Fin 8) := {1, 2, 3}
  have wanted_size : wanted.card = 3 := by decide
  have zero_missing : 0 ∉ wanted := by decide
  let ew : ↥wanted ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using wanted_size)
  let en : ↥neighbors ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using size)
  let adjust : ↥wanted ≃ ↥neighbors := ew.trans en.symm
  let initial : Equiv.Perm (Fin 8) := adjust.extendSubtype
  have image_eq (j : Fin 8) : initial j ∈ neighbors ↔ j ∈ wanted := by
    by_cases inside : j ∈ wanted
    · exact iff_of_true (Equiv.extendSubtype_mem adjust _ inside) inside
    · exact iff_of_false (Equiv.extendSubtype_not_mem adjust _ inside) inside
  have initialZero : initial 0 ∉ neighbors := fun inside => zero_missing ((image_eq 0).mp inside)
  let restore := Equiv.swap (initial 0) 0
  have restore_mem (j : Fin 8) : restore j ∈ neighbors ↔ j ∈ neighbors := by
    by_cases first : j = initial 0
    · subst j
      simpa only [restore, Equiv.swap_apply_left] using iff_of_false zero_outside initialZero
    by_cases second : j = 0
    · subst j
      simpa only [restore, Equiv.swap_apply_right] using iff_of_false initialZero zero_outside
    rw [show restore j = j from Equiv.swap_apply_of_ne_of_ne first second]
  refine ⟨initial.trans restore, Equiv.swap_apply_left _ _, ?_⟩
  intro j
  change restore (initial j) ∈ neighbors ↔ _
  rw [restore_mem, image_eq]
  simp [wanted]

end WeightSixteenCubicGeometry

namespace FiniteSearchMasks

variable {α : Type}

def bitMask (xs : List α) (chosen : α → Bool) : Nat :=
  (xs.zipIdx.map fun (x, i) => if chosen x then 2^i else 0).foldr Nat.lor 0

lemma foldr_or_testBit (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ n ∈ words, n.testBit i = true := by
  induction words with
  | nil => simp
  | cons word words ih =>
      change (word ||| words.foldr Nat.lor 0).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with bit | ⟨n, hn, bit⟩
        · exact ⟨word, Or.inl rfl, bit⟩
        · exact ⟨n, Or.inr hn, bit⟩
      · rintro ⟨n, h, bit⟩
        rcases h with rfl | mem
        · exact Or.inl bit
        · exact Or.inr ⟨n, mem, bit⟩

theorem bitMask_testBit (xs : List α) (chosen : α → Bool) (i : Nat) :
    (bitMask xs chosen).testBit i = true ↔ ∃ x, xs[i]? = some x ∧ chosen x = true := by
  rw [bitMask, foldr_or_testBit]
  constructor
  · rintro ⟨n, member, set⟩
    obtain ⟨⟨x,j⟩, hxj, rfl⟩ := List.mem_map.mp member
    cases hx : chosen x with
    | false => simp [hx] at set
    | true =>
      have ji : j = i := by simpa [hx, Nat.testBit_two_pow] using set
      subst j
      exact ⟨x, List.mk_mem_zipIdx_iff_getElem?.mp hxj, hx⟩
  · rintro ⟨x, hx, chosen_x⟩
    refine ⟨2^i, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    exact ⟨(x,i), List.mk_mem_zipIdx_iff_getElem?.mpr hx, by simp [chosen_x]⟩

lemma bitMask_getElem_testBit (xs : List α) (chosen : α → Bool) (i : ℕ) (in_list : i < xs.length) :
    (bitMask xs chosen).testBit i = chosen xs[i] := by
  apply Bool.eq_iff_iff.mpr
  rw [bitMask_testBit]
  simp [List.getElem?_eq_getElem in_list]

end FiniteSearchMasks


namespace WeightSixteenCubicGraphs

open Finset FiniteSearchMasks

def rowMasks : List Nat := [0x7f, 0x1f81, 0x3e082, 0x3c2104, 0x1c44208, 0x6488410, 0xa910820, 0xd221040]

def rowMask (v : Nat) : Nat := rowMasks[v]?.getD 0

def offset (v : Fin 7) : Nat := ([0,7,13,18,22,25,27] : List Nat)[v.val]?.getD 0

def width (v : Fin 7) : Nat := 7-v.val

def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | steps+1, word => if word = 0 then 0 else
    1 + countBits steps (word ^^^ 2^word.log2)

def degree (code v : Nat) : Nat := countBits 7 (code &&& rowMask v)

def edgeIndex (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  a * (15-a)/2 + (b-a-1)


lemma countBits_correct (steps w : Nat) (S : Finset Nat) (size : S.card ≤ steps)
    (agreement : ∀ i, w.testBit i = true ↔ i ∈ S) : countBits steps w = S.card := by
  induction steps generalizing w S with
  | zero =>
    have empty : S.card = 0 := by omega
    exact empty.symm
  | succ n ih =>
    by_cases zero : w = 0
    · have none : S = ∅ := by
        ext i
        rw [← agreement i, zero]
        simp
      simp [countBits, zero, none]
    · let i := w.log2
      have chosen : i ∈ S := (agreement i).mp (Nat.testBit_log2 zero)
      have bit : w.testBit i = true := Nat.testBit_log2 zero
      have size' : (S.erase i).card ≤ n := by
        rw [Finset.card_erase_of_mem chosen]
        omega
      have reduced (j : Nat) :
          (w ^^^ 2^i).testBit j = true ↔ j ∈ S.erase i := by
        by_cases same : j = i
        · subst j
          simp [Nat.testBit_xor, Nat.testBit_two_pow_self, bit]
        · simp only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm same, decide_false,
            Bool.xor_false, Finset.mem_erase]
          exact (agreement j).trans ⟨fun hit => ⟨same,hit⟩, fun hit => hit.2⟩
      simp only [countBits, if_neg zero]
      change 1 + countBits n (w ^^^ 2^i) = _
      rw [ih _ _ size' reduced, Finset.card_erase_of_mem chosen]
      have positive := Finset.card_pos.mpr ⟨i, chosen⟩
      omega

def pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]

lemma pairs_size : pairs.length = 28 := rfl

def pairOf (i : Fin 28) : Fin 8 × Fin 8 := pairs[i.val]'(by simpa only [pairs_size] using i.isLt)

def neighbor (v : Fin 8) (i : Fin 28) : Fin 8 :=
  if (pairOf i).1 = v then (pairOf i).2 else (pairOf i).1

def encode (g : Fin 8 → Fin 8 → Bool) : Nat :=
  bitMask pairs (fun (v,w) => g v w)

lemma encode_bit (g : Fin 8 → Fin 8 → Bool) (i : Fin 28) :
    (encode g).testBit i.val = g (pairOf i).1 (pairOf i).2 := by
  unfold encode pairOf
  exact bitMask_getElem_testBit _ _ _ (by simpa only [pairs_size] using i.isLt)

lemma encode_off (g : Fin 8 → Fin 8 → Bool) (i : Nat) (outside : 28 ≤ i) :
    (encode g).testBit i = false := by
  by_contra on
  have yes : (encode g).testBit i = true := Bool.eq_true_of_not_eq_false on
  obtain ⟨edge, found, _⟩ := (bitMask_testBit _ _ _).mp yes
  rw [List.getElem?_eq_none (by simpa only [pairs_size] using outside)] at found
  contradiction

lemma encode_bound (g : Fin 8 → Fin 8 → Bool) : encode g < 2^28 := by
  by_cases empty : encode g = 0
  · simp [empty]
  · apply (Nat.log2_lt empty).mp
    by_contra outside
    exact Bool.false_ne_true ((encode_off g _ (Nat.le_of_not_gt outside)).symm.trans (Nat.testBit_log2 empty))

lemma row_bit : ∀ (v : Fin 8) (i : Fin 28),
    (rowMask v.val).testBit i.val = decide ((pairOf i).1 = v ∨ (pairOf i).2 = v) := by decide +kernel

lemma index_of_pair (v : Fin 8) (i : Fin 28)
    (joined : (pairOf i).1 = v ∨ (pairOf i).2 = v) :
    edgeIndex v.val (neighbor v i).val = i.val := by
  have Numeric : ∀ v : Fin 8, ∀ i : Fin 28, (pairOf i).1 = v ∨ (pairOf i).2 = v →
      edgeIndex v.val (neighbor v i).val = i.val := by decide +kernel
  exact Numeric v i joined

lemma neighbor_different (v : Fin 8) (i : Fin 28) : neighbor v i ≠ v := by
  have Numeric : ∀ v : Fin 8, ∀ i : Fin 28, neighbor v i ≠ v := by decide +kernel
  exact Numeric v i

lemma ordered_pair_exists (v w : Fin 8) (different : v ≠ w) :
    ∃ i : Fin 28, pairOf i = (v,w) ∨ pairOf i = (w,v) := by
  have Numeric : ∀ v w : Fin 8, v ≠ w →
      ∃ i : Fin 28, pairOf i = (v,w) ∨ pairOf i = (w,v) := by decide +kernel
  exact Numeric v w different

lemma relevant_bit (g : Fin 8 → Fin 8 → Bool) (symm : ∀ x y, g x y = g y x)
    (v : Fin 8) (i : Fin 28) :
    (encode g &&& rowMask v.val).testBit i.val = true ↔
      ((pairOf i).1 = v ∨ (pairOf i).2 = v) ∧ g v (neighbor v i) = true := by
  rw [Nat.testBit_land, encode_bit, row_bit, Bool.and_eq_true, decide_eq_true_eq, and_comm]
  by_cases first : (pairOf i).1 = v
  · simp [first, neighbor]
  by_cases second : (pairOf i).2 = v
  · simp [first, second, neighbor, symm (pairOf i).1 v]
  · simp [first, second]

theorem degree_encode (g : Fin 8 → Fin 8 → Bool) (symm : ∀ x y, g x y = g y x)
    (loopfree : ∀ x, g x x = false) (v : Fin 8) :
    degree (encode g) v.val = (Finset.univ.filter fun w => g v w = true).card := by
  classical
  let bs : Finset (Fin 28) := Finset.univ.filter fun i => (encode g &&& rowMask v.val).testBit i.val = true
  let ns : Finset (Fin 8) := Finset.univ.filter fun w => g v w = true
  have chosen (i : Fin 28) : i ∈ bs ↔
      ((pairOf i).1 = v ∨ (pairOf i).2 = v) ∧ g v (neighbor v i) = true := by
    simpa only [bs, Finset.mem_filter, Finset.mem_univ, true_and] using relevant_bit g symm v i
  have card_eq : bs.card = ns.card := by
    apply Finset.card_bij (fun i _ => neighbor v i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((chosen i).mp hi).2⟩
    · intro i hi j hj eq
      apply Fin.ext
      have left := index_of_pair v i ((chosen i).mp hi).1
      have right := index_of_pair v j ((chosen j).mp hj).1
      rw [eq] at left
      exact left.symm.trans right
    · intro w hw
      have active := (Finset.mem_filter.mp hw).2
      have different : v ≠ w := by intro same; subst w; simp [loopfree] at active
      obtain ⟨i, orientation⟩ := ordered_pair_exists v w different
      obtain first | second := orientation
      · have pick : neighbor v i = w := by simp [neighbor, first]
        exact ⟨i,(chosen i).mpr ⟨Or.inl (by rw [first]), by rwa [pick]⟩,pick⟩
      · have pick : neighbor v i = w := by simp [neighbor, second, different.symm]
        exact ⟨i,(chosen i).mpr ⟨Or.inr (by rw [second]), by rwa [pick]⟩,pick⟩
  let selected := bs.image Fin.val
  have count_selected : selected.card = bs.card := Finset.card_image_of_injective bs Fin.val_injective
  have bounded : ns.card ≤ 7 := by
    have inside : ns ⊆ Finset.univ.erase v := by
      intro w hw
      refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
      intro same
      subst w
      have active := (Finset.mem_filter.mp hw).2
      simp [loopfree] at active
    have count := Finset.card_le_card inside
    rwa [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at count
  have agreement (i : Nat) :
      (encode g &&& rowMask v.val).testBit i = true ↔ i ∈ selected := by
    by_cases within : i < 28
    · constructor
      · intro hit
        exact Finset.mem_image.mpr ⟨⟨i,within⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, rfl⟩
      · intro hi
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hj).2
    · have bit := encode_off g i (Nat.le_of_not_gt within)
      have absent : i ∉ selected := by
        intro hi
        obtain ⟨j,_,same⟩ := Finset.mem_image.mp hi
        exact within (same ▸ j.isLt)
      simp [bit, absent]
  have values := countBits_correct 7 (encode g &&& rowMask v.val) selected
    (count_selected.trans card_eq ▸ bounded) agreement
  change countBits 7 (encode g &&& rowMask v.val) = ns.card
  exact values.trans (count_selected.trans card_eq)

end WeightSixteenCubicGraphs

namespace WeightSixteenCubicGraphs

open Finset WeightSixteenCubicGeometry

lemma first_pairs : ∀ i : Fin 7,
    (pairOf ⟨i.val, by omega⟩).1 = 0 ∧
    ((7 : Nat).testBit i.val = true ↔
      (pairOf ⟨i.val, by omega⟩).2 = 1 ∨
      (pairOf ⟨i.val, by omega⟩).2 = 2 ∨
      (pairOf ⟨i.val, by omega⟩).2 = 3) := by decide +kernel

lemma first_row_encoding (g : Fin 8 → Fin 8 → Bool)
    (row : ∀ j, g 0 j = true ↔ j = 1 ∨ j = 2 ∨ j = 3) :
    encode g &&& (2^7-1) = 7 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases within : j < 7
  · let i : Fin 7 := ⟨j,within⟩
    let k : Fin 28 := ⟨j,by omega⟩
    rw [Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_true within, Bool.and_true]
    change (encode g).testBit k.val = (7:Nat).testBit i.val
    rw [encode_bit, (first_pairs i).1]
    exact Bool.eq_iff_iff.mpr ((row (pairOf k).2).trans (first_pairs i).2.symm)
  · have zero := Nat.testBit_lt_two_pow ((show 7 < 2^7 by decide).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt within)))
    simp only [Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_false within,
      Bool.and_false, zero]

noncomputable def exteriorGraph
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8))
    (a b : Fin 8) : Bool :=
  decide (e b ∈ outer A S (e a))

lemma exteriorGraph_symm
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8)) :
    ∀ a b, exteriorGraph A S e a b = exteriorGraph A S e b a := by
  intro a b
  apply Bool.eq_iff_iff.mpr
  simpa only [exteriorGraph, decide_eq_true_eq] using outer_symm A S (e a) (e b)

lemma exteriorGraph_loopfree
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8)) :
    ∀ a, exteriorGraph A S e a a = false := by
  intro a
  exact decide_eq_false (outer_irrefl A S (e a))

lemma exteriorGraph_degree
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111)) (e : Equiv.Perm (Fin 8)) (a : Fin 8) :
    (Finset.univ.filter fun b => exteriorGraph A S e a b = true).card =
      (outer A S (e a)).card := by
  apply Finset.card_bij (fun b _ => e b)
  · intro b hb
    exact of_decide_eq_true (Finset.mem_filter.mp hb).2
  · intro b _ c _ equal
    exact e.injective equal
  · intro b hb
    refine ⟨e.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,e.apply_symm_apply b⟩
    simp [exteriorGraph, hb]

theorem encode_exterior_normalized
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4) :
    ∃ e : Equiv.Perm (Fin 8), e 0 = 0 ∧
      (encode (exteriorGraph A S e) &&& (2^7-1) = 7) ∧
      ∀ v < 8, degree (encode (exteriorGraph A S e)) v = 3 := by
  have actual := exterior_cubic A S share degree_two line_four
  obtain ⟨e, fixed, across⟩ := normalize_first_neighbors (outer A S 0) (actual 0) (outer_irrefl A S 0)
  have row (j : Fin 8) : exteriorGraph A S e 0 j = true ↔ j = 1 ∨ j = 2 ∨ j = 3 := by
    simpa only [exteriorGraph, decide_eq_true_eq, fixed] using across j
  refine ⟨e,fixed,first_row_encoding _ row,?_⟩
  intro v small
  let j : Fin 8 := ⟨v,small⟩
  change degree (encode (exteriorGraph A S e)) j.val = 3
  rw [degree_encode _ (exteriorGraph_symm A S e) (exteriorGraph_loopfree A S e),
    exteriorGraph_degree]
  exact actual (e j)

end WeightSixteenCubicGraphs

namespace WeightSixteenCubicGraphs

def low (word bits : Nat) : Nat := word &&& (2^bits-1)

def stage (v : Fin 7) (previous : List Nat) : List Nat :=
  previous.flatMap fun old => (List.range (2^width v)).filterMap fun piece =>
    let child := old ||| (piece <<< offset v)
    if degree child v.val = 3 then some child else none

def enumerate : List Nat :=
  (stage 6 (stage 5 (stage 4 (stage 3 (stage 2 (stage 1 [7])))))).filter fun w => degree w 7 = 3

lemma mask_length (v : Fin 7) : rowMask v.val < 2^(offset v + width v) := by
  fin_cases v <;> decide

lemma low_full (w n : Nat) (range : w < 2^n) : low w n = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i<n
  · simp only [low, Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_true inside, Bool.and_true]
  · have blank := Nat.testBit_lt_two_pow (range.trans_le
       (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt inside)))
    simp only [low, Nat.testBit_land, blank, Bool.false_and]

lemma low_preserves_degree (w : Nat) (v : Fin 7) :
    degree (low w (offset v + width v)) v.val = degree w v.val := by
  have agree : low w (offset v + width v) &&& rowMask v.val = w &&& rowMask v.val := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases inside : i < offset v + width v
    · simp only [low, Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_true inside, Bool.and_true]
    · have blank := Nat.testBit_lt_two_pow ((mask_length v).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt inside)))
      simp only [Nat.testBit_land, blank, Bool.and_false]
  unfold degree
  rw [agree]

lemma low_extend (w offset width : Nat) :
    low w offset ||| (low (w >>> offset) width <<< offset) = low w (offset+width) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [low, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases lower : i<offset
  · have past : ¬ offset ≤ i := by omega
    have inside : i<offset+width := by omega
    simp [lower,past,inside]
  · have reached : offset ≤ i := by omega
    have same : i-offset+offset = i := Nat.sub_add_cancel reached
    have next : i - offset < width ↔ i < offset + width := by omega
    simp [lower,reached,next]

lemma stage_complete (w : Nat) (v : Fin 7) (nodes : List Nat)
    (previous : low w (offset v) ∈ nodes) (good : degree w v.val = 3) :
    low w (offset v + width v) ∈ stage v nodes := by
  unfold stage
  apply List.mem_flatMap.mpr
  refine ⟨low w (offset v), previous, List.mem_filterMap.mpr ⟨low (w >>> offset v) (width v), ?_, ?_⟩⟩
  · apply List.mem_range.mpr
    exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
  · rw [low_extend]
    dsimp only
    rw [low_preserves_degree, good, if_pos rfl]

lemma enumerate_complete (w : Nat) (small : w < 2^28)
    (normal : low w 7 = 7) (cubic : ∀ v < 8, degree w v = 3) : w ∈ enumerate := by
  have initial : low w (offset 1) ∈ [7] := by
    change low w 7 ∈ [7]
    simp [normal]
  have one := stage_complete w 1 _ initial (cubic 1 (by decide))
  have two := stage_complete w 2 _ one (cubic 2 (by decide))
  have three := stage_complete w 3 _ two (cubic 3 (by decide))
  have four := stage_complete w 4 _ three (cubic 4 (by decide))
  have five := stage_complete w 5 _ four (cubic 5 (by decide))
  have six := stage_complete w 6 _ five (cubic 6 (by decide))
  unfold enumerate
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true (cubic 7 (by decide))⟩
  change low w 28 ∈ _ at six
  simpa only [low_full w 28 small] using six

def edges : List (Nat × Nat) :=
  (List.range 8).flatMap fun a => ((List.range 8).filter fun b => a < b).map fun b => (a,b)

def imageOf (packed i : Nat) : Nat := ((packed >>> (3*i)) &&& 7)

def moveWord (word move : Nat) : Nat :=
  (edges.zipIdx.map fun (e,j) =>
    if word.testBit j then 2^edgeIndex (imageOf move e.1) (imageOf move e.2) else 0).foldr Nat.lor 0

def representatives : List Nat := [0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187]

inductive EntryTable where
  | leaf (row : Nat × (Nat × Nat))
  | node (pivot : Nat) (left right : EntryTable)

def EntryTable.find (key : Nat) : EntryTable → Nat × (Nat × Nat)
  | .leaf row => row
  | .node pivot left right => if key<pivot then left.find key else right.find key

def EntryTable.all (test : Nat × (Nat × Nat) → Bool) : EntryTable → Bool
  | .leaf row => test row
  | .node _ left right => left.all test && right.all test

lemma EntryTable.find_correct (table : EntryTable) (test : Nat × (Nat × Nat) → Bool)
    (accepted : table.all test = true) (key : Nat) : test (table.find key) = true := by
  induction table with
  | leaf row => exact accepted
  | node pivot left right ihLeft ihRight =>
    change (left.all test && right.all test) = true at accepted
    simp only [Bool.and_eq_true] at accepted
    obtain ⟨goodLeft, goodRight⟩ := accepted
    by_cases low : key < pivot
    · simpa only [EntryTable.find, if_pos low] using ihLeft goodLeft
    · simpa only [EntryTable.find, if_neg low] using ihRight goodRight

def records : EntryTable := (.node 0xa668a07 (.node 0x6e24907 (.node 0x4f24c07 (.node 0x3a8d807 (.node 0x3659807 (.node 0x2ea5807 (.node 0x1f19407 (.node 0x1e99807 (.node 0x1db1407 (.leaf (0x1da9807, (0, 0xfac688))) (.leaf (0x1db1407, (0, 0xf74688)))) (.node 0x1eb0c07 (.leaf (0x1e99807, (0, 0xdec688))) (.leaf (0x1eb0c07, (0, 0xbf4688))))) (.node 0x2e69807 (.node 0x1f28c07 (.leaf (0x1f19407, (0, 0xd7c688))) (.leaf (0x1f28c07, (0, 0xbbc688)))) (.node 0x2e71407 (.leaf (0x2e69807, (1, 0xfac688))) (.leaf (0x2e71407, (1, 0xf74688)))))) (.node 0x34f1807 (.node 0x2f25407 (.node 0x2eb1207 (.leaf (0x2ea5807, (1, 0xfa5688))) (.leaf (0x2eb1207, (1, 0xf66688)))) (.node 0x2f29207 (.leaf (0x2f25407, (1, 0xf35688))) (.leaf (0x2f29207, (1, 0xf2e688))))) (.node 0x3571407 (.node 0x3569807 (.leaf (0x34f1807, (1, 0x6acdc1))) (.leaf (0x3569807, (2, 0xfac688)))) (.node 0x35a5807 (.leaf (0x3571407, (2, 0xfac650))) (.node 0x35b1207 (.leaf (0x35a5807, (3, 0xfac688))) (.leaf (0x35b1207, (3, 0xfac650)))))))) (.node 0x3728a07 (.node 0x370d807 (.node 0x3695807 (.node 0x3670c07 (.leaf (0x3659807, (3, 0xde5688))) (.leaf (0x3670c07, (3, 0xde5650)))) (.node 0x36b0a07 (.leaf (0x3695807, (2, 0xde5688))) (.leaf (0x36b0a07, (2, 0xde5650))))) (.node 0x3719207 (.node 0x3715407 (.leaf (0x370d807, (1, 0x6acf81))) (.leaf (0x3715407, (2, 0xfac2d0)))) (.node 0x3724c07 (.leaf (0x3719207, (3, 0xfac2d0))) (.leaf (0x3724c07, (3, 0xde52d0)))))) (.node 0x3969407 (.node 0x38e9807 (.node 0x3730607 (.leaf (0x3728a07, (2, 0xde52d0))) (.leaf (0x3730607, (1, 0x6ace31)))) (.node 0x38f1407 (.leaf (0x38e9807, (2, 0xf74650))) (.leaf (0x38f1407, (2, 0xf74688))))) (.node 0x39a9207 (.node 0x39a5407 (.leaf (0x3969407, (1, 0x754dc1))) (.leaf (0x39a5407, (3, 0xf74688)))) (.node 0x3a59407 (.leaf (0x39a9207, (3, 0xf74650))) (.node 0x3a68c07 (.leaf (0x3a59407, (3, 0xd3d688))) (.leaf (0x3a68c07, (3, 0xd3d650))))))))) (.node 0x3e28907 (.node 0x3ca3807 (.node 0x3aa8a07 (.node 0x3a99207 (.node 0x3a95407 (.leaf (0x3a8d807, (2, 0xf742d0))) (.leaf (0x3a95407, (1, 0x754f81)))) (.node 0x3aa4c07 (.leaf (0x3a99207, (3, 0xf742d0))) (.leaf (0x3aa4c07, (3, 0xd3d2d0))))) (.node 0x3b0d407 (.node 0x3ab0607 (.leaf (0x3aa8a07, (1, 0x754e31))) (.leaf (0x3ab0607, (2, 0xd3d2d0)))) (.node 0x3b28607 (.leaf (0x3b0d407, (2, 0xd3d688))) (.leaf (0x3b28607, (2, 0xd3d650)))))) (.node 0x3da1087 (.node 0x3d23407 (.node 0x3cb1107 (.leaf (0x3ca3807, (3, 0x2ee9c2))) (.leaf (0x3cb1107, (3, 0x2ee83a)))) (.node 0x3d29107 (.leaf (0x3d23407, (3, 0x35e9c2))) (.leaf (0x3d29107, (3, 0x35e83a))))) (.node 0x3e13407 (.node 0x3e0b807 (.leaf (0x3da1087, (4, 0xfac688))) (.leaf (0x3e0b807, (3, 0x2eef02)))) (.node 0x3e19107 (.leaf (0x3e13407, (3, 0x35ef02))) (.node 0x3e22c07 (.leaf (0x3e19107, (4, 0xfac4c8))) (.leaf (0x3e22c07, (4, 0xfac458)))))))) (.node 0x4da5807 (.node 0x3f09087 (.node 0x3e91087 (.node 0x3e30507 (.leaf (0x3e28907, (3, 0x35ee22))) (.leaf (0x3e30507, (3, 0x2eee22)))) (.node 0x3ea0887 (.leaf (0x3e91087, (3, 0x35e13a))) (.leaf (0x3ea0887, (3, 0x35e1e2))))) (.node 0x4cf1807 (.node 0x3f20487 (.leaf (0x3f09087, (3, 0x2ee13a))) (.leaf (0x3f20487, (3, 0x2ee1e2)))) (.node 0x4d69807 (.leaf (0x4cf1807, (1, 0x6a5dc1))) (.node 0x4d71407 (.leaf (0x4d69807, (3, 0xfa5688))) (.leaf (0x4d71407, (3, 0xfa5650))))))) (.node 0x4e95807 (.node 0x4e59807 (.node 0x4db1207 (.leaf (0x4da5807, (2, 0xfa5688))) (.leaf (0x4db1207, (2, 0xfa5650)))) (.node 0x4e70c07 (.leaf (0x4e59807, (2, 0xdec688))) (.leaf (0x4e70c07, (2, 0xdec650))))) (.node 0x4f0d807 (.node 0x4eb0a07 (.leaf (0x4e95807, (3, 0xdec688))) (.leaf (0x4eb0a07, (3, 0xdec650)))) (.node 0x4f15407 (.leaf (0x4f0d807, (1, 0x6a5f81))) (.node 0x4f19207 (.leaf (0x4f15407, (3, 0xfa52d0))) (.leaf (0x4f19207, (2, 0xfa52d0)))))))))) (.node 0x5e12c07 (.node 0x59a8a07 (.node 0x5718a07 (.node 0x5570c07 (.node 0x4f30607 (.node 0x4f28a07 (.leaf (0x4f24c07, (2, 0xdec2d0))) (.leaf (0x4f28a07, (3, 0xdec2d0)))) (.node 0x5559807 (.leaf (0x4f30607, (1, 0x6a5e31))) (.leaf (0x5559807, (1, 0xdec688))))) (.node 0x55b0a07 (.node 0x5595807 (.leaf (0x5570c07, (1, 0xbf4688))) (.leaf (0x5595807, (1, 0xde5688)))) (.node 0x5714c07 (.leaf (0x55b0a07, (1, 0xbe6688))) (.leaf (0x5714c07, (1, 0x9f5688)))))) (.node 0x5968c07 (.node 0x58f0c07 (.node 0x58d9807 (.leaf (0x5718a07, (1, 0x9ee688))) (.leaf (0x58d9807, (2, 0xbf4650)))) (.node 0x5959407 (.leaf (0x58f0c07, (2, 0xbf4688))) (.leaf (0x5959407, (3, 0x9bd650))))) (.node 0x5995407 (.node 0x598d807 (.leaf (0x5968c07, (3, 0x9bd688))) (.leaf (0x598d807, (2, 0xbf42d0)))) (.node 0x5999207 (.leaf (0x5995407, (3, 0x9bd2d0))) (.node 0x59a4c07 (.leaf (0x5999207, (1, 0xad4e31))) (.leaf (0x59a4c07, (1, 0xad4f81)))))))) (.node 0x5cb0907 (.node 0x5a98a07 (.node 0x5a58c07 (.node 0x59b0607 (.leaf (0x59a8a07, (3, 0xbf42d0))) (.leaf (0x59b0607, (2, 0x9bd2d0)))) (.node 0x5a94c07 (.leaf (0x5a58c07, (1, 0xad4dc1))) (.leaf (0x5a94c07, (3, 0xbf4688))))) (.node 0x5b18607 (.node 0x5b0cc07 (.leaf (0x5a98a07, (3, 0xbf4650))) (.leaf (0x5b0cc07, (2, 0x9bd688)))) (.node 0x5c93807 (.leaf (0x5b18607, (2, 0x9bd650))) (.leaf (0x5c93807, (3, 0x66e9c2)))))) (.node 0x5d22c07 (.node 0x5d13407 (.node 0x5d0b807 (.leaf (0x5cb0907, (3, 0x66e83a))) (.leaf (0x5d0b807, (3, 0x66ef02)))) (.node 0x5d19107 (.leaf (0x5d13407, (4, 0xdec458))) (.leaf (0x5d19107, (3, 0xa5ee22))))) (.node 0x5d30507 (.node 0x5d28907 (.leaf (0x5d22c07, (3, 0xa5ef02))) (.leaf (0x5d28907, (4, 0xdec4c8)))) (.node 0x5d91087 (.leaf (0x5d30507, (3, 0x66ee22))) (.node 0x5da0887 (.leaf (0x5d91087, (3, 0xa5e1e2))) (.leaf (0x5da0887, (3, 0xa5e13a))))))))) (.node 0x6a55407 (.node 0x6670a07 (.node 0x5f10487 (.node 0x5e90887 (.node 0x5e18907 (.leaf (0x5e12c07, (3, 0xa5e9c2))) (.leaf (0x5e18907, (3, 0xa5e83a)))) (.node 0x5f08887 (.leaf (0x5e90887, (4, 0xdec688))) (.leaf (0x5f08887, (3, 0x66e13a))))) (.node 0x6571207 (.node 0x6565807 (.leaf (0x5f10487, (3, 0x66e1e2))) (.leaf (0x6565807, (0, 0xfa5688)))) (.node 0x6655807 (.leaf (0x6571207, (0, 0xf66688))) (.leaf (0x6655807, (0, 0xde5688)))))) (.node 0x68f1207 (.node 0x6724a07 (.node 0x6715207 (.leaf (0x6670a07, (0, 0xbe6688))) (.leaf (0x6715207, (0, 0xd67688)))) (.node 0x68e5807 (.leaf (0x6724a07, (0, 0xba7688))) (.leaf (0x68e5807, (2, 0xf66650))))) (.node 0x6969207 (.node 0x6965407 (.leaf (0x68f1207, (2, 0xf66688))) (.leaf (0x6965407, (3, 0xf66650)))) (.node 0x69a5207 (.leaf (0x6969207, (3, 0xf66688))) (.node 0x6a4d807 (.leaf (0x69a5207, (1, 0x762dc1))) (.leaf (0x6a4d807, (2, 0xf662d0)))))))) (.node 0x6c63807 (.node 0x6a70607 (.node 0x6a64c07 (.node 0x6a59207 (.leaf (0x6a55407, (3, 0xf662d0))) (.leaf (0x6a59207, (1, 0x762f81)))) (.node 0x6a68a07 (.leaf (0x6a64c07, (1, 0x762e31))) (.leaf (0x6a68a07, (3, 0xd2f2d0))))) (.node 0x6aa4a07 (.node 0x6a95207 (.leaf (0x6a70607, (2, 0xd2f2d0))) (.leaf (0x6a95207, (3, 0xd2f688)))) (.node 0x6b0d207 (.leaf (0x6aa4a07, (3, 0xd2f650))) (.node 0x6b24607 (.leaf (0x6b0d207, (2, 0xd2f688))) (.leaf (0x6b24607, (2, 0xd2f650))))))) (.node 0x6d61087 (.node 0x6d23207 (.node 0x6c71107 (.leaf (0x6c63807, (3, 0x2f59c2))) (.leaf (0x6c71107, (3, 0x2f583a)))) (.node 0x6d25107 (.leaf (0x6d23207, (3, 0x3739c2))) (.leaf (0x6d25107, (3, 0x37383a))))) (.node 0x6e13207 (.node 0x6e07807 (.leaf (0x6d61087, (4, 0xfa5688))) (.leaf (0x6e07807, (3, 0x2f5f02)))) (.node 0x6e15107 (.leaf (0x6e13207, (3, 0x373f02))) (.node 0x6e22a07 (.leaf (0x6e15107, (4, 0xfa54c8))) (.leaf (0x6e22a07, (4, 0xfa5458))))))))))) (.node 0x7a90287 (.node 0x7704887 (.node 0x7258a07 (.node 0x714d807 (.node 0x6f05087 (.node 0x6e51087 (.node 0x6e30307 (.leaf (0x6e24907, (3, 0x373e22))) (.leaf (0x6e30307, (3, 0x2f5e22)))) (.node 0x6e60887 (.leaf (0x6e51087, (3, 0x37313a))) (.leaf (0x6e60887, (3, 0x3731e2))))) (.node 0x70d5807 (.node 0x6f20287 (.leaf (0x6f05087, (3, 0x2f513a))) (.leaf (0x6f20287, (3, 0x2f51e2)))) (.node 0x70f0a07 (.leaf (0x70d5807, (2, 0xbe6650))) (.leaf (0x70f0a07, (2, 0xbe6688)))))) (.node 0x7168a07 (.node 0x7159207 (.node 0x7155407 (.leaf (0x714d807, (2, 0xbe62d0))) (.leaf (0x7155407, (1, 0xae2e31)))) (.node 0x7164c07 (.leaf (0x7159207, (3, 0x9af2d0))) (.leaf (0x7164c07, (3, 0xbe62d0))))) (.node 0x7195207 (.node 0x7170607 (.leaf (0x7168a07, (1, 0xae2f81))) (.leaf (0x7170607, (2, 0x9af2d0)))) (.node 0x71a4a07 (.leaf (0x7195207, (3, 0x9af650))) (.node 0x7254c07 (.leaf (0x71a4a07, (3, 0x9af688))) (.leaf (0x7254c07, (3, 0xbe6650)))))))) (.node 0x7515107 (.node 0x7453807 (.node 0x730ca07 (.node 0x7294a07 (.leaf (0x7258a07, (3, 0xbe6688))) (.leaf (0x7294a07, (1, 0xae2dc1)))) (.node 0x7314607 (.leaf (0x730ca07, (2, 0x9af688))) (.leaf (0x7314607, (2, 0x9af650))))) (.node 0x7507807 (.node 0x7470907 (.leaf (0x7453807, (3, 0x6759c2))) (.leaf (0x7470907, (3, 0x67583a)))) (.node 0x7513207 (.leaf (0x7507807, (3, 0x675f02))) (.leaf (0x7513207, (4, 0xde5458)))))) (.node 0x7551087 (.node 0x7524907 (.node 0x7522a07 (.leaf (0x7515107, (3, 0xa73e22))) (.leaf (0x7522a07, (3, 0xa73f02)))) (.node 0x7530307 (.leaf (0x7524907, (4, 0xde54c8))) (.leaf (0x7530307, (3, 0x675e22))))) (.node 0x7612a07 (.node 0x7560887 (.leaf (0x7551087, (3, 0xa731e2))) (.leaf (0x7560887, (3, 0xa7313a)))) (.node 0x7614907 (.leaf (0x7612a07, (3, 0xa739c2))) (.node 0x7650887 (.leaf (0x7614907, (3, 0xa7383a))) (.leaf (0x7650887, (4, 0xde5688))))))))) (.node 0x790b207 (.node 0x7887807 (.node 0x7859107 (.node 0x784b807 (.node 0x7710287 (.leaf (0x7704887, (3, 0x67513a))) (.leaf (0x7710287, (3, 0x6751e2)))) (.node 0x7853407 (.leaf (0x784b807, (1, 0xe1ab0e))) (.leaf (0x7853407, (3, 0x6705ec))))) (.node 0x7868907 (.node 0x7862c07 (.leaf (0x7859107, (3, 0x2f057c))) (.leaf (0x7862c07, (3, 0x2f05ec)))) (.node 0x7870507 (.leaf (0x7868907, (3, 0x67057c))) (.leaf (0x7870507, (1, 0xe1aa66)))))) (.node 0x78a4907 (.node 0x7895107 (.node 0x7893207 (.leaf (0x7887807, (1, 0xe1a94e))) (.leaf (0x7893207, (3, 0x6465ec)))) (.node 0x78a2a07 (.leaf (0x7895107, (3, 0x2c657c))) (.leaf (0x78a2a07, (3, 0x2c65ec))))) (.node 0x78d1087 (.node 0x78b0307 (.leaf (0x78a4907, (3, 0x64657c))) (.leaf (0x78b0307, (1, 0xe1a86e)))) (.node 0x78e0887 (.leaf (0x78d1087, (1, 0x6b8366))) (.node 0x7907407 (.leaf (0x78e0887, (1, 0x6b832e))) (.leaf (0x7907407, (3, 0x670eac)))))))) (.node 0x7a06c07 (.node 0x7928307 (.node 0x7922607 (.node 0x790d107 (.leaf (0x790b207, (3, 0x646eac))) (.leaf (0x790d107, (1, 0x6b8a66)))) (.node 0x7924507 (.leaf (0x7922607, (1, 0x6b8b0e))) (.leaf (0x7924507, (3, 0x646f54))))) (.node 0x7960487 (.node 0x7949087 (.leaf (0x7928307, (3, 0x670f54))) (.leaf (0x7949087, (3, 0x2c6abc)))) (.node 0x7985087 (.leaf (0x7960487, (3, 0x2c6bd4))) (.node 0x79a0287 (.leaf (0x7985087, (3, 0x2f0abc))) (.leaf (0x79a0287, (3, 0x2f0bd4))))))) (.node 0x7a14507 (.node 0x7a0c907 (.node 0x7a0aa07 (.leaf (0x7a06c07, (3, 0x2f0eac))) (.leaf (0x7a0aa07, (3, 0x2c6eac)))) (.node 0x7a12607 (.leaf (0x7a0c907, (1, 0x6b886e))) (.leaf (0x7a12607, (1, 0x6b894e))))) (.node 0x7a48887 (.node 0x7a18307 (.leaf (0x7a14507, (3, 0x2c6f54))) (.leaf (0x7a18307, (3, 0x2f0f54)))) (.node 0x7a50487 (.leaf (0x7a48887, (3, 0x646abc))) (.node 0x7a84887 (.leaf (0x7a50487, (3, 0x646bd4))) (.leaf (0x7a84887, (3, 0x670abc)))))))))) (.node 0x9658c07 (.node 0x8e95407 (.node 0x7e10187 (.node 0x7c22907 (.node 0x7b08287 (.node 0x7b04487 (.leaf (0x7a90287, (3, 0x670bd4))) (.leaf (0x7b04487, (1, 0xe1a366)))) (.node 0x7c13107 (.leaf (0x7b08287, (1, 0xe1a32e))) (.leaf (0x7c13107, (4, 0x7355c1))))) (.node 0x7d20187 (.node 0x7d03087 (.leaf (0x7c22907, (4, 0x8f55c1))) (.leaf (0x7d03087, (4, 0x735e81)))) (.node 0x7e02887 (.leaf (0x7d20187, (4, 0x735e11))) (.leaf (0x7e02887, (4, 0x8f5e81)))))) (.node 0x8da5407 (.node 0x8cf1407 (.node 0x8ce9807 (.leaf (0x7e10187, (4, 0x8f5e11))) (.leaf (0x8ce9807, (3, 0xf35650)))) (.node 0x8d69407 (.leaf (0x8cf1407, (3, 0xf35688))) (.leaf (0x8d69407, (1, 0x715dc1))))) (.node 0x8e59407 (.node 0x8da9207 (.leaf (0x8da5407, (2, 0xf35688))) (.leaf (0x8da9207, (2, 0xf35650)))) (.node 0x8e68c07 (.leaf (0x8e59407, (2, 0xd7c688))) (.node 0x8e8d807 (.leaf (0x8e68c07, (2, 0xd7c650))) (.leaf (0x8e8d807, (3, 0xf352d0)))))))) (.node 0x94f0c07 (.node 0x8eb0607 (.node 0x8ea4c07 (.node 0x8e99207 (.leaf (0x8e95407, (1, 0x715f81))) (.leaf (0x8e99207, (2, 0xf352d0)))) (.node 0x8ea8a07 (.leaf (0x8ea4c07, (2, 0xd7c2d0))) (.leaf (0x8ea8a07, (1, 0x715e31))))) (.node 0x8f28607 (.node 0x8f0d407 (.leaf (0x8eb0607, (3, 0xd7c2d0))) (.leaf (0x8f0d407, (3, 0xd7c688)))) (.node 0x94d9807 (.leaf (0x8f28607, (3, 0xd7c650))) (.leaf (0x94d9807, (3, 0x9f5650)))))) (.node 0x9595407 (.node 0x9568c07 (.node 0x9559407 (.leaf (0x94f0c07, (3, 0x9f5688))) (.leaf (0x9559407, (2, 0xbbc650)))) (.node 0x958d807 (.leaf (0x9568c07, (2, 0xbbc688))) (.leaf (0x958d807, (3, 0x9f52d0))))) (.node 0x95a4c07 (.node 0x9599207 (.leaf (0x9595407, (2, 0xbbc2d0))) (.leaf (0x9599207, (1, 0x8d5e31)))) (.node 0x95a8a07 (.leaf (0x95a4c07, (1, 0x8d5f81))) (.node 0x95b0607 (.leaf (0x95a8a07, (2, 0x9f52d0))) (.leaf (0x95b0607, (3, 0xbbc2d0))))))))) (.node 0x9d0b407 (.node 0x99a8607 (.node 0x9718607 (.node 0x9698a07 (.node 0x9694c07 (.leaf (0x9658c07, (1, 0x8d5dc1))) (.leaf (0x9694c07, (2, 0x9f5688)))) (.node 0x970cc07 (.leaf (0x9698a07, (2, 0x9f5650))) (.leaf (0x970cc07, (3, 0xbbc688))))) (.node 0x98e8c07 (.node 0x98d9407 (.leaf (0x9718607, (3, 0xbbc650))) (.leaf (0x98d9407, (1, 0xd7c688)))) (.node 0x998d407 (.leaf (0x98e8c07, (1, 0xbbc688))) (.leaf (0x998d407, (1, 0xd3d688)))))) (.node 0x9c93407 (.node 0x9a98607 (.node 0x9a8cc07 (.leaf (0x99a8607, (1, 0xb3e688))) (.leaf (0x9a8cc07, (1, 0x9bd688)))) (.node 0x9c8b807 (.leaf (0x9a98607, (1, 0x97e688))) (.leaf (0x9c8b807, (4, 0xd7c458))))) (.node 0x9ca2c07 (.node 0x9c99107 (.leaf (0x9c93407, (3, 0x74ef02))) (.leaf (0x9c99107, (3, 0xacee22)))) (.node 0x9ca8907 (.leaf (0x9ca2c07, (3, 0xacef02))) (.node 0x9cb0507 (.leaf (0x9ca8907, (3, 0x74ee22))) (.leaf (0x9cb0507, (4, 0xd7c4c8)))))))) (.node 0xa4e5807 (.node 0x9e0ac07 (.node 0x9d89087 (.node 0x9d28507 (.leaf (0x9d0b407, (3, 0x74e9c2))) (.leaf (0x9d28507, (3, 0x74e83a)))) (.node 0x9da0487 (.leaf (0x9d89087, (3, 0xace1e2))) (.leaf (0x9da0487, (3, 0xace13a))))) (.node 0x9e88887 (.node 0x9e18507 (.leaf (0x9e0ac07, (3, 0xace9c2))) (.leaf (0x9e18507, (3, 0xace83a)))) (.node 0x9e90487 (.leaf (0x9e88887, (3, 0x74e1e2))) (.node 0x9f08487 (.leaf (0x9e90487, (3, 0x74e13a))) (.leaf (0x9f08487, (4, 0xd7c688))))))) (.node 0xa5a5207 (.node 0xa565407 (.node 0xa4f1207 (.leaf (0xa4e5807, (3, 0xf2e650))) (.leaf (0xa4f1207, (3, 0xf2e688)))) (.node 0xa569207 (.leaf (0xa565407, (2, 0xf2e650))) (.leaf (0xa569207, (2, 0xf2e688))))) (.node 0xa655407 (.node 0xa64d807 (.leaf (0xa5a5207, (1, 0x72adc1))) (.leaf (0xa64d807, (3, 0xf2e2d0)))) (.node 0xa659207 (.leaf (0xa655407, (2, 0xf2e2d0))) (.node 0xa664c07 (.leaf (0xa659207, (1, 0x72af81))) (.leaf (0xa664c07, (1, 0x72ae31)))))))))))) (.node 0xcca2a07 (.node 0xb612607 (.node 0xb168607 (.node 0xae07407 (.node 0xaa4d407 (.node 0xa70d207 (.node 0xa695207 (.node 0xa670607 (.leaf (0xa668a07, (2, 0xd672d0))) (.leaf (0xa670607, (3, 0xd672d0)))) (.node 0xa6a4a07 (.leaf (0xa695207, (2, 0xd67688))) (.leaf (0xa6a4a07, (2, 0xd67650))))) (.node 0xa8e5407 (.node 0xa724607 (.leaf (0xa70d207, (3, 0xd67688))) (.leaf (0xa724607, (3, 0xd67650)))) (.node 0xa8e9207 (.leaf (0xa8e5407, (0, 0xf35688))) (.leaf (0xa8e9207, (0, 0xf2e688)))))) (.node 0xac63407 (.node 0xaa8d207 (.node 0xaa68607 (.leaf (0xaa4d407, (0, 0xd3d688))) (.leaf (0xaa68607, (0, 0xb3e688)))) (.node 0xaaa4607 (.leaf (0xaa8d207, (0, 0xd2f688))) (.leaf (0xaaa4607, (0, 0xb37688))))) (.node 0xaca3207 (.node 0xac69107 (.leaf (0xac63407, (3, 0x39d9c2))) (.leaf (0xac69107, (3, 0x39d83a)))) (.node 0xaca5107 (.leaf (0xaca3207, (3, 0x3ab9c2))) (.node 0xace1087 (.leaf (0xaca5107, (3, 0x3ab83a))) (.leaf (0xace1087, (4, 0xf35688)))))))) (.node 0xae85087 (.node 0xae24507 (.node 0xae0d107 (.node 0xae0b207 (.leaf (0xae07407, (3, 0x39df02))) (.leaf (0xae0b207, (3, 0x3abf02)))) (.node 0xae22607 (.leaf (0xae0d107, (4, 0xf354c8))) (.leaf (0xae22607, (4, 0xf35458))))) (.node 0xae49087 (.node 0xae28307 (.leaf (0xae24507, (3, 0x3abe22))) (.leaf (0xae28307, (3, 0x39de22)))) (.node 0xae60487 (.leaf (0xae49087, (3, 0x3ab13a))) (.leaf (0xae60487, (3, 0x3ab1e2)))))) (.node 0xb0d9207 (.node 0xb0cd807 (.node 0xaea0287 (.leaf (0xae85087, (3, 0x39d13a))) (.leaf (0xaea0287, (3, 0x39d1e2)))) (.node 0xb0d5407 (.leaf (0xb0cd807, (1, 0xb1ae31))) (.leaf (0xb0d5407, (2, 0xb3e2d0))))) (.node 0xb0e8a07 (.node 0xb0e4c07 (.leaf (0xb0d9207, (3, 0x9772d0))) (.leaf (0xb0e4c07, (3, 0xb3e2d0)))) (.node 0xb0f0607 (.leaf (0xb0e8a07, (2, 0x9772d0))) (.node 0xb14d407 (.leaf (0xb0f0607, (1, 0xb1af81))) (.leaf (0xb14d407, (2, 0xb3e650))))))))) (.node 0xb4a2a07 (.node 0xb44b807 (.node 0xb258607 (.node 0xb1a4607 (.node 0xb18d207 (.leaf (0xb168607, (2, 0xb3e688))) (.leaf (0xb18d207, (3, 0x977650)))) (.node 0xb24cc07 (.leaf (0xb1a4607, (3, 0x977688))) (.leaf (0xb24cc07, (3, 0xb3e650))))) (.node 0xb294607 (.node 0xb28ca07 (.leaf (0xb258607, (3, 0xb3e688))) (.leaf (0xb28ca07, (2, 0x977650)))) (.node 0xb30c607 (.leaf (0xb294607, (2, 0x977688))) (.leaf (0xb30c607, (1, 0xb1adc1)))))) (.node 0xb468907 (.node 0xb459107 (.node 0xb453407 (.leaf (0xb44b807, (3, 0x7885ec))) (.leaf (0xb453407, (1, 0xec2b0e)))) (.node 0xb462c07 (.leaf (0xb459107, (3, 0x39857c))) (.leaf (0xb462c07, (3, 0x3985ec))))) (.node 0xb487807 (.node 0xb470507 (.leaf (0xb468907, (1, 0xec2a66))) (.leaf (0xb470507, (3, 0x78857c)))) (.node 0xb493207 (.leaf (0xb487807, (3, 0x788eac))) (.node 0xb495107 (.leaf (0xb493207, (3, 0xc435ec))) (.leaf (0xb495107, (1, 0x7d0a66)))))))) (.node 0xb524507 (.node 0xb4e0887 (.node 0xb4b0307 (.node 0xb4a4907 (.leaf (0xb4a2a07, (1, 0x7d0b0e))) (.leaf (0xb4a4907, (3, 0xc4357c)))) (.node 0xb4d1087 (.leaf (0xb4b0307, (3, 0x788f54))) (.leaf (0xb4d1087, (3, 0x21eabc))))) (.node 0xb50b207 (.node 0xb507407 (.leaf (0xb4e0887, (3, 0x21ebd4))) (.leaf (0xb507407, (1, 0xec294e)))) (.node 0xb50d107 (.leaf (0xb50b207, (3, 0xc43eac))) (.node 0xb522607 (.leaf (0xb50d107, (3, 0x21e57c))) (.leaf (0xb522607, (3, 0x21e5ec))))))) (.node 0xb585087 (.node 0xb549087 (.node 0xb528307 (.leaf (0xb524507, (3, 0xc43f54))) (.leaf (0xb528307, (1, 0xec286e)))) (.node 0xb560487 (.leaf (0xb549087, (1, 0x7d0366))) (.leaf (0xb560487, (1, 0x7d032e))))) (.node 0xb606c07 (.node 0xb5a0287 (.leaf (0xb585087, (3, 0x398abc))) (.leaf (0xb5a0287, (3, 0x398bd4)))) (.node 0xb60aa07 (.leaf (0xb606c07, (3, 0x398eac))) (.node 0xb60c907 (.leaf (0xb60aa07, (1, 0x7d094e))) (.leaf (0xb60c907, (3, 0x21ef54)))))))))) (.node 0xc559207 (.node 0xb8c9087 (.node 0xb708287 (.node 0xb650487 (.node 0xb618307 (.node 0xb614507 (.leaf (0xb612607, (3, 0x21eeac))) (.leaf (0xb614507, (1, 0x7d086e)))) (.node 0xb648887 (.leaf (0xb618307, (3, 0x398f54))) (.leaf (0xb648887, (3, 0xc43abc))))) (.node 0xb690287 (.node 0xb684887 (.leaf (0xb650487, (3, 0xc43bd4))) (.leaf (0xb684887, (1, 0xec2366)))) (.node 0xb704487 (.leaf (0xb690287, (1, 0xec232e))) (.leaf (0xb704487, (3, 0x788abc)))))) (.node 0xb88b207 (.node 0xb868507 (.node 0xb84b407 (.leaf (0xb708287, (3, 0x788bd4))) (.leaf (0xb84b407, (3, 0x78d9c2)))) (.node 0xb887407 (.leaf (0xb868507, (3, 0x78d83a))) (.leaf (0xb887407, (3, 0x78df02))))) (.node 0xb8a2607 (.node 0xb88d107 (.leaf (0xb88b207, (4, 0xd3d458))) (.leaf (0xb88d107, (3, 0xb8be22)))) (.node 0xb8a4507 (.leaf (0xb8a2607, (3, 0xb8bf02))) (.node 0xb8a8307 (.leaf (0xb8a4507, (4, 0xd3d4c8))) (.leaf (0xb8a8307, (3, 0x78de22)))))))) (.node 0xbc22507 (.node 0xba48487 (.node 0xba0a607 (.node 0xb8e0487 (.leaf (0xb8c9087, (3, 0xb8b1e2))) (.leaf (0xb8e0487, (3, 0xb8b13a)))) (.node 0xba0c507 (.leaf (0xba0a607, (3, 0xb8b9c2))) (.leaf (0xba0c507, (3, 0xb8b83a))))) (.node 0xba88287 (.node 0xba84487 (.leaf (0xba48487, (4, 0xd3d688))) (.leaf (0xba84487, (3, 0x78d13a)))) (.node 0xbc0b107 (.leaf (0xba88287, (3, 0x78d1e2))) (.leaf (0xbc0b107, (4, 0x7a55c1)))))) (.node 0xbe08187 (.node 0xbca0187 (.node 0xbc83087 (.leaf (0xbc22507, (4, 0x99d5c1))) (.leaf (0xbc83087, (4, 0x7a5e81)))) (.node 0xbe02487 (.leaf (0xbca0187, (4, 0x7a5e11))) (.leaf (0xbe02487, (4, 0x99de81))))) (.node 0xc4f0a07 (.node 0xc4d5807 (.leaf (0xbe08187, (4, 0x99de11))) (.leaf (0xc4d5807, (3, 0x9ee650)))) (.node 0xc54d807 (.leaf (0xc4f0a07, (3, 0x9ee688))) (.node 0xc555407 (.leaf (0xc54d807, (3, 0x9ee2d0))) (.leaf (0xc555407, (1, 0x8eae31))))))))) (.node 0xc94d407 (.node 0xc694a07 (.node 0xc595207 (.node 0xc568a07 (.node 0xc564c07 (.leaf (0xc559207, (2, 0xba72d0))) (.leaf (0xc564c07, (2, 0x9ee2d0)))) (.node 0xc570607 (.leaf (0xc568a07, (1, 0x8eaf81))) (.leaf (0xc570607, (3, 0xba72d0))))) (.node 0xc654c07 (.node 0xc5a4a07 (.leaf (0xc595207, (2, 0xba7650))) (.leaf (0xc5a4a07, (2, 0xba7688)))) (.node 0xc658a07 (.leaf (0xc654c07, (2, 0x9ee650))) (.leaf (0xc658a07, (2, 0x9ee688)))))) (.node 0xc8d5407 (.node 0xc714607 (.node 0xc70ca07 (.leaf (0xc694a07, (1, 0x8eadc1))) (.leaf (0xc70ca07, (3, 0xba7688)))) (.node 0xc8cd807 (.leaf (0xc714607, (3, 0xba7650))) (.leaf (0xc8cd807, (1, 0x95ae31))))) (.node 0xc8e4c07 (.node 0xc8d9207 (.leaf (0xc8d5407, (3, 0x97e2d0))) (.leaf (0xc8d9207, (2, 0xb372d0)))) (.node 0xc8e8a07 (.leaf (0xc8e4c07, (2, 0x97e2d0))) (.node 0xc8f0607 (.leaf (0xc8e8a07, (3, 0xb372d0))) (.leaf (0xc8f0607, (1, 0x95af81)))))))) (.node 0xcc4b807 (.node 0xca4cc07 (.node 0xc98d207 (.node 0xc968607 (.leaf (0xc94d407, (3, 0x97e650))) (.leaf (0xc968607, (3, 0x97e688)))) (.node 0xc9a4607 (.leaf (0xc98d207, (2, 0xb37650))) (.leaf (0xc9a4607, (2, 0xb37688))))) (.node 0xca8ca07 (.node 0xca58607 (.leaf (0xca4cc07, (2, 0x97e650))) (.leaf (0xca58607, (2, 0x97e688)))) (.node 0xca94607 (.leaf (0xca8ca07, (3, 0xb37650))) (.node 0xcb0c607 (.leaf (0xca94607, (3, 0xb37688))) (.leaf (0xcb0c607, (1, 0x95adc1))))))) (.node 0xcc68907 (.node 0xcc59107 (.node 0xcc53407 (.leaf (0xcc4b807, (3, 0xcc85ec))) (.leaf (0xcc53407, (3, 0xc585ec)))) (.node 0xcc62c07 (.leaf (0xcc59107, (1, 0x7c2a66))) (.leaf (0xcc62c07, (1, 0x7c2b0e))))) (.node 0xcc87807 (.node 0xcc70507 (.leaf (0xcc68907, (3, 0xc5857c))) (.leaf (0xcc70507, (3, 0xcc857c)))) (.node 0xcc93207 (.leaf (0xcc87807, (3, 0xcc8eac))) (.node 0xcc95107 (.leaf (0xcc93207, (1, 0xed0b0e))) (.leaf (0xcc95107, (3, 0x38357c))))))))))) (.node 0xe0d5207 (.node 0xd458907 (.node 0xce0c907 (.node 0xcd22607 (.node 0xcce0887 (.node 0xccb0307 (.node 0xcca4907 (.leaf (0xcca2a07, (3, 0x3835ec))) (.leaf (0xcca4907, (1, 0xed0a66)))) (.node 0xccd1087 (.leaf (0xccb0307, (3, 0xcc8f54))) (.leaf (0xccd1087, (3, 0x233abc))))) (.node 0xcd0b207 (.node 0xcd07407 (.leaf (0xcce0887, (3, 0x233bd4))) (.leaf (0xcd07407, (3, 0xc58eac)))) (.node 0xcd0d107 (.leaf (0xcd0b207, (1, 0xed094e))) (.leaf (0xcd0d107, (3, 0x23357c)))))) (.node 0xcd60487 (.node 0xcd28307 (.node 0xcd24507 (.leaf (0xcd22607, (3, 0x2335ec))) (.leaf (0xcd24507, (1, 0xed086e)))) (.node 0xcd49087 (.leaf (0xcd28307, (3, 0xc58f54))) (.leaf (0xcd49087, (3, 0x383abc))))) (.node 0xcda0287 (.node 0xcd85087 (.leaf (0xcd60487, (3, 0x383bd4))) (.leaf (0xcd85087, (1, 0x7c2366)))) (.node 0xce06c07 (.leaf (0xcda0287, (1, 0x7c232e))) (.node 0xce0aa07 (.leaf (0xce06c07, (1, 0x7c294e))) (.leaf (0xce0aa07, (3, 0x383eac)))))))) (.node 0xcf04487 (.node 0xce48887 (.node 0xce14507 (.node 0xce12607 (.leaf (0xce0c907, (3, 0x233f54))) (.leaf (0xce12607, (3, 0x233eac)))) (.node 0xce18307 (.leaf (0xce14507, (3, 0x383f54))) (.leaf (0xce18307, (1, 0x7c286e))))) (.node 0xce84887 (.node 0xce50487 (.leaf (0xce48887, (1, 0xed0366))) (.leaf (0xce50487, (1, 0xed032e)))) (.node 0xce90287 (.leaf (0xce84887, (3, 0xc58abc))) (.leaf (0xce90287, (3, 0xc58bd4)))))) (.node 0xd14cc07 (.node 0xd0d4c07 (.node 0xcf08287 (.leaf (0xcf04487, (3, 0xcc8abc))) (.leaf (0xcf08287, (3, 0xcc8bd4)))) (.node 0xd0d8a07 (.leaf (0xd0d4c07, (0, 0x9f5688))) (.leaf (0xd0d8a07, (0, 0x9ee688))))) (.node 0xd18ca07 (.node 0xd158607 (.leaf (0xd14cc07, (0, 0x9bd688))) (.leaf (0xd158607, (0, 0x97e688)))) (.node 0xd194607 (.leaf (0xd18ca07, (0, 0x9af688))) (.node 0xd452c07 (.leaf (0xd194607, (0, 0x977688))) (.leaf (0xd452c07, (3, 0xc5d9c2))))))))) (.node 0xd88aa07 (.node 0xd514507 (.node 0xd506c07 (.node 0xd494907 (.node 0xd492a07 (.leaf (0xd458907, (3, 0xc5d83a))) (.leaf (0xd492a07, (3, 0xc6b9c2)))) (.node 0xd4d0887 (.leaf (0xd494907, (3, 0xc6b83a))) (.leaf (0xd4d0887, (4, 0x9f5688))))) (.node 0xd50c907 (.node 0xd50aa07 (.leaf (0xd506c07, (3, 0xc5df02))) (.leaf (0xd50aa07, (3, 0xc6bf02)))) (.node 0xd512607 (.leaf (0xd50c907, (4, 0x9f54c8))) (.leaf (0xd512607, (4, 0x9f5458)))))) (.node 0xd584887 (.node 0xd548887 (.node 0xd518307 (.leaf (0xd514507, (3, 0xc6be22))) (.leaf (0xd518307, (3, 0xc5de22)))) (.node 0xd550487 (.leaf (0xd548887, (3, 0xc6b13a))) (.leaf (0xd550487, (3, 0xc6b1e2))))) (.node 0xd84ac07 (.node 0xd590287 (.leaf (0xd584887, (3, 0xc5d13a))) (.leaf (0xd590287, (3, 0xc5d1e2)))) (.node 0xd858507 (.leaf (0xd84ac07, (3, 0xccd9c2))) (.node 0xd886c07 (.leaf (0xd858507, (3, 0xccd83a))) (.leaf (0xd886c07, (3, 0xccdf02)))))))) (.node 0xd948487 (.node 0xd898307 (.node 0xd892607 (.node 0xd88c907 (.leaf (0xd88aa07, (4, 0x9bd458))) (.leaf (0xd88c907, (3, 0xd4be22)))) (.node 0xd894507 (.leaf (0xd892607, (3, 0xd4bf02))) (.leaf (0xd894507, (4, 0x9bd4c8))))) (.node 0xd8d0487 (.node 0xd8c8887 (.leaf (0xd898307, (3, 0xccde22))) (.leaf (0xd8c8887, (3, 0xd4b1e2)))) (.node 0xd90a607 (.leaf (0xd8d0487, (3, 0xd4b13a))) (.node 0xd90c507 (.leaf (0xd90a607, (3, 0xd4b9c2))) (.leaf (0xd90c507, (3, 0xd4b83a))))))) (.node 0xdc12507 (.node 0xd988287 (.node 0xd984487 (.leaf (0xd948487, (4, 0x9bd688))) (.leaf (0xd984487, (3, 0xccd13a)))) (.node 0xdc0a907 (.leaf (0xd988287, (3, 0xccd1e2))) (.leaf (0xdc0a907, (4, 0xce55c1))))) (.node 0xdc90187 (.node 0xdc82887 (.leaf (0xdc12507, (4, 0xd1d5c1))) (.leaf (0xdc82887, (4, 0xce5e81)))) (.node 0xdd02487 (.leaf (0xdc90187, (4, 0xce5e11))) (.node 0xdd08187 (.leaf (0xdd02487, (4, 0xd1de81))) (.leaf (0xdd08187, (4, 0xd1de11)))))))))) (.node 0xea84287 (.node 0xe614307 (.node 0xe455107 (.node 0xe24ca07 (.node 0xe14d207 (.node 0xe0e4a07 (.leaf (0xe0d5207, (1, 0xd67688))) (.leaf (0xe0e4a07, (1, 0xba7688)))) (.node 0xe164607 (.leaf (0xe14d207, (1, 0xd2f688))) (.leaf (0xe164607, (1, 0xb37688))))) (.node 0xe447807 (.node 0xe254607 (.leaf (0xe24ca07, (1, 0x9af688))) (.leaf (0xe254607, (1, 0x977688)))) (.node 0xe453207 (.leaf (0xe447807, (4, 0xd67458))) (.leaf (0xe453207, (3, 0x771f02)))))) (.node 0xe507207 (.node 0xe464907 (.node 0xe462a07 (.leaf (0xe455107, (3, 0xaf1e22))) (.leaf (0xe462a07, (3, 0xaf1f02)))) (.node 0xe470307 (.leaf (0xe464907, (3, 0x771e22))) (.leaf (0xe470307, (4, 0xd674c8))))) (.node 0xe545087 (.node 0xe524307 (.leaf (0xe507207, (3, 0x7719c2))) (.leaf (0xe524307, (3, 0x77183a)))) (.node 0xe560287 (.leaf (0xe545087, (3, 0xaf11e2))) (.node 0xe606a07 (.leaf (0xe560287, (3, 0xaf113a))) (.leaf (0xe606a07, (3, 0xaf19c2)))))))) (.node 0xe868307 (.node 0xe847407 (.node 0xe650287 (.node 0xe644887 (.leaf (0xe614307, (3, 0xaf183a))) (.leaf (0xe644887, (3, 0x7711e2)))) (.node 0xe704287 (.leaf (0xe650287, (3, 0x77113a))) (.leaf (0xe704287, (4, 0xd67688))))) (.node 0xe84d107 (.node 0xe84b207 (.leaf (0xe847407, (4, 0xd2f458))) (.leaf (0xe84b207, (3, 0x7a9f02)))) (.node 0xe862607 (.leaf (0xe84d107, (3, 0xb99e22))) (.node 0xe864507 (.leaf (0xe862607, (3, 0xb99f02))) (.leaf (0xe864507, (3, 0x7a9e22))))))) (.node 0xe8e0287 (.node 0xe8a4307 (.node 0xe887207 (.leaf (0xe868307, (4, 0xd2f4c8))) (.leaf (0xe887207, (3, 0x7a99c2)))) (.node 0xe8c5087 (.leaf (0xe8a4307, (3, 0x7a983a))) (.leaf (0xe8c5087, (3, 0xb991e2))))) (.node 0xea0c307 (.node 0xea06607 (.leaf (0xe8e0287, (3, 0xb9913a))) (.leaf (0xea06607, (3, 0xb999c2)))) (.node 0xea44487 (.leaf (0xea0c307, (3, 0xb9983a))) (.node 0xea48287 (.leaf (0xea44487, (3, 0x7a91e2))) (.leaf (0xea48287, (3, 0x7a913a))))))))) (.node 0xf106607 (.node 0xf04aa07 (.node 0xec60187 (.node 0xec22307 (.node 0xec07107 (.leaf (0xea84287, (4, 0xd2f688))) (.leaf (0xec07107, (4, 0x7ac5c1)))) (.node 0xec43087 (.leaf (0xec22307, (4, 0x9ab5c1))) (.leaf (0xec43087, (4, 0x7ace81))))) (.node 0xee04187 (.node 0xee02287 (.leaf (0xec60187, (4, 0x7ace11))) (.leaf (0xee02287, (4, 0x9abe81)))) (.node 0xf046c07 (.leaf (0xee04187, (4, 0x9abe11))) (.leaf (0xf046c07, (4, 0x9af458)))))) (.node 0xf058307 (.node 0xf052607 (.node 0xf04c907 (.leaf (0xf04aa07, (3, 0xce9f02))) (.leaf (0xf04c907, (3, 0xd59e22)))) (.node 0xf054507 (.leaf (0xf052607, (3, 0xd59f02))) (.leaf (0xf054507, (3, 0xce9e22))))) (.node 0xf094307 (.node 0xf086a07 (.leaf (0xf058307, (4, 0x9af4c8))) (.leaf (0xf086a07, (3, 0xce99c2)))) (.node 0xf0c4887 (.leaf (0xf094307, (3, 0xce983a))) (.node 0xf0d0287 (.leaf (0xf0c4887, (3, 0xd591e2))) (.leaf (0xf0d0287, (3, 0xd5913a)))))))) (.node 0xf502287 (.node 0xf184287 (.node 0xf144487 (.node 0xf10c307 (.leaf (0xf106607, (3, 0xd599c2))) (.leaf (0xf10c307, (3, 0xd5983a)))) (.node 0xf148287 (.leaf (0xf144487, (3, 0xce91e2))) (.leaf (0xf148287, (3, 0xce913a))))) (.node 0xf412307 (.node 0xf406907 (.leaf (0xf184287, (4, 0x9af688))) (.leaf (0xf406907, (4, 0xcec5c1)))) (.node 0xf442887 (.leaf (0xf412307, (4, 0xd2b5c1))) (.node 0xf450187 (.leaf (0xf442887, (4, 0xcece81))) (.leaf (0xf450187, (4, 0xcece11))))))) (.node 0xf842487 (.node 0xf806507 (.node 0xf504187 (.leaf (0xf502287, (4, 0xd2be81))) (.leaf (0xf504187, (4, 0xd2be11)))) (.node 0xf80a307 (.leaf (0xf806507, (4, 0xd5c5c1))) (.leaf (0xf80a307, (4, 0xd635c1))))) (.node 0xf882287 (.node 0xf848187 (.leaf (0xf842487, (4, 0xd5ce81))) (.leaf (0xf848187, (4, 0xd5ce11)))) (.node 0xf884187 (.leaf (0xf882287, (4, 0xd63e81))) (.node 0xfc02187 (.leaf (0xf884187, (4, 0xd63e11))) (.leaf (0xfc02187, (5, 0xfac688)))))))))))))

def valid (record : Nat × (Nat × Nat)) : Bool :=
  decide (((List.range 8).map (imageOf record.2.2)).Nodup) &&
    representatives[record.2.1]? == some (moveWord record.1 record.2.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 600000000 in
lemma checked : records.all valid = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 600000000 in
lemma covered_all : enumerate.all (fun w => (records.find w).1 == w) = true := by rfl

theorem normalized_classification (w : Nat) (small : w < 2^28) (normal : low w 7 = 7)
    (cubic : ∀ v < 8, degree w v = 3) :
    ∃ rep ∈ representatives, ∃ move, ((List.range 8).map (imageOf move)).Nodup ∧ moveWord w move = rep := by
  have member := enumerate_complete w small normal cubic
  let row := records.find w
  have same : row.1 = w := beq_iff_eq.mp (List.all_eq_true.mp covered_all w member)
  have data : valid row = true := EntryTable.find_correct records valid checked w
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at data
  have actual : moveWord row.1 row.2.2 ∈ representatives := List.mem_of_getElem? data.2
  rw [same] at actual
  exact ⟨_, actual, row.2.2, data.1, rfl⟩

end WeightSixteenCubicGraphs

namespace WeightSixteenCubicGraphs

open FiniteSearchMasks Finset

lemma edge_slots : edges = pairs.map (fun (a,b) => (a.val,b.val)) := by rfl

lemma edge_count : edges.length = 28 := by rw [edge_slots, List.length_map, pairs_size]

lemma edges_at (i : Fin 28) :
    edges[i.val]? = some ((pairOf i).1.val,(pairOf i).2.val) := by
  rw [edge_slots, List.getElem?_map, List.getElem?_eq_getElem (by simpa only [pairs_size] using i.isLt)]
  rfl

lemma edgeIndex_comm (a b : Nat) : edgeIndex a b = edgeIndex b a := by
  simp [edgeIndex, min_comm a b, max_comm a b]

lemma pairOf_distinct : ∀ i : Fin 28, (pairOf i).1 ≠ (pairOf i).2 := by decide +kernel

lemma index_pairOf : ∀ i : Fin 28, edgeIndex (pairOf i).1.val (pairOf i).2.val = i.val := by
  decide +kernel

lemma valid_address : ∀ a b : Fin 8, a ≠ b → edgeIndex a.val b.val < 28 := by decide +kernel

lemma endpoints_at_address (a b : Fin 8) (different : a ≠ b) :
    pairOf ⟨edgeIndex a.val b.val, valid_address a b different⟩ = (a,b) ∨
    pairOf ⟨edgeIndex a.val b.val, valid_address a b different⟩ = (b,a) := by
  have bound := valid_address a b different
  have Numeric : ∀ a b : Fin 8, ∀ i : Fin 28, a ≠ b → i.val = edgeIndex a.val b.val →
      pairOf i = (a,b) ∨ pairOf i = (b,a) := by decide +kernel
  exact Numeric a b ⟨_,bound⟩ different rfl

def movePoint (packed : Nat) (a : Fin 8) : Fin 8 :=
  ⟨imageOf packed a.val, Nat.and_lt_two_pow _ (by decide : 7 < 2^3)⟩

noncomputable def movePerm (packed : Nat) (checked : ((List.range 8).map (imageOf packed)).Nodup) :
    Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (movePoint packed) <|
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro a b same
      apply Fin.ext
      have small_a : a.val < ((List.range 8).map (imageOf packed)).length := by simpa using a.isLt
      have small_b : b.val < ((List.range 8).map (imageOf packed)).length := by simpa using b.isLt
      apply (checked.getElem_inj_iff (hi := small_a) (hj := small_b)).mp
      simpa only [movePoint, List.getElem_map, List.getElem_range] using congrArg Fin.val same, rfl⟩

def movedEdge (e : Equiv.Perm (Fin 8)) (i : Fin 28) : Fin 28 :=
  ⟨edgeIndex (e (pairOf i).1).val (e (pairOf i).2).val,
    valid_address _ _ (fun eq => pairOf_distinct i (e.injective eq))⟩

lemma movedEdge_endpoints (e : Equiv.Perm (Fin 8)) (i : Fin 28) :
    pairOf (movedEdge e i) = (e (pairOf i).1,e (pairOf i).2) ∨
    pairOf (movedEdge e i) = (e (pairOf i).2,e (pairOf i).1) :=
  endpoints_at_address _ _ (fun eq => pairOf_distinct i (e.injective eq))

lemma movedEdge_inverse (e : Equiv.Perm (Fin 8)) (i : Fin 28) :
    movedEdge e.symm (movedEdge e i) = i := by
  apply Fin.ext
  change edgeIndex (e.symm (pairOf (movedEdge e i)).1).val
    (e.symm (pairOf (movedEdge e i)).2).val = i.val
  rcases movedEdge_endpoints e i with one | two
  · simpa only [one, Equiv.symm_apply_apply] using index_pairOf i
  · simpa only [two, Equiv.symm_apply_apply, edgeIndex_comm (pairOf i).2.val (pairOf i).1.val] using index_pairOf i

lemma movedEdge_injective (e : Equiv.Perm (Fin 8)) : Function.Injective (movedEdge e) :=
  Function.LeftInverse.injective (movedEdge_inverse e)

lemma movedEdge_surjective (e : Equiv.Perm (Fin 8)) : Function.Surjective (movedEdge e) := by
  intro i
  exact ⟨movedEdge e.symm i, by simpa only [Equiv.symm_symm] using movedEdge_inverse e.symm i⟩

lemma moveWord_bit (w packed bit : Nat) (checked : ((List.range 8).map (imageOf packed)).Nodup) :
    (moveWord w packed).testBit bit = true ↔
      ∃ j : Fin 28, w.testBit j.val = true ∧ (movedEdge (movePerm packed checked) j).val = bit := by
  rw [moveWord, foldr_or_testBit]
  constructor
  · rintro ⟨z, present, bit_z⟩
    obtain ⟨⟨e,j⟩, selected, rfl⟩ := List.mem_map.mp present
    have written := List.mk_mem_zipIdx_iff_getElem?.mp selected
    have small : j < 28 := by simpa only [edge_count] using (List.getElem?_eq_some_iff.mp written).1
    let addr : Fin 28 := ⟨j,small⟩
    have edgeEq : e = ((pairOf addr).1.val,(pairOf addr).2.val) :=
      Option.some.inj (written.symm.trans (edges_at addr))
    subst e
    cases active : w.testBit j with
    | false => simp [active] at bit_z
    | true =>
      have target : edgeIndex (imageOf packed (pairOf addr).1.val) (imageOf packed (pairOf addr).2.val) = bit := by
        simpa [active, Nat.testBit_two_pow] using bit_z
      exact ⟨addr,active,target⟩
  · rintro ⟨j, active, target⟩
    refine ⟨2^bit, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    refine ⟨(((pairOf j).1.val,(pairOf j).2.val),j.val), List.mk_mem_zipIdx_iff_getElem?.mpr (edges_at j),?_⟩
    change (if w.testBit j.val then
      2^edgeIndex (imageOf packed (pairOf j).1.val) (imageOf packed (pairOf j).2.val) else 0) = 2^bit
    exact if_pos active ▸ congrArg (fun n => 2^n) target

theorem encode_after_move (g : Fin 8 → Fin 8 → Bool) (symm : ∀ a b, g a b = g b a)
    (packed : Nat) (checked : ((List.range 8).map (imageOf packed)).Nodup) :
    let e := movePerm packed checked
    moveWord (encode g) packed = encode (fun a b => g (e.symm a) (e.symm b)) := by
  let e := movePerm packed checked
  let changed := fun a b => g (e.symm a) (e.symm b)
  change moveWord (encode g) packed = encode changed
  have agreement (i : Fin 28) :
      (encode changed).testBit (movedEdge e i).val = (encode g).testBit i.val := by
    rw [encode_bit, encode_bit]
    rcases movedEdge_endpoints e i with one | two
    · simp only [changed, one, Equiv.symm_apply_apply]
    · simpa only [changed, two, Equiv.symm_apply_apply] using symm (pairOf i).2 (pairOf i).1
  apply Nat.eq_of_testBit_eq
  intro bit
  apply Bool.eq_iff_iff.mpr
  rw [moveWord_bit _ packed bit checked]
  by_cases small : bit < 28
  · let address : Fin 28 := ⟨bit,small⟩
    obtain ⟨j, placed⟩ := movedEdge_surjective e address
    have reaches : (movedEdge e j).val = bit := congrArg Fin.val placed
    rw [← reaches, agreement]
    constructor
    · rintro ⟨i, active, target⟩
      have same := movedEdge_injective e (Fin.ext target)
      exact same ▸ active
    · intro active
      exact ⟨j,active,rfl⟩
  · simp only [encode_off changed bit (Nat.le_of_not_gt small), Bool.false_eq_true, iff_false]
    rintro ⟨j,_,same⟩
    exact small (same ▸ (movedEdge e j).isLt)

theorem cubic_representative (g : Fin 8 → Fin 8 → Bool)
    (symmetric : ∀ x y, g x y = g y x) (loopfree : ∀ x, g x x = false)
    (degreeThree : ∀ x, (Finset.univ.filter fun y => g x y = true).card = 3) :
    ∃ relabel : Equiv.Perm (Fin 8),
      encode (fun x y => g (relabel x) (relabel y)) ∈ representatives := by
  let neighbors : Finset (Fin 8) := Finset.univ.filter fun x => g 0 x = true
  have three : neighbors.card = 3 := degreeThree 0
  have missing : 0 ∉ neighbors := by simp [neighbors,loopfree]
  obtain ⟨base,fixed,normal⟩ := WeightSixteenCubicGeometry.normalize_first_neighbors neighbors three missing
  let h : Fin 8 → Fin 8 → Bool := fun a b => g (base a) (base b)
  have hSymm (a b : Fin 8) : h a b = h b a := symmetric _ _
  have hLoop (a : Fin 8) : h a a = false := loopfree _
  have hRow (j : Fin 8) : h 0 j = true ↔ j = 1 ∨ j = 2 ∨ j = 3 := by
    simpa only [neighbors, h, fixed, Finset.mem_filter, Finset.mem_univ, true_and] using normal j
  have hDegree (a : Fin 8) : (Finset.univ.filter fun b => h a b = true).card = 3 := by
    refine (show (Finset.univ.filter fun b => h a b = true).card =
        (Finset.univ.filter fun b => g (base a) b = true).card from ?_).trans (degreeThree (base a))
    apply Finset.card_bij (fun b _ => base b)
    · intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    · intro b _ c _ eq
      exact base.injective eq
    · intro b hb
      refine ⟨base.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,base.apply_symm_apply b⟩
      simpa only [h, Equiv.apply_symm_apply] using (Finset.mem_filter.mp hb).2
  have degrees (j : Nat) (below : j < 8) : degree (encode h) j = 3 := by
    let i : Fin 8 := ⟨j,below⟩
    change degree (encode h) i.val = 3
    rw [degree_encode h hSymm hLoop, hDegree]
  obtain ⟨rep, member, packed, picked, target⟩ :=
    normalized_classification (encode h) (encode_bound h) (first_row_encoding h hRow) degrees
  let undo := (movePerm packed picked).symm
  have agree : moveWord (encode h) packed = encode (fun a b => h (undo a) (undo b)) :=
    encode_after_move h hSymm packed picked
  refine ⟨undo.trans base,?_⟩
  change encode (fun a b => h (undo a) (undo b)) ∈ representatives
  rwa [← agree, target]

theorem exterior_representative
    (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (share : ∀ a b, a ≠ b → ∃! p, WeightSixteenCubicGeometry.together A p a b)
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4) :
    ∃ p : Equiv.Perm (Fin 8), encode (exteriorGraph A S p) ∈ representatives := by
  let identity : Equiv.Perm (Fin 8) := Equiv.refl _
  let g := exteriorGraph A S identity
  have cubic (a : Fin 8) : (Finset.univ.filter fun b => g a b = true).card = 3 :=
    (exteriorGraph_degree A S identity a).trans
      (WeightSixteenCubicGeometry.exterior_cubic A S share degree_two line_four a)
  exact cubic_representative g (exteriorGraph_symm A S identity) (exteriorGraph_loopfree A S identity) cubic

end WeightSixteenCubicGraphs


namespace WeightSixteenTripleProjection

open Finset
open WeightSixteenCubicGeometry

theorem free_internal_neighbors (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (T : Finset (Fin 8)) (degree : ∀ p ∈ S, (Finset.univ.filter fun a => A a p = true).card = 2)
    (rowPairs : ∀ a b, a ≠ b → ∃! p, A a p = true ∧ A b p = true)
    (a : Fin 8) (outsideT : a ∉ T) :
    (S.filter fun p => A a p = true ∧ ∀ b ∈ T, A b p = false).card =
    (Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ ¬ (∃ p ∉ S, A a p = true ∧ A b p = true)).card := by
  classical
  let free := S.filter fun p => A a p = true ∧ ∀ b ∈ T, A b p = false
  let candidates := Finset.univ.filter
    fun b => b ≠ a ∧ b ∉ T ∧ ¬ (∃ p ∉ S, A a p = true ∧ A b p = true)
  have picked (p : Fin 111) (hp : p ∈ free) : ∃! b, b ≠ a ∧ A b p = true :=
    second_row A p (degree p (Finset.mem_filter.mp hp).1) a (Finset.mem_filter.mp hp).2.1
  let other (p : Fin 111) (hp : p ∈ free) := Classical.choose (picked p hp)
  have spec (p : Fin 111) (hp : p ∈ free) :
      (other p hp ≠ a ∧ A (other p hp) p = true) ∧
      ∀ b, b ≠ a ∧ A b p = true → b = other p hp :=
    Classical.choose_spec (picked p hp)
  change free.card = candidates.card
  apply Finset.card_bij other
  · intro p hp
    obtain ⟨inS,ona,off⟩ := Finset.mem_filter.mp hp
    obtain ⟨ne,onb⟩ := (spec p hp).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne,?_,?_⟩
    · intro insideT
      have notOn := off _ insideT
      rw [notOn] at onb
      contradiction
    · rintro ⟨r,outside,hr⟩
      obtain ⟨_,_,unique⟩ := rowPairs a _ ne.symm
      have eq := (unique p ⟨ona,onb⟩).trans (unique r hr).symm
      exact outside (eq ▸ inS)
  · intro p hp q hq equal
    obtain ⟨ne,onb⟩ := (spec p hp).1
    have onq := (spec q hq).1.2
    rw [← equal] at onq
    obtain ⟨_,_,unique⟩ := rowPairs a _ ne.symm
    exact (unique p ⟨(Finset.mem_filter.mp hp).2.1,onb⟩).trans
      (unique q ⟨(Finset.mem_filter.mp hq).2.1,onq⟩).symm
  · intro b hb
    obtain ⟨_,ne,outB,noOuter⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,onBoth,_⟩ := rowPairs a b ne.symm
    have inS : p ∈ S := by
      by_contra outside
      exact noOuter ⟨p,outside,onBoth⟩
    obtain ⟨d,_,unique⟩ := second_row A p (degree p inS) a onBoth.1
    have bd : b = d := unique b ⟨ne,onBoth.2⟩
    have not_in (c : Fin 8) (hc : c ∈ T) : A c p = false := by
      cases val : A c p with
      | false => rfl
      | true =>
        have ca : c ≠ a := fun same => outsideT (same ▸ hc)
        have cb := (unique c ⟨ca,val⟩).trans bd.symm
        exact False.elim (outB (cb ▸ hc))
    have hp : p ∈ free := Finset.mem_filter.mpr ⟨inS,onBoth.1,not_in⟩
    exact ⟨p,hp,((spec p hp).2 b ⟨ne,onBoth.2⟩).symm⟩

end WeightSixteenTripleProjection



namespace WeightSixteenSaturatedColumn

open Finset
open scoped BigOperators

theorem saturated_column {R P : Type} [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P]
    (M : R → P → Bool) (pointCount : Fintype.card P = 111)
    (rowSize : ∀ l, (Finset.univ.filter fun q => M l q = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (p : P) (onSize : (Finset.univ.filter fun l => M l p = true).card = 11) :
    ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true := by
  let on := Finset.univ.filter fun l => M l p = true
  let ray (l : R) := (Finset.univ.filter fun q => M l q = true).erase p
  let covered := on.biUnion ray
  let other : Finset P := Finset.univ.erase p
  have rays_disjoint : (on : Set R).PairwiseDisjoint ray := by
    intro a ha b hb different
    change Disjoint (ray a) (ray b)
    rw [Finset.disjoint_left]
    intro q qa qb
    obtain ⟨ne,in_a⟩ := Finset.mem_erase.mp qa
    obtain ⟨_,in_b⟩ := Finset.mem_erase.mp qb
    exact different (columnPairs p q ne.symm a b
      (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2 (Finset.mem_filter.mp in_a).2
      (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 (Finset.mem_filter.mp in_b).2)
  have ray_size (l : R) (hl : l ∈ on) : (ray l).card = 10 := by
    change ((Finset.univ.filter fun q => M l q = true).erase p).card = 10
    have on_l : p ∈ Finset.univ.filter (fun q => M l q = true) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem on_l,rowSize]
  have matched : covered.card = 110 := by
    change (on.biUnion ray).card = 110
    rw [Finset.card_biUnion rays_disjoint,Finset.sum_congr rfl ray_size,Finset.sum_const,Nat.nsmul_eq_mul]
    change (Finset.univ.filter fun l => M l p = true).card * 10 = 110
    rw [onSize]
  have other_size : other.card = 110 := by
    change ((Finset.univ : Finset P).erase p).card = 110
    rw [Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,pointCount]
  have subset : covered ⊆ other := by
    intro q hq
    obtain ⟨l,_,loc⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp loc).1,Finset.mem_univ _⟩
  have full : covered = other := by
    apply Finset.eq_of_subset_of_card_le subset
    rw [other_size,matched]
  intro q ne
  have elsewhere : q ∈ other := Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ _⟩
  have some_ray : q ∈ covered := full.symm ▸ elsewhere
  obtain ⟨l,hl,present⟩ := Finset.mem_biUnion.mp some_ray
  have lp := (Finset.mem_filter.mp hl).2
  have lq := (Finset.mem_filter.mp (Finset.mem_erase.mp present).2).2
  exact ⟨l,⟨lp,lq⟩,fun m hm => columnPairs p q ne m l hm.1 hm.2 lp lq⟩

lemma count_incidence_sum {X Y : Type} [Fintype X] [Fintype Y]
    (P : X ⊕ Y → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (.inl x)).card +
      (Finset.univ.filter fun y => P (.inr y)).card := by
  have same : Finset.univ.filter P = (Finset.univ.filter fun x => P (.inl x)).disjSum
      (Finset.univ.filter fun y => P (.inr y)) := by
    ext l
    cases l <;> simp [Finset.mem_filter]
  rw [same,Finset.card_disjSum]

theorem free_points_on_heavy_line
    (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 9)
    (q : Fin 111) (hq : q ∉ S) (a : Fin 8) :
    let onQ := Finset.univ.filter fun b : Fin 8 => M (.inl b) q = true
    let free := S.filter fun p => M (.inl a) p = true ∧ ∀ b ∈ onQ, M (.inl b) p = false
    free.card ≤ (Finset.univ.filter fun b : Fin 72 => M (.inr b) q = true).card := by
  classical
  let onQ := Finset.univ.filter fun b : Fin 8 => M (.inl b) q = true
  let free := S.filter fun p => M (.inl a) p = true ∧ ∀ b ∈ onQ, M (.inl b) p = false
  let B := Finset.univ.filter fun b : Fin 72 => M (.inr b) q = true
  have exists_line (p : Fin 111) (hp : p ∈ free) : ∃ b ∈ B, M (.inr b) p = true := by
    obtain ⟨inS,_,off⟩ := Finset.mem_filter.mp hp
    have degree : (Finset.univ.filter fun l => M l p = true).card = 11 := by
      rw [count_incidence_sum, (inside p inS).1, (inside p inS).2]
    have ne : p ≠ q := fun equal => hq (equal ▸ inS)
    obtain ⟨l,left,_⟩ := saturated_column M (Fintype.card_fin 111) rows columnPairs p degree q ne
    cases l with
    | inl b =>
      have found : b ∈ onQ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,left.2⟩
      exact False.elim (Bool.noConfusion ((off b found).symm.trans left.1))
    | inr b =>
      exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,left.2⟩,left.1⟩
  let f (p : ↥free) : ↥B := ⟨Classical.choose (exists_line p.val p.property),
    (Classical.choose_spec (exists_line p.val p.property)).1⟩
  have known (p : ↥free) : M (.inr (f p).val) p.val = true :=
    (Classical.choose_spec (exists_line p.val p.property)).2
  have injective : Function.Injective f := by
    intro p t equality
    apply Subtype.ext
    by_contra ne
    have ap := ((Finset.mem_filter.mp p.property).2).1
    have at' := ((Finset.mem_filter.mp t.property).2).1
    have bp := known p
    have bt := known t
    rw [← equality] at bt
    have wrong := columnPairs p.val t.val ne (.inl a) (.inr (f p).val) ap at' bp bt
    cases wrong
  exact Finset.card_le_card_of_injective injective

end WeightSixteenSaturatedColumn



namespace WeightSixteenTripleNumerics

open Finset
open WeightSixteenCubicGraphs

def adj (r : Nat) (a b : Fin 8) : Bool :=
  decide (a ≠ b) && r.testBit (edgeIndex a.val b.val)

def CanHold (G : Fin 8 → Fin 8 → Bool) (T : Finset (Fin 8)) : Prop :=
  T.card = 3 ∧
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b → G a b = true) ∧
    ∀ a ∉ T, (Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ G a b = false).card ≤ 2

instance (G : Fin 8 → Fin 8 → Bool) (T : Finset (Fin 8)) : Decidable (CanHold G T) := by
  unfold CanHold
  infer_instance

def rep (i : Fin 6) : Nat := representatives[i.val]!

def tripleSets : List (Finset (Fin 8)) := [{0,1,2}, {0,1,3}, {0,1,4}, {0,1,5}, {0,1,6}, {0,1,7}, {0,2,3}, {0,2,4}, {0,2,5}, {0,2,6}, {0,2,7}, {0,3,4}, {0,3,5}, {0,3,6}, {0,3,7}, {0,4,5}, {0,4,6}, {0,4,7}, {0,5,6}, {0,5,7}, {0,6,7}, {1,2,3}, {1,2,4}, {1,2,5}, {1,2,6}, {1,2,7}, {1,3,4}, {1,3,5}, {1,3,6}, {1,3,7}, {1,4,5}, {1,4,6}, {1,4,7}, {1,5,6}, {1,5,7}, {1,6,7}, {2,3,4}, {2,3,5}, {2,3,6}, {2,3,7}, {2,4,5}, {2,4,6}, {2,4,7}, {2,5,6}, {2,5,7}, {2,6,7}, {3,4,5}, {3,4,6}, {3,4,7}, {3,5,6}, {3,5,7}, {3,6,7}, {4,5,6}, {4,5,7}, {4,6,7}, {5,6,7}]

set_option maxHeartbeats 25000000 in
set_option maxRecDepth 4096 in
lemma card_three_listed : ∀ T : Finset (Fin 8), T.card = 3 → T ∈ tripleSets := by
  decide +kernel

def permissibleWord (r : Nat) : Bool := r == 0x2e69807 || r == 0x35a5807

def verify_excluded (i : Fin 6) : Bool :=
  if permissibleWord (rep i) then true
  else tripleSets.all (fun T => !decide (CanHold (adj (rep i)) T))

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 12000 in
lemma excluded_checks : ∀ i : Fin 6, verify_excluded i = true := by decide +kernel

theorem verify_one (i : Fin 6) (has : ∃ T : Finset (Fin 8), CanHold (adj (rep i)) T) :
    rep i = 0x2e69807 ∨ rep i = 0x35a5807 := by
  obtain ⟨T,hT⟩ := has
  cases check : permissibleWord (rep i) with
  | true => simpa [permissibleWord, Bool.or_eq_true] using check
  | false =>
    have data_ := excluded_checks i
    rw [verify_excluded,check] at data_
    simp only [Bool.false_eq_true, if_false] at data_
    have member : T ∈ tripleSets :=
      card_three_listed T hT.1
    have deny := List.all_eq_true.mp data_ T member
    simp only [hT,decide_true,Bool.not_true] at deny
    contradiction

set_option maxHeartbeats 20000000 in
lemma only_one_triangle_check :
    tripleSets.all (fun T => !decide (CanHold (adj 0x2e69807) T) || decide (T = {4,5,6})) = true := by rfl

lemma unique_triangle (T : Finset (Fin 8)) (ht : CanHold (adj 0x2e69807) T) : T = {4,5,6} := by
  have member : T ∈ tripleSets :=
    card_three_listed T ht.1
  have h := List.all_eq_true.mp only_one_triangle_check T member
  simpa only [ht,decide_true,Bool.not_true,Bool.false_or,decide_eq_true_eq] using h

theorem verify_two (i : Fin 6)
    (has : ∃ T U : Finset (Fin 8), CanHold (adj (rep i)) T ∧ CanHold (adj (rep i)) U ∧ Disjoint T U) :
      rep i = 0x35a5807 := by
  obtain ⟨T,U,hT,hU,apart⟩ := has
  rcases verify_one i ⟨T,hT⟩ with h | h
  · rw [h] at hT hU
    have same := (unique_triangle T hT).trans (unique_triangle U hU).symm
    subst U
    have zero := (Finset.disjoint_self_iff_empty T).mp apart
    have card := hT.1
    rw [zero,Finset.card_empty] at card
    omega
  · exact h

lemma representatives_count : representatives.length = 6 := rfl

lemma rep_pick (r : Nat) (valid : r ∈ representatives) : ∃ i : Fin 6, rep i = r := by
  obtain ⟨n,hn,match_⟩ := List.mem_iff_getElem.mp valid
  let i : Fin 6 := ⟨n,by simpa only [representatives_count] using hn⟩
  exact ⟨i,(getElem!_pos representatives n hn).trans match_⟩

lemma recover_adjacency (G : Fin 8 → Fin 8 → Bool) (symm : ∀ a b, G a b = G b a)
    (loop : ∀ a, G a a = false) : adj (encode G) = G := by
  funext a b
  by_cases equal : a = b
  · subst b
    simp [adj,loop a]
  obtain ⟨x,shape⟩ := ordered_pair_exists a b equal
  have bit := encode_bit G x
  have at_index := index_pairOf x
  have index : edgeIndex a.val b.val = x.val := by
    rcases shape with ab | ba
    · simpa only [ab] using at_index
    · rw [edgeIndex_comm]
      simpa only [ba] using at_index
  change (decide (a ≠ b) && (encode G).testBit (edgeIndex a.val b.val)) = G a b
  rw [index]
  simp only [equal,ne_eq,not_false_eq_true,decide_true,Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [bit]
  rcases shape with ab | ba
  · simp [ab]
  · simpa only [ba] using (show G b a = true ↔ G a b = true by rw [symm b a])

end WeightSixteenTripleNumerics



namespace WeightSixteenTripleNumerics

open Finset WeightSixteenCubicGraphs

lemma cardinal_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl

theorem geometry_allows_triangle (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (cols : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 9)
    (outside : ∀ p ∉ S, 2 * (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card +
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 8)
    (e : Equiv.Perm (Fin 8)) (q : Fin 111) (hq : q ∉ S)
    (triple : (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true).card = 3) :
    CanHold (exteriorGraph (fun a p => M (.inl a) p) S e)
      (Finset.univ.filter fun a => M (.inl (e a)) q = true) := by
  classical
  let A (a : Fin 8) (p : Fin 111) := M (.inl a) p
  let R (a : Fin 8) (p : Fin 111) := A (e a) p
  let T := Finset.univ.filter fun a => R a q = true
  let original := Finset.univ.filter fun a => A a q = true
  let G := exteriorGraph A S e
  have T_iff (a : Fin 8) : a ∈ T ↔ R a q = true := by simp [T]
  have orig_iff (a : Fin 8) : a ∈ original ↔ A a q = true := by simp [original]
  have lead (a b : Fin 8) (ne : a ≠ b) :
      G a b = true ↔ ∃ p ∉ S, R a p = true ∧ R b p = true := by
    have distinct : e b ≠ e a := fun same => ne (e.injective same).symm
    simp [G,exteriorGraph,WeightSixteenCubicGeometry.mem_outer,distinct,R,
      WeightSixteenCubicGeometry.together]
  have B_count : (Finset.univ.filter fun b : Fin 72 => M (.inr b) q = true).card = 2 := by
    have count := outside q hq
    rw [triple] at count
    omega
  refine ⟨(cardinal_relabel e (fun a => A a q = true)).trans triple,?_,?_⟩
  · intro a ha b hb distinct
    exact (lead a b distinct).mpr ⟨q,hq,(T_iff a).mp ha,(T_iff b).mp hb⟩
  · intro a ha
    have degree (p : Fin 111) (hp : p ∈ S) : (Finset.univ.filter fun a => R a p = true).card = 2 :=
      (cardinal_relabel e (fun b => A b p = true)).trans (inside p hp).1
    have shares (a b : Fin 8) (distinct : a ≠ b) : ∃! p, R a p = true ∧ R b p = true :=
      rowPairs (.inl (e a)) (.inl (e b)) (fun same => distinct (e.injective (Sum.inl.inj same)))
    have count := WeightSixteenTripleProjection.free_internal_neighbors R S T degree shares a ha
    have same_candidates :
        (Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ G a b = false) =
        Finset.univ.filter fun b => b ≠ a ∧ b ∉ T ∧ ¬ (∃ p ∉ S, R a p = true ∧ R b p = true) := by
      ext b
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      apply and_congr_right
      intro ne
      apply and_congr_right
      intro _
      cases value : G a b with
      | false => simp [← lead a b (Ne.symm ne),value]
      | true => simp [← lead a b (Ne.symm ne),value]
    rw [same_candidates,← count]
    have free :
        (S.filter fun p => R a p = true ∧ ∀ b ∈ T, R b p = false) =
        S.filter fun p => A (e a) p = true ∧ ∀ b ∈ original, A b p = false := by
      ext p
      simp only [Finset.mem_filter]
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      constructor
      · intro prop b hb
        obtain ⟨c,rfl⟩ := e.surjective b
        exact prop c ((T_iff c).mpr ((orig_iff (e c)).mp hb))
      · intro prop b hb
        exact prop (e b) ((orig_iff (e b)).mpr ((T_iff b).mp hb))
    rw [free,← B_count]
    exact WeightSixteenSaturatedColumn.free_points_on_heavy_line M S rows cols inside q hq (e a)

end WeightSixteenTripleNumerics



namespace WeightSixteenTripleNumerics

open Finset WeightSixteenCubicGraphs

theorem triangle_model_word (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (a_count : ∀ a : Fin 8, (S.filter fun p => M (.inl a) p = true).card = 4)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (cols : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (inside : ∀ p ∈ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 9)
    (outside : ∀ p ∉ S, 2 * (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card +
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 8) :
    ∃ (e : Equiv.Perm (Fin 8)) (i : Fin 6),
      rep i = encode (exteriorGraph (fun a p => M (.inl a) p) S e) ∧
      ∀ q ∉ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) q = true).card = 3 →
        CanHold (adj (rep i)) (Finset.univ.filter fun a => M (.inl (e a)) q = true) := by
  let A (a : Fin 8) (p : Fin 111) := M (.inl a) p
  have own (a b : Fin 8) (different : a ≠ b) : ∃! p, WeightSixteenCubicGeometry.together A p a b :=
    rowPairs (.inl a) (.inl b) (fun eq => different (Sum.inl.inj eq))
  obtain ⟨e,valid⟩ := exterior_representative A S own (fun p hp => (inside p hp).1) a_count
  obtain ⟨i,matching⟩ := rep_pick _ valid
  refine ⟨e,i,matching,?_⟩
  intro q hq count
  rw [matching,recover_adjacency _ (exteriorGraph_symm A S e) (exteriorGraph_loopfree A S e)]
  exact geometry_allows_triangle M S rows rowPairs cols inside outside e q hq count

lemma word_model_syntax (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111))
    (e : Equiv.Perm (Fin 8)) :
    encode (fun a b => decide (b ≠ a ∧ ∃ p ∉ S, M (.inl (e a)) p = true ∧ M (.inl (e b)) p = true)) =
      encode (exteriorGraph (fun a p => M (.inl a) p) S e) := by
  congr 1
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,exteriorGraph,WeightSixteenCubicGeometry.mem_outer,
    WeightSixteenCubicGeometry.together]
  exact and_congr (not_congr e.injective.eq_iff.symm) Iff.rfl

end WeightSixteenTripleNumerics


theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1 := by
  classical
  intro M S rows As inside outside rowPairs cols found
  obtain ⟨e,i,meaning,allowed⟩ :=
    WeightSixteenTripleNumerics.triangle_model_word M S rows As rowPairs cols inside outside
  refine ⟨e,?_⟩
  change WeightSixteenCubicGraphs.encode (fun a b => decide (b ≠ a ∧
    ∃ x ∉ S, M (.inl (e a)) x = true ∧ M (.inl (e b)) x = true)) ∈ ([0x2e69807, 0x35a5807] : List Nat)
  rw [WeightSixteenTripleNumerics.word_model_syntax,← meaning]
  obtain ⟨p,hp,three⟩ := found
  have options := WeightSixteenTripleNumerics.verify_one i ⟨_,allowed p hp three⟩
  simpa [Finset.mem_filter] using options
