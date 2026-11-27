import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

/-! Project the double-center incidence matrix to one row of hidden points. -/

namespace WeightSixteenDoubleCenters

open Finset

abbrev HRow := Fin 4 ⊕ Fin 4
abbrev Visible := (Fin 4 × Fin 4) ⊕ (Fin 2 ⊕ (HRow × Fin 6))
abbrev Column := Visible ⊕ Fin 45

lemma sum_embedding {X Y Z : Type} (f : X → Z) (g : Y → Z)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (separate : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  intro a b same
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (hf same)
    | inr b => exact False.elim (separate a b same)
  | inr a =>
    cases b with
    | inl b => exact False.elim (separate b a same.symm)
    | inr b => exact congrArg Sum.inr (hg same)

end WeightSixteenDoubleCenters


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

end WeightSixteenSaturatedColumn


namespace WeightSixteenDoubleCenters

open Finset

abbrev Grid := Fin 4 × Fin 4

def allowedPairs : Finset (Finset Grid) :=
  ((Finset.univ : Finset Grid).powersetCard 2).filter fun T =>
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x.1 ≠ y.1 ∧ x.2 ≠ y.2

set_option maxHeartbeats 10000000 in
theorem allowed_pairs_card : allowedPairs.card = 72 := by decide +kernel

def codePair (M : HRow ⊕ Fin 72 → Column → Bool) (b : Fin 72) : Finset Grid :=
  Finset.univ.filter fun p => M (.inr b) (.inl (.inl p)) = true

theorem index_two_secants (M : HRow ⊕ Fin 72 → Column → Bool)
    (both : ∀ b, (codePair M b).card = 2)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (horizontal : ∀ a b j, M (.inl (.inl a)) (.inl (.inl (b,j))) = decide (a = b))
    (vertical : ∀ a b j, M (.inl (.inr a)) (.inl (.inl (j,b))) = decide (a = b)) :
    ∃ e : Fin 72 ≃ ↥allowedPairs, ∀ b, (e b).val = codePair M b := by
  let point (z : Grid) : Column := .inl (.inl z)
  have p_inj : Function.Injective point := fun _ _ eq => Sum.inl.inj (Sum.inl.inj eq)
  have on_pair (x : Grid) (b : Fin 72) :
      x ∈ codePair M b ↔ M (.inr b) (point x) = true := by simp [codePair,point]
  have inAllowed (b : Fin 72) : codePair M b ∈ allowedPairs := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,both b⟩,?_⟩
    intro x hx y hy different
    have y_ne := fun eq : point x = point y => different (p_inj eq)
    have onX := (on_pair x b).mp hx
    have onY := (on_pair y b).mp hy
    constructor
    · intro same
      have atX : M (.inl (.inl x.1)) (point x) = true := by simp [point,horizontal]
      have atY : M (.inl (.inl x.1)) (point y) = true := by simp [point,horizontal,same]
      have h := columnPairs _ _ y_ne (.inl (.inl x.1)) (.inr b) atX atY onX onY
      cases h
    · intro same
      have atX : M (.inl (.inr x.2)) (point x) = true := by simp [point,vertical]
      have atY : M (.inl (.inr x.2)) (point y) = true := by simp [point,vertical,same]
      have h := columnPairs _ _ y_ne (.inl (.inr x.2)) (.inr b) atX atY onX onY
      cases h
  let f (b : Fin 72) : ↥allowedPairs := ⟨codePair M b,inAllowed b⟩
  have inj : Function.Injective f := by
    intro b c equal
    have eq : codePair M b = codePair M c := congrArg Subtype.val equal
    obtain ⟨x,y,ne,land⟩ := Finset.card_eq_two.mp (both b)
    have hx : x ∈ codePair M b := land ▸ Finset.mem_insert_self _ _
    have hy : y ∈ codePair M b := land ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have same := columnPairs _ _ (fun h => ne (p_inj h)) (.inr b) (.inr c)
      ((on_pair x b).mp hx) ((on_pair y b).mp hy)
      ((on_pair x c).mp (eq ▸ hx)) ((on_pair y c).mp (eq ▸ hy))
    exact Sum.inr.inj same
  have counts : Fintype.card (Fin 72) = Fintype.card ↥allowedPairs := by
    rw [Fintype.card_fin,Fintype.card_coe,allowed_pairs_card]
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inj,counts⟩),fun _ => rfl⟩

end WeightSixteenDoubleCenters


namespace WeightSixteenDoubleCenters

open Finset

lemma card_filter_disjSum {X Y : Type} [Fintype X] [Fintype Y]
    (P : X ⊕ Y → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (.inl x)).card +
      (Finset.univ.filter fun y => P (.inr y)).card := by
  have same : Finset.univ.filter P = (Finset.univ.filter fun x => P (.inl x)).disjSum
      (Finset.univ.filter fun y => P (.inr y)) := by
    ext l
    cases l <;> simp [Finset.mem_filter]
  rw [same,Finset.card_disjSum]

theorem five_hidden_points (M : HRow ⊕ Fin 72 → Column → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (horizontal : ∀ a b j, M (.inl (.inl a)) (.inl (.inl (b,j))) = decide (a = b))
    (vertical : ∀ a b j, M (.inl (.inr a)) (.inl (.inl (j,b))) = decide (a = b))
    (block : ∀ a b i, M (.inl a) (.inl (.inr (.inr (b,i)))) = decide (a = b))
    (hidden : ∀ a i, M (.inl a) (.inr i) = false)
    (centers_off : ∀ b i, M (.inr b) (.inl (.inr (.inl i))) = false)
    (b : Fin 72) (legal : codePair M b ∈ allowedPairs) :
    (Finset.univ.filter fun q : Fin 45 => M (.inr b) (.inr q) = true).card = 5 := by
  classical
  obtain ⟨size,compat⟩ := Finset.mem_filter.mp legal
  have inside_size := (Finset.mem_powersetCard.mp size).2
  obtain ⟨x,y,ne,direct⟩ := Finset.card_eq_two.mp inside_size
  have mem_x : x ∈ codePair M b := direct ▸ Finset.mem_insert_self _ _
  have mem_y : y ∈ codePair M b := direct ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨differentL,differentR⟩ := compat x mem_x y mem_y ne
  let L := (.inl x.1 : HRow)
  let L' := (.inl y.1 : HRow)
  let R := (.inr x.2 : HRow)
  let R' := (.inr y.2 : HRow)
  let heavyMeet : Finset HRow := {L,L',R,R'}
  have cover_count : heavyMeet.card = 4 := by
    simp [heavyMeet,L,L',R,R',differentL,differentR]
  let privateHits := Finset.univ.filter (fun p : HRow × Fin 6 => M (.inr b) (.inl (.inr (.inr p))) = true)
  let otherHeavy := Finset.univ \ heavyMeet
  have member_iff (a : HRow) :
      a ∈ heavyMeet ↔ ∃ s ∈ codePair M b, M (.inl a) (.inl (.inl s)) = true := by
    rw [direct]
    cases a with
    | inl a => simp [heavyMeet,L,L',R,R',horizontal]
    | inr a => simp [heavyMeet,L,L',R,R',vertical]
  have block_iff (a : HRow) (pair : HRow × Fin 6) :
      M (.inl a) (.inl (.inr (.inr pair))) = true ↔ a = pair.1 := by
    simpa only [block,decide_eq_true_eq]
  have b_mem (s : Grid) : s ∈ codePair M b ↔ M (.inr b) (.inl (.inl s)) = true := by
    simp [codePair]
  have share (a : HRow) : ∃! p, M (.inl a) p = true ∧ M (.inr b) p = true :=
    rowPairs (.inl a) (.inr b) (by simp)
  have card_private : privateHits.card = otherHeavy.card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p present
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro conflict
      obtain ⟨s,hs,heavy⟩ := (member_iff p.1).mp conflict
      obtain ⟨_,_,unique⟩ := share p.1
      have one := unique (.inl (.inl s)) ⟨heavy,(b_mem s).mp hs⟩
      have two := unique (.inl (.inr (.inr p))) ⟨(block_iff p.1 p).mpr rfl,(Finset.mem_filter.mp present).2⟩
      have bad := Sum.inl.inj (one.trans two.symm)
      cases bad
    · intro p hp q hq same
      obtain ⟨_,_,unique⟩ := share p.1
      have here := unique (.inl (.inr (.inr p))) ⟨(block_iff p.1 p).mpr rfl,(Finset.mem_filter.mp hp).2⟩
      have there := unique (.inl (.inr (.inr q))) ⟨(block_iff p.1 q).mpr same,(Finset.mem_filter.mp hq).2⟩
      exact Sum.inr.inj (Sum.inr.inj (Sum.inl.inj (here.trans there.symm)))
    · intro a ha
      have missing := (Finset.mem_sdiff.mp ha).2
      obtain ⟨p,⟨heavy,light⟩,_⟩ := share a
      cases p with
      | inr i =>
        rw [hidden] at heavy
        contradiction
      | inl v =>
        cases v with
        | inl s =>
          exact False.elim (missing ((member_iff a).mpr ⟨s,(b_mem s).mpr light,heavy⟩))
        | inr w =>
          cases w with
          | inl i =>
            rw [centers_off] at light
            contradiction
          | inr pair =>
            exact ⟨pair,Finset.mem_filter.mpr ⟨Finset.mem_univ _,light⟩,((block_iff a pair).mp heavy).symm⟩
  have countOther : otherHeavy.card = 4 := by
    change (Finset.univ \ heavyMeet).card = 4
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ heavyMeet),Finset.card_univ,
      Fintype.card_sum,Fintype.card_fin,cover_count]
  have count_centers : (Finset.univ.filter fun i : Fin 2 => M (.inr b) (.inl (.inr (.inl i))) = true).card = 0 := by
    simp [centers_off]
  have row := rows (.inr b)
  rw [card_filter_disjSum,card_filter_disjSum,card_filter_disjSum] at row
  change (codePair M b).card + (_ + privateHits.card) + _ = 11 at row
  rw [inside_size,count_centers,card_private,countOther] at row
  omega

end WeightSixteenDoubleCenters


namespace WeightSixteenDoubleCenters

open Finset

abbrev SmallColumn := Visible ⊕ Fin 5
abbrev Rows := HRow ⊕ Fin 72
abbrev Incidence := Rows → Column → Bool

def oldCode (p : Grid) : Column := .inl (.inl p)

def newCode (p : Grid) : SmallColumn := .inl (.inl p)

theorem five_hidden_projection (M : Incidence)
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (codeDegree : ∀ p : Grid, (Finset.univ.filter fun l => M l (oldCode p) = true).card = 11)
    (invisible : ∀ a i, M (.inl a) (.inr i) = false)
    (b : Fin 72)
    (five : (Finset.univ.filter fun q : Fin 45 => M (.inr b) (.inr q) = true).card = 5) :
    ∃ f : SmallColumn ↪ Column,
      (∀ v : Visible, f (.inl v) = .inl v) ∧
      (∀ h : Fin 5, ∃ h' : Fin 45, f (.inr h) = .inr h' ∧ M (.inr b) (.inr h') = true) ∧
      (∀ a : HRow, (Finset.univ.filter fun x => M (.inl a) (f x) = true).card = 11) ∧
      (∀ a : HRow, ∀ l : Rows, .inl a ≠ l → ∃! x, M (.inl a) (f x) = true ∧ M l (f x) = true) ∧
      (∀ l : Rows, .inr b ≠ l → ∃! x, M (.inr b) (f x) = true ∧ M l (f x) = true) ∧
      (∀ p : Grid, ∀ x : SmallColumn, newCode p ≠ x →
        ∃! l, M l (f (newCode p)) = true ∧ M l (f x) = true) ∧
      (∀ x y : SmallColumn, x ≠ y → ∀ l m, M l (f x) = true → M l (f y) = true →
        M m (f x) = true → M m (f y) = true → l = m) := by
  classical
  let seen := Finset.univ.filter fun q : Fin 45 => M (.inr b) (.inr q) = true
  let pick : Fin 5 ≃ ↥seen := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact five)).symm
  let tail (i : Fin 5) : Column := .inr (pick i).val
  let start (v : Visible) : Column := .inl v
  let incl : SmallColumn → Column := Sum.elim start tail
  have injection : Function.Injective incl := sum_embedding start tail (fun _ _ => Sum.inl.inj)
    (fun _ _ eq => pick.injective (Subtype.ext (Sum.inr.inj eq))) (fun _ _ eq => by cases eq)
  let f : SmallColumn ↪ Column := ⟨incl,injection⟩
  have vis (v : Visible) : f (.inl v) = .inl v := rfl
  have hid (i : Fin 5) : f (.inr i) = .inr (pick i).val := rfl
  have staysOff (a : HRow) (i : Fin 5) : M (.inl a) (f (.inr i)) = false := by
    rw [hid,invisible]
  refine ⟨f,vis,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(pick i).val,hid i,(Finset.mem_filter.mp (pick i).property).2⟩
  · intro a
    have entire := rows (.inl a)
    rw [card_filter_disjSum] at entire ⊢
    have onlyVisibleOld : (Finset.univ.filter fun h : Fin 45 => M (.inl a) (.inr h) = true).card = 0 := by
      simp [invisible]
    have onlyVisibleNew : (Finset.univ.filter fun h : Fin 5 => M (.inl a) (f (.inr h)) = true).card = 0 := by
      simp [staysOff]
    rw [onlyVisibleNew]
    rw [onlyVisibleOld] at entire
    simpa only [vis] using entire
  · intro a l different
    obtain ⟨x,⟨hitA,hitB⟩,unique⟩ := rowPairs (.inl a) l different
    cases x with
    | inr i =>
      rw [invisible] at hitA
      contradiction
    | inl v =>
      refine ⟨.inl v,?_ ,?_⟩
      · simpa only [vis] using And.intro hitA hitB
      · intro y hy
        apply f.injective
        rw [vis]
        exact unique (f y) hy
  · intro l different
    obtain ⟨x,⟨at_b,at_l⟩,only⟩ := rowPairs (.inr b) l different
    have kept : ∃ y : SmallColumn, f y = x := by
      cases x with
      | inl v => exact ⟨.inl v,vis v⟩
      | inr j =>
        let z : ↥seen := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,at_b⟩⟩
        refine ⟨.inr (pick.symm z),?_⟩
        rw [hid,pick.apply_symm_apply]
    obtain ⟨y,aligned⟩ := kept
    refine ⟨y,?_ ,?_⟩
    · change M (.inr b) (f y) = true ∧ M l (f y) = true
      rw [aligned]
      exact ⟨at_b,at_l⟩
    · intro y' hy
      exact f.injective ((only (f y') hy).trans aligned.symm)
  · intro p x different
    have link : f (newCode p) = oldCode p := rfl
    rw [link]
    have ne : oldCode p ≠ f x := fun eq => different (f.injective (link.trans eq))
    exact WeightSixteenSaturatedColumn.saturated_column M (by decide +kernel) rows columnPairs
      (oldCode p) (codeDegree p) (f x) ne
  · intro x y different
    exact columnPairs (f x) (f y) (fun eq => different (f.injective eq))

end WeightSixteenDoubleCenters


namespace WeightSixteenDoubleCenters

open Finset

def onCode : Finset Column :=
  Finset.univ.filter fun c => ∃ a b : Fin 4, c = oldCode (a,b)

theorem select_hidden_projection (M : Incidence)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (columnPairs : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m)
    (rows : ∀ l, (Finset.univ.filter fun p => M l p = true).card = 11)
    (twos : ∀ b, (onCode.filter fun p => M (.inr b) p = true).card = 2)
    (interior : ∀ p ∈ onCode, (Finset.univ.filter fun a : HRow => M (.inl a) p = true).card = 2 ∧
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 9)
    (exterior : ∀ p ∉ onCode, 2*(Finset.univ.filter fun a : HRow => M (.inl a) p = true).card +
      (Finset.univ.filter fun b : Fin 72 => M (.inr b) p = true).card = 8)
    (horizontal : ∀ a b j, M (.inl (.inl a)) (.inl (.inl (b,j))) = decide (a = b))
    (vertical : ∀ a b j, M (.inl (.inr a)) (.inl (.inl (j,b))) = decide (a = b))
    (centers : ∀ a : Fin 4, ∀ i : Fin 2,
      M (.inl (.inl a)) (.inl (.inr (.inl i))) = decide (i = 0) ∧
      M (.inl (.inr a)) (.inl (.inr (.inl i))) = decide (i = 1))
    (block : ∀ a b i, M (.inl a) (.inl (.inr (.inr (b,i)))) = decide (a = b))
    (hidden : ∀ a i, M (.inl a) (.inr i) = false) :
    ∃ f : SmallColumn ↪ Column,
      (∀ v : Visible, f (.inl v) = .inl v) ∧
      (∀ h : Fin 5, ∃ h' : Fin 45, f (.inr h) = .inr h' ∧ M (.inr 0) (.inr h') = true) ∧
      (∀ a : HRow, (Finset.univ.filter fun x => M (.inl a) (f x) = true).card = 11) ∧
      (∀ a : HRow, ∀ l : Rows, .inl a ≠ l → ∃! x, M (.inl a) (f x) = true ∧ M l (f x) = true) ∧
      (∀ l : Rows, .inr 0 ≠ l → ∃! x, M (.inr 0) (f x) = true ∧ M l (f x) = true) ∧
      (∀ p : Grid, ∀ x : SmallColumn, newCode p ≠ x →
        ∃! l, M l (f (newCode p)) = true ∧ M l (f x) = true) := by
  have inside_eq (p : Column) : p ∈ onCode ↔ ∃ a b : Fin 4, p = oldCode (a,b) := by simp [onCode]
  have index_injective : Function.Injective oldCode := fun _ _ eq => Sum.inl.inj (Sum.inl.inj eq)
  have twos' (b : Fin 72) : (codePair M b).card = 2 := by
    refine (show (codePair M b).card = (onCode.filter fun p => M (.inr b) p = true).card from ?_).trans (twos b)
    apply Finset.card_bij (fun z _ => oldCode z)
    · intro z hz
      refine Finset.mem_filter.mpr ⟨(inside_eq _).mpr ⟨z.1,z.2,rfl⟩,?_⟩
      exact (Finset.mem_filter.mp hz).2
    · intro x _ y _ equal
      exact index_injective equal
    · intro p hp
      obtain ⟨isInside,onB⟩ := Finset.mem_filter.mp hp
      obtain ⟨a,c,rfl⟩ := (inside_eq p).mp isInside
      exact ⟨(a,c),Finset.mem_filter.mpr ⟨Finset.mem_univ _,onB⟩,rfl⟩
  have degree (p : Grid) : (Finset.univ.filter fun l => M l (oldCode p) = true).card = 11 := by
    have code : oldCode p ∈ onCode := (inside_eq _).mpr ⟨p.1,p.2,rfl⟩
    have census := interior _ code
    rw [card_filter_disjSum,census.1,census.2]
  have centers_off (b : Fin 72) (i : Fin 2) : M (.inr b) (.inl (.inr (.inl i))) = false := by
    let c : Column := .inl (.inr (.inl i))
    have ext : c ∉ onCode := by
      intro hit
      obtain ⟨a,v,eq⟩ := (inside_eq c).mp hit
      have impossible := Sum.inl.inj eq
      cases impossible
    have card_upper : (Finset.univ.filter fun a : HRow => M (.inl a) c = true).card = 4 := by
      rw [card_filter_disjSum]
      have left (a : Fin 4) : M (.inl (.inl a)) c = decide (i = 0) := (centers a i).1
      have right (a : Fin 4) : M (.inl (.inr a)) c = decide (i = 1) := (centers a i).2
      fin_cases i <;> simp only [left,right] <;> decide +kernel
    have Bdegree : (Finset.univ.filter fun u : Fin 72 => M (.inr u) c = true).card = 0 := by
      have bounds := exterior c ext
      rw [card_upper] at bounds
      omega
    change M (.inr b) c = false
    cases hit : M (.inr b) c
    · rfl
    · have found : b ∈ Finset.univ.filter fun u : Fin 72 => M (.inr u) c = true :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
      have impossible := Finset.card_pos.mpr ⟨b,found⟩
      omega
  obtain ⟨e,eCode⟩ := index_two_secants M twos' columnPairs horizontal vertical
  have lawful : codePair M 0 ∈ allowedPairs := eCode 0 ▸ (e 0).property
  have five := five_hidden_points M rowPairs rows horizontal vertical block hidden centers_off 0 lawful
  obtain ⟨f,vis,hits,complete,heavy_meet,secant_meet,code_meet,_⟩ :=
    five_hidden_projection M rows rowPairs columnPairs degree hidden 0 five
  exact ⟨f,vis,hits,complete,heavy_meet,secant_meet,code_meet⟩

end WeightSixteenDoubleCenters


open WeightSixteenDoubleCenters

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H2_R1_H3_R1_H2_R1.H1
  dsimp only
  intro M rows twos interior exterior rowPairs columnPairs horiz vert centers block hidden
  exact select_hidden_projection M rowPairs columnPairs rows twos interior exterior horiz vert centers block hidden

