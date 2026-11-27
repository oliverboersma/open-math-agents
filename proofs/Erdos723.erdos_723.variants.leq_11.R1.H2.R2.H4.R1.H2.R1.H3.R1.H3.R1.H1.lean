import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Basic

/-! The fiber and relabeling lemmas are adapted from @avivorly, merged PR
4295, commit 2480861cef03dcc829e98474d65d97ff9dfe50e6. Apply the triple
normal form to the unique triple through both points outside the four-set.
The nineteen-column representative is checked directly. -/

namespace WeightNineteenSupportRelabel

open Finset
open scoped BigOperators

abbrev Columns := Fin 19 → Finset (Fin 6)

def shared (C : Columns) : Finset (Fin 19) :=
  Finset.univ.filter fun p => 2 ≤ (C p).card

def layout (C : Columns) : Finset (Finset (Fin 6)) :=
  (shared C).image C

def fiber (C : Columns) (s : Finset (Fin 6)) : Finset (Fin 19) :=
  Finset.univ.filter fun p => C p = s

lemma mem_fiber (C : Columns) (s : Finset (Fin 6)) (p : Fin 19) :
    p ∈ fiber C s ↔ C p = s := by simp [fiber]

lemma injective_shared (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    (shared C : Set (Fin 19)).InjOn C := by
  intro p hp q hq same
  by_contra different
  have small := overlap p q different
  rw [same,Finset.inter_self] at small
  have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
  omega

lemma high_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (s : Finset (Fin 6)) (many : 2 ≤ s.card) :
    (fiber C s).card = if s ∈ layout C then 1 else 0 := by
  by_cases yes : s ∈ layout C
  · rw [if_pos yes]
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp yes
    apply Finset.card_eq_one.mpr
    refine ⟨p,?_⟩
    ext q
    rw [mem_fiber,Finset.mem_singleton]
    constructor
    · intro hs
      have hq : q ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
      exact injective_shared C overlap hq hp (hs.trans eq.symm)
    · rintro rfl
      exact eq
  · rw [if_neg yes]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hs := (mem_fiber C s p).mp hp
    have here : p ∈ shared C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs.symm ▸ many⟩
    exact yes (hs ▸ Finset.mem_image_of_mem C here)

lemma single_fiber (C : Columns)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (a : Fin 6) :
    (fiber C {a}).card + ((layout C).filter fun s => a ∈ s).card =
      (Finset.univ.filter fun p => a ∈ C p).card := by
  let high := (shared C).filter fun p => a ∈ C p
  have image_high : high.image C = (layout C).filter fun s => a ∈ s := by
    ext s
    constructor
    · rintro hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨sharedp,one⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ sharedp,one⟩
    · rintro hs
      obtain ⟨in_layout,one⟩ := Finset.mem_filter.mp hs
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp in_layout
      exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,one⟩,rfl⟩
  have inj : (high : Set (Fin 19)).InjOn C := by
    intro p hp q hq same
    exact injective_shared C overlap (Finset.filter_subset _ _ hp) (Finset.filter_subset _ _ hq) same
  have high_count := Finset.card_image_of_injOn inj
  rw [image_high] at high_count
  have apart : Disjoint (fiber C {a}) high := by
    rw [Finset.disjoint_left]
    intro p hf hp
    have hs := (mem_fiber C {a} p).mp hf
    have many := (Finset.mem_filter.mp ((Finset.mem_filter.mp hp).1)).2
    rw [hs,Finset.card_singleton] at many
    omega
  have cover : fiber C {a} ∪ high = Finset.univ.filter fun p => a ∈ C p := by
    ext p
    rw [Finset.mem_union, mem_fiber]
    have hit : p ∈ (Finset.univ.filter fun p => a ∈ C p) ↔ a ∈ C p := by simp
    rw [hit]
    constructor
    · rintro (one | above)
      · rw [one]
        simp
      · exact (Finset.mem_filter.mp above).2
    · intro on_a
      by_cases many : 2 ≤ (C p).card
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ p,many⟩,on_a⟩)
      · apply Or.inl
        symm
        apply Finset.eq_of_subset_of_card_le ((Finset.singleton_subset_iff).mpr on_a)
        rw [Finset.card_singleton]
        omega
  rw [high_count,← Finset.card_union_of_disjoint apart,cover]

lemma sum_fibers (C : Columns) : (∑ s : Finset (Fin 6), (fiber C s).card) = 19 := by
  calc
    _ = ∑ s : Finset (Fin 6), ∑ p : Fin 19, if C p = s then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.sum_filter]
      simp [fiber]
    _ = ∑ p : Fin 19, ∑ s : Finset (Fin 6), if C p = s then (1 : Nat) else 0 := Finset.sum_comm
    _ = 19 := by simp [eq_comm]

theorem relabel_columns (C D : Columns)
    (c_overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (d_overlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (c_row : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (d_row : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 5)
    (same : layout C = layout D) :
    ∃ e : Equiv.Perm (Fin 19), ∀ p, D (e p) = C p := by
  classical
  have counts_ne (s : Finset (Fin 6)) (nonzero : s ≠ ∅) : (fiber C s).card = (fiber D s).card := by
    by_cases large : 2 ≤ s.card
    · rw [high_fiber C c_overlap s large,high_fiber D d_overlap s large,same]
    · have pos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr nonzero)
      obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
      have left := single_fiber C c_overlap a
      have right := single_fiber D d_overlap a
      rw [same,c_row] at left
      rw [d_row] at right
      omega
  have all_counts (s : Finset (Fin 6)) : (fiber C s).card = (fiber D s).card := by
    by_cases zero : s = ∅
    · subst s
      let nonempty := (Finset.univ : Finset (Finset (Fin 6))).erase ∅
      have agree : (∑ s ∈ nonempty, (fiber C s).card) = ∑ s ∈ nonempty, (fiber D s).card := by
        apply Finset.sum_congr rfl
        intro s hs
        exact counts_ne s (Finset.ne_of_mem_erase hs)
      have hc := Finset.sum_erase_add Finset.univ (fun s => (fiber C s).card) (Finset.mem_univ ∅)
      have hd := Finset.sum_erase_add Finset.univ (fun s => (fiber D s).card) (Finset.mem_univ ∅)
      rw [sum_fibers] at hc hd
      change (∑ s ∈ nonempty, (fiber C s).card) + (fiber C ∅).card = 19 at hc
      change (∑ s ∈ nonempty, (fiber D s).card) + (fiber D ∅).card = 19 at hd
      omega
    · exact counts_ne s zero
  let match_card (s : Finset (Fin 6)) : Fintype.card ↥(fiber C s) = Fintype.card ↥(fiber D s) := by
    rw [Fintype.card_coe,Fintype.card_coe,all_counts]
  let fibers (s : Finset (Fin 6)) : ↥(fiber C s) ≃ ↥(fiber D s) :=
    (Fintype.equivOfCardEq (match_card s))
  let as_fiber (W : Columns) (s : Finset (Fin 6)) : {p // W p = s} ≃ ↥(fiber W s) :=
    Equiv.subtypeEquivProp (funext fun p => propext (mem_fiber W s p).symm)
  let mapped (s : Finset (Fin 6)) : {p // C p = s} ≃ {p // D p = s} :=
    ((as_fiber C s).trans (fibers s)).trans (as_fiber D s).symm
  let e : Equiv.Perm (Fin 19) :=
    (Equiv.sigmaFiberEquiv C).symm.trans
      ((Equiv.sigmaCongrRight mapped).trans (Equiv.sigmaFiberEquiv D))
  exact ⟨e,fun p => (mapped (C p) ⟨p,rfl⟩).property⟩

end WeightNineteenSupportRelabel


namespace WeightNineteenFourRelabel

open Finset

theorem relabel_four (s : Finset (Fin 6)) (card_four : s.card = 4) (x : Fin 6) (hx : x ∈ s) :
    ∃ e : Equiv.Perm (Fin 6), e x = 0 ∧ ∀ y, y ∈ s ↔ (e y).val < 4 := by
  classical
  let t := Finset.univ \ s
  have card_two : t.card = 2 := by
    change (Finset.univ \ s).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s),Finset.card_univ,Fintype.card_fin,card_four]
  let left0 : Fin 4 ≃ ↥s := (Fintype.equivFinOfCardEq (by rwa [Fintype.card_coe])).symm
  let left := (Equiv.swap 0 (left0.symm ⟨x,hx⟩)).trans left0
  let right : Fin 2 ≃ ↥t := (Fintype.equivFinOfCardEq (by rwa [Fintype.card_coe])).symm
  let asComplement : ↥t ≃ {i // i ∉ s} :=
    Equiv.subtypeEquivProp (funext fun i => propext (by simp [t]))
  let pack := (Equiv.sumCongr left (right.trans asComplement)).trans (Equiv.sumCompl (· ∈ s))
  let fromSum : Fin 4 ⊕ Fin 2 ≃ Fin 6 := finSumFinEquiv
  let e : Equiv.Perm (Fin 6) := pack.symm.trans fromSum
  refine ⟨e,?_,?_⟩
  · have on_zero : pack (.inl 0) = x := by
      change (left 0).val = x
      simp [left]
    have there : pack.symm x = .inl 0 := by
      rw [← on_zero,Equiv.symm_apply_apply]
    change fromSum (pack.symm x) = 0
    rw [there]
    rfl
  · intro y
    let z := pack.symm y
    have yz : pack z = y := pack.apply_symm_apply _
    change y ∈ s ↔ (fromSum z).val < 4
    cases found : z with
    | inl a =>
      have ya : y = (left a).val := yz.symm.trans (by
        rw [found]; rfl)
      constructor
      · intro _
        exact a.isLt
      · intro _
        exact ya.symm ▸ (left a).property
    | inr a =>
      have ya : y = (right a).val := yz.symm.trans (by
        rw [found]; rfl)
      have absent : y ∉ s := fun present => (Finset.mem_sdiff.mp (right a).property).2 (ya ▸ present)
      have large : ¬ (fromSum (.inr a)).val < 4 := by
        change ¬ (4 + a.val) < 4
        omega
      exact ⟨fun hs => (absent hs).elim, fun ht => (large ht).elim⟩

end WeightNineteenFourRelabel

namespace WeightNineteenFourRelabel

open Finset

def firstFour : Finset (Fin 6) := {0,1,2,3}

def outerPair : Finset (Fin 6) := Finset.univ \ firstFour

def available (S : Finset (Fin 6)) : Finset (Finset (Fin 6)) :=
  (Finset.univ : Finset (Fin 6)).powersetCard 2 \ S.powersetCard 2

def transform (e : Equiv.Perm (Fin 6)) : Finset (Fin 6) ↪ Finset (Fin 6) :=
  (Finset.mapEmbedding e.toEmbedding).toEmbedding

lemma first_four_char : ∀ a : Fin 6, a ∈ firstFour ↔ a.val < 4 := by decide +kernel

lemma moves_four (S : Finset (Fin 6)) (e : Equiv.Perm (Fin 6))
    (form : ∀ y, y ∈ S ↔ (e y).val < 4) :
    S.map e.toEmbedding = firstFour := by
  ext y
  rw [Finset.mem_map_equiv,form,(e.apply_symm_apply y),first_four_char]

lemma move_available (S : Finset (Fin 6)) (e : Equiv.Perm (Fin 6)) :
    (available S).map (transform e) = available (S.map e.toEmbedding) := by
  unfold available transform
  rw [Finset.map_sdiff,← Finset.powersetCard_map,← Finset.powersetCard_map,Finset.map_univ_equiv]

theorem normal_four_with_triple (S T : Finset (Fin 6)) (F : Finset (Finset (Fin 6)))
    (four : S.card = 4)
    (three : T.card = 3) (outer : (Finset.univ \ S) ⊆ T)
    (full : F = insert S (insert T (available S \ T.powersetCard 2))) :
    ∃ e : Equiv.Perm (Fin 6),
      F.map (transform e) = insert firstFour (insert (insert 0 outerPair)
        (available firstFour \ (insert 0 outerPair).powersetCard 2)) := by
  let D := Finset.univ \ S
  have card_two : D.card = 2 := by
    change (Finset.univ \ S).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),Finset.card_univ,Fintype.card_fin,four]
  have residue : (T \ D).card = 1 := by rw [Finset.card_sdiff_of_subset outer,three,card_two]
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp residue
  have mem : u ∈ T \ D := hu ▸ Finset.mem_singleton_self u
  have inS : u ∈ S := by
    by_contra absent
    have belongs : u ∈ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,absent⟩
    exact (Finset.mem_sdiff.mp mem).2 belongs
  have expandT : T = insert u D := by
    ext x
    rw [Finset.mem_insert]
    constructor
    · intro onT
      by_cases inD : x ∈ D
      · exact Or.inr inD
      · have on : x ∈ T \ D := Finset.mem_sdiff.mpr ⟨onT,inD⟩
        rw [hu] at on
        exact Or.inl (Finset.mem_singleton.mp on)
    · rintro (left | right)
      · exact left.symm ▸ (Finset.mem_sdiff.mp mem).1
      · exact outer right
  obtain ⟨e,marked,chosen⟩ := relabel_four S four u inS
  have moved := moves_four S e chosen
  have outside : D.map e.toEmbedding = outerPair := by
    change (Finset.univ \ S).map e.toEmbedding = outerPair
    rw [Finset.map_sdiff,Finset.map_univ_equiv,moved]
    rfl
  have tripleRelabeled : T.map e.toEmbedding = insert 0 outerPair := by
    rw [expandT,Finset.map_insert,Equiv.toEmbedding_apply,marked,outside]
  refine ⟨e,?_⟩
  rw [full,Finset.map_insert,Finset.map_insert,Finset.map_sdiff,move_available]
  change insert (S.map e.toEmbedding) (insert (T.map e.toEmbedding)
    (available (S.map e.toEmbedding) \ (T.powersetCard 2).map (transform e))) = _
  unfold transform
  rw [← Finset.powersetCard_map,moved,tripleRelabeled]

end WeightNineteenFourRelabel

namespace WeightNineteenFourNormalize

open Finset WeightNineteenSupportRelabel WeightNineteenFourRelabel

def relabel (C : Columns) (e : Equiv.Perm (Fin 6)) : Columns :=
  fun p => (C p).map e.toEmbedding

lemma layout_relabel (C : Columns) (e : Equiv.Perm (Fin 6)) :
    layout (relabel C e) = (layout C).map (transform e) := by
  have same : shared (relabel C e) = shared C := by
    ext p
    simp only [shared,Finset.mem_filter,relabel,Finset.card_map]
  unfold layout
  rw [same,Finset.map_eq_image,Finset.image_image]
  rfl

theorem use_canonical_columns (C D : Columns) (e : Equiv.Perm (Fin 6))
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1)
    (rows : ∀ a, (Finset.univ.filter fun p => a ∈ C p).card = 5)
    (targetOverlap : ∀ p q, p ≠ q → (D p ∩ D q).card ≤ 1)
    (targetRows : ∀ a, (Finset.univ.filter fun p => a ∈ D p).card = 5)
    (matched : (layout C).map (transform e) = layout D) :
    ∃ π : Equiv.Perm (Fin 19), ∀ p, relabel C e (π p) = D p := by
  have movedOverlap (p q : Fin 19) (different : p ≠ q) :
      (relabel C e p ∩ relabel C e q).card ≤ 1 := by
    have same : relabel C e p ∩ relabel C e q = (C p ∩ C q).map e.toEmbedding := by
      ext a
      simp only [relabel,Finset.mem_inter,Finset.mem_map_equiv]
    rw [same,Finset.card_map]
    exact overlap p q different
  have movedRows (a : Fin 6) : (Finset.univ.filter fun p => a ∈ relabel C e p).card = 5 := by
    have same : (Finset.univ.filter fun p => a ∈ relabel C e p) =
        Finset.univ.filter fun p => e.symm a ∈ C p := by
      ext p
      simp only [relabel,Finset.mem_filter,Finset.mem_map_equiv]
    rw [same,rows]
  obtain ⟨π,form⟩ := relabel_columns (relabel C e) D movedOverlap targetOverlap movedRows targetRows
    ((layout_relabel C e).trans matched)
  exact ⟨π.symm,fun p => by simpa only [Equiv.apply_symm_apply] using (form (π.symm p)).symm⟩

lemma normal_triple_family (F : Finset (Finset (Fin 6))) (U T : Finset (Fin 6))
    (hu : U ∈ F) (hT : T ∈ F) (four : U.card = 4) (three : T.card = 3)
    (sizes : ∀ V ∈ F, 2 ≤ V.card ∧ V.card ≤ 4)
    (overlap : ∀ V ∈ F, ∀ W ∈ F, V ≠ W → (V ∩ W).card ≤ 1)
    (outer : (Finset.univ \ U) ⊆ T)
    (pairs : F.filter (fun V => V.card = 2) = available U \ T.powersetCard 2) :
    F = insert U (insert T (available U \ T.powersetCard 2)) := by
  have outside : (Finset.univ \ U).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),Finset.card_univ,Fintype.card_fin,four]
  have covered : F = insert U (insert T (F.filter fun V => V.card = 2)) := by
    ext V
    rw [Finset.mem_insert,Finset.mem_insert,Finset.mem_filter]
    constructor
    · intro hv
      by_cases isTwo : V.card = 2
      · exact Or.inr (Or.inr ⟨hv,isTwo⟩)
      by_cases vu : V = U
      · exact Or.inl vu
      by_cases vt : V = T
      · exact Or.inr (Or.inl vt)
      have vcard := sizes V hv
      have small := overlap V hv U hu vu
      have bound := (Finset.card_le_card (Finset.subset_univ (V ∪ U))).trans_eq (Fintype.card_fin 6)
      have union := Finset.card_union_add_card_inter V U
      have inter := overlap V hv T hT vt
      have shared : 2 ≤ (V \ U).card := by rw [Finset.card_sdiff,Finset.inter_comm U V]; omega
      have included : V \ U ⊆ Finset.univ \ U := by
        intro a ha
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp ha).2⟩
      have capture : V \ U ⊆ V ∩ T := by
        intro a ha
        exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ha).1,outer (included ha)⟩
      have le := Finset.card_le_card capture
      omega
    · rintro (rfl | rfl | ⟨hv,_⟩)
      · exact hu
      · exact hT
      · exact hv
  rw [covered,pairs]

end WeightNineteenFourNormalize


open Finset WeightNineteenSupportRelabel WeightNineteenFourRelabel WeightNineteenFourNormalize

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1.H1 := by
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H3_R1_H3_R1.H1
  dsimp only
  intro C overlap rows maxSize U hU four T hT three outer pairs

  let F := layout C
  have sizes (V : Finset (Fin 6)) (hv : V ∈ F) : 2 ≤ V.card ∧ V.card ≤ 4 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(Finset.mem_filter.mp hp).2,maxSize p⟩
  have separated (V : Finset (Fin 6)) (hv : V ∈ F) (W : Finset (Fin 6)) (hw : W ∈ F)
      (different : V ≠ W) : (V ∩ W).card ≤ 1 := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hw
    exact overlap p q (fun eq => different (congrArg C eq))

  have full := normal_triple_family F U T hU hT four three sizes separated outer pairs
  obtain ⟨e,moved⟩ := normal_four_with_triple U T F four three outer full
  let D (p : Fin 19) := (([[0, 1, 2, 3], [0, 4, 5], [1, 4], [1, 5], [2, 4], [2, 5], [3, 4], [3, 5], [0], [0], [0], [1], [1], [2], [2], [3], [3], [4], [5]] : List (List (Fin 6)))[p.val]!).toFinset
  have targetOverlap : ∀ p q : Fin 19, p ≠ q → (D p ∩ D q).card ≤ 1 := by decide +kernel
  have targetRows : ∀ a : Fin 6, (Finset.univ.filter fun p => a ∈ D p).card = 5 := by decide +kernel
  have eq : layout D = insert firstFour (insert (insert 0 outerPair)
      (available firstFour \ (insert 0 outerPair).powersetCard 2)) := by decide +kernel
  obtain ⟨π,matched⟩ := use_canonical_columns C D e overlap rows targetOverlap targetRows (moved.trans eq.symm)
  exact ⟨e,π,matched⟩
