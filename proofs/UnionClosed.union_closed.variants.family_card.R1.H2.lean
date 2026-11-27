import OMAReductions.R_UnionClosed_union_closed_variants_family_card_R1
import Mathlib

namespace OMA.UnionClosed50Structure
open Finset UnionClosed
open OMA.R_UnionClosed_union_closed_variants_family_card_R1
open scoped Classical

def freq {α : Type*} (F : Finset (Finset α)) [DecidableEq α] (i : α) : ℕ :=
  (F.filter (i ∈ ·)).card

private theorem unionMember {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (hc : IsUnionClosed F) (B : Finset (Finset α)) (sub : B ⊆ F) (hn : B.Nonempty) :
    B.biUnion id ∈ F := by
  induction B using Finset.induction_on with
  | empty => simp at hn
  | @insert X B _ ih =>
    have hx : X ∈ F := sub (mem_insert_self ..)
    by_cases nonempty : B.Nonempty
    · rw [biUnion_insert]
      exact hc _ hx _ (ih (fun _ h => sub (mem_insert_of_mem h)) nonempty)
    · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
      simpa using hx

/-- Choose a union-irreducible set having a prescribed coordinate, and contained
in a prescribed upper set. If it splits as a union, one factor still qualifies. -/
private theorem basisBelow {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (hc : IsUnionClosed F) {U : Finset α} (hU : U ∈ F) {x : α} (hx : x ∈ U) :
    ∃ B ∈ F, x ∈ B ∧ B ⊆ U ∧ IsUnionClosed (F.erase B) := by
  classical
  let K := F.filter (fun B => x ∈ B ∧ B ⊆ U)
  have hK : K.Nonempty := ⟨U,mem_filter.mpr ⟨hU,hx,Subset.rfl⟩⟩
  obtain ⟨B,hB,least⟩ := K.exists_min_image Finset.card hK
  obtain ⟨bF,xb,bu⟩ := mem_filter.mp hB
  refine ⟨B,bF,xb,bu,?_⟩
  intro V hV W hW
  refine mem_erase.mpr ⟨?_,hc _ (mem_erase.mp hV).2 _ (mem_erase.mp hW).2⟩
  intro eq
  have proper (T : Finset α) (hT : T ∈ F.erase B) (tB : T ⊆ B) (xt : x ∈ T) : False := by
    have lc := least T (mem_filter.mpr ⟨(mem_erase.mp hT).2,xt,tB.trans bu⟩)
    exact (mem_erase.mp hT).1 (eq_of_subset_of_card_le tB lc)
  have xvw := mem_union.mp (eq.symm ▸ xb : x ∈ V ∪ W)
  rcases xvw with xv | xw
  · exact proper V hV (eq ▸ subset_union_left) xv
  · exact proper W hW (eq ▸ subset_union_right) xw

private theorem freqErase {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    {B : Finset α} (hb : B ∈ F) {x : α} (hx : x ∈ B) :
    freq (F.erase B) x = freq F x - 1 := by
  classical
  have h : (F.erase B).filter (x ∈ ·) = (F.filter (x ∈ ·)).erase B := by
    ext; simp [and_assoc]
  exact (congrArg Finset.card h).trans (card_erase_of_mem (mem_filter.mpr ⟨hb,hx⟩))

private theorem freqMono {α : Type*} [DecidableEq α] {B F : Finset (Finset α)} (sub : B ⊆ F)
    (x : α) : freq B x ≤ freq F x := card_le_card (filter_subset_filter _ sub)

lemma structural : H2 := by
  classical
  intro m n hm F active sep hc count cap heavy minimal
  change ∀ i, freq F i ≤ n at cap
  change ∃ i, freq F i = n at heavy
  let M (i : Fin m) := (F.filter (i ∉ ·)).biUnion id
  have avoid (i : Fin m) : i ∉ M i := by
    intro hi
    obtain ⟨X,hX,hix⟩ := mem_biUnion.mp hi
    exact (mem_filter.mp hX).2 hix
  have inside (i : Fin m) (X : Finset (Fin m)) (hX : X ∈ F) (hi : i ∉ X) : X ⊆ M i :=
    fun _ hy => mem_biUnion.mpr ⟨X,mem_filter.mpr ⟨hX,hi⟩,hy⟩
  have maximal (i : Fin m) : M i ∈ F := by
    apply unionMember hc _ (filter_subset ..)
    apply card_pos.mp
    have parts := card_filter_add_card_filter_not (s := F) (p := fun X => i ∈ X)
    change freq F i + (F.filter (i ∉ ·)).card = F.card at parts
    have := cap i
    omega
  have inj : Function.Injective M := by
    intro i j eq
    apply sep
    ext X
    simp only [mem_filter]
    by_cases hX : X ∈ F
    · simp only [hX,true_and]
      constructor
      · intro hi
        by_contra hj
        exact avoid i (eq.symm ▸ inside j X hX hj hi)
      · intro hj
        by_contra hi
        exact avoid j (eq ▸ inside i X hX hi hj)
    · simp [hX]
  have ground : (univ : Finset (Fin m)) ∈ F := by
    have hn : F.Nonempty := card_pos.mp (by omega)
    have h := unionMember hc F (fun _ h => h) hn
    have eq : F.biUnion id = univ := by
      apply eq_univ_of_forall
      intro i
      obtain ⟨X,hX,hi⟩ := active i
      exact mem_biUnion.mpr ⟨X,hX,hi⟩
    rwa [eq] at h
  let G := univ.image M
  let C : Finset (Finset (Fin m)) := insert univ G
  have gc : G.card = m := by simp [G,card_image_of_injective _ inj]
  have topNot : univ ∉ G := by
    intro h
    obtain ⟨i,_,eq⟩ := mem_image.mp h
    exact avoid i (eq.symm ▸ mem_univ i)
  have sub : C ⊆ F := by
    intro U hu
    rcases mem_insert.mp hu with rfl | h
    · exact ground
    · obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact maximal i
  have cb : C.card = m+1 := by change (insert univ G).card = _; rw [card_insert_of_notMem topNot,gc]
  have enough : 2 ≤ n := by have := card_le_card sub; omega
  have other (z i : Fin m) (hz : freq F z = n) (diff : z ≠ i) : z ∈ M i := by
    by_contra missing
    have dominated : F.filter (z ∈ ·) ⊆ F.filter (i ∈ ·) := by
      intro X hX
      have ⟨hX,hzX⟩ := mem_filter.mp hX
      refine mem_filter.mpr ⟨hX,?_⟩
      by_contra hi
      exact missing (inside i X hX hi hzX)
    have equal := eq_of_subset_of_card_le dominated (show freq F i ≤ freq F z by rw [hz]; exact cap i)
    exact diff (sep equal)
  have cannotErase (i : Fin m) : ¬ IsUnionClosed (F.erase (M i)) := by
    intro eraseClosed
    let E := F.erase (M i)
    have Ecard : E.card = 2*n := by change (F.erase (M i)).card = _; rw [card_erase_of_mem (maximal i),count]; omega
    have Esub : E ⊆ F := erase_subset .. 
    have Eproper : E.card < F.card := by omega
    by_cases hi : freq F i = n
    · obtain ⟨U,hU,iu⟩ := active i
      obtain ⟨B,bF,ib,_,bc⟩ := basisBelow hc hU iu
      have diff : B ≠ M i := fun eq => avoid i (eq ▸ ib)
      have bE : B ∈ E := mem_erase.mpr ⟨diff,bF⟩
      let V := E.erase B
      have vc : IsUnionClosed V := by
        intro X hx Y hy
        have ⟨nx,hxE⟩ := mem_erase.mp hx
        have ⟨ny,hyE⟩ := mem_erase.mp hy
        have v1 := eraseClosed X hxE Y hyE
        have v2 := bc X (mem_erase.mpr ⟨nx,Esub hxE⟩) Y (mem_erase.mpr ⟨ny,Esub hyE⟩)
        exact mem_erase.mpr ⟨(mem_erase.mp v2).1,v1⟩
      have vcard : V.card = 2*n-1 := by change (E.erase B).card = _; rw [card_erase_of_mem bE,Ecard]
      have nt : V ≠ {∅} := by
        intro eq
        have : V.card = 1 := by rw [eq,card_singleton]
        omega
      obtain ⟨z,hz⟩ := minimal V ((erase_subset B E).trans Esub) (by omega) nt vc
      change V.card ≤ 2*freq V z at hz
      have vb : freq V z ≤ freq E z := freqMono (erase_subset ..) z
      have ef : freq E z ≤ freq F z := freqMono Esub z
      have zfull : freq F z = n := by have := cap z; omega
      by_cases iz : z = i
      · subst z
        have h : freq V i = freq E i-1 := freqErase E bE ib
        omega
      · have h : freq E z = freq F z-1 := freqErase F (maximal i) (other z i zfull iz)
        omega
    · have nt : E ≠ {∅} := by
        intro eq
        have : E.card = 1 := by rw [eq,card_singleton]
        omega
      obtain ⟨z,hz⟩ := minimal E Esub Eproper nt eraseClosed
      change E.card ≤ 2*freq E z at hz
      have ef : freq E z ≤ freq F z := freqMono Esub z
      have zfull : freq F z = n := by have := cap z; omega
      have diff : z ≠ i := fun eq => hi (eq ▸ zfull)
      have h : freq E z = freq F z-1 := freqErase F (maximal i) (other z i zfull diff)
      omega
  let D := F \ C
  obtain ⟨y,_,highest⟩ := univ.exists_max_image (freq D) (show (univ : Finset (Fin m)).Nonempty from ⟨⟨0,by omega⟩,mem_univ _⟩)
  have alldiff (i : Fin m) (diff : y ≠ i) : y ∈ M i := by
    by_contra absent
    have dom (X : Finset (Fin m)) (hX : X ∈ F) (hy : y ∈ X) : i ∈ X := by
      by_contra hi
      exact absent (inside i X hX hi hy)
    have strictCol : ∃ U ∈ F, i ∈ U ∧ y ∉ U := by
      by_contra! no
      apply diff
      apply sep
      ext U
      simp only [mem_filter]
      exact ⟨fun h => ⟨h.1,dom U h.1 h.2⟩,fun h => ⟨h.1,no U h.1 h.2⟩⟩
    obtain ⟨U,hU,iu,ny⟩ := strictCol
    obtain ⟨B,bF,ib,bu,bc⟩ := basisBelow hc hU iu
    have yb : y ∉ B := fun hy => ny (bu hy)
    have bd : B ∈ D := by
      apply mem_sdiff.mpr
      refine ⟨bF,?_⟩
      intro h
      rcases mem_insert.mp h with eq | hG
      · exact yb (eq.symm ▸ mem_univ y)
      · obtain ⟨j,_,eq⟩ := mem_image.mp hG
        exact cannotErase j (eq.symm ▸ bc)
    have inc : D.filter (y ∈ ·) ⊆ D.filter (i ∈ ·) := by
      intro X hX
      obtain ⟨hD,hy⟩ := mem_filter.mp hX
      exact mem_filter.mpr ⟨hD,dom X (mem_sdiff.mp hD).1 hy⟩
    have same := eq_of_subset_of_card_le inc (highest i (mem_univ _))
    have h : B ∈ D.filter (y ∈ ·) := same.symm ▸ (mem_filter.mpr ⟨bd,ib⟩ : B ∈ D.filter (i ∈ ·))
    exact yb (mem_filter.mp h).2
  have counted : m ≤ freq C y := by
    let J := (univ.erase y).image M
    have jsub : J ⊆ G := image_subset_image (erase_subset ..)
    have jcount : J.card = m-1 := by
      change ((univ.erase y).image M).card = _
      rw [card_image_of_injective _ inj,card_erase_of_mem (mem_univ y),card_univ,Fintype.card_fin]
    have cov : insert univ J ⊆ C.filter (y ∈ ·) := by
      intro X hX
      rcases mem_insert.mp hX with rfl | hj
      · exact mem_filter.mpr ⟨mem_insert_self ..,mem_univ _⟩
      · obtain ⟨i,hi,eq⟩ := mem_image.mp hj
        exact mem_filter.mpr ⟨mem_insert_of_mem (jsub hj),eq ▸ alldiff i (mem_erase.mp hi).1.symm⟩
    have hcard := card_le_card cov
    have nj : univ ∉ J := fun h => topNot (jsub h)
    rw [card_insert_of_notMem nj,jcount] at hcard
    change m ≤ (C.filter (y ∈ ·)).card
    omega
  have decomposition : freq D y + freq C y = freq F y := by
    have eq : D.filter (y ∈ ·) = (F.filter (y ∈ ·)) \ (C.filter (y ∈ ·)) := by
      ext; simp [D]; tauto
    exact (congrArg (· + freq C y) (congrArg Finset.card eq)).trans
      (card_sdiff_add_card_eq_card (filter_subset_filter _ sub))
  have bound := cap y
  obtain ⟨x,hx⟩ := heavy
  refine ⟨x,hx,C,sub,by omega,?_,?_⟩
  · have single : (F.filter (x ∉ ·)) ∩ C ⊆ {M x} := by
      intro X hX
      obtain ⟨hno,hC⟩ := mem_inter.mp hX
      have miss := (mem_filter.mp hno).2
      rcases mem_insert.mp hC with rfl | hG
      · exact (miss (mem_univ _)).elim
      · obtain ⟨i,_,rfl⟩ := mem_image.mp hG
        by_cases eq : x = i
        · simp [eq]
        · exact (miss (other x i hx eq)).elim
    simpa using card_le_card single
  · intro z
    have h := highest z (mem_univ _)
    change freq D z ≤ n-m
    omega

end OMA.UnionClosed50Structure

theorem OMA.solution : OMA.R_UnionClosed_union_closed_variants_family_card_R1.H2 :=
  OMA.UnionClosed50Structure.structural
