import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
The point-detection step uses the signed short exact sequence of the intersection
and the canonical chain pushout, followed by the small-chain comparison to the
union. The subdivision route is described by PoincareLib's integral open-cover
sequence and small-chain comparison (frenzymath/PoincareConjecture, 62db01af).
-/
namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1

open CategoryTheory Limits HomologicalComplex

/-- Equality in the union lifts the first component to the intersection,
given the short exact signed intersection sequence for small chains. -/
theorem signedSequenceLifting
    {I A B P : ChainComplex AddCommGrpCat ℕ}
    (i : I ⟶ A) (j : I ⟶ B) (a : A ⟶ P) (b : B ⟶ P)
    (hz : CategoryStruct.comp (biprod.lift i (-j)) (biprod.desc a b) = 0)
    (hs : (ShortComplex.mk (biprod.lift i (-j)) (biprod.desc a b) hz).ShortExact)
    (n : ℕ) (u : A.homology n) (v : B.homology n)
    (huv : homologyMap a n u = homologyMap b n v) :
    ∃ w : I.homology n, homologyMap i n w = u := by
  let H := homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n
  let x := H.map biprod.inl u - H.map biprod.inr v
  have hmap {K L N : ChainComplex AddCommGrpCat ℕ} (f : K ⟶ L) (g : L ⟶ N)
      (t : K.homology n) : H.map g (H.map f t) = H.map (CategoryStruct.comp f g) t :=
    ConcreteCategory.congr_hom (H.map_comp f g).symm t
  have hx : H.map (biprod.desc a b) x = 0 := by
    rw [show x = H.map biprod.inl u - H.map biprod.inr v from rfl, map_sub,
      hmap, hmap, biprod.inl_desc, biprod.inr_desc]
    exact sub_eq_zero.mpr huv
  have he := hs.homology_exact₂ n
  rw [ShortComplex.ab_exact_iff_ker_le_range] at he
  obtain ⟨w, hw⟩ := he hx
  refine ⟨w, ?_⟩
  have hp := congrArg (fun y => H.map biprod.fst y) hw
  change H.map biprod.fst (H.map (biprod.lift i (-j)) w) = H.map biprod.fst x at hp
  rw [hmap, biprod.lift_fst, show x = H.map biprod.inl u - H.map biprod.inr v from rfl,
    map_sub, hmap, hmap, biprod.inl_fst, biprod.inr_fst, H.map_id, H.map_zero] at hp
  change homologyMap i n w = id u - (0 : A.homology n) at hp
  simpa using hp


theorem signedSequenceLiftingOfQuasiIso
    {I A B P X : ChainComplex AddCommGrpCat ℕ}
    (i : I ⟶ A) (j : I ⟶ B) (a : A ⟶ P) (b : B ⟶ P)
    (q : P ⟶ X) (hz : CategoryStruct.comp (biprod.lift i (-j)) (biprod.desc a b) = 0)
    (hs : (ShortComplex.mk (biprod.lift i (-j)) (biprod.desc a b) hz).ShortExact)
    (hq : QuasiIso q) (n : ℕ) (u : A.homology n) (v : B.homology n)
    (huv : homologyMap (CategoryStruct.comp a q) n u = homologyMap (CategoryStruct.comp b q) n v) :
    ∃ w : I.homology n, homologyMap i n w = u := by
  let : IsIso (homologyMap q n) :=
    (quasiIsoAt_iff_isIso_homologyMap q n).mp ((quasiIso_iff q).mp hq n)
  apply signedSequenceLifting i j a b hz hs n u v
  apply (AddCommGrpCat.mono_iff_injective _).mp
    (inferInstance : Mono (homologyMap q n))
  simpa only [homologyMap_comp, AddCommGrpCat.comp_apply] using huv


open AlgebraicTopology

section OpenUnion

variable {X : Type} [TopologicalSpace X] (U V : Set X)

private noncomputable abbrev chains :=
  (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)

private def subspaceInclusion {A B : Set X} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

private abbrev leftIntersection := subspaceInclusion (Set.inter_subset_left (s := U) (t := V))
private abbrev rightIntersection := subspaceInclusion (Set.inter_subset_right (s := U) (t := V))
private abbrev leftUnion := subspaceInclusion (Set.subset_union_left (s := U) (t := V))
private abbrev rightUnion := subspaceInclusion (Set.subset_union_right (s := U) (t := V))

private theorem openUnionSquare :
    CategoryStruct.comp (chains.map (leftIntersection U V)) (chains.map (leftUnion U V)) =
      CategoryStruct.comp (chains.map (rightIntersection U V)) (chains.map (rightUnion U V)) := by
  rw [← chains.map_comp, ← chains.map_comp]
  rfl

private theorem pushoutSequenceZero :
    CategoryStruct.comp
      (biprod.lift (chains.map (leftIntersection U V)) (-chains.map (rightIntersection U V)))
      (biprod.desc
        (pushout.inl (chains.map (leftIntersection U V)) (chains.map (rightIntersection U V)))
        (pushout.inr (chains.map (leftIntersection U V)) (chains.map (rightIntersection U V)))) = 0 :=
  (IsPushout.of_isColimit (pushoutIsPushout (chains.map (leftIntersection U V))
    (chains.map (rightIntersection U V)))).shortComplex.zero

end OpenUnion

def H1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (U V : Set X), IsOpen U → IsOpen V →
    QuasiIso (pushout.desc (chains.map (leftUnion U V)) (chains.map (rightUnion U V)) (openUnionSquare U V))

def H2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (U V : Set X),
    let i := chains.map (leftIntersection U V)
    let j := chains.map (rightIntersection U V)
    (ShortComplex.mk (biprod.lift i (-j))
      (biprod.desc (pushout.inl i j) (pushout.inr i j)) (pushoutSequenceZero U V)).ShortExact

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1.H2 := by
  intro hSmall hSeq X _ U V hU hV
  dsimp only
  intro u v huv
  let i := chains.map (leftIntersection U V)
  let j := chains.map (rightIntersection U V)
  let a := chains.map (leftUnion U V)
  let b := chains.map (rightUnion U V)
  let q := pushout.desc a b (openUnionSquare U V)
  apply signedSequenceLiftingOfQuasiIso i j (pushout.inl i j) (pushout.inr i j)
    q (pushoutSequenceZero U V) (hSeq X U V) (hSmall X U V hU hV) 3 u v
  dsimp only [q]
  rwa [pushout.inl_desc, pushout.inr_desc]

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1
