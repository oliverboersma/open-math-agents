import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1
import Mathlib

/-! Integral singular excision, adapted from the PoincareLib contributors,
frenzymath/Poincare-Conjecture at 432c38f2aa5a30efb13871292d17b4a3309a496a, Apache-2.0.
Original code by the LehengChen/PoincareConjecture contributors at 60de1a94ca7038d04ed123b490a3229f8aa5fa75. Copyright (c) 2026 The PoincareLib contributors.
The module-valued construction follows the port by Marcus Buffett in open-math-agents PR 5271.
The new natural comparison transports relative chains and homology through the forgetful functor. -/

/-
Poincare Conjecture

This distribution contains adapted portions of external Lean developments.
The following notices apply to those portions, not to the entire project.
See PoincareConjecture/MODIFICATIONS.md and the per-file source notices for
the scope of adaptations, authorship, comparison revisions, and changes.

DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

DeGiorgi (including material incorporated through DifferentialGeometry)
Copyright 2026 Scott Armstrong and Julia Kempe

TauCeti (individual file notices determine which notice applies)
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.

ClassificationOfSurfaces
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.

Mathlib adaptations
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.

These sources are distributed under Apache-2.0. Verbatim source licenses and
the DifferentialGeometry NOTICE are retained in
archive/PoincareConjecture/provenance/2026-09-29/licenses/.

-/



noncomputable section FzIntegralRelativeChains

/-!
# Actual integral relative singular chains

Relative chains are the cokernel of the actual subspace-chain inclusion.
The coefficient object and all topological spaces retain the same universe.
Homotopies of pairs descend the natural singular prism through these cokernels.
-/


open CategoryTheory Limits MonoidalCategory
open scoped Simplicial BigOperators unitInterval

universe u

namespace Poincare.Topology

abbrev integralCoefficient : ModuleCat.{u} Int :=
  ModuleCat.of Int (ULift.{u} Int)

abbrev integralChainsFunctor :
    TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} Int) Nat :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} Int)).obj
    integralCoefficient

abbrev integralChains (X : Type u) [TopologicalSpace X] :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  integralChainsFunctor.obj (TopCat.of X)

abbrev integralHomology (X : Type u) [TopologicalSpace X] (n : Nat) :
    ModuleCat.{u} Int :=
  (integralChains X).homology n

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSubspaceChains (A : Set X) : integralChains A ⟶ integralChains X :=
  integralChainsFunctor.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)

theorem integralSubspaceChains_mono (A : Set X) : Mono (integralSubspaceChains A) := by
  let i : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
  change Mono (integralChainsFunctor.map i)
  infer_instance

abbrev integralRelativeChains (A : Set X) : ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralSubspaceChains A)

abbrev integralRelativeHomology (A : Set X) (n : Nat) : ModuleCat.{u} Int :=
  (integralRelativeChains A).homology n

abbrev integralRelativeProjection (A : Set X) :
    integralChains X ⟶ integralRelativeChains A :=
  cokernel.π (integralSubspaceChains A)

abbrev integralToRelativeHomology (A : Set X) (n : Nat) :
    integralHomology X n ⟶ integralRelativeHomology A n :=
  HomologicalComplex.homologyMap (integralRelativeProjection A) n

def integralRelativeMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) : integralRelativeChains A ⟶ integralRelativeChains B :=
  cokernel.map (integralSubspaceChains A) (integralSubspaceChains B)
    (integralChainsFunctor.map (TopCat.ofHom
      ⟨fun a : A => ⟨f a, hf a.property⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk _⟩))
    (integralChainsFunctor.map (TopCat.ofHom f)) (by
      simp only [integralSubspaceChains, ← Functor.map_comp]
      rfl)

theorem integralRelativeMap_projection (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) :
    (CategoryStruct.comp (integralRelativeProjection A ) ( integralRelativeMap f hf)) =
      (CategoryStruct.comp (integralChainsFunctor.map (TopCat.ofHom f) ) ( integralRelativeProjection B)) :=
  cokernel.π_desc _ _ _

abbrev integralPairSequence (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.cokernelSequence (integralSubspaceChains A)

theorem integralPairSequence_shortExact (A : Set X) :
    (integralPairSequence A).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (integralSubspaceChains A)
  mono_f := integralSubspaceChains_mono A

def integralRelativeBoundary (A : Set X) (n : Nat) :
    integralRelativeHomology A (n + 1) ⟶ integralHomology A n :=
  (integralPairSequence_shortExact A).δ (n + 1) n rfl

theorem integral_relative_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Nonempty (Homotopy (integralRelativeMap f hf) (integralRelativeMap g hg)) := by
  let ia : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let ib : TopCat.of B ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let fa : C(A, B) := ⟨fun a => ⟨f a, hf a.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let ga : C(A, B) := ⟨fun a => ⟨g a, hg a.property⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let HA : ContinuousMap.Homotopy fa ga :=
    { toFun := fun q => ⟨H (q.1, q.2), hH q.1 q.2.property⟩
      continuous_toFun :=
        (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left a := Subtype.ext (H.map_zero_left a)
      map_one_left a := Subtype.ext (H.map_one_left a) }
  let HT : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  let HAT : TopCat.Homotopy (TopCat.ofHom fa) (TopCat.ofHom ga) := HA
  have htop : (CategoryStruct.comp (ia ▷ TopCat.I ) ( HT.h)) = (CategoryStruct.comp (HAT.h ) ( ib)) := by
    ext q
    rfl
  have hs : (CategoryStruct.comp (TopCat.toSSet.map ia ▷ Δ[1] ) ( HT.toSSet.h)) =
      (CategoryStruct.comp (HAT.toSSet.h ) ( TopCat.toSSet.map ib)) := by
    dsimp [TopCat.Homotopy.toSSet]
    rw [← whisker_exchange_assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← TopCat.toSSet.map_comp, htop, TopCat.toSSet.map_comp]
    simp only [Category.assoc]
  let S := HT.toSSet.toSimplicialObjectHomotopy
  let SA := HAT.toSSet.toSimplicialObjectHomotopy
  have hsimplex (n : Nat) (k : Fin (n + 1)) :
      (CategoryStruct.comp ((TopCat.toSSet.map ia).app (Opposite.op ⦋n⦌) ) ( S.h k)) =
        (CategoryStruct.comp (SA.h k ) ( (TopCat.toSSet.map ib).app (Opposite.op ⦋n + 1⦌))) := by
    ext x
    change ((CategoryStruct.comp ((SSet.yonedaEquiv.symm ((TopCat.toSSet.map ia).app _ x) ▷ Δ[1]) ) (
        HT.toSSet.h))).app _ _ =
      ((CategoryStruct.comp ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ) ( (CategoryStruct.comp (HAT.toSSet.h ) (
        TopCat.toSSet.map ib))))).app _ _
    rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, hs]
  let F : Type u ⥤ ModuleCat.{u} Int := sigmaConst.obj integralCoefficient
  let P : Homotopy (integralChainsFunctor.map (TopCat.ofHom f))
      (integralChainsFunctor.map (TopCat.ofHom g)) :=
    HT.singularChainComplexFunctorObjMap integralCoefficient
  let PA : Homotopy (integralChainsFunctor.map (TopCat.ofHom fa))
      (integralChainsFunctor.map (TopCat.ofHom ga)) :=
    HAT.singularChainComplexFunctorObjMap integralCoefficient
  have hprism (i j : Nat) :
      (CategoryStruct.comp ((integralSubspaceChains A).f i ) ( P.hom i j)) =
        (CategoryStruct.comp (PA.hom i j ) ( (integralSubspaceChains B).f j)) := by
    by_cases hij : i + 1 = j
    · subst j
      change (CategoryStruct.comp (F.map ((TopCat.toSSet.map ia).app (Opposite.op ⦋i⦌)) ) (
          CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
            (S.whiskerRight F) i (i + 1))) =
        (CategoryStruct.comp (CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
            (SA.whiskerRight F) i (i + 1) ) (
          F.map ((TopCat.toSSet.map ib).app (Opposite.op ⦋i + 1⦌))))
      rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
        CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
      change (CategoryStruct.comp (F.map ((TopCat.toSSet.map ia).app (Opposite.op ⦋i⦌)) ) (
          (-∑ k : Fin (i + 1), ((-1 : Int) ^ k.val) • F.map (S.h k)))) =
        (CategoryStruct.comp ((-∑ k : Fin (i + 1), ((-1 : Int) ^ k.val) • F.map (SA.h k)) ) (
          F.map ((TopCat.toSSet.map ib).app (Opposite.op ⦋i + 1⦌))))
      simp only [Preadditive.comp_neg, Preadditive.neg_comp,
        Preadditive.comp_sum, Preadditive.sum_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      rw [← F.map_comp, ← F.map_comp, hsimplex]
    · rw [P.zero i j hij, PA.zero i j hij, comp_zero, zero_comp]
  let pA := integralRelativeProjection A
  let pB := integralRelativeProjection B
  have hzero (i j : Nat) :
      (CategoryStruct.comp ((integralSubspaceChains A).f i ) ( ((CategoryStruct.comp (P.hom i j ) ( pB.f j))))) = 0 := by
    rw [← Category.assoc, hprism, Category.assoc]
    have hb : (CategoryStruct.comp ((integralSubspaceChains B).f j ) ( pB.f j)) = 0 :=
      congrArg (fun q => q.f j) (cokernel.condition (integralSubspaceChains B))
    rw [hb, comp_zero]
  let D (i j : Nat) :=
    CokernelCofork.IsColimit.desc'
      (isColimitOfHasCokernelOfPreservesColimit
        (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) i)
        (integralSubspaceChains A))
      ((CategoryStruct.comp (P.hom i j ) ( pB.f j))) (hzero i j)
  let T (i j : Nat) : (integralRelativeChains A).X i ⟶
      (integralRelativeChains B).X j := (D i j).val
  have hT (i j : Nat) : (CategoryStruct.comp (pA.f i ) ( T i j)) = (CategoryStruct.comp (P.hom i j ) ( pB.f j)) := (D i j).property
  have hf' (i : Nat) : (CategoryStruct.comp (pA.f i ) ( (integralRelativeMap f hf).f i)) =
      (CategoryStruct.comp ((integralChainsFunctor.map (TopCat.ofHom f)).f i ) ( pB.f i)) :=
    congrArg (fun q => q.f i) (integralRelativeMap_projection f hf)
  have hg' (i : Nat) : (CategoryStruct.comp (pA.f i ) ( (integralRelativeMap g hg).f i)) =
      (CategoryStruct.comp ((integralChainsFunctor.map (TopCat.ofHom g)).f i ) ( pB.f i)) :=
    congrArg (fun q => q.f i) (integralRelativeMap_projection g hg)
  refine ⟨{ hom := T, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    apply (cancel_epi (pA.f i)).mp
    rw [hT, P.zero i j hij, zero_comp, comp_zero]
  · intro i
    apply (cancel_epi (pA.f i)).mp
    rw [Preadditive.comp_add, Preadditive.comp_add, hf', hg',
      ← dNext_comp_left pA T i, ← prevD_comp_left pA T i]
    simp_rw [hT]
    rw [dNext_comp_right P.hom pB i, prevD_comp_right P.hom pB i, P.comm i]
    simp only [Preadditive.add_comp]

def integralHomeomorphHomologyIso (e : X ≃ₜ Y) (n : Nat) :
    integralHomology X n ≅ integralHomology Y n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).mapIso
    (integralChainsFunctor.mapIso (TopCat.isoOfHomeo e))

theorem integral_contractible_homology_isZero
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : Nat) (hn : n ≠ 0) : IsZero (integralHomology X n) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let a : TopCat.of X ⟶ TopCat.of (ULift.{u} Unit) :=
    TopCat.ofHom (ContinuousMap.const X (ULift.up ()))
  let b : TopCat.of (ULift.{u} Unit) ⟶ TopCat.of X :=
    TopCat.ofHom (ContinuousMap.const (ULift.{u} Unit) x)
  have hz : IsZero (integralHomology (ULift.{u} Unit) n) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} Int) n integralCoefficient (TopCat.of (ULift.{u} Unit)) hn
  have H' : TopCat.Homotopy (𝟙 (TopCat.of X)) ((CategoryStruct.comp (a ) ( b))) := H
  have heq := H'.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  rw [IsZero.iff_id_eq_zero]
  have hmap : HomologicalComplex.homologyMap (integralChainsFunctor.map ((CategoryStruct.comp (a ) ( b)))) n = 0 := by
    rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
    rw [hz.eq_of_tgt (HomologicalComplex.homologyMap (integralChainsFunctor.map a) n) 0,
      zero_comp]
  have hid : HomologicalComplex.homologyMap
      (integralChainsFunctor.map (𝟙 (TopCat.of X))) n = 0 := heq.trans hmap
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at hid
  exact hid

end Poincare.Topology

end FzIntegralRelativeChains

noncomputable section FzIntegralChainCoordinates

/-!
# Coordinates of actual integral singular chains

The coproduct coordinates are indexed by continuous maps from the standard
simplex. Subspace chains correspond to the coordinates whose entire simplex
image lies in the subspace. The resulting splitting is degreewise.
-/


open CategoryTheory Limits
open scoped Simplicial BigOperators

universe u

namespace Poincare.Topology

abbrev integralSimplex (n : Nat) := stdSimplex Real (Fin (n + 1))

def integralSimplexFace (n : Nat) (i : Fin (n + 2)) :
    C(integralSimplex n, integralSimplex (n + 1)) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSingularGenerator {n : Nat} (s : C(integralSimplex n, X)) :
    integralCoefficient.{u} ⟶ (integralChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s)

def integralChainCoordinates (X : Type u) [TopologicalSpace X] (n : Nat) :
    (integralChains X).X n ≃ₗ[Int]
      (C(integralSimplex n, X) →₀ ULift.{u} Int) :=
  let S := TopCat.toSSet.obj (TopCat.of X)
  let e := (S.isColimitChainComplexXCofan integralCoefficient n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (S.obj (Opposite.op ⦋n⦌)))
  e.toLinearEquiv.trans
    (Finsupp.domLCongr ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)))

theorem integralChainCoordinates_generator {n : Nat}
    (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
    integralChainCoordinates X n (integralSingularGenerator s a) = Finsupp.single s a := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let E := (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)
  let e := (S.isColimitChainComplexXCofan integralCoefficient n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (S.obj (Opposite.op ⦋n⦌)))
  have hι := IsColimit.comp_coconePointUniqueUpToIso_hom
    (S.isColimitChainComplexXCofan integralCoefficient n)
    (ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (S.obj (Opposite.op ⦋n⦌)))
    (Discrete.mk (E.symm s))
  have he : e.hom (integralSingularGenerator s a) = Finsupp.single (E.symm s) a :=
    congrArg (fun f => f a) hι
  change Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) E
    (e.hom (integralSingularGenerator s a)) = Finsupp.single s a
  rw [he, Finsupp.domLCongr_single, E.apply_symm_apply]

theorem integralSingularGenerator_boundary {n : Nat}
    (s : C(integralSimplex (n + 1), X)) :
    (CategoryStruct.comp (integralSingularGenerator s ) ( (integralChains X).d (n + 1) n)) =
      ∑ i : Fin (n + 2), ((-1 : Int) ^ i.val) •
        integralSingularGenerator (s.comp (integralSimplexFace n i)) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let E := (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)
  let E' := (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n + 1⦌)
  change (CategoryStruct.comp (S.ιChainComplex (E'.symm s) ) ( (S.chainComplex integralCoefficient).d (n + 1) n)) =
    ∑ i : Fin (n + 2), ((-1 : Int) ^ i.val) •
      S.ιChainComplex (E.symm (s.comp (integralSimplexFace n i)))
  rw [SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : S.obj (Opposite.op ⦋n⦌) =>
    ((-1 : Int) ^ i.val) • S.ιChainComplex (R := integralCoefficient) x)
  apply E.injective
  ext z
  change (TopCat.of X).toSSetObjEquiv _ (S.δ i (E'.symm s)) z =
    (E (E.symm (s.comp (integralSimplexFace n i)))) z
  rw [TopCat.toSSetObjEquiv_δ_apply, E'.apply_symm_apply, E.apply_symm_apply]
  rfl

theorem integralSingularGenerator_map {n : Nat}
    (s : C(integralSimplex n, X)) (f : C(X, Y)) :
    (CategoryStruct.comp (integralSingularGenerator s ) (
      (integralChainsFunctor.map (TopCat.ofHom f)).f n)) =
        integralSingularGenerator (f.comp s) := by
  change (CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s) ) (
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) integralCoefficient).f n)) =
    (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
      (((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm (f.comp s))
  rw [SSet.ι_chainComplexMap_f]
  rfl

theorem integral_subspace_range_iff (A : Set X) (n : Nat)
    (c : (integralChains X).X n) :
    c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ↔
      ∀ s ∈ (integralChainCoordinates X n c).support, Set.range s ⊆ A := by
  classical
  let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(integralSimplex n, A) → C(integralSimplex n, X) := fun s => v.comp s
  let i := (integralSubspaceChains A).f n
  let EA := integralChainCoordinates A n
  let EX := integralChainCoordinates X n
  have hf : Function.Injective f := by
    intro s t h
    ext z
    exact congrArg (fun k : C(integralSimplex n, X) => k z) h
  have hgen (s : C(integralSimplex n, A)) :
      (CategoryStruct.comp (integralSingularGenerator s ) ( i)) = integralSingularGenerator (f s) :=
    integralSingularGenerator_map s v
  have hcoord : EX.toLinearMap.comp (i.hom.comp EA.symm.toLinearMap) =
      Finsupp.lmapDomain (ULift.{u} Int) Int f := by
    apply Finsupp.lhom_ext
    intro s a
    change EX (i (EA.symm (Finsupp.single s a))) =
      Finsupp.mapDomain f (Finsupp.single s a)
    have hs : EA.symm (Finsupp.single s a) = integralSingularGenerator s a := by
      apply EA.injective
      rw [EA.apply_symm_apply]
      exact (integralChainCoordinates_generator s a).symm
    have hg : i (integralSingularGenerator s a) = integralSingularGenerator (f s) a :=
      congrArg (fun k => k a) (hgen s)
    rw [hs, hg, integralChainCoordinates_generator, Finsupp.mapDomain_single]
  have happ (a : (integralChains A).X n) :
      EX (i a) = Finsupp.mapDomain f (EA a) := by
    have h := LinearMap.congr_fun hcoord (EA a)
    change EX (i (EA.symm (EA a))) = Finsupp.mapDomain f (EA a) at h
    simpa only [EA.symm_apply_apply] using h
  have hfrange (s : C(integralSimplex n, X)) :
      s ∈ Set.range f ↔ Set.range s ⊆ A := by
    constructor
    · rintro ⟨t, rfl⟩ y ⟨z, rfl⟩
      exact (t z).property
    · intro hs
      refine ⟨⟨fun z => ⟨s z, hs ⟨z, rfl⟩⟩, s.continuous.subtype_mk _⟩, ?_⟩
      ext z
      rfl
  have hrange : c ∈ LinearMap.range i.hom ↔ EX c ∈ Set.range (Finsupp.mapDomain f) := by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨EA a, (happ a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨EA.symm a, EX.injective ?_⟩
      rw [happ, EA.apply_symm_apply, ha]
  change c ∈ LinearMap.range i.hom ↔ ∀ s ∈ (EX c).support, Set.range s ⊆ A
  rw [hrange, Finsupp.mem_range_mapDomain_iff f hf]
  constructor
  · intro h s hs
    apply (hfrange s).mp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hs) (h s hn)
  · intro h s hs
    by_contra hn
    exact hs ((hfrange s).mpr (h s (Finsupp.mem_support_iff.mpr hn)))

theorem integral_chain_finite_representation (n : Nat)
    (c : (integralChains X).X n) :
    c = ∑ s ∈ (integralChainCoordinates X n c).support,
      integralSingularGenerator s (integralChainCoordinates X n c s) := by
  apply (integralChainCoordinates X n).injective
  simp only [map_sum]
  calc
    integralChainCoordinates X n c =
        ∑ s ∈ (integralChainCoordinates X n c).support,
          Finsupp.single s (integralChainCoordinates X n c s) :=
      (Finsupp.sum_single (integralChainCoordinates X n c)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact (integralChainCoordinates_generator s _).symm

theorem integral_pair_degree_split (A : Set X) (n : Nat) :
    ∃ r : (integralChains X).X n ⟶ (integralChains A).X n,
    ∃ s : (integralRelativeChains A).X n ⟶ (integralChains X).X n,
      (CategoryStruct.comp ((integralSubspaceChains A).f n ) ( r)) = 𝟙 _ ∧
      (CategoryStruct.comp (s ) ( (integralRelativeProjection A).f n)) = 𝟙 _ ∧
      (CategoryStruct.comp (r ) ( (integralSubspaceChains A).f n)) +
        (CategoryStruct.comp ((integralRelativeProjection A).f n ) ( s)) = 𝟙 _ := by
  let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(integralSimplex n, A) → C(integralSimplex n, X) := fun s => v.comp s
  let i := (integralSubspaceChains A).f n
  let p := (integralRelativeProjection A).f n
  let EA := integralChainCoordinates A n
  let EX := integralChainCoordinates X n
  have hf : Function.Injective f := by
    intro s t h
    ext z
    exact congrArg (fun k : C(integralSimplex n, X) => k z) h
  let r : (integralChains X).X n ⟶ (integralChains A).X n :=
    ModuleCat.ofHom (EA.symm.toLinearMap.comp
      ((Finsupp.lcomapDomain (R := Int) (M := ULift.{u} Int) f hf).comp EX.toLinearMap))
  have hgen (s : C(integralSimplex n, A)) :
      (CategoryStruct.comp (integralSingularGenerator s ) ( i)) = integralSingularGenerator (f s) :=
    integralSingularGenerator_map s v
  have hrgen (s : C(integralSimplex n, A)) (a : ULift.{u} Int) :
      r (integralSingularGenerator (f s) a) = integralSingularGenerator s a := by
    change EA.symm (Finsupp.comapDomain f
      (EX (integralSingularGenerator (f s) a)) hf.injOn) = integralSingularGenerator s a
    apply EA.injective
    rw [EA.apply_symm_apply, integralChainCoordinates_generator,
      integralChainCoordinates_generator, Finsupp.comapDomain_single]
  have hir : (CategoryStruct.comp (i ) ( r)) = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro x
    obtain ⟨s, rfl⟩ := ((TopCat.of A).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm.surjective x
    change (CategoryStruct.comp (integralSingularGenerator s ) ( ((CategoryStruct.comp (i ) ( r))))) = (CategoryStruct.comp (integralSingularGenerator s ) ( 𝟙 _))
    rw [← Category.assoc, hgen, Category.comp_id]
    ext a
    exact hrgen s a
  let t : (integralChains X).X n ⟶ (integralChains X).X n := 𝟙 _ - (CategoryStruct.comp (r ) ( i))
  have hit : (CategoryStruct.comp (i ) ( t)) = 0 := by
    dsimp only [t]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hir,
      Category.id_comp, sub_self]
  let d := CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)
      (integralSubspaceChains A)) t hit
  let s : (integralRelativeChains A).X n ⟶ (integralChains X).X n := d.val
  have hps : (CategoryStruct.comp (p ) ( s)) = t := d.property
  have hip : (CategoryStruct.comp (i ) ( p)) = 0 :=
    congrArg (fun q => q.f n) (cokernel.condition (integralSubspaceChains A))
  have hsp : (CategoryStruct.comp (s ) ( p)) = 𝟙 _ := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hps]
    dsimp only [t]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hip, comp_zero,
      sub_zero, Category.comp_id]
  refine ⟨r, s, hir, hsp, ?_⟩
  change (CategoryStruct.comp (r ) ( i)) + (CategoryStruct.comp (p ) ( s)) = 𝟙 _
  rw [hps]
  change (CategoryStruct.comp (r ) ( i)) + (𝟙 _ - (CategoryStruct.comp (r ) ( i))) = 𝟙 _
  rw [← add_sub_assoc, add_sub_cancel_left]

end Poincare.Topology

end FzIntegralChainCoordinates

noncomputable section FzIntegralHomologyZero

/-!
# The augmentation of integral homology in degree zero

Point classes generate degree-zero singular homology. The augmentation sends
each point class to one and is natural for every continuous map.
-/


open CategoryTheory Limits
open scoped Simplicial

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralHomologyZeroAugmentation (X : Type u) [TopologicalSpace X] :
    integralHomology X 0 ⟶ integralCoefficient :=
  (TopCat.of X).singularHomology₀ε integralCoefficient

def integralPointClass (x : X) : integralCoefficient ⟶ integralHomology X 0 :=
  (CategoryStruct.comp ((integralChains X).liftCycles
    (integralSingularGenerator (ContinuousMap.const (integralSimplex 0) x))
    0 (by simp) (by simp) ) ( (integralChains X).homologyπ 0))

theorem integralPointClass_augmentation (x : X) :
    (CategoryStruct.comp (integralPointClass x ) ( integralHomologyZeroAugmentation X)) = 𝟙 _ := by
  exact (TopCat.toSSet.obj (TopCat.of X)).liftCycles_ιChainComplex_homologyπ_homology₀ε
    integralCoefficient _

theorem integralHomologyZero_hom_ext {M : ModuleCat.{u} Int}
    (f g : integralHomology X 0 ⟶ M)
    (h : ∀ x : X, (CategoryStruct.comp (integralPointClass x ) ( f)) = (CategoryStruct.comp (integralPointClass x ) ( g))) : f = g := by
  let K := integralChains X
  let e := K.iCyclesIso 0 0 (by simp) (by simp)
  apply (cancel_epi (K.homologyπ 0)).mp
  apply (cancel_epi e.inv).mp
  apply SSet.chainComplex_hom_ext
  intro z
  obtain ⟨s, rfl⟩ := ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋0⦌)).symm.surjective z
  have hs : s = ContinuousMap.const (integralSimplex 0) (s default) := by
    ext t
    exact congrArg s (Subsingleton.elim t default)
  have hl : (CategoryStruct.comp (integralSingularGenerator s ) ( e.inv)) =
      K.liftCycles (integralSingularGenerator s) 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      Category.comp_id, HomologicalComplex.liftCycles_i]
  change (CategoryStruct.comp (integralSingularGenerator s ) ( (CategoryStruct.comp (e.inv ) ( (CategoryStruct.comp (K.homologyπ 0 ) ( f)))))) =
    (CategoryStruct.comp (integralSingularGenerator s ) ( (CategoryStruct.comp (e.inv ) ( (CategoryStruct.comp (K.homologyπ 0 ) ( g))))))
  rw [← Category.assoc (integralSingularGenerator s), hl,
    ← Category.assoc (integralSingularGenerator s), hl, hs]
  exact h (s default)

theorem integralPointClass_map (f : C(X, Y)) (x : X) :
    (CategoryStruct.comp (integralPointClass x ) ( HomologicalComplex.homologyMap
        (integralChainsFunctor.map (TopCat.ofHom f)) 0)) = integralPointClass (f x) := by
  let F := integralChainsFunctor.map (TopCat.ofHom f)
  let sx := integralSingularGenerator (ContinuousMap.const (integralSimplex 0) x)
  let sy := integralSingularGenerator (ContinuousMap.const (integralSimplex 0) (f x))
  have hs : (CategoryStruct.comp (sx ) ( F.f 0)) = sy := by
    exact integralSingularGenerator_map (ContinuousMap.const (integralSimplex 0) x) f
  have hl : (integralChains Y).liftCycles ((CategoryStruct.comp (sx ) ( F.f 0))) 0 (by simp)
      (by rw [Category.assoc, F.comm, ← Category.assoc]; simp) =
        (integralChains Y).liftCycles sy 0 (by simp) (by simp) := by
    apply (cancel_mono ((integralChains Y).iCycles 0)).mp
    rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, hs]
  change (CategoryStruct.comp (((CategoryStruct.comp ((integralChains X).liftCycles sx 0 (by simp) (by simp) ) (
      (integralChains X).homologyπ 0))) ) ( HomologicalComplex.homologyMap F 0)) =
    (CategoryStruct.comp ((integralChains Y).liftCycles sy 0 (by simp) (by simp) ) (
      (integralChains Y).homologyπ 0))
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap, hl]

theorem integralHomologyZeroAugmentation_natural (f : C(X, Y)) :
    (CategoryStruct.comp (HomologicalComplex.homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0 ) (
      integralHomologyZeroAugmentation Y)) = integralHomologyZeroAugmentation X := by
  apply integralHomologyZero_hom_ext
  intro x
  rw [← Category.assoc, integralPointClass_map,
    integralPointClass_augmentation, integralPointClass_augmentation]

theorem integralHomologyZeroAugmentation_isIso (X : Type u) [TopologicalSpace X]
    [PathConnectedSpace X] : IsIso (integralHomologyZeroAugmentation X) := by
  change IsIso ((TopCat.of X).singularHomology₀ε integralCoefficient)
  infer_instance

/-- For a path-connected target the kernel on `H_0` is the augmentation kernel. -/
def integralHomologyZeroMapKernelIso (f : C(X, Y)) [PathConnectedSpace Y] :
    kernel (HomologicalComplex.homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 0) ≅
      kernel (integralHomologyZeroAugmentation X) := by
  let := integralHomologyZeroAugmentation_isIso Y
  exact (kernelCompMono _ (integralHomologyZeroAugmentation Y)).symm ≪≫
    kernelIsoOfEq (integralHomologyZeroAugmentation_natural f)

end Poincare.Topology

end FzIntegralHomologyZero

noncomputable section FzIntegralZeroSphere

/-!
# The integral reduced homology of the zero-sphere

The two point classes give two free integral coordinates. Augmentation is
their sum, whose kernel is the integral module generated by their difference.
-/


open CategoryTheory Limits

universe u

namespace Poincare.Topology

private def integralPairSum :
    ModuleCat.of Int (Bool → ULift.{u} Int) ⟶ integralCoefficient :=
  ModuleCat.ofHom
    ((LinearMap.proj false : (Bool → ULift.{u} Int) →ₗ[Int] ULift.{u} Int) +
      LinearMap.proj true)

private def integralPairSumKernelIso : kernel integralPairSum.{u} ≅ integralCoefficient := by
  let e : LinearMap.ker integralPairSum.{u}.hom ≃ₗ[Int] ULift.{u} Int :=
    { toFun := fun z => z.val false
      invFun := fun a => ⟨fun b => if b then -a else a, by
        change a + -a = 0
        exact add_neg_cancel a⟩
      left_inv := by
        intro z
        apply Subtype.ext
        funext b
        cases b
        · rfl
        · have hz : z.val false + z.val true = 0 := z.property
          have ht : z.val true = -z.val false := by
            simpa using congrArg (fun a => a - z.val false) hz
          exact ht.symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ModuleCat.kernelIsoKer integralPairSum ≪≫ e.toModuleIso

/-- A space with exactly two path components has augmentation kernel `Z`. -/
def integralTwoComponentsAugmentationKernelIso
    (X : Type u) [TopologicalSpace X] (e : ZerothHomotopy X ≃ Bool) :
    kernel (integralHomologyZeroAugmentation X) ≅ integralCoefficient := by
  classical
  let Q : ZerothHomotopy X → ModuleCat.{u} Int := fun _ => integralCoefficient
  let eS : (∐ Q) ≅ ModuleCat.of Int (ZerothHomotopy X →₀ ULift.{u} Int) :=
    colimit.isoColimitCocone
      ⟨_, ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (ZerothHomotopy X)⟩
  let eF : ModuleCat.of Int (ZerothHomotopy X →₀ ULift.{u} Int) ≅
      ModuleCat.of Int (Bool → ULift.{u} Int) :=
    ((Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) e).trans
      (Finsupp.linearEquivFunOnFinite Int (ULift.{u} Int) Bool)).toModuleIso
  let eH := (TopCat.of X).singularHomology₀Iso integralCoefficient
  let E := eH ≪≫ eS ≪≫ eF
  have hsum : (CategoryStruct.comp (eS.hom ) ( (CategoryStruct.comp (eF.hom ) ( integralPairSum)))) = Limits.Sigma.desc (fun _ => 𝟙 integralCoefficient) := by
    apply Sigma.hom_ext
    intro i
    have hi : (CategoryStruct.comp (Sigma.ι Q i ) ( eS.hom)) =
        ModuleCat.ofHom (Finsupp.lsingle i (R := Int) (M := ULift.{u} Int)) :=
      colimit.isoColimitCocone_ι_hom _ _
    rw [← Category.assoc, hi, Sigma.ι_desc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ((Finsupp.linearEquivFunOnFinite Int (ULift.{u} Int) Bool)
        ((Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) e) (Finsupp.single i a))) false +
      ((Finsupp.linearEquivFunOnFinite Int (ULift.{u} Int) Bool)
        ((Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) e) (Finsupp.single i a))) true = a
    rw [Finsupp.domLCongr_single, Finsupp.linearEquivFunOnFinite_single]
    cases e i <;> simp
  have hE : (CategoryStruct.comp (integralHomologyZeroAugmentation X ) ( (Iso.refl integralCoefficient).hom)) =
      (CategoryStruct.comp (E.hom ) ( integralPairSum)) := by
    rw [Iso.refl_hom, Category.comp_id]
    change integralHomologyZeroAugmentation X = (CategoryStruct.comp (((CategoryStruct.comp (eH.hom ) ( (CategoryStruct.comp (eS.hom ) ( eF.hom))))) ) ( integralPairSum))
    rw [Category.assoc, Category.assoc, hsum]
    exact ((TopCat.of X).singularHomology₀Iso_sigma_desc_id integralCoefficient).symm
  exact kernel.mapIso _ _ E (Iso.refl _) hE ≪≫ integralPairSumKernelIso

private def integralZerothHomotopyEquivOfTotallyDisconnected
    (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    ZerothHomotopy X ≃ X where
  toFun := ZerothHomotopy.lift id (by
    intro x y p
    have h := TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1
    simpa using h)
  invFun := ZerothHomotopy.mk
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective q
    rfl
  right_inv := fun _ => rfl

private def integralRealUnitSphereEquivBool : Metric.sphere (0 : Real) 1 ≃ Bool where
  toFun x := if x.val = 1 then true else false
  invFun b := ⟨if b then 1 else -1, by cases b <;> simp⟩
  left_inv x := by
    have hxnorm : |x.val| = 1 := by
      have hx : dist x.val (0 : Real) = 1 := x.property
      rw [Real.dist_eq, sub_zero] at hx
      exact hx
    have hx : x.val = 1 ∨ x.val = -1 := abs_eq_abs.mp (by simpa using hxnorm)
    apply Subtype.ext
    rcases hx with hx | hx <;> norm_num [hx]
  right_inv b := by cases b <;> norm_num

private def integralZeroSphereEquivBool :
    Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1 ≃ Bool := by
  let e := (OrthonormalBasis.singleton (Fin 1) Real).repr.symm
  let eS : Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1 ≃ Metric.sphere (0 : Real) 1 :=
    e.toEquiv.subtypeEquiv (fun x => by
      simp only [Metric.mem_sphere, dist_zero_right]
      change (‖x‖ = 1) ↔ ‖e x‖ = 1
      rw [e.norm_map]
      rfl)
  exact eS.trans integralRealUnitSphereEquivBool

/-- The zero-sphere supplies the explicit integral base of sphere homology. -/
def integralZeroSphereAugmentationKernelIso :
    kernel (integralHomologyZeroAugmentation
      (Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1)) ≅ integralCoefficient := by
  let S := Metric.sphere (0 : EuclideanSpace Real (Fin 1)) 1
  let : Finite S := Finite.of_equiv Bool integralZeroSphereEquivBool.symm
  exact integralTwoComponentsAugmentationKernelIso S
    ((integralZerothHomotopyEquivOfTotallyDisconnected S).trans integralZeroSphereEquivBool)

end Poincare.Topology

end FzIntegralZeroSphere

noncomputable section FzIntegralSmallChains

/-!
# Small integral singular chains

Small chains are the integer span of singular simplices whose entire image
lies in one member of the supplied family. The differential and inclusion
are restrictions of the actual singular-chain maps.
-/


open CategoryTheory
open scoped BigOperators

universe u v

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] {I : Type v}

def IntegralSmallSimplex (U : I → Set X) {n : Nat}
    (s : C(integralSimplex n, X)) : Prop :=
  ∃ i, Set.range s ⊆ U i

def integralSmallChains (U : I → Set X) (n : Nat) :
    Submodule Int ((integralChains X).X n) :=
  Submodule.span Int (Set.range (fun s : {s : C(integralSimplex n, X) //
    IntegralSmallSimplex U s} => integralSingularGenerator s.val (ULift.up 1)))

def integralSmallChainComplex (U : I → Set X) :
    ChainComplex (ModuleCat.{u} Int) Nat := by
  have hpres (i j : Nat) (c : integralSmallChains U i) :
      (integralChains X).d i j c.val ∈ integralSmallChains U j := by
    by_cases hij : (ComplexShape.down Nat).Rel i j
    · change j + 1 = i at hij
      subst i
      have hle : integralSmallChains U (j + 1) ≤
          (integralSmallChains U j).comap ((integralChains X).d (j + 1) j).hom := by
        apply Submodule.span_le.mpr
        rintro _ ⟨s, rfl⟩
        change (integralChains X).d (j + 1) j
          (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains U j
        let ev : (integralCoefficient.{u} ⟶ (integralChains X).X j) →+
            (integralChains X).X j :=
          { toFun := fun f => f (ULift.up 1)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have he := congrArg ev (integralSingularGenerator_boundary s.val)
        rw [map_sum] at he
        change (integralChains X).d (j + 1) j
          (integralSingularGenerator s.val (ULift.up 1)) = _ at he
        rw [he]
        apply Submodule.sum_mem
        intro k _
        rw [map_zsmul]
        apply (integralSmallChains U j).toAddSubgroup.zsmul_mem
        change integralSingularGenerator (s.val.comp (integralSimplexFace j k))
          (ULift.up 1) ∈ integralSmallChains U j
        apply Submodule.subset_span
        refine ⟨⟨s.val.comp (integralSimplexFace j k), ?_⟩, rfl⟩
        rcases s.property with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro _ ⟨z, rfl⟩
        exact ha ⟨integralSimplexFace j k z, rfl⟩
      exact hle c.property
    · rw [(integralChains X).shape i j hij]
      exact (integralSmallChains U j).zero_mem
  let C : Nat → ModuleCat.{u} Int := fun n =>
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    ModuleCat.of Int (integralSmallChains U n)
  let d (i j : Nat) : C i ⟶ C j := by
    letI : Module Int (integralSmallChains U i) := (integralSmallChains U i).module
    letI : Module Int (integralSmallChains U j) := (integralSmallChains U j).module
    exact ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U j)
      (((integralChains X).d i j).hom.domRestrict (integralSmallChains U i)) (hpres i j))
  refine { X := C, d := d, shape := ?_, d_comp_d' := ?_ }
  · intro i j hij
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (integralChains X).d i j c.val = 0
    rw [(integralChains X).shape i j hij]
    rfl
  · intro i j k _ _
    apply ConcreteCategory.hom_ext
    intro c
    apply Subtype.ext
    change (integralChains X).d j k ((integralChains X).d i j c.val) = 0
    exact congrArg (fun f : (integralChains X).X i ⟶ (integralChains X).X k =>
      f c.val) ((integralChains X).d_comp_d i j k)

def integralSmallChainInclusion (U : I → Set X) :
    integralSmallChainComplex U ⟶ integralChains X where
  f n := by
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    exact ModuleCat.ofHom (integralSmallChains U n).subtype
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

theorem integralSmallChainInclusion_mono (U : I → Set X) :
    Mono (integralSmallChainInclusion U) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  exact Subtype.ext h

end Poincare.Topology

end FzIntegralSmallChains

noncomputable section FzIntegralChainSupport

/-!
# Support of integral singular chains

These identities express the sum and intersection used in singular excision
in the actual free modules on continuous singular simplices.
-/


open CategoryTheory
open scoped BigOperators

universe u v

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {I : Type v}

theorem integralChainCoordinates_map (f : C(X, Y)) (n : Nat)
    (c : (integralChains X).X n) :
    integralChainCoordinates Y n ((integralChainsFunctor.map (TopCat.ofHom f)).f n c) =
      Finsupp.mapDomain (fun s => f.comp s) (integralChainCoordinates X n c) := by
  let EX := integralChainCoordinates X n
  let EY := integralChainCoordinates Y n
  let q := (integralChainsFunctor.map (TopCat.ofHom f)).f n
  have he : EY.toLinearMap.comp (q.hom.comp EX.symm.toLinearMap) =
      Finsupp.lmapDomain (ULift.{u} Int) Int (fun s => f.comp s) := by
    apply Finsupp.lhom_ext
    intro s a
    have hs : EX.symm (Finsupp.single s a) = integralSingularGenerator s a := by
      apply EX.injective
      rw [EX.apply_symm_apply]
      exact (integralChainCoordinates_generator s a).symm
    change EY (q (EX.symm (Finsupp.single s a))) =
      Finsupp.mapDomain (fun s => f.comp s) (Finsupp.single s a)
    rw [hs]
    have hq : q (integralSingularGenerator s a) = integralSingularGenerator (f.comp s) a :=
      congrArg (fun k => k a) (integralSingularGenerator_map s f)
    rw [hq, integralChainCoordinates_generator, Finsupp.mapDomain_single]
  have hec := LinearMap.congr_fun he (EX c)
  change EY (q (EX.symm (EX c))) = Finsupp.mapDomain (fun s => f.comp s) (EX c) at hec
  simpa only [EX.symm_apply_apply] using hec

theorem integralSingularGenerator_mem_small (U : I → Set X) {n : Nat}
    (s : C(integralSimplex n, X)) (hs : IntegralSmallSimplex U s)
    (a : ULift.{u} Int) : integralSingularGenerator s a ∈ integralSmallChains U n := by
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  rw [ha, map_zsmul]
  apply (integralSmallChains U n).toAddSubgroup.zsmul_mem
  exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩

theorem integralSmallChains_of_support (U : I → Set X) (n : Nat)
    (c : (integralChains X).X n)
    (hc : ∀ s ∈ (integralChainCoordinates X n c).support, IntegralSmallSimplex U s) :
    c ∈ integralSmallChains U n := by
  rw [integral_chain_finite_representation n c]
  apply Submodule.sum_mem
  intro s hs
  exact integralSingularGenerator_mem_small U s (hc s hs) _

theorem integralSmallChains_eq_top_of_univ (U : I → Set X) (i : I)
    (hi : U i = Set.univ) (n : Nat) : integralSmallChains U n = ⊤ := by
  apply top_unique
  intro c _
  apply integralSmallChains_of_support U n c
  intro s _
  exact ⟨i, by rw [hi]; exact Set.subset_univ _⟩

theorem integralSmallChainInclusion_isIso_of_univ (U : I → Set X) (i : I)
    (hi : U i = Set.univ) : IsIso (integralSmallChainInclusion U) := by
  have hdeg (n : Nat) : IsIso ((integralSmallChainInclusion U).f n) := by
    let : Mono ((integralSmallChainInclusion U).f n) :=
      (ModuleCat.mono_iff_injective _).mpr (fun _ _ h => Subtype.ext h)
    let : Epi ((integralSmallChainInclusion U).f n) :=
      (ModuleCat.epi_iff_surjective _).mpr (by
        intro c
        refine ⟨⟨c, ?_⟩, rfl⟩
        rw [integralSmallChains_eq_top_of_univ U i hi n]
        exact Submodule.mem_top)
    exact isIso_of_mono_of_epi _
  let := hdeg
  exact HomologicalComplex.Hom.isIso_of_components _

theorem integralSubspaceChains_range_le_small (U : I → Set X) (A : Set X)
    (i : I) (hi : A ⊆ U i) (n : Nat) :
    LinearMap.range ((integralSubspaceChains A).f n).hom ≤ integralSmallChains U n := by
  rintro _ ⟨c, rfl⟩
  apply integralSmallChains_of_support
  intro s hs
  let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcoord := integralChainCoordinates_map v n c
  change integralChainCoordinates X n ((integralSubspaceChains A).f n c) = _ at hcoord
  rw [hcoord] at hs
  obtain ⟨t, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hs)
  refine ⟨i, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hi (t z).property

theorem integralSingularGenerator_mem_subspace (A : Set X) {n : Nat}
    (s : C(integralSimplex n, X)) (hs : Set.range s ⊆ A) (a : ULift.{u} Int) :
    integralSingularGenerator s a ∈ LinearMap.range ((integralSubspaceChains A).f n).hom := by
  classical
  apply (integral_subspace_range_iff A n _).mpr
  rw [integralChainCoordinates_generator]
  intro t ht
  have hts : t = s := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp ht) (Finsupp.single_eq_of_ne hne)
  exact hts ▸ hs

theorem integralSubspaceChains_range_inf (A B : Set X) (n : Nat) :
    LinearMap.range ((integralSubspaceChains A).f n).hom ⊓
        LinearMap.range ((integralSubspaceChains B).f n).hom =
      LinearMap.range ((integralSubspaceChains (A ∩ B)).f n).hom := by
  ext c
  simp only [Submodule.mem_inf, integral_subspace_range_iff]
  constructor
  · rintro ⟨hA, hB⟩ s hs x hx
    exact ⟨hA s hs hx, hB s hs hx⟩
  · intro h
    exact ⟨fun s hs x hx => (h s hs hx).1, fun s hs x hx => (h s hs hx).2⟩

theorem integralSubspaceChains_range_preimage (A B : Set X) (n : Nat)
    (c : (integralChains B).X n) :
    (integralSubspaceChains B).f n c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ↔
      c ∈ LinearMap.range
        ((integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)).f n).hom := by
  let v : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(integralSimplex n, B) → C(integralSimplex n, X) := fun s => v.comp s
  have hg : Function.Injective g := by
    intro s t h
    ext z
    exact congrArg (fun q : C(integralSimplex n, X) => q z) h
  rw [integral_subspace_range_iff, integral_subspace_range_iff]
  have hcoord := integralChainCoordinates_map v n c
  change integralChainCoordinates X n ((integralSubspaceChains B).f n c) =
    Finsupp.mapDomain g (integralChainCoordinates B n c) at hcoord
  rw [hcoord]
  constructor
  · intro h s hs x hx
    have hmem : g s ∈ (Finsupp.mapDomain g (integralChainCoordinates B n c)).support := by
      rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply hg]
      exact Finsupp.mem_support_iff.mp hs
    obtain ⟨z, rfl⟩ := hx
    exact h (g s) hmem ⟨z, rfl⟩
  · intro h s hs x hx
    obtain ⟨t, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero (Finsupp.mem_support_iff.mp hs)
    have ht : t ∈ (integralChainCoordinates B n c).support := by
      rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply hg] at hs
      exact Finsupp.mem_support_iff.mpr hs
    obtain ⟨z, rfl⟩ := hx
    exact h t ht ⟨z, rfl⟩

theorem integralSmallChains_two_eq_sup (A B : Set X) (n : Nat) :
    integralSmallChains (fun b : Bool => if b then A else B) n =
      LinearMap.range ((integralSubspaceChains A).f n).hom ⊔
        LinearMap.range ((integralSubspaceChains B).f n).hom := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    obtain ⟨b, hb⟩ := s.property
    cases b with
    | false =>
        exact Submodule.mem_sup_right (integralSingularGenerator_mem_subspace B s.val hb _)
    | true =>
        exact Submodule.mem_sup_left (integralSingularGenerator_mem_subspace A s.val hb _)
  · apply sup_le
    · exact integralSubspaceChains_range_le_small _ A true (fun _ h => h) n
    · exact integralSubspaceChains_range_le_small _ B false (fun _ h => h) n

end Poincare.Topology

end FzIntegralChainSupport

noncomputable section FzIntegralOrderedChains

/-!
# Integral chains on ordered vertex tuples

The index counts vertices. The empty tuple supplies the auxiliary
augmentation used by the cone formula and the finite subdivision recursion.
-/


open scoped BigOperators

universe u v w

namespace Poincare.Topology

abbrev integralOrderedChains (V : Type u) (k : Nat) :=
  (Fin k → V) →₀ Int

def integralOrderedBoundary (V : Type u) (k : Nat) :
    integralOrderedChains V (k + 1) →ₗ[Int] integralOrderedChains V k :=
  ∑ i : Fin (k + 1), ((-1 : Int) ^ i.val) •
    Finsupp.lmapDomain Int Int (fun v : Fin (k + 1) → V => v ∘ i.succAbove)

def integralOrderedCone {V : Type u} (k : Nat) (b : V) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains V (k + 1) :=
  Finsupp.lmapDomain Int Int
    (fun v : Fin k → V => Fin.cons (α := fun _ : Fin (k + 1) => V) b v)

def integralOrderedMap {V : Type u} {W : Type v} (k : Nat) (f : V → W) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains W k :=
  Finsupp.lmapDomain Int Int (fun v : Fin k → V => f ∘ v)

theorem integralOrderedBoundary_single {V : Type u} (k : Nat)
    (v : Fin (k + 1) → V) (a : Int) :
    integralOrderedBoundary V k (Finsupp.single v a) =
      ∑ i : Fin (k + 1), ((-1 : Int) ^ i.val) •
        Finsupp.single (v ∘ i.succAbove) a := by
  simp [integralOrderedBoundary, Finsupp.lmapDomain_apply]

theorem integralOrderedCone_single {V : Type u} (k : Nat) (b : V)
    (v : Fin k → V) (a : Int) :
    integralOrderedCone k b (Finsupp.single v a) =
      Finsupp.single (Fin.cons (α := fun _ : Fin (k + 1) => V) b v) a := by
  simp [integralOrderedCone, Finsupp.lmapDomain_apply]

theorem integralOrderedMap_single {V : Type u} {W : Type v} (k : Nat)
    (f : V → W) (v : Fin k → V) (a : Int) :
    integralOrderedMap k f (Finsupp.single v a) = Finsupp.single (f ∘ v) a := by
  simp [integralOrderedMap, Finsupp.lmapDomain_apply]

theorem integralOrderedBoundary_cone_zero {V : Type u} (b : V)
    (c : integralOrderedChains V 0) :
    integralOrderedBoundary V 0 (integralOrderedCone 0 b c) = c := by
  have h : (integralOrderedBoundary V 0).comp (integralOrderedCone 0 b) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedBoundary V 0 (integralOrderedCone 0 b (Finsupp.single v a)) =
      Finsupp.single v a
    rw [integralOrderedCone_single, integralOrderedBoundary_single, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    exact congrArg (fun t : Fin 0 → V => Finsupp.single t a) (Subsingleton.elim _ _)
  exact LinearMap.congr_fun h c

theorem integralOrderedBoundary_cone_succ {V : Type u} (k : Nat) (b : V)
    (c : integralOrderedChains V (k + 1)) :
    integralOrderedBoundary V (k + 1) (integralOrderedCone (k + 1) b c) =
      c - integralOrderedCone k b (integralOrderedBoundary V k c) := by
  have h : (integralOrderedBoundary V (k + 1)).comp (integralOrderedCone (k + 1) b) =
      LinearMap.id - (integralOrderedCone k b).comp (integralOrderedBoundary V k) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedBoundary V (k + 1)
        (integralOrderedCone (k + 1) b (Finsupp.single v a)) =
      Finsupp.single v a - integralOrderedCone k b
        (integralOrderedBoundary V k (Finsupp.single v a))
    have hzero :
        Fin.cons (α := fun _ : Fin (k + 2) => V) b v ∘
          (0 : Fin (k + 2)).succAbove = v := by
      funext i
      rfl
    have hremove (i : Fin (k + 1)) : i.removeNth v = v ∘ i.succAbove := by
      funext j
      rfl
    rw [integralOrderedCone_single, integralOrderedBoundary_single,
      integralOrderedBoundary_single, map_sum, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, hzero, Fin.val_succ, pow_succ,
      mul_neg, mul_one, neg_smul, map_smul, integralOrderedCone_single,
      Fin.cons_comp_succ_succAbove, hremove, ← Finset.sum_neg_distrib,
      sub_eq_add_neg]
  exact LinearMap.congr_fun h c

theorem integralOrderedBoundary_boundary {V : Type u} (k : Nat)
    (c : integralOrderedChains V (k + 2)) :
    integralOrderedBoundary V k (integralOrderedBoundary V (k + 1) c) = 0 := by
  induction k with
  | zero =>
      have h : (integralOrderedBoundary V 0).comp (integralOrderedBoundary V 1) = 0 := by
        apply Finsupp.lhom_ext
        intro v a
        change integralOrderedBoundary V 0
          (integralOrderedBoundary V 1 (Finsupp.single v a)) = 0
        have hv : Finsupp.single v a =
            integralOrderedCone 1 (v 0) (Finsupp.single (Fin.tail v) a) := by
          rw [integralOrderedCone_single, Fin.cons_self_tail]
        rw [hv, integralOrderedBoundary_cone_succ, map_sub,
          integralOrderedBoundary_cone_zero, sub_self]
      exact LinearMap.congr_fun h c
  | succ k ih =>
      have h : (integralOrderedBoundary V (k + 1)).comp
          (integralOrderedBoundary V (k + 2)) = 0 := by
        apply Finsupp.lhom_ext
        intro v a
        change integralOrderedBoundary V (k + 1)
          (integralOrderedBoundary V (k + 2) (Finsupp.single v a)) = 0
        have hv : Finsupp.single v a =
            integralOrderedCone (k + 2) (v 0) (Finsupp.single (Fin.tail v) a) := by
          rw [integralOrderedCone_single, Fin.cons_self_tail]
        rw [hv, integralOrderedBoundary_cone_succ, map_sub,
          integralOrderedBoundary_cone_succ, ih, map_zero, sub_zero, sub_self]
      exact LinearMap.congr_fun h c

theorem integralOrderedMap_boundary {V : Type u} {W : Type v} (k : Nat)
    (f : V → W) (c : integralOrderedChains V (k + 1)) :
    integralOrderedMap k f (integralOrderedBoundary V k c) =
      integralOrderedBoundary W k (integralOrderedMap (k + 1) f c) := by
  have h : (integralOrderedMap k f).comp (integralOrderedBoundary V k) =
      (integralOrderedBoundary W k).comp (integralOrderedMap (k + 1) f) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap k f (integralOrderedBoundary V k (Finsupp.single v a)) =
      integralOrderedBoundary W k (integralOrderedMap (k + 1) f (Finsupp.single v a))
    rw [integralOrderedBoundary_single, map_sum, integralOrderedMap_single,
      integralOrderedBoundary_single]
    simp only [map_smul, integralOrderedMap_single, Function.comp_assoc]
  exact LinearMap.congr_fun h c

theorem integralOrderedMap_cone {V : Type u} {W : Type v} (k : Nat)
    (f : V → W) (b : V) (c : integralOrderedChains V k) :
    integralOrderedMap (k + 1) f (integralOrderedCone k b c) =
      integralOrderedCone k (f b) (integralOrderedMap k f c) := by
  have h : (integralOrderedMap (k + 1) f).comp (integralOrderedCone k b) =
      (integralOrderedCone k (f b)).comp (integralOrderedMap k f) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap (k + 1) f (integralOrderedCone k b (Finsupp.single v a)) =
      integralOrderedCone k (f b) (integralOrderedMap k f (Finsupp.single v a))
    rw [integralOrderedCone_single, integralOrderedMap_single,
      integralOrderedMap_single, integralOrderedCone_single]
    apply congrArg (fun t : Fin (k + 1) → W => Finsupp.single t a)
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact LinearMap.congr_fun h c

theorem integralOrderedMap_comp {V : Type u} {W : Type v} {Z : Type w}
    (k : Nat) (f : V → W) (g : W → Z) (c : integralOrderedChains V k) :
    integralOrderedMap k g (integralOrderedMap k f c) =
      integralOrderedMap k (g ∘ f) c := by
  have h : (integralOrderedMap k g).comp (integralOrderedMap k f) =
      integralOrderedMap k (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap k g (integralOrderedMap k f (Finsupp.single v a)) =
      integralOrderedMap k (g ∘ f) (Finsupp.single v a)
    rw [integralOrderedMap_single, integralOrderedMap_single, integralOrderedMap_single]
    rfl
  exact LinearMap.congr_fun h c

theorem integralOrderedMap_id {V : Type u} (k : Nat)
    (c : integralOrderedChains V k) :
    integralOrderedMap k (id : V → V) c = c := by
  have h : integralOrderedMap k (id : V → V) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro v a
    change integralOrderedMap k id (Finsupp.single v a) = Finsupp.single v a
    rw [integralOrderedMap_single]
    rfl
  exact LinearMap.congr_fun h c

end Poincare.Topology

end FzIntegralOrderedChains

noncomputable section FzIntegralOrderedSubdivision

/-!
# Subdivision and prism on ordered integral chains

Both maps use the augmented vertex-count grading. Their recursions require
only a center of each nonempty tuple; geometric properties of the center
are explicit hypotheses of the naturality and support statements.
-/


open scoped BigOperators

universe u v

namespace Poincare.Topology

def integralOrderedSubdivision {V : Type u}
    (b : ∀ n : Nat, (Fin (n + 1) → V) → V) (k : Nat) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains V k :=
  Nat.rec (motive := fun k => integralOrderedChains V k →ₗ[Int] integralOrderedChains V k)
    LinearMap.id
    (fun k S => Finsupp.lsum Int (fun v : Fin (k + 1) → V =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight
        (integralOrderedCone k (b k v)
          (S (integralOrderedBoundary V k (Finsupp.single v 1)))))) k

def integralOrderedPrism {V : Type u}
    (b : ∀ n : Nat, (Fin (n + 1) → V) → V) (k : Nat) :
    integralOrderedChains V k →ₗ[Int] integralOrderedChains V (k + 1) :=
  Nat.rec (motive := fun k =>
      integralOrderedChains V k →ₗ[Int] integralOrderedChains V (k + 1))
    0
    (fun k T => Finsupp.lsum Int (fun v : Fin (k + 1) → V =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight
        (integralOrderedCone (k + 1) (b k v)
          (Finsupp.single v 1 -
            integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
            T (integralOrderedBoundary V k (Finsupp.single v 1)))))) k

variable {V : Type u}
variable (b : ∀ n : Nat, (Fin (n + 1) → V) → V)

theorem integralOrderedSubdivision_zero :
    integralOrderedSubdivision b 0 = LinearMap.id := rfl

theorem integralOrderedSubdivision_single_succ (k : Nat)
    (v : Fin (k + 1) → V) :
    integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) =
      integralOrderedCone k (b k v)
        (integralOrderedSubdivision b k
          (integralOrderedBoundary V k (Finsupp.single v 1))) := by
  simp [integralOrderedSubdivision, Finsupp.lsum_single, LinearMap.smulRight_apply]

theorem integralOrderedPrism_zero : integralOrderedPrism b 0 = 0 := rfl

theorem integralOrderedPrism_single_succ (k : Nat)
    (v : Fin (k + 1) → V) :
    integralOrderedPrism b (k + 1) (Finsupp.single v 1) =
      integralOrderedCone (k + 1) (b k v)
        (Finsupp.single v 1 -
          integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
          integralOrderedPrism b k
            (integralOrderedBoundary V k (Finsupp.single v 1))) := by
  simp [integralOrderedPrism, Finsupp.lsum_single, LinearMap.smulRight_apply]

theorem integralOrderedSubdivision_one
    (hb : ∀ v : Fin 1 → V, b 0 v = v 0) :
    integralOrderedSubdivision b 1 = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext_ring
  change integralOrderedSubdivision b 1 (Finsupp.single v 1) = Finsupp.single v 1
  rw [integralOrderedSubdivision_single_succ, integralOrderedSubdivision_zero]
  change integralOrderedCone 0 (b 0 v)
    (integralOrderedBoundary V 0 (Finsupp.single v 1)) = Finsupp.single v 1
  rw [integralOrderedBoundary_single, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, integralOrderedCone_single, hb]
  apply congrArg (fun t : Fin 1 → V => Finsupp.single t (1 : Int))
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

theorem integralOrderedPrism_one
    (hb : ∀ v : Fin 1 → V, b 0 v = v 0) :
    integralOrderedPrism b 1 = 0 := by
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext_ring
  change integralOrderedPrism b 1 (Finsupp.single v 1) = 0
  rw [integralOrderedPrism_single_succ, integralOrderedSubdivision_one b hb,
    integralOrderedPrism_zero]
  simp

theorem integralOrderedSubdivision_boundary (k : Nat)
    (c : integralOrderedChains V (k + 1)) :
    integralOrderedBoundary V k (integralOrderedSubdivision b (k + 1) c) =
      integralOrderedSubdivision b k (integralOrderedBoundary V k c) := by
  induction k with
  | zero =>
      have h : (integralOrderedBoundary V 0).comp (integralOrderedSubdivision b 1) =
          (integralOrderedSubdivision b 0).comp (integralOrderedBoundary V 0) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V 0
          (integralOrderedSubdivision b 1 (Finsupp.single v 1)) =
            integralOrderedSubdivision b 0
              (integralOrderedBoundary V 0 (Finsupp.single v 1))
        rw [integralOrderedSubdivision_single_succ, integralOrderedBoundary_cone_zero]
      exact LinearMap.congr_fun h c
  | succ k ih =>
      have h : (integralOrderedBoundary V (k + 1)).comp
          (integralOrderedSubdivision b (k + 2)) =
          (integralOrderedSubdivision b (k + 1)).comp
            (integralOrderedBoundary V (k + 1)) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V (k + 1)
          (integralOrderedSubdivision b (k + 2) (Finsupp.single v 1)) =
            integralOrderedSubdivision b (k + 1)
              (integralOrderedBoundary V (k + 1) (Finsupp.single v 1))
        rw [integralOrderedSubdivision_single_succ, integralOrderedBoundary_cone_succ,
          ih, integralOrderedBoundary_boundary, map_zero, map_zero, sub_zero]
      exact LinearMap.congr_fun h c

theorem integralOrderedPrism_boundary (k : Nat)
    (c : integralOrderedChains V (k + 1)) :
    integralOrderedBoundary V (k + 1) (integralOrderedPrism b (k + 1) c) +
      integralOrderedPrism b k (integralOrderedBoundary V k c) =
        c - integralOrderedSubdivision b (k + 1) c := by
  induction k with
  | zero =>
      have h : (integralOrderedBoundary V 1).comp (integralOrderedPrism b 1) +
          (integralOrderedPrism b 0).comp (integralOrderedBoundary V 0) =
          LinearMap.id - integralOrderedSubdivision b 1 := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V 1
            (integralOrderedPrism b 1 (Finsupp.single v 1)) +
          integralOrderedPrism b 0 (integralOrderedBoundary V 0 (Finsupp.single v 1)) =
            Finsupp.single v 1 - integralOrderedSubdivision b 1 (Finsupp.single v 1)
        rw [integralOrderedPrism_single_succ, integralOrderedPrism_zero]
        simp only [LinearMap.zero_apply, sub_zero, add_zero]
        have hz : integralOrderedBoundary V 0
            (Finsupp.single v 1 - integralOrderedSubdivision b 1 (Finsupp.single v 1)) =
            0 := by
          rw [map_sub, integralOrderedSubdivision_boundary, integralOrderedSubdivision_zero]
          exact sub_self _
        rw [integralOrderedBoundary_cone_succ, hz, map_zero, sub_zero]
      exact LinearMap.congr_fun h c
  | succ k ih =>
      have h : (integralOrderedBoundary V (k + 2)).comp
          (integralOrderedPrism b (k + 2)) +
          (integralOrderedPrism b (k + 1)).comp (integralOrderedBoundary V (k + 1)) =
          LinearMap.id - integralOrderedSubdivision b (k + 2) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedBoundary V (k + 2)
            (integralOrderedPrism b (k + 2) (Finsupp.single v 1)) +
          integralOrderedPrism b (k + 1)
            (integralOrderedBoundary V (k + 1) (Finsupp.single v 1)) =
          Finsupp.single v 1 - integralOrderedSubdivision b (k + 2) (Finsupp.single v 1)
        have ht := ih (integralOrderedBoundary V (k + 1) (Finsupp.single v 1))
        rw [integralOrderedBoundary_boundary, map_zero, add_zero] at ht
        have hz : integralOrderedBoundary V (k + 1)
            (Finsupp.single v 1 - integralOrderedSubdivision b (k + 2) (Finsupp.single v 1) -
              integralOrderedPrism b (k + 1)
                (integralOrderedBoundary V (k + 1) (Finsupp.single v 1))) = 0 := by
          rw [map_sub, map_sub, integralOrderedSubdivision_boundary, ht, sub_self]
        rw [integralOrderedPrism_single_succ, integralOrderedBoundary_cone_succ,
          hz, map_zero, sub_zero, sub_add_cancel]
      exact LinearMap.congr_fun h c

theorem integralOrderedSubdivision_map {W : Type v}
    (bW : ∀ n : Nat, (Fin (n + 1) → W) → W) (f : V → W)
    (hb : ∀ (n : Nat) (v : Fin (n + 1) → V), f (b n v) = bW n (f ∘ v))
    (k : Nat) (c : integralOrderedChains V k) :
    integralOrderedMap k f (integralOrderedSubdivision b k c) =
      integralOrderedSubdivision bW k (integralOrderedMap k f c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : (integralOrderedMap (k + 1) f).comp (integralOrderedSubdivision b (k + 1)) =
          (integralOrderedSubdivision bW (k + 1)).comp (integralOrderedMap (k + 1) f) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedMap (k + 1) f
            (integralOrderedSubdivision b (k + 1) (Finsupp.single v 1)) =
          integralOrderedSubdivision bW (k + 1)
            (integralOrderedMap (k + 1) f (Finsupp.single v 1))
        rw [integralOrderedSubdivision_single_succ, integralOrderedMap_cone, ih,
          integralOrderedMap_boundary, integralOrderedMap_single,
          integralOrderedSubdivision_single_succ, hb]
      exact LinearMap.congr_fun h c

theorem integralOrderedPrism_map {W : Type v}
    (bW : ∀ n : Nat, (Fin (n + 1) → W) → W) (f : V → W)
    (hb : ∀ (n : Nat) (v : Fin (n + 1) → V), f (b n v) = bW n (f ∘ v))
    (k : Nat) (c : integralOrderedChains V k) :
    integralOrderedMap (k + 1) f (integralOrderedPrism b k c) =
      integralOrderedPrism bW k (integralOrderedMap k f c) := by
  induction k with
  | zero => simp only [integralOrderedPrism_zero, LinearMap.zero_apply, map_zero]
  | succ k ih =>
      have h : (integralOrderedMap (k + 2) f).comp (integralOrderedPrism b (k + 1)) =
          (integralOrderedPrism bW (k + 1)).comp (integralOrderedMap (k + 1) f) := by
        apply Finsupp.lhom_ext'
        intro v
        apply LinearMap.ext_ring
        change integralOrderedMap (k + 2) f
            (integralOrderedPrism b (k + 1) (Finsupp.single v 1)) =
          integralOrderedPrism bW (k + 1)
            (integralOrderedMap (k + 1) f (Finsupp.single v 1))
        rw [integralOrderedPrism_single_succ, integralOrderedMap_cone,
          (integralOrderedMap (k + 1) f).map_sub,
          (integralOrderedMap (k + 1) f).map_sub,
          integralOrderedMap_single, integralOrderedSubdivision_map b bW f hb,
          ih, integralOrderedMap_boundary, integralOrderedMap_single,
          integralOrderedPrism_single_succ, hb]
      exact LinearMap.congr_fun h c

theorem integralOrderedSubdivision_support (A : Set V)
    (hA : ∀ (n : Nat) (v : Fin (n + 1) → V), Set.range v ⊆ A → b n v ∈ A)
    (k : Nat) (c : integralOrderedChains V k)
    (hc : ∀ v ∈ c.support, Set.range v ⊆ A) :
    ∀ v ∈ (integralOrderedSubdivision b k c).support, Set.range v ⊆ A := by
  classical
  induction k with
  | zero => exact hc
  | succ k ih =>
      have hfaces (v : Fin (k + 1) → V) (hv : Set.range v ⊆ A) :
          ∀ w ∈ (integralOrderedBoundary V k (Finsupp.single v 1)).support,
            Set.range w ⊆ A := by
        intro w hw
        rw [integralOrderedBoundary_single] at hw
        obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
        have heq : w = v ∘ i.succAbove :=
          ((Finsupp.mem_support_single _ _ _).mp (Finsupp.support_smul hwi)).1
        subst w
        rintro _ ⟨j, rfl⟩
        exact hv ⟨i.succAbove j, rfl⟩
      intro w hw
      change w ∈ (c.sum (fun v a => a • integralOrderedCone k (b k v)
        (integralOrderedSubdivision b k
          (integralOrderedBoundary V k (Finsupp.single v 1))))).support at hw
      obtain ⟨v, hvc, hw⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
      have hwcone := Finsupp.support_smul hw
      change w ∈ (Finsupp.mapDomain
        (fun t : Fin k → V => Fin.cons (α := fun _ : Fin (k + 1) => V) (b k v) t)
        (integralOrderedSubdivision b k
          (integralOrderedBoundary V k (Finsupp.single v 1)))).support at hwcone
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hwcone)
      have htA : Set.range t ⊆ A :=
        ih _ (hfaces v (hc v hvc)) t ht
      rintro _ ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hA k v (hc v hvc)
      · exact htA ⟨i, rfl⟩

theorem integralOrderedPrism_support (A : Set V)
    (hA : ∀ (n : Nat) (v : Fin (n + 1) → V), Set.range v ⊆ A → b n v ∈ A)
    (k : Nat) (c : integralOrderedChains V k)
    (hc : ∀ v ∈ c.support, Set.range v ⊆ A) :
    ∀ v ∈ (integralOrderedPrism b k c).support, Set.range v ⊆ A := by
  classical
  induction k with
  | zero =>
      intro v hv
      simp only [integralOrderedPrism_zero, LinearMap.zero_apply, Finsupp.support_zero,
        Finset.notMem_empty] at hv
  | succ k ih =>
      have hfaces (v : Fin (k + 1) → V) (hv : Set.range v ⊆ A) :
          ∀ w ∈ (integralOrderedBoundary V k (Finsupp.single v 1)).support,
            Set.range w ⊆ A := by
        intro w hw
        rw [integralOrderedBoundary_single] at hw
        obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hw)
        have heq : w = v ∘ i.succAbove :=
          ((Finsupp.mem_support_single _ _ _).mp (Finsupp.support_smul hwi)).1
        subst w
        rintro _ ⟨j, rfl⟩
        exact hv ⟨i.succAbove j, rfl⟩
      intro w hw
      change w ∈ (c.sum (fun v a => a • integralOrderedCone (k + 1) (b k v)
        (Finsupp.single v 1 - integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
          integralOrderedPrism b k
            (integralOrderedBoundary V k (Finsupp.single v 1))))).support at hw
      obtain ⟨v, hvc, hw⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
      have hwcone := Finsupp.support_smul hw
      change w ∈ (Finsupp.mapDomain
        (fun t : Fin (k + 1) → V =>
          Fin.cons (α := fun _ : Fin (k + 2) => V) (b k v) t)
        (Finsupp.single v 1 - integralOrderedSubdivision b (k + 1) (Finsupp.single v 1) -
          integralOrderedPrism b k
            (integralOrderedBoundary V k (Finsupp.single v 1)))).support at hwcone
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hwcone)
      have hunit : ∀ z ∈ (Finsupp.single v (1 : Int)).support, Set.range z ⊆ A := by
        intro z hz
        have hzv : z = v := ((Finsupp.mem_support_single _ _ _).mp hz).1
        subst z
        exact hc v hvc
      have htA : Set.range t ⊆ A := by
        rcases Finset.mem_union.mp (Finsupp.support_sub ht) with hs | ht
        · rcases Finset.mem_union.mp (Finsupp.support_sub hs) with hv | hs
          · exact hunit t hv
          · exact integralOrderedSubdivision_support b A hA (k + 1) _ hunit t hs
        · exact ih _ (hfaces v (hc v hvc)) t ht
      rintro _ ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hA k v (hc v hvc)
      · exact htA ⟨i, rfl⟩

end Poincare.Topology

end FzIntegralOrderedSubdivision

noncomputable section FzIntegralSimplexSubdivisionGeometry

/-!
# Geometry of integral simplex subdivision

The mean and affine maps use the ambient real coordinates of the actual
standard simplex. The mesh estimates concern every supported ordered tuple,
including repeated vertices and zero-dimensional simplices.
-/


open scoped BigOperators

namespace Poincare.Topology

def integralSimplexVertices (n : Nat) : Fin (n + 1) → integralSimplex n :=
  fun i => stdSimplex.vertex (S := Real) i

def integralSimplexBarycenter (d n : Nat)
    (v : Fin (n + 1) → integralSimplex d) : integralSimplex d := by
  refine ⟨((n + 1 : Real)⁻¹) • ∑ i, (v i).val, ?_⟩
  rw [Finset.smul_sum]
  apply (convex_stdSimplex Real (Fin (d + 1))).sum_mem
  · intro i _
    positivity
  · have hn : (n + 1 : Real) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_inv_cancel₀ hn
  · intro i _
    exact (v i).property

def integralSimplexAffine {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) :
    C(integralSimplex n, integralSimplex d) where
  toFun x := ⟨∑ i, x.val i • (v i).val,
    (convex_stdSimplex Real (Fin (d + 1))).sum_mem
      (fun i _ => x.property.1 i) x.property.2 (fun i _ => (v i).property)⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_finsetSum Finset.univ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)) _

theorem integralSimplexBarycenter_val (d n : Nat)
    (v : Fin (n + 1) → integralSimplex d) :
    (integralSimplexBarycenter d n v).val =
      ((n + 1 : Real)⁻¹) • ∑ i, (v i).val := rfl

theorem integralSimplexBarycenter_one (d : Nat) (v : Fin 1 → integralSimplex d) :
    integralSimplexBarycenter d 0 v = v 0 := by
  apply Subtype.ext
  simp [integralSimplexBarycenter_val]

theorem integralSimplexAffine_apply {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (x : integralSimplex n) :
    (integralSimplexAffine v x).val = ∑ i, x.val i • (v i).val := rfl

theorem integralSimplexAffine_vertex {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (i : Fin (n + 1)) :
    integralSimplexAffine v (integralSimplexVertices n i) = v i := by
  apply Subtype.ext
  funext j
  simp [integralSimplexAffine, integralSimplexVertices, stdSimplex.vertex,
    Pi.single_apply]

theorem integralSimplexAffine_vertices (n : Nat) :
    integralSimplexAffine (integralSimplexVertices n) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  simp [integralSimplexAffine, integralSimplexVertices, stdSimplex.vertex,
    Pi.single_apply]

theorem integralSimplexAffine_comp {d n k : Nat}
    (v : Fin (n + 1) → integralSimplex d)
    (w : Fin (k + 1) → integralSimplex n) :
    (integralSimplexAffine v).comp (integralSimplexAffine w) =
      integralSimplexAffine (fun i => integralSimplexAffine v (w i)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, integralSimplexAffine_apply]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem integralSimplexAffine_barycenter {d n k : Nat}
    (v : Fin (n + 1) → integralSimplex d)
    (w : Fin (k + 1) → integralSimplex n) :
    integralSimplexAffine v (integralSimplexBarycenter n k w) =
      integralSimplexBarycenter d k (fun i => integralSimplexAffine v (w i)) := by
  apply Subtype.ext
  simp only [integralSimplexAffine_apply, integralSimplexBarycenter_val]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem integralSimplexAffine_face {d n : Nat}
    (v : Fin (n + 2) → integralSimplex d) (i : Fin (n + 2)) :
    (integralSimplexAffine v).comp (integralSimplexFace n i) =
      integralSimplexAffine (v ∘ i.succAbove) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, integralSimplexAffine_apply]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ k : Fin (n + 2),
      FunOnFinite.linearMap Real Real i.succAbove x.val k * (v k).val j) =
    ∑ k : Fin (n + 1), x.val k * (v (i.succAbove k)).val j
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul,
    Finset.sum_filter, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem integralSimplexBarycenter_dist_le {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (D : Real) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (z : integralSimplex d)
    (hz : z.val ∈ convexHull Real (Set.range (fun i => (v i).val))) :
    dist (integralSimplexBarycenter d n v) z ≤ (n : Real) / (n + 1) * D := by
  have _ := hD
  have hn : (n + 1 : Real) ≠ 0 := by positivity
  have hmean (j : Fin (n + 1)) :
      (integralSimplexBarycenter d n v).val - (v j).val =
        (n + 1 : Real)⁻¹ • ∑ i, ((v i).val - (v j).val) := by
    rw [integralSimplexBarycenter_val]
    funext l
    simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_sub, Pi.mul_apply,
      Pi.add_apply, Pi.natCast_apply, Pi.one_apply, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul]
  have hvertex (j : Fin (n + 1)) :
      dist (integralSimplexBarycenter d n v).val (v j).val ≤
        (n : Real) / (n + 1) * D := by
    have hsum : ‖∑ i : Fin (n + 1), ((v i).val - (v j).val)‖ ≤ (n : Real) * D := by
      rw [Fin.sum_univ_succAbove (fun i => (v i).val - (v j).val) j]
      simp only [sub_self, zero_add]
      calc
        ‖∑ i : Fin n, ((v (j.succAbove i)).val - (v j).val)‖ ≤
            ∑ i : Fin n, ‖(v (j.succAbove i)).val - (v j).val‖ := norm_sum_le _ _
        _ ≤ ∑ _ : Fin n, D := Finset.sum_le_sum (fun i _ => by
          simpa only [Subtype.dist_eq, dist_eq_norm] using hv (j.succAbove i) j)
        _ = (n : Real) * D := by simp
    rw [dist_eq_norm, hmean, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      (n + 1 : Real)⁻¹ * ‖∑ i : Fin (n + 1), ((v i).val - (v j).val)‖ ≤
          (n + 1 : Real)⁻¹ * ((n : Real) * D) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (n : Real) / (n + 1) * D := by rw [div_eq_mul_inv]; ring
  have hball : convexHull Real (Set.range (fun i => (v i).val)) ⊆
      Metric.closedBall (integralSimplexBarycenter d n v).val
        ((n : Real) / (n + 1) * D) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨j, rfl⟩
    simpa only [Metric.mem_closedBall, dist_comm] using hvertex j
  change dist (integralSimplexBarycenter d n v).val z.val ≤ _
  rw [dist_comm]
  exact hball hz

theorem integralSimplexAffine_dist_le {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (D : Real) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : integralSimplex n) : dist (integralSimplexAffine v x)
      (integralSimplexAffine v y) ≤ D := by
  have _ := hD
  have hmem (z : integralSimplex n) :
      (integralSimplexAffine v z).val ∈
        convexHull Real (Set.range (fun i => (v i).val)) := by
    rw [integralSimplexAffine_apply]
    apply (convex_convexHull Real _).sum_mem
    · intro i _
      exact z.property.1 i
    · exact z.property.2
    · intro i _
      exact subset_convexHull Real _ ⟨i, rfl⟩
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩ :=
    convexHull_exists_dist_ge2 (hmem x) (hmem y)
  exact h.trans (hv i j)

theorem integralSimplexSubdivision_mesh {d n : Nat}
    (v : Fin (n + 1) → integralSimplex d) (D : Real) (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (w : Fin (n + 1) → integralSimplex d)
    (hw : w ∈ (integralOrderedSubdivision (integralSimplexBarycenter d)
      (n + 1) (Finsupp.single v 1)).support) :
    ∀ i j, dist (w i) (w j) ≤ (n : Real) / (n + 1) * D := by
  classical
  induction n generalizing D with
  | zero =>
      intro i j
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      simp
  | succ n ih =>
      rw [integralOrderedSubdivision_single_succ] at hw
      change w ∈ (Finsupp.mapDomain
        (fun t : Fin (n + 1) → integralSimplex d =>
          Fin.cons (α := fun _ : Fin (n + 2) => integralSimplex d)
            (integralSimplexBarycenter d (n + 1) v) t)
        (integralOrderedSubdivision (integralSimplexBarycenter d) (n + 1)
          (integralOrderedBoundary (integralSimplex d) (n + 1)
            (Finsupp.single v 1)))).support at hw
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
      rw [integralOrderedBoundary_single, map_sum] at ht
      simp only [map_smul] at ht
      obtain ⟨a, _, hta⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum ht)
      have hta' := Finsupp.support_smul hta
      have hface (i j : Fin (n + 1)) :
          dist ((v ∘ a.succAbove) i) ((v ∘ a.succAbove) j) ≤ D :=
        hv (a.succAbove i) (a.succAbove j)
      have htail := ih (v ∘ a.succAbove) D hD hface t hta'
      let A : Set (integralSimplex d) :=
        {p | p.val ∈ convexHull Real (Set.range (fun i => (v i).val))}
      have hA (m : Nat) (u : Fin (m + 1) → integralSimplex d)
          (hu : Set.range u ⊆ A) : integralSimplexBarycenter d m u ∈ A := by
        change (integralSimplexBarycenter d m u).val ∈
          convexHull Real (Set.range (fun i => (v i).val))
        rw [integralSimplexBarycenter_val, Finset.smul_sum]
        apply (convex_convexHull Real _).sum_mem
        · intro i _
          positivity
        · have hm : (m + 1 : Real) ≠ 0 := by positivity
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          exact mul_inv_cancel₀ hm
        · intro i _
          exact hu ⟨i, rfl⟩
      have hunit : ∀ u ∈ (Finsupp.single (v ∘ a.succAbove) (1 : Int)).support,
          Set.range u ⊆ A := by
        intro u hu
        have he : u = v ∘ a.succAbove := ((Finsupp.mem_support_single _ _ _).mp hu).1
        subst u
        rintro _ ⟨j, rfl⟩
        exact subset_convexHull Real _ ⟨a.succAbove j, rfl⟩
      have htA : Set.range t ⊆ A :=
        integralOrderedSubdivision_support (integralSimplexBarycenter d)
          A hA (n + 1) _ hunit t hta'
      have hcenter (j : Fin (n + 1)) :
          dist (integralSimplexBarycenter d (n + 1) v) (t j) ≤
            ((n + 1 : Nat) : Real) / (((n + 1 : Nat) : Real) + 1) * D :=
        integralSimplexBarycenter_dist_le v D hD hv (t j) (htA ⟨j, rfl⟩)
      have hfactor : (n : Real) / (n + 1) ≤
          ((n + 1 : Nat) : Real) / (((n + 1 : Nat) : Real) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        nlinarith
      have hR : 0 ≤ ((n + 1 : Nat) : Real) /
          (((n + 1 : Nat) : Real) + 1) * D := by positivity
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [dist_self] using hR
        · exact hcenter j
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [Fin.cons_succ, Fin.cons_zero, dist_comm] using hcenter i
        · exact (htail i j).trans (mul_le_mul_of_nonneg_right hfactor hD)

theorem integralSimplexSubdivision_iterate_mesh {d n : Nat}
    (r : Nat) (v : Fin (n + 1) → integralSimplex d)
    (D : Real) (hD : 0 ≤ D) (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (w : Fin (n + 1) → integralSimplex d)
    (hw : w ∈ (((integralOrderedSubdivision (integralSimplexBarycenter d)
      (n + 1)) ^ r) (Finsupp.single v 1)).support) :
    ∀ i j, dist (w i) (w j) ≤ ((n : Real) / (n + 1)) ^ r * D := by
  classical
  induction r generalizing w with
  | zero =>
      simp only [pow_zero, Module.End.one_apply, Finsupp.mem_support_single] at hw
      obtain ⟨rfl, _⟩ := hw
      simpa only [pow_zero, one_mul] using hv
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply] at hw
      let c := ((integralOrderedSubdivision (integralSimplexBarycenter d)
        (n + 1)) ^ r) (Finsupp.single v 1)
      change w ∈ (c.sum (fun u a => a • integralOrderedCone n
        (integralSimplexBarycenter d n u)
        (integralOrderedSubdivision (integralSimplexBarycenter d) n
          (integralOrderedBoundary (integralSimplex d) n
            (Finsupp.single u 1))))).support at hw
      obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hw)
      have hwu' : w ∈ (integralOrderedSubdivision (integralSimplexBarycenter d)
          (n + 1) (Finsupp.single u 1)).support := by
        rw [integralOrderedSubdivision_single_succ]
        exact Finsupp.support_smul hwu
      have huD := ih u hu
      have hbound := integralSimplexSubdivision_mesh u
        (((n : Real) / (n + 1)) ^ r * D) (by positivity) huD w hwu'
      simpa only [pow_succ', mul_assoc] using hbound

end Poincare.Topology

end FzIntegralSimplexSubdivisionGeometry

noncomputable section FzIntegralTupleRealization

/-!
# Realization of ordered tuples in actual integral singular chains

Each tuple realizes as its affine singular simplex. Integer linear
extension preserves boundaries, affine changes of model and small support.
-/


open CategoryTheory
open scoped BigOperators

universe u v

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {I : Type v}

def integralTupleRealization (d n : Nat) (s : C(integralSimplex d, X)) :
    integralOrderedChains (integralSimplex d) (n + 1) →ₗ[Int]
      (integralChains X).X n :=
  letI : MulAction Int ((integralChains X).X n) :=
    ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
  Finsupp.lsum (N := (integralChains X).X n) Int
    (fun v : Fin (n + 1) → integralSimplex d =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (M := (integralChains X).X n)
        (integralSingularGenerator (s.comp (integralSimplexAffine v)) (ULift.up 1)))

theorem integralTupleRealization_single (d n : Nat)
    (s : C(integralSimplex d, X))
    (v : Fin (n + 1) → integralSimplex d) (a : Int) :
    integralTupleRealization d n s (Finsupp.single v a) =
      a • integralSingularGenerator (s.comp (integralSimplexAffine v)) (ULift.up 1) := by
  simp only [integralTupleRealization, Finsupp.lsum_single,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  exact int_smul_eq_zsmul ((integralChains X).X n).isModule a _

theorem integralTupleRealization_boundary (d n : Nat)
    (s : C(integralSimplex d, X))
    (c : integralOrderedChains (integralSimplex d) (n + 2)) :
    (integralChains X).d (n + 1) n (integralTupleRealization d (n + 1) s c) =
      integralTupleRealization d n s
        (integralOrderedBoundary (integralSimplex d) (n + 1) c) := by
  have h : ((integralChains X).d (n + 1) n).hom.comp
        (integralTupleRealization d (n + 1) s) =
      (integralTupleRealization d n s).comp
        (integralOrderedBoundary (integralSimplex d) (n + 1)) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change (integralChains X).d (n + 1) n
        (integralTupleRealization d (n + 1) s (Finsupp.single v 1)) =
      integralTupleRealization d n s
        (integralOrderedBoundary (integralSimplex d) (n + 1) (Finsupp.single v 1))
    rw [integralTupleRealization_single, one_smul,
      integralOrderedBoundary_single, map_sum]
    simp only [map_zsmul, integralTupleRealization_single, one_smul]
    let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
        (integralChains X).X n :=
      { toFun := fun f => f (ULift.up 1)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hg := congrArg ev
      (integralSingularGenerator_boundary (s.comp (integralSimplexAffine v)))
    rw [map_sum] at hg
    change (integralChains X).d (n + 1) n
      (integralSingularGenerator (s.comp (integralSimplexAffine v)) (ULift.up 1)) = _ at hg
    rw [hg]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    apply congrArg (fun x : (integralChains X).X n => ((-1 : Int) ^ i.val) • x)
    change integralSingularGenerator
        (s.comp ((integralSimplexAffine v).comp (integralSimplexFace n i)))
          (ULift.up 1) =
      integralSingularGenerator (s.comp (integralSimplexAffine (v ∘ i.succAbove)))
        (ULift.up 1)
    rw [integralSimplexAffine_face]
  exact LinearMap.congr_fun h c

theorem integralTupleRealization_affine {d e : Nat} (n : Nat)
    (v : Fin (d + 1) → integralSimplex e) (s : C(integralSimplex e, X))
    (c : integralOrderedChains (integralSimplex d) (n + 1)) :
    integralTupleRealization d n (s.comp (integralSimplexAffine v)) c =
      integralTupleRealization e n s
        (integralOrderedMap (n + 1) (integralSimplexAffine v) c) := by
  have h : integralTupleRealization d n (s.comp (integralSimplexAffine v)) =
      (integralTupleRealization e n s).comp
        (integralOrderedMap (n + 1) (integralSimplexAffine v)) := by
    apply Finsupp.lhom_ext
    intro w a
    change integralTupleRealization d n (s.comp (integralSimplexAffine v))
        (Finsupp.single w a) =
      integralTupleRealization e n s
        (integralOrderedMap (n + 1) (integralSimplexAffine v) (Finsupp.single w a))
    rw [integralOrderedMap_single, integralTupleRealization_single,
      integralTupleRealization_single]
    apply congrArg (fun x : (integralChains X).X n => a • x)
    change integralSingularGenerator
        (s.comp ((integralSimplexAffine v).comp (integralSimplexAffine w)))
          (ULift.up 1) =
      integralSingularGenerator
        (s.comp (integralSimplexAffine ((integralSimplexAffine v) ∘ w))) (ULift.up 1)
    rw [integralSimplexAffine_comp]
    rfl
  exact LinearMap.congr_fun h c

theorem integralTupleRealization_natural (d n : Nat)
    (s : C(integralSimplex d, X)) (f : C(X, Y))
    (c : integralOrderedChains (integralSimplex d) (n + 1)) :
    (integralChainsFunctor.map (TopCat.ofHom f)).f n
      (integralTupleRealization d n s c) =
        integralTupleRealization d n (f.comp s) c := by
  have h : ((integralChainsFunctor.map (TopCat.ofHom f)).f n).hom.comp
        (integralTupleRealization d n s) =
      integralTupleRealization d n (f.comp s) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change (integralChainsFunctor.map (TopCat.ofHom f)).f n
        (integralTupleRealization d n s (Finsupp.single v 1)) =
      integralTupleRealization d n (f.comp s) (Finsupp.single v 1)
    simp only [integralTupleRealization_single, one_smul]
    exact congrArg
      (fun g : integralCoefficient.{u} ⟶ (integralChains Y).X n => g (ULift.up 1))
      (integralSingularGenerator_map (s.comp (integralSimplexAffine v)) f)
  exact LinearMap.congr_fun h c

theorem integralTupleRealization_small (U : I → Set X) (d n : Nat)
    (s : C(integralSimplex d, X)) (hs : IntegralSmallSimplex U s)
    (c : integralOrderedChains (integralSimplex d) (n + 1)) :
    integralTupleRealization d n s c ∈ integralSmallChains U n := by
  classical
  have hgen (v : Fin (n + 1) → integralSimplex d) (a : Int) :
      integralTupleRealization d n s (Finsupp.single v a) ∈
        integralSmallChains U n := by
    rw [integralTupleRealization_single]
    apply (integralSmallChains U n).toAddSubgroup.zsmul_mem
    apply Submodule.subset_span
    refine ⟨⟨s.comp (integralSimplexAffine v), ?_⟩, rfl⟩
    rcases hs with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨integralSimplexAffine v z, rfl⟩
  rw [← Finsupp.sum_single c]
  change integralTupleRealization d n s
    (∑ v ∈ c.support, Finsupp.single v (c v)) ∈ integralSmallChains U n
  rw [map_sum]
  apply Submodule.sum_mem
  intro v _
  exact hgen v (c v)

end Poincare.Topology

end FzIntegralTupleRealization

noncomputable section FzIntegralSubdivision

/-!
# Barycentric subdivision of actual integral singular chains

The signed ordered operators are realized on each singular simplex.
Their prism, support bounds and geometric mesh control the actual iterates.
-/


open CategoryTheory
open scoped BigOperators Simplicial

universe u v

namespace Poincare.Topology

def integralBarycentricSubdivision (X : Type u) [TopologicalSpace X] :
    integralChains X ⟶ integralChains X := by
  classical
  let R (n : Nat) (s : C(integralSimplex n, X)) :=
    integralTupleRealization n n s
      (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
        (Finsupp.single (integralSimplexVertices n) 1))
  let F (n : Nat) : (integralChains X).X n ⟶ (integralChains X).X n :=
    letI : MulAction Int ((integralChains X).X n) :=
      ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
    ModuleCat.ofHom
      ((Finsupp.lsum (N := (integralChains X).X n) Int
        (fun s : C(integralSimplex n, X) =>
          (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
            (M := (integralChains X).X n) (R n s))).comp
        (integralChainCoordinates X n).toLinearMap)
  have hF (n : Nat) (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
      F n (integralSingularGenerator s a) = a.down • R n s := by
    let : MulAction Int ((integralChains X).X n) :=
      ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X n) Int
      (fun t : C(integralSimplex n, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X n) (R n t)))
      (integralChainCoordinates X n (integralSingularGenerator s a)) = _
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact int_smul_eq_zsmul ((integralChains X).X n).isModule a.down _
  have hface (n : Nat) (s : C(integralSimplex (n + 1), X)) (i : Fin (n + 2)) :
      R n (s.comp (integralSimplexFace n i)) =
        integralTupleRealization (n + 1) n s
          (integralOrderedSubdivision (integralSimplexBarycenter (n + 1)) (n + 1)
            (Finsupp.single (integralSimplexVertices (n + 1) ∘ i.succAbove) 1)) := by
    let w := integralSimplexVertices (n + 1) ∘ i.succAbove
    have hw : integralSimplexAffine w = integralSimplexFace n i := by
      simpa only [w, integralSimplexAffine_vertices, ContinuousMap.id_comp] using
        (integralSimplexAffine_face (integralSimplexVertices (n + 1)) i).symm
    have hb (k : Nat) (v : Fin (k + 1) → integralSimplex n) :
        integralSimplexAffine w (integralSimplexBarycenter n k v) =
          integralSimplexBarycenter (n + 1) k (integralSimplexAffine w ∘ v) :=
      integralSimplexAffine_barycenter w v
    have hvertex : integralSimplexAffine w ∘ integralSimplexVertices n = w := by
      funext j
      exact integralSimplexAffine_vertex w j
    dsimp only [R]
    rw [← hw, integralTupleRealization_affine,
      integralOrderedSubdivision_map (integralSimplexBarycenter n)
        (integralSimplexBarycenter (n + 1)) (integralSimplexAffine w) hb,
      integralOrderedMap_single, hvertex]
  have hunit (n : Nat) (s : C(integralSimplex (n + 1), X)) :
      (integralChains X).d (n + 1) n
          (F (n + 1) (integralSingularGenerator s (ULift.up 1))) =
        F n ((integralChains X).d (n + 1) n
          (integralSingularGenerator s (ULift.up 1))) := by
    let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
        (integralChains X).X n :=
      { toFun := fun f => f (ULift.up 1)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hd := congrArg ev (integralSingularGenerator_boundary s)
    rw [map_sum] at hd
    change (integralChains X).d (n + 1) n
      (integralSingularGenerator s (ULift.up 1)) = _ at hd
    rw [hF, one_smul, hd, map_sum]
    dsimp only [R]
    rw [integralTupleRealization_boundary, integralOrderedSubdivision_boundary,
      integralOrderedBoundary_single, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_zsmul]
    have hFi : F n (ev (integralSingularGenerator (s.comp (integralSimplexFace n i)))) =
        R n (s.comp (integralSimplexFace n i)) := by
      change F n (integralSingularGenerator (s.comp (integralSimplexFace n i)) (ULift.up 1)) = _
      exact (hF n _ (ULift.up 1)).trans (one_zsmul _)
    exact congrArg (fun c : (integralChains X).X n => ((-1 : Int) ^ i.val) • c)
      ((hface n s i).symm.trans hFi.symm)
  refine { f := F, comm' := ?_ }
  intro i j hij
  change j + 1 = i at hij
  subst i
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨s, rfl⟩ :=
    ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋j + 1⦌)).symm.surjective x
  change (CategoryStruct.comp (integralSingularGenerator s ) ( ((CategoryStruct.comp (F (j + 1) ) ( (integralChains X).d (j + 1) j))))) =
    (CategoryStruct.comp (integralSingularGenerator s ) ( ((CategoryStruct.comp ((integralChains X).d (j + 1) j ) ( F j)))))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  change (integralChains X).d (j + 1) j (F (j + 1) (integralSingularGenerator s a)) =
    F j ((integralChains X).d (j + 1) j (integralSingularGenerator s a))
  rw [ha]
  simp only [map_zsmul]
  exact congrArg (fun c : (integralChains X).X j => a.down • c) (hunit j s)

def integralSubdivisionPrism (X : Type u) [TopologicalSpace X] :
    Homotopy (𝟙 (integralChains X)) (integralBarycentricSubdivision X) := by
  classical
  let R (n : Nat) (s : C(integralSimplex n, X)) :=
    integralTupleRealization n (n + 1) s
      (integralOrderedPrism (integralSimplexBarycenter n) (n + 1)
        (Finsupp.single (integralSimplexVertices n) 1))
  let T (n : Nat) : (integralChains X).X n ⟶ (integralChains X).X (n + 1) :=
    letI : MulAction Int ((integralChains X).X (n + 1)) :=
      ((integralChains X).X (n + 1)).isModule.toDistribMulAction.toMulAction
    ModuleCat.ofHom
      ((Finsupp.lsum (N := (integralChains X).X (n + 1)) Int
        (fun s : C(integralSimplex n, X) =>
          (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
            (M := (integralChains X).X (n + 1)) (R n s))).comp
        (integralChainCoordinates X n).toLinearMap)
  let P (i j : Nat) : (integralChains X).X i ⟶ (integralChains X).X j :=
    if h : i + 1 = j then (CategoryStruct.comp (T i ) ( eqToHom (congrArg (fun k => (integralChains X).X k) h)))
    else 0
  have hT (n : Nat) (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
      T n (integralSingularGenerator s a) = a.down • R n s := by
    let : MulAction Int ((integralChains X).X (n + 1)) :=
      ((integralChains X).X (n + 1)).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X (n + 1)) Int
      (fun t : C(integralSimplex n, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X (n + 1)) (R n t)))
      (integralChainCoordinates X n (integralSingularGenerator s a)) = _
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact int_smul_eq_zsmul ((integralChains X).X (n + 1)).isModule a.down _
  have hS (n : Nat) (s : C(integralSimplex n, X)) :
      (integralBarycentricSubdivision X).f n (integralSingularGenerator s (ULift.up 1)) =
        integralTupleRealization n n s
          (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
            (Finsupp.single (integralSimplexVertices n) 1)) := by
    let Q (t : C(integralSimplex n, X)) :=
      integralTupleRealization n n t
        (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
          (Finsupp.single (integralSimplexVertices n) 1))
    let : MulAction Int ((integralChains X).X n) :=
      ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X n) Int
      (fun t : C(integralSimplex n, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X n) (Q t)))
      (integralChainCoordinates X n (integralSingularGenerator s (ULift.up 1))) = Q s
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact (int_smul_eq_zsmul ((integralChains X).X n).isModule 1 _).trans (one_zsmul _)
  have hface (n : Nat) (s : C(integralSimplex (n + 1), X)) (i : Fin (n + 2)) :
      R n (s.comp (integralSimplexFace n i)) =
        integralTupleRealization (n + 1) (n + 1) s
          (integralOrderedPrism (integralSimplexBarycenter (n + 1)) (n + 1)
            (Finsupp.single (integralSimplexVertices (n + 1) ∘ i.succAbove) 1)) := by
    let w := integralSimplexVertices (n + 1) ∘ i.succAbove
    have hw : integralSimplexAffine w = integralSimplexFace n i := by
      simpa only [w, integralSimplexAffine_vertices, ContinuousMap.id_comp] using
        (integralSimplexAffine_face (integralSimplexVertices (n + 1)) i).symm
    have hb (k : Nat) (v : Fin (k + 1) → integralSimplex n) :
        integralSimplexAffine w (integralSimplexBarycenter n k v) =
          integralSimplexBarycenter (n + 1) k (integralSimplexAffine w ∘ v) :=
      integralSimplexAffine_barycenter w v
    have hvertex : integralSimplexAffine w ∘ integralSimplexVertices n = w := by
      funext j
      exact integralSimplexAffine_vertex w j
    dsimp only [R]
    rw [← hw, integralTupleRealization_affine,
      integralOrderedPrism_map (integralSimplexBarycenter n)
        (integralSimplexBarycenter (n + 1)) (integralSimplexAffine w) hb,
      integralOrderedMap_single, hvertex]
  have hunit (n : Nat) (s : C(integralSimplex n, X)) :
      integralSingularGenerator s (ULift.up 1) =
        (dNext n P + prevD n P + (integralBarycentricSubdivision X).f n)
          (integralSingularGenerator s (ULift.up 1)) := by
    cases n with
    | zero =>
        have hzero : T 0 (integralSingularGenerator s (ULift.up 1)) = 0 := by
          rw [hT]
          dsimp only [R]
          rw [integralOrderedPrism_one _ (integralSimplexBarycenter_one 0),
            LinearMap.zero_apply, map_zero]
          exact one_zsmul _
        rw [dNext_eq_zero P 0 (by simp),
          prevD_eq P (show (ComplexShape.down Nat).Rel 1 0 from rfl)]
        simp only [P, dif_pos rfl, eqToHom_refl, Category.comp_id]
        change integralSingularGenerator s (ULift.up 1) =
          0 + (integralChains X).d 1 0 (T 0 (integralSingularGenerator s (ULift.up 1))) +
            (integralBarycentricSubdivision X).f 0 (integralSingularGenerator s (ULift.up 1))
        rw [hzero, map_zero, zero_add, zero_add, hS]
        rw [integralOrderedSubdivision_one _ (integralSimplexBarycenter_one 0)]
        simp only [LinearMap.id_apply, integralTupleRealization_single,
          one_smul, integralSimplexAffine_vertices, ContinuousMap.comp_id]
    | succ n =>
        let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
            (integralChains X).X n :=
          { toFun := fun f => f (ULift.up 1)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hd := congrArg ev (integralSingularGenerator_boundary s)
        rw [map_sum] at hd
        change (integralChains X).d (n + 1) n
          (integralSingularGenerator s (ULift.up 1)) = _ at hd
        have htd : T n ((integralChains X).d (n + 1) n
            (integralSingularGenerator s (ULift.up 1))) =
          integralTupleRealization (n + 1) (n + 1) s
            (integralOrderedPrism (integralSimplexBarycenter (n + 1)) (n + 1)
              (integralOrderedBoundary (integralSimplex (n + 1)) (n + 1)
                (Finsupp.single (integralSimplexVertices (n + 1)) 1))) := by
          rw [hd, map_sum, integralOrderedBoundary_single, map_sum, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [map_zsmul]
          have hTi : T n (ev (integralSingularGenerator (s.comp (integralSimplexFace n i)))) =
              R n (s.comp (integralSimplexFace n i)) := by
            change T n
              (integralSingularGenerator (s.comp (integralSimplexFace n i)) (ULift.up 1)) = _
            exact (hT n _ (ULift.up 1)).trans (one_zsmul _)
          exact congrArg (fun c : (integralChains X).X (n + 1) =>
            ((-1 : Int) ^ i.val) • c) (hTi.trans (hface n s i))
        have hpr := congrArg (integralTupleRealization (n + 1) (n + 1) s)
          (integralOrderedPrism_boundary (integralSimplexBarycenter (n + 1))
            (n + 1) (Finsupp.single (integralSimplexVertices (n + 1)) 1))
        rw [map_add, map_sub, integralTupleRealization_single, one_smul,
          integralSimplexAffine_vertices, ContinuousMap.comp_id] at hpr
        rw [dNext_eq P (show (ComplexShape.down Nat).Rel (n + 1) n from rfl),
          prevD_eq P (show (ComplexShape.down Nat).Rel (n + 2) (n + 1) from rfl)]
        simp only [P, dif_pos rfl, eqToHom_refl, Category.comp_id]
        change integralSingularGenerator s (ULift.up 1) =
          T n ((integralChains X).d (n + 1) n (integralSingularGenerator s (ULift.up 1))) +
            (integralChains X).d (n + 2) (n + 1)
              (T (n + 1) (integralSingularGenerator s (ULift.up 1))) +
            (integralBarycentricSubdivision X).f (n + 1)
              (integralSingularGenerator s (ULift.up 1))
        rw [htd, hT, one_smul, hS]
        dsimp only [R]
        rw [integralTupleRealization_boundary]
        calc
          _ = _ := sub_eq_iff_eq_add.mp hpr.symm
          _ = _ := by abel
  refine { hom := P, zero := ?_, comm := ?_ }
  · intro i j hij
    exact dif_neg hij
  · intro n
    apply SSet.chainComplex_hom_ext
    intro x
    obtain ⟨s, rfl⟩ :=
      ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm.surjective x
    change (CategoryStruct.comp (integralSingularGenerator s ) ( 𝟙 ((integralChains X).X n))) =
      (CategoryStruct.comp (integralSingularGenerator s ) (
        (dNext n P + prevD n P + (integralBarycentricSubdivision X).f n)))
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
      apply ULift.ext
      simp
    change integralSingularGenerator s a =
      (dNext n P + prevD n P + (integralBarycentricSubdivision X).f n)
        (integralSingularGenerator s a)
    rw [ha]
    simp only [map_zsmul]
    exact congrArg (fun c : (integralChains X).X n => a.down • c) (hunit n s)

def integralSubdivisionIterate (X : Type u) [TopologicalSpace X] (k : Nat) :
    integralChains X ⟶ integralChains X :=
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  CategoryTheory.End.asHom (S ^ k)

def integralIteratedSubdivisionPrism (X : Type u) [TopologicalSpace X]
    (k : Nat) : Homotopy (𝟙 (integralChains X)) (integralSubdivisionIterate X k) := by
  classical
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  let T := integralSubdivisionPrism X
  let P (k i j : Nat) :=
    ∑ r ∈ Finset.range k, (CategoryStruct.comp ((CategoryTheory.End.asHom (S ^ r)).f i ) ( T.hom i j))
  have hstep (r i : Nat) :
      (CategoryTheory.End.asHom (S ^ r)).f i =
        dNext i (fun a b => (CategoryStruct.comp ((CategoryTheory.End.asHom (S ^ r)).f a ) ( T.hom a b))) +
        prevD i (fun a b => (CategoryStruct.comp ((CategoryTheory.End.asHom (S ^ r)).f a ) ( T.hom a b))) +
        (CategoryTheory.End.asHom (S ^ (r + 1))).f i := by
    have h := (T.compLeft (CategoryTheory.End.asHom (S ^ r))).comm i
    dsimp only [Homotopy.compLeft] at h
    simpa only [Category.comp_id, pow_succ',
      CategoryTheory.End.mul_def, S, CategoryTheory.End.of, CategoryTheory.End.asHom] using h
  have hc (r i : Nat) : 𝟙 ((integralChains X).X i) =
      dNext i (P r) + prevD i (P r) + (CategoryTheory.End.asHom (S ^ r)).f i := by
    induction r with
    | zero =>
        have hP : P 0 = 0 := by
          funext a b
          exact Finset.sum_range_zero _
        rw [hP, map_zero, map_zero, zero_add, zero_add]
        rfl
    | succ r ih =>
        have hP : P (r + 1) = P r +
            (fun a b => (CategoryStruct.comp ((CategoryTheory.End.asHom (S ^ r)).f a ) ( T.hom a b))) := by
          funext a b
          exact Finset.sum_range_succ _ r
        rw [hP, map_add, map_add]
        calc
          _ = _ := ih
          _ = _ := by rw [hstep r i]; abel
  refine { hom := P k, zero := ?_, comm := hc k }
  intro i j hij
  dsimp only [P]
  apply Finset.sum_eq_zero
  intro r _
  rw [T.zero i j hij, CategoryTheory.Limits.comp_zero]

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {I : Type v}

theorem integralSubdivisionIterate_zero :
    integralSubdivisionIterate X 0 = 𝟙 (integralChains X) := rfl

theorem integralIteratedSubdivisionPrism_zero (i j : Nat) :
    (integralIteratedSubdivisionPrism X 0).hom i j = 0 := by
  simp only [integralIteratedSubdivisionPrism, Finset.sum_range_zero]

theorem integralSubdivision_natural (f : C(X, Y)) :
    (CategoryStruct.comp (integralBarycentricSubdivision X ) ( integralChainsFunctor.map (TopCat.ofHom f))) =
      (CategoryStruct.comp (integralChainsFunctor.map (TopCat.ofHom f) ) ( integralBarycentricSubdivision Y)) := by
  have hS (Z : Type u) [TopologicalSpace Z] (n : Nat) (s : C(integralSimplex n, Z)) :
      (integralBarycentricSubdivision Z).f n (integralSingularGenerator s (ULift.up 1)) =
        integralTupleRealization n n s
          (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
            (Finsupp.single (integralSimplexVertices n) 1)) := by
    let Q (t : C(integralSimplex n, Z)) :=
      integralTupleRealization n n t
        (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
          (Finsupp.single (integralSimplexVertices n) 1))
    let : MulAction Int ((integralChains Z).X n) :=
      ((integralChains Z).X n).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains Z).X n) Int
      (fun t : C(integralSimplex n, Z) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains Z).X n) (Q t)))
      (integralChainCoordinates Z n (integralSingularGenerator s (ULift.up 1))) = Q s
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact (int_smul_eq_zsmul ((integralChains Z).X n).isModule 1 _).trans (one_zsmul _)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨s, rfl⟩ :=
    ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm.surjective x
  change (CategoryStruct.comp (integralSingularGenerator s ) (
      ((CategoryStruct.comp ((integralBarycentricSubdivision X).f n ) (
        (integralChainsFunctor.map (TopCat.ofHom f)).f n))))) =
    (CategoryStruct.comp (integralSingularGenerator s ) (
      ((CategoryStruct.comp ((integralChainsFunctor.map (TopCat.ofHom f)).f n ) (
        (integralBarycentricSubdivision Y).f n)))))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : (integralChainsFunctor.map (TopCat.ofHom f)).f n
      (integralSingularGenerator s (ULift.up 1)) =
        integralSingularGenerator (f.comp s) (ULift.up 1) :=
    congrArg (fun q : integralCoefficient.{u} ⟶ (integralChains Y).X n => q (ULift.up 1))
      (integralSingularGenerator_map s f)
  change (integralChainsFunctor.map (TopCat.ofHom f)).f n
      ((integralBarycentricSubdivision X).f n (integralSingularGenerator s a)) =
    (integralBarycentricSubdivision Y).f n
      ((integralChainsFunctor.map (TopCat.ofHom f)).f n (integralSingularGenerator s a))
  rw [ha]
  simp only [map_zsmul]
  apply congrArg (fun c : (integralChains Y).X n => a.down • c)
  rw [hS, integralTupleRealization_natural, hg, hS]

theorem integralSubdivision_small (U : I → Set X) (n : Nat)
    (c : (integralChains X).X n) (hc : c ∈ integralSmallChains U n) :
    (integralBarycentricSubdivision X).f n c ∈ integralSmallChains U n := by
  have hle : integralSmallChains U n ≤
      (integralSmallChains U n).comap ((integralBarycentricSubdivision X).f n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change (integralBarycentricSubdivision X).f n
      (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains U n
    have hS : (integralBarycentricSubdivision X).f n
        (integralSingularGenerator s.val (ULift.up 1)) =
      integralTupleRealization n n s.val
        (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
          (Finsupp.single (integralSimplexVertices n) 1)) := by
      let Q (t : C(integralSimplex n, X)) :=
        integralTupleRealization n n t
          (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
            (Finsupp.single (integralSimplexVertices n) 1))
      let : MulAction Int ((integralChains X).X n) :=
        ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
      change (Finsupp.lsum (N := (integralChains X).X n) Int
        (fun t : C(integralSimplex n, X) =>
          (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
            (M := (integralChains X).X n) (Q t)))
        (integralChainCoordinates X n (integralSingularGenerator s.val (ULift.up 1))) = Q s.val
      rw [integralChainCoordinates_generator, Finsupp.lsum_single,
        LinearMap.smulRight_apply]
      exact (int_smul_eq_zsmul ((integralChains X).X n).isModule 1 _).trans (one_zsmul _)
    rw [hS]
    exact integralTupleRealization_small U n n s.val s.property _
  exact hle hc

theorem integralIteratedSubdivisionPrism_small (U : I → Set X) (k i j : Nat)
    (c : (integralChains X).X i) (hc : c ∈ integralSmallChains U i) :
    (integralIteratedSubdivisionPrism X k).hom i j c ∈ integralSmallChains U j := by
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  have hpow (r n : Nat) (c : (integralChains X).X n)
      (hc : c ∈ integralSmallChains U n) :
      (CategoryTheory.End.asHom (S ^ r)).f n c ∈ integralSmallChains U n := by
    induction r with
    | zero => simpa using hc
    | succ r ih =>
        rw [pow_succ', CategoryTheory.End.mul_def]
        exact integralSubdivision_small U n _ ih
  have hT (a b : Nat) (c : (integralChains X).X a)
      (hc : c ∈ integralSmallChains U a) :
      (integralSubdivisionPrism X).hom a b c ∈ integralSmallChains U b := by
    by_cases hab : a + 1 = b
    · subst b
      have hle : integralSmallChains U a ≤ (integralSmallChains U (a + 1)).comap
          ((integralSubdivisionPrism X).hom a (a + 1)).hom := by
        apply Submodule.span_le.mpr
        rintro _ ⟨s, rfl⟩
        change (integralSubdivisionPrism X).hom a (a + 1)
          (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains U (a + 1)
        have hgen : (integralSubdivisionPrism X).hom a (a + 1)
            (integralSingularGenerator s.val (ULift.up 1)) =
          integralTupleRealization a (a + 1) s.val
            (integralOrderedPrism (integralSimplexBarycenter a) (a + 1)
              (Finsupp.single (integralSimplexVertices a) 1)) := by
          let Q (t : C(integralSimplex a, X)) :=
            integralTupleRealization a (a + 1) t
              (integralOrderedPrism (integralSimplexBarycenter a) (a + 1)
                (Finsupp.single (integralSimplexVertices a) 1))
          let : MulAction Int ((integralChains X).X (a + 1)) :=
            ((integralChains X).X (a + 1)).isModule.toDistribMulAction.toMulAction
          simp only [integralSubdivisionPrism, dif_pos rfl, eqToHom_refl]
          change (Finsupp.lsum (N := (integralChains X).X (a + 1)) Int
            (fun t : C(integralSimplex a, X) =>
              (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
                (M := (integralChains X).X (a + 1)) (Q t)))
            (integralChainCoordinates X a (integralSingularGenerator s.val (ULift.up 1))) = Q s.val
          rw [integralChainCoordinates_generator, Finsupp.lsum_single,
            LinearMap.smulRight_apply]
          exact (int_smul_eq_zsmul ((integralChains X).X (a + 1)).isModule 1 _).trans (one_zsmul _)
        rw [hgen]
        exact integralTupleRealization_small U a (a + 1) s.val s.property _
      exact hle hc
    · rw [(integralSubdivisionPrism X).zero a b hab]
      exact (integralSmallChains U b).zero_mem
  change ((∑ r ∈ Finset.range k,
    (CategoryStruct.comp ((CategoryTheory.End.asHom (S ^ r)).f i ) ( (integralSubdivisionPrism X).hom i j))).hom) c ∈ _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  exact hT i j _ (hpow r i c hc)

theorem integral_subdivision_eventually_small (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    (n : Nat) (c : (integralChains X).X n) :
    ∃ k : Nat, (integralSubdivisionIterate X k).f n c ∈ integralSmallChains U n := by
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  have hS (m : Nat) (s : C(integralSimplex m, X)) :
      (integralBarycentricSubdivision X).f m (integralSingularGenerator s (ULift.up 1)) =
        integralTupleRealization m m s
          (integralOrderedSubdivision (integralSimplexBarycenter m) (m + 1)
            (Finsupp.single (integralSimplexVertices m) 1)) := by
    let Q (t : C(integralSimplex m, X)) :=
      integralTupleRealization m m t
        (integralOrderedSubdivision (integralSimplexBarycenter m) (m + 1)
          (Finsupp.single (integralSimplexVertices m) 1))
    let : MulAction Int ((integralChains X).X m) :=
      ((integralChains X).X m).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X m) Int
      (fun t : C(integralSimplex m, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X m) (Q t)))
      (integralChainCoordinates X m (integralSingularGenerator s (ULift.up 1))) = Q s
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact (int_smul_eq_zsmul ((integralChains X).X m).isModule 1 _).trans (one_zsmul _)
  -- This identifies the actual chain-map iterate with the geometric ordered iterate.
  have hreal (d m : Nat) (s : C(integralSimplex d, X))
      (b : integralOrderedChains (integralSimplex d) (m + 1)) :
      (integralBarycentricSubdivision X).f m (integralTupleRealization d m s b) =
        integralTupleRealization d m s
          (integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1) b) := by
    have he : ((integralBarycentricSubdivision X).f m).hom.comp
          (integralTupleRealization d m s) =
        (integralTupleRealization d m s).comp
          (integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1)) := by
      apply Finsupp.lhom_ext'
      intro w
      apply LinearMap.ext_ring
      change (integralBarycentricSubdivision X).f m
          (integralTupleRealization d m s (Finsupp.single w 1)) =
        integralTupleRealization d m s
          (integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1)
            (Finsupp.single w 1))
      have hb (k : Nat) (v : Fin (k + 1) → integralSimplex m) :
          integralSimplexAffine w (integralSimplexBarycenter m k v) =
            integralSimplexBarycenter d k (integralSimplexAffine w ∘ v) :=
        integralSimplexAffine_barycenter w v
      have hvertex : integralSimplexAffine w ∘ integralSimplexVertices m = w := by
        funext i
        exact integralSimplexAffine_vertex w i
      rw [integralTupleRealization_single, one_smul, hS,
        integralTupleRealization_affine,
        integralOrderedSubdivision_map (integralSimplexBarycenter m)
          (integralSimplexBarycenter d) (integralSimplexAffine w) hb,
        integralOrderedMap_single, hvertex]
    exact LinearMap.congr_fun he b
  have hiter (r d m : Nat) (s : C(integralSimplex d, X))
      (b : integralOrderedChains (integralSimplex d) (m + 1)) :
      (CategoryTheory.End.asHom (S ^ r)).f m (integralTupleRealization d m s b) =
        integralTupleRealization d m s
          ((integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1) ^ r) b) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [pow_succ', CategoryTheory.End.mul_def]
        change (integralBarycentricSubdivision X).f m
            ((CategoryTheory.End.asHom (S ^ r)).f m (integralTupleRealization d m s b)) = _
        rw [ih, hreal, pow_succ', Module.End.mul_apply]
  have hpow (r m : Nat) (b : (integralChains X).X m)
      (hb : b ∈ integralSmallChains U m) :
      (CategoryTheory.End.asHom (S ^ r)).f m b ∈ integralSmallChains U m := by
    induction r with
    | zero => simpa using hb
    | succ r ih =>
        rw [pow_succ', CategoryTheory.End.mul_def]
        exact integralSubdivision_small U m _ ih
  have hgen (s : C(integralSimplex n, X)) :
      ∃ r : Nat, (CategoryTheory.End.asHom (S ^ r)).f n
        (integralSingularGenerator s (ULift.up 1)) ∈ integralSmallChains U n := by
    cases n with
    | zero =>
        have hx : s (integralSimplexVertices 0 0) ∈ ⋃ i, U i := by
          rw [hcover]
          exact Set.mem_univ _
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        have hs : IntegralSmallSimplex U s := by
          refine ⟨i, ?_⟩
          rintro _ ⟨z, rfl⟩
          simpa only [Subsingleton.elim z (integralSimplexVertices 0 0)] using hi
        refine ⟨0, ?_⟩
        change integralSingularGenerator s (ULift.up 1) ∈ integralSmallChains U 0
        exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
    | succ m =>
        let V : I → Set (integralSimplex (m + 1)) := fun i => s ⁻¹' U i
        have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage s.continuous
        have hVc : Set.univ ⊆ ⋃ i, V i := by
          intro z _
          have hz : s z ∈ ⋃ i, U i := by rw [hcover]; exact Set.mem_univ _
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        obtain ⟨δ, hδ, hball⟩ :=
          lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hV hVc
        let q : Real := ((m + 1 : Nat) : Real) / (((m + 1 : Nat) : Real) + 1)
        have hq0 : 0 ≤ q := by dsimp only [q]; positivity
        have hq1 : q < 1 := by
          dsimp only [q]
          rw [div_lt_one (by positivity)]
          exact lt_add_one _
        have hlim : ∀ᶠ r in Filter.atTop, q ^ r < δ :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually (gt_mem_nhds hδ)
        obtain ⟨r, hr⟩ := hlim.exists
        let b := (integralOrderedSubdivision (integralSimplexBarycenter (m + 1))
          (m + 2) ^ r) (Finsupp.single (integralSimplexVertices (m + 1)) 1)
        have hvertices (i j : Fin (m + 2)) :
            dist (integralSimplexVertices (m + 1) i)
              (integralSimplexVertices (m + 1) j) ≤ 1 := by
          exact (Metric.dist_le_diam_of_mem
            (isCompact_stdSimplex Real (Fin (m + 2))).isBounded
            (integralSimplexVertices (m + 1) i).property
            (integralSimplexVertices (m + 1) j).property).trans diam_stdSimplex_le
        have hsmall (w : Fin (m + 2) → integralSimplex (m + 1)) (hw : w ∈ b.support) :
            IntegralSmallSimplex U (s.comp (integralSimplexAffine w)) := by
          have hmesh : ∀ i j, dist (w i) (w j) ≤ q ^ r := by
            simpa only [q, mul_one] using
              integralSimplexSubdivision_iterate_mesh r (integralSimplexVertices (m + 1))
                1 zero_le_one hvertices w hw
          obtain ⟨i, hi⟩ := hball (w 0) (Set.mem_univ _)
          refine ⟨i, ?_⟩
          rintro _ ⟨z, rfl⟩
          apply hi
          change dist (integralSimplexAffine w z) (w 0) < δ
          have hd := integralSimplexAffine_dist_le w (q ^ r) (pow_nonneg hq0 r)
            hmesh z (integralSimplexVertices (m + 1) 0)
          rw [integralSimplexAffine_vertex] at hd
          exact hd.trans_lt hr
        have hbase : integralTupleRealization (m + 1) (m + 1) s
            (Finsupp.single (integralSimplexVertices (m + 1)) 1) =
              integralSingularGenerator s (ULift.up 1) := by
          rw [integralTupleRealization_single, one_smul,
            integralSimplexAffine_vertices, ContinuousMap.comp_id]
        refine ⟨r, ?_⟩
        rw [← hbase, hiter]
        change integralTupleRealization (m + 1) (m + 1) s b ∈ integralSmallChains U (m + 1)
        rw [← Finsupp.sum_single b]
        change integralTupleRealization (m + 1) (m + 1) s
          (∑ w ∈ b.support, Finsupp.single w (b w)) ∈ integralSmallChains U (m + 1)
        rw [map_sum]
        apply Submodule.sum_mem
        intro w hw
        rw [integralTupleRealization_single]
        apply (integralSmallChains U (m + 1)).toAddSubgroup.zsmul_mem
        exact Submodule.subset_span ⟨⟨_, hsmall w hw⟩, rfl⟩
  choose count hcount using hgen
  let k := (integralChainCoordinates X n c).support.sup count
  refine ⟨k, ?_⟩
  change (CategoryTheory.End.asHom (S ^ k)).f n c ∈ integralSmallChains U n
  rw [integral_chain_finite_representation n c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  let a := integralChainCoordinates X n c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  change (CategoryTheory.End.asHom (S ^ k)).f n (integralSingularGenerator s a) ∈ _
  rw [ha]
  simp only [map_zsmul]
  apply (integralSmallChains U n).toAddSubgroup.zsmul_mem
  have hle : count s ≤ k := Finset.le_sup hs
  have hk : k = (k - count s) + count s := (Nat.sub_add_cancel hle).symm
  rw [hk, pow_add, CategoryTheory.End.mul_def]
  exact hpow (k - count s) n _ (hcount s)

end Poincare.Topology

end FzIntegralSubdivision

noncomputable section FzIntegralSmallHomology

/-!
# Small chains compute integral singular homology

The proof works with elements of the actual cycle and homology modules.
Subdivision provides small representatives, and the subdivision prism turns
an ambient bounding chain into a small bounding chain. This includes degree zero.
-/


open CategoryTheory Limits

universe u v

namespace Poincare.Topology

private theorem integralHomologyπ_eq_zero_iff
    (K : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔
      ∃ b : K.X (n + 1), K.d (n + 1) n b = K.iCycles n z := by
  let T := ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n + 1) n)
  have hT : T.Exact := T.exact_of_g_is_cokernel
    (K.homologyIsCokernel (n + 1) n (by simp))
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT z hz
    refine ⟨b, ?_⟩
    have he := congrArg (K.iCycles n) hb
    simpa only [T, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using he
  · rintro ⟨b, hb⟩
    have hb' : K.toCycles (n + 1) n b = z := by
      apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
      simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using hb
    rw [← hb']
    exact congrArg (fun q => q b) (K.toCycles_comp_homologyπ (n + 1) n)

private theorem integralSmall_boundary
    {X : Type u} [TopologicalSpace X] {I : Type v}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat)
    (c : (integralChains X).X n)
    (hc : (integralChains X).d n (n - 1) c = 0)
    (hsmall : c ∈ integralSmallChains U n)
    (b : (integralChains X).X (n + 1))
    (hb : (integralChains X).d (n + 1) n b = c) :
    ∃ b' : (integralChains X).X (n + 1),
      b' ∈ integralSmallChains U (n + 1) ∧
      (integralChains X).d (n + 1) n b' = c := by
  obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover (n + 1) b
  let K := integralChains X
  let S := integralSubdivisionIterate X k
  let H := integralIteratedSubdivisionPrism X k
  refine ⟨S.f (n + 1) b + H.hom n (n + 1) c,
    (integralSmallChains U (n + 1)).add_mem hk
      (integralIteratedSubdivisionPrism_small U k n (n + 1) c hsmall), ?_⟩
  have hbS : K.d (n + 1) n (S.f (n + 1) b) = S.f n c := by
    have he := congrArg (fun q => q b) (S.comm (n + 1) n)
    change K.d (n + 1) n (S.f (n + 1) b) = S.f n (K.d (n + 1) n b) at he
    rw [hb] at he
    exact he
  rw [map_add, hbS]
  have he := congrArg (fun q => q c) (H.comm n)
  rw [HomologicalComplex.id_f] at he
  cases n with
  | zero =>
      rw [dNext_eq_zero H.hom 0 (by simp),
        prevD_eq H.hom (show (ComplexShape.down Nat).Rel 1 0 from rfl)] at he
      change c = 0 + K.d 1 0 (H.hom 0 1 c) + S.f 0 c at he
      rw [zero_add] at he
      exact (add_comm _ _).trans he.symm
  | succ m =>
      rw [dNext_eq H.hom (show (ComplexShape.down Nat).Rel (m + 1) m from rfl),
        prevD_eq H.hom (show (ComplexShape.down Nat).Rel (m + 2) (m + 1) from rfl)] at he
      change c = H.hom m (m + 1) (K.d (m + 1) m c) +
        K.d (m + 2) (m + 1) (H.hom (m + 1) (m + 2) c) + S.f (m + 1) c at he
      have hc' : K.d (m + 1) m c = 0 := by simpa using hc
      rw [hc', map_zero, zero_add] at he
      exact (add_comm _ _).trans he.symm

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- The inclusion of small integral chains induces an isomorphism in every degree. -/
theorem integralSmallChainInclusion_homology_isIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralSmallChainInclusion U) n) := by
  let K := integralChains X
  let L := integralSmallChainComplex U
  let f := integralSmallChainInclusion U
  have hi (z : L.cycles n) :
      K.iCycles n (HomologicalComplex.cyclesMap f n z) =
        f.f n (L.iCycles n z) := by
    exact congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i f n)
  have hπ (z : L.cycles n) :
      K.homologyπ n (HomologicalComplex.cyclesMap f n z) =
        HomologicalComplex.homologyMap f n (L.homologyπ n z) := by
    exact (congrArg (fun q => q z)
      (HomologicalComplex.homologyπ_naturality (φ := f) (i := n))).symm
  have hinj : Function.Injective (HomologicalComplex.homologyMap f n) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro y hy
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ n)).mp inferInstance y
    have hz0 : K.homologyπ n (HomologicalComplex.cyclesMap f n z) = 0 := by
      rw [hπ, hz, hy]
    obtain ⟨b, hb⟩ := (integralHomologyπ_eq_zero_iff K n _).mp hz0
    rw [hi] at hb
    let c := L.iCycles n z
    have hc : K.d n (n - 1) (f.f n c) = 0 := by
      have he := congrArg (fun q => q c) (f.comm n (n - 1))
      change K.d n (n - 1) (f.f n c) = f.f (n - 1) (L.d n (n - 1) c) at he
      have hcz : L.d n (n - 1) c = 0 :=
        congrArg (fun q => q z) (L.iCycles_d n (n - 1))
      rw [hcz, map_zero] at he
      exact he
    obtain ⟨b', hb'small, hb'⟩ := integralSmall_boundary U hU hcover n
      (f.f n c) hc c.property b hb
    have hzsmall : L.homologyπ n z = 0 := by
      apply (integralHomologyπ_eq_zero_iff L n z).mpr
      refine ⟨⟨b', hb'small⟩, ?_⟩
      apply Subtype.ext
      exact hb'
    exact hz.symm.trans hzsmall
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap f n) := by
    intro y
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance y
    obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover n (K.iCycles n z)
    let S := integralSubdivisionIterate X k
    let z' := HomologicalComplex.cyclesMap S n z
    have hi' : K.iCycles n z' = S.f n (K.iCycles n z) :=
      congrArg (fun q => q z) (HomologicalComplex.cyclesMap_i S n)
    let c : L.X n := ⟨K.iCycles n z', by rw [hi']; exact hk⟩
    have hc : (L.sc n).g c = 0 := by
      apply Subtype.ext
      exact congrArg (fun q => q z') (K.iCycles_d n ((ComplexShape.down Nat).next n))
    let w : L.cycles n := (L.sc n).cyclesMk c hc
    have hw : L.iCycles n w = c := (L.sc n).i_cyclesMk c hc
    have hwmap : HomologicalComplex.cyclesMap f n w = z' := by
      apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
      rw [hi, hw]
      rfl
    refine ⟨L.homologyπ n w, ?_⟩
    rw [← hπ, hwmap]
    have hS : HomologicalComplex.homologyMap S n = 𝟙 _ := by
      simpa only [HomologicalComplex.homologyMap_id] using
        (integralIteratedSubdivisionPrism X k).homologyMap_eq n |>.symm
    have he := congrArg (fun q => q z)
      (HomologicalComplex.homologyπ_naturality (φ := S) (i := n))
    rw [hS] at he
    exact he.symm.trans hz
  let : Mono (HomologicalComplex.homologyMap f n) :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  let : Epi (HomologicalComplex.homologyMap f n) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi _

/-- Small chains and all singular chains have the same integral homology. -/
theorem integralSmallChainInclusion_quasiIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) :
    QuasiIso (integralSmallChainInclusion U) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact integralSmallChainInclusion_homology_isIso U hU hcover n

end Poincare.Topology

end FzIntegralSmallHomology

noncomputable section FzIntegralSmallRelativeChains

/-!
# Small relative integral chains

The small chains of a pair are the cokernel of the restricted-cover subspace
inclusion. The canonical map to relative singular chains is a quasi-isomorphism.
-/


open CategoryTheory Limits

universe u v

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] {I : Type v}

private theorem integralSubspaceChains_small (U : I → Set X) (A : Set X)
    (n : Nat) (c : (integralChains A).X n)
    (hc : c ∈ integralSmallChains (fun i => (Subtype.val : A → X) ⁻¹' U i) n) :
    (integralSubspaceChains A).f n c ∈ integralSmallChains U n := by
  let V : I → Set A := fun i => (Subtype.val : A → X) ⁻¹' U i
  have hle : integralSmallChains V n ≤
      (integralSmallChains U n).comap ((integralSubspaceChains A).f n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have he := congrArg (fun q => q (ULift.up 1)) (integralSingularGenerator_map s.val v)
    change (integralSubspaceChains A).f n (integralSingularGenerator s.val (ULift.up 1)) =
      integralSingularGenerator (v.comp s.val) (ULift.up 1) at he
    change (integralSubspaceChains A).f n (integralSingularGenerator s.val (ULift.up 1))
      ∈ integralSmallChains U n
    rw [he]
    apply Submodule.subset_span
    refine ⟨⟨v.comp s.val, ?_⟩, rfl⟩
    obtain ⟨i, hi⟩ := s.property
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨z, rfl⟩
  exact hle hc

/-- The subspace-chain inclusion restricted to small chains. -/
def integralSmallSubspaceChains (U : I → Set X) (A : Set X) :
    integralSmallChainComplex (fun i => (Subtype.val : A → X) ⁻¹' U i) ⟶
      integralSmallChainComplex U where
  f n := by
    let V : I → Set A := fun i => (Subtype.val : A → X) ⁻¹' U i
    letI : Module Int (integralSmallChains V n) := (integralSmallChains V n).module
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    exact ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U n)
      (((integralSubspaceChains A).f n).hom.domRestrict (integralSmallChains V n))
      (fun c => integralSubspaceChains_small U A n c.val c.property))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun q => q c.val) ((integralSubspaceChains A).comm i j)

theorem integralSmallSubspaceChains_inclusion (U : I → Set X) (A : Set X) :
    (CategoryStruct.comp (integralSmallSubspaceChains U A ) ( integralSmallChainInclusion U)) =
      (CategoryStruct.comp (integralSmallChainInclusion (fun i => (Subtype.val : A → X) ⁻¹' U i) ) (
        integralSubspaceChains A)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

theorem integralSmallSubspaceChains_mono (U : I → Set X) (A : Set X) :
    Mono (integralSmallSubspaceChains U A) := by
  let : Mono (integralSubspaceChains A) := integralSubspaceChains_mono A
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  apply Subtype.ext
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains A).f n)).mp inferInstance
  exact congrArg Subtype.val h

/-- The actual cokernel complex of small chains of the subspace. -/
abbrev integralSmallRelativeChains (U : I → Set X) (A : Set X) :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralSmallSubspaceChains U A)

abbrev integralSmallRelativeProjection (U : I → Set X) (A : Set X) :
    integralSmallChainComplex U ⟶ integralSmallRelativeChains U A :=
  cokernel.π (integralSmallSubspaceChains U A)

/-- The canonical relative comparison induced by the two small-chain inclusions. -/
def integralSmallRelativeComparison (U : I → Set X) (A : Set X) :
    integralSmallRelativeChains U A ⟶ integralRelativeChains A :=
  cokernel.map (integralSmallSubspaceChains U A) (integralSubspaceChains A)
    (integralSmallChainInclusion (fun i => (Subtype.val : A → X) ⁻¹' U i))
    (integralSmallChainInclusion U) (integralSmallSubspaceChains_inclusion U A)

theorem integralSmallRelativeComparison_projection (U : I → Set X) (A : Set X) :
    (CategoryStruct.comp (integralSmallRelativeProjection U A ) ( integralSmallRelativeComparison U A)) =
      (CategoryStruct.comp (integralSmallChainInclusion U ) ( integralRelativeProjection A)) :=
  cokernel.π_desc _ _ _

/-- Small relative chains compute relative integral homology for every open cover. -/
theorem integralSmallRelativeComparison_quasiIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (A : Set X) :
    QuasiIso (integralSmallRelativeComparison U A) := by
  let V : I → Set A := fun i => (Subtype.val : A → X) ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage continuous_subtype_val
  have hcoverV : (⋃ i, V i) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro a
    have ha : a.val ∈ ⋃ i, U i := by rw [hcover]; exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  let S := ShortComplex.cokernelSequence (integralSmallSubspaceChains U A)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := integralSmallSubspaceChains_mono U A }
  let φ : S ⟶ integralPairSequence A :=
    { τ₁ := integralSmallChainInclusion V
      τ₂ := integralSmallChainInclusion U
      τ₃ := integralSmallRelativeComparison U A
      comm₁₂ := integralSmallSubspaceChains_inclusion U A
      comm₂₃ := (integralSmallRelativeComparison_projection U A).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS
    (integralPairSequence_shortExact A)
    (integralSmallChainInclusion_quasiIso V hV hcoverV)
    (integralSmallChainInclusion_quasiIso U hU hcover)

theorem integralSmallRelativeComparison_homology_isIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (A : Set X) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralSmallRelativeComparison U A) n) := by
  let := integralSmallRelativeComparison_quasiIso U hU hcover A
  infer_instance

end Poincare.Topology

end FzIntegralSmallRelativeChains

noncomputable section FzIntegralExcision

/-!
# Integral singular excision for an open cover

The map of pairs `(B, A intersect B) -> (X, A)` induces an isomorphism when
the two open subspaces cover `X`. The proof identifies its small-chain factor
as a degreewise cokernel isomorphism using singular-simplex support.
-/


open CategoryTheory Limits

universe u

namespace Poincare.Topology

private theorem integralCokernelMap_isIso
    {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) (p : K₁ ⟶ L₁) (q : K₂ ⟶ L₂)
    (w : (CategoryStruct.comp (f ) ( q)) = (CategoryStruct.comp (p ) ( g)))
    (hspan : ∀ (n : Nat) (d : L₂.X n),
      ∃ (b : K₂.X n) (c : L₁.X n), q.f n b + g.f n c = d)
    (hinter : ∀ (n : Nat) (b : K₂.X n),
      q.f n b ∈ LinearMap.range (g.f n).hom → b ∈ LinearMap.range (f.f n).hom) :
    IsIso (cokernel.map f g p q w) := by
  let r := cokernel.map f g p q w
  let πf := cokernel.π f
  let πg := cokernel.π g
  have hπ (n : Nat) : (CategoryStruct.comp (πf.f n ) ( r.f n)) = (CategoryStruct.comp (q.f n ) ( πg.f n)) :=
    congrArg (fun k => k.f n) (cokernel.π_desc f ((CategoryStruct.comp (q ) ( cokernel.π g))) _)
  have hker {C D : ChainComplex (ModuleCat.{u} Int) Nat} (k : C ⟶ D)
      (n : Nat) (d : D.X n) :
      (cokernel.π k).f n d = 0 ↔ d ∈ LinearMap.range (k.f n).hom := by
    constructor
    · intro hd
      exact (ShortComplex.moduleCat_exact_iff _).mp
        ((ShortComplex.cokernelSequence_exact k).map
          (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)) d hd
    · rintro ⟨c, rfl⟩
      exact congrArg (fun h => h.f n c) (cokernel.condition k)
  have hdeg (n : Nat) : IsIso (r.f n) := by
    have hinj : Function.Injective (r.f n) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro y hy
      obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (πf.f n)).mp inferInstance y
      have hqb : πg.f n (q.f n b) = 0 := by
        have he := congrArg (fun k => k b) (hπ n)
        change r.f n (πf.f n b) = πg.f n (q.f n b) at he
        exact he.symm.trans (by rw [hb]; exact hy)
      exact hb.symm.trans ((hker f n b).mpr (hinter n b ((hker g n _).mp hqb)))
    have hsurj : Function.Surjective (r.f n) := by
      intro y
      obtain ⟨d, hd⟩ := (ModuleCat.epi_iff_surjective (πg.f n)).mp inferInstance y
      obtain ⟨b, c, hbc⟩ := hspan n d
      refine ⟨πf.f n b, ?_⟩
      calc
        r.f n (πf.f n b) = πg.f n (q.f n b) :=
          congrArg (fun k => k b) (hπ n)
        _ = πg.f n (q.f n b + g.f n c) := by
          rw [map_add, (hker g n _).mpr ⟨c, rfl⟩, add_zero]
        _ = y := by rw [hbc, hd]
    let : Mono (r.f n) := (ModuleCat.mono_iff_injective _).mpr hinj
    let : Epi (r.f n) := (ModuleCat.epi_iff_surjective _).mpr hsurj
    exact isIso_of_mono_of_epi _
  let := hdeg
  exact HomologicalComplex.Hom.isIso_of_components _

variable {X : Type u} [TopologicalSpace X]

/-- The canonical excision map for a two-member open cover is an integral
homology isomorphism, including degree zero. -/
theorem integral_open_cover_excision
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap
      (integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
        (A := (Subtype.val : B → X) ⁻¹' A) (B := A) (fun _ hb => hb)) n) := by
  let U : Bool → Set X := fun b => if b then A else B
  let UA : Bool → Set A := fun b => (Subtype.val : A → X) ⁻¹' U b
  let UB : Bool → Set B := fun b => (Subtype.val : B → X) ⁻¹' U b
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  have hUA : UA true = Set.univ := by
    ext a
    exact ⟨fun _ => Set.mem_univ _, fun _ => a.property⟩
  have hUB : UB false = Set.univ := by
    ext b
    exact ⟨fun _ => Set.mem_univ _, fun _ => b.property⟩
  let jA := integralSmallChainInclusion UA
  let jB := integralSmallChainInclusion UB
  let j := integralSmallChainInclusion U
  let : IsIso jA := integralSmallChainInclusion_isIso_of_univ UA true hUA
  let : IsIso jB := integralSmallChainInclusion_isIso_of_univ UB false hUB
  let f := integralSubspaceChains AB
  let g := integralSmallSubspaceChains U A
  let q := (CategoryStruct.comp (inv jB ) ( integralSmallSubspaceChains U B))
  let a : C(AB, A) := ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let t := integralChainsFunctor.map (TopCat.ofHom a)
  let p := (CategoryStruct.comp (t ) ( inv jA))
  have hg : (CategoryStruct.comp (g ) ( j)) = (CategoryStruct.comp (jA ) ( integralSubspaceChains A)) :=
    integralSmallSubspaceChains_inclusion U A
  have hq : (CategoryStruct.comp (q ) ( j)) = integralSubspaceChains B := by
    dsimp only [q]
    rw [Category.assoc, integralSmallSubspaceChains_inclusion U B,
      ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have ht : (CategoryStruct.comp (f ) ( integralSubspaceChains B)) = (CategoryStruct.comp (t ) ( integralSubspaceChains A)) := by
    change (CategoryStruct.comp (integralChainsFunctor.map _ ) ( integralChainsFunctor.map _)) =
      (CategoryStruct.comp (integralChainsFunctor.map _ ) ( integralChainsFunctor.map _))
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have w : (CategoryStruct.comp (f ) ( q)) = (CategoryStruct.comp (p ) ( g)) := by
    let : Mono j := integralSmallChainInclusion_mono U
    apply (cancel_mono j).mp
    rw [Category.assoc, hq, Category.assoc, hg]
    dsimp only [p]
    rw [Category.assoc, ← Category.assoc (inv jA), IsIso.inv_hom_id,
      Category.id_comp, ht]
  let r := cokernel.map f g p q w
  have hqval (m : Nat) (b : (integralChains B).X m) :
      j.f m (q.f m b) = (integralSubspaceChains B).f m b :=
    congrArg (fun k => k.f m b) hq
  have hgval (m : Nat) (a' : (integralSmallChainComplex UA).X m) :
      j.f m (g.f m a') = (integralSubspaceChains A).f m (jA.f m a') :=
    congrArg (fun k => k.f m a') hg
  have hspan (m : Nat) (d : (integralSmallChainComplex U).X m) :
      ∃ (b : (integralChains B).X m) (c : (integralSmallChainComplex UA).X m),
        q.f m b + g.f m c = d := by
    have hd : d.val ∈ LinearMap.range ((integralSubspaceChains A).f m).hom ⊔
        LinearMap.range ((integralSubspaceChains B).f m).hom := by
      rw [← integralSmallChains_two_eq_sup A B m]
      exact d.property
    obtain ⟨x, ⟨a', rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hd
    refine ⟨b, (inv jA).f m a', ?_⟩
    apply Subtype.ext
    change j.f m (q.f m b) + j.f m (g.f m ((inv jA).f m a')) = d.val
    rw [hqval, hgval]
    have hja : jA.f m ((inv jA).f m a') = a' :=
      congrArg (fun k => k.f m a') (IsIso.inv_hom_id jA)
    rw [hja]
    exact (add_comm _ _).trans hab
  have hinter (m : Nat) (b : (integralChains B).X m)
      (hb : q.f m b ∈ LinearMap.range (g.f m).hom) :
      b ∈ LinearMap.range (f.f m).hom := by
    apply (integralSubspaceChains_range_preimage A B m b).mp
    obtain ⟨a', ha'⟩ := hb
    refine ⟨jA.f m a', ?_⟩
    have he := congrArg (j.f m) ha'
    rw [hgval, hqval] at he
    exact he
  let : IsIso r := integralCokernelMap_isIso f g p q w hspan hinter
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · exact hB
    · exact hA
  have hcoverU : (⋃ b, U b) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; exact Set.mem_univ _
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  let c := integralSmallRelativeComparison U A
  have hr : (CategoryStruct.comp (integralRelativeProjection AB ) ( r)) = (CategoryStruct.comp (q ) ( integralSmallRelativeProjection U A)) :=
    cokernel.π_desc _ _ _
  have hfactor : (CategoryStruct.comp (r ) ( c)) = integralRelativeMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      (A := AB) (B := A) (fun _ hb => hb) := by
    apply (cancel_epi (integralRelativeProjection AB)).mp
    rw [← Category.assoc, hr, Category.assoc,
      integralSmallRelativeComparison_projection, ← Category.assoc, hq]
    exact (integralRelativeMap_projection
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      (A := AB) (B := A) (fun _ hb => hb)).symm
  let : IsIso (HomologicalComplex.homologyMap c n) :=
    integralSmallRelativeComparison_homology_isIso U hU hcoverU A n
  rw [← hfactor, HomologicalComplex.homologyMap_comp]
  infer_instance

end Poincare.Topology

end FzIntegralExcision

noncomputable section CoeffBridge

open CategoryTheory Limits AlgebraicTopology
namespace IntegralComparison
abbrev U := forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}
abbrev R := ModuleCat.of ℤ (ULift.{0} ℤ)
abbrev coeff : U.obj R ≅ AddCommGrpCat.of ℤ := (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddCommGrpIso

def freeIso : sigmaConst.{0}.obj (U.obj R) ≅ sigmaConst.obj R ⋙ U := by
  refine NatIso.ofComponents (fun I => (PreservesCoproduct.iso U (fun _ : I => R)).symm) ?_
  intro I J f
  apply Sigma.hom_ext
  intro i
  change (CategoryStruct.comp (Sigma.ι _ i) (CategoryStruct.comp (Sigma.map' f (fun _ => 𝟙 _))
    (sigmaComparison U (fun _ : J => R)))) = CategoryStruct.comp (Sigma.ι _ i)
    (CategoryStruct.comp (sigmaComparison U (fun _ : I => R)) (U.map (Sigma.map' f (fun _ => 𝟙 _))))
  rw [Sigma.ι_comp_map'_assoc, Category.id_comp, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc,
    ← U.map_comp, Sigma.ι_comp_map', Category.id_comp]

abbrev C := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
abbrev D := (singularChainComplexFunctor (ModuleCat ℤ)).obj R
abbrev F := U.mapHomologicalComplex (ComplexShape.down ℕ)

def singularIso : C ≅ D ⋙ F := by
  let e := (SimplicialObject.whiskering _ _).mapIso freeIso
  let a := Functor.isoWhiskerLeft TopCat.toSSet
    (Functor.isoWhiskerRight e (alternatingFaceMapComplex AddCommGrpCat))
  let q := Functor.isoWhiskerLeft
    (TopCat.toSSet ⋙ (SimplicialObject.whiskering _ _).obj (sigmaConst.obj R))
    (eqToIso (map_alternatingFaceMapComplex U)).symm
  exact (singularChainComplexFunctor AddCommGrpCat).mapIso coeff.symm ≪≫ a ≪≫ q

def cokerIso : F.mapArrow ⋙ (coker _) ≅ (coker _) ⋙ F := by
  refine NatIso.ofComponents (fun i => (PreservesCokernel.iso F i.hom).symm) ?_
  intro i j s
  exact cokernel_map_comp_cokernelComparison i.hom F j.hom s.left s.right s.w.symm

def relativeIso : C.mapArrow ⋙ (coker _) ≅ (D.mapArrow ⋙ (coker _)) ⋙ F :=
  Functor.isoWhiskerRight ((Functor.mapArrowFunctor _ _).mapIso singularIso) (coker _) ≪≫
    Functor.isoWhiskerLeft D.mapArrow cokerIso

theorem relative_transfer {a b : Arrow TopCat.{0}} (f : a ⟶ b) (n : ℕ)
    (h : IsIso (HomologicalComplex.homologyMap ((D.mapArrow ⋙ (coker _)).map f) n)) :
    IsIso (HomologicalComplex.homologyMap ((C.mapArrow ⋙ (coker _)).map f) n) := by
  let e := Functor.isoWhiskerRight relativeIso (HomologicalComplex.homologyFunctor _ _ n)
  apply (NatIso.isIso_map_iff e f).mpr
  let : QuasiIsoAt ((D.mapArrow ⋙ (coker _)).map f) n :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mpr h
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
    (HomologicalComplex.quasiIsoAt_map_of_preservesHomology ((D.mapArrow ⋙ (coker _)).map f) U n)

end IntegralComparison
end CoeffBridge

open CategoryTheory Limits Poincare.Topology
open scoped ContinuousMap

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro X space A B n hA hB cover
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let i : TopCat.of AB ⟶ TopCat.of B := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let j : TopCat.of A ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let f : TopCat.of AB ⟶ TopCat.of A := TopCat.ofHom ⟨fun x => ⟨x.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let g : TopCat.of B ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let s : Arrow.mk i ⟶ Arrow.mk j := Arrow.homMk' f g (by rfl)
  exact IntegralComparison.relative_transfer s n (integral_open_cover_excision A B hA hB cover n)
