import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
import Mathlib

/-!
Top homology of noncompact connected manifolds, using singular subdivision, excision and compact support detection.
Adapted from the PoincareLib contributors, LehengChen/PoincareConjecture at
60de1a94ca7038d04ed123b490a3229f8aa5fa75, via frenzymath/Poincare-Conjecture at
432c38f2aa5a30efb13871292d17b4a3309a496a and its byte-identical PoincareLib
delivery in frenzymath/PoincareConjecture at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
Licensed under Apache-2.0. Copyright (c) 2026 The PoincareLib contributors.
The original module names are preserved in section headings. This adaptation makes
category composition explicit, combines the modules, transports the module-valued
homology to abelian groups, and proves pointwise vanishing by chart-supported homotopies. The proof generalizes the sphere calculation and compact support arguments to all dimensions at least two.
-/

noncomputable section FzIntegralRelativeChains

/-!
# Actual integral relative singular chains

Relative chains are the cokernel of the actual subspace-chain inclusion.
The coefficient object and all topological spaces retain the same universe.
Homotopies of pairs descend the natural singular prism through these cokernels.
-/


section
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
end 

end FzIntegralRelativeChains

noncomputable section FzIntegralChainCoordinates

/-!
# Coordinates of actual integral singular chains

The coproduct coordinates are indexed by continuous maps from the standard
simplex. Subspace chains correspond to the coordinates whose entire simplex
image lies in the subspace. The resulting splitting is degreewise.
-/


section
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
end 

end FzIntegralChainCoordinates

noncomputable section FzIntegralSmallChains

/-!
# Small integral singular chains

Small chains are the integer span of singular simplices whose entire image
lies in one member of the supplied family. The differential and inclusion
are restrictions of the actual singular-chain maps.
-/


section
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
end 

end FzIntegralSmallChains

noncomputable section FzIntegralChainSupport

/-!
# Support of integral singular chains

These identities express the sum and intersection used in singular excision
in the actual free modules on continuous singular simplices.
-/


section
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
end 

end FzIntegralChainSupport

noncomputable section FzIntegralOrderedChains

/-!
# Integral chains on ordered vertex tuples

The index counts vertices. The empty tuple supplies the auxiliary
augmentation used by the cone formula and the finite subdivision recursion.
-/


section
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
end 

end FzIntegralOrderedChains

noncomputable section FzIntegralOrderedSubdivision

/-!
# Subdivision and prism on ordered integral chains

Both maps use the augmented vertex-count grading. Their recursions require
only a center of each nonempty tuple; geometric properties of the center
are explicit hypotheses of the naturality and support statements.
-/


section
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
end 

end FzIntegralOrderedSubdivision

noncomputable section FzIntegralSimplexSubdivisionGeometry

/-!
# Geometry of integral simplex subdivision

The mean and affine maps use the ambient real coordinates of the actual
standard simplex. The mesh estimates concern every supported ordered tuple,
including repeated vertices and zero-dimensional simplices.
-/


section
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
end 

end FzIntegralSimplexSubdivisionGeometry

noncomputable section FzIntegralTupleRealization

/-!
# Realization of ordered tuples in actual integral singular chains

Each tuple realizes as its affine singular simplex. Integer linear
extension preserves boundaries, affine changes of model and small support.
-/


section
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
end 

end FzIntegralTupleRealization

noncomputable section FzIntegralSubdivision

/-!
# Barycentric subdivision of actual integral singular chains

The signed ordered operators are realized on each singular simplex.
Their prism, support bounds and geometric mesh control the actual iterates.
-/


section
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
end 

end FzIntegralSubdivision

noncomputable section FzIntegralSmallHomology

/-!
# Small chains compute integral singular homology

The proof works with elements of the actual cycle and homology modules.
Subdivision provides small representatives, and the subdivision prism turns
an ambient bounding chain into a small bounding chain. This includes degree zero.
-/


section
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
end 

end FzIntegralSmallHomology

noncomputable section FzIntegralSmallRelativeChains

/-!
# Small relative integral chains

The small chains of a pair are the cokernel of the restricted-cover subspace
inclusion. The canonical map to relative singular chains is a quasi-isomorphism.
-/


section
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
end 

end FzIntegralSmallRelativeChains

noncomputable section FzIntegralExcision

/-!
# Integral singular excision for an open cover

The map of pairs `(B, A intersect B) -> (X, A)` induces an isomorphism when
the two open subspaces cover `X`. The proof identifies its small-chain factor
as a degreewise cokernel isomorphism using singular-simplex support.
-/


section
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
end 

end FzIntegralExcision

noncomputable section FzIntegralMayerVietoris

/-!
# Relative Mayer--Vietoris chain algebra

For two subsets `A,B` of a space, this file builds the actual intermediate
quotient

`C(B)/C(A ∩ B) -> C(X)/C(A) -> Q(A,B)`

and the signed map from the two relative complexes into `Q(A,B)`.  The
degreewise exactness is proved from the free singular-chain support
identities.  The subsequent comparison of `Q(A,B)` with the relative complex
of `A ∪ B` is an excision theorem and is deliberately kept separate.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralNestedInclusion {A B : Set X} (h : A ⊆ B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a => ⟨a.val, h a.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def integralNestedChains {A B : Set X} (h : A ⊆ B) :
    integralChains A ⟶ integralChains B :=
  integralChainsFunctor.map (integralNestedInclusion h)

@[simp]
theorem integralNestedChains_subspaceChains {A B : Set X} (h : A ⊆ B) :
    (CategoryStruct.comp (integralNestedChains h ) ( integralSubspaceChains B)) = integralSubspaceChains A := by
  rw [integralNestedChains, integralSubspaceChains, ← integralChainsFunctor.map_comp]
  rfl

abbrev integralNestedQuotient {A B : Set X} (h : A ⊆ B) :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralNestedChains h)

def integralNestedToRelative {A B : Set X} (h : A ⊆ B) :
    integralNestedQuotient h ⟶ integralRelativeChains A :=
  cokernel.desc (integralNestedChains h)
    ((CategoryStruct.comp (integralSubspaceChains B ) ( integralRelativeProjection A))) (by
      rw [← Category.assoc, integralNestedChains_subspaceChains,
        cokernel.condition])

@[simp]
theorem integralNestedToRelative_projection {A B : Set X} (h : A ⊆ B) :
    (CategoryStruct.comp (cokernel.π (integralNestedChains h) ) ( integralNestedToRelative h)) =
      (CategoryStruct.comp (integralSubspaceChains B ) ( integralRelativeProjection A)) :=
  cokernel.π_desc _ _ _

def integralRelativeRestriction {A B : Set X} (h : A ⊆ B) :
    integralRelativeChains A ⟶ integralRelativeChains B :=
  integralRelativeMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) A B from
    fun ⦃x⦄ hx => by rw [ContinuousMap.id_apply]; exact h hx)

@[simp]
theorem integralRelativeRestriction_projection {A B : Set X} (h : A ⊆ B) :
    (CategoryStruct.comp (integralRelativeProjection A ) ( integralRelativeRestriction h)) =
      integralRelativeProjection B := by
  change (CategoryStruct.comp (integralRelativeProjection A ) (
    integralRelativeMap (ContinuousMap.id X) _)) = integralRelativeProjection B
  have hm := integralRelativeMap_projection (ContinuousMap.id X)
    (A := A) (B := B)
    (show Set.MapsTo (ContinuousMap.id X) A B from
      fun ⦃x⦄ hx => by rw [ContinuousMap.id_apply]; exact h hx)
  rw [hm]
  change (CategoryStruct.comp (integralChainsFunctor.map (𝟙 (TopCat.of X)) ) ( integralRelativeProjection B)) = _
  simp

def integralPairInclusion (A B : Set X) :
    integralRelativeChains ((Subtype.val : B → X) ⁻¹' A) ⟶
      integralRelativeChains A :=
  integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := (Subtype.val : B → X) ⁻¹' A) (B := A)
      (show Set.MapsTo (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
        ((Subtype.val : B → X) ⁻¹' A) A from fun ⦃x⦄ hx => by exact hx)

@[simp]
theorem integralPairInclusion_projection (A B : Set X) :
    (CategoryStruct.comp (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A) ) (
        integralPairInclusion A B)) =
      (CategoryStruct.comp (integralSubspaceChains B ) ( integralRelativeProjection A)) := by
  change (CategoryStruct.comp (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A) ) (
    integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)) _)) = _
  have hm := integralRelativeMap_projection
    (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := (Subtype.val : B → X) ⁻¹' A) (B := A)
    (show Set.MapsTo (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      ((Subtype.val : B → X) ⁻¹' A) A from fun ⦃x⦄ hx => by exact hx)
  rw [hm]
  rfl

abbrev integralSumQuotient (A B : Set X) :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralPairInclusion A B)

abbrev integralSumProjection (A B : Set X) :
    integralRelativeChains A ⟶ integralSumQuotient A B :=
  cokernel.π (integralPairInclusion A B)

def integralSumAmbientProjection (A B : Set X) :
    integralChains X ⟶ integralSumQuotient A B :=
  (CategoryStruct.comp (integralRelativeProjection A ) ( integralSumProjection A B))

@[simp]
theorem integralSubspace_sumAmbientProjection_left (A B : Set X) :
    (CategoryStruct.comp (integralSubspaceChains A ) ( integralSumAmbientProjection A B)) = 0 := by
  simp [integralSumAmbientProjection, ← Category.assoc]

@[simp]
theorem integralSubspace_sumAmbientProjection_right (A B : Set X) :
    (CategoryStruct.comp (integralSubspaceChains B ) ( integralSumAmbientProjection A B)) = 0 := by
  rw [integralSumAmbientProjection, ← Category.assoc,
    ← integralPairInclusion_projection, Category.assoc,
    cokernel.condition, comp_zero]

theorem integralProjection_surjective {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : C ⟶ D) (n : Nat) :
    Function.Surjective ((cokernel.π f).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem integralProjection_eq_zero_iff
    {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : C ⟶ D) (n : Nat) (x : D.X n) :
    (cokernel.π f).f n x = 0 ↔ ∃ y, f.f n y = x := by
  have h := (ShortComplex.cokernelSequence_exact f).map
    (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).mp h x
  · rintro ⟨y, rfl⟩
    exact congrArg (fun q => q.f n y) (cokernel.condition f)

theorem integralPairInclusion_injective (A B : Set X) (n : Nat) :
    Function.Injective ((integralPairInclusion A B).f n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨b, rfl⟩ := integralProjection_surjective
    (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) n x
  have hn := congrArg (fun f => f.f n b) (integralPairInclusion_projection A B)
  change (integralPairInclusion A B).f n
      ((integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A)).f n b) =
    (integralRelativeProjection A).f n ((integralSubspaceChains B).f n b) at hn
  rw [hn] at hx
  obtain ⟨a, ha⟩ := (integralProjection_eq_zero_iff
    (integralSubspaceChains A) n _).mp hx
  have hb : (integralSubspaceChains B).f n b ∈
      LinearMap.range ((integralSubspaceChains A).f n).hom := ⟨a, ha⟩
  have hb' : b ∈ LinearMap.range
      ((integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)).f n).hom :=
    (integralSubspaceChains_range_preimage A B n b).mp hb
  exact (integralProjection_eq_zero_iff
    (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) n _).mpr hb'

instance integralPairInclusion_mono (A B : Set X) :
    Mono (integralPairInclusion A B) :=
  HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).mpr (integralPairInclusion_injective A B n))

theorem integralSumAmbientProjection_eq_zero_iff (A B : Set X) (n : Nat)
    (x : (integralChains X).X n) :
    (integralSumAmbientProjection A B).f n x = 0 ↔
      ∃ a : (integralChains A).X n, ∃ b : (integralChains B).X n,
        x = (integralSubspaceChains A).f n a +
          (integralSubspaceChains B).f n b := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (integralProjection_eq_zero_iff
      (integralPairInclusion A B) n _).mp hx
    obtain ⟨b, rfl⟩ := integralProjection_surjective
      (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) n y
    have hn := congrArg (fun f => f.f n b) (integralPairInclusion_projection A B)
    change (integralPairInclusion A B).f n
        ((integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A)).f n b) =
      (integralRelativeProjection A).f n ((integralSubspaceChains B).f n b) at hn
    rw [hn] at hy
    have hz : (integralRelativeProjection A).f n
        (x - (integralSubspaceChains B).f n b) = 0 := by
      rw [map_sub, hy]
      exact sub_self _
    obtain ⟨a, ha⟩ := (integralProjection_eq_zero_iff
      (integralSubspaceChains A) n _).mp hz
    exact ⟨a, b, (sub_eq_iff_eq_add.mp ha.symm)⟩
  · rintro ⟨a, b, rfl⟩
    rw [map_add]
    have ha := congrArg (fun f => f.f n a)
      (integralSubspace_sumAmbientProjection_left A B)
    have hb := congrArg (fun f => f.f n b)
      (integralSubspace_sumAmbientProjection_right A B)
    exact (congrArg₂ (· + ·) ha hb).trans (zero_add 0)

def integralSumRightProjection (A B : Set X) :
    integralRelativeChains B ⟶ integralSumQuotient A B :=
  cokernel.desc (integralSubspaceChains B) (integralSumAmbientProjection A B)
    (integralSubspace_sumAmbientProjection_right A B)

@[simp]
theorem integralProjection_sumRightProjection (A B : Set X) :
    (CategoryStruct.comp (integralRelativeProjection B ) ( integralSumRightProjection A B)) =
      integralSumAmbientProjection A B :=
  cokernel.π_desc _ _ _

def integralUnionRestriction (A B : Set X) :
    integralRelativeChains (A ∩ B) ⟶
      integralRelativeChains A ⊞ integralRelativeChains B :=
  biprod.lift
    (integralRelativeRestriction (Set.inter_subset_left : A ∩ B ⊆ A))
    (integralRelativeRestriction (Set.inter_subset_right : A ∩ B ⊆ B))

def integralSumDifference (A B : Set X) :
    integralRelativeChains A ⊞ integralRelativeChains B ⟶
      integralSumQuotient A B :=
  biprod.desc (integralSumProjection A B) (-integralSumRightProjection A B)

theorem integralUnionRestriction_sumDifference (A B : Set X) :
    (CategoryStruct.comp (integralUnionRestriction A B ) ( integralSumDifference A B)) = 0 := by
  rw [integralUnionRestriction, integralSumDifference, biprod.lift_desc,
    Preadditive.comp_neg, ← sub_eq_add_neg]
  apply sub_eq_zero.mpr
  apply (cancel_epi (integralRelativeProjection (A ∩ B))).mp
  simp only [← Category.assoc, integralRelativeRestriction_projection,
    integralProjection_sumRightProjection]
  rfl

def integralRelativeMayerVietoris (A B : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralUnionRestriction A B) (integralSumDifference A B)
    (integralUnionRestriction_sumDifference A B)

theorem integralBiprod_component_ext {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    {n : Nat} {x y : (C ⊞ D).X n}
    (h₁ : (biprod.fst : C ⊞ D ⟶ C).f n x =
      (biprod.fst : C ⊞ D ⟶ C).f n y)
    (h₂ : (biprod.snd : C ⊞ D ⟶ D).f n x =
      (biprod.snd : C ⊞ D ⟶ D).f n y) :
    x = y := by
  have ht (z : (C ⊞ D).X n) := congrArg (fun f => f z) (biprod_total_f C D n)
  exact (ht x).symm.trans ((congrArg₂ (· + ·)
    (congrArg ((biprod.inl : C ⟶ C ⊞ D).f n) h₁)
    (congrArg ((biprod.inr : D ⟶ C ⊞ D).f n) h₂)).trans (ht y))

theorem integralSumDifference_apply (A B : Set X) (n : Nat)
    (y : (integralRelativeChains A ⊞ integralRelativeChains B).X n) :
    (integralSumDifference A B).f n y =
      (integralSumProjection A B).f n
        ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
          integralRelativeChains A).f n y) -
      (integralSumRightProjection A B).f n
        ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
          integralRelativeChains B).f n y) := by
  have h : integralSumDifference A B =
      (CategoryStruct.comp (biprod.fst ) ( integralSumProjection A B)) -
        (CategoryStruct.comp (biprod.snd ) ( integralSumRightProjection A B)) := by
    apply biprod.hom_ext' <;> simp [integralSumDifference, Preadditive.comp_sub]
  exact congrArg (fun f => f.f n y) h

theorem integralUnionRestriction_injective (A B : Set X) (n : Nat) :
    Function.Injective ((integralUnionRestriction A B).f n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨c, rfl⟩ := integralProjection_surjective
    (integralSubspaceChains (A ∩ B)) n x
  have hA : (integralRelativeProjection A).f n c = 0 := by
    have h := congrArg (fun f => f.f n c)
      (show (CategoryStruct.comp (integralRelativeProjection (A ∩ B) ) ( (CategoryStruct.comp (integralUnionRestriction A B ) (
        biprod.fst)))) = integralRelativeProjection A by
        rw [integralUnionRestriction, biprod.lift_fst,
          integralRelativeRestriction_projection])
    exact h.symm.trans ((congrArg
      ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains A).f n) hx).trans (map_zero _))
  have hB : (integralRelativeProjection B).f n c = 0 := by
    have h := congrArg (fun f => f.f n c)
      (show (CategoryStruct.comp (integralRelativeProjection (A ∩ B) ) ( (CategoryStruct.comp (integralUnionRestriction A B ) (
        biprod.snd)))) = integralRelativeProjection B by
        rw [integralUnionRestriction, biprod.lift_snd,
          integralRelativeRestriction_projection])
    exact h.symm.trans ((congrArg
      ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains B).f n) hx).trans (map_zero _))
  obtain ⟨a, ha⟩ := (integralProjection_eq_zero_iff
    (integralSubspaceChains A) n _).mp hA
  obtain ⟨b, hb⟩ := (integralProjection_eq_zero_iff
    (integralSubspaceChains B) n _).mp hB
  have hc : c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ⊓
      LinearMap.range ((integralSubspaceChains B).f n).hom :=
    ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [integralSubspaceChains_range_inf] at hc
  exact (integralProjection_eq_zero_iff
    (integralSubspaceChains (A ∩ B)) n c).mpr hc

theorem integralRelativeMayerVietoris_shortExact (A B : Set X) :
    (integralRelativeMayerVietoris A B).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    let y' : (integralRelativeChains A ⊞ integralRelativeChains B).X n := y
    obtain ⟨u, hu⟩ := integralProjection_surjective
      (integralSubspaceChains A) n
      ((biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains A).f n y')
    obtain ⟨v, hv⟩ := integralProjection_surjective
      (integralSubspaceChains B) n
      ((biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains B).f n y')
    have hdiff : (integralSumAmbientProjection A B).f n (u - v) = 0 := by
      change (integralSumDifference A B).f n y' = 0 at hy
      have happly := integralSumDifference_apply A B n y'
      rw [happly, ← hu, ← hv] at hy
      have hA : (integralSumProjection A B).f n
          ((integralRelativeProjection A).f n u) =
          (integralSumAmbientProjection A B).f n u := rfl
      have hB := congrArg (fun f => f.f n v)
        (integralProjection_sumRightProjection A B)
      change (integralSumRightProjection A B).f n
          ((integralRelativeProjection B).f n v) =
        (integralSumAmbientProjection A B).f n v at hB
      rw [map_sub, ← hA, ← hB]
      exact hy
    obtain ⟨a, b, hab⟩ :=
      (integralSumAmbientProjection_eq_zero_iff A B n (u - v)).mp hdiff
    let w := u - (integralSubspaceChains A).f n a
    have hw : w = v + (integralSubspaceChains B).f n b := by
      dsimp [w]
      rw [sub_eq_iff_eq_add.mp hab]
      abel
    refine ⟨(integralRelativeProjection (A ∩ B)).f n w, ?_⟩
    apply integralBiprod_component_ext
    · have h := congrArg (fun f => f.f n w)
        (show (CategoryStruct.comp (integralRelativeProjection (A ∩ B) ) ( (CategoryStruct.comp (integralUnionRestriction A B ) (
          biprod.fst)))) = integralRelativeProjection A by
          rw [integralUnionRestriction, biprod.lift_fst,
            integralRelativeRestriction_projection])
      change (biprod.fst : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains A).f n
        ((integralUnionRestriction A B).f n
          ((integralRelativeProjection (A ∩ B)).f n w)) = _
      refine h.trans ?_
      change (integralRelativeProjection A).f n
        (u - (integralSubspaceChains A).f n a) = _
      rw [map_sub,
        (integralProjection_eq_zero_iff (integralSubspaceChains A) n _).mpr ⟨a, rfl⟩,
        sub_zero, hu]
    · have h := congrArg (fun f => f.f n w)
        (show (CategoryStruct.comp (integralRelativeProjection (A ∩ B) ) ( (CategoryStruct.comp (integralUnionRestriction A B ) (
          biprod.snd)))) = integralRelativeProjection B by
          rw [integralUnionRestriction, biprod.lift_snd,
            integralRelativeRestriction_projection])
      change (biprod.snd : integralRelativeChains A ⊞ integralRelativeChains B ⟶
        integralRelativeChains B).f n
        ((integralUnionRestriction A B).f n
          ((integralRelativeProjection (A ∩ B)).f n w)) = _
      refine h.trans ?_
      rw [hw, map_add,
        (integralProjection_eq_zero_iff (integralSubspaceChains B) n _).mpr ⟨b, rfl⟩,
        add_zero, hv]
  · exact (ModuleCat.mono_iff_injective _).mpr
      (integralUnionRestriction_injective A B n)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨a, rfl⟩ := integralProjection_surjective (integralPairInclusion A B) n z
    refine ⟨(biprod.inl : integralRelativeChains A ⟶ _).f n a, ?_⟩
    exact congrArg (fun f => f.f n a)
      (show (CategoryStruct.comp (biprod.inl ) ( integralSumDifference A B)) = integralSumProjection A B by
        simp [integralSumDifference])

def integralSumComparison (A B : Set X) :
    integralSumQuotient A B ⟶ integralRelativeChains (A ∪ B) :=
  cokernel.desc (integralPairInclusion A B)
    (integralRelativeRestriction (Set.subset_union_left : A ⊆ A ∪ B)) (by
      apply (cancel_epi
        (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
      rw [← Category.assoc, integralPairInclusion_projection, Category.assoc,
        integralRelativeRestriction_projection,
        ← integralNestedChains_subspaceChains
          (Set.subset_union_right : B ⊆ A ∪ B), Category.assoc,
        cokernel.condition]
      simp
    )

@[simp]
theorem integralSumProjection_comparison (A B : Set X) :
    (CategoryStruct.comp (integralSumProjection A B ) ( integralSumComparison A B)) =
      integralRelativeRestriction (Set.subset_union_left : A ⊆ A ∪ B) :=
  cokernel.π_desc _ _ _

end Poincare.Topology
end 

end FzIntegralMayerVietoris

noncomputable section FzIntegralMayerVietorisExcision

/-!
# The nested relative short exact sequence

For `A ⊆ B ⊆ X`, the actual relative chains of `B` modulo the chains in `A`
map into `C(X)/C(A)`, followed by the identity-induced map to `C(X)/C(B)`.
This sequence is proved degreewise from singular-chain representatives.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralNestedRelativePairSequence (A B : Set X) (h : A ⊆ B) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralPairInclusion A B) (integralRelativeRestriction h)
    (by
      apply (cancel_epi
        (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
      rw [← Category.assoc, integralPairInclusion_projection, Category.assoc,
        integralRelativeRestriction_projection,
        cokernel.condition]
      simp)

theorem integralNestedRelativePairSequence_shortExact
    (A B : Set X) (h : A ⊆ B) :
    (integralNestedRelativePairSequence A B h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    obtain ⟨c, hc⟩ := integralProjection_surjective
      (integralSubspaceChains A) n y
    have hz : (integralRelativeProjection B).f n c = 0 := by
      have hp := congrArg (fun f => f.f n c)
        (integralRelativeRestriction_projection h)
      change (integralRelativeRestriction h).f n
          ((integralRelativeProjection A).f n c) =
        (integralRelativeProjection B).f n c at hp
      rw [hc] at hp
      exact hp.symm.trans (by
        change (integralRelativeRestriction h).f n y = 0 at hy
        exact hy)
    obtain ⟨b, hb⟩ := (integralProjection_eq_zero_iff
      (integralSubspaceChains B) n c).mp hz
    refine ⟨(integralRelativeProjection
      ((Subtype.val : B → X) ⁻¹' A)).f n b, ?_⟩
    · have hp := congrArg (fun f => f.f n b)
        (integralPairInclusion_projection A B)
      change (integralPairInclusion A B).f n
          ((integralRelativeProjection
            ((Subtype.val : B → X) ⁻¹' A)).f n b) = y
      change (integralPairInclusion A B).f n
          ((integralRelativeProjection
            ((Subtype.val : B → X) ⁻¹' A)).f n b) =
        (integralRelativeProjection A).f n ((integralSubspaceChains B).f n b) at hp
      rw [hp, hb]
      exact hc
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact integralPairInclusion_injective A B n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    obtain ⟨c, hc⟩ := integralProjection_surjective
      (integralSubspaceChains B) n y
    refine ⟨(integralRelativeProjection A).f n c, ?_⟩
    have hp := congrArg (fun f => f.f n c)
      (integralRelativeRestriction_projection h)
    change (integralRelativeRestriction h).f n
        ((integralRelativeProjection A).f n c) =
      (integralRelativeProjection B).f n c at hp
    exact hp.trans hc

def integralUnionMemberHomeomorph (A B : Set X) :
    B ≃ₜ ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) where
  toFun b := ⟨⟨b.val, Or.inr b.property⟩, b.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def integralUnionIntersectionHomeomorph (A B : Set X) :
    ((Subtype.val : B → X) ⁻¹' A) ≃ₜ
      ((Subtype.val : ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) → ↥(A ∪ B)) ⁻¹'
        ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A)) where
  toFun a := ⟨integralUnionMemberHomeomorph A B a.val, a.property⟩
  invFun a := ⟨(integralUnionMemberHomeomorph A B).symm a.val, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((integralUnionMemberHomeomorph A B).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((integralUnionMemberHomeomorph A B).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

def integralUnionExcisionSourceIso (A B : Set X) :
    integralRelativeChains ((Subtype.val : B → X) ⁻¹' A) ≅
      integralRelativeChains
        ((Subtype.val : ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) → ↥(A ∪ B)) ⁻¹'
          ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A)) :=
  cokernel.mapIso _ _
    (integralChainsFunctor.mapIso
      (TopCat.isoOfHomeo (integralUnionIntersectionHomeomorph A B)))
    (integralChainsFunctor.mapIso
      (TopCat.isoOfHomeo (integralUnionMemberHomeomorph A B))) (by
      simp only [Functor.mapIso_hom, integralSubspaceChains, ← Functor.map_comp]
      rfl)

def integralUnionLeftComparison (A B : Set X) :
    integralRelativeChains ((Subtype.val : B → X) ⁻¹' A) ⟶
      integralRelativeChains ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) :=
  integralRelativeMap
    (⟨fun b => ⟨b.val, Or.inr b.property⟩,
      continuous_subtype_val.subtype_mk _⟩ : C(B, ↥(A ∪ B)))
    (show Set.MapsTo _ ((Subtype.val : B → X) ⁻¹' A)
      ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) from fun _ hx => hx)

@[simp]
theorem integralUnionLeftComparison_projection (A B : Set X) :
    (CategoryStruct.comp (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A) ) (
      integralUnionLeftComparison A B)) =
        (CategoryStruct.comp (integralNestedChains (Set.subset_union_right : B ⊆ A ∪ B) ) (
          integralRelativeProjection ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A))) := by
  exact integralRelativeMap_projection _ _

theorem integralUnionLeftComparison_toRelative (A B : Set X) :
    (CategoryStruct.comp (integralUnionLeftComparison A B ) ( integralPairInclusion A (A ∪ B))) =
      integralPairInclusion A B := by
  apply (cancel_epi (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
  rw [← Category.assoc, integralUnionLeftComparison_projection,
    Category.assoc, integralPairInclusion_projection,
    ← Category.assoc, integralNestedChains_subspaceChains,
    integralPairInclusion_projection]

theorem integralUnionLeftComparison_homology_isIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralUnionLeftComparison A B) n) := by
  let UA : Set ↥(A ∪ B) := (Subtype.val : ↥(A ∪ B) → X) ⁻¹' A
  let UB : Set ↥(A ∪ B) := (Subtype.val : ↥(A ∪ B) → X) ⁻¹' B
  let e := integralPairInclusion UA UB
  have hcover : UA ∪ UB = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact x.property
  let : IsIso (HomologicalComplex.homologyMap e n) :=
    integral_open_cover_excision UA UB (hA.preimage continuous_subtype_val)
      (hB.preimage continuous_subtype_val) hcover n
  have hfactor : (CategoryStruct.comp ((integralUnionExcisionSourceIso A B).hom ) ( e)) =
      integralUnionLeftComparison A B := by
    apply (cancel_epi
      (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
    simp only [integralUnionExcisionSourceIso, cokernel.mapIso_hom, cokernel.map,
      cokernel.π_desc_assoc, Functor.mapIso_hom]
    dsimp only [e, UA, UB]
    rw [Category.assoc, integralPairInclusion_projection,
      integralUnionLeftComparison_projection, ← Category.assoc]
    dsimp only [integralSubspaceChains]
    rw [← integralChainsFunctor.map_comp]
    rfl
  rw [← hfactor, HomologicalComplex.homologyMap_comp]
  infer_instance

def integralSumComparisonDiagram (A B : Set X) :
    ShortComplex.cokernelSequence (integralPairInclusion A B) ⟶
      integralNestedRelativePairSequence A (A ∪ B) Set.subset_union_left where
  τ₁ := integralUnionLeftComparison A B
  τ₂ := 𝟙 _
  τ₃ := integralSumComparison A B
  comm₁₂ := by
    change (CategoryStruct.comp (integralUnionLeftComparison A B ) ( integralPairInclusion A (A ∪ B))) =
      (CategoryStruct.comp (integralPairInclusion A B ) ( 𝟙 _))
    rw [Category.comp_id, integralUnionLeftComparison_toRelative]
  comm₂₃ := by
    change (CategoryStruct.comp (𝟙 _ ) ( integralRelativeRestriction Set.subset_union_left)) =
      (CategoryStruct.comp (integralSumProjection A B ) ( integralSumComparison A B))
    rw [Category.id_comp, integralSumProjection_comparison]

/-- The intermediate quotient computes the relative homology of the union. -/
theorem integralSumComparison_quasiIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (integralSumComparison A B) := by
  have hS : (ShortComplex.cokernelSequence (integralPairInclusion A B)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := integralPairInclusion_mono A B }
  have hleft : QuasiIso (integralUnionLeftComparison A B) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact integralUnionLeftComparison_homology_isIso A B hA hB n
  have hid : QuasiIso (𝟙 (integralRelativeChains A)) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (integralSumComparisonDiagram A B) hS
    (integralNestedRelativePairSequence_shortExact A (A ∪ B) Set.subset_union_left)
    hleft hid

theorem integralSumComparison_homology_isIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralSumComparison A B) n) := by
  let := integralSumComparison_quasiIso A B hA hB
  infer_instance

end Poincare.Topology
end 

end FzIntegralMayerVietorisExcision

noncomputable section FzIntegralSupportMayerVietoris

/-!
# Integral relative homology with closed supports

The support restriction maps are induced by the identity of the ambient
space.  The intermediate relative chain sequence and the canonical excision
comparison give the Mayer--Vietoris exactness used to glue support classes.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

abbrev integralSupportChains (K : Set X) := integralRelativeChains Kᶜ

abbrev integralSupportHomology (K : Set X) (n : Nat) :=
  integralRelativeHomology Kᶜ n

def integralSupportRestriction {K L : Set X} (h : K ⊆ L) :
    integralSupportChains L ⟶ integralSupportChains K :=
  integralRelativeRestriction (Set.compl_subset_compl.mpr h)

@[simp]
theorem integralSupportRestriction_projection {K L : Set X} (h : K ⊆ L) :
    (CategoryStruct.comp (integralRelativeProjection Lᶜ ) ( integralSupportRestriction h)) =
      integralRelativeProjection Kᶜ :=
  integralRelativeRestriction_projection _

@[simp]
theorem integralSupportRestriction_comp {K L D : Set X}
    (hKL : K ⊆ L) (hLD : L ⊆ D) :
    (CategoryStruct.comp (integralSupportRestriction hLD ) ( integralSupportRestriction hKL)) =
      integralSupportRestriction (hKL.trans hLD) := by
  apply (cancel_epi (integralRelativeProjection Dᶜ)).mp
  simp only [← Category.assoc, integralSupportRestriction_projection]

def integralSupportHomologyRestriction {K L : Set X} (h : K ⊆ L) (n : Nat) :
    integralSupportHomology L n ⟶ integralSupportHomology K n :=
  homologyMap (integralSupportRestriction h) n

@[simp]
theorem integralSupportHomologyRestriction_comp {K L D : Set X}
    (hKL : K ⊆ L) (hLD : L ⊆ D) (n : Nat) :
    (CategoryStruct.comp (integralSupportHomologyRestriction hLD n ) ( integralSupportHomologyRestriction hKL n)) =
      integralSupportHomologyRestriction (hKL.trans hLD) n := by
  rw [integralSupportHomologyRestriction, integralSupportHomologyRestriction,
    ← homologyMap_comp, integralSupportRestriction_comp]
  rfl

def integralRelativeSetIso {A B : Set X} (h : A = B) :
    integralRelativeChains A ≅ integralRelativeChains B :=
  eqToIso (congrArg integralRelativeChains h)

@[simp]
theorem integralRelativeSetIso_projection {A B : Set X} (h : A = B) :
    (CategoryStruct.comp (integralRelativeProjection A ) ( (integralRelativeSetIso h).hom)) =
      integralRelativeProjection B := by
  subst B
  simp [integralRelativeSetIso]

def integralSupportUnionMap (K L : Set X) :
    integralSupportChains (K ∪ L) ⟶ integralSupportChains K ⊞ integralSupportChains L :=
  biprod.lift (integralSupportRestriction (Set.subset_union_left : K ⊆ K ∪ L))
    (integralSupportRestriction (Set.subset_union_right : L ⊆ K ∪ L))

def integralSupportDifference (K L : Set X) :
    integralSupportChains K ⊞ integralSupportChains L ⟶
      integralSupportChains (K ∩ L) :=
  biprod.desc (integralSupportRestriction (Set.inter_subset_left : K ∩ L ⊆ K))
    (-integralSupportRestriction (Set.inter_subset_right : K ∩ L ⊆ L))

def integralSupportComparison (K L : Set X) :
    integralSumQuotient Kᶜ Lᶜ ⟶ integralSupportChains (K ∩ L) :=
  (CategoryStruct.comp (integralSumComparison Kᶜ Lᶜ ) ( (integralRelativeSetIso (Set.compl_inter K L).symm).hom))

@[simp]
theorem integralSupportComparison_left (K L : Set X) :
    (CategoryStruct.comp (integralSumProjection Kᶜ Lᶜ ) ( integralSupportComparison K L)) =
      integralSupportRestriction (Set.inter_subset_left : K ∩ L ⊆ K) := by
  apply (cancel_epi (integralRelativeProjection Kᶜ)).mp
  simp only [integralSupportComparison, ← Category.assoc,
    integralSumProjection_comparison, integralRelativeRestriction_projection,
    integralRelativeSetIso_projection, integralSupportRestriction_projection]

@[simp]
theorem integralSupportComparison_right (K L : Set X) :
    (CategoryStruct.comp (integralSumRightProjection Kᶜ Lᶜ ) ( integralSupportComparison K L)) =
      integralSupportRestriction (Set.inter_subset_right : K ∩ L ⊆ L) := by
  apply (cancel_epi (integralRelativeProjection Lᶜ)).mp
  rw [← Category.assoc, integralProjection_sumRightProjection,
    integralSumAmbientProjection, Category.assoc, integralSupportComparison_left,
    integralSupportRestriction_projection, integralSupportRestriction_projection]

@[simp]
theorem integralSupportComparison_difference (K L : Set X) :
    (CategoryStruct.comp (integralSumDifference Kᶜ Lᶜ ) ( integralSupportComparison K L)) =
      integralSupportDifference K L := by
  apply biprod.hom_ext'
  · simp [integralSumDifference, integralSupportDifference]
  · simp [integralSumDifference, integralSupportDifference, Preadditive.neg_comp]

def integralSupportIntermediateSequence (K L : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralSupportUnionMap K L) (integralSumDifference Kᶜ Lᶜ) (by
    rw [integralSupportUnionMap, integralSumDifference, biprod.lift_desc,
      Preadditive.comp_neg, ← sub_eq_add_neg]
    apply sub_eq_zero.mpr
    apply (cancel_epi (integralRelativeProjection (K ∪ L)ᶜ)).mp
    simp only [← Category.assoc, integralSupportRestriction_projection,
      integralProjection_sumRightProjection]
    rfl)

def integralSupportIntermediateSequenceIso (K L : Set X) :
    integralRelativeMayerVietoris Kᶜ Lᶜ ≅ integralSupportIntermediateSequence K L :=
  ShortComplex.isoMk (integralRelativeSetIso (Set.compl_union K L).symm)
    (Iso.refl _) (Iso.refl _) (by
      change (CategoryStruct.comp ((integralRelativeSetIso (Set.compl_union K L).symm).hom ) (
          integralSupportUnionMap K L)) = (CategoryStruct.comp (integralUnionRestriction Kᶜ Lᶜ ) ( 𝟙 _))
      rw [Category.comp_id]
      apply (cancel_epi (integralRelativeProjection (Kᶜ ∩ Lᶜ))).mp
      apply biprod.hom_ext
      · simp only [Category.assoc, integralUnionRestriction,
          integralSupportUnionMap, biprod.lift_fst, integralRelativeRestriction_projection]
        rw [← Category.assoc, integralRelativeSetIso_projection,
          integralSupportRestriction_projection]
      · simp only [Category.assoc, integralUnionRestriction,
          integralSupportUnionMap, biprod.lift_snd, integralRelativeRestriction_projection]
        rw [← Category.assoc, integralRelativeSetIso_projection,
          integralSupportRestriction_projection]) (by
      simp [integralSupportIntermediateSequence, integralRelativeMayerVietoris])

theorem integralSupportIntermediateSequence_shortExact (K L : Set X) :
    (integralSupportIntermediateSequence K L).ShortExact :=
  ShortComplex.shortExact_of_iso (integralSupportIntermediateSequenceIso K L)
    (integralRelativeMayerVietoris_shortExact Kᶜ Lᶜ)

def integralSupportIntersectionHomologyIso
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat) :
    (integralSumQuotient Kᶜ Lᶜ).homology n ≅ integralSupportHomology (K ∩ L) n := by
  let : IsIso (homologyMap (integralSumComparison Kᶜ Lᶜ) n) :=
    integralSumComparison_homology_isIso Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n
  exact asIso (homologyMap (integralSumComparison Kᶜ Lᶜ) n) ≪≫
    (homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).mapIso
      (integralRelativeSetIso (Set.compl_inter K L).symm)

theorem integralSupportComparison_homology_isIso
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat) :
    IsIso (homologyMap (integralSupportComparison K L) n) := by
  let : IsIso (homologyMap (integralSumComparison Kᶜ Lᶜ) n) :=
    integralSumComparison_homology_isIso Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n
  rw [integralSupportComparison, homologyMap_comp]
  infer_instance

theorem integralHomologyBiprod_ext
    (C D : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat)
    {a b : (C ⊞ D).homology n}
    (h₁ : homologyMap (biprod.fst : C ⊞ D ⟶ C) n a =
      homologyMap (biprod.fst : C ⊞ D ⟶ C) n b)
    (h₂ : homologyMap (biprod.snd : C ⊞ D ⟶ D) n a =
      homologyMap (biprod.snd : C ⊞ D ⟶ D) n b) : a = b := by
  have ht : (CategoryStruct.comp (homologyMap (biprod.fst : C ⊞ D ⟶ C) n ) ( homologyMap biprod.inl n)) +
      (CategoryStruct.comp (homologyMap (biprod.snd : C ⊞ D ⟶ D) n ) ( homologyMap biprod.inr n)) = 𝟙 _ := by
    rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_add,
      biprod.total, homologyMap_id]
  have he : homologyMap (biprod.inl : C ⟶ C ⊞ D) n
        (homologyMap (biprod.fst : C ⊞ D ⟶ C) n a) +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) n
        (homologyMap (biprod.snd : C ⊞ D ⟶ D) n a) = a :=
    congrArg (fun f => f a) ht
  have hf : homologyMap (biprod.inl : C ⟶ C ⊞ D) n
        (homologyMap (biprod.fst : C ⊞ D ⟶ C) n b) +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) n
        (homologyMap (biprod.snd : C ⊞ D ⟶ D) n b) = b :=
    congrArg (fun f => f b) ht
  rw [h₁, h₂] at he
  exact he.symm.trans hf

@[simp]
theorem integralSupportUnionMap_homology_fst (K L : Set X) (n : Nat) :
    (CategoryStruct.comp (homologyMap (integralSupportUnionMap K L) n ) ( homologyMap biprod.fst n)) =
      integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n := by
  rw [← homologyMap_comp, integralSupportUnionMap, biprod.lift_fst]
  rfl

@[simp]
theorem integralSupportUnionMap_homology_snd (K L : Set X) (n : Nat) :
    (CategoryStruct.comp (homologyMap (integralSupportUnionMap K L) n ) ( homologyMap biprod.snd n)) =
      integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n := by
  rw [← homologyMap_comp, integralSupportUnionMap, biprod.lift_snd]
  rfl

/-- Compatible homology classes on two closed supports have an actual class
on the union, with the prescribed canonical restrictions. -/
theorem exists_integralSupportHomology_union
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (a : integralSupportHomology K n) (b : integralSupportHomology L n)
    (hab : integralSupportHomologyRestriction (Set.inter_subset_left : K ∩ L ⊆ K) n a =
      integralSupportHomologyRestriction (Set.inter_subset_right : K ∩ L ⊆ L) n b) :
    ∃ c : integralSupportHomology (K ∪ L) n,
      integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n c = a ∧
      integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n c = b := by
  let C := integralSupportChains K
  let D := integralSupportChains L
  let v : (C ⊞ D).homology n :=
    homologyMap (biprod.inl : C ⟶ C ⊞ D) n a +
      homologyMap (biprod.inr : D ⟶ C ⊞ D) n b
  have hfst : homologyMap (biprod.fst : C ⊞ D ⟶ C) n v = a := by
    simp [v, ← ConcreteCategory.comp_apply, ← homologyMap_comp]
  have hsnd : homologyMap (biprod.snd : C ⊞ D ⟶ D) n v = b := by
    simp [v, ← ConcreteCategory.comp_apply, ← homologyMap_comp]
  have hv : homologyMap (integralSumDifference Kᶜ Lᶜ) n v = 0 := by
    let := integralSupportComparison_homology_isIso K L hK hL n
    apply (ModuleCat.mono_iff_injective (homologyMap (integralSupportComparison K L) n)).mp
      inferInstance
    rw [map_zero, ← ConcreteCategory.comp_apply, ← homologyMap_comp,
      integralSupportComparison_difference]
    simp only [v, map_add, ← ConcreteCategory.comp_apply, ← homologyMap_comp,
      integralSupportDifference, biprod.inl_desc, biprod.inr_desc, homologyMap_neg]
    change (integralSupportHomologyRestriction (Set.inter_subset_left : K ∩ L ⊆ K) n).hom a +
      (-integralSupportHomologyRestriction (Set.inter_subset_right : K ∩ L ⊆ L) n).hom b = 0
    simpa only [ModuleCat.hom_neg, LinearMap.neg_apply, sub_eq_add_neg] using
      sub_eq_zero.mpr hab
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((integralSupportIntermediateSequence_shortExact K L).homology_exact₂ n) v hv
  change integralSupportHomology (K ∪ L) n at c
  change homologyMap (integralSupportUnionMap K L) n c = v at hc
  refine ⟨c, ?_, ?_⟩
  · have he := congrArg (homologyMap (biprod.fst : C ⊞ D ⟶ C) n) hc
    change homologyMap (biprod.fst : C ⊞ D ⟶ C) n
        (homologyMap (integralSupportUnionMap K L) n c) =
      homologyMap (biprod.fst : C ⊞ D ⟶ C) n v at he
    rw [← ConcreteCategory.comp_apply, integralSupportUnionMap_homology_fst, hfst] at he
    exact he
  · have he := congrArg (homologyMap (biprod.snd : C ⊞ D ⟶ D) n) hc
    change homologyMap (biprod.snd : C ⊞ D ⟶ D) n
        (homologyMap (integralSupportUnionMap K L) n c) =
      homologyMap (biprod.snd : C ⊞ D ⟶ D) n v at he
    rw [← ConcreteCategory.comp_apply, integralSupportUnionMap_homology_snd, hsnd] at he
    exact he

theorem integralSupportUnionMap_homology_mono
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (hI : IsZero (integralSupportHomology (K ∩ L) (n + 1))) :
    Mono (homologyMap (integralSupportUnionMap K L) n) := by
  have hQ : IsZero ((integralSumQuotient Kᶜ Lᶜ).homology (n + 1)) :=
    IsZero.of_iso hI (integralSupportIntersectionHomologyIso K L hK hL (n + 1))
  exact ((integralSupportIntermediateSequence_shortExact K L).homology_exact₁
    (n + 1) n rfl).mono_g (hQ.eq_zero_of_src _)

theorem integralSupportHomology_union_ext
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (hI : IsZero (integralSupportHomology (K ∩ L) (n + 1)))
    {a b : integralSupportHomology (K ∪ L) n}
    (h₁ : integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n a =
      integralSupportHomologyRestriction (Set.subset_union_left : K ⊆ K ∪ L) n b)
    (h₂ : integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n a =
      integralSupportHomologyRestriction (Set.subset_union_right : L ⊆ K ∪ L) n b) : a = b := by
  let := integralSupportUnionMap_homology_mono K L hK hL n hI
  apply (ModuleCat.mono_iff_injective (homologyMap (integralSupportUnionMap K L) n)).mp
    inferInstance
  apply integralHomologyBiprod_ext
  · simpa only [← ConcreteCategory.comp_apply,
      integralSupportUnionMap_homology_fst] using h₁
  · simpa only [← ConcreteCategory.comp_apply,
      integralSupportUnionMap_homology_snd] using h₂

theorem integralSupportHomology_union_isZero
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (n : Nat)
    (hI : IsZero (integralSupportHomology (K ∩ L) (n + 1)))
    (hK₀ : IsZero (integralSupportHomology K n))
    (hL₀ : IsZero (integralSupportHomology L n)) :
    IsZero (integralSupportHomology (K ∪ L) n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => integralSupportHomology_union_ext K L hK hL n hI ?_ ?_⟩
  · exact (ModuleCat.isZero_iff_subsingleton.mp hK₀).elim _ _
  · exact (ModuleCat.isZero_iff_subsingleton.mp hL₀).elim _ _

end Poincare.Topology
end 

end FzIntegralSupportMayerVietoris

noncomputable section FzIntegralChartSupport

/-!
# Transporting integral support homology through an open chart

The chart's source and target homeomorphism gives an isomorphism of actual
relative chain complexes. Open excision compares each of these pairs with
its ambient space. These comparisons commute with support restriction.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralOpenSupportMap (K U : Set X) :
    integralRelativeChains ((Subtype.val : U → X) ⁻¹' Kᶜ) ⟶ integralSupportChains K :=
  integralPairInclusion Kᶜ U

theorem integralOpenSupportMap_homology_isIso
    (K U : Set X) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : Nat) :
    IsIso (homologyMap (integralOpenSupportMap K U) n) := by
  apply integral_open_cover_excision Kᶜ U hK.isOpen_compl hU ?_ n
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_cases hx : x ∈ K
  · exact Or.inr (hKU hx)
  · exact Or.inl hx

def integralOpenSupportHomologyIso
    (K U : Set X) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : Nat) :
    integralRelativeHomology ((Subtype.val : U → X) ⁻¹' Kᶜ) n ≅
      integralSupportHomology K n := by
  let := integralOpenSupportMap_homology_isIso K U hK hU hKU n
  exact asIso (homologyMap (integralOpenSupportMap K U) n)

theorem integralOpenSupportMap_naturality
    {K L : Set X} (hLK : L ⊆ K) (U : Set X) :
    (CategoryStruct.comp (integralOpenSupportMap K U ) ( integralSupportRestriction hLK)) =
      (CategoryStruct.comp (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr hLK)) ) ( integralOpenSupportMap L U)) := by
  apply (cancel_epi (integralRelativeProjection ((Subtype.val : U → X) ⁻¹' Kᶜ))).mp
  rw [← Category.assoc, integralOpenSupportMap, integralPairInclusion_projection,
    Category.assoc, integralSupportRestriction_projection,
    ← Category.assoc, integralRelativeRestriction_projection,
    integralOpenSupportMap, integralPairInclusion_projection]

def integralRelativeHomeomorphIso (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (h : ∀ x, x ∈ A ↔ e x ∈ B) : integralRelativeChains A ≅ integralRelativeChains B :=
  cokernel.mapIso _ _
    (integralChainsFunctor.mapIso (TopCat.isoOfHomeo (e.subtype h)))
    (integralChainsFunctor.mapIso (TopCat.isoOfHomeo e)) (by
      simp only [Functor.mapIso_hom, integralSubspaceChains, ← Functor.map_comp]
      rfl)

@[simp]
theorem integralRelativeHomeomorphIso_projection
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) :
    (CategoryStruct.comp (integralRelativeProjection A ) ( (integralRelativeHomeomorphIso e A B h).hom)) =
      (CategoryStruct.comp (integralChainsFunctor.map (TopCat.ofHom (e : C(X, Y))) ) (
        integralRelativeProjection B)) := by
  simp only [integralRelativeHomeomorphIso, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc, Functor.mapIso_hom]
  rfl

theorem integralRelativeHomeomorphIso_naturality
    (e : X ≃ₜ Y) {A A' : Set X} {B B' : Set Y}
    (h : ∀ x, x ∈ A ↔ e x ∈ B) (h' : ∀ x, x ∈ A' ↔ e x ∈ B')
    (hA : A ⊆ A') (hB : B ⊆ B') :
    (CategoryStruct.comp ((integralRelativeHomeomorphIso e A B h).hom ) ( integralRelativeRestriction hB)) =
      (CategoryStruct.comp (integralRelativeRestriction hA ) ( (integralRelativeHomeomorphIso e A' B' h').hom)) := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [← Category.assoc, integralRelativeHomeomorphIso_projection,
    Category.assoc, integralRelativeRestriction_projection,
    ← Category.assoc, integralRelativeRestriction_projection,
    integralRelativeHomeomorphIso_projection]

def integralChartRelativeChainsIso (e : OpenPartialHomeomorph X Y)
    (K : Set X) (hK : K ⊆ e.source) :
    integralRelativeChains ((Subtype.val : e.source → X) ⁻¹' Kᶜ) ≅
      integralRelativeChains ((Subtype.val : e.target → Y) ⁻¹' (e '' K)ᶜ) :=
  integralRelativeHomeomorphIso e.toHomeomorphSourceTarget _ _ (by
    intro p
    change p.val ∉ K ↔ e p.val ∉ e '' K
    constructor
    · intro hp he
      obtain ⟨k, hk, hkp⟩ := he
      exact hp ((e.injOn (hK hk) p.property hkp) ▸ hk)
    · intro hp hk
      exact hp ⟨p.val, hk, rfl⟩)

@[simp]
theorem integralChartRelativeChainsIso_projection
    (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : K ⊆ e.source) :
    (CategoryStruct.comp (integralRelativeProjection ((Subtype.val : e.source → X) ⁻¹' Kᶜ) ) (
      (integralChartRelativeChainsIso e K hK).hom)) =
        (CategoryStruct.comp (integralChainsFunctor.map (TopCat.ofHom
          (e.toHomeomorphSourceTarget : C(e.source, e.target))) ) (
            integralRelativeProjection ((Subtype.val : e.target → Y) ⁻¹' (e '' K)ᶜ))) :=
  integralRelativeHomeomorphIso_projection _ _ _ _

theorem integralChartRelativeChainsIso_naturality
    (e : OpenPartialHomeomorph X Y) {K L : Set X}
    (hK : K ⊆ e.source) (hL : L ⊆ e.source) (hLK : L ⊆ K) :
    (CategoryStruct.comp ((integralChartRelativeChainsIso e K hK).hom ) (
        integralRelativeRestriction
          (Set.preimage_mono (Set.compl_subset_compl.mpr (Set.image_mono hLK))))) =
      (CategoryStruct.comp (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr hLK)) ) (
          (integralChartRelativeChainsIso e L hL).hom)) :=
  integralRelativeHomeomorphIso_naturality _ _ _ _ _

def integralChartSupportHomologyIso [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X)
    (hK : IsCompact K) (hKs : K ⊆ e.source) (n : Nat) :
    integralSupportHomology K n ≅ integralSupportHomology (e '' K) n :=
  (integralOpenSupportHomologyIso K e.source hK.isClosed e.open_source hKs n).symm ≪≫
    (homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).mapIso
      (integralChartRelativeChainsIso e K hKs) ≪≫
    integralOpenSupportHomologyIso (e '' K) e.target
      (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed e.open_target
      (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)) n

theorem integralChartSupportHomologyIso_naturality [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKs : K ⊆ e.source)
    (hLs : L ⊆ e.source) (hLK : L ⊆ K) (n : Nat) :
    (CategoryStruct.comp ((integralChartSupportHomologyIso e K hK hKs n).hom ) (
        integralSupportHomologyRestriction (Set.image_mono hLK) n)) =
      (CategoryStruct.comp (integralSupportHomologyRestriction hLK n ) (
        (integralChartSupportHomologyIso e L hL hLs n).hom)) := by
  let SK := integralOpenSupportHomologyIso K e.source hK.isClosed e.open_source hKs n
  let SL := integralOpenSupportHomologyIso L e.source hL.isClosed e.open_source hLs n
  let TK := integralOpenSupportHomologyIso (e '' K) e.target
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hKs hx)) n
  let TL := integralOpenSupportHomologyIso (e '' L) e.target
    (hL.image_of_continuousOn (e.continuousOn.mono hLs)).isClosed e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hLs hx)) n
  let f := homologyMap (integralChartRelativeChainsIso e K hKs).hom n
  let g := homologyMap (integralChartRelativeChainsIso e L hLs).hom n
  let r := homologyMap (integralRelativeRestriction
    (Set.preimage_mono (f := (Subtype.val : e.source → X))
      (Set.compl_subset_compl.mpr hLK))) n
  let s := homologyMap (integralRelativeRestriction
    (Set.preimage_mono (f := (Subtype.val : e.target → Y))
      (Set.compl_subset_compl.mpr (Set.image_mono (f := e) hLK)))) n
  have hS : (CategoryStruct.comp (SK.hom ) ( integralSupportHomologyRestriction hLK n)) = (CategoryStruct.comp (r ) ( SL.hom)) := by
    change (CategoryStruct.comp (homologyMap (integralOpenSupportMap K e.source) n ) (
        homologyMap (integralSupportRestriction hLK) n)) =
      (CategoryStruct.comp (homologyMap (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr hLK))) n ) (
        homologyMap (integralOpenSupportMap L e.source) n))
    rw [← homologyMap_comp, ← homologyMap_comp, integralOpenSupportMap_naturality]
  have hT : (CategoryStruct.comp (TK.hom ) ( integralSupportHomologyRestriction (Set.image_mono hLK) n)) =
      (CategoryStruct.comp (s ) ( TL.hom)) := by
    change (CategoryStruct.comp (homologyMap (integralOpenSupportMap (e '' K) e.target) n ) (
        homologyMap (integralSupportRestriction (Set.image_mono hLK)) n)) =
      (CategoryStruct.comp (homologyMap (integralRelativeRestriction
        (Set.preimage_mono (Set.compl_subset_compl.mpr (Set.image_mono hLK)))) n ) (
        homologyMap (integralOpenSupportMap (e '' L) e.target) n))
    rw [← homologyMap_comp, ← homologyMap_comp, integralOpenSupportMap_naturality]
  have hchart : (CategoryStruct.comp (f ) ( s)) = (CategoryStruct.comp (r ) ( g)) := by
    dsimp only [f, g, s, r]
    rw [← homologyMap_comp, ← homologyMap_comp,
      integralChartRelativeChainsIso_naturality e hKs hLs hLK]
  change (CategoryStruct.comp (((CategoryStruct.comp (SK.inv ) ( (CategoryStruct.comp (f ) ( TK.hom))))) ) ( _)) = (CategoryStruct.comp (_ ) ( ((CategoryStruct.comp (SL.inv ) ( (CategoryStruct.comp (g ) ( TL.hom)))))))
  apply (cancel_epi SK.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc SK.hom, hS]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hT, ← Category.assoc f, hchart, Category.assoc]

end Poincare.Topology
end 

end FzIntegralChartSupport

noncomputable section FzIntegralFiniteSupport

/-!
# Finite unions of supports

Mayer--Vietoris transfers simultaneous higher-degree vanishing from all
finite intersections to their union.  The same induction detects a top
class by its restrictions to points once the intersection groups above
that degree vanish.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u v

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSupportHomology_empty_isZero (n : Nat) :
    IsZero (integralSupportHomology (∅ : Set X) n) := by
  let e : TopCat.of (Set.univ : Set X) ≅ TopCat.of X :=
    TopCat.isoOfHomeo (Homeomorph.Set.univ X)
  have : IsIso (integralSubspaceChains (Set.univ : Set X)) := by
    change IsIso (integralChainsFunctor.map e.hom)
    infer_instance
  change IsZero ((integralRelativeChains (∅ : Set X)ᶜ).homology n)
  rw [Set.compl_empty]
  exact (homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).map_isZero
    (isZero_cokernel_of_epi (integralSubspaceChains (Set.univ : Set X)))

theorem integralSupportHomology_finset_union_isZero
    {ι : Type v} (s : Finset ι) (F : ι → Set X) (d : Nat)
    (hF : ∀ i ∈ s, IsClosed (F i))
    (hI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
      IsZero (integralSupportHomology (⋂ i ∈ t, F i) (n + d))) :
    ∀ n : Nat, IsZero (integralSupportHomology (⋃ i ∈ s, F i) (n + d)) := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty =>
      intro n
      simpa using (integralSupportHomology_empty_isZero (X := X) (n + d))
  | @insert a s ha ih =>
      intro n
      have hrest : ∀ i ∈ s, IsClosed (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hrestI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ m : Nat,
          IsZero (integralSupportHomology (⋂ i ∈ t, F i) (m + d)) :=
        fun t ht htn m => hI t (ht.trans (Finset.subset_insert a s)) htn m
      have hG : ∀ i ∈ s, IsClosed (F a ∩ F i) :=
        fun i hi => (hF a (Finset.mem_insert_self a s)).inter (hrest i hi)
      have hGI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ m : Nat,
          IsZero (integralSupportHomology (⋂ i ∈ t, F a ∩ F i) (m + d)) := by
        intro t ht htn m
        have h := hI (insert a t) (Finset.insert_subset_insert a ht)
          (Finset.insert_nonempty a t) m
        rw [Finset.set_biInter_insert] at h
        have he : (⋂ i ∈ t, F a ∩ F i) = F a ∩ ⋂ i ∈ t, F i :=
          Set.inter_biInter htn.to_set F (F a)
        rw [he]
        exact h
      have hoverlap : IsZero
          (integralSupportHomology (F a ∩ ⋃ i ∈ s, F i) ((n + d) + 1)) := by
        have h := ih (fun i => F a ∩ F i) hG hGI (n + 1)
        simpa only [Set.inter_iUnion, Nat.add_right_comm n 1 d] using h
      have ha₀ : IsZero (integralSupportHomology (F a) (n + d)) := by
        simpa using hI {a} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a s))
          (Finset.singleton_nonempty a) n
      rw [Finset.set_biUnion_insert]
      exact integralSupportHomology_union_isZero (F a) (⋃ i ∈ s, F i)
        (hF a (Finset.mem_insert_self a s)) (isClosed_biUnion_finset hrest) (n + d)
        hoverlap ha₀ (ih F hrest hrestI n)

theorem integralSupportHomology_finset_union_detected
    {ι : Type v} (s : Finset ι) (F : ι → Set X) (d : Nat)
    (hF : ∀ i ∈ s, IsClosed (F i))
    (hI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
      IsZero (integralSupportHomology (⋂ i ∈ t, F i) (n + (d + 1))))
    (hD : ∀ i ∈ s, ∀ a : integralSupportHomology (F i) d,
      (∀ x : X, ∀ hx : x ∈ F i,
        integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hx) d a = 0) →
      a = 0)
    (a : integralSupportHomology (⋃ i ∈ s, F i) d)
    (ha : ∀ x : X, ∀ hx : x ∈ ⋃ i ∈ s, F i,
      integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hx) d a = 0) :
    a = 0 := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty =>
      have h := integralSupportHomology_empty_isZero (X := X) d
      have h' : IsZero (integralSupportHomology (⋃ i ∈ (∅ : Finset ι), F i) d) := by
        simpa using h
      exact (ModuleCat.isZero_iff_subsingleton.mp h').elim _ _
  | @insert i s hi ih =>
      revert a
      rw [Finset.set_biUnion_insert]
      intro a ha
      have hrest : ∀ j ∈ s, IsClosed (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have hrestI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
          IsZero (integralSupportHomology (⋂ j ∈ t, F j) (n + (d + 1))) :=
        fun t ht htn n => hI t (ht.trans (Finset.subset_insert i s)) htn n
      have hG : ∀ j ∈ s, IsClosed (F i ∩ F j) :=
        fun j hj => (hF i (Finset.mem_insert_self i s)).inter (hrest j hj)
      have hGI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
          IsZero (integralSupportHomology (⋂ j ∈ t, F i ∩ F j) (n + (d + 1))) := by
        intro t ht htn n
        have h := hI (insert i t) (Finset.insert_subset_insert i ht)
          (Finset.insert_nonempty i t) n
        rw [Finset.set_biInter_insert] at h
        have he : (⋂ j ∈ t, F i ∩ F j) = F i ∩ ⋂ j ∈ t, F j :=
          Set.inter_biInter htn.to_set F (F i)
        rw [he]
        exact h
      have hoverlap : IsZero
          (integralSupportHomology (F i ∩ ⋃ j ∈ s, F j) (d + 1)) := by
        have h := integralSupportHomology_finset_union_isZero s
          (fun j => F i ∩ F j) (d + 1) hG hGI 0
        simpa only [Set.inter_iUnion, Nat.zero_add] using h
      apply integralSupportHomology_union_ext (F i) (⋃ j ∈ s, F j)
        (hF i (Finset.mem_insert_self i s)) (isClosed_biUnion_finset hrest) d hoverlap
      · rw [map_zero]
        apply hD i (Finset.mem_insert_self i s)
        intro x hx
        rw [← ConcreteCategory.comp_apply, integralSupportHomologyRestriction_comp]
        exact ha x (Set.mem_union_left _ hx)
      · rw [map_zero]
        apply ih F hrest hrestI (fun j hj => hD j (Finset.mem_insert_of_mem hj))
        intro x hx
        rw [← ConcreteCategory.comp_apply, integralSupportHomologyRestriction_comp]
        exact ha x (Set.mem_union_right _ hx)

end Poincare.Topology
end 

end FzIntegralFiniteSupport

noncomputable section FzIntegralCompactGluing

/-!
# Compact support detection and gluing

Finite closed refinements of a neighborhood cover transfer local support
calculations to a compact set. Compatible locally represented families of
point classes then glue by the actual support Mayer--Vietoris sequence.
-/


section
open CategoryTheory Limits HomologicalComplex Set

universe u v

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def IntegralSupportDetected (K : Set X) (d : Nat) : Prop :=
  ∀ a : integralSupportHomology K d,
    (∀ x : X, ∀ hx : x ∈ K,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = 0) → a = 0

theorem exists_finite_compact_support_refinement [T2Space X] [RegularSpace X]
    (K : Set X) (hK : IsCompact K) (U : K → Set X)
    (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x : K, (x : X) ∈ U x) :
    ∃ s : Finset K, ∃ F : K → Set X,
      (∀ x, IsCompact (F x) ∧ F x ⊆ K ∩ U x) ∧ (⋃ x ∈ s, F x) = K := by
  have hN : ∀ x : K, ∃ N : Set X,
      N ∈ nhds (x : X) ∧ IsClosed N ∧ N ⊆ U x :=
    fun x => exists_mem_nhds_isClosed_subset ((hU x).mem_nhds (hxU x))
  choose N hxN hNclosed hNU using hN
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (N x))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hxN ⟨x, hx⟩)⟩)
  refine ⟨s, fun x => K ∩ N x,
    (fun x => ⟨hK.inter_right (hNclosed x), inter_subset_inter_right K (hNU x)⟩), ?_⟩
  apply subset_antisymm (iUnion₂_subset (fun _ _ => inter_subset_left))
  intro y hy
  obtain ⟨x, hxs, hyN⟩ := mem_iUnion₂.mp (hs hy)
  exact mem_iUnion₂.mpr ⟨x, hxs, hy, interior_subset hyN⟩

/-- Higher-degree vanishing and point detection on local compact supports
imply the corresponding statements on a compact union. -/
theorem integralCompactSupport_local_to_global [T2Space X] [RegularSpace X]
    (K : Set X) (hK : IsCompact K) (d : Nat)
    (hlocal : ∀ x : X, x ∈ K → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ L : Set X, IsCompact L → L ⊆ U →
        (∀ n : Nat, IsZero (integralSupportHomology L (n + (d + 1)))) ∧
          IntegralSupportDetected L d) :
    (∀ n : Nat, IsZero (integralSupportHomology K (n + (d + 1)))) ∧
      IntegralSupportDetected K d := by
  classical
  choose U hU hxU hcalc using fun x : K => hlocal x x.property
  obtain ⟨s, F, hF, hFK⟩ := exists_finite_compact_support_refinement K hK U hU hxU
  have hclosed : ∀ x ∈ s, IsClosed (F x) := fun x _ => (hF x).1.isClosed
  have hI : ∀ t : Finset K, t ⊆ s → t.Nonempty → ∀ n : Nat,
      IsZero (integralSupportHomology (⋂ x ∈ t, F x) (n + (d + 1))) := by
    intro t ht htn n
    obtain ⟨x, hxt⟩ := htn
    have hcompact : IsCompact (⋂ y ∈ t, F y) :=
      (hF x).1.of_isClosed_subset
        (isClosed_iInter (fun y => isClosed_iInter (fun _ => (hF y).1.isClosed)))
        (fun z hz => mem_iInter.mp (mem_iInter.mp hz x) hxt)
    have hsub : (⋂ y ∈ t, F y) ⊆ U x := fun z hz =>
      ((hF x).2 (mem_iInter.mp (mem_iInter.mp hz x) hxt)).2
    exact (hcalc x _ hcompact hsub).1 n
  constructor
  · intro n
    simpa only [hFK] using
      integralSupportHomology_finset_union_isZero s F (d + 1) hclosed hI n
  · have hd : IntegralSupportDetected (⋃ x ∈ s, F x) d := by
      intro a ha
      apply integralSupportHomology_finset_union_detected s F d hclosed hI ?_ a ha
      intro x hx
      exact (hcalc x (F x) (hF x).1 (fun z hz => ((hF x).2 hz).2)).2
    simpa only [hFK] using hd

@[simp]
theorem integralSupportHomologyRestriction_apply_comp
    {K L D : Set X} (hKL : K ⊆ L) (hLD : L ⊆ D) (n : Nat)
    (a : integralSupportHomology D n) :
    integralSupportHomologyRestriction hKL n (integralSupportHomologyRestriction hLD n a) =
      integralSupportHomologyRestriction (hKL.trans hLD) n a :=
  congrArg (fun f => f a) (integralSupportHomologyRestriction_comp hKL hLD n)

theorem exists_integralSupportHomology_finite_gluing [T2Space X]
    (d : Nat) (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L d)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) d)
    {ι : Type v} (s : Finset ι) (F : ι → Set X)
    (hF : ∀ i ∈ s, IsCompact (F i))
    (hclasses : ∀ i ∈ s, ∃ a : integralSupportHomology (F i) d,
      ∀ x : X, ∀ hx : x ∈ F i,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x) :
    ∃ a : integralSupportHomology (⋃ i ∈ s, F i) d,
      ∀ x : X, ∀ hx : x ∈ ⋃ i ∈ s, F i,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro x hx
      simp at hx
  | @insert i s hi ih =>
      have hrest : ∀ j ∈ s, IsCompact (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      obtain ⟨b, hb⟩ := hclasses i (Finset.mem_insert_self i s)
      obtain ⟨c, hc⟩ := ih hrest (fun j hj => hclasses j (Finset.mem_insert_of_mem hj))
      let L := ⋃ j ∈ s, F j
      have hL : IsCompact L := s.isCompact_biUnion hrest
      have hcompat : integralSupportHomologyRestriction (inter_subset_left : F i ∩ L ⊆ F i) d b =
          integralSupportHomologyRestriction (inter_subset_right : F i ∩ L ⊆ L) d c := by
        apply sub_eq_zero.mp
        apply hD (F i ∩ L) ((hF i (Finset.mem_insert_self i s)).inter_right hL.isClosed)
        intro x hx
        rw [map_sub, integralSupportHomologyRestriction_apply_comp,
          integralSupportHomologyRestriction_apply_comp, hb x hx.1, hc x hx.2, sub_self]
      obtain ⟨a, hab, hac⟩ := exists_integralSupportHomology_union (F i) L
        (hF i (Finset.mem_insert_self i s)).isClosed hL.isClosed d b c hcompat
      rw [Finset.set_biUnion_insert]
      refine ⟨a, ?_⟩
      intro x hx
      rcases hx with hx | hx
      · have he := integralSupportHomologyRestriction_apply_comp
          (singleton_subset_iff.mpr hx) (subset_union_left : F i ⊆ F i ∪ L) d a
        rw [hab] at he
        exact he.symm.trans (hb x hx)
      · have he := integralSupportHomologyRestriction_apply_comp
          (singleton_subset_iff.mpr hx) (subset_union_right : L ⊆ F i ∪ L) d a
        rw [hac] at he
        exact he.symm.trans (hc x hx)

/-- A locally represented family of point classes has a unique class on
each compact support. The local family is an explicit input here. -/
theorem exists_unique_integralSupportHomology_compact_gluing [T2Space X] [RegularSpace X]
    (d : Nat) (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L d)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) d)
    (K : Set X) (hK : IsCompact K)
    (hlocal : ∀ x : X, x ∈ K → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U d,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d b = omega y) :
    ∃! a : integralSupportHomology K d,
      ∀ x : X, ∀ hx : x ∈ K,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x := by
  classical
  choose U hU hxU b hb using fun x : K => hlocal x x.property
  obtain ⟨s, F, hF, hFK⟩ := exists_finite_compact_support_refinement K hK U hU hxU
  have hclasses : ∀ x ∈ s, ∃ a : integralSupportHomology (F x) d,
      ∀ y : X, ∀ hy : y ∈ F x,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d a = omega y := by
    intro x hx
    have hsub : F x ⊆ U x := fun y hy => ((hF x).2 hy).2
    refine ⟨integralSupportHomologyRestriction hsub d (b x), ?_⟩
    intro y hy
    rw [integralSupportHomologyRestriction_apply_comp]
    exact hb x y (hsub hy)
  have hex : ∃ a : integralSupportHomology K d,
      ∀ x : X, ∀ hx : x ∈ K,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x := by
    let P (L : Set X) : Prop := ∃ a : integralSupportHomology L d,
      ∀ x : X, ∀ hx : x ∈ L,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a = omega x
    have h : P (⋃ x ∈ s, F x) := exists_integralSupportHomology_finite_gluing d hD omega s F
      (fun x _ => (hF x).1) hclasses
    exact hFK ▸ h
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply sub_eq_zero.mp
  apply hD K hK
  intro x hx
  rw [map_sub, hb x hx, ha x hx, sub_self]

end Poincare.Topology
end 

end FzIntegralCompactGluing

noncomputable section FzSphereOpenCover

/-!
# Contractible open covers of spheres

The two complements of antipodal points are Euclidean charts. Their
intersection retracts radially onto the sphere of one lower dimension.
-/


section
open Set Metric
open scoped Topology ContinuousMap unitInterval

universe u

namespace Poincare.Topology

/-- Radial normalization gives an equivalence with punctured space. -/
def puncturedSpaceSphereHomotopyEquiv
    (E : Type u) [NormedAddCommGroup E] [NormedSpace Real E] :
    {x : E | x ≠ 0} ≃ₕ sphere (0 : E) 1 := by
  let P := {x : E | x ≠ 0}
  have hn (x : P) : ‖x.val‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
  have hq (x : P) : ‖x.val‖⁻¹ • x.val ∈ sphere (0 : E) 1 := by
    simp [norm_smul, hn x]
  let q : C(P, sphere (0 : E) 1) :=
    ⟨fun x => ⟨‖x.val‖⁻¹ • x.val, hq x⟩,
      ((continuous_subtype_val.norm.inv₀ hn).smul continuous_subtype_val).subtype_mk hq⟩
  let j : C(sphere (0 : E) 1, P) :=
    ⟨fun x => ⟨x.val, ne_zero_of_mem_sphere one_ne_zero x⟩,
      continuous_subtype_val.subtype_mk _⟩
  let c (z : unitInterval × P) : Real :=
    (1 - (z.1 : Real)) * ‖z.2.val‖⁻¹ + (z.1 : Real)
  have hcpos (z : unitInterval × P) : 0 < c z := by
    have hnorm : 0 < ‖z.2.val‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr z.2.property)
    by_cases ht : (z.1 : Real) = 1
    · simp [c, ht]
    · have hdiff : 0 < 1 - (z.1 : Real) :=
        sub_pos.mpr (lt_of_le_of_ne z.1.property.2 ht)
      exact add_pos_of_pos_of_nonneg (mul_pos hdiff hnorm) z.1.property.1
  have hc : Continuous c :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_subtype_val.comp continuous_snd).norm.inv₀ (fun z => hn z.2))).add
      (continuous_subtype_val.comp continuous_fst)
  let H : ContinuousMap.Homotopy (j.comp q) (ContinuousMap.id P) :=
    { toFun := fun z => ⟨c z • z.2.val, smul_ne_zero (hcpos z).ne' z.2.property⟩
      continuous_toFun := (hc.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left x := by
        apply Subtype.ext
        change c (0, x) • x.val = ‖x.val‖⁻¹ • x.val
        simp [c]
      map_one_left x := by
        apply Subtype.ext
        change c (1, x) • x.val = x.val
        simp [c] }
  refine ⟨q, j, ⟨H⟩, ?_⟩
  have hqj : q.comp j = ContinuousMap.id (sphere (0 : E) 1) := by
    ext x
    change ‖x.val‖⁻¹ • x.val = x.val
    simp [mem_sphere_zero_iff_norm.mp x.property]
  rw [hqj]

/-- A punctured sphere chart sends the antipodal point to zero. -/
theorem exists_sphere_puncture_homeomorph
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] (n : Nat) [Fact (Module.finrank Real E = n + 1)]
    (v : sphere (0 : E) 1) :
    ∃ h : ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ EuclideanSpace Real (Fin n),
      h ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere Real v).symm⟩ = 0 := by
  let e := stereographic' n v
  let h : ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ EuclideanSpace Real (Fin n) :=
    (Homeomorph.setCongr (stereographic'_source v).symm).trans
      (e.toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))
  refine ⟨h, ?_⟩
  change stereographic' n v (-v) = 0
  simp [stereographic']

/-- The two punctured charts cover a sphere and intersect in a smaller sphere up to homotopy. -/
theorem exists_sphere_contractible_open_cover (n : Nat) :
    ∃ A B : Set (sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1),
      IsOpen A ∧ IsOpen B ∧ A ∪ B = Set.univ ∧
      ContractibleSpace A ∧ ContractibleSpace B ∧
      Nonempty (↥(A ∩ B) ≃ₕ sphere (0 : EuclideanSpace Real (Fin (n + 1))) 1) := by
  let E := EuclideanSpace Real (Fin (n + 2))
  let S := sphere (0 : E) 1
  let : Fact (Module.finrank Real E = (n + 1) + 1) := ⟨by simp [E]⟩
  have hSne : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨v, hv⟩ := hSne
  let p : S := ⟨v, hv⟩
  have hne : p ≠ -p := ne_neg_of_mem_unit_sphere Real p
  let A : Set S := {p}ᶜ
  let B : Set S := {-p}ᶜ
  obtain ⟨hA, hz⟩ := exists_sphere_puncture_homeomorph (n + 1) p
  obtain ⟨hB, _⟩ := exists_sphere_puncture_homeomorph (n + 1) (-p)
  have hcover : A ∪ B = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x = p
    · right
      simpa only [B, Set.mem_compl_iff, Set.mem_singleton_iff, hx] using hne
    · exact Or.inl hx
  let H : ↥(A ∩ B) ≃ₜ {x : A | x.val ≠ -p} :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hzero (x : A) : x.val ≠ -p ↔ hA x ≠ 0 := by
    rw [← hz, hA.injective.ne_iff]
    constructor
    · intro hx h
      exact hx (congrArg Subtype.val h)
    · intro hx h
      exact hx (Subtype.ext h)
  let G := hA.subtype (p := fun x : A => x.val ≠ -p)
    (q := fun x : EuclideanSpace Real (Fin (n + 1)) => x ≠ 0) hzero
  refine ⟨A, B, isOpen_compl_singleton, isOpen_compl_singleton, hcover,
    hA.contractibleSpace, hB.contractibleSpace, ?_⟩
  exact ⟨((H.trans G).toHomotopyEquiv).trans
    (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace Real (Fin (n + 1))))⟩

end Poincare.Topology
end 

end FzSphereOpenCover

noncomputable section FzClosedBallComplement

/-!
# A closed-ball complement and its center puncture

Radial interpolation stays outside the closed ball because its endpoint
radii are both larger than the ball radius. The resulting equivalence has
the literal inclusion into the center puncture as its forward map.
-/


open Set Metric
open scoped Topology ContinuousMap unitInterval

universe u

namespace Poincare.Topology

section
variable {E : Type u} [NormedAddCommGroup E]

theorem closedBallComplement_subset_puncture (c : E) (r : Real) (hr : 0 ≤ r) :
    (closedBall c r)ᶜ ⊆ ({c}ᶜ : Set E) := by
  apply Set.compl_subset_compl.mpr
  exact singleton_subset_iff.mpr (mem_closedBall_self hr)

def closedBallComplementInclusion (c : E) (r : Real) (hr : 0 ≤ r) :
    C(((closedBall c r)ᶜ : Set E), ({c}ᶜ : Set E)) :=
  ⟨fun x => ⟨x.val, closedBallComplement_subset_puncture c r hr x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

variable [NormedSpace Real E]

def closedBallComplementPunctureHomotopyEquiv (c : E) (r : Real) (hr : 0 ≤ r) :
    ((closedBall c r)ᶜ : Set E) ≃ₕ ({c}ᶜ : Set E) := by
  let P : Set E := {c}ᶜ
  let O : Set E := (closedBall c r)ᶜ
  let R : Real := r + 1
  have hR : r < R := by dsimp [R]; linarith
  have hRpos : 0 < R := hr.trans_lt hR
  have hn (x : P) : ‖x.val - c‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr x.property)
  let v : C(P, E) :=
    ⟨fun x => ‖x.val - c‖⁻¹ • (x.val - c),
      (((continuous_subtype_val.sub continuous_const).norm.inv₀ hn).smul
        (continuous_subtype_val.sub continuous_const))⟩
  have hv (x : P) : ‖v x‖ = 1 := by
    change ‖‖x.val - c‖⁻¹ • (x.val - c)‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (hn x)]
  have hvrecover (x : P) : ‖x.val - c‖ • v x = x.val - c := by
    change ‖x.val - c‖ • (‖x.val - c‖⁻¹ • (x.val - c)) = x.val - c
    rw [smul_smul, mul_inv_cancel₀ (hn x), one_smul]
  have hj (x : P) : c + R • v x ∈ O := by
    change ¬dist (c + R • v x) c ≤ r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hRpos.le, hv, mul_one]
    exact not_le_of_gt hR
  let j : C(P, O) :=
    ⟨fun x => ⟨c + R • v x, hj x⟩,
      (continuous_const.add (continuous_const.smul v.continuous)).subtype_mk hj⟩
  let i : C(O, P) := closedBallComplementInclusion c r hr
  let radius (z : unitInterval × P) : Real :=
    AffineMap.lineMap R ‖z.2.val - c‖ (z.1 : Real)
  have hrad : Continuous radius := by
    dsimp [radius]
    simp only [AffineMap.lineMap_apply_ring]
    fun_prop
  have hradpos (z : unitInterval × P) : 0 < radius z :=
    (convex_Ioi (0 : Real)).lineMap_mem hRpos
      (norm_pos_iff.mpr (sub_ne_zero.mpr z.2.property)) z.1.property
  let K : C(unitInterval × P, E) :=
    ⟨fun z => c + radius z • v z.2,
      continuous_const.add (hrad.smul (v.continuous.comp continuous_snd))⟩
  have hKnorm (z : unitInterval × P) : ‖K z - c‖ = radius z := by
    change ‖c + radius z • v z.2 - c‖ = radius z
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hradpos z).le,
      hv, mul_one]
  have hKpoint (z : unitInterval × P) : K z ∈ P := by
    intro h
    have he : K z = c := h
    have hnorm := hKnorm z
    rw [he, sub_self, norm_zero] at hnorm
    exact (ne_of_gt (hradpos z)) hnorm.symm
  have hKout (t : unitInterval) (x : O) : K (t, i x) ∈ O := by
    have hx : r < ‖(i x).val - c‖ := by
      change r < ‖x.val - c‖
      have hx' : ¬dist x.val c ≤ r := x.property
      simpa only [not_le, dist_eq_norm] using hx'
    have hradius : r < radius (t, i x) :=
      (convex_Ioi r).lineMap_mem hR hx t.property
    change ¬dist (K (t, i x)) c ≤ r
    rw [dist_eq_norm, hKnorm]
    exact not_le_of_gt hradius
  have hK0 (x : P) : K (0, x) = (j x).val := by
    change c + AffineMap.lineMap R ‖x.val - c‖ 0 • v x = c + R • v x
    rw [AffineMap.lineMap_apply_zero]
  have hK1 (x : P) : K (1, x) = x.val := by
    change c + AffineMap.lineMap R ‖x.val - c‖ 1 • v x = x.val
    rw [AffineMap.lineMap_apply_one, hvrecover]
    abel
  let HO : (j.comp i).Homotopy (ContinuousMap.id O) :=
    { toFun := fun z => ⟨K (z.1, i z.2), hKout z.1 z.2⟩
      continuous_toFun :=
        (K.continuous.comp (continuous_fst.prodMk
          (i.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left x := Subtype.ext (hK0 (i x))
      map_one_left x := Subtype.ext (hK1 (i x)) }
  let HP : (i.comp j).Homotopy (ContinuousMap.id P) :=
    { toFun := fun z => ⟨K z, hKpoint z⟩
      continuous_toFun := K.continuous.subtype_mk hKpoint
      map_zero_left x := Subtype.ext (hK0 x)
      map_one_left x := Subtype.ext (hK1 x) }
  exact ⟨i, j, ⟨HO⟩, ⟨HP⟩⟩

theorem closedBallComplementPunctureHomotopyEquiv_toFun
    (c : E) (r : Real) (hr : 0 ≤ r) :
    (closedBallComplementPunctureHomotopyEquiv c r hr).toFun =
      closedBallComplementInclusion c r hr := rfl

def punctureTranslationHomeomorph (c : E) :
    ({c}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E) := by
  have hf (x : ({c}ᶜ : Set E)) : x.val - c ∈ ({0}ᶜ : Set E) :=
    sub_ne_zero.mpr x.property
  have hg (x : ({0}ᶜ : Set E)) : c + x.val ∈ ({c}ᶜ : Set E) := by
    intro h
    have he : c + x.val = c := h
    exact x.property (add_left_cancel (he.trans (add_zero c).symm))
  exact {
    toFun := fun x => ⟨x.val - c, hf x⟩
    invFun := fun x => ⟨c + x.val, hg x⟩
    left_inv := fun x => Subtype.ext (by dsimp; abel)
    right_inv := fun x => Subtype.ext (by dsimp; abel)
    continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk hf
    continuous_invFun := (continuous_const.add continuous_subtype_val).subtype_mk hg }

def closedBallComplementSphereHomotopyEquiv (c : E) (r : Real) (hr : 0 ≤ r) :
    ((closedBall c r)ᶜ : Set E) ≃ₕ sphere (0 : E) 1 :=
  (closedBallComplementPunctureHomotopyEquiv c r hr).trans
    ((punctureTranslationHomeomorph c).toHomotopyEquiv.trans
      (puncturedSpaceSphereHomotopyEquiv E))

end

end Poincare.Topology

end FzClosedBallComplement

noncomputable section FzCompactConvexComplement

/-!
# Complements of compact convex sets

The literal inclusion of the complement of a compact convex set into the
puncture at any of its points is a homotopy equivalence. The inverse expands
radially past a bounding sphere. Outward radial motion cannot enter the
convex set, including when that set has empty interior.
-/


section
open Set Metric
open scoped Topology ContinuousMap unitInterval

universe u

namespace Poincare.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

theorem convex_complement_outward (K : Set E) (hK : Convex Real K)
    (x : E) (hx : x ∈ K) (y : E) (hy : y ∉ K) (a : Real) (ha : 1 ≤ a) :
    x + a • (y - x) ∉ K := by
  intro h
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hm := hK.add_smul_sub_mem hx h
    (show a⁻¹ ∈ Icc (0 : Real) 1 from
      ⟨inv_nonneg.mpr ha0.le, inv_le_one_of_one_le₀ ha⟩)
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul,
    add_sub_cancel] at hm
  exact hy hm

def compactConvexComplementInclusion (K : Set E) (x : E) (hx : x ∈ K) :
    C((Kᶜ : Set E), ({x}ᶜ : Set E)) :=
  ⟨fun y => ⟨y.val, fun h => y.property (h ▸ hx)⟩,
    continuous_subtype_val.subtype_mk _⟩

def compactConvexComplementPunctureHomotopyEquiv
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) : (Kᶜ : Set E) ≃ₕ ({x}ᶜ : Set E) := by
  let R := (hK.isBounded.subset_ball_lt 0 x).choose
  have hKR : K ⊆ ball x R := (hK.isBounded.subset_ball_lt 0 x).choose_spec.2
  let P : Set E := {x}ᶜ
  let O : Set E := Kᶜ
  have hn (y : P) : ‖y.val - x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr y.property)
  have hnpos (y : P) : 0 < ‖y.val - x‖ := lt_of_le_of_ne (norm_nonneg _) (hn y).symm
  let alpha : C(P, Real) :=
    ⟨fun y => max 1 (R / ‖y.val - x‖),
      continuous_const.max
        (continuous_const.div (continuous_subtype_val.sub continuous_const).norm hn)⟩
  have ha (y : P) : 1 ≤ alpha y := le_max_left _ _
  have hj (y : P) : x + alpha y • (y.val - x) ∈ O := by
    intro hy
    have hnorm : ‖x + alpha y • (y.val - x) - x‖ < R := by
      simpa only [mem_ball, dist_eq_norm] using hKR hy
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (ha y))]
      at hnorm
    have hle : R ≤ alpha y * ‖y.val - x‖ :=
      (div_le_iff₀ (hnpos y)).mp (le_max_right 1 _)
    exact (not_lt_of_ge hle) hnorm
  let j : C(P, O) :=
    ⟨fun y => ⟨x + alpha y • (y.val - x), hj y⟩,
      (continuous_const.add (alpha.continuous.smul
        (continuous_subtype_val.sub continuous_const))).subtype_mk hj⟩
  let i : C(O, P) := compactConvexComplementInclusion K x hx
  let beta (z : unitInterval × P) : Real :=
    AffineMap.lineMap (alpha z.2) 1 (z.1 : Real)
  have hbeta : Continuous beta := by
    dsimp [beta]
    simp only [AffineMap.lineMap_apply_ring]
    fun_prop
  have hb (z : unitInterval × P) : 1 ≤ beta z :=
    (convex_Ici (1 : Real)).lineMap_mem (ha z.2)
      (show (1 : Real) ∈ Ici 1 from by simp) z.1.property
  let H : C(unitInterval × P, E) :=
    ⟨fun z => x + beta z • (z.2.val - x),
      continuous_const.add (hbeta.smul
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const))⟩
  have hHP (z : unitInterval × P) : H z ∈ P := by
    intro h
    have hzero : beta z • (z.2.val - x) = 0 := by
      have he : x + beta z • (z.2.val - x) = x := h
      exact add_left_cancel (he.trans (add_zero x).symm)
    have hb0 : beta z ≠ 0 := (zero_lt_one.trans_le (hb z)).ne'
    exact (sub_ne_zero.mpr z.2.property) ((smul_eq_zero.mp hzero).resolve_left hb0)
  have hHO (t : unitInterval) (y : O) : H (t, i y) ∈ O :=
    convex_complement_outward K hconv x hx y.val y.property (beta (t, i y)) (hb _)
  have hH0 (y : P) : H (0, y) = (j y).val := by
    change x + AffineMap.lineMap (alpha y) 1 0 • (y.val - x) =
      x + alpha y • (y.val - x)
    rw [AffineMap.lineMap_apply_zero]
  have hH1 (y : P) : H (1, y) = y.val := by
    change x + AffineMap.lineMap (alpha y) 1 1 • (y.val - x) = y.val
    rw [AffineMap.lineMap_apply_one, one_smul, add_sub_cancel]
  let HO : (j.comp i).Homotopy (ContinuousMap.id O) :=
    { toFun := fun z => ⟨H (z.1, i z.2), hHO z.1 z.2⟩
      continuous_toFun :=
        (H.continuous.comp (continuous_fst.prodMk
          (i.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left y := Subtype.ext (hH0 (i y))
      map_one_left y := Subtype.ext (hH1 (i y)) }
  let HP : (i.comp j).Homotopy (ContinuousMap.id P) :=
    { toFun := fun z => ⟨H z, hHP z⟩
      continuous_toFun := H.continuous.subtype_mk hHP
      map_zero_left y := Subtype.ext (hH0 y)
      map_one_left y := Subtype.ext (hH1 y) }
  exact ⟨i, j, ⟨HO⟩, ⟨HP⟩⟩

theorem compactConvexComplementPunctureHomotopyEquiv_toFun
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) :
    (compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx).toFun =
      compactConvexComplementInclusion K x hx := by
  unfold compactConvexComplementPunctureHomotopyEquiv
  rfl

end Poincare.Topology
end 

end FzCompactConvexComplement

noncomputable section FzIntegralCoverHomology

/-!
# Integral homology of a cover by two contractible subspaces

Excision and the homology sequence give the positive-degree suspension
isomorphism. In degree one the result is the actual kernel of the inclusion
on degree-zero homology, so disconnected overlaps remain visible.
-/


section
open CategoryTheory Limits

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSubspaceChains_homology_mono_of_contractible
    (A : Set X) [ContractibleSpace A] (n : Nat) :
    Mono (HomologicalComplex.homologyMap (integralSubspaceChains A) n) := by
  obtain ⟨a, ⟨H⟩⟩ := id_nullhomotopic A
  let i : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let q : TopCat.of X ⟶ TopCat.of A := TopCat.ofHom (ContinuousMap.const X a)
  let HT : TopCat.Homotopy (𝟙 (TopCat.of A)) ((CategoryStruct.comp (i ) ( q))) := H
  have he := HT.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  change HomologicalComplex.homologyMap (integralChainsFunctor.map (𝟙 _)) n =
    HomologicalComplex.homologyMap (integralChainsFunctor.map ((CategoryStruct.comp (i ) ( q)))) n at he
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp] at he
  exact mono_of_mono_fac he.symm

/-- Collapsing a contractible subspace preserves all positive integral homology. -/
theorem integralToRelativeHomology_isIso_of_contractible
    (A : Set X) [ContractibleSpace A] (n : Nat) :
    IsIso (integralToRelativeHomology A (n + 1)) := by
  let S := integralPairSequence_shortExact A
  have hA := integral_contractible_homology_isZero A (n + 1) (by omega)
  let : Mono (integralToRelativeHomology A (n + 1)) :=
    (S.homology_exact₂ (n + 1)).mono_g (hA.eq_of_src _ _)
  let : Mono (HomologicalComplex.homologyMap (integralSubspaceChains A) n) :=
    integralSubspaceChains_homology_mono_of_contractible A n
  have hδ : S.δ (n + 1) n rfl = 0 := by
    apply (cancel_mono (HomologicalComplex.homologyMap (integralSubspaceChains A) n)).mp
    exact (S.δ_comp (n + 1) n rfl).trans zero_comp.symm
  let : Epi (integralToRelativeHomology A (n + 1)) :=
    (S.homology_exact₃ (n + 1) n rfl).epi_f hδ
  exact isIso_of_mono_of_epi _

/-- The degree shift associated to an open cover by two contractible subspaces. -/
def integralContractibleCoverHomologyIso
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : Nat) :
    integralHomology X (n + 2) ≅
      integralHomology ((Subtype.val : B → X) ⁻¹' A) (n + 1) := by
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let e := integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := AB) (B := A) (fun _ hb => hb)
  let : IsIso (integralToRelativeHomology A (n + 2)) :=
    integralToRelativeHomology_isIso_of_contractible A (n + 1)
  let : IsIso (HomologicalComplex.homologyMap e (n + 2)) :=
    integral_open_cover_excision A B hA hB hcover (n + 2)
  exact asIso (integralToRelativeHomology A (n + 2)) ≪≫
    (asIso (HomologicalComplex.homologyMap e (n + 2))).symm ≪≫
    (integralPairSequence_shortExact AB).δIso (n + 2) (n + 1) rfl
      (integral_contractible_homology_isZero B (n + 2) (by omega))
      (integral_contractible_homology_isZero B (n + 1) (by omega))

/-- The degree-one group of a contractible cover is the kernel of the
overlap inclusion on degree-zero integral homology. -/
def integralContractibleCoverHomologyOneIso
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    integralHomology X 1 ≅ kernel (HomologicalComplex.homologyMap
      (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) 0) := by
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let e := integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := AB) (B := A) (fun _ hb => hb)
  let : IsIso (integralToRelativeHomology A 1) :=
    integralToRelativeHomology_isIso_of_contractible A 0
  let : IsIso (HomologicalComplex.homologyMap e 1) :=
    integral_open_cover_excision A B hA hB hcover 1
  let S := integralPairSequence_shortExact AB
  let : Mono (S.δ 1 0 rfl) :=
    S.mono_δ 1 0 rfl (integral_contractible_homology_isZero B 1 (by omega))
  exact asIso (integralToRelativeHomology A 1) ≪≫
    (asIso (HomologicalComplex.homologyMap e 1)).symm ≪≫
    (S.homology_exact₁ 1 0 rfl).fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

end Poincare.Topology
end 

end FzIntegralCoverHomology

noncomputable section FzIntegralHomologyEquiv

/-!
# Integral homology of homotopy equivalent spaces

The isomorphism consists of the actual maps on homology induced by the
two continuous maps of the equivalence.
-/


section
open CategoryTheory
open scoped ContinuousMap

universe u

namespace Poincare.Topology

def integralHomologyIsoOfHomotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₕ Y) (n : Nat) : integralHomology X n ≅ integralHomology Y n where
  hom := HomologicalComplex.homologyMap
    (integralChainsFunctor.map (TopCat.ofHom h.toFun)) n
  inv := HomologicalComplex.homologyMap
    (integralChainsFunctor.map (TopCat.ofHom h.invFun)) n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
    let H : TopCat.Homotopy ((CategoryStruct.comp (TopCat.ofHom h.toFun ) ( TopCat.ofHom h.invFun)))
        (𝟙 (TopCat.of X)) := Classical.choice h.left_inv
    simpa only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] using
      H.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
    let H : TopCat.Homotopy ((CategoryStruct.comp (TopCat.ofHom h.invFun ) ( TopCat.ofHom h.toFun)))
        (𝟙 (TopCat.of Y)) := Classical.choice h.right_inv
    simpa only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] using
      H.congr_homologyMap_singularChainComplexFunctor integralCoefficient n

end Poincare.Topology
end 

end FzIntegralHomologyEquiv

noncomputable section FzIntegralSphereHomology

/-!
# Integral sphere homology by contractible open covers

The cover and intersection equivalence are constructed from stereographic
charts, and the homology isomorphism comes from canonical excision.
-/


section
open CategoryTheory Metric
open scoped ContinuousMap Topology

universe u

namespace Poincare.Topology

def intersectionPreimageHomeomorph
    {X : Type u} [TopologicalSpace X] (A B : Set X) :
    ↥(A ∩ B) ≃ₜ ((Subtype.val : B → X) ⁻¹' A) where
  toFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  invFun x := ⟨x.val.val, x.property, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual top-degree recurrence for spheres of dimension at least two. -/
def integralSphereHomologySuccIso (n : Nat) :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin (n + 3))) 1) (n + 2) ≅
      integralHomology (sphere (0 : EuclideanSpace Real (Fin (n + 2))) 1) (n + 1) := by
  apply Classical.choice
  obtain ⟨A, B, hA, hB, hcover, hAc, hBc, ⟨hAB⟩⟩ :=
    exists_sphere_contractible_open_cover (n + 1)
  let : ContractibleSpace A := hAc
  let : ContractibleSpace B := hBc
  exact ⟨integralContractibleCoverHomologyIso A B hA hB hcover n ≪≫
    integralHomologyIsoOfHomotopyEquiv
      (((intersectionPreimageHomeomorph A B).symm.toHomotopyEquiv).trans hAB) (n + 1)⟩

end Poincare.Topology
end 

end FzIntegralSphereHomology

noncomputable section FzIntegralAmbientRelative

/-!
# Relative homology of a contractible ambient space

The connecting map in the integral pair sequence identifies the positive
relative groups of a contractible ambient space with the homology of the
subspace. This is the algebraic local-homology shift used for punctured
Euclidean neighborhoods.
-/


section
open CategoryTheory

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralContractibleAmbientRelativeBoundaryIso
    (A : Set X) [ContractibleSpace X] (n : Nat) :
    integralRelativeHomology A (n + 2) ≅ integralHomology A (n + 1) := by
  let S := integralPairSequence_shortExact A
  exact S.δIso (n + 2) (n + 1) rfl
    (integral_contractible_homology_isZero X (n + 2) (by omega))
    (integral_contractible_homology_isZero X (n + 1) (by omega))

end Poincare.Topology
end 

end FzIntegralAmbientRelative

noncomputable section GnIntegralSphereVanishing

/-!
# Integral homology above the dimension of the two-sphere

Two contractible sphere covers reduce degree three on the two-sphere to
positive-degree homology of the finite zero-sphere. The relative connecting
isomorphism then gives degree-four vanishing for punctured Euclidean space.
-/


open CategoryTheory Limits Metric
open scoped ContinuousMap Topology

namespace Poincare.Topology

section
private theorem zeroSphere_positive_homology_isZero (n : Nat) (hn : n ≠ 0) :
    IsZero (integralHomology (sphere (0 : EuclideanSpace Real (Fin 1)) 1) n) := by
  let e := (OrthonormalBasis.singleton (Fin 1) Real).repr.symm
  let eS : sphere (0 : EuclideanSpace Real (Fin 1)) 1 ≃ sphere (0 : Real) 1 :=
    e.toEquiv.subtypeEquiv (fun x => by
      simp only [mem_sphere, dist_zero_right]
      change (‖x‖ = 1) ↔ ‖e x‖ = 1
      rw [e.norm_map]
      rfl)
  have hfinite : (sphere (0 : Real) 1).Finite := by
    rw [Real.sphere_eq_pair 0 (by norm_num)]
    exact Set.toFinite _
  let : Fintype (sphere (0 : Real) 1) := hfinite.fintype
  let : Finite (sphere (0 : EuclideanSpace Real (Fin 1)) 1) :=
    Finite.of_equiv (sphere (0 : Real) 1) eS.symm
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat Int) n integralCoefficient
      (TopCat.of (sphere (0 : EuclideanSpace Real (Fin 1)) 1)) hn

private def sphereHomologyDegreeShiftIso (m n : Nat) :
    integralHomology (sphere (0 : EuclideanSpace Real (Fin (m + 2))) 1) (n + 2) ≅
      integralHomology (sphere (0 : EuclideanSpace Real (Fin (m + 1))) 1) (n + 1) := by
  apply Classical.choice
  obtain ⟨A, B, hA, hB, hcover, hAc, hBc, ⟨hAB⟩⟩ :=
    exists_sphere_contractible_open_cover m
  let : ContractibleSpace A := hAc
  let : ContractibleSpace B := hBc
  exact ⟨integralContractibleCoverHomologyIso A B hA hB hcover n ≪≫
    integralHomologyIsoOfHomotopyEquiv
      (((intersectionPreimageHomeomorph A B).symm.toHomotopyEquiv).trans hAB) (n + 1)⟩

theorem sphereHomologyAbove_isZero (k n : Nat) :
    IsZero (integralHomology (sphere (0 : EuclideanSpace Real (Fin (k + 1))) 1) (n + k + 1)) := by
  induction k with
  | zero => exact zeroSphere_positive_homology_isZero (n + 1) (by omega)
  | succ k ih => exact ih.of_iso (sphereHomologyDegreeShiftIso k (n + k))

end

end Poincare.Topology

end GnIntegralSphereVanishing

noncomputable section GnIntegralConvexSupport

/-!
# Integral homology supported on a compact convex set

The canonical restriction to any point of a compact convex set is a
quasi-isomorphism. In Euclidean three-space this computes the top support
group and proves vanishing in every larger degree, including for convex
sets with empty interior.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

theorem integralCompactConvexSupportRestriction_quasiIso
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) :
    QuasiIso (integralSupportRestriction (Set.singleton_subset_iff.mpr hx)) := by
  let O : Set E := Kᶜ
  let P : Set E := {x}ᶜ
  let incl : integralChains O ⟶ integralChains P := integralChainsFunctor.map
    (TopCat.ofHom (compactConvexComplementInclusion K x hx))
  have hI : QuasiIso incl := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (integralHomologyIsoOfHomotopyEquiv
      (compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx) n).hom
    infer_instance
  let F : integralPairSequence O ⟶ integralPairSequence P :=
    { τ₁ := incl
      τ₂ := 𝟙 (integralChains E)
      τ₃ := integralSupportRestriction (Set.singleton_subset_iff.mpr hx)
      comm₁₂ := by
        change (CategoryStruct.comp (incl ) ( integralSubspaceChains P)) = (CategoryStruct.comp (integralSubspaceChains O ) ( 𝟙 _))
        rw [Category.comp_id]
        dsimp only [incl, integralSubspaceChains]
        rw [← Functor.map_comp]
        rfl
      comm₂₃ := by
        change (CategoryStruct.comp (𝟙 _ ) ( integralRelativeProjection P)) =
          (CategoryStruct.comp (integralRelativeProjection O ) ( integralSupportRestriction _))
        rw [Category.id_comp, integralSupportRestriction_projection] }
  exact HomologySequence.quasiIso_τ₃ F
    (integralPairSequence_shortExact O) (integralPairSequence_shortExact P) hI
      (by change QuasiIso (𝟙 (integralChains E)); infer_instance)

theorem integralCompactConvexSupportRestriction_homology_isIso
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) (n : Nat) :
    IsIso (integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hx) n) := by
  let := integralCompactConvexSupportRestriction_quasiIso K hK hconv x hx
  change IsIso (homologyMap (integralSupportRestriction _) n)
  infer_instance

theorem integralEuclideanCompactConvexSupportAbove_isZero {k : Nat}
    (K : Set (EuclideanSpace Real (Fin (k + 2)))) (hK : IsCompact K)
    (hconv : Convex Real K) (x : EuclideanSpace Real (Fin (k + 2))) (hx : x ∈ K) (n : Nat) :
    IsZero (integralSupportHomology K (n + (k + 3))) :=
  (sphereHomologyAbove_isZero (k + 1) n).of_iso
    (integralContractibleAmbientRelativeBoundaryIso Kᶜ (n + k + 1) ≪≫
      integralHomologyIsoOfHomotopyEquiv
        ((compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx).trans
          ((punctureTranslationHomeomorph x).toHomotopyEquiv.trans
            (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace Real (Fin (k + 2)))))) (n + k + 2))

end Poincare.Topology
end 

end GnIntegralConvexSupport

noncomputable section FzIntegralSupportLocalization

/-!
# Localization of relative singular homology near a point

The finitely many simplex images in a singular chain form a compact set.
In a Hausdorff space, a chain vanishing relative to a puncture therefore
vanishes relative to the complement of an open neighborhood of that point.
Lifting a relative boundary to ambient chains gives the corresponding
statement for actual relative homology classes, in every degree.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

@[simp]
theorem integralRelativeRestriction_comp {A B D : Set X}
    (hAB : A ⊆ B) (hBD : B ⊆ D) :
    (CategoryStruct.comp (integralRelativeRestriction hAB ) ( integralRelativeRestriction hBD)) =
      integralRelativeRestriction (hAB.trans hBD) := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [← Category.assoc, integralRelativeRestriction_projection,
    integralRelativeRestriction_projection, integralRelativeRestriction_projection]

theorem exists_open_integralRelativeProjection_eq_zero [T2Space X]
    (n : Nat) (c : (integralChains X).X n) (x : X)
    (hc : (integralRelativeProjection ({x}ᶜ : Set X)).f n c = 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (integralRelativeProjection Uᶜ).f n c = 0 := by
  classical
  let F := (integralChainCoordinates X n c).support
  let S : Set X := ⋃ s ∈ F, Set.range s
  have hS : IsCompact S :=
    F.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hr : c ∈ LinearMap.range
      ((integralSubspaceChains ({x}ᶜ : Set X)).f n).hom :=
    (integralProjection_eq_zero_iff (integralSubspaceChains ({x}ᶜ : Set X)) n c).mp hc
  have hs := (integral_subspace_range_iff ({x}ᶜ : Set X) n c).mp hr
  refine ⟨Sᶜ, hS.isClosed.isOpen_compl, ?_, ?_⟩
  · intro hx
    obtain ⟨s, hsf, hx⟩ := Set.mem_iUnion₂.mp hx
    exact hs s hsf hx rfl
  · rw [compl_compl]
    apply (integralProjection_eq_zero_iff (integralSubspaceChains S) n c).mpr
    apply (integral_subspace_range_iff S n c).mpr
    intro s hsf y hy
    exact Set.mem_iUnion₂.mpr ⟨s, hsf, hy⟩

private theorem homologyClass_zero_iff_boundary
    (C : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) (z : C.cycles n) :
    C.homologyπ n z = 0 ↔
      ∃ b : C.X (n + 1), C.d (n + 1) n b = C.iCycles n z := by
  let S := ShortComplex.mk (C.toCycles (n + 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n + 1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (n + 1) n (by simp))
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
    refine ⟨b, ?_⟩
    have he := congrArg (C.iCycles n) hb
    simpa only [S, ← ConcreteCategory.comp_apply, toCycles_i] using he
  · rintro ⟨b, hb⟩
    have he : C.toCycles (n + 1) n b = z := by
      apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
      simpa only [← ConcreteCategory.comp_apply, toCycles_i] using hb
    rw [← he]
    exact congrArg (fun f => f b) (C.toCycles_comp_homologyπ (n + 1) n)

/-- A class trivial at a point is trivial after restriction to a neighborhood
of that point inside its original support. -/
theorem exists_open_integralRelativeHomology_restriction_eq_zero [T2Space X]
    (K : Set X) (n : Nat) (a : integralRelativeHomology Kᶜ n)
    (x : X) (hx : x ∈ K)
    (ha : homologyMap (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n a = 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      homologyMap (integralRelativeRestriction
        (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K))) n a = 0 := by
  let C := integralChains X
  let R := integralRelativeChains Kᶜ
  let P := integralRelativeChains ({x}ᶜ : Set X)
  let f : R ⟶ P := integralRelativeRestriction
    (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (R.homologyπ n)).mp inferInstance a
  obtain ⟨c, hc⟩ := integralProjection_surjective (integralSubspaceChains Kᶜ) n
    (R.iCycles n z)
  have hlocal : P.homologyπ n (cyclesMap f n z) = 0 := by
    have he := congrArg (fun g => g z) (homologyπ_naturality (φ := f) (i := n))
    change homologyMap f n (R.homologyπ n z) = P.homologyπ n (cyclesMap f n z) at he
    rw [hz] at he
    exact he.symm.trans ha
  obtain ⟨b, hb⟩ := (homologyClass_zero_iff_boundary P n _).mp hlocal
  obtain ⟨d, hd⟩ := integralProjection_surjective
    (integralSubspaceChains ({x}ᶜ : Set X)) (n + 1) b
  have hp : (integralRelativeProjection ({x}ᶜ : Set X)).f n c =
      P.iCycles n (cyclesMap f n z) := by
    have he := congrArg (fun g => g.f n c)
      (integralRelativeRestriction_projection
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)))
    change f.f n ((integralRelativeProjection Kᶜ).f n c) =
      (integralRelativeProjection ({x}ᶜ : Set X)).f n c at he
    rw [hc] at he
    exact he.symm.trans
      (congrArg (fun g => g z) (cyclesMap_i f n)).symm
  have hres : (integralRelativeProjection ({x}ᶜ : Set X)).f n
      (c - C.d (n + 1) n d) = 0 := by
    rw [map_sub, hp]
    have he := congrArg (fun g => g d)
      ((integralRelativeProjection ({x}ᶜ : Set X)).comm (n + 1) n)
    change P.d (n + 1) n ((integralRelativeProjection ({x}ᶜ : Set X)).f (n + 1) d) =
      (integralRelativeProjection ({x}ᶜ : Set X)).f n (C.d (n + 1) n d) at he
    rw [hd, hb] at he
    exact sub_eq_zero.mpr he
  obtain ⟨U, hU, hxU, hresU⟩ :=
    exists_open_integralRelativeProjection_eq_zero n (c - C.d (n + 1) n d) x hres
  refine ⟨U, hU, hxU, ?_⟩
  let Q := integralRelativeChains (K ∩ U)ᶜ
  let g : R ⟶ Q := integralRelativeRestriction
    (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K))
  have hresQ : (integralRelativeProjection (K ∩ U)ᶜ).f n
      (c - C.d (n + 1) n d) = 0 := by
    have he := congrArg (fun k => k.f n (c - C.d (n + 1) n d))
      (integralRelativeRestriction_projection
        (Set.compl_subset_compl.mpr (Set.inter_subset_right : K ∩ U ⊆ U)))
    change (integralRelativeRestriction
        (Set.compl_subset_compl.mpr (Set.inter_subset_right : K ∩ U ⊆ U))).f n
        ((integralRelativeProjection Uᶜ).f n (c - C.d (n + 1) n d)) =
      (integralRelativeProjection (K ∩ U)ᶜ).f n
        (c - C.d (n + 1) n d) at he
    rw [hresU, map_zero] at he
    exact he.symm
  have hboundary : Q.homologyπ n (cyclesMap g n z) = 0 := by
    apply (homologyClass_zero_iff_boundary Q n _).mpr
    refine ⟨(integralRelativeProjection (K ∩ U)ᶜ).f (n + 1) d, ?_⟩
    have hdQ := congrArg (fun k => k d)
      ((integralRelativeProjection (K ∩ U)ᶜ).comm (n + 1) n)
    change Q.d (n + 1) n ((integralRelativeProjection (K ∩ U)ᶜ).f (n + 1) d) =
      (integralRelativeProjection (K ∩ U)ᶜ).f n (C.d (n + 1) n d) at hdQ
    rw [hdQ]
    rw [map_sub, sub_eq_zero] at hresQ
    rw [← hresQ]
    have he := congrArg (fun k => k.f n c)
      (integralRelativeRestriction_projection
        (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K)))
    change g.f n ((integralRelativeProjection Kᶜ).f n c) =
      (integralRelativeProjection (K ∩ U)ᶜ).f n c at he
    rw [hc] at he
    exact he.symm.trans
      (congrArg (fun k => k z) (cyclesMap_i g n)).symm
  have he := congrArg (fun k => k z) (homologyπ_naturality (φ := g) (i := n))
  change homologyMap g n (R.homologyπ n z) = Q.homologyπ n (cyclesMap g n z) at he
  rw [hz] at he
  exact he.trans hboundary

/-- A locally trivial support class vanishes on a compact relative
neighborhood, which can be chosen inside any prescribed open neighborhood. -/
theorem exists_compact_integralRelativeHomology_restriction_eq_zero
    [T2Space X] [RegularSpace X]
    (K : Set X) (hK : IsCompact K) (n : Nat) (a : integralRelativeHomology Kᶜ n)
    (x : X) (hx : x ∈ K)
    (ha : homologyMap (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n a = 0)
    (W : Set X) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V L : Set X, IsOpen V ∧ x ∈ V ∧ IsCompact L ∧ K ∩ V ⊆ L ∧
      ∃ hL : L ⊆ K ∩ W,
        homologyMap (integralRelativeRestriction
          (Set.compl_subset_compl.mpr (hL.trans Set.inter_subset_left))) n a = 0 := by
  obtain ⟨U, hU, hxU, haU⟩ :=
    exists_open_integralRelativeHomology_restriction_eq_zero K n a x hx ha
  obtain ⟨F, hxF, hF, hFUW⟩ := exists_mem_nhds_isClosed_subset
    ((hU.inter hW).mem_nhds ⟨hxU, hxW⟩)
  let L := K ∩ F
  have hLKU : L ⊆ K ∩ U := fun _ hy => ⟨hy.1, (hFUW hy.2).1⟩
  have hLKW : L ⊆ K ∩ W := fun _ hy => ⟨hy.1, (hFUW hy.2).2⟩
  refine ⟨interior F, L, isOpen_interior, mem_interior_iff_mem_nhds.mpr hxF,
    hK.inter_right hF, (fun _ hy => ⟨hy.1, interior_subset hy.2⟩), hLKW, ?_⟩
  have hc : (CategoryStruct.comp (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K)) ) (
        integralRelativeRestriction (Set.compl_subset_compl.mpr hLKU))) =
      integralRelativeRestriction
        (Set.compl_subset_compl.mpr (hLKW.trans Set.inter_subset_left)) := by
    rw [integralRelativeRestriction_comp]
  rw [← hc, homologyMap_comp]
  change homologyMap (integralRelativeRestriction (Set.compl_subset_compl.mpr hLKU)) n
    (homologyMap (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K))) n a) = 0
  rw [haU, map_zero]

end Poincare.Topology
end 

end FzIntegralSupportLocalization

noncomputable section FzIntegralSupportContinuity

/-!
# Enlarging the support of a relative singular class

Every relative class lifts to an open neighborhood of its support. An ambient
representative has a boundary with finitely many simplex images outside that
support. Their closed union can be removed, so the same representative is
already a relative cycle on an open neighborhood. No compactness assumption
on the original support is needed.
-/


section
open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_open_integralRelativeProjection_support [T2Space X]
    (K : Set X) (n : Nat) (c : (integralChains X).X n)
    (hc : (integralRelativeProjection Kᶜ).f n c = 0) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      (integralRelativeProjection Uᶜ).f n c = 0 := by
  classical
  let F := (integralChainCoordinates X n c).support
  let S : Set X := ⋃ s ∈ F, Set.range s
  have hS : IsCompact S :=
    F.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hr : c ∈ LinearMap.range ((integralSubspaceChains Kᶜ).f n).hom :=
    (integralProjection_eq_zero_iff (integralSubspaceChains Kᶜ) n c).mp hc
  have hs := (integral_subspace_range_iff Kᶜ n c).mp hr
  refine ⟨Sᶜ, hS.isClosed.isOpen_compl, ?_, ?_⟩
  · intro x hx hxS
    obtain ⟨s, hsf, hxs⟩ := Set.mem_iUnion₂.mp hxS
    exact hs s hsf hxs hx
  · rw [compl_compl]
    apply (integralProjection_eq_zero_iff (integralSubspaceChains S) n c).mpr
    apply (integral_subspace_range_iff S n c).mpr
    intro s hsf y hy
    exact Set.mem_iUnion₂.mpr ⟨s, hsf, hy⟩

/-- A relative class is the restriction of a class with open support. -/
theorem exists_open_integralRelativeHomology_lift [T2Space X]
    (K : Set X) (n : Nat) (a : integralRelativeHomology Kᶜ n) :
    ∃ U : Set X, IsOpen U ∧ ∃ hKU : K ⊆ U,
      ∃ b : integralRelativeHomology Uᶜ n,
        homologyMap (integralRelativeRestriction (Set.compl_subset_compl.mpr hKU)) n b = a := by
  let C := integralChains X
  let R := integralRelativeChains Kᶜ
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (R.homologyπ n)).mp inferInstance a
  obtain ⟨c, hc⟩ := integralProjection_surjective (integralSubspaceChains Kᶜ) n
    (R.iCycles n z)
  let m := (ComplexShape.down Nat).next n
  have hdc : (integralRelativeProjection Kᶜ).f m (C.d n m c) = 0 := by
    have he := congrArg (fun g => g c) ((integralRelativeProjection Kᶜ).comm n m)
    change R.d n m ((integralRelativeProjection Kᶜ).f n c) =
      (integralRelativeProjection Kᶜ).f m (C.d n m c) at he
    rw [hc] at he
    exact he.symm.trans (congrArg (fun g => g z) (R.iCycles_d n m))
  obtain ⟨U, hU, hKU, hdU⟩ :=
    exists_open_integralRelativeProjection_support K m (C.d n m c) hdc
  let Q := integralRelativeChains Uᶜ
  let f : Q ⟶ R := integralRelativeRestriction (Set.compl_subset_compl.mpr hKU)
  let q : Q.X n := (integralRelativeProjection Uᶜ).f n c
  have hq : (Q.sc n).g q = 0 := by
    have he := congrArg (fun g => g c) ((integralRelativeProjection Uᶜ).comm n m)
    change Q.d n m q = (integralRelativeProjection Uᶜ).f m (C.d n m c) at he
    exact he.trans hdU
  let w : Q.cycles n := (Q.sc n).cyclesMk q hq
  have hw : Q.iCycles n w = q := (Q.sc n).i_cyclesMk q hq
  have hwz : cyclesMap f n w = z := by
    apply (ModuleCat.mono_iff_injective (R.iCycles n)).mp inferInstance
    have hi := congrArg (fun g => g w) (cyclesMap_i f n)
    change R.iCycles n (cyclesMap f n w) = f.f n (Q.iCycles n w) at hi
    rw [hi, hw]
    have hp := congrArg (fun g => g.f n c)
      (integralRelativeRestriction_projection (Set.compl_subset_compl.mpr hKU))
    change f.f n q = (integralRelativeProjection Kᶜ).f n c at hp
    exact hp.trans hc
  refine ⟨U, hU, hKU, Q.homologyπ n w, ?_⟩
  have he := congrArg (fun g => g w) (homologyπ_naturality (φ := f) (i := n))
  change homologyMap f n (Q.homologyπ n w) = R.homologyπ n (cyclesMap f n w) at he
  rw [hwz, hz] at he
  exact he

/-- Every intermediate support in a sufficiently small open neighborhood
admits a class restricting to the given class. -/
theorem exists_open_integralRelativeHomology_lift_forall [T2Space X]
    (K : Set X) (n : Nat) (a : integralRelativeHomology Kᶜ n) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ (L : Set X) (hKL : K ⊆ L), L ⊆ U →
        ∃ b : integralRelativeHomology Lᶜ n,
          homologyMap (integralRelativeRestriction
            (Set.compl_subset_compl.mpr hKL)) n b = a := by
  obtain ⟨U, hU, hKU, b, hb⟩ := exists_open_integralRelativeHomology_lift K n a
  refine ⟨U, hU, hKU, ?_⟩
  intro L hKL hLU
  refine ⟨homologyMap (integralRelativeRestriction (Set.compl_subset_compl.mpr hLU)) n b, ?_⟩
  have hc : (CategoryStruct.comp (integralRelativeRestriction (Set.compl_subset_compl.mpr hLU) ) (
      integralRelativeRestriction (Set.compl_subset_compl.mpr hKL))) =
        integralRelativeRestriction (Set.compl_subset_compl.mpr hKU) := by
    rw [integralRelativeRestriction_comp]
  have he := congrArg (fun g : integralRelativeChains Uᶜ ⟶ integralRelativeChains Kᶜ =>
    homologyMap g n b) hc
  rw [homologyMap_comp] at he
  exact he.trans hb

end Poincare.Topology
end 

end FzIntegralSupportContinuity

noncomputable section GnIntegralCompactSupport

/-!
# Integral homology supported on compact Euclidean sets

Compact supports admit finite closed-ball neighborhoods.  Outward continuity
of relative cycles and the finite Mayer--Vietoris induction therefore pass
the convex calculations to arbitrary compact subsets of Euclidean space.
-/


section
open CategoryTheory Limits HomologicalComplex Metric Set

universe u v

namespace Poincare.Topology

theorem exists_finite_closedBall_support_neighborhood
    {X : Type u} [PseudoMetricSpace X]
    (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : Real, 0 < r ∧ ∃ s : Finset K,
      K ⊆ interior (⋃ x ∈ s, closedBall (x : X) r) ∧
      (⋃ x ∈ s, closedBall (x : X) r) ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : X) r)
    (fun _ => isOpen_ball) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hr⟩)
  refine ⟨r, hr, s, ?_, ?_⟩
  · apply hs.trans
    apply (isOpen_biUnion (fun x _ => isOpen_ball)).subset_interior_iff.mpr
    exact iUnion₂_mono (fun _ _ => ball_subset_closedBall)
  · exact iUnion₂_subset (fun x _ => (closedBall_subset_cthickening x.property r).trans hrU)

variable {k : Nat}

private theorem euclidean_compact_convex_above
    (K : Set (EuclideanSpace Real (Fin (k + 2)))) (hK : IsCompact K)
    (hc : Convex Real K) (n : Nat) :
    IsZero (integralSupportHomology K (n + (k + 3))) := by
  rcases K.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]
    exact integralSupportHomology_empty_isZero (n + (k + 3))
  · exact integralEuclideanCompactConvexSupportAbove_isZero K hK hc x hx n

private theorem euclidean_convex_intersection_above
    {ι : Type v} (s : Finset ι) (F : ι → Set (EuclideanSpace Real (Fin (k + 2))))
    (hs : s.Nonempty) (hF : ∀ i ∈ s, IsCompact (F i))
    (hc : ∀ i ∈ s, Convex Real (F i)) (n : Nat) :
    IsZero (integralSupportHomology (⋂ i ∈ s, F i) (n + (k + 3))) := by
  obtain ⟨j, hj⟩ := hs
  apply euclidean_compact_convex_above
  · exact (hF j hj).of_isClosed_subset
      (isClosed_iInter (fun i => isClosed_iInter (fun hi => (hF i hi).isClosed)))
      (fun x hx => mem_iInter.mp (mem_iInter.mp hx j) hj)
  · exact convex_iInter (fun i => convex_iInter (fun hi => hc i hi))

theorem integralEuclideanFiniteConvexSupportAbove_isZero
    {ι : Type v} (s : Finset ι) (F : ι → Set (EuclideanSpace Real (Fin (k + 2))))
    (hF : ∀ i ∈ s, IsCompact (F i)) (hc : ∀ i ∈ s, Convex Real (F i)) (n : Nat) :
    IsZero (integralSupportHomology (⋃ i ∈ s, F i) (n + (k + 3))) := by
  apply integralSupportHomology_finset_union_isZero s F (k + 3) (fun i hi => (hF i hi).isClosed)
  intro t ht htn m
  exact euclidean_convex_intersection_above t F htn
    (fun i hi => hF i (ht hi)) (fun i hi => hc i (ht hi)) m

theorem integralEuclideanFiniteConvexSupportTop_detected
    {ι : Type v} (s : Finset ι) (F : ι → Set (EuclideanSpace Real (Fin (k + 2))))
    (hF : ∀ i ∈ s, IsCompact (F i)) (hc : ∀ i ∈ s, Convex Real (F i))
    (a : integralSupportHomology (⋃ i ∈ s, F i) (k + 2))
    (ha : ∀ x, ∀ hx : x ∈ ⋃ i ∈ s, F i,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) (k + 2) a = 0) :
    a = 0 := by
  apply integralSupportHomology_finset_union_detected s F (k + 2)
    (fun i hi => (hF i hi).isClosed) ?_ ?_ a ha
  · intro t ht htn n
    exact euclidean_convex_intersection_above t F htn
      (fun i hi => hF i (ht hi)) (fun i hi => hc i (ht hi)) n
  · intro i hi b hb
    rcases (F i).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · have hz : IsZero (integralSupportHomology (F i) (k + 2)) := by
        rw [h]
        exact integralSupportHomology_empty_isZero (k + 2)
      exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _
    · let := integralCompactConvexSupportRestriction_homology_isIso
        (F i) (hF i hi) (hc i hi) x hx (k + 2)
      apply (ModuleCat.mono_iff_injective
        (integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) (k + 2))).mp inferInstance
      rw [map_zero]
      exact hb x hx

/-- Relative integral homology above the dimension vanishes for every
compact support in Euclidean space. -/
theorem integralEuclideanCompactSupportAbove_isZero
    (K : Set (EuclideanSpace Real (Fin (k + 2)))) (hK : IsCompact K) (n : Nat) :
    IsZero (integralSupportHomology K (n + (k + 3))) := by
  have hz : ∀ a : integralSupportHomology K (n + (k + 3)), a = 0 := by
    intro a
    obtain ⟨U, hU, hKU, hlift⟩ := exists_open_integralRelativeHomology_lift_forall K (n + (k + 3)) a
    obtain ⟨r, hr, s, hKs, hsU⟩ :=
      exists_finite_closedBall_support_neighborhood K U hK hU hKU
    let L := ⋃ x ∈ s, closedBall (x : EuclideanSpace Real (Fin (k + 2))) r
    have hKL : K ⊆ L := hKs.trans interior_subset
    obtain ⟨b, hb⟩ := hlift L hKL hsU
    have hb₀ : b = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp
        (integralEuclideanFiniteConvexSupportAbove_isZero s
          (fun x : K => closedBall (x : EuclideanSpace Real (Fin (k + 2))) r)
          (fun _ _ => isCompact_closedBall _ _) (fun _ _ => convex_closedBall _ _) n)).elim _ _
    rw [hb₀, map_zero] at hb
    exact hb.symm
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- A top-degree class with compact Euclidean support is determined by its
restrictions at all points of that support. -/
theorem integralEuclideanCompactSupportTop_detected
    (K : Set (EuclideanSpace Real (Fin (k + 2)))) (hK : IsCompact K)
    (a : integralSupportHomology K (k + 2))
    (ha : ∀ x, ∀ hx : x ∈ K,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) (k + 2) a = 0) :
    a = 0 := by
  obtain ⟨U, hU, hKU, b, hb⟩ := exists_open_integralRelativeHomology_lift K (k + 2) a
  change integralSupportHomologyRestriction hKU (k + 2) b = a at hb
  have hlocal : ∀ x : K,
      integralSupportHomologyRestriction
        (singleton_subset_iff.mpr (hKU x.property)) (k + 2) b = 0 := by
    intro x
    have he := congrArg (fun f => f b)
      (integralSupportHomologyRestriction_comp
        (singleton_subset_iff.mpr x.property) hKU (k + 2))
    change integralSupportHomologyRestriction (singleton_subset_iff.mpr x.property) (k + 2)
        (integralSupportHomologyRestriction hKU (k + 2) b) =
      integralSupportHomologyRestriction
        (singleton_subset_iff.mpr (hKU x.property)) (k + 2) b at he
    rw [hb] at he
    exact he.symm.trans (ha x x.property)
  have hnear : ∀ x : K, ∃ V : Set (EuclideanSpace Real (Fin (k + 2))),
      IsOpen V ∧ (x : EuclideanSpace Real (Fin (k + 2))) ∈ V ∧
        integralSupportHomologyRestriction (inter_subset_left : U ∩ V ⊆ U) (k + 2) b = 0 := by
    intro x
    exact exists_open_integralRelativeHomology_restriction_eq_zero
      U (k + 2) b x (hKU x.property) (hlocal x)
  choose V hV hxV hbV using hnear
  let W := U ∩ ⋃ x : K, V x
  have hW : IsOpen W := hU.inter (isOpen_iUnion hV)
  have hKW : K ⊆ W := fun x hx => ⟨hKU hx, mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩⟩
  have hWlocal : ∀ y, ∀ hy : y ∈ W,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1) (k + 2) b = 0 := by
    intro y hy
    obtain ⟨x, hyV⟩ := mem_iUnion.mp hy.2
    have hsmall : {y} ⊆ U ∩ V x := singleton_subset_iff.mpr ⟨hy.1, hyV⟩
    have he := congrArg (fun f => f b)
      (integralSupportHomologyRestriction_comp hsmall inter_subset_left (k + 2))
    change integralSupportHomologyRestriction hsmall (k + 2)
        (integralSupportHomologyRestriction inter_subset_left (k + 2) b) =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy.1) (k + 2) b at he
    rw [hbV x, map_zero] at he
    exact he.symm
  obtain ⟨r, hr, s, hKs, hsW⟩ :=
    exists_finite_closedBall_support_neighborhood K W hK hW hKW
  let L := ⋃ x ∈ s, closedBall (x : EuclideanSpace Real (Fin (k + 2))) r
  have hKL : K ⊆ L := hKs.trans interior_subset
  have hLU : L ⊆ U := hsW.trans inter_subset_left
  let c : integralSupportHomology L (k + 2) := integralSupportHomologyRestriction hLU (k + 2) b
  have hc : c = 0 := by
    apply integralEuclideanFiniteConvexSupportTop_detected s
      (fun x : K => closedBall (x : EuclideanSpace Real (Fin (k + 2))) r)
      (fun _ _ => isCompact_closedBall _ _) (fun _ _ => convex_closedBall _ _)
    intro y hy
    have he := congrArg (fun f => f b)
      (integralSupportHomologyRestriction_comp (singleton_subset_iff.mpr hy) hLU (k + 2))
    change integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) (k + 2) c =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr (hLU hy)) (k + 2) b at he
    exact he.trans (hWlocal y (hsW hy))
  have hca : integralSupportHomologyRestriction hKL (k + 2) c = a := by
    dsimp only [c]
    rw [← ConcreteCategory.comp_apply, integralSupportHomologyRestriction_comp]
    exact hb
  rw [hc, map_zero] at hca
  exact hca.symm

end Poincare.Topology
end 

end GnIntegralCompactSupport

noncomputable section GnIntegralManifoldSupport

/-!
# Compact support homology on three-manifolds

Open charts transport the Euclidean compact-support calculation, including
its singleton restriction maps. Finite compact support gluing then proves
higher-degree vanishing and top-degree point detection on the manifold.
-/


section
open CategoryTheory Limits
open Set

universe u

namespace Poincare.Topology

variable {k : Nat}

theorem integralManifoldCompactSupport
    {M : Type} [TopologicalSpace M] [T2Space M] [RegularSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin (k + 2))) M]
    (K : Set M) (hK : IsCompact K) :
    (∀ n : Nat, IsZero (integralSupportHomology K (n + (k + 3)))) ∧
      IntegralSupportDetected K (k + 2) := by
  apply integralCompactSupport_local_to_global K hK (k + 2)
  intro x hx
  let e := chartAt (EuclideanSpace Real (Fin (k + 2))) x
  refine ⟨e.source, e.open_source, mem_chart_source _ x, ?_⟩
  intro L hL hLs
  have himage : IsCompact (e '' L) :=
    hL.image_of_continuousOn (e.continuousOn.mono hLs)
  constructor
  · intro n
    let E := (integralChartSupportHomologyIso e L hL hLs (n + (k + 3))).toLinearEquiv
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (integralEuclideanCompactSupportAbove_isZero (e '' L) himage n)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun a b => E.injective (hz.elim (E a) (E b))⟩
  · intro a ha
    let E := (integralChartSupportHomologyIso e L hL hLs (k + 2)).toLinearEquiv
    apply E.injective
    rw [map_zero]
    apply integralEuclideanCompactSupportTop_detected (e '' L) himage (E a)
    rintro y ⟨z, hz, rfl⟩
    have he := (ConcreteCategory.congr_hom (integralChartSupportHomologyIso_naturality e hL isCompact_singleton hLs
      (singleton_subset_iff.mpr (hLs hz)) (singleton_subset_iff.mpr hz) (k + 2)) a).symm
    change (integralChartSupportHomologyIso e {z} isCompact_singleton _ (k + 2)).hom
      (integralSupportHomologyRestriction (singleton_subset_iff.mpr hz) (k + 2) a) =
      integralSupportHomologyRestriction (Set.image_mono (f := e) (singleton_subset_iff.mpr hz)) (k + 2) (E a) at he
    rw [ha z hz, map_zero] at he
    have himg : e '' ({z} : Set M) = ({e z} : Set (EuclideanSpace Real (Fin (k + 2)))) :=
      Set.image_singleton
    have hs : ({e z} : Set (EuclideanSpace Real (Fin (k + 2)))) ⊆ e '' ({z} : Set M) := by
      rw [himg]
    have hm := congrArg (fun f => f (E a))
      (integralSupportHomologyRestriction_comp hs
        (Set.image_mono (f := e) (singleton_subset_iff.mpr hz)) (k + 2))
    change integralSupportHomologyRestriction hs (k + 2)
        (integralSupportHomologyRestriction
          (Set.image_mono (f := e) (singleton_subset_iff.mpr hz)) (k + 2) (E a)) =
      integralSupportHomologyRestriction
        (hs.trans (Set.image_mono (f := e) (singleton_subset_iff.mpr hz))) (k + 2) (E a) at hm
    rw [← he, map_zero] at hm
    exact hm.symm

end Poincare.Topology
end 

end GnIntegralManifoldSupport

noncomputable section FzIntegralSupportUniv

/-!
# Absolute homology as homology supported on the whole space

The singular chains of the empty subspace vanish in every degree. Thus the
actual quotient projection for the pair with empty subspace is an isomorphism.
-/


section
open CategoryTheory Limits HomologicalComplex Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSubspaceChains_empty : integralSubspaceChains (∅ : Set X) = 0 := by
  classical
  have hzero (n : Nat) (a : (integralChains (∅ : Set X)).X n) : a = 0 := by
    apply (integralChainCoordinates (∅ : Set X) n).injective
    ext s
    exact (s ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex Real 0⟩).property.elim
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rw [hzero n a]
  simp

theorem integralRelativeProjection_empty_isIso :
    IsIso (integralRelativeProjection (∅ : Set X)) := by
  change IsIso (cokernel.π (integralSubspaceChains (∅ : Set X)))
  rw [integralSubspaceChains_empty]
  infer_instance

def integralHomologySupportUnivIso (X : Type u) [TopologicalSpace X] (n : Nat) :
    integralHomology X n ≅ integralSupportHomology (univ : Set X) n := by
  let := integralRelativeProjection_empty_isIso (X := X)
  have : IsIso (integralToRelativeHomology (∅ : Set X) n) := by
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).map
      (integralRelativeProjection (∅ : Set X)))
    infer_instance
  change integralHomology X n ≅ integralRelativeHomology (univ : Set X)ᶜ n
  rw [Set.compl_univ]
  exact asIso (integralToRelativeHomology (∅ : Set X) n)

end Poincare.Topology
end 

end FzIntegralSupportUniv

noncomputable section CoeffBridge

open CategoryTheory Limits AlgebraicTopology
section
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

def chainIso (X : TopCat.{0}) :
    ((singularChainComplexFunctor AddCommGrpCat).obj (U.obj R)).obj X ≅
    (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj R).obj X) := by
  let S := TopCat.toSSet.obj X
  let A := S ⋙ sigmaConst.obj R
  let e := (alternatingFaceMapComplex AddCommGrpCat).mapIso (Functor.isoWhiskerLeft S freeIso)
  have q := Functor.congr_obj (map_alternatingFaceMapComplex U) A
  exact e ≪≫ (eqToIso q).symm

def homologyIso (X : TopCat.{0}) (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj X ≅
    U.obj (((singularHomologyFunctor (ModuleCat ℤ) n).obj R).obj X) := by
  let C := ((singularChainComplexFunctor (ModuleCat ℤ)).obj R).obj X
  let e := ((singularHomologyFunctor AddCommGrpCat n).mapIso coeff.symm).app X
  let q := (HomologicalComplex.homologyFunctor AddCommGrpCat _ n).mapIso (chainIso X)
  exact e ≪≫ q ≪≫ (C.sc n).mapHomologyIso U

end IntegralComparison
end 

end CoeffBridge

noncomputable section GnMoveEuclid

open Set Metric Filter
open scoped Topology
section
namespace LocalMove
abbrev E (d : Nat) := EuclideanSpace ℝ (Fin d)
variable {d : Nat}
def weight (c : (E d)) (r : ℝ) (v : (E d)) : ℝ := max 0 (min 1 ((5*r - dist v c)/r))
lemma weight_bounds (c : (E d)) (r : ℝ) (v : (E d)) : 0 ≤ weight c r v ∧ weight c r v ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma weight_one {c v : (E d)} {r : ℝ} (hr : 0 < r) (hv : dist v c ≤ 4*r) :
    weight c r v = 1 := by
  have h : 1 ≤ (5*r-dist v c)/r := (le_div_iff₀ hr).mpr (by linarith)
  simp [weight,min_eq_left h]
lemma weight_zero {c v : (E d)} {r : ℝ} (hr : 0 < r) (hv : 5*r ≤ dist v c) :
    weight c r v = 0 := by
  have h : (5*r-dist v c)/r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  exact max_eq_left ((min_le_right _ _).trans h)
lemma weight_cont (c : (E d)) (r : ℝ) : Continuous (weight c r) := by unfold weight; fun_prop

def shift (c : (E d)) (r : ℝ) (a b : (E d)) (t : unitInterval) (v : (E d)) : (E d) :=
  v + ((t.val * weight c r v) • (b-a))
lemma shift_cont (c : (E d)) (r : ℝ) (a b : (E d)) : Continuous (fun p : unitInterval × (E d) => shift c r a b p.1 p.2) := by
  unfold shift
  have h := (weight_cont c r).comp (continuous_snd : Continuous (Prod.snd : unitInterval × (E d) → (E d)))
  fun_prop
lemma shift_dist {c a b : (E d)} {r : ℝ} (ha : dist a c < r) (hb : dist b c < r)
    (t : unitInterval) (v : (E d)) : dist (shift c r a b t v) v < 2*r := by
  have h := weight_bounds c r v
  have h0 : 0 ≤ t.val * weight c r v := mul_nonneg t.property.1 h.1
  have h1 : t.val * weight c r v ≤ 1 := mul_le_one₀ t.property.2 h.1 h.2
  have hd : dist b a < 2*r := by linarith [dist_triangle_right b a c]
  simpa [shift,dist_eq_norm, norm_smul,Real.norm_eq_abs,abs_of_nonneg h0,abs_of_nonneg t.property.1,abs_of_nonneg h.1] using
    (le_trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg (b-a))) (one_mul ‖b-a‖).le).trans_lt (by simpa [dist_eq_norm] using hd)
lemma shift_target {c a b : (E d)} {r : ℝ} (hr : 0 < r) (ha : dist a c < r) (hb : dist b c < r)
    {V : Set (E d)} (hc : closedBall c (8*r) ⊆ V) {v : (E d)} (hv : v ∈ V) (t : unitInterval) :
    shift c r a b t v ∈ V := by
  by_cases h : 5*r ≤ dist v c
  · simpa [shift,weight_zero hr h] using hv
  · apply hc
    rw [mem_closedBall]
    linarith [dist_triangle (shift c r a b t v) v c,shift_dist ha hb t v]
lemma shift_hit {c a b : (E d)} {r : ℝ} (hr : 0 < r) (ha : dist a c < r) (hb : dist b c < r)
    {v : (E d)} (h : shift c r a b 1 v = b) : v = a := by
  have hd := shift_dist ha hb 1 v
  rw [h, dist_comm] at hd
  have hv : dist v c ≤ 4*r := by linarith [dist_triangle v b c]
  have eq : v + (b-a) = b := by simpa [shift,weight_one hr hv] using h
  calc v = (v + (b-a)) - (b-a) := by abel
       _ = b - (b-a) := by rw [eq]
       _ = a := by abel

end LocalMove
end 

end GnMoveEuclid

noncomputable section GnMoveChart

open Set Metric Filter CategoryTheory
open scoped Topology
section
namespace LocalMove

variable {d : Nat}

lemma chart_motion {M : Type} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M (E d)) (c : (E d)) {r : ℝ} (hr : 0 < r)
    (hV : closedBall c (8*r) ⊆ e.target)
    {a b : M} (ha : a ∈ e.source) (hb : b ∈ e.source)
    (ha' : dist (e a) c < r) (hb' : dist (e b) c < r) :
    ∃ f : TopCat.of M ⟶ TopCat.of M, Nonempty (TopCat.Homotopy (𝟙 _) f) ∧
      ∀ z, f z = b → z = a := by
  classical
  let g := shift c r (e a) (e b)
  let m (p : unitInterval × M) := if p.2 ∈ e.source then e.symm (g p.1 (e p.2)) else p.2
  let K := e.symm '' closedBall c (5*r)
  have inner : closedBall c (5*r) ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith : 5*r ≤ 8*r)).trans hV
  have hK : IsCompact K := (isCompact_closedBall c (5*r)).image_of_continuousOn
    (e.continuousOn_symm.mono inner)
  have subK : K ⊆ e.source := by
    rintro _ ⟨w,hw,rfl⟩
    exact e.map_target (inner hw)
  have ht (t : unitInterval) {z : M} (hz : z ∈ e.source) : g t (e z) ∈ e.target :=
    shift_target hr ha' hb' hV (e.map_source hz) t
  have outside (p : unitInterval × M) (hp : p.2 ∉ K) : m p = p.2 := by
    by_cases hs : p.2 ∈ e.source
    · have hfar : 5*r ≤ dist (e p.2) c := by
        by_contra! hh
        exact hp ⟨e p.2,mem_closedBall.mpr hh.le,e.left_inv hs⟩
      simp [m,hs,g,shift,weight_zero hr hfar,e.left_inv hs]
    · simp [m,hs]
  have hm : Continuous m := continuous_iff_continuousAt.mpr fun p => by
    by_cases hs : p.2 ∈ e.source
    · have hpair : ContinuousAt (fun q : unitInterval × M => (q.1,e q.2)) p :=
        continuousAt_fst.prodMk ((e.continuousAt hs).comp continuousAt_snd)
      have hgs : ContinuousAt (fun q : unitInterval × M => g q.1 (e q.2)) p :=
        (shift_cont c r (e a) (e b)).continuousAt.comp hpair
      have hc : ContinuousAt (fun q : unitInterval × M => e.symm (g q.1 (e q.2))) p :=
        (e.continuousAt_symm (ht p.1 hs)).comp' (f := fun q : unitInterval × M => g q.1 (e q.2)) hgs
      apply hc.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hs)] with q hq
      exact if_pos hq
    · apply (continuous_snd.continuousAt : ContinuousAt (Prod.snd : unitInterval × M → M) p).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds (fun h => hs (subK h)))] with q hq
      exact outside q hq
  let f : TopCat.of M ⟶ TopCat.of M := TopCat.ofHom
    ⟨fun z => m (1,z), hm.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨f,?_,?_⟩
  · refine ⟨{ toFun := m
              continuous_toFun := hm
              map_one_left := fun _ => rfl
              map_zero_left := ?_ }⟩
    intro z
    change m (0,z) = z
    by_cases h : z ∈ e.source <;> simp [m,h,g,shift,e.left_inv]
  · intro z hz
    change m (1,z) = b at hz
    by_cases hs : z ∈ e.source
    · have h' : e.symm (g 1 (e z)) = b := by simpa [m,hs] using hz
      have eq : g 1 (e z) = e b := (e.right_inv (ht 1 hs)).symm.trans (congrArg e h')
      have h := shift_hit hr ha' hb' eq
      exact e.injOn hs ha h
    · have eq : z = b := by simpa [m,hs] using hz
      exact (hs (eq ▸ hb)).elim

lemma move_neighbors {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (E d) M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ a ∈ U, ∀ b ∈ U,
      ∃ f : TopCat.of M ⟶ TopCat.of M, Nonempty (TopCat.Homotopy (𝟙 _) f) ∧
        ∀ z, f z = b → z = a := by
  let e := chartAt (E d) x
  have hx : x ∈ e.source := mem_chart_source (E d) x
  obtain ⟨s,hs,hsT⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let r := s/10
  have hr : 0 < r := by dsimp [r]; positivity
  have hV : closedBall (e x) (8*r) ⊆ e.target :=
    (closedBall_subset_ball (by dsimp [r]; linarith : 8*r < s)).trans hsT
  refine ⟨e.source ∩ e ⁻¹' ball (e x) r,e.isOpen_inter_preimage isOpen_ball,⟨hx,mem_ball_self hr⟩,?_⟩
  intro a ha b hb
  exact chart_motion e _ hr hV ha.1 hb.1 ha.2 hb.2

end LocalMove
end 

end GnMoveChart

noncomputable section GnManCore

open Set Filter CategoryTheory Limits AlgebraicTopology HomologicalComplex
open Poincare.Topology
open scoped Topology
section
namespace VanishTop

lemma compact_carrier {M : Type} [TopologicalSpace M] (n : ℕ) (a : integralHomology M n) :
    ∃ K : Set M, IsCompact K ∧ ∀ L : Set M, Disjoint K L → integralToRelativeHomology Lᶜ n a = 0 := by
  classical
  let C := integralChains M
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance a
  let c := C.iCycles n z
  let S := (integralChainCoordinates M n c).support
  let K : Set M := ⋃ s ∈ S, Set.range s
  refine ⟨K,S.finite_toSet.isCompact_biUnion (fun s _ => isCompact_range s.continuous),?_⟩
  intro L hL
  have support : c ∈ LinearMap.range ((integralSubspaceChains Lᶜ).f n).hom := by
    apply (integral_subspace_range_iff _ _ _).mpr
    intro s hs p hp hpl
    exact Set.disjoint_left.mp hL (Set.mem_iUnion₂.mpr ⟨s,hs,hp⟩) hpl
  obtain ⟨u,hu⟩ := support
  let f := integralRelativeProjection Lᶜ
  let D := integralRelativeChains Lᶜ
  have zero : f.f n c = 0 := by
    rw [←hu]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (cokernel.condition (integralSubspaceChains Lᶜ)) n) u
  have hz : cyclesMap f n z = 0 := by
    apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    rw [map_zero]
    exact (ConcreteCategory.congr_hom (cyclesMap_i f n) z).trans zero
  exact (ConcreteCategory.congr_hom (homologyπ_naturality f n) z).trans
    (by change D.homologyπ n (cyclesMap f n z) = 0; rw [hz,map_zero])

lemma carry_point {M : Type} [TopologicalSpace M] (n : ℕ) (a : integralHomology M n) {x y : M}
    (f : TopCat.of M ⟶ TopCat.of M) (hf : TopCat.Homotopy (𝟙 _) f) (hit : ∀ p, f p = y → p = x)
    (h : integralToRelativeHomology ({x}ᶜ : Set M) n a = 0) :
    integralToRelativeHomology ({y}ᶜ : Set M) n a = 0 := by
  have maps : Set.MapsTo f.hom ({x}ᶜ : Set M) {y}ᶜ := fun p hp hy => hp (hit p hy)
  let v := integralRelativeMap f.hom maps
  have ev := integralRelativeMap_projection f.hom maps
  have e := congrArg (fun k => homologyMap k n) ev
  rw [homologyMap_comp,homologyMap_comp] at e
  have act : homologyMap (integralChainsFunctor.map f) n = 𝟙 _ := by
    have h' := hf.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
    change homologyMap (integralChainsFunctor.map (𝟙 _)) n = homologyMap (integralChainsFunctor.map f) n at h'
    exact h'.symm.trans ((congrArg (fun k => homologyMap k n) (integralChainsFunctor.map_id (TopCat.of M))).trans (homologyMap_id _ _))
  have eq := ConcreteCategory.congr_hom e a
  change homologyMap v n (integralToRelativeHomology ({x}ᶜ : Set M) n a) =
    integralToRelativeHomology ({y}ᶜ : Set M) n (homologyMap (integralChainsFunctor.map f) n a) at eq
  rw [h,map_zero,act] at eq
  exact eq.symm

lemma punctures {d : Nat} {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (LocalMove.E d) M] [ConnectedSpace M]
    (hM : ¬CompactSpace M) (n : ℕ) (a : integralHomology M n) :
    ∀ x : M, integralToRelativeHomology ({x}ᶜ : Set M) n a = 0 := by
  let S : Set M := fun x => integralToRelativeHomology ({x}ᶜ : Set M) n a = 0
  have near (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ u ∈ U, ∀ v ∈ U, u ∈ S → v ∈ S := by
    obtain ⟨U,hU,hx,hm⟩ := LocalMove.move_neighbors (d := d) x
    refine ⟨U,hU,hx,?_⟩
    intro u hu v hv
    obtain ⟨f,⟨hf⟩,hit⟩ := hm u hu v hv
    exact carry_point n a f hf hit
  have ho : IsOpen S := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨U,hU,hxU,hm⟩ := near x
    exact ⟨U,fun y hy => hm x hxU y hy hx,hU,hxU⟩
  have hc : IsOpen Sᶜ := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨U,hU,hxU,hm⟩ := near x
    exact ⟨U,fun y hy h => hx (hm y hy x hxU h),hU,hxU⟩
  obtain ⟨K,hK,hout⟩ := compact_carrier n a
  obtain ⟨x,hx⟩ : ∃ x, x ∉ K := by
    by_contra! h
    exact hM ⟨Set.eq_univ_of_forall h ▸ hK⟩
  have hn : S.Nonempty := ⟨x,hout {x} (Set.disjoint_singleton_right.mpr hx)⟩
  have top : S = univ := (isClopen_iff.mp ⟨isOpen_compl_iff.mp hc,ho⟩).resolve_left hn.ne_empty
  exact fun y => (show y ∈ S from top ▸ mem_univ y)
end VanishTop
end 

end GnManCore

open Set CategoryTheory Limits AlgebraicTopology HomologicalComplex
open Poincare.Topology
noncomputable section
namespace VanishTop

variable {k : Nat}

lemma region_restrict {M : Type} [TopologicalSpace M] (a : integralHomology M (k + 2))
    {K L : Set M} (h : K ⊆ L) :
    integralSupportHomologyRestriction h (k + 2) (integralToRelativeHomology Lᶜ (k + 2) a) =
      integralToRelativeHomology Kᶜ (k + 2) a := by
  have eq := congrArg (fun f => homologyMap f (k + 2)) (integralSupportRestriction_projection h)
  rw [homologyMap_comp] at eq
  exact ConcreteCategory.congr_hom eq a

lemma no_top (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (LocalMove.E (k + 2)) M] [ConnectedSpace M]
    (hM : ¬ CompactSpace M) (a : integralHomology M (k + 2)) : a = 0 := by
  classical
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (LocalMove.E (k + 2)) M
  obtain ⟨K,hK,hs⟩ := compact_carrier (k + 2) a
  obtain ⟨D,hD,hKD⟩ := exists_compact_superset hK
  let L := (interior D)ᶜ
  have hL : IsClosed L := isOpen_interior.isClosed_compl
  have hI : IsCompact (D ∩ L) := hD.inter_right hL
  have h₄ : IsZero (integralSupportHomology (D ∩ L) ((k + 2)+1)) := by
    simpa only [Nat.zero_add] using (integralManifoldCompactSupport (k := k) _ hI).1 0
  have hcover : D ∪ L = univ := Set.eq_univ_of_forall fun x => by
    by_cases hx : x ∈ interior D
    · exact Or.inl (interior_subset hx)
    · exact Or.inr hx
  have dval : integralToRelativeHomology Dᶜ (k + 2) a = 0 := by
    apply (integralManifoldCompactSupport (k := k) D hD).2
    intro z hz
    exact (region_restrict (k := k) a _).trans (punctures (d := k + 2) hM (k + 2) a z)
  have lval : integralToRelativeHomology Lᶜ (k + 2) a = 0 :=
    hs L (Set.disjoint_left.mpr (fun _ hk hl => hl (hKD hk)))
  have union_zero : integralToRelativeHomology (D ∪ L)ᶜ (k + 2) a = 0 := by
    apply integralSupportHomology_union_ext D L hD.isClosed hL (k + 2) h₄
    · rw [map_zero]
      exact (region_restrict (k := k) a _).trans dval
    · rw [map_zero]
      exact (region_restrict (k := k) a _).trans lval
  rw [hcover,Set.compl_univ] at union_zero
  letI := integralRelativeProjection_empty_isIso (X := M)
  haveI : IsIso (integralToRelativeHomology (∅ : Set M) (k + 2)) := by
    change IsIso ((homologyFunctor (ModuleCat ℤ) _ (k + 2)).map (integralRelativeProjection (∅ : Set M)))
    infer_instance
  apply (ModuleCat.mono_iff_injective (integralToRelativeHomology (∅ : Set M) (k + 2))).mp inferInstance
  rwa [map_zero]

end VanishTop
end

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1.H2 := by
  intro M _ _ _ _ hM
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  let e := IntegralComparison.homologyIso (TopCat.of M) 2
  have inj := (AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance
  refine ⟨fun a b => inj ?_⟩
  exact (VanishTop.no_top (k := 0) M hM (e.hom a)).trans (VanishTop.no_top (k := 0) M hM (e.hom b)).symm

