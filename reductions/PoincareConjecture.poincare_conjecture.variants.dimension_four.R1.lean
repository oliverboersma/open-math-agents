import FormalConjectures.Millennium.Poincare
import Mathlib

/-!
For a homotopy four-sphere, compactness, simple connectivity, and vanishing of
second integral homology give the hypotheses for the zero-intersection-form case
of Freedman's classification. The remaining geometric input is phrased as a
Euclidean puncture. One-point compactification recovers the homeomorphism.

The homotopy invariance argument is adapted from @tamoghnokandar, merged PR 3548.
-/

open CategoryTheory Limits AlgebraicTopology Set
open scoped ContinuousMap

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1

lemma homotopy_homology {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (n : Nat) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) ≅
      (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)
  let f := TopCat.ofHom e.toFun
  let g := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    exact (show TopCat.Homotopy (CategoryStruct.comp f g) (𝟙 (TopCat.of X)) from h).congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    exact (show TopCat.Homotopy (CategoryStruct.comp g f) (𝟙 (TopCat.of Y)) from h).congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n

lemma compact_euclidean_puncture {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (p : M) (n : Nat) (e : ↥({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) := by
  let P := ({p}ᶜ : Set M)
  let t := OnePoint.equivOfIsEmbeddingOfRangeEq p (Subtype.val : P → M)
    Topology.IsEmbedding.subtypeVal (Subtype.range_val)
  exact ⟨t.symm.trans (e.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp)))⟩

def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M],
  M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 → CompactSpace M

def H2 : Prop := SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)

def H3 : Prop := IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj
  (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1)))

/-- The zero-form case of the topological classification, stated for a puncture. -/
def H4 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [CompactSpace M] [SecondCountableTopology M] [SimplyConnectedSpace M],
  IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)) →
  ∃ p : M, Nonempty (↥({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin 4))

theorem main : H1 → H2 → H3 → H4 → type_of% @PoincareConjecture.poincare_conjecture.variants.dimension_four := by
  intro compact simple homology recognize M _ _ _ e
  letI : CompactSpace M := compact M e
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 4)) M
  letI : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) := simple
  letI : SimplyConnectedSpace M := e.simplyConnectedSpace
  obtain ⟨h⟩ := homotopy_homology e 2
  obtain ⟨p,⟨t⟩⟩ := recognize M (homology.of_iso h)
  exact compact_euclidean_puncture p 4 t

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1

