import FormalConjectures.Millennium.Poincare
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Abelian

/-!
Reduction of the registry statement along the published topological-to-smooth route
for three-manifolds.  The two homology leaves are the standard compactness argument:
the sphere has nonzero top integral homology, while a connected noncompact manifold
has zero top homology.  The remaining leaves are Moise's smoothing theorem and the
smooth three-dimensional Poincare theorem (Perelman).  See Qin, Liao, Khaitan and
Chow, arXiv:2609.33842, for the Lean formalization blueprint.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold ContDiff EuclideanGeometry ContinuousMap
open PoincareConjecture

private theorem homotopy_homology_iso (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) :
    Nonempty ((((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of X)) ≅ (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.of Y))) := by
  let F := (singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.left_inv
    have hh : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
  · rw [← F.map_comp, ← F.map_id]
    obtain ⟨h⟩ := e.right_inv
    have hh : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := h
    exact hh.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n

def H1 : Prop :=
  ¬ IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj
    (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [ConnectedSpace M], ¬ CompactSpace M →
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj (AddCommGrpCat.of ℤ)).obj
      (TopCat.of M))

def H3 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [CompactSpace M] [SecondCountableTopology M],
    ∃ atlas : ChartedSpace (ℝ^3) M, letI := atlas; IsManifold (𝓡 3) ∞ M

def H4 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [CompactSpace M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M],
    M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

theorem main : H1 → H2 → H3 → H4 → type_of% @PoincareConjecture.poincare_conjecture := by
  intro hSphere hVanishing hSmoothStructure hSmoothPoincare M _ _ _ e
  classical
  letI : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num) _ zero_le_one)
  obtain ⟨h⟩ := e.left_inv
  letI : PathConnectedSpace M :=
    ⟨⟨e.invFun (Classical.choice (inferInstance : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))⟩, fun x y =>
      ((show Joined (e.invFun (e x)) x from ⟨h.evalAt x⟩).symm.trans
        ((PathConnectedSpace.joined (e x) (e y)).map e.invFun.continuous)).trans
        (show Joined (e.invFun (e y)) y from ⟨h.evalAt y⟩)⟩
  letI : CompactSpace M := by
    by_contra hnc
    obtain ⟨iso⟩ := homotopy_homology_iso 3 e
    exact hSphere ((hVanishing M hnc).of_iso iso.symm)
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (ℝ^3) M
  obtain ⟨atlas, compat⟩ := hSmoothStructure M
  letI : ChartedSpace (ℝ^3) M := atlas
  letI : IsManifold (𝓡 3) ∞ M := compat
  obtain ⟨d⟩ := hSmoothPoincare M e
  exact ⟨d.toHomeomorph⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R1
