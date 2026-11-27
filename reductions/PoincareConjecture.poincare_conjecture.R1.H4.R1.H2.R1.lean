import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Elliptization gives a spherical space form, hence a smooth map from the
standard sphere with injective differential everywhere. This is the only
global geometric input. The second input is the local inverse function
theorem, with no compactness or simple-connectivity condition.

The proof below upgrades the local diffeomorphism to a covering by
compactness. Lifting the identity and uniqueness of lifts on the connected
sphere provide both inverse identities. No degree, chosen orientation,
or bijectivity of the spherical parametrization is assumed.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1

open scoped Manifold ContDiff EuclideanGeometry

/-- The immersion supplied by a round spherical space-form presentation. -/
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [CompactSpace M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M],
    ∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧ ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x)

/-- The local inverse function theorem on boundaryless smooth three-manifolds. -/
def H2 : Prop := ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (ℝ^3) A] [ChartedSpace (ℝ^3) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B] (f : A → B),
    ContMDiff (𝓡 3) (𝓡 3) ∞ f → (∀ x, Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x)) →
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f

section Proof

private theorem covering_bijective {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    {f : E → B} (cov : IsCoveringMap f) : Function.Bijective f := by
  classical
  let e : E := Classical.choice inferInstance
  obtain ⟨g,⟨hbase,hright⟩,_⟩ := cov.existsUnique_continuousMap_lifts
    (ContinuousMap.id B) (f e) e rfl
  have right (b : B) : f (g b) = b := congrFun hright b
  have left : (g : B → E) ∘ f = id := by
    apply cov.eq_of_comp_eq (g.continuous.comp cov.continuous) continuous_id _ e hbase
    funext x
    exact right (f x)
  exact ⟨fun x y h => by simpa only [Function.comp_apply,id_eq] using
    ((congrFun left x).symm.trans ((congrArg g h).trans (congrFun left y))),
    fun b => ⟨g b,right b⟩⟩

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1.H2 := by
  intro geometry inverse M _ _ _ _ _ _ _
  obtain ⟨f,hf,hinj⟩ := geometry M
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  letI : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]
      norm_num) _ zero_le_one)
  letI : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (ℝ^3) M
  have localInv : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := by
    apply inverse S M f hf
    intro x
    let L : (ℝ^3) →L[ℝ] (ℝ^3) := mfderiv (𝓡 3) (𝓡 3) f x
    change Function.Bijective L
    exact ⟨hinj x,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := L.toLinearMap) rfl).mp (hinj x)⟩
  have cov := isLocalHomeomorph_iff_isCoveringMap.mp localInv.isLocalHomeomorph
  exact ⟨(localInv.diffeomorphOfBijective (covering_bijective cov)).symm⟩

end Proof

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1
