import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1
import Mathlib

/-!
Reduce compatible smoothing to the connected Hamilton–Cairns theorem
and assembly of smooth atlases on the open connected components.
The connected route is the one used by PoincareLib's
`Topology/Manifold/Smoothing/Compatible.lean` at 62db01af.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2

open Set TopologicalSpace
open scoped Manifold ContDiff

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ConnectedSpace M],
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := atlas
      IsManifold (𝓡 3) ∞ M

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [LocallyConnectedSpace M],
    (∀ x : M, ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (connectedComponent x),
      letI := atlas
      IsManifold (𝓡 3) ∞ (connectedComponent x)) →
    ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := atlas
      IsManifold (𝓡 3) ∞ M

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1.H3 := by
  intro hConnected hAssembly M _ _ _ _ _
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  apply hAssembly M
  intro x
  let U : Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : CompactSpace (connectedComponent x) :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let : ConnectedSpace (connectedComponent x) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (connectedComponent x) :=
    inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 3)) U)
  exact hConnected (connectedComponent x)

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2
