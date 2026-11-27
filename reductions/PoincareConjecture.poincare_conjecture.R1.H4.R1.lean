import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
The smooth step has the homotopy equivalence supplied by the catalogue target.
The published smooth endpoint instead assumes simple connectivity. Separate
simple connectivity of the sphere from the Hamilton–Perelman smooth theorem.
The latter follows the Lean blueprint of Qin, Liao, Khaitan and Chow
(arXiv:2609.33842).
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

def H1 : Prop :=
  SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [CompactSpace M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M],
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1.H4 := by
  intro hSphere hSmooth M _ _ _ _ _ _ e
  letI : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := hSphere
  letI : SimplyConnectedSpace M := e.simplyConnectedSpace
  exact hSmooth M

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1
