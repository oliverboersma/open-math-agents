import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Yau's conjecture on the first eigenvalue

Source: https://en.wikipedia.org/wiki/Yau's_conjecture_on_the_first_eigenvalue
See also the formulation in https://arxiv.org/abs/2611.26893.
Credit: @jianxiongw

For a closed connected embedded minimal hypersurface of the round unit sphere, the least
positive eigenvalue of the nonnegative Laplace–Beltrami operator equals its dimension.
-/

namespace OMA.S_wp_yau_s_conjecture_on_the_first_eigenvalue

open scoped BigOperators ContDiff Manifold

noncomputable section

abbrev Coordinates (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The coordinate matrix of the metric induced by the Euclidean embedding. -/
def inducedMetric {n : ℕ} (param : Coordinates n → Coordinates (n + 2))
    (z : Coordinates n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    inner ℝ (fderiv ℝ param z (EuclideanSpace.single i 1))
      (fderiv ℝ param z (EuclideanSpace.single j 1))

/-- The Riemannian volume density in the chart. -/
def volumeDensity {n : ℕ} (param : Coordinates n → Coordinates (n + 2))
    (z : Coordinates n) : ℝ :=
  Real.sqrt (inducedMetric param z).det

/-- The coordinate formula for minus the Laplace–Beltrami operator of the induced metric. -/
def laplaceInCoordinates {n : ℕ} (param : Coordinates n → Coordinates (n + 2))
    (u : Coordinates n → ℝ) (z : Coordinates n) : ℝ :=
  -(volumeDensity param z)⁻¹ *
    ∑ i : Fin n,
      fderiv ℝ (fun y => volumeDensity param y *
        ∑ j : Fin n, ((inducedMetric param y)⁻¹) i j *
          fderiv ℝ u y (EuclideanSpace.single j 1)) z (EuclideanSpace.single i 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]

/-- Evaluate the nonnegative Laplace–Beltrami operator using the chart at the given point. -/
def laplaceBeltrami (embedding : M → Coordinates (n + 2)) (u : M → ℝ) (p : M) : ℝ :=
  let c := chartAt (Coordinates n) p
  laplaceInCoordinates (embedding ∘ c.symm) (u ∘ c.symm) (c p)

/-- Takahashi's criterion for minimality in the unit sphere, using the induced metric.
See https://doi.org/10.2969/jmsj/01840380. -/
def IsMinimalInUnitSphere (embedding : M → Coordinates (n + 2)) : Prop :=
  (∀ p, ‖embedding p‖ = 1) ∧
  ∀ k : Fin (n + 2), ∀ p : M,
    laplaceBeltrami (n := n) embedding (fun q => embedding q k) p = (n : ℝ) * embedding p k

/-- The positive eigenvalues of the induced Laplace–Beltrami operator on smooth functions. -/
def positiveEigenvalues (embedding : M → Coordinates (n + 2)) : Set ℝ :=
  {eigenvalue | 0 < eigenvalue ∧ ∃ u : M → ℝ,
    ContMDiff 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℝ) ∞ u ∧ u ≠ 0 ∧
      ∀ p : M, laplaceBeltrami (n := n) embedding u p = eigenvalue * u p}

theorem main :
    ∀ (n : ℕ), 0 < n →
      ∀ (M : Type*) [TopologicalSpace M] [T2Space M]
        [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
        [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
        (embedding : M → Coordinates (n + 2)),
        ContMDiff 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Coordinates (n + 2)) ∞ embedding →
        Topology.IsEmbedding embedding →
        (∀ p : M,
          let c := chartAt (Coordinates n) p
          Function.Injective (fderiv ℝ (embedding ∘ c.symm) (c p))) →
        IsMinimalInUnitSphere (n := n) embedding →
        IsLeast (positiveEigenvalues (n := n) embedding) (n : ℝ) := by
  sorry

end

end OMA.S_wp_yau_s_conjecture_on_the_first_eigenvalue
