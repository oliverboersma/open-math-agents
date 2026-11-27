import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1
import Mathlib

/-!
Newman's engulfing method isolates the high-dimensional input on a punctured
homotopy sphere. Shrinking a Euclidean chart around a compact set gives a
relatively compact open cell. A compact exhaustion then selects nested cells
covering the puncture. Brown's monotone union theorem identifies that puncture
with Euclidean space. Compactification supplies the desired homeomorphism.
-/

open Set Topology
open scoped ContinuousMap
namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1

/-- Engulf each compact subset of one puncture in a Euclidean open cell. -/
def H1 : Prop := ∀ (n : ℕ), 5 ≤ n →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
    M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    ∃ p : M, ∀ K : Set ↥(({p} : Set M)ᶜ), IsCompact K →
      ∃ f : EuclideanSpace ℝ (Fin n) → ↥(({p} : Set M)ᶜ), IsOpenEmbedding f ∧ K ⊆ range f

/-- Shrink an engulfing cell around a compact set while retaining Euclidean coordinates. -/
def H2 : Prop := ∀ (n : ℕ) (N : Type) [TopologicalSpace N] [T2Space N] (K : Set N),
    IsCompact K → ∀ f : EuclideanSpace ℝ (Fin n) → N, IsOpenEmbedding f → K ⊆ range f →
    ∃ U : Set N, K ⊆ U ∧ IsOpen U ∧ IsCompact (closure U) ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))

/-- Countable selection for a cofinal family of relatively compact cells. -/
def H3 : Prop := ∀ (n : ℕ) (N : Type) [TopologicalSpace N] [SigmaCompactSpace N],
    (∀ K : Set N, IsCompact K → ∃ U : Set N, K ⊆ U ∧ IsOpen U ∧ IsCompact (closure U) ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))) →
    ∃ U : ℕ → Set N, (∀ j, IsOpen (U j) ∧ Nonempty (↥(U j) ≃ₜ EuclideanSpace ℝ (Fin n))) ∧
      (∀ j, closure (U j) ⊆ U (j+1)) ∧ ⋃ j, U j = univ

/-- Brown's monotone union theorem for open n-cells. -/
def H4 : Prop := ∀ (n : ℕ) (N : Type) [TopologicalSpace N] [T2Space N] (U : ℕ → Set N),
    (∀ j, IsOpen (U j) ∧ Nonempty (↥(U j) ≃ₜ EuclideanSpace ℝ (Fin n))) →
    (∀ j, U j ⊆ U (j+1)) → (⋃ j, U j) = univ → Nonempty (N ≃ₜ EuclideanSpace ℝ (Fin n))

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1.H4 := by
  intro engulf shrink selectCell brown n hn M _ _ _ _ _ e
  obtain ⟨p,hp⟩ := engulf n hn M e
  let P := (({p} : Set M)ᶜ)
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  letI : LocallyCompactSpace P := isOpen_compl_singleton.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨U,hU,hinc,hcov⟩ := selectCell n P (by
    intro K hK
    obtain ⟨f,hf,hs⟩ := hp K hK
    exact shrink n P K hK f hf hs)
  obtain ⟨t⟩ := brown n P U hU (fun j => subset_closure.trans (hinc j)) hcov
  let c := OnePoint.equivOfIsEmbeddingOfRangeEq p (Subtype.val : P → M)
    Topology.IsEmbedding.subtypeVal Subtype.range_val
  exact ⟨c.symm.trans (t.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp)))⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1
