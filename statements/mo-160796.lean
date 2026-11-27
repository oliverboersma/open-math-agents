import Mathlib

/-!
# MathOverflow 160796

Source: https://mathoverflow.net/questions/160796
-/

namespace OMA.S_mo_160796

open MeasureTheory Set

inductive GeneratedDynkin {α : Type} (base : Set (Set α)) : Set α → Prop
  | basic {U : Set α} : U ∈ base → GeneratedDynkin base U
  | whole : GeneratedDynkin base univ
  | complement {U : Set α} : GeneratedDynkin base U → GeneratedDynkin base Uᶜ
  | union {U : ℕ → Set α} : Pairwise (fun i j => Disjoint (U i) (U j)) →
      (∀ i, GeneratedDynkin base (U i)) → GeneratedDynkin base (⋃ i, U i)

theorem main : ∀ (α : Type) [MeasurableSpace α] (base : Set (Set α)),
    (∀ U ∈ base, MeasurableSet U) →
    ∀ μ ν : Measure α, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ U ∈ base, μ U = ν U) → ∀ U, GeneratedDynkin base U → μ U = ν U := by
  sorry

end OMA.S_mo_160796
