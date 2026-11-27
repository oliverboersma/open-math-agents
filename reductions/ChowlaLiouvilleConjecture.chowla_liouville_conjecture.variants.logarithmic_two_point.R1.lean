import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture
import Mathlib

/-! Reduction of Tao's logarithmically averaged two-point Chowla theorem
(`ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.logarithmic_two_point`) to
separate cancellation over even indices (`H1`) and odd indices (`H2`). In `main`, we partition
`Finset.Icc 1 N` into even and non-even indices via `Finset.sum_filter_add_sum_filter_not`
and combine the two limits using `Filter.Tendsto.add`. -/

namespace OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_logarithmic_two_point_R1

open Filter Topology

/-- Logarithmic two-point Liouville correlation restricted to even indices `n` tends to 0. -/
def H1 : Prop :=
  ∀ a : ℕ, 1 ≤ a →
    Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ (Finset.Icc 1 N).filter Even,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + a) : ℝ) / (n : ℝ)) /
            Real.log (N : ℝ))
      atTop (𝓝 0)

/-- Logarithmic two-point Liouville correlation restricted to odd indices `n` tends to 0. -/
def H2 : Prop :=
  ∀ a : ℕ, 1 ≤ a →
    Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Even n),
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + a) : ℝ) / (n : ℝ)) /
            Real.log (N : ℝ))
      atTop (𝓝 0)

theorem main : H1 → H2 →
    type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.logarithmic_two_point := by
  intro h1 h2 a ha
  have hsum := (h1 a ha).add (h2 a ha)
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div, Finset.sum_filter_add_sum_filter_not]

end OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_logarithmic_two_point_R1
