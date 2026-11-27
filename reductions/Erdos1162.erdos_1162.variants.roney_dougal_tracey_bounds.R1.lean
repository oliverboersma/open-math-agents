import FormalConjectures.ErdosProblems.«1162»

-- Reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey_bounds.R1 of Erdős Problem 1162 — roney dougal tracey bounds
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is the two-sided bound of Roney-Dougal and Tracey on the number `f n` of subgroups
-- of the symmetric group: a lower bound with a linear-in-`n log n` exponent correction and an
-- upper bound with an `n ^ (3/2)` correction. The two sides are independent.

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_bounds_R1

open Erdos1162

/-- The lower bound: some `α > 0` with `2 ^ (n ^ 2 / 16 + α n log n) <= f n` for all `n > 1`
(logarithm to base `2`). -/
def H1 : Prop :=
  ∃ α > (0 : ℝ), ∀ n : ℕ, 1 < n →
    (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + α * n * Real.logb 2 n) ≤ f n

/-- The upper bound: some `β` with `f n <= 2 ^ (n ^ 2 / 16 + β n ^ (3/2))` for all `n > 1`
(logarithm to base `2`). -/
def H2 : Prop :=
  ∃ β : ℝ, ∀ n : ℕ, 1 < n →
    (f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2 / 16 + β * (n : ℝ) ^ ((3 : ℝ) / 2))

theorem main : H1 → H2 → type_of% @Erdos1162.erdos_1162.variants.roney_dougal_tracey_bounds := by
  rintro ⟨α, hα, h1⟩ ⟨β, h2⟩
  exact ⟨α, hα, β, fun n hn => ⟨h1 n hn, h2 n hn⟩⟩

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_bounds_R1
