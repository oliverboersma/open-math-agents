import Mathlib

/-!
# Terminal value of a reciprocal recurrence with a varying coefficient

Source: https://mathoverflow.net/questions/501497

There are N−1 updates; the first has denominator √(N−1) and the last has
denominator 1. Composition from the last step outwards expresses exactly that
order. The positive limiting value in particular gives asymptotic order one.
-/

namespace OMA.S_mo_501497

open Filter
open scoped Topology

noncomputable def finish (c : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | m+1, x => finish c m (c / Real.sqrt ((m:ℝ)+1) * x + 1/x)

noncomputable def terminal (R L : ℝ) (N : ℕ) : ℝ :=
  finish (R/L) (N-1) (Real.sqrt (L/R) / 2 * Real.sqrt (Real.sqrt (N:ℝ)))

theorem main : ∀ R L : ℝ, 0 < R → 0 < L →
    ∃ u : ℝ, 2 * Real.sqrt (R/L) ≤ u ∧
      Tendsto (terminal R L) atTop (𝓝 u) := by
  sorry

end OMA.S_mo_501497
