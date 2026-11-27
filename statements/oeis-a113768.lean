import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Growth of the floor-cube-root recurrence

The source starts with a(1)=1. Here value j denotes a(j+1). Dividing the
published comparison (2/3)n√((2/3)n) by n√n gives (2/3)√(2/3).

Source: https://oeis.org/A113768
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a113768

noncomputable def value : ℕ → ℕ
  | 0 => 1
  | n+1 => value n + ⌊((value n : ℕ) : ℝ) ^ (1/3:ℝ)⌋₊

open Filter Topology

theorem main : Tendsto
    (fun j : ℕ => (value j : ℝ) / (((j : ℝ)+1) * Real.sqrt ((j : ℝ)+1)))
    atTop (𝓝 ((2/3) * Real.sqrt (2/3))) := by
  sorry

end OMA.S_oeis_a113768
