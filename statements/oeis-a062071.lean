import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The self-power floor sum and the constant A073009

At positive n, A062071 is the sum of ⌊n/jʲ⌋ for j starting at one.
Natural division gives the floors. Every term with j>n vanishes.
The conjectured coefficient is the sum of the reciprocals 1/jʲ.
The ratio going to one expresses Kotesovec's asymptotic equivalence.

Source: https://oeis.org/A062071
Constant: https://oeis.org/A073009
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a062071

def denominator (k : ℕ) := (k+1)^(k+1)

noncomputable def floorSum (n : ℕ) : ℝ :=
  ∑' k : ℕ, ((n / denominator k : ℕ) : ℝ)

noncomputable def constantValue : ℝ := ∑' k : ℕ, 1/(denominator k : ℝ)

open Filter Topology

theorem main : Tendsto (fun n : ℕ => floorSum n / (constantValue * (n:ℝ)))
    atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a062071
