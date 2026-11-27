import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Adamson's product formula for the generating series of A000332

The examples with bases 2, 3, and 4 are the first cases of the same
digit product for every integer base `b ≥ 2`. The limit uses the
coefficientwise topology on formal power series over the integers.

The entry prints an initial prefix of `1, 5, 14, ...`. The displayed
series `X / (1 - X)^5` has coefficients `1, 5, 15` at degrees 1, 2,
and 3. This statement formalizes the displayed product identity.

Source: https://oeis.org/A000332
Credit: @justusklocke-cloud
-/

open Filter
open scoped BigOperators Topology PowerSeries.WithPiTopology

namespace OMA.S_oeis_a000332

theorem main : ∀ b : ℕ, 2 ≤ b →
    Tendsto
      (fun N : ℕ => (PowerSeries.X : PowerSeries ℤ) *
        ∏ i ∈ Finset.range N,
          (∑ j ∈ Finset.range b, (PowerSeries.X : PowerSeries ℤ) ^ (j * b ^ i)) ^ 5)
      atTop
      (𝓝 ((PowerSeries.X : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ 5).val)) := by
  sorry

end OMA.S_oeis_a000332
