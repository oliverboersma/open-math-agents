import Mathlib

/-!
# A123341 and the prime-counting recurrence

The sequence starts at index 1. Its value at 0 is set to 0 to obtain a
function on the natural numbers. The summands at every index n > 1 have
positive indices, as there are fewer than n primes up to n.

Source: https://oeis.org/A123341
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a123341

/-- The sum of the preceding π(n) values, starting from a(1) = 1. -/
def a (n : ℕ) : ℕ :=
  if h : n ≤ 1 then n else
    ∑ i ∈ Finset.range n.primeCounting, a (n-(i+1))
termination_by n
decreasing_by omega

/-- The conjectured normalized limit exists and is strictly positive. -/
theorem main : ∃ L : ℝ, 0 < L ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / 2^n) Filter.atTop (nhds L) := by
  sorry

end OMA.S_oeis_a123341
