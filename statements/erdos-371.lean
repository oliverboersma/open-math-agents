import Mathlib

/-!
# Erdős Problem 371

Source: https://www.erdosproblems.com/371
Credit: @mattdorman

The source asks: let `P(n)` denote the largest prime factor of `n`. Show that the set of `n` with
`P(n) < P(n+1)` has density `1/2`.

Reading used here: density is natural (asymptotic) density over the positive integers, i.e.
`#{1 ≤ n ≤ N : P(n) < P(n+1)} / N → 1/2`. `P(n)` is the largest element of `n.primeFactors`;
for `n = 1`, which has no prime factor, it is `0` by convention (a single value of `n` does not
change a density).
-/

open Filter Topology

namespace OMA.S_erdos_371

/-- The largest prime factor of `n` (`0` when `n` has no prime factor). -/
def largestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

theorem main :
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter
          (fun n => largestPrimeFactor n < largestPrimeFactor (n + 1))).card : ℝ) / N)
      atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_erdos_371
