import Mathlib.NumberTheory.Divisors

/-!
# The second difference of total arithmetic-progression length

For a last term z+1 and length k+1 with k positive, the common difference
may be any integer from 1 through z/k. The separate contribution 1 is
the singleton ending at z+1. Summing these lengths over the possible
last terms counts the progressions of A264100 directly.

Franklin T. Adams-Watters proved the second-difference identity in the
November 5, 2015 comments to https://oeis.org/A264100.
Formalization: @anmolspace with OpenAI Codex.
-/
namespace OMA.S_oeis_a264100

def endingWeight (z : ℕ) : ℕ :=
  1 + ∑ k ∈ Finset.Icc 1 z, (k+1)*(z/k)

def totalLength (n : ℕ) : ℕ := ∑ z ∈ Finset.range n, endingWeight z

theorem main : ∀ n : ℕ,
    (totalLength (n+2) - totalLength (n+1)) - (totalLength (n+1) - totalLength n) =
      (∑ d ∈ (n+1).divisors, d) + (n+1).divisors.card := by
  sorry

end OMA.S_oeis_a264100
