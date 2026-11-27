import Mathlib

/-!
# Weighted triple sum for the sixth binomial coefficient

Source: https://oeis.org/A000579
Credit: @Heart-galaxy

OEIS states that for every natural number `n`, the sum of `k * l * m` over
nonnegative `k`, `l`, and `m` with `k + l + m ≤ n` equals `a(n+3)`, where
`a(t) = Nat.choose t 6`. The finite ranges below include `0 ≤ k,l,m ≤ n`;
the indicator retains exactly the terms satisfying the simplex constraint.
-/

namespace OMA.S_oeis_a000579

def weightedTripleSimplexSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    ∑ l ∈ Finset.range (n + 1),
      ∑ m ∈ Finset.range (n + 1),
        if k + l + m ≤ n then k * l * m else 0

theorem main : ∀ n : ℕ, Nat.choose (n + 3) 6 = weightedTripleSimplexSum n := by
  sorry

end OMA.S_oeis_a000579
