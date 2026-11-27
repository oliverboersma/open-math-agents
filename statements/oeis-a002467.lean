import Mathlib

/-!
# A002467: The game of Mousetrap with n cards (given n letters and n envelopes, how many ways are there to fill the envelopes so that at leas

Source: https://oeis.org/A002467
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a002467

/-- A002467: the number of permutations of `n` letters with at least one fixed point,
equivalently `n!` minus the number of derangements (`A000166`). -/
def a (n : ℕ) : ℕ := Nat.factorial n - numDerangements n

/-- Plouffe's conjecture (OEIS A002467): for `n > 0`,
`a(n)` is the nearest integer to `(1 - 1/e) * n!`.
`Int.round` is Mathlib's nearest-integer function (ties toward positive infinity),
which is the standard reading of `{x}` in the OEIS comment. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n : ℤ) = round (((1 : ℝ) - 1 / Real.exp 1) * (Nat.factorial n : ℝ)) := by
  sorry

end OMA.S_oeis_a002467

