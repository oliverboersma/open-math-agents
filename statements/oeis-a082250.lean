import Mathlib

/-!
# A082250: Divisibility of consecutive blocks of decimal integers

Source: https://oeis.org/A082250
Credit: @laurilehtinen

The two blocks contain k consecutive positive integers each, all of decimal width r.
In reverse order the integers within each block are read from largest to smallest,
as in the companion sequence https://oeis.org/A082249.
-/

namespace OMA.S_oeis_a082250

/-- Concatenate integers of decimal width r in their listed order. -/
def concat (r : ℕ) (xs : List ℕ) : ℕ :=
  xs.foldl (fun acc x => acc * 10^r + x) 0

/-- Divisibility of the first block is conjectured to pass to the next block
in each order, provided the second block still consists of r-digit numbers. -/
theorem main : ∀ n k r s : ℕ, 0 < n → 0 < k → 0 < r →
    10^(r-1) ≤ s → s+2*k ≤ 10^r →
    let first := List.range' s k
    let next := List.range' (s+k) k
    (n ∣ concat r first → n ∣ concat r next) ∧
      (n ∣ concat r first.reverse → n ∣ concat r next.reverse) := by
  sorry

end OMA.S_oeis_a082250

