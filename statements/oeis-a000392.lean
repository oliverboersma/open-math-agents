import Mathlib

/-!
# OEIS A000392: sums of recursively generated sets

Source: https://oeis.org/A000392
Credit: @Heart-galaxy

OEIS A000392 is the Stirling number of the second kind `S(n, 3)`, indexed from zero.
John W. Layman (November 21, 2007) conjectured that, starting with `S(1) = {1}` and
letting `S(n)` for `n > 1` be the smallest set containing `x`, `2*x`, and `3*x` for
each `x` in `S(n-1)`, the sum of the elements of `S(n)` equals `a(n+2)`.
The shift `n+2` incorporates Fred Daniel Kline's October 2, 2014 offset correction.

Status: known result. The same OEIS entry records Kline's October 2, 2014 observation
that the conjecture follows by identifying `S(n)` with the first `n` rows of A036561,
whose row sums are A001047. The theorem below formalizes the recorded statement,
without supplying a formal proof.
-/

namespace OMA.S_oeis_a000392

/-- The zero-indexed sequence A000392. -/
def a (n : ℕ) : ℕ := Nat.stirlingSecond n 3

/-- The finite sets in Layman's construction. The value at zero is an unused convention.
The union of the three images is precisely the smallest set required by the source;
using a finset ensures each distinct element is counted once. -/
def S : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {1}
  | n + 2 => S (n + 1) ∪ (S (n + 1)).image (fun x => 2 * x) ∪
      (S (n + 1)).image (fun x => 3 * x)

/-- Layman's identity for every positive index. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (n + 2) = ∑ x ∈ S n, x := by
  sorry

end OMA.S_oeis_a000392
