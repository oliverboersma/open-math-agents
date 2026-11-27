import Mathlib

/-!
# A362559: Number of integer partitions of n whose weighted sum is divisible by n.

Source: https://oeis.org/A362559
Credit: @rorcores

The entry (offset 1, data 1, 1, 2, 1, 2, 3, 3, 3, 5, 4, 5, 7, 8, 11, 14, ...) records in its
COMMENTS section:

  The (one-based) weighted sum of a sequence (y_1,...,y_k) is Sum_{i=1..k} i*y_i. This is also the
  sum of partial sums of the reverse.

  Conjecture: A partition of n has weighted sum divisible by n iff its reverse has weighted sum
  divisible by n.

Conventions:
* An integer partition of `n` (with `n ≥ 1`, the offset of the entry) is written, as in the entry's
  examples such as `(4,2,2,1)`, as a weakly decreasing list of positive integers with sum `n`.
* The weighted sum of the list `(y_1, ..., y_k)` is `1 * y_1 + 2 * y_2 + ... + k * y_k`; in Lean the
  list is indexed from `0`, so the entry at index `i` has weight `i + 1`. For example the weighted
  sum of `(4,2,2,1)` is `1*4 + 2*2 + 3*2 + 4*1 = 18`.
* The reverse of the partition is the same list read backwards, `(y_k, ..., y_1)`.
-/

namespace OMA.S_oeis_a362559

/-- The (one-based) weighted sum of a sequence `(y_1, ..., y_k)`: `Σ_{i=1..k} i * y_i`. -/
def weightedSum (y : List ℕ) : ℕ := ∑ i : Fin y.length, (i.val + 1) * y[i]

/-- `y` is an integer partition of `n`: a weakly decreasing list of positive integers with sum
`n`. -/
def IsPartition (n : ℕ) (y : List ℕ) : Prop :=
  y.Pairwise (· ≥ ·) ∧ (∀ a ∈ y, 0 < a) ∧ y.sum = n

/-- Wiseman's conjecture: a partition of `n` has weighted sum divisible by `n` if and only if its
reverse has weighted sum divisible by `n`. -/
theorem main : ∀ (n : ℕ) (y : List ℕ), 1 ≤ n → IsPartition n y →
    (n ∣ weightedSum y ↔ n ∣ weightedSum y.reverse) := by
  sorry

end OMA.S_oeis_a362559
