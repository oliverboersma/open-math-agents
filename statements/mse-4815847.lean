import Mathlib

/-!
# Can this be done? Split Pascal's triangle (without the $1$s) with a straight line into two regions of equal sums.

Source: https://math.stackexchange.com/questions/4815847/can-this-be-done-split-pascals-triangle-without-the-1s-with-a-straight-lin
Credit: @mgv27

Consider Pascal's triangle with $n$ rows, without the $1$s, with each number placed at a
vertex of a triangular grid. Does there exist an $n$ such that this triangle can be divided by
a straight line (that does not pass through any vertex) into two regions of equal sums?
The asker (and computer searches, cross-posted as MathOverflow 514243) suggests it cannot be
done.

Formalization notes:
* `main` states the conjectured negative answer.
* Entries are `C(r, k)` for `1 ≤ k ≤ r - 1`, `r ≤ N` (rows `0..N`; the 1s removed). We require
  `N ≥ 2`, otherwise there are no entries and both sums are trivially `0`.
* We place `C(r, k)` at the point `(r, k)` (the "left-justified" triangle). The usual
  equilateral layout is the image under an invertible linear map, which maps lines to lines,
  so the question is unchanged.
* A line not through any vertex is `{a r + b k + c = 0}` with `a r + b k + c ≠ 0` at every
  entry; the two regions are the two strict sides. (Equal sums of positive entries force both
  regions to be nonempty.)
* Sanity check: total sums for `N = 2, …, 8` are 2, 8, 22, 52, 114, 240, 494 (A145654).
-/

namespace OMA.S_mse_4815847

/-- Positions `(r, k)` of the entries of Pascal's triangle with rows `0..N`, without the 1s. -/
def entries (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => 1 ≤ p.2 ∧ p.2 + 1 ≤ p.1)

/-- The affine function `a r + b k + c` defining a line, evaluated at position `p = (r, k)`. -/
def side (a b c : ℝ) (p : ℕ × ℕ) : ℝ := a * p.1 + b * p.2 + c

/-- No line avoiding all vertices splits the triangle (without the 1s) into equal sums. -/
theorem main :
    ∀ N : ℕ, 2 ≤ N → ∀ a b c : ℝ, (∀ p ∈ entries N, side a b c p ≠ 0) →
    ∑ p ∈ (entries N).filter (fun p => 0 < side a b c p), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => side a b c p < 0), Nat.choose p.1 p.2 := by
  sorry

end OMA.S_mse_4815847
