import Mathlib

/-!
# OEIS A126364: the proposed relation to A025565

Source: https://oeis.org/A126364
Auxiliary sequences: https://oeis.org/A025565 and https://oeis.org/A025564
Credit: @Heart-galaxy

A126364 counts length-n decimal words, allowing leading zeros, in which adjacent
symbols differ by at most one. `row k i` counts the words of length k+1 ending in
digit i: each one-digit word has count one, and appending a digit sums the counts
for its allowed predecessor digits. Thus the tridiagonal transfer recurrence
below is the direct counting construction, independent of any scalar recurrence
or conjectured generating function. The empty word has count a(0)=1.

A025565 has offset 1. The explicit array code in A025565 (also in A025564) uses
zero-based rows starting [1], [1,2,1], and adds the three entries in the preceding
row. Its (n-1,n-1) entry defines A025565(n), exactly as the source code specifies.
Integer column indices ensure entries to the left of each row are zero.

Indexing review note: the A025565 prose says T(n,n-1), whereas its executable
Mathematica code says T[n-1,n-1] with zero-based rows. This statement follows
the executable code and the actual published sequence 1,2,4,10,... . Human review
should check this row-label convention; the prose is not silently reinterpreted.

Daniel Forgues conjectured on August 23, 2011 that
A126364(n) = 3*A126364(n-1) - A025565(n) for n>=2.
The proposed relation is stated below with ordinary integer subtraction.
-/

namespace OMA.S_oeis_a126364

/-- Allowed adjacent decimal digits, including equality. -/
def adjacency : Matrix (Fin 10) (Fin 10) ℕ := fun i j =>
  if i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 then 1 else 0

/-- Counts of smooth decimal words of length k+1 by their final digit. -/
def row : ℕ → Fin 10 → ℕ
  | 0 => fun _ => 1
  | k + 1 => adjacency.mulVec (row k)

/-- The word-counting sequence, with the empty-word convention at zero. -/
def a (n : ℕ) : ℕ := if n = 0 then 1 else ∑ i : Fin 10, row (n - 1) i

/-- The zero-indexed triangular array given in A025564 and in the code for A025565. -/
def T : ℕ → ℤ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 2 then 1 else if k = 1 then 2 else 0
  | n + 2, k => T (n + 1) (k - 2) + T (n + 1) (k - 1) + T (n + 1) k

/-- A025565, whose positive index n uses entry (n-1,n-1) of the zero-indexed array. -/
def a025565 (n : ℕ) : ℕ := T (n - 1) ((n - 1 : ℕ) : ℤ)

/-- Forgues' proposed relation for every n>=2. The accompanying disproof uses n=12:
the two sides are 1161634 and 1161632, computed from the canonical definitions. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℤ) = 3 * (a (n - 1) : ℤ) - (a025565 n : ℤ) := by
  sorry

end OMA.S_oeis_a126364

