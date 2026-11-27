import Mathlib

/-!
# A183761: Number of 2 X 2 nonsingular 0..n matrices with rows in increasing order.

Source: https://oeis.org/A183761
Credit: @bnb9001

The sequence has offset 1 (3, 25, 96, ...). A matrix is given by its rows `(a, b)` and `(c, d)`
with entries in `0..n`. Rows in increasing order means the first row comes strictly before the
second in lexicographic order (`a < c`, or `a = c` and `b < d`), as in R. H. Hardin's array
sequences; nonsingular means `a d - b c ≠ 0`.

Conjecture (Clark Kimberling, 2012): the sequence also gives the number of 2 X 2 matrices with
all terms in {0, 1, ..., n} and positive determinant. David Radcliffe notes that this is true.
-/

namespace OMA.S_oeis_a183761

/-- All `2 × 2` matrices with entries in `0..n`, as pairs of rows `((a, b), (c, d))`. -/
def mats (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) ×ˢ (Finset.range (n + 1) ×ˢ Finset.range (n + 1))

/-- The determinant `a d - b c` of the matrix with rows `(a, b)` and `(c, d)`. -/
def det (M : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ := (M.1.1 : ℤ) * M.2.2 - (M.1.2 : ℤ) * M.2.1

/-- Row `r` comes strictly before row `s` in lexicographic order. -/
def RowLt (r s : ℕ × ℕ) : Prop := r.1 < s.1 ∨ (r.1 = s.1 ∧ r.2 < s.2)

instance (r s : ℕ × ℕ) : Decidable (RowLt r s) := by unfold RowLt; infer_instance

/-- For every `n ≥ 1`, the nonsingular `0..n` matrices with rows in increasing order are as many
as the `0..n` matrices with positive determinant. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((mats n).filter (fun M => RowLt M.1 M.2 ∧ det M ≠ 0)).card =
      ((mats n).filter (fun M => 0 < det M)).card := by
  sorry

end OMA.S_oeis_a183761
