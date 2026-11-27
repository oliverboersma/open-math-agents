import Mathlib

/-!
# OEIS A067576

Row i enumerates in increasing order the integers with exactly i set
bits. The positive column j corresponds to the zero-based rank j-1.
Clark Kimberling conjectured that every column becomes geometric with
ratio two after adding one to its entries, and gave the first five
starting rows. The following gives the exact starting row in every
column: max(1,j) for column j+1.

Source: https://oeis.org/A067576
-/

namespace OMA.S_oeis_a067576

noncomputable def entry (i j : ℕ) := Nat.nth (fun a : ℕ => a.bitIndices.length=i) (j-1)

theorem main : ∀ j : ℕ, IsLeast
    {r : ℕ | 0 < r ∧ ∀ i ≥ r, entry (i+1) (j+1)+1 = 2*(entry i (j+1)+1)}
    (max 1 j) := by
  sorry

end OMA.S_oeis_a067576
