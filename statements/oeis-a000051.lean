import Mathlib

/-!
# Permanent formula for OEIS A000051

This is the corrected form of Peter Luschny's formula in https://oeis.org/A000051.
Sela Fried proved it in Theorem 1 of https://arxiv.org/abs/2606.09913.
Lean statement by @dk8827.
-/

namespace OMA.S_oeis_a000051

/-- The matrix rows and columns are numbered from 1 through `n + 1` in the source. -/
theorem main :
    ∀ n : ℕ,
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := fun j k =>
        -⌊(((j.val : ℚ) + 1) - ((k.val : ℚ) + 1) - 2) / ((n : ℚ) + 1)⌋
      M.permanent = (2 : ℤ) ^ n + 1 := by
  sorry

end OMA.S_oeis_a000051
