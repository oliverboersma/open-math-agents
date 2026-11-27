import Mathlib

/-!
# OEIS A000188

Source: https://oeis.org/A000188
Credit: @Heart-galaxy

For every positive `n`, the number of residues `x` modulo `n` satisfying `x^2 = 0` equals the
number of integers `k` with `1 ≤ k ≤ n` for which `n * k` is a square. The source also describes
`A000188(n)` as the square root of the largest square dividing `n`, and `A010052` as the
characteristic function of squares. Since `n` and `k` are positive here, the offset-zero value
`A010052(0) = 1` is not involved.

This conjecture was proved by Sela Fried, “Proofs of some conjectures of Yanev” (2025), Theorem 1;
see https://oeis.org/A000188/a000188.pdf.
-/

namespace OMA.S_oeis_a000188

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((Finset.range n).filter (fun x => x * x % n = 0)).card =
      ((Finset.Icc 1 n).filter (fun k => IsSquare (n * k))).card := by
  sorry

end OMA.S_oeis_a000188
