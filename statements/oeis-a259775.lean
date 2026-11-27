import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# The stepped path through iterated partial sums of squares

Row zero below is the positive squares. Each following row takes partial
sums of the preceding row. The first displayed row in the OEIS example
therefore has index one. The path visits columns q and q+1 of row q+1
in succession. The source sequence starts at index one, so path t is
a(t+1). Substitution n=t+4 covers every index of the proposed recurrence.

Source: https://oeis.org/A259775 (conjecture by R. J. Mathar)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a259775

def partialSums : ℕ → ℕ → ℚ
  | 0, j => ((j : ℚ)+1)^2
  | r+1, j => ∑ t ∈ Finset.range (j+1), partialSums r t

def path (t : ℕ) := partialSums (t/2+1) ((t+1)/2)

theorem main : ∀ t : ℕ, let n : ℚ := (t : ℚ)+4;
    -(n+5)*(13*n-11)*path (t+3) + (8*n^2+39*n-35)*path (t+2) +
    2*(26*n^2+48*n+25)*path (t+1) - 4*(8*n+5)*(n-1)*path t = 0 := by
  sorry

end OMA.S_oeis_a259775
