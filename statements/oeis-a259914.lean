import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# The staircase through repeated partial sums of cubes

Row zero contains the positive cubes. Repeated partial sums give subsequent
rows, beginning with the first row displayed in the OEIS example. Consecutive
pairs of path entries use columns q and q+1 of row q+1. Thus path t is OEIS
a(t+1), and the substitution n=t+4 covers every index at which a(n-3) exists.

Source: https://oeis.org/A259914 (conjecture by R. J. Mathar)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a259914

def partialSums : ℕ → ℕ → ℚ
  | 0, j => ((j : ℚ)+1)^3
  | r+1, j => ∑ t ∈ Finset.range (j+1), partialSums r t

def path (t : ℕ) := partialSums (t/2+1) ((t+1)/2)

theorem main : ∀ t : ℕ, let n : ℚ := (t : ℚ)+4;
    2*(n+7)*(145672*n^2-236343*n+123525)*path (t+3) +
    (-78613*n^3-794662*n^2+327391*n+20220)*path (t+2) +
    2*(-582688*n^3-1889455*n^2-2148719*n-832650)*path (t+1) +
    4*(n-1)*(78613*n^2+133361*n+64050)*path t = 0 := by
  sorry

end OMA.S_oeis_a259914
