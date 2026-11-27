import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs

/-!
# A recurrence for A127769

The OEIS formula for a positive index `n` is `3*choose(4*n-2,2*n)/(2*n+1)`.
Expanding the binomial coefficient gives `3*(4*n-2)!/((2*n+1)!*(2*n-2)!)`.
Thus `term k` is exactly `a(k+1)`. The conjecture concerns `n>1`, so every
index in it is positive. We use `n=t+2` and exact rational arithmetic.

Source: https://oeis.org/A127769 (recurrence by R. J. Mathar)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a127769

def term (k : ℕ) : ℚ := 3 * ((4*k+2).factorial : ℚ) /
    (((2*k+3).factorial : ℚ) * ((2*k).factorial : ℚ))

theorem main : ∀ t : ℕ, let n : ℚ := (t : ℚ) + 2
    n * (2*n+1) * (2*n-3) * term (t+1) -
      2 * (4*n-5) * (4*n-3) * (2*n-1) * term t = 0 := by
  sorry

end OMA.S_oeis_a127769
