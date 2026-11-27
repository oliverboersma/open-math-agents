import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs

/-!
# A recurrence for A052183

The sequence has offset zero. Substituting the factorial expression for
`choose(3*n,n)` into `(n+2)*choose(3*n,n)/(2*n+1)` gives the exact rational
expression below. Mathar's recurrence uses the terms at `n`, `n-1`, and
`n-2`. Setting `n=t+2` covers their entire common domain.

Source: https://oeis.org/A052183 (recurrence by R. J. Mathar)
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a052183

def a (n : ℕ) : ℚ := ((n : ℚ) + 2) * ((3*n).factorial : ℚ) /
    ((n.factorial : ℚ) * ((2*n+1).factorial : ℚ))

theorem main : ∀ t : ℕ, let n : ℚ := (t : ℚ) + 2
    2*n*(2*n+1)*a (t+2) + (-47*n^2+50*n-12)*a (t+1) +
      15*(3*n-4)*(3*n-5)*a t = 0 := by
  sorry

end OMA.S_oeis_a052183
