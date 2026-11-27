import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Rat.Defs

/-!
# Mathar's recurrence for quarter-plane excursions

A151341 counts walks of length `2*n` in the nonnegative quadrant from the
origin to itself, using (1,0), (-1,-1), (-1,0), and (-1,1). The horizontal
coordinates form a Dyck path of semilength `n`. On its `n` westward steps
the vertical increments form a Motzkin path of length `n`. These two paths
uniquely reconstruct the walk, giving the product formula recorded in OEIS.

Manuel Kauers contributed A151341. R. J. Mathar proposed the recurrence
in July 2017. Its last term uses index `n-2`, so the recurrence starts at 2.
The Motzkin recurrence and initial values are from A001006.

Sources: https://oeis.org/A151341 and https://oeis.org/A001006.
Formalization by @anmolspace.
-/

namespace OMA.S_oeis_a151341

/-- Motzkin numbers, using their second-order recurrence over the rationals. -/
def motzkin : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | k+2 => ((2*(k : ℚ)+5) * motzkin (k+1) + 3*((k : ℚ)+1) * motzkin k) / (k+4 : ℚ)

/-- Each Dyck path can be decorated independently by a Motzkin path. -/
def a (n : ℕ) : ℚ := (catalan n : ℚ) * motzkin n

theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ)*((n : ℚ)+2)*((n : ℚ)+1)*a n
      - 2*(n : ℚ)*(2*(n : ℚ)-1)*(2*(n : ℚ)+1)*a (n-1)
      - 12*((n : ℚ)-1)*(2*(n : ℚ)-1)*(2*(n : ℚ)-3)*a (n-2) = 0 := by
  sorry

end OMA.S_oeis_a151341
