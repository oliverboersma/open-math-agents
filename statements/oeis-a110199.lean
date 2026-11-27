import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# A recurrence for repeated partial sums of Catalan numbers

Source: https://oeis.org/A110199 (OEIS Foundation, CC BY-SA 4.0).
Paul Barry contributed the sequence, and R. J. Mathar conjectured the
recurrence on November 9, 2012. Formalization by @anmolspace.

The sequence has offset zero and uses the inclusive upper limit `n / 2`.
The recurrence starts at `n = 3`, the first index for which `a (n - 3)` is
defined. The signed coefficients and the equality are taken in the integers.
-/

namespace OMA.S_oeis_a110199

def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), catalan k

theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℤ) + 2) * (a n : ℤ) + ((n : ℤ) + 2) * (a (n - 1) : ℤ) +
    4 * ((n : ℤ) - 1) * (a (n - 2) : ℤ) +
    4 * (1 - (n : ℤ)) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a110199
