import Mathlib

/-!
# The D-finite recurrence recorded in OEIS A091540

Source: https://oeis.org/A091540
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A091/A091540.seq
Credit: @Heart-galaxy

The sequence has offset 2. Its triple-factorial formula is
(3^n * n! - 3 * Product_{j=0..n-1} (3*j+1)) / 6 for n >= 2.
We take the numerator and quotient in the integers; indices below 2 are
auxiliary values and do not occur in the stated recurrence.

R. J. Mathar conjectured the recurrence on July 15, 2026. Eiver Rodríguez
proved it in the OEIS entry on September 20, 2026, by eliminating the
product from two consecutive first-order relations. The recurrence starts
at n >= 4, so all sequence indices are at least the offset 2.
This file states that known result.
-/

namespace OMA.S_oeis_a091540

open Finset

def q (n : ℕ) : ℤ := ∏ j ∈ range n, (3 * (j : ℤ) + 1)

def numerator (n : ℕ) : ℤ := (3 : ℤ) ^ n * (n.factorial : ℤ) - 3 * q n

def a (n : ℕ) : ℤ := numerator n / 6

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + (-6 * (n : ℤ) + 5) * a (n - 1) +
      3 * ((n : ℤ) - 1) * (3 * (n : ℤ) - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a091540
