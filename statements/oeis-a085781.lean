import Mathlib

/-!
# A four-term recurrence for OEIS A085781

Source: https://oeis.org/A085781. The sequence starts at index zero.
R. J. Mathar proposed this recurrence on January 25, 2013.
Credit: @dreamzzz-dev
-/

namespace OMA.S_oeis_a085781

/-- The binomial formula defining the sequence, viewed in the integers. -/
def a (n : ℕ) : ℤ :=
  2 * ((2 * n + 1).choose (n + 1) : ℤ) - 2 ^ n

/-- The OEIS recurrence at every index where its four terms are defined. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * a n - 2 * (4 * (n : ℤ) + 1) * a (n - 1) +
      4 * (5 * (n : ℤ) - 3) * a (n - 2) +
      8 * (-2 * (n : ℤ) + 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a085781
