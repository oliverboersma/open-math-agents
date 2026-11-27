import Mathlib

/-!
# A296161: Barker's recurrence

Source: https://oeis.org/A296161
Credit: @ivillar

Wesley Ivan Hurt's sequence: the sum of the larger parts of the partitions of n into two parts
whose smaller part is odd, a(n) = Sum_{i=1..floor(n/2)} (n-i) * (i mod 2) (offset 1; data 0, 1,
2, 3, 4, 8, 10, 12, 14, 21, ...). Colin Barker conjectured (Dec 06 2017)
a(n) = a(n-1) + 2*a(n-4) - 2*a(n-5) - a(n-8) + a(n-9) for n > 9.

Formalization notes:
* The recurrence is stated over ℤ.
* Barker's generating function x^2*(1 + x + x^2 + x^3 + 2*x^4) / ((1-x)^3*(1+x)^2*(1+x^2)^2) is
  the rational function determined by this recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a296161

/-- A296161: `a(n) = Sum_{i=1..floor(n/2)} (n-i) * (i mod 2)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (n / 2), (n - i) * (i % 2)

/-- Barker's conjectured recurrence for A296161, for every `n > 9`. -/
theorem main : ∀ n : ℕ, 9 < n →
    (a n : ℤ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a296161
