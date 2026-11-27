import Mathlib

/-!
# A303120: Barker's closed form and recurrence

Source: https://oeis.org/A303120
Credit: @ivillar

Wesley Ivan Hurt's sequence: the total area of all rectangles p X q with p + q = n^2 and p ≤ q,
i.e. a(n) = Sum_{i=1..floor(n^2/2)} i*(n^2 - i) (offset 1; data 0, 7, 60, 372, 1300, ...).
Colin Barker conjectured (Apr 19 2018 and Mar 19 2019), among others,
a(n) = (n^2*(-4 + 3*(1+(-1)^n)*n^2 + 4*n^4)) / 48 and
a(n) = 2*a(n-1) + 4*a(n-2) - 10*a(n-3) - 5*a(n-4) + 20*a(n-5) - 20*a(n-7) + 5*a(n-8)
  + 10*a(n-9) - 4*a(n-10) - 2*a(n-11) + a(n-12) for n > 12.

Formalization notes:
* The closed form is stated over ℚ for n ≥ 1; the recurrence is stated over ℤ.
* Barker's generating function is the rational function determined by this recurrence and the
  initial terms; it is not restated here.
-/

namespace OMA.S_oeis_a303120

/-- A303120: `a(n) = Sum_{i=1..floor(n^2/2)} i*(n^2 - i)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (n ^ 2 / 2), i * (n ^ 2 - i)

/-- Barker's closed form and order-12 recurrence for A303120. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (n : ℚ) ^ 2 * (-4 + 3 * (1 + (-1) ^ n) * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 4) / 48) ∧
    (∀ n : ℕ, 12 < n →
      (a n : ℤ) = 2 * a (n - 1) + 4 * a (n - 2) - 10 * a (n - 3) - 5 * a (n - 4) + 20 * a (n - 5) -
        20 * a (n - 7) + 5 * a (n - 8) + 10 * a (n - 9) - 4 * a (n - 10) - 2 * a (n - 11) +
        a (n - 12)) := by
  sorry

end OMA.S_oeis_a303120
