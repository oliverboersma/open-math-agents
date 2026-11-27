import Mathlib

/-!
# A367191: a(n) is the largest positive number k such that k^2 + k*n + n^2 is a perfect square, or 0 if no such k exists.

Source: https://oeis.org/A367191
Credit: @rorcores

The entry (offset 0, data 0, 0, 0, 5, 0, 16, 10, 33, 7, 56, 32, 85, 20, 120, 66, 161, 39, ...)
records in its FORMULA section:

  Conjectured formulas according to n mod 4 in first column.
    0, (n/4 - 1)(3n/4 + 1),
    1 or 3, 4((n + 3)/4 - 1)(3(n + 3)/4 - 2),
    2, 2((n + 2)/4 - 1)(3(n + 2)/4 - 1).

Conventions:
* `a(n)` is the largest positive integer `k` with `k^2 + k*n + n^2` a perfect square, and `a(n) = 0`
  if there is no positive `k` with that property (the entry's definition).
* The divisions in the formulas are exact divisions of rational numbers, not floors: for example
  at `n = 3` the second formula is `4 * (6/4 - 1) * (18/4 - 2) = 5 = a(3)`. So the formulas are
  stated as identities in `ℚ`.
* Range: the formulas are stated for `n ≥ 1`. At `n = 0` every positive `k` makes `k^2` a perfect
  square, so there is no largest `k`; the entry lists `a(0) = 0`, while the first formula evaluates
  to `-1` there, so `n = 0` is not covered by the conjectured formulas.
-/

namespace OMA.S_oeis_a367191

/-- `k` is a positive number such that `k^2 + k*n + n^2` is a perfect square. -/
def Admissible (n k : ℕ) : Prop := 0 < k ∧ IsSquare (k ^ 2 + k * n + n ^ 2)

/-- `a` is the term `a(n)` of A367191: the largest admissible `k`, or `0` if no admissible `k`
exists. -/
def IsValue (n a : ℕ) : Prop :=
  (Admissible n a ∧ ∀ k : ℕ, Admissible n k → k ≤ a) ∨ (a = 0 ∧ ∀ k : ℕ, ¬ Admissible n k)

/-- The conjectured formulas for `a(n)` according to `n mod 4`, for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ a : ℕ, IsValue n a ∧
    (n % 4 = 0 → (a : ℚ) = ((n : ℚ) / 4 - 1) * (3 * (n : ℚ) / 4 + 1)) ∧
    ((n % 4 = 1 ∨ n % 4 = 3) →
      (a : ℚ) = 4 * (((n : ℚ) + 3) / 4 - 1) * (3 * ((n : ℚ) + 3) / 4 - 2)) ∧
    (n % 4 = 2 → (a : ℚ) = 2 * (((n : ℚ) + 2) / 4 - 1) * (3 * ((n : ℚ) + 2) / 4 - 1)) := by
  sorry

end OMA.S_oeis_a367191
