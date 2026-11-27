import Mathlib

/-!
# A330715: a(1), a(2), a(3) = 1; a(n) = (a(n-1) mod a(n-3)) + a(n-2) + 1.

Source: https://oeis.org/A330715
Credit: @JeremyDevs

Formalizes two of the conjectures of Colin Barker (Dec 28 2019) recorded in OEIS A330715:
* a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4) for n > 9;
* a(n) = (99 - 3*(-1)^n - 24*n + 2*n^2) / 8 for n > 5.

Conventions:
* The sequence has offset 1: a(1) = a(2) = a(3) = 1 and
  a(n) = (a(n-1) mod a(n-3)) + a(n-2) + 1 for n ≥ 4, written with `n + 4` in place of `n`.
  The terms are natural numbers 1, 1, 1, 2, 2, 3, 4, 4, 6, 7, 10, 12, 16, ... The value `a 0 = 0`
  is a placeholder for the unused index 0; it enters neither the recursion nor the statement.
* The recurrence has negative coefficients, so both sides are compared in `ℤ`. For `n > 9` the
  indices `n - 1`, `n - 3`, `n - 4` are genuine (no truncation).
* The closed form is stated without division, as
  `8 * a(n) = 99 - 3*(-1)^n - 24*n + 2*n^2` in `ℤ`, which is the same assertion.
* Barker's third conjecture, the generating function
  x*(1 - x - x^2 + 2*x^3 - x^4 + x^6 - 2*x^7 + 2*x^8) / ((1 - x)^3*(1 + x)), is not stated
  separately: given the first nine terms it is the same assertion as the recurrence for n > 9.
-/

namespace OMA.S_oeis_a330715

/-- A330715 (offset 1): a(1) = a(2) = a(3) = 1, a(n) = (a(n-1) mod a(n-3)) + a(n-2) + 1. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => a (n + 3) % a (n + 1) + a (n + 2) + 1

/-- Barker's conjectures: the linear recurrence for `n > 9` and the closed form for `n > 5`. -/
theorem main :
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 2 * (a (n - 1) : ℤ) - 2 * (a (n - 3) : ℤ) + (a (n - 4) : ℤ)) ∧
    (∀ n : ℕ, 5 < n →
      8 * (a n : ℤ) = 99 - 3 * (-1 : ℤ) ^ n - 24 * (n : ℤ) + 2 * (n : ℤ) ^ 2) := by
  sorry

end OMA.S_oeis_a330715
