import Mathlib

/-!
# A192358: Coefficients of x in the reduction of the polynomial p(n,x)=(1/2)((x+3)^n+(x-3)^n) by x^2->x+1.

Source: https://oeis.org/A192358
Credit: @JeremyDevs

Formalizes the conjecture of Colin Barker (Nov 22 2012) recorded in OEIS A192358:
a(n) = 2*a(n-1) + 19*a(n-2) - 20*a(n-3) - 55*a(n-4).

Conventions:
* p(n,x) = (1/2)((x+3)^n + (x-3)^n) is a polynomial with rational (in fact integer)
  coefficients; it is `p n` below, in `ℚ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 1 and its first term comes from p(0,x) = 1 (data 0, 1, 1, 29, 57, ...:
  p(0,x) = 1 -> 1, p(1,x) = x -> x, p(2,x) = x^2 + 9 -> 10 + x, p(3,x) = x^3 + 27x -> 1 + 29x),
  so a(n) is the coefficient of x in the reduction of p(n-1,x). Only `n ≥ 1` is used.
* The recurrence involves a(n-4), so it is asserted for every `n > 4`, where all the indices
  `n - 1, ..., n - 4` are at least 1. The terms are compared in `ℚ`.
* Barker's generating function x^2*(8*x^2-x+1)/((5*x^2+5*x+1)*(11*x^2-7*x+1)) is not stated
  separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192358

open Polynomial

/-- p(n,x) = (1/2)((x+3)^n + (x-3)^n). -/
noncomputable def p (n : ℕ) : ℚ[X] := C (1 / 2) * ((X + C 3) ^ n + (X - C 3) ^ n)

/-- A192358 (offset 1): the coefficient of x in the reduction of p(n-1,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℚ := (p (n - 1) %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n > 4`, a(n) = 2*a(n-1) + 19*a(n-2) - 20*a(n-3) - 55*a(n-4). -/
theorem main : ∀ n : ℕ, 4 < n →
    a n = 2 * a (n - 1) + 19 * a (n - 2) - 20 * a (n - 3) - 55 * a (n - 4) := by
  sorry

end OMA.S_oeis_a192358
