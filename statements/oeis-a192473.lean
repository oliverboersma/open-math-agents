import Mathlib

/-!
# A192473: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x)=1+x^n+x^(2n+2).

Source: https://oeis.org/A192473
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Jun 07 2019) in OEIS A192473:
a(n) = 4*a(n-1) - 3*a(n-2) - 2*a(n-3) + a(n-4) for n > 4.

Conventions:
* p(n,x) = 1 + x^n + x^(2n+2); it is `p n` below, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 1 and a(n) is the coefficient of x in the reduction of p(n,x)
  (data 4, 9, 23, 58, 149, ...; EXAMPLE section of the entry: p(1,x) = 1+x+x^4 -> 3+4x,
  p(2,x) = 1+x^2+x^6 -> 7+9x, p(3,x) = 1+x^3+x^8 -> 15+23x, p(4,x) = 1+x^4+x^10 -> 37+58x).
  Only `n ≥ 1` is used.
* The recurrence is asserted for every `n > 4`, as in the source; the indices `n - 1, ..., n - 4`
  are then at least 1. The terms are integers.
* Barker's generating function x*(4 - 7*x - x^2 + x^3) / ((1 - 3*x + x^2)*(1 - x - x^2)) is not
  stated separately: given the first four terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a192473

open Polynomial

/-- p(n,x) = 1 + x^n + x^(2n+2). -/
noncomputable def p (n : ℕ) : ℤ[X] := 1 + X ^ n + X ^ (2 * n + 2)

/-- A192473 (offset 1): the coefficient of x in the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n > 4`, a(n) = 4*a(n-1) - 3*a(n-2) - 2*a(n-3) + a(n-4). -/
theorem main : ∀ n : ℕ, 4 < n →
    a n = 4 * a (n - 1) - 3 * a (n - 2) - 2 * a (n - 3) + a (n - 4) := by
  sorry

end OMA.S_oeis_a192473
