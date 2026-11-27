import Mathlib

/-!
# A192924: Constant term in the reduction by (x^2->x+1) of the polynomial p(n,x) defined below at Comments.

Source: https://oeis.org/A192924
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A192924 (R. J. Mathar, May 08 2014):
a(n) + 2*(-n+1)*a(n-1) + (n^2-3*n-1)*a(n-2) + 3*(n-2)*a(n-3) + a(n-4) = 0.

Conventions:
* The titular polynomial is defined (COMMENTS section of the entry) by
  p(n,x) = n*p(n-1,x) + (x^2)*p(n-2,x), with p(0,x) = 1, p(1,x) = x; it is `p n` below, in
  `ℤ[X]`, with the recursion written with `n + 2` in place of `n`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its constant term is its coefficient of index 0.
* The sequence has offset 0 and a(n) is the constant term of the reduction of p(n,x)
  (data 1, 0, 1, 4, 20, 115, 761, ...; for instance p(2,x) = 2x + x^2 -> 1 + 3x).
* The recurrence involves a(n-4), so it is asserted for every `n ≥ 4`, the smallest index at
  which a(n-4) exists. The terms are integers.
-/

namespace OMA.S_oeis_a192924

open Polynomial

/-- p(0,x) = 1, p(1,x) = x, p(n,x) = n*p(n-1,x) + x^2*p(n-2,x). -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => C (((n + 2 : ℕ) : ℤ)) * p (n + 1) + X ^ 2 * p n

/-- A192924 (offset 0): the constant term of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 0

/-- For every `n ≥ 4`,
a(n) + 2*(-n+1)*a(n-1) + (n^2-3*n-1)*a(n-2) + 3*(n-2)*a(n-3) + a(n-4) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + 2 * (-(n : ℤ) + 1) * a (n - 1) + ((n : ℤ) ^ 2 - 3 * (n : ℤ) - 1) * a (n - 2)
      + 3 * ((n : ℤ) - 2) * a (n - 3) + a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a192924
