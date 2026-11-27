import Mathlib

/-!
# A192745: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192745
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A192745 (R. J. Mathar, May 04 2014):
a(n) - n*a(n-1) + (n-2)*a(n-2) + (n-1)*a(n-3) = 0.

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + n! for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 and a(n) is the coefficient of x of the reduction of p(n,x)
  (data 0, 1, 2, 5, 13, 42, ...; EXAMPLE section of the entry: 1 -> 1, 1+x -> 1+x, 2+x+x^2 -> 3+2x,
  6+2x+x^2+x^3 -> 8+5x, 24+6x+2x^2+x^3+x^4 -> 29+13x).
* The recurrence involves a(n-3), so it is asserted for every `n ≥ 3`, the smallest index at
  which a(n-3) exists. The terms are integers.
-/

namespace OMA.S_oeis_a192745

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + n!. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C ((n + 1).factorial : ℤ)

/-- A192745 (offset 0): the coefficient of x of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n ≥ 3`, a(n) - n*a(n-1) + (n-2)*a(n-2) + (n-1)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n - (n : ℤ) * a (n - 1) + ((n : ℤ) - 2) * a (n - 2) + ((n : ℤ) - 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a192745
