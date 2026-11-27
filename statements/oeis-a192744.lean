import Mathlib

/-!
# A192744: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192744
Credit: @JeremyDevs

Formalizes the two conjectures of R. J. Mathar recorded in OEIS A192744:
* (May 04 2014) a(n) + (-n-2)*a(n-1) + 2*(n-1)*a(n-2) + 3*a(n-3) + (-n+2)*a(n-4) = 0;
* (Dec 16 2015) (-n+2)*a(n) + (n^2-n-1)*a(n-1) + (-n^2+3*n-3)*a(n-2) - (n-1)^2*a(n-3) = 0.

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + n! for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its constant term is its coefficient of index 0.
* The sequence has offset 0 and a(n) is the constant term of the reduction of p(n,x)
  (data 1, 1, 3, 8, 29, 133, ...; EXAMPLE section of the entry: 1 -> 1, 1+x -> 1+x, 2+x+x^2 -> 3+2x,
  6+2x+x^2+x^3 -> 8+5x, 24+6x+2x^2+x^3+x^4 -> 29+13x).
* The first recurrence involves a(n-4), so it is asserted for every `n ≥ 4`; the second involves
  a(n-3), so it is asserted for every `n ≥ 3`. These are the smallest indices at which all the
  terms exist. The terms are integers.
-/

namespace OMA.S_oeis_a192744

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + n!. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C ((n + 1).factorial : ℤ)

/-- A192744 (offset 0): the constant term of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 0

/-- Mathar's two conjectured recurrences for A192744. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      a n + (-(n : ℤ) - 2) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) + 3 * a (n - 3)
        + (-(n : ℤ) + 2) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      (-(n : ℤ) + 2) * a n + ((n : ℤ) ^ 2 - (n : ℤ) - 1) * a (n - 1)
        + (-(n : ℤ) ^ 2 + 3 * (n : ℤ) - 3) * a (n - 2) - ((n : ℤ) - 1) ^ 2 * a (n - 3) = 0) := by
  sorry

end OMA.S_oeis_a192744
