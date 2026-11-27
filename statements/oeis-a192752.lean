import Mathlib

/-!
# A192752: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments.

Source: https://oeis.org/A192752
Credit: @JeremyDevs

Formalizes the closed form conjectured in OEIS A192752 (R. J. Mathar, May 04 2014):
a(n) = A000071(n+3) + 5*A000071(n+2) - 2*A000071(n+1).

Conventions:
* The titular polynomial is defined recursively (COMMENTS section of the entry) by
  p(n,x) = x*p(n-1,x) + 4*n+3 for n > 0, where p(0,x) = 1; it is `p n` below, in `ℤ[X]`,
  with the recursion written with `n + 1` in place of `n`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its constant term is its coefficient of index 0.
* The sequence has offset 0 and a(n) is the constant term of the reduction of p(n,x)
  (data 1, 7, 12, 23, 39, 66, ...; for instance p(1,x) = x + 7 -> 7 + x, p(2,x) = x^2 + 7x + 11 -> 12 + 8x).
* A000071(n) = Fibonacci(n) - 1 (the name of that entry), with Fibonacci(0) = 0,
  Fibonacci(1) = 1: here `(Nat.fib n : ℤ) - 1`.
* The closed form is asserted for every `n ≥ 0`, the full range of the offset-0 sequence.
* The same comment also records "G.f.: ( 1+5*x-2*x^2 ) / ( (x-1)*(x^2+x-1) ), and first differences in A022136".
  These are not stated separately: the generating function is the one of the closed form.
-/

namespace OMA.S_oeis_a192752

open Polynomial

/-- p(0,x) = 1, p(n,x) = x*p(n-1,x) + 4*n+3. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (4 * ((n : ℤ) + 1) + 3)

/-- A192752 (offset 0): the constant term of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 0

/-- For every `n`, a(n) = A000071(n+3) + 5*A000071(n+2) - 2*A000071(n+1). -/
theorem main : ∀ n : ℕ,
    a n = ((Nat.fib (n + 3) : ℤ) - 1) + 5 * ((Nat.fib (n + 2) : ℤ) - 1) - 2 * ((Nat.fib (n + 1) : ℤ) - 1) := by
  sorry

end OMA.S_oeis_a192752
