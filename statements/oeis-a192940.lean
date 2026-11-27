import Mathlib

/-!
# A192940: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x)=(x+2)(x+4)...(x+2n).

Source: https://oeis.org/A192940
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A192940 (R. J. Mathar, May 08 2014):
a(n) + (-4*n+1)*a(n-1) + (4*n^2-6*n+1)*a(n-2) = 0.

Conventions:
* p(n,x) = (x+2)(x+4)...(x+2n) is the product of the n factors shown, with p(0,x) = 1
  (the empty product); it is `p n` below, in `ℤ[X]`.
* The reduction of a polynomial by x^2 -> x+1 (see A192232) replaces x^2 by x+1 repeatedly until
  a polynomial of degree at most 1 is left; this is the remainder of the polynomial modulo
  x^2 - x - 1, here `p n %ₘ (X ^ 2 - X - 1)`. Its coefficient of x is its coefficient of index 1.
* The sequence has offset 0 and a(n) is the coefficient of x of the reduction of p(n,x)
  (data 0, 1, 7, 58, 583, ...; EXAMPLE section of the entry:
  p(0,x) = 1 -> 1, p(1,x) = x+2 -> 2 + x, p(2,x) = (x+2)(x+4) -> 9 + 7x,
  p(3,x) = (x+2)(x+4)(x+6) -> 61 + 58x).
* The recurrence involves a(n-2), so it is asserted for every `n ≥ 2`, the smallest index at
  which a(n-2) exists. The terms are integers.
-/

namespace OMA.S_oeis_a192940

open Polynomial

/-- p(n,x) = (x+2)(x+4)...(x+2n). -/
noncomputable def p (n : ℕ) : ℤ[X] := ∏ k ∈ Finset.Icc 1 n, (X + C (2 * (k : ℤ)))

/-- A192940 (offset 0): the coefficient of x of the reduction of p(n,x) by x^2 -> x+1. -/
noncomputable def a (n : ℕ) : ℤ := (p n %ₘ (X ^ 2 - X - 1)).coeff 1

/-- For every `n ≥ 2`, a(n) + (-4*n+1)*a(n-1) + (4*n^2-6*n+1)*a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n + (-4 * (n : ℤ) + 1) * a (n - 1) + (4 * (n : ℤ) ^ 2 - 6 * (n : ℤ) + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a192940
