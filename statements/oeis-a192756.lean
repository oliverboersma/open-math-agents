import Mathlib

/-!
# A192756: Coefficient of x in the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments

Source: https://oeis.org/A192756
Credit: @ivillar

Clark Kimberling's sequence (offset 0): the polynomial p(n,x) is defined recursively by
p(n,x) = x*p(n-1,x) + 5n for n > 0, with p(0,x) = 1 (the comment writes x*(n-1,x) for
x*p(n-1,x), as the Mathematica program confirms). Reducing by x^2 -> x+1 means replacing x^2 by
x + 1 repeatedly until the degree is at most 1 (see A192232 and A192744); the result is the
remainder of p(n,x) on division by the monic polynomial x^2 - x - 1. a(n) is the coefficient of x
in it.

Conjecture (R. J. Mathar, May 04 2014):
  G.f.: -x*(1+3*x+x^2) / ( (x^2+x-1)*(x-1)^2 ).
  a(n) = A001924(n)+3*A001924(n-1)+A001924(n-2).
  Partial sums of A166863.
Here A001924 is "Apply partial sum operator twice to Fibonacci numbers" (offset 0) and A166863 is
a(1) = 1, a(2) = 5, a(n) = a(n-1) + a(n-2) + 5 (offset 1), so the last claim reads
a(n) = A166863(1) + ... + A166863(n).
-/

namespace OMA.S_oeis_a192756

open Polynomial

/-- p(0,x) = 1 and p(n,x) = x*p(n-1,x) + 5n for n > 0. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (5 * ((n : ℤ) + 1))

/-- The reduction of a polynomial by x^2 -> x+1: its remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n): the coefficient of x in the reduction of p(n,x) by x^2 -> x+1 (offset 0). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 1

/-- A001924: the partial sum operator applied twice to the Fibonacci numbers (offset 0). -/
def A001924 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1), Nat.fib j

/-- A166863 (offset 1): a(1) = 1, a(2) = 5, a(n) = a(n-1) + a(n-2) + 5; the value at 0 is unused. -/
def A166863 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | n + 3 => A166863 (n + 2) + A166863 (n + 1) + 5

/-- The conjectured g.f. -x*(1+3*x+x^2) / ((x^2+x-1)*(x-1)^2), as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (-PowerSeries.X * (1 + 3 * PowerSeries.X + PowerSeries.X ^ 2)) *
    ((PowerSeries.X ^ 2 + PowerSeries.X - 1) * (PowerSeries.X - 1) ^ 2)⁻¹

/-- Mathar's conjecture: the g.f., the A001924 formula (for n ≥ 2, so that n - 2 is an index) and
the partial sums of A166863. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) = G ∧
    (∀ n : ℕ, 2 ≤ n → a n = A001924 n + 3 * A001924 (n - 1) + A001924 (n - 2)) ∧
    (∀ n : ℕ, a n = ∑ k ∈ Finset.Icc 1 n, (A166863 k : ℤ)) := by
  sorry

end OMA.S_oeis_a192756
