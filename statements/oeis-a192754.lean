import Mathlib

/-!
# A192754: Constant term of the reduction by x^2->x+1 of the polynomial p(n,x) defined below in Comments

Source: https://oeis.org/A192754
Credit: @ivillar

Clark Kimberling's sequence (offset 0): the polynomial p(n,x) is defined recursively by
p(n,x) = x*p(n-1,x) + 5*n + 1 for n > 0, with p(0,x) = 1. Reducing by x^2 -> x+1 means replacing
x^2 by x + 1 repeatedly until the degree is at most 1 (see A192232 and A192744); the result is the
remainder of p(n,x) on division by the monic polynomial x^2 - x - 1. a(n) is its constant term.

Conjecture (R. J. Mathar, May 04 2014):
  G.f.: ( 1+4*x ) / ( (x-1)*(x^2+x-1) ), partial sums of A022095.
  a(n) = A000071(n+3)+4*A000071(n+2).
Here A022095 is the Fibonacci sequence beginning 1, 5 (offset 0), so the partial-sum claim reads
a(n) = A022095(0) + ... + A022095(n), and A000071(m) = Fibonacci(m) - 1.
-/

namespace OMA.S_oeis_a192754

open Polynomial

/-- p(0,x) = 1 and p(n,x) = x*p(n-1,x) + 5*n + 1 for n > 0. -/
noncomputable def p : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => X * p n + C (5 * ((n : ℤ) + 1) + 1)

/-- The reduction of a polynomial by x^2 -> x+1: its remainder modulo x^2 - x - 1. -/
noncomputable def reduce (f : ℤ[X]) : ℤ[X] := f %ₘ (X ^ 2 - X - 1)

/-- a(n): the constant term of the reduction of p(n,x) by x^2 -> x+1 (offset 0). -/
noncomputable def a (n : ℕ) : ℤ := (reduce (p n)).coeff 0

/-- A000071: a(n) = Fibonacci(n) - 1. -/
def A000071 (n : ℕ) : ℤ := Nat.fib n - 1

/-- A022095: Fibonacci sequence beginning 1, 5 (offset 0). -/
def A022095 : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => A022095 (n + 1) + A022095 n

/-- The conjectured g.f. (1+4*x) / ((x-1)*(x^2+x-1)), as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (1 + 4 * PowerSeries.X) * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1))⁻¹

/-- Mathar's conjecture: the g.f., the partial sums of A022095 and the A000071 formula. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) = G ∧
    (∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1), (A022095 k : ℤ)) ∧
    (∀ n : ℕ, a n = A000071 (n + 3) + 4 * A000071 (n + 2)) := by
  sorry

end OMA.S_oeis_a192754
