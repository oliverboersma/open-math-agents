import Mathlib

/-!
# A002791: Irvine's formula 4*sigma(n) - f(n mod 6)

Source: https://oeis.org/A002791
Credit: @ivillar

A002791 (offset 1): a(n) = Sum_{d|n, d <= 4} d^2 + 4*Sum_{d|n, d>4} d; data 1, 5, 10, 21, 21, 38,
29, 53, ...
Conjecture (Sean A. Irvine, May 17 2014): a(n) = 4*sigma(n) - f(n mod 6), where f(0) = 10,
f(1) = 3, f(2) = 7, f(3) = 6, f(4) = 7, f(5) = 3.

Formalization notes.
* The sums run over the positive divisors d of n (`Nat.divisors`); sigma is the sum of the
  divisors, `ArithmeticFunction.sigma 1`. The identity is stated in ℤ for every n ≥ 1.
* This formalizes the second of Irvine's two conjectured formulas. (The first, an inverse
  Moebius transform of a g.f. printed as (x + 2x^2 + 2x^3 + 2x^4 - 3x^4)/(1 - x)^2, is not
  stated here.)
-/

namespace OMA.S_oeis_a002791

/-- A002791: a(n) = Sum_{d|n, d <= 4} d^2 + 4*Sum_{d|n, d>4} d. -/
def a (n : ℕ) : ℕ :=
  (∑ d ∈ n.divisors with d ≤ 4, d ^ 2) + 4 * ∑ d ∈ n.divisors with 4 < d, d

/-- Irvine's correction term f(n mod 6). -/
def f (r : ℕ) : ℤ :=
  match r with
  | 0 => 10
  | 1 => 3
  | 2 => 7
  | 3 => 6
  | 4 => 7
  | _ => 3

/-- Irvine's conjecture: a(n) = 4*sigma(n) - f(n mod 6) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = 4 * (ArithmeticFunction.sigma 1 n : ℤ) - f (n % 6) := by
  sorry

end OMA.S_oeis_a002791
