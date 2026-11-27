import Mathlib

/-!
# A108475: Expansion of (1-3*x) / (1-5*x-5*x^2+x^3).

Source: https://oeis.org/A108475
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jul 08 2009, in the formulas of A108475):
a(n) = A000129(n+1)*A001333(n).

Conventions:
* a(n) (offset 0) is the coefficient of x^n in the power series (1-3x)/(1-5x-5x^2+x^3) over
  the rationals; the denominator has constant term 1, so it is invertible. Data: 1, 2, 15, 84,
  493, 2870, ...
* A000129 are the Pell numbers: P(0) = 0, P(1) = 1, P(n) = 2*P(n-1) + P(n-2).
* A001333: Q(0) = Q(1) = 1, Q(n) = 2*Q(n-1) + Q(n-2) (numerators of continued fraction
  convergents to sqrt(2)).
-/

namespace OMA.S_oeis_a108475

open PowerSeries

/-- A108475(n): the n-th coefficient of (1-3x)/(1-5x-5x^2+x^3). -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n ((1 - 3 * X : PowerSeries ℚ) * (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ)⁻¹)

/-- A000129, the Pell numbers. -/
def pell : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

/-- A001333. -/
def pellLucas : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * pellLucas (n + 1) + pellLucas n

/-- Mathar's conjecture: a(n) = A000129(n+1)*A001333(n). -/
theorem main : ∀ n : ℕ, a n = pell (n + 1) * pellLucas n := by
  sorry

end OMA.S_oeis_a108475
