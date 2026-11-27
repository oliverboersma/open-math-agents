import Mathlib

/-!
# A108476: Expansion of (1-4*x)/(1-6*x-12*x^2+8*x^3).

Source: https://oeis.org/A108476
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jul 08 2009, in the formulas of A108476):
a(n) = A002605(n+1)*A026150(n).

Conventions:
* a(n) (offset 0) is the coefficient of x^n in the power series (1-4x)/(1-6x-12x^2+8x^3) over
  the rationals; the denominator has constant term 1, so it is invertible. Data: 1, 2, 24, 160,
  1232, 9120, ...
* A002605: b(0) = 0, b(1) = 1, b(n) = 2*(b(n-1) + b(n-2)).
* A026150: c(0) = c(1) = 1, c(n+2) = 2*c(n+1) + 2*c(n).
-/

namespace OMA.S_oeis_a108476

open PowerSeries

/-- A108476(n): the n-th coefficient of (1-4x)/(1-6x-12x^2+8x^3). -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n ((1 - 4 * X : PowerSeries ℚ) * (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- A002605. -/
def A002605 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * (A002605 (n + 1) + A002605 n)

/-- A026150. -/
def A026150 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * A026150 (n + 1) + 2 * A026150 n

/-- Mathar's conjecture: a(n) = A002605(n+1)*A026150(n). -/
theorem main : ∀ n : ℕ, a n = A002605 (n + 1) * A026150 n := by
  sorry

end OMA.S_oeis_a108476
