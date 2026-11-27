import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Barker's recurrence and the companion identity for OEIS A303647

Source: https://oeis.org/A303647/internal
Colin Barker, 28 April 2018. The companion identity uses the shift corrected on
18 September 2026. The offset-one sequences are padded with zero at index zero.
-/

namespace OMA.S_oeis_a303647

noncomputable def ratio : ℝ := 1 / ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1)

noncomputable def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌈ratio * (a (n + 1) : ℝ) + 1⌉

noncomputable def a301483 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊ratio * (a301483 (n + 1) : ℝ)⌋

-- Coefficients of (1 - 3X - X^2)/(1 - 4X + 2X^3 + X^4).
def a195350 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 10
  | n + 4 => 4 * a195350 (n + 3) - 2 * a195350 (n + 1) - a195350 n

-- Coefficients of 1/(1 - 4X + 2X^3 + X^4).
def a195339 : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 16
  | 3 => 62
  | n + 4 => 4 * a195339 (n + 3) - 2 * a195339 (n + 1) - a195339 n

theorem main :
    (∀ n : ℕ, 2 < n → a n = a301483 (n + 2) - a195350 (n + 2) + a195339 (n - 3)) ∧
    ((1 - PowerSeries.X) * (1 - 3 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) *
      PowerSeries.mk a = PowerSeries.X * (1 + PowerSeries.X + PowerSeries.X ^ 2)) ∧
    (∀ n : ℕ, 4 < n → a n = 4 * a (n - 1) - 2 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a303647
