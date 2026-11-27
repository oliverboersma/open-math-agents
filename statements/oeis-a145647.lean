import Mathlib

/-! Barker’s 2019 conjectures for the forward differences of the hydrogen
wavelength sequence using its published Maple calibration. Sources:
https://oeis.org/A145647 and https://oeis.org/A145646. Credit: @shunyaekam. -/

namespace OMA.S_oeis_a145647

def wavelength (n : ℕ) : ℤ :=
  ((2 * n ^ 2 * 10 ^ 16 + 10973731568527) / (2 * 10973731568527) : ℕ)

def gap (n : ℕ) : ℤ := wavelength (n + 1) - wavelength n

noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (gap n : ℚ)

theorem main :
    (let x : PowerSeries ℚ := PowerSeries.X
     series * ((1 - x) ^ 2 * (1 + x ^ 2)) =
       x * (2734 - 912 * x + 2735 * x ^ 2 - 912 * x ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → (gap n : ℂ) =
      (3646 + (-Complex.I) ^ n + Complex.I ^ n + 7290 * (n : ℂ)) / 4) ∧
    (∀ n : ℕ, 4 < n → gap n =
      2 * gap (n-1) - 2 * gap (n-2) + 2 * gap (n-3) - gap (n-4)) := by
  sorry

end OMA.S_oeis_a145647
