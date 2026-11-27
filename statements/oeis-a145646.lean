import Mathlib

/-!
Barker's three proposed formulas in OEIS A145646 (2019). The source's
executable numerical convention uses R = 10973731.568527 per meter and
rounds n²·10¹⁰/R to the nearest integer. This fixes the input for an exact
mathematical sequence; the underlying measured Rydberg constant is a
separate issue. The ordinary generating function starts at n = 1.
Source: https://oeis.org/A145646
Credit: @shunyaekam
-/

namespace OMA.S_oeis_a145646

def wavelength (n : ℕ) : ℤ :=
  ((2 * n ^ 2 * 10 ^ 16 + 10973731568527) / (2 * 10973731568527) : ℕ)

noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (wavelength n : ℚ)

theorem main :
    (let x : PowerSeries ℚ := PowerSeries.X
     series * ((1 - x) ^ 3 * (1 + x ^ 2)) =
       x * (911 + 912 * x + 910 * x ^ 2 + 913 * x ^ 3 - x ^ 4)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (wavelength n : ℂ) = (-1 / 8 + Complex.I / 8) *
        ((3 + 3 * Complex.I) + (-Complex.I) ^ n + Complex.I ^ (1 + n) -
          (1 + Complex.I) * n - (3645 + 3645 * Complex.I) * (n : ℂ) ^ 2)) ∧
    (∀ n : ℕ, 5 < n → wavelength n =
      3 * wavelength (n-1) - 4 * wavelength (n-2) + 4 * wavelength (n-3) -
      3 * wavelength (n-4) + wavelength (n-5)) := by
  sorry

end OMA.S_oeis_a145646
