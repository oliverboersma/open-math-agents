import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Defs

/-!
# A recurrence for OEIS A191993

R. J. Mathar's recurrence begins where all three terms exist. The sequence
starts at `n = 1`, so the recurrence index below is `n = t + 3`. The exact
rational half agrees with the source since the positive-index central
binomial coefficients are even.

Source: https://oeis.org/A191993
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a191993

def a (n : ℕ) : ℚ := 3 ^ (n - 1) + (Nat.centralBinom n : ℚ) / 2

theorem main : ∀ t : ℕ, let n : ℚ := (t : ℚ) + 3
    n * (n - 3) * a (t + 3) - (7 * n ^ 2 - 23 * n + 12) * a (t + 2) +
    6 * (2 * n - 3) * (n - 2) * a (t + 1) = 0 := by
  sorry

end OMA.S_oeis_a191993
