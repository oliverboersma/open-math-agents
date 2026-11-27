import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt

/-!
# Shunia's square-root formula for OEIS A002457

Source: https://oeis.org/A002457/internal
Joseph M. Shunia, 11 September 2025.
The natural square root is the floor of the nonnegative square root.
-/

namespace OMA.S_oeis_a002457

theorem main : ∀ n : ℕ, 0 < n →
    Nat.sqrt (((16 : ℕ) ^ n + 1) ^ (2 * n + 1)) % (16 ^ n) =
      (2 * n + 1).factorial / n.factorial ^ 2 := by
  sorry

end OMA.S_oeis_a002457
