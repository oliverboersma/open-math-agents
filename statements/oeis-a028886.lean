import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Kurkov's primality criterion for OEIS A028886

Source: https://oeis.org/A028886/internal
Mikhail Kurkov, 18 December 2025.
The bounds on both integer variables are positive, so they can be stated over naturals.
-/

namespace OMA.S_oeis_a028886

theorem main : ∀ m : ℕ, 2 < m →
    (Nat.Prime ((2 * m + 1) ^ 2 - 8) ↔
      ∀ q : ℕ, 1 ≤ q → q ≤ 2 * (m - 2) → ¬ IsSquare (q * (m + 1) + q.choose 2 + 1)) := by
  sorry

end OMA.S_oeis_a028886
