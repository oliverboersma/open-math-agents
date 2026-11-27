import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# OEIS A068128

The conjecture in comment 3 concerns every triangular target T, extending
the sequence's own defining target T = 6. The set below counts distinct
triangular numbers, and the digit sum is taken in base ten.

Source: https://oeis.org/A068128
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a068128

def triangular (n : ℕ) : ℕ := (n + 1).choose 2

theorem main : ∀ n : ℕ, Set.Infinite
    {t : ℕ | (∃ k : ℕ, t = triangular k) ∧ (Nat.digits 10 t).sum = triangular n} := by
  sorry

end OMA.S_oeis_a068128
