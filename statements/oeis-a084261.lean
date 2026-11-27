import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# OEIS A084261

Paul Barry defines A084261 as the binomial transform of the factorials with
zeros inserted between consecutive terms. R. J. Mathar conjectured the
four-term recurrence on 30 November 2012.

Source: https://oeis.org/A084261
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a084261

def interlaced (j : ℕ) : ℤ :=
  if j % 2 = 0 then ((j / 2).factorial : ℤ) else 0

def transform (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * f j

def a (n : ℕ) : ℤ := transform n interlaced

/-- Writing the index as k+3 covers exactly the indices n ≥ 3. -/
theorem main : ∀ k : ℕ,
    2 * a (k + 3) - 4 * a (k + 2) - ((k : ℤ) + 1) * a (k + 1)
      + ((k : ℤ) + 1) * a k = 0 := by
  sorry

end OMA.S_oeis_a084261
