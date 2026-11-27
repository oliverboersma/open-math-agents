import Mathlib.Data.Int.Basic

/-!
# The conjectured OEIS formula for A203159

Source: https://oeis.org/A203159
The sequence starts at index one, and its value at zero is adjoined.
The recurrence starts at the first index with all positive-indexed terms.
-/

namespace OMA.S_oeis_a203159

/-- The full product and the omission sum for the first n positive even integers. -/
def products : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (p, e) := products n
    let t := 2 * ((n : ℤ) + 1)
    (p * t, e * t + p)

def a (n : ℕ) : ℤ := (products n).2

theorem main : ∀ n : ℕ, 2 < n →
    a n + 2 * (-2 * (n : ℤ) + 1) * a (n - 1) +
      4 * ((n : ℤ) - 1) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a203159
