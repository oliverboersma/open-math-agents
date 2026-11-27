import Mathlib.Data.Rat.Floor

/-!
# OEIS A048590

Harvey P. Dale's linear recurrence for the Pisot ceiling sequence L(8, 9).
The sequence has offset zero. Taha Kabiri established the recurrence from
index six in 2026.

https://oeis.org/A048590
-/

namespace OMA.S_oeis_a048590

/-- Starting at eight and nine, take the ceiling of the square of the latest
term divided by the previous term. -/
def a : ℕ → ℕ
  | 0 => 8
  | 1 => 9
  | n + 2 => ⌈(a (n + 1) : ℚ) ^ 2 / (a n : ℚ)⌉₊

theorem main : ∀ n : ℕ, 6 ≤ n →
    (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) +
      (a (n - 4) : ℤ) - (a (n - 5) : ℤ) := by
  sorry

end OMA.S_oeis_a048590
