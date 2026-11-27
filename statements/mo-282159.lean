import Mathlib

/-!
# Positive integer solutions of a quadratic recurrence

Ilya Bogdanov asks whether a strictly increasing sequence of positive integers
can satisfy the recurrence in MathOverflow question 282159 for every index
starting at one. The integer `d` is fixed throughout the sequence.

Source: https://mathoverflow.net/questions/282159
-/

namespace OMA.S_mo_282159

/-- Index zero is unused. Clearing the positive denominator gives an equality
in the integers and preserves the exact division in the question. -/
theorem main :
    ∃ (d : ℤ) (c : ℕ → ℤ), StrictMonoOn c (Set.Ici 1) ∧
      ∀ n : ℕ, 1 ≤ n →
        0 < c n ∧ (n : ℤ) * c (n + 1) = c n * (c n + n + d) := by
  sorry

end OMA.S_mo_282159
