import Mathlib.Data.Nat.Prime.Defs

/-!
# A083382: Schinzel's conjecture on prime counts in rows

Source: https://oeis.org/A083382
Credit: @hiattco

Place the integers from 1 through `n^2` in `n` consecutive rows of length `n`.
The minimum prime count among these rows is positive for every `n > 1`
exactly when each row contains a prime.
-/

namespace OMA.S_oeis_a083382

/-- Each zero-indexed row contains a prime. The row begins at `row * n + 1`
and ends at `(row + 1) * n`. -/
theorem main : ∀ n : ℕ, 1 < n → ∀ row : ℕ, row < n →
    ∃ p : ℕ, Nat.Prime p ∧ row * n < p ∧ p ≤ (row + 1) * n := by
  sorry

end OMA.S_oeis_a083382
