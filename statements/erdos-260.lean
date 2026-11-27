import Mathlib

/-!
# Erdős Problem 260

Source: https://www.erdosproblems.com/260
Credit: @mattdorman

The source asks: let `a₁ < a₂ < ⋯` be an increasing sequence such that `aₙ / n → ∞`. Is the sum
`∑ₙ aₙ / 2^{aₙ}` irrational?

Reading used here: the `aₙ` are natural numbers (the sum `∑ aₙ / 2^{aₙ}` is the setting of the
source); the sequence is indexed from `0`, so `a n` stands for `a_{n+1}` and the growth condition is
`a n / (n + 1) → ∞`. The series converges because `a` is strictly increasing. The statement below
is the affirmative answer.
-/

open Filter

namespace OMA.S_erdos_260

theorem main :
    ∀ a : ℕ → ℕ, StrictMono a →
      Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) + 1)) atTop atTop →
        Irrational (∑' n : ℕ, (a n : ℝ) / 2 ^ (a n)) := by
  sorry

end OMA.S_erdos_260
