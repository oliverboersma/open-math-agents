import Mathlib

/-!
# Odd greedy expansion

https://en.wikipedia.org/wiki/Odd_greedy_expansion

Does the odd greedy algorithm terminate for every positive rational number
whose reduced denominator is odd? At each step it uses the largest unused
odd unit fraction that is at most the remainder.

Credit: @grp06
-/

namespace OMA.S_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion

/-- A finite odd greedy expansion records the algorithm's choices in order. -/
def IsOddGreedyExpansion (q : ℚ) (denominators : List ℕ) : Prop :=
  (denominators.map fun d => 1 / (d : ℚ)).sum = q ∧
    ∀ (i : ℕ) (hi : i < denominators.length),
      let used := denominators.take i
      let remainder := q - (used.map fun d => 1 / (d : ℚ)).sum
      IsLeast {d : ℕ | Odd d ∧ d ∉ used ∧ 1 / (d : ℚ) ≤ remainder} denominators[i]

theorem main :
    ∀ q : ℚ, 0 < q → Odd q.den → ∃ denominators : List ℕ, IsOddGreedyExpansion q denominators := by
  sorry

end OMA.S_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion

