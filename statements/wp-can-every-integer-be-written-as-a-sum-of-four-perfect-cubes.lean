import Mathlib

/-!
# Can every integer be written as a sum of four perfect cubes?

Source: https://en.wikipedia.org/wiki/Sum_of_four_cubes_problem
Credit: @sauronsoul-bit

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes

-- definitions the statement needs (no sorry, no axiom)

theorem main : ∀ n : ℤ, ∃ a b c d : ℤ, n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 := by
  sorry

end OMA.S_wp_can_every_integer_be_written_as_a_sum_of_four_perfect_cubes
