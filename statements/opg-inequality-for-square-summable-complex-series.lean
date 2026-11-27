import Mathlib

/-!
# Inequality for square summable complex series

Source: https://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series

The sequence is indexed by positive integers. In the input square sum, `n + 1`
enumerates those indices, so `a 0` is unused. The two sums on the other side
both start at zero.

Ibragimov and Salimova proved the inequality in
https://doi.org/10.4171/EM/278.
-/

namespace OMA.S_opg_inequality_for_square_summable_complex_series

theorem main : ∀ a : ℕ → ℂ, Summable (fun n : ℕ => ‖a (n + 1)‖ ^ 2) →
    (6 / Real.pi ^ 2) *
        (∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2) ≤
      ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
  sorry

end OMA.S_opg_inequality_for_square_summable_complex_series
