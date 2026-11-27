import Mathlib

/-!
# A sextic counterexample to Euler's sum of powers conjecture

Source: https://www.openproblemgarden.org/op/a_sextic_counterexample_to_eulers_sum_of_powers_conjecture
Credit: @Hennyrick
-/

namespace OMA.S_opg_a_sextic_counterexample_to_eulers_sum_of_powers_conjecture

theorem main :
    ∃ a b c d e f : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧
      a ^ 6 + b ^ 6 + c ^ 6 + d ^ 6 + e ^ 6 = f ^ 6 := by
  sorry

end OMA.S_opg_a_sextic_counterexample_to_eulers_sum_of_powers_conjecture
