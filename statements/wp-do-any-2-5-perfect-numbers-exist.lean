import Mathlib

/-!
# Do any (2, 5)-perfect numbers exist?

Source: https://en.wikipedia.org/wiki/Superperfect_number#Generalizations
Credit: @mmiranda2

The divisor sum is applied twice to a positive integer. Cohen and te Riele
conjectured that the resulting value is never five times the original integer.
Reference: https://doi.org/10.1080/10586458.1996.10504580
-/

namespace OMA.S_wp_do_any_2_5_perfect_numbers_exist

theorem main :
    ∃ n : ℕ, 0 < n ∧ ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 n) = 5 * n := by
  sorry

end OMA.S_wp_do_any_2_5_perfect_numbers_exist

