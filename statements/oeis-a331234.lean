import Mathlib

/-!
# The largest triangular number with nine positive divisors

Jon E. Schoenfield's OEIS entry A331234 gives the fifth term in factored form
and conjectures that it is the last.
https://oeis.org/A331234
-/

namespace OMA.S_oeis_a331234

theorem main : IsGreatest
    {m : ℕ | (∃ k : ℕ, m = k * (k + 1) / 2) ∧ m.divisors.card = 9}
    ((13558774610046711780701 * 19175002942688032928599 : ℕ) ^ 2) := by
  sorry

end OMA.S_oeis_a331234
