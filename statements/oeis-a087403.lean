import Mathlib

/-!
# The nonvanishing conjecture for OEIS A087403

Source: https://oeis.org/A087403 (OEIS Foundation, CC BY-SA 4.0).
Nicholas S. Wedd's sequence takes the least prime obtained by repeating
the decimal representation of n a positive number of times and
appending a digit 1. The value is zero if there is no such prime.
The original conjecture says no term is zero. Farideh Firoozbakht
recorded a refutation of this conjecture in January 2015.
-/

namespace OMA.S_oeis_a087403

def repeatDecimal (n copies : ℕ) : ℕ :=
  ∑ j ∈ Finset.range copies, n * (10 ^ (Nat.digits 10 n).length) ^ j

noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ copies : ℕ, 0 < copies ∧ p = 10 * repeatDecimal n copies + 1}

theorem main : ∀ n : ℕ, 0 < n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a087403
