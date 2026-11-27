import Mathlib

/-!
# Finiteness of OEIS A006716

Source: https://oeis.org/A006716
Credit: @Mmexicann

The sequence contains the positive squares whose decimal digits all belong
to the set {1, 4, 9}. Its first terms include 1, 4, 9 and 49.
-/

namespace OMA.S_oeis_a006716

theorem main :
    Set.Finite {n : ℕ | 0 < n ∧ IsSquare n ∧
      ∀ d ∈ Nat.digits 10 n, d = 1 ∨ d = 4 ∨ d = 9} := by
  sorry

end OMA.S_oeis_a006716
