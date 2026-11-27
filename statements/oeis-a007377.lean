import Mathlib

/-!
# The largest power of two whose decimal digits are all nonzero (OEIS A007377)

Source: https://oeis.org/A007377, example by N. J. A. Sloane, February 10, 2023.
Credit: @Mmexicann
-/

namespace OMA.S_oeis_a007377

/-- The largest exponent for which the decimal expansion of a power of two omits zero is 86. -/
theorem main : IsGreatest {k : ℕ | 0 ∉ Nat.digits 10 (2 ^ k)} 86 := by
  sorry

end OMA.S_oeis_a007377
