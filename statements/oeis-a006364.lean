import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Ring.Parity

/-! Yanev's signed formula for OEIS A006364, using its increasing enumeration. -/

namespace OMA.S_oeis_a006364

/-- A000120, the number of ones in the binary expansion. -/
def bitCount (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The binary digits above the last bit have even weight. -/
def Qualifies (m : ℕ) : Prop := bitCount (m / 2) % 2 = 0

/-- A006364, using the one-based index of the OEIS entry. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Qualifies (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = 2 * (n : ℤ) + (-1 : ℤ) ^ (n - bitCount (n - 1)) - (3 + (-1 : ℤ) ^ n) / 2 := by
  sorry

end OMA.S_oeis_a006364
