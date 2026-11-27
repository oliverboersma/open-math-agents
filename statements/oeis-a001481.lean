import Mathlib.Data.Nat.Basic

/-!
J. Lowell's conjecture at https://oeis.org/A001481/internal.

The listed zero-summand exceptions start at 2, so this states the claim for
positive exponents. The separate exponent-zero case is 0 + 1.
-/

namespace OMA.S_oeis_a001481

def SumTwoSquares (n : ℕ) : Prop := ∃ x y : ℕ, x ^ 2 + y ^ 2 = n

theorem main : ∀ a b k : ℕ, 0 < k → a ≠ b →
    SumTwoSquares a → SumTwoSquares b → a + b = 2 ^ k →
    a = 0 ∨ b = 0 := by
  sorry

end OMA.S_oeis_a001481
