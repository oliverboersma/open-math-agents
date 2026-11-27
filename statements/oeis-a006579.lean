import Mathlib

/-!
# The gcd sum at composite indices (OEIS A006579)

Source: https://oeis.org/A006579, conjecture of Thomas Ordowski, June 11, 2025.
Credit: @Mmexicann
-/

namespace OMA.S_oeis_a006579

/-- Sum of the gcds of `n` with the positive integers strictly below `n`. -/
def gcdSum (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum (fun k => Nat.gcd n k)

theorem main : ∀ n : ℕ, 1 < n → ¬ n.Prime →
    ¬ Int.ModEq (n : ℤ) (gcdSum n : ℤ) (-1) := by
  sorry

end OMA.S_oeis_a006579
