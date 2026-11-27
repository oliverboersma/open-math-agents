import Mathlib

/-!
# Is the Goldbach conjecture easier if we allow 1 as a prime?

Source: https://mathoverflow.net/questions/439892/is-the-goldbach-conjecture-easier-if-we-allow-1-as-a-prime
Credit: @nokiexow

Both assertions concern every even integer greater than two. Only the
allowed summands change; the hypothesis is not restricted to one integer.
-/

namespace OMA.S_mo_439892

def GoldbachWith (allowed : ℕ → Prop) : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ a b : ℕ, allowed a ∧ allowed b ∧ a + b = n

theorem main : GoldbachWith (fun p => p = 1 ∨ p.Prime) → GoldbachWith Nat.Prime := by
  sorry

end OMA.S_mo_439892

