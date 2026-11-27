import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Dist

/-!
# OEIS A358616: first positions of row minima in the Gilbreath array

Sources: https://oeis.org/A358616 and https://oeis.org/A036262
Credit: @SiraTone

The prime row is row zero here; columns are indexed from zero internally.
Thus the OEIS position k (which starts at one) corresponds to column k - 1.
The prime row and its first difference row both have minimum position one,
matching the initial two terms of A358616.

We express occurrence of a position directly: its entry is a global row
minimum and every earlier entry is strictly larger. This is equivalent to
being the first occurrence of the least term, without choosing a search bound
or assuming the original Gilbreath conjecture.
-/

namespace OMA.S_oeis_a358616

/-- Iterated absolute differences of the primes, with the prime row numbered zero. -/
noncomputable def row : ℕ → ℕ → ℕ
  | 0, j => Nat.nth Nat.Prime j
  | n + 1, j => Nat.dist (row n (j + 1)) (row n j)

/-- Every positive position occurs as the first position of a row minimum. -/
theorem main :
    ∀ k : ℕ, 0 < k → ∃ n : ℕ,
      (∀ j : ℕ, row n (k - 1) ≤ row n j) ∧
      (∀ j : ℕ, j < k - 1 → row n (k - 1) < row n j) := by
  sorry

end OMA.S_oeis_a358616

