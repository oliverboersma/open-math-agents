import Mathlib

/-!
# Are there infinitely many cubes which are Goldbach numbers?

Source: https://mathoverflow.net/questions/485166
Credit: @nokiexow

The prime summands need not be distinct. Their sum is positive, so every
integer cube equal to such a sum has a natural cube root.
-/

namespace OMA.S_mo_485166

theorem main : Set.Infinite {n : ℕ | Even n ∧ (∃ k : ℕ, n = k ^ 3) ∧
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q} := by
  sorry

end OMA.S_mo_485166

