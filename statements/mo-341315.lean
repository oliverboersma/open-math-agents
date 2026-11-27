import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Data.Nat.Prime.Infinite

/-!
# MathOverflow question 341315, Question 1

Source: https://mathoverflow.net/questions/341315

The title restates Question 1. The author clarifies in a comment that the exponent k is
at least two.
-/

namespace OMA.S_mo_341315

theorem main :
    {p : ℕ | p.Prime ∧ ∃ k n : ℕ, 2 ≤ k ∧ 1 ≤ n ∧ n < p ∧
      p ^ k > n * UniqueFactorizationMonoid.radical (p ^ (k + 1) - n)}.Infinite := by
  sorry

end OMA.S_mo_341315
