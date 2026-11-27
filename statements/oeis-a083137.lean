import Mathlib

/-!
# OEIS A083137

The first term is 1. Each next term is the least decimal palindrome
larger than every previous term and relatively prime to every previous
term. The conjecture is that this greedy sequence continues indefinitely.

Source: https://oeis.org/A083137
-/

namespace OMA.S_oeis_a083137

def palindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

def eligible (a : ℕ → ℕ) (n p : ℕ) : Prop :=
  palindrome p ∧ ∀ i ≤ n, a i < p ∧ p.Coprime (a i)

theorem main : ∃ a : ℕ → ℕ, a 0 = 1 ∧
    ∀ n, IsLeast {p | eligible a n p} (a (n+1)) := by
  sorry

end OMA.S_oeis_a083137
