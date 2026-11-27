import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A228410

Source: https://oeis.org/A228410 (M. F. Hasler, OEIS Foundation,
CC BY-SA 4.0). The sequence starts at 1. Each successor is the least
unused positive integer whose decimal digits can be combined with the
preceding term's digits and rearranged into a palindromic integer.
Index zero in Lean represents the first term in the OEIS entry.

The conjecture says that the sequence is a permutation of the positive
integers. The nonnegative variant A228407 uses a different initial term
and includes zero in its search domain.
-/

namespace OMA.S_oeis_a228410

def digitWord (n : ℕ) : List ℕ := Nat.digits 10 n

def Compatible (a b : ℕ) : Prop :=
  ∃ w : List ℕ, w.Perm (digitWord a ++ digitWord b) ∧ w.reverse = w ∧
    ∃ d : ℕ, w.head? = some d ∧ 0 < d

def Greedy (a : ℕ → ℕ) : Prop := a 0 = 1 ∧
  ∀ n, IsLeast {m : ℕ | 0 < m ∧ (∀ i ≤ n, a i ≠ m) ∧ Compatible (a n) m} (a (n+1))

theorem main : ∃ a : ℕ → ℕ, Greedy a ∧ Function.Injective a ∧ Set.range a = {m : ℕ | 0 < m} := by
  sorry

end OMA.S_oeis_a228410
