import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A228407

Source: https://oeis.org/A228407 (Eric Angelini, OEIS Foundation,
CC BY-SA 4.0). The sequence starts at zero. Each successor is the least
unused nonnegative integer whose digits, combined with the preceding
term's digits, can be rearranged into a palindromic integer. Zero supplies
one zero digit. A rearranged word must have a nonzero leading digit, as
in the example distinguishing 101 from 010.

The conjecture, proved by N. J. A. Sloane in November 2013, asserts that
the greedy sequence is a permutation of the nonnegative integers.
-/

namespace OMA.S_oeis_a228407

def digitWord (n : ℕ) : List ℕ := if n = 0 then [0] else Nat.digits 10 n

def Compatible (a b : ℕ) : Prop :=
  ∃ w : List ℕ, w.Perm (digitWord a ++ digitWord b) ∧ w.reverse = w ∧
    ∃ d : ℕ, w.head? = some d ∧ 0 < d

def Greedy (a : ℕ → ℕ) : Prop := a 0 = 0 ∧
  ∀ n, IsLeast {m : ℕ | (∀ i ≤ n, a i ≠ m) ∧ Compatible (a n) m} (a (n+1))

theorem main : ∃ a : ℕ → ℕ, Greedy a ∧ Function.Bijective a := by
  sorry

end OMA.S_oeis_a228407
