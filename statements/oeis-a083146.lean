import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A083146

Source: https://oeis.org/A083146 (Franklin T. Adams-Watters, July 2006,
OEIS Foundation, CC BY-SA 4.0). Related sequences: A083145 and A119368.

State the conjecture that A083145 and A083146 differ infinitely often.
The two sequences differ exactly at the positive palindromes whose least
proper palindromic multiple is the concatenation of two copies of themselves.
Two copies give the smallest proper multiple among concatenations, so it
suffices to compare that multiple with every proper palindromic multiple.
-/

namespace OMA.S_oeis_a083146

def Pal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

def twice (n : ℕ) : ℕ := n * (10 ^ (Nat.digits 10 n).length + 1)

theorem main : Set.Infinite
    {p : ℕ | 0 < p ∧ Pal p ∧ IsLeast {m : ℕ | p < m ∧ p ∣ m ∧ Pal m} (twice p)} := by
  sorry

end OMA.S_oeis_a083146
