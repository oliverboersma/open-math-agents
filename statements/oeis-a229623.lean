import Mathlib

/-!
Derek Orr's April 2015 conjecture on decimal palindromes whose difference
with their digit sum is also a palindrome. The sequence includes zero and
is indexed starting at one, so its n-th term has index n - 1 in Nat.nth.
Source: https://oeis.org/A229623
-/

namespace OMA.S_oeis_a229623

def qualifies (m : ℕ) : Prop :=
  (Nat.digits 10 m).Palindrome ∧ (Nat.digits 10 (m - (Nat.digits 10 m).sum)).Palindrome

theorem main : ∀ n : ℕ, 21 ≤ n → Nat.nth qualifies (n - 1) = 10 ^ (n - 18) + 1 := by
  sorry

end OMA.S_oeis_a229623
