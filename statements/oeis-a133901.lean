import Mathlib

/-!
# OEIS A133901

Klaus Brockhaus and Zak Seidov conjectured that infinitely many decimal
palindromes have a nonpalindromic square whose decimal reversal is a square.
These are exactly the exceptional terms of A128921 described in A133901.

Source: https://oeis.org/A133901
-/

namespace OMA.S_oeis_a133901

def reverseDecimal (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

def terms : Set ℕ :=
  {n | 0 < n ∧ reverseDecimal n = n ∧ reverseDecimal (n ^ 2) ≠ n ^ 2 ∧
    ∃ m : ℕ, reverseDecimal (n ^ 2) = m ^ 2}

theorem main : terms.Infinite := by
  sorry

end OMA.S_oeis_a133901
