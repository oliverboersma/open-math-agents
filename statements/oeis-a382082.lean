import Mathlib

/-!
# A382082: F(k) such that F(k) + (F(k) reversed) is a palindrome, where F(k) is a Fibonacci number.

Source: https://oeis.org/A382082
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: The sequence appears to be finite.

Conventions: base 10. The reversal of `x` is `Nat.ofDigits 10 (Nat.digits 10 x).reverse`; `m` is a palindrome when its digit list equals its reverse. The sequence lists the values `F(k)`, so the claim is that the set of such Fibonacci values is finite.
-/

namespace OMA.S_oeis_a382082

/-- The decimal reversal of `n`. -/
def rev (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- `m` is a decimal palindrome. -/
def IsPalindrome (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- Only finitely many Fibonacci numbers `x` have `x + rev x` a palindrome. -/
theorem main : {x : ℕ | (∃ k : ℕ, x = Nat.fib k) ∧ IsPalindrome (x + rev x)}.Finite := by
  sorry

end OMA.S_oeis_a382082
