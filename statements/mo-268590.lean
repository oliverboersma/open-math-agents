import Mathlib

/-!
# MathOverflow 268590: can a number be palindromic in more than 3 consecutive bases?

Source: https://mathoverflow.net/questions/268590
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: can a natural number be nontrivially palindromic in more than `3` consecutive number
bases? "Nontrivially" excludes one-digit palindromes. The asker conjectures that no such number
exists ("there are no 4-palindromes"); since a number palindromic in `k ≥ 4` consecutive bases is
palindromic in `4` consecutive bases, this is the whole question.

We state the asker's conjecture (a disproof of `main` exhibits a 4-palindrome).

Conventions: bases are integers `b ≥ 2`; the base-`b` digits of `N` are `Nat.digits b N`
(least significant first, which does not affect being a palindrome); "nontrivially palindromic"
means the digit list has length at least `2` and equals its reverse.
-/

namespace OMA.S_mo_268590

/-- `N` is a palindrome in base `b` with at least two digits. -/
def NontrivPalindrome (b N : ℕ) : Prop :=
  2 ≤ (Nat.digits b N).length ∧ (Nat.digits b N).reverse = Nat.digits b N

/-- No natural number is nontrivially palindromic in four consecutive bases `b, b+1, b+2, b+3`. -/
theorem main : ¬ ∃ N b : ℕ, 2 ≤ b ∧ ∀ i < 4, NontrivPalindrome (b + i) N := by
  sorry

end OMA.S_mo_268590
