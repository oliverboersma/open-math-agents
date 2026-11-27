import Mathlib

/-!
# A090075: (Presumed) number of palindromes in the Reverse and Add! trajectory of 10^n.

Source: https://oeis.org/A090075
Credit: @jared-jasinski

The OEIS entry A090075 records the presumed number of base-10 palindromes in the Reverse and Add!
trajectory of `10^n` and states the conjecture (cf. A077594) that there is no positive integer
whose Reverse and Add! trajectory contains more than twelve palindromes.

By OEIS convention (see A077594 and A090075), the trajectory of `k > 0` starts at step `0` with
`k` itself (`reverseAndAdd^[0] k = k`), and for `k > 0` the trajectory is strictly increasing.
Using `Set.encard ≤ 12` faithfully captures having at most twelve palindromes (excluding both
trajectories with more than twelve palindromes and trajectories with infinitely many palindromes).
-/

namespace OMA.S_oeis_a090075

/-- The natural number whose base-10 digits are the reversal of `n`'s base-10 digits. -/
def reverseDigits10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- One step of the base-10 Reverse and Add! operation: `n ↦ n + reverseDigits10 n`. -/
def reverseAndAdd (n : ℕ) : ℕ :=
  n + reverseDigits10 n

/-- A natural number is a base-10 palindrome if its base-10 digit list is a palindrome. -/
def IsDecimalPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).Palindrome

/-- Conjecture from OEIS A090075 (cf. A077594): there is no positive integer whose base-10
Reverse and Add! trajectory contains more than twelve palindromes. -/
theorem main :
    ∀ k : ℕ, 0 < k → {m : ℕ | IsDecimalPalindrome (reverseAndAdd^[m] k)}.encard ≤ 12 := by
  sorry

end OMA.S_oeis_a090075
