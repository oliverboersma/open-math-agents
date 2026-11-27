import Mathlib

/-!
# OEIS A268135

The conjecture asks for infinitely many positive integers `n` such that the
decimal digit sum of `n ^ 2` properly divides the digit sum of `n`. Chai Wah
Wu observed that appending zeros to 149 settles this first question and
asked whether infinitely many such integers are not multiples of ten.

Source: https://oeis.org/A268135
-/

namespace OMA.S_oeis_a268135

def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

def properTerms : Set ℕ :=
  {n | 0 < n ∧ digitSum (n ^ 2) ∣ digitSum n ∧ digitSum (n ^ 2) < digitSum n}

theorem main : properTerms.Infinite ∧ {n ∈ properTerms | ¬ 10 ∣ n}.Infinite := by
  sorry

end OMA.S_oeis_a268135
