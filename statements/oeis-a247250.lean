import Mathlib

/-!
# Primitive prime divisors in the Pell sequence

The conjecture recorded by Eric Chen in OEIS A247250 concerns the first
appearance of a prime divisor among the positive-index Pell numbers.
The initial value at index zero is excluded when looking at earlier terms.
Source: https://oeis.org/A247250
Credit: @ZedingZhang

Faye and Luca identify this assertion as known in Section 2 of
Pell numbers whose Euler function is a Pell number.
-/

namespace OMA.S_oeis_a247250

/-- The Pell numbers A000129, indexed from zero. -/
def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

/-- Each Pell number from index two onward has a prime factor first
    appearing at that index. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ p ∣ pell n ∧
    ∀ m : ℕ, 0 < m → m < n → ¬ p ∣ pell m := by
  sorry

end OMA.S_oeis_a247250

