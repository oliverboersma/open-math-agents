import Mathlib

/-!
# A330718: a(n) = numerator(Sum_{k=1..n} (2^k-2)/k).

Source: https://oeis.org/A330718
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: for n > 3, if n^2 | a(n), then n is prime.

Conventions: offset 1; the sum is computed in `ℚ` and `a(n)` is its reduced numerator `Rat.num` (an integer).
-/

namespace OMA.S_oeis_a330718

/-- `a(n)` is the numerator of `Sum_{k=1..n} (2^k - 2)/k`. -/
def a (n : ℕ) : ℤ := (∑ k ∈ Finset.Icc 1 n, ((2 : ℚ) ^ k - 2) / k).num

/-- For `n > 3`, if `n^2` divides `a(n)` then `n` is prime. -/
theorem main : ∀ n : ℕ, 3 < n → (n : ℤ) ^ 2 ∣ a n → n.Prime := by
  sorry

end OMA.S_oeis_a330718
