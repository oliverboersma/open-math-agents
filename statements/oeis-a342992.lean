import Mathlib

/-!
# A342992: Smallest k such that k*n contains only prime digits, or 0 if no such k exists

Source: https://oeis.org/A342992
Credit: @niclorusso

Conjecture (in the comments of A342992): a(n) > 0 for all n that are not divisible by 5.

Conventions:
* The sequence has offset 1. The prime digits are 2, 3, 5, 7; k*n "contains only prime digits" when
  every decimal digit of k*n (`Nat.digits 10`) is one of them.
* a(n) > 0 means that some k >= 1 has this property (a(n) is then the least such k).
-/

namespace OMA.S_oeis_a342992

/-- Every decimal digit of `x` is a prime digit `2, 3, 5` or `7`. -/
def HasOnlyPrimeDigits (x : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 x, d ∈ ({2, 3, 5, 7} : Finset ℕ)

/-- The conjecture on A342992: every `n >= 1` not divisible by 5 has a positive multiple `k * n`
whose decimal digits are all prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ 5 ∣ n → ∃ k : ℕ, 1 ≤ k ∧ HasOnlyPrimeDigits (k * n) := by
  sorry

end OMA.S_oeis_a342992
