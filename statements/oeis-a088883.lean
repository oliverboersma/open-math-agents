import Mathlib

/-!
# A088883: Primes which when concatenated with their reverse and incremented by 2 yield a new prime.

Source: https://oeis.org/A088883
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: All these primes are of the form 6*k + 1 (Davide Rotondo, Apr 29 2025).

Conventions: base 10. The reverse of `p` is `Nat.ofDigits 10 (Nat.digits 10 p).reverse`, and the concatenation of `p` with a number having as many digits as `p` is `p * 10^(number of digits of p) + reverse`. Example: `109 -> 109901 + 2 = 109903`.
-/

namespace OMA.S_oeis_a088883

/-- The decimal reversal of `n`. -/
def rev (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- If `p` is prime and the concatenation of `p` with its reverse, plus 2, is prime, then
`p = 6k + 1`. -/
theorem main : ∀ p : ℕ, p.Prime →
    (p * 10 ^ (Nat.digits 10 p).length + rev p + 2).Prime → p % 6 = 1 := by
  sorry

end OMA.S_oeis_a088883
