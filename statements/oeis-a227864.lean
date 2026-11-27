import Mathlib

/-!
# A227864: Smallest base in which n's digital reversal is prime, or 0 if no such base exists

Source: https://oeis.org/A227864
Credit: @niclorusso

Conjecture 1 (in the comments of A227864): 0, 1 and 4 are the only values where there is no base
in which a digital reversal makes a prime.

Conventions:
* Bases are integers b >= 2. The digital reversal of n in base b reverses the base-b digits of n:
  `Nat.ofDigits b (Nat.digits b n).reverse` (`Nat.digits b n` lists the base-b digits of n, least
  significant first, with no leading zeros; leading zeros created by the reversal are dropped).
* n ranges over the natural numbers (offset 0); a(n) = 0 exactly when no base works.
* "the only values" is stated as a set equality.
-/

namespace OMA.S_oeis_a227864

/-- The digital reversal of `n` in base `b`. -/
def reversal (b n : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b n).reverse

/-- Conjecture 1 on A227864: the `n` whose digital reversal is prime in no base `b >= 2` are
exactly `0`, `1` and `4`. -/
theorem main : {n : ℕ | ¬ ∃ b : ℕ, 2 ≤ b ∧ (reversal b n).Prime} = {0, 1, 4} := by
  sorry

end OMA.S_oeis_a227864
