import Mathlib

/-!
# OEIS A088862

For each n, take the least positive integer with exactly n prime
factors counted with multiplicity whose divisors greater than one
form a binary prefix code. For positive a and b, a is a prefix of b
in standard binary exactly when removing some number of trailing bits
from b yields a, that is, b / 2^k = a for some k.

The conjecture is that this least integer exists for every n.

Source: https://oeis.org/A088862
-/

namespace OMA.S_oeis_a088862

def eligible (n m : ℕ) : Prop :=
  0 < m ∧ m.primeFactorsList.length=n ∧
    ∀ a : ℕ, a ∣ m → 1 < a → ∀ b : ℕ, b ∣ m → 1 < b → ∀ k : ℕ, b/2^k=a → a=b

theorem main : ∀ n : ℕ, ∃ m, IsLeast {x : ℕ | eligible n x} m := by
  sorry

end OMA.S_oeis_a088862
