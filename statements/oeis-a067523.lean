import Mathlib

/-!
# A067523: The smallest prime with a possible given digit sum.

Source: https://oeis.org/A067523
Credit: @ShoQo

Except for 3 no other prime has a digit sum which is a multiple of 3. Hence the possible digit
sums are 2,3,4,5,7,8,10,11,13,14,16,..., etc. Conjecture: For every possible digit sum there
exists a prime.

Formalization notes:
* Digit sums are in base 10.
* The "possible" digit sums are, as listed in the source, `s = 3` and every `s ≥ 2` not
  divisible by 3 (1 is not listed: a number with digit sum 1 is a power of 10).
-/

namespace OMA.S_oeis_a067523

theorem main :
    ∀ s : ℕ, 2 ≤ s → (s = 3 ∨ ¬ 3 ∣ s) →
      ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).sum = s := by
  sorry

end OMA.S_oeis_a067523
