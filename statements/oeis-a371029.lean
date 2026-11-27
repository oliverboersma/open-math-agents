import Mathlib

/-!
OEIS A371029 conjectures that infinitely many positive indices give a pair
of primes on either side of 27m³ + 3m.

https://oeis.org/A371029
-/

namespace OMA.S_oeis_a371029

theorem main :
    {m : ℕ | let k := 27 * m ^ 3 + 3 * m
             0 < m ∧ Nat.Prime (k - 1) ∧ Nat.Prime (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a371029
