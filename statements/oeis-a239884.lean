import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Group.Even

/-!
# OEIS A239884, a square after counting primes twice
Source: https://oeis.org/A239884 (see also A238902, conjecture (i)).
Credit: @garrytaulu

The sequence uses zero as the sentinel for an empty search. Its value is
positive exactly when at least one candidate in the indicated interval exists.
-/

namespace OMA.S_oeis_a239884

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
    IsSquare (Nat.primeCounting (Nat.primeCounting (k * n))) := by
  sorry

end OMA.S_oeis_a239884
