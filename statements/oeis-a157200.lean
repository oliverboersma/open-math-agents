import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Infinitude of the primes in OEIS A157200

Source: https://oeis.org/A157200 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The conjecture concerns distinct prime values of the expression that defines
the sequence of positive indices.
-/

namespace OMA.S_oeis_a157200

theorem main : Set.Infinite {p : ℕ | p.Prime ∧ ∃ k : ℕ, 0 < k ∧ p = k * (2 * k) ^ k - 1} := by
  sorry

end OMA.S_oeis_a157200
