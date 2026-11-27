import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Four primes between consecutive positive cubes

Cino Hilliard's conjecture of 5 January 2003 in OEIS A060199.
The index starts at one to exclude the lower cube zero. Both endpoints
are excluded by the open interval.

Source: https://oeis.org/A060199 (OEIS Foundation, CC BY-SA 4.0)
Formalization: @DomTheDeveloper
-/

namespace OMA.S_oeis_a060199

theorem main : ∀ n : ℕ, 1 ≤ n →
    4 ≤ ((Finset.Ioo (n ^ 3) ((n + 1) ^ 3)).filter Nat.Prime).card := by
  sorry

end OMA.S_oeis_a060199
