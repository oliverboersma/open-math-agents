import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Bounds.Defs

/-!
# Minimum common difference of prime progressions in OEIS A033188

Source: https://oeis.org/A033188 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

David W. Wilson conjectures that for n at least 8, the least positive common
difference of an n-term prime arithmetic progression is the product of the
primes at most n.
-/

namespace OMA.S_oeis_a033188

def primeProgressionDifferences (n : ℕ) : Set ℕ :=
  {d | 0 < d ∧ ∃ a : ℕ, ∀ i : Fin n, Nat.Prime (a + (i : ℕ) * d)}

theorem main : ∀ n : ℕ, 8 ≤ n → IsLeast (primeProgressionDifferences n) (primorial n) := by
  sorry

end OMA.S_oeis_a033188
