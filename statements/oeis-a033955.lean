import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Nth

/-!
# Sum of remainders of the primes in OEIS A033955

Source: https://oeis.org/A033955 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

Alonso del Arte's conjecture uses one-based prime indices. In Mathlib `Nat.nth`
is zero-based, so the condition on the prime index becomes `5 < n`.
-/

namespace OMA.S_oeis_a033955

open scoped BigOperators

theorem main : ∀ n : ℕ, 5 < n →
    Nat.nth Nat.Prime n < ∑ k ∈ Finset.range n, Nat.nth Nat.Prime n % Nat.nth Nat.Prime k := by
  sorry

end OMA.S_oeis_a033955
