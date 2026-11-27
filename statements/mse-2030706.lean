import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# Sets of natural numbers closed under addition of successors

Source: Lehs, Math.StackExchange 2030706, November 25, 2016, CC BY-SA 3.0.
https://math.stackexchange.com/questions/2030706/sets-of-natural-numbers-closed-under-addition-of-successors

An unbounded set of positive natural numbers has a unique increasing
enumeration. Its members between two endpoints in the set are precisely a
consecutive block of that enumeration. As clarified by the author, no
integer > 1 divides every member of the set.
-/

namespace OMA.S_mse_2030706

open Finset

noncomputable def block (A : Set ℕ) (l u : ℕ) : Finset ℕ := by
  classical
  exact (Icc l u).filter (· ∈ A)

theorem main : ∀ A : Set ℕ, (∀ x ∈ A, 0 < x) →
    (∀ N : ℕ, ∃ x ∈ A, N < x) →
    (∀ d : ℕ, (∀ x ∈ A, d ∣ x) → d = 1) →
    (∀ l ∈ A, ∀ u ∈ A, l ≤ u → (∑ x ∈ block A l u, x) ∈ A) →
    ∃ N : ℕ, ∀ n > N, n ∈ A := by
  sorry

end OMA.S_mse_2030706
