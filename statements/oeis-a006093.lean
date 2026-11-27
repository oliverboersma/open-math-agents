import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs

/-!
# Distinct reciprocal sums over intervals of shifted primes

Zhi-Wei Sun conjectures that a sum of reciprocals of positive integer
powers of shifted primes determines its interval of indices for each shift
`d ≥ -1` and exponent `m > 0`, apart from two pairs for `d = m = 1`.
A006093 itself is the case `d = -1` and `m = 1`.

Source: https://oeis.org/A006093
Credit: @justusklocke-cloud
-/

open scoped BigOperators

namespace OMA.S_oeis_a006093

/-- The rational sum over a one-based prime index interval. -/
noncomputable def intervalSum (d : ℤ) (m i j : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc i j, 1 / ((Nat.nth Nat.Prime (k - 1) : ℚ) + (d : ℚ)) ^ m

/-- The two exceptional unordered pairs of index intervals in the source. -/
def ExceptionalIntervals (I J : ℕ × ℕ) : Prop :=
  ({I, J} : Finset (ℕ × ℕ)) = {(4, 4), (8, 10)} ∨
    ({I, J} : Finset (ℕ × ℕ)) = {(4, 7), (5, 10)}

theorem main : ∀ (d : ℤ) (m i j s t : ℕ), -1 ≤ d → 0 < m →
    0 < i → i ≤ j → 0 < s → s ≤ t →
    intervalSum d m i j = intervalSum d m s t →
    (i, j) = (s, t) ∨ (d = 1 ∧ m = 1 ∧ ExceptionalIntervals (i, j) (s, t)) := by
  sorry

end OMA.S_oeis_a006093
