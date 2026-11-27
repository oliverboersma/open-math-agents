import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Cast.Order

/-!
# Summing a quadratic expression by its gcd with n

Source: https://oeis.org/A373561
Credit: @anmolspace

Mats Granvik conjectured that grouping the values of x²+y²−z² by their gcd
with n, then summing over gcds from 1 through n, recovers the polynomial
defining A373561. The variables x, y and z also range from 1 through n.
-/

namespace OMA.S_oeis_a373561

open Finset

/-- The weight can be negative, so the subtraction takes place in the integers. -/
def weight (x y z : ℕ) : ℤ := (x : ℤ)^2 + (y : ℤ)^2 - (z : ℤ)^2

/-- Indexing by `i+1` makes each of the three coordinates run from 1 through n. -/
def groupedSum (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 n, ∑ z ∈ range n, ∑ y ∈ range n, ∑ x ∈ range n,
    if Int.gcd (weight (x+1) (y+1) (z+1)) n = k then weight (x+1) (y+1) (z+1) else 0

/-- Granvik's conjectured polynomial identity, including the empty sum for n = 0. -/
theorem main : ∀ n : ℕ,
    (1/3 : ℚ) * n^5 + (1/2 : ℚ) * n^4 + (1/6 : ℚ) * n^3 = (groupedSum n : ℚ) := by
  sorry

end OMA.S_oeis_a373561
