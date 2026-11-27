import Mathlib.Data.Finset.Prod
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Common sums from complementary sets in OEIS A039799

Source: https://oeis.org/A039799 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

For each subset of {1, ..., n}, count the distinct integers that are a sum
of two different elements of the subset and also a sum of two different
elements of its complement. Rob Pratt conjectures the largest possible count.
-/

namespace OMA.S_oeis_a039799

def pairSums (s : Finset ℕ) : Finset ℕ :=
  ((s.product s).filter fun p => p.1 < p.2).image fun p => p.1 + p.2

def commonSumCounts (n : ℕ) : Set ℕ :=
  let ground := Finset.Icc 1 n
  {m | ∃ s : Finset ℕ, s ⊆ ground ∧ (pairSums s ∩ pairSums (ground \ s)).card = m}

theorem main : ∀ n : ℕ, 14 ≤ n → IsGreatest (commonSumCounts n) (2 * n - 11) := by
  sorry

end OMA.S_oeis_a039799
