import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

/-!
# A periodic statistic of consecutive ratios

Source: https://oeis.org/A328002 (Peter Luschny, OEIS Foundation, CC BY-SA 4.0).
The factors of the original product are `2/j` for even `j` and `j/2` for odd `j`.
The source indexes `a` and its adjacent ratios starting at zero.
-/

namespace OMA.S_oeis_a328002

def factor (j : ℕ) : ℚ := if j % 2 = 0 then 2 / j else j / 2

def a (n : ℕ) : ℚ := 2^n * ∑ k ∈ Finset.range (n+1), ∏ i ∈ Finset.range k, factor (i+1)

def q (n : ℕ) : ℚ := a (n+1) / a n

def d (n : ℕ) : ℤ := (q n).num - 2 * ((q n).den : ℤ)

theorem main : ∀ n : ℕ, d n = ([1,2,3,3,3,2,1,1,3,6,3,1] : List ℤ)[n % 12]! := by
  sorry

end OMA.S_oeis_a328002
