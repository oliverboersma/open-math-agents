import Mathlib

/-!
# The Rule 81 triangle and the divisor sum

Wesley Ivan Hurt's conjecture in OEIS A266982, 22 March 2016.
Source: https://oeis.org/A266982
Credit: @LoopsGod

The initial configuration on the integer line has a single ON cell at zero.
At time `t` we read positions `-t` through `t` from left to right. The rows
have lengths 1, 3, 5, ... and offset zero, so row `t` starts at index `t ^ 2`.
-/

namespace OMA.S_oeis_a266982

/-- Wolfram rule 81, using the binary neighbourhood index `4*l + 2*c + r`. -/
def rule81 (l c r : Bool) : Bool :=
  (81 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- State of site `i` after `t` synchronous updates on the entire integer line. -/
def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule81 (cell t (i - 1)) (cell t i) (cell t (i + 1))

/-- Entry of the triangle flattened in row order, with the initial cell at index zero. -/
def a (n : ℕ) : ℕ :=
  let t := n.sqrt
  (cell t (((n - t ^ 2 : ℕ) : ℤ) - (t : ℤ))).toNat

/-- For indices 1 and 2 the sum is empty, as in the stated formula. -/
theorem main : a 0 = 1 ∧ ∀ n : ℕ, 0 < n →
    a n = (∑ i ∈ Finset.Ioc 0 (n - 2), (n - 2) / i) % 2 := by
  sorry

end OMA.S_oeis_a266982
