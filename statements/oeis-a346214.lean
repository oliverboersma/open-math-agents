import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# The co-index of a uniformly chosen binary nilpotent matrix

The first assertion is the conjectured limiting distribution. The second
is the finite identity on the range printed by Geoffrey Critzer in 2025.
The square of the distance from j to 1 is the ordinary integer (j-1)^2,
including j=0. Clearing positive denominators in the finite formula
avoids truncating a possibly negative exponent.

Source: https://oeis.org/A346214
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a346214

open scoped BigOperators

abbrev BinaryMatrix (n : ℕ) := Matrix (Fin n) (Fin n) (ZMod 2)

/-- A002884 is the number of invertible binary n by n matrices. -/
def glOrder (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)

/-- Count matrices of exact positive nilpotency index k. -/
noncomputable def table (n k : ℕ) : ℕ :=
  Set.ncard {M : BinaryMatrix n | 0 < k ∧ M ^ k = 0 ∧
    ∀ i : ℕ, 0 < i → i < k → M ^ i ≠ 0}

noncomputable def nilpotents (n : ℕ) : ℕ :=
  Set.ncard {M : BinaryMatrix n | ∃ k : ℕ, 0 < k ∧ M ^ k = 0}

/-- The co-index is n minus the nilpotency index. -/
noncomputable def probability (n j : ℕ) : ℝ :=
  if j < n then (table n (n-j) : ℝ) / (nilpotents n : ℝ) else 0

/-- The limiting probability and the printed finite-count assertion. -/
theorem main :
    (∀ j : ℕ, Filter.Tendsto (fun n : ℕ => probability n j) Filter.atTop
      (nhds ((∏' i : ℕ, (1 - (1 : ℝ) / 2 ^ (i+1))) *
        (2 : ℝ) ^ ((Nat.dist j 1) ^ 2) / (glOrder j : ℝ)))) ∧
    (∀ n j : ℕ, 0 < n → j < n → j < 2 * n →
      table n (n-j) * glOrder j * 2 ^ n =
        glOrder n * 2 ^ ((Nat.dist j 1) ^ 2)) := by
  sorry

end OMA.S_oeis_a346214
