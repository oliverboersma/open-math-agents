import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range

/-! Layman's floor formula for partitions into parts 3 and 5, OEIS A008676. -/

namespace OMA.S_oeis_a008676

open Finset

/-- Pairs of multiplicities for parts 3 and 5 in a partition of `n`. -/
def representations (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1))).filter fun p => 3 * p.1 + 5 * p.2 = n

def a (n : ℕ) : ℕ := (representations n).card

theorem main : ∀ n : ℕ,
    (a n : ℤ) = (2 * ((n : ℤ) + 3)) / 3 - (3 * ((n : ℤ) + 3)) / 5 := by
  sorry

end OMA.S_oeis_a008676
