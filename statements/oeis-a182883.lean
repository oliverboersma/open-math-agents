/-
OEIS A182883, Peter Bala's binomial sum and signed recurrence.
Reference: https://oeis.org/A182883
Credit: @Heart-galaxy
Text credit: OEIS Foundation, CC BY-SA 4.0.

Only the weight-2 horizontal step is allowed. A path begins and ends at height
zero, so the number of up steps equals the number of down steps. Each pair
of disjoint sets of step positions identifies one ordered path.
-/

import Mathlib

namespace OMA.S_oeis_a182883

open Finset

/-- A balanced path with j upward and j downward steps, and l horizontal steps,
is specified by its disjoint sets of upward and downward positions. -/
def paths (j l : ℕ) : Finset (Σ _ : Finset ℕ, Finset ℕ) :=
  let positions := range (2 * j + l)
  (positions.powersetCard j).sigma (fun up => (positions \ up).powersetCard j)

/-- Upward and horizontal steps have weight 2, and downward steps have weight 1. -/
def multiplicities (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1))).filter
    (fun p => 3 * p.1 + 2 * p.2 = n)

def a (n : ℕ) : ℕ := ∑ p ∈ multiplicities n, (paths p.1 p.2).card

theorem main :
    (∀ n : ℕ, a n = ∑ k ∈ range (n / 2 + 1),
      (n - k).choose k * k.choose (n - 2 * k)) ∧
    (∀ n : ℕ, 4 ≤ n → (n : ℤ) * (a n : ℤ) =
      (2 * (n : ℤ) - 2) * (a (n - 2) : ℤ) + (4 * (n : ℤ) - 6) * (a (n - 3) : ℤ) -
      ((n : ℤ) - 2) * (a (n - 4) : ℤ)) := by
  sorry

end OMA.S_oeis_a182883
