import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite

/-! Mathar's OEIS A005994 identity with the zero-sum array count A203286. -/

open Finset

namespace OMA.S_oeis_a005994

/-- The multiplicities of the magnitudes one, two, and three. -/
structure Counts where
  one : ℕ
  two : ℕ
  three : ℕ

def total (t : Counts) : ℕ := t.one + t.two + t.three

def weight (t : Counts) : ℕ := t.one + 2 * t.two + 3 * t.three

/-- Positive and negative multiplicities of a nondecreasing array of length `2*n`.
The other `2*(n-total p.1)` entries are zeros. -/
def Configuration (n : ℕ) :=
  {p : Counts × Counts // total p.1 = total p.2 ∧ weight p.1 = weight p.2 ∧ total p.1 ≤ n}

noncomputable def arrayCount (n : ℕ) : ℕ := Nat.card (Configuration n)

def triangle (n d : ℕ) : ℕ := (n + 2 - 2 * d).choose 2

def alkaneCount (n : ℕ) : ℕ :=
  ∑ d ∈ range (n + 1), (2 * d + 1) * triangle n d

theorem main : ∀ n : ℕ, alkaneCount n + alkaneCount (n + 1) = arrayCount (n + 1) := by
  sorry

end OMA.S_oeis_a005994
