import Mathlib

/-!
# The two formulas conjectured for OEIS A122554

Source: https://oeis.org/A122554
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A122/A122554.seq
Credit: @Heart-galaxy

The source has offset 1. Starting with S(1) = {1}, S(n) is the smallest set
containing x, 2*x, and x+2 for each x in S(n-1); a(n) is its cardinality.
The union below is exactly that smallest set. S(0) is an unused convention.

R. J. Mathar conjectured the order-four recurrence for n > 6 and the Lucas
formula for n > 2 on November 18, 2009. The source reports both conjectures
proved by Sela Fried on February 18, 2026; see
https://oeis.org/A122554/a122554.pdf . This file states the known result.
LucasNat uses the canonical initial values L(0)=2 and L(1)=1.

The recurrence is written as an equality of sums to avoid truncated subtraction.
-/

namespace OMA.S_oeis_a122554

/-- Layman's sets; index zero is an unused convention. -/
def S : ℕ → Finset ℕ
  | 0 => ∅
  | 1 => {1}
  | n + 2 => S (n + 1) ∪ (S (n + 1)).image (fun x => x + 2) ∪
      (S (n + 1)).image (fun x => 2 * x)

/-- The cardinality sequence A122554 at its positive indices. -/
def a (n : ℕ) : ℕ := (S n).card

/-- The Lucas numbers with their canonical zero-indexed initial values. -/
def LucasNat : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => LucasNat n + LucasNat (n + 1)

/-- Mathar's two conjectures, reported proved in the source in 2026. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      a n + 2 * a (n - 2) + a (n - 3) = 3 * a (n - 1) + a (n - 4)) ∧
    (∀ n : ℕ, 2 < n → a n = LucasNat n + n - 1) := by
  sorry

end OMA.S_oeis_a122554
