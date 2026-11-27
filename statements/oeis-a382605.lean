import Mathlib

/-!
# OEIS A382605

Daniel Mondot asks when the cyclic chain of rods 1, 2, ..., n can be folded
into two equal sides, with both turns at joints. Between two joints i < j,
one side consists of the consecutive rods i+1 through j. The other side
consists of the remaining rods in their cyclic order.

The second equivalence uses the original difference-of-squares definition
of the index sequence A154708. Both sequences start at positive indices.

Sources: https://oeis.org/A382605 and https://oeis.org/A154708
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a382605

def total : ℕ → ℕ
  | 0 => 0
  | n+1 => total n + (n+1)

def folds (n : ℕ) : Prop :=
  ∃ i j : ℕ, i < j ∧ j ≤ n ∧ 2 * total j = total n + 2 * total i

def inA154708 (n : ℕ) : Prop :=
  ∃ b c : ℕ, b ≤ n ∧ n < c ∧ n*(n+1) + b^2 = c^2

theorem main : ∀ n : ℕ, 0 < n →
    (folds n ↔ Even (total n)) ∧ (folds n ↔ inA154708 n) := by
  sorry

end OMA.S_oeis_a382605
