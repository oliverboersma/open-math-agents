import Mathlib

/-!
# Queens attacking at most one other queen

OEIS A260113 gives the maximum size of such a placement on a square chessboard.
Giovanni Resta proposed the formula in 2015. See Theorem 2.2 of Ago, Bašić
and Ciganović (https://arxiv.org/abs/2608.27432).

Source: https://oeis.org/A260113
Credit: @physbuzz
-/

namespace OMA.S_oeis_a260113

/-- Distinct squares in a common row, column, or diagonal of the board. -/
def attacks {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2 ∨
    Nat.dist p.1.val q.1.val = Nat.dist p.2.val q.2.val)

/-- Each queen has at most one other occupied square along its attack lines. -/
def valid {n : ℕ} (queens : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ queens, ∀ q ∈ queens, ∀ r ∈ queens, attacks p q → attacks p r → q = r

/-- On every board of side at least six, the maximum number of queens is ⌊4n/3⌋. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    IsGreatest {k : ℕ | ∃ queens : Finset (Fin n × Fin n), valid queens ∧ queens.card = k}
      (4 * n / 3) := by
  sorry

end OMA.S_oeis_a260113
