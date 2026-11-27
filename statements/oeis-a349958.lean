import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Bounds.Basic

/-!
# First row of Pascal's triangle containing a multiple of n

Source: https://oeis.org/A349958 (Nathan M Epstein; conjecture by Robert Israel,
OEIS Foundation, CC BY-SA 4.0).

Rows and columns start at zero. For positive n, the sequence takes the least
row containing a multiple of n. The conjecture says that this row is n exactly
for prime powers with positive exponent (A246655). In particular a(1) = 0.
-/

namespace OMA.S_oeis_a349958

def containsMultiple (n row : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ row ∧ n ∣ row.choose k

theorem main : ∀ n : ℕ, 0 < n →
    (IsLeast {row : ℕ | containsMultiple n row} n ↔ IsPrimePow n) := by
  sorry

end OMA.S_oeis_a349958
