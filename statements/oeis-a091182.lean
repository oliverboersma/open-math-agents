import Mathlib

/-!
# Prime pairs from additive decompositions

OEIS A091182 counts the representations of n as x + y, with x ≥ y > 0,
for which xy − 1 and xy + 1 are both prime. Zhi-Wei Sun conjectured that the
count is positive for every n > 3120. He also proposed a generalization with
offset m and a threshold that may depend on m.

Source: https://oeis.org/A091182 (Zhi-Wei Sun, November 27, 2012).
Lean statement: @Halldon
-/

namespace OMA.S_oeis_a091182

/-- Both integers at distance m from xy are positive primes. -/
def primePair (m x y : ℕ) : Prop :=
  Nat.Prime (x * y - m) ∧ Nat.Prime (x * y + m)

theorem main :
    (∀ n : ℕ, 3120 < n → ∃ x y : ℕ, 0 < y ∧ y ≤ x ∧ n = x + y ∧ primePair 1 x y) ∧
    (∀ m : ℕ, 0 < m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even ((m - 1) * n) →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧ primePair m x y) := by
  sorry

end OMA.S_oeis_a091182
