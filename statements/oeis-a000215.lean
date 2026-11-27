import Mathlib

-- Credit: @Heart-galaxy
-- Source: https://oeis.org/A000215
namespace OMA.S_oeis_a000215

-- In the third conjecture, n > 5 is the common range of the numbers being characterized.
theorem main :
    (∀ n : ℕ, Nat.Prime (2 ^ (2 ^ n) + 1) ↔ n ≤ 4) ∧
    (∀ n : ℕ, (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = 2 ^ (2 ^ n) + 1) →
      Nat.minFac (2 ^ (2 ^ n) + 1) < 3 * 2 ^ ((2 ^ n) / 2 - n - 2)) ∧
    (∀ n : ℕ, n > 5 →
      ((∃ k : ℕ, k > 1 ∧ 2 ^ (2 ^ k) + 1 = n) ↔
        (n - 1) ^ 4 - 1 ∣ 2 ^ (n - 1) - 1)) := by
  sorry

end OMA.S_oeis_a000215