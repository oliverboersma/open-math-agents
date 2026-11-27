import Mathlib.Data.Nat.GCD.Basic

/-!
# Strong divisibility for a second-order recurrence

Lehs's question on Mathematics Stack Exchange asks about all positive
coprime coefficients and all positive initial values F(1), with F(0) = 0.
The recurrence starts at F(2), so it never needs a negative index.

Source: https://math.stackexchange.com/questions/2145404
Formalization: @ecirak42.
-/

namespace OMA.S_mse_2145404

theorem main : ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    ∀ F : ℕ → ℕ, F 0 = 0 → 0 < F 1 →
    (∀ i : ℕ, F (i + 2) = a * F (i + 1) + b * F i) →
    ∀ m n : ℕ, F (Nat.gcd m n) = Nat.gcd (F n) (F m) := by
  sorry

end OMA.S_mse_2145404
