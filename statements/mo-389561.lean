import Mathlib

/-!
# MathOverflow 389561

Source: https://mathoverflow.net/questions/389561
-/

namespace OMA.S_mo_389561



theorem main : ∀ (n : ℕ) (F : Type) [Field F] [Fintype F] [CharP F 3],
    Fintype.card F = 3 ^ (2 * n + 1) →
    (∀ x y : F, x ^ 2 + y ^ 2 + y + 1 = 0 ↔ x = 0 ∧ y = 1) ∧
    (∀ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
      (x ^ 2 + y ^ 2 + y * z + z ^ 2 = 0 ↔ x = 0 ∧ y = z ∧ z ≠ 0)) := by
  sorry

end OMA.S_mo_389561
