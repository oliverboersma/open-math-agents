import Mathlib.Data.Int.Basic

/-!
# Square and triangular representations in OEIS A270706

Source: https://oeis.org/A270706 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

This is part (i) of Zhi-Wei Sun's conjectures in the entry. The order of
an integer triple is retained, including the possibility of a negative
first coordinate. The uniqueness claim is about the full ordered triple.
-/

namespace OMA.S_oeis_a270706

def triangular (k : ℤ) : ℤ := k * (k + 1) / 2

def Represents (n : ℕ) (t : ℤ × ℤ × ℤ) : Prop :=
  t.1 ≠ 0 ∧ 0 < t.2.1 ∧ 0 ≤ t.2.2 ∧
    t.1 ^ 2 * triangular t.1 + t.2.1 ^ 2 + triangular t.2.2 = (n : ℤ)

theorem main :
    (∀ n : ℕ, 0 < n → ∃ t : ℤ × ℤ × ℤ, Represents n t) ∧
    (∀ n : ℕ, (∃! t : ℤ × ℤ × ℤ, Represents n t) →
      n = 1 ∨ n = 3 ∨ n = 90 ∨ n = 438 ∨ n = 480 ∨ n = 7108) := by
  sorry

end OMA.S_oeis_a270706
