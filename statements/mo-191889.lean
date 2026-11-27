import Mathlib

/-!
# The least powerful sum of two coprime fourth powers

Noam D. Elkies asks whether 3088257489493360278725196965477359217 is the
least powerful number expressible as x^4 + y^4 with coprime x and y.
We use positive x and y, the intended nontrivial convention in the question.
The displayed example has x = 427511122 and y = 1322049209.

Source https://mathoverflow.net/questions/191889
Question by Noam D. Elkies, CC BY-SA.
Formalization credited to @gwelb.
-/

namespace OMA.S_mo_191889

/-- A positive integer is powerful when every prime divisor divides it at least twice. -/
def IsPowerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem main :
    IsLeast {n : ℕ | IsPowerful n ∧
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x.Coprime y ∧ n = x ^ 4 + y ^ 4}
      3088257489493360278725196965477359217 := by
  sorry

end OMA.S_mo_191889
