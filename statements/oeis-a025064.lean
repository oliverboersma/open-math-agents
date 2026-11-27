import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-!
# Positions of representable numbers of the form 3k² (OEIS A025064)

A025060 lists the positive values of ab + bc + ac for 0 < a < b < c, in increasing
order without repetition. A025064 gives the positions of the values of the form
3k² in that list. Both ranks start at one. Robert Israel's formula starts at
index 22 of A025064.

Source: https://oeis.org/A025064 (OEIS Foundation, CC BY-SA 4.0)
Formalization: @DomTheDeveloper
-/

namespace OMA.S_oeis_a025064

def Representable (m : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ m = a * b + b * c + a * c

noncomputable def countTo (P : ℕ → Prop) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 m).filter P).card

theorem main : ∀ n : ℕ, 22 ≤ n → ∃ k : ℕ, 0 < k ∧ Representable (3 * k ^ 2) ∧
    countTo (fun j => Representable (3 * j ^ 2)) k = n ∧
    countTo Representable (3 * k ^ 2) = 3 * n ^ 2 + 18 * n - 38 := by
  sorry

end OMA.S_oeis_a025064
