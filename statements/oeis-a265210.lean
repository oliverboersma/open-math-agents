import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Card

/-!
# Period and digit frequencies in the ternary columns of powers of two

Source: https://oeis.org/A265210 (L. Edson Jeffery, OEIS Foundation, CC BY-SA 4.0).

The entry numbers columns starting at one. Here j = k-1, so 3^j is the
place value of column k. A row belongs to that column exactly when the
power of two in the row has reached that place value.
-/

namespace OMA.S_oeis_a265210

def digit (j n : ℕ) : ℕ := (2^n / 3^j) % 3

def columnPeriod (j t : ℕ) : Prop :=
  ∀ n : ℕ, 3^j ≤ 2^n → digit j (n+t) = digit j n

theorem main : ∀ j : ℕ,
    IsLeast {t : ℕ | 0 < t ∧ columnPeriod j t} (2*3^j) ∧
    (0 < j → ∀ start : ℕ, 3^j ≤ 2^start → ∀ d : ℕ, d < 3 →
      ((Finset.range (2*3^j)).filter (fun i => digit j (start+i) = d)).card = (2*3^j)/3) := by
  sorry

end OMA.S_oeis_a265210
