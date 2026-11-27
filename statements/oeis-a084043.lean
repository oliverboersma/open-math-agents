import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Find

/-!
# Palindromic multiples with an internal occurrence of the original digits

Source: https://oeis.org/A084043 (Amarnath Murthy, OEIS Foundation, CC BY-SA 4.0).
For positive n, a(n) is the least positive palindromic multiple of n in which the
complete decimal representation of n is preceded and followed by at least one digit,
with zero used when no witness exists. Nat.digits lists digits in reverse reading
order. Reversing all three strings preserves the two nonempty margins.
-/

namespace OMA.S_oeis_a084043

def admissible (n m : ℕ) : Prop := 0 < m ∧ n ∣ m ∧
    (Nat.digits 10 m).reverse = Nat.digits 10 m ∧
    ∃ left right : List ℕ, left ≠ [] ∧ right ≠ [] ∧
      Nat.digits 10 m = left ++ Nat.digits 10 n ++ right

noncomputable def a (n : ℕ) : ℕ := open Classical in
  if h : ∃ m, admissible n m then Nat.find h else 0

theorem main : ∀ n : ℕ, 0 < n → (a n = 0 ↔ 10 ∣ n) := by
  sorry

end OMA.S_oeis_a084043
