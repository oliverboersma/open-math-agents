import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime divisors of numbers whose consecutive divisor differences divide the number

Source: https://oeis.org/A060765 (David A. Corneth's July 2017 conjecture,
OEIS Foundation, CC BY-SA 4.0). A positive integer belongs to the sequence when
any two neighboring divisors, in increasing order, differ by a divisor of n.
-/

namespace OMA.S_oeis_a060765

def belongs (n : ℕ) : Prop := 0 < n ∧ ∀ a b : ℕ, a ∣ n → b ∣ n → a < b →
    (∀ d : ℕ, d ∣ n → a < d → d < b → False) → b-a ∣ n

theorem main : ∀ n : ℕ, belongs n → ∀ p : ℕ, p.Prime → p ∣ n → p-1 ∣ n/p := by
  sorry

end OMA.S_oeis_a060765
