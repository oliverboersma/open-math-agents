import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Nth

/-!
# Comparing base-11 digit restrictions

Sources: https://oeis.org/A212495 (Douglas Latimer) and https://oeis.org/A033036
(Clark Kimberling), OEIS Foundation, CC BY-SA 4.0. Both entries have offset 1.
The zero-based index i used by Nat.nth corresponds to source index i+1.
Zero is in the even-digit list and is excluded from the odd-digit list.
-/

namespace OMA.S_oeis_a212495

def evenDigits (n : ℕ) : Prop := ∀ d ∈ Nat.digits 11 n, Even d

def oddDigits (n : ℕ) : Prop := 0 < n ∧ ∀ d ∈ Nat.digits 11 n, Odd d

theorem main : {i : ℕ | Nat.nth oddDigits i < Nat.nth evenDigits i}.Finite := by
  sorry

end OMA.S_oeis_a212495
