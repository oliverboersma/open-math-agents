import Mathlib.Data.Nat.Basic

/-!
# Unboundedness of the halving and multiplication sequence

Source: https://oeis.org/A290650 (John Bailey, OEIS Foundation, CC BY-SA 4.0).
Felix Fröhlich conjectured that this positive-integer sequence is unbounded.
The first source term a(1) is represented by term 0.
-/

namespace OMA.S_oeis_a290650

def term : ℕ → ℕ
  | 0 => 1
  | i+1 => if term i % 2 = 0 then term i / 2 else term i * (i+2)

theorem main : ∀ B : ℕ, ∃ i : ℕ, B < term i := by
  sorry

end OMA.S_oeis_a290650
