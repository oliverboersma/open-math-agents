import Mathlib

/-!
# OEIS A077739: multiples beginning and ending in n with digit sum n

Amarnath Murthy's sequence takes the smallest positive multiple m of n
which begins and ends with the decimal expansion of n and has digit sum n.
The term is zero when there is no such multiple. Its conjectured zero
indices are exactly 11, 17, and 19. Positional digits in Mathlib are
little-endian, so the prefix condition checks the low digits of m
and the suffix condition checks its high digits. The two copies may overlap.

Source: https://oeis.org/A077739
-/

namespace OMA.S_oeis_a077739

def qualifies (n m : ℕ) : Prop :=
  0 < m ∧ n ∣ m ∧
    (Nat.digits 10 n).IsPrefix (Nat.digits 10 m) ∧
    (Nat.digits 10 n).IsSuffix (Nat.digits 10 m) ∧
    (Nat.digits 10 m).sum = n

noncomputable def term (n : ℕ) : ℕ := sInf {m | qualifies n m}

theorem main : ∀ n : ℕ, 0 < n → (term n = 0 ↔ n = 11 ∨ n = 17 ∨ n = 19) := by
  sorry

end OMA.S_oeis_a077739
