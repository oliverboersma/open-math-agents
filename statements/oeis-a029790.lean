import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Card

/-!
# Disjoint decimal digits in OEIS A029790

Source: https://oeis.org/A029790 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The sequence lists positive integers whose decimal digits occur in neither
their square nor their cube. Manfred Scheucher conjectures that there is no
28th term. The source lists 27 terms.
-/

namespace OMA.S_oeis_a029790

def qualifies (k : ℕ) : Prop :=
  0 < k ∧ ∀ d ∈ Nat.digits 10 k, d ∉ Nat.digits 10 (k ^ 2) ∧ d ∉ Nat.digits 10 (k ^ 3)

theorem main : Set.encard {k : ℕ | qualifies k} = 27 := by
  sorry

end OMA.S_oeis_a029790
