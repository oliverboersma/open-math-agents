import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Decimal length of the triple Catalan iterate

Waldemar Puszkarz defines A273400 by three iterations of the Catalan
numbers, starting at index zero. He conjectures that only finitely many
indices have fewer decimal digits in this iterate than `catalan n`.
This is the explicit meaning given in OEIS for the growth comparison.

Source: https://oeis.org/A273400. Formalization by @anmolspace.
-/

namespace OMA.S_oeis_a273400

def a (n : ℕ) : ℕ := catalan (catalan (catalan n))

theorem main : {n : ℕ | (Nat.digits 10 (a n)).length < catalan n}.Finite := by
  sorry

end OMA.S_oeis_a273400
