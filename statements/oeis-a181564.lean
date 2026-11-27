import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Insert

/-!
# Semiprime idoneal numbers (OEIS A181564)

Jonathan Vos Post conjectured that the sixteen listed semiprime idoneal numbers
are all of them. The length of the prime factor list counts multiplicity.
The ternary representation criterion is Euler's equivalent definition of
idoneality used in Formal Conjectures.

Source: https://oeis.org/A181564 (OEIS Foundation, CC BY-SA 4.0)
Formalization: @DomTheDeveloper
-/

namespace OMA.S_oeis_a181564

def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧ ¬ ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

theorem main : ∀ n : ℕ, (IsIdoneal n ∧ n.primeFactorsList.length = 2) ↔
    n ∈ ({4, 6, 9, 10, 15, 21, 22, 25, 33, 57, 58, 85, 93, 133, 177, 253} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a181564
