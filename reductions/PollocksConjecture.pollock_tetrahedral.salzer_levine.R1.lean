import FormalConjectures.Wikipedia.PollocksConjecture

-- Reduction PollocksConjecture.pollock_tetrahedral.salzer_levine.R1 of the Salzer-Levine strengthening of Pollock's conjecture
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Salzer and Levine found by computation that 343867 is not a sum of four tetrahedral numbers, and
conjectured that it is the largest such number. `H1` is their computation: no four tetrahedral
numbers add up to 343867, a search over all quadruples of the 127 tetrahedral numbers below it.
`H2` is the open part: every larger number is a sum of four tetrahedral numbers.
-/

namespace OMA.R_PollocksConjecture_pollock_tetrahedral_salzer_levine_R1

/-- Salzer and Levine: 343867 is not a sum of four tetrahedral numbers. -/
def H1 : Prop := (343867 : ℕ) ∈ PollocksConjecture.NotSumOfFourTetrahedral

/-- The open part: a number that is not a sum of four tetrahedral numbers is at most 343867. -/
def H2 : Prop := ∀ N ∈ PollocksConjecture.NotSumOfFourTetrahedral, N ≤ 343867

theorem main : H1 → H2 → type_of% @PollocksConjecture.pollock_tetrahedral.salzer_levine :=
  fun h1 h2 => ⟨h1, fun N hN => h2 N hN⟩

end OMA.R_PollocksConjecture_pollock_tetrahedral_salzer_levine_R1
