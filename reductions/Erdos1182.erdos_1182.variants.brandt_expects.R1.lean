import FormalConjectures.ErdosProblems.«1182»

-- Reduction Erdos1182.erdos_1182.variants.brandt_expects.R1 of Erdős Problem 1182
-- (Brandt's expected order of growth of the 3-good edge threshold).
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target bounds `F n` between `2 n` and `6 n` eventually. The two inequalities are proved from
-- different constructions (a lower-bound family and an upper-bound obstruction), so each is its own
-- step.

namespace OMA.R_Erdos1182_erdos_1182_variants_brandt_expects_R1

/-- Lower bound: eventually `F n` exceeds `2 n`. -/
def H1 : Prop :=
  Filter.Eventually (fun n : ℕ => 2 * n < Erdos1182.F n) Filter.atTop

/-- Upper bound: eventually `F n` is below `6 n`. -/
def H2 : Prop :=
  Filter.Eventually (fun n : ℕ => Erdos1182.F n < 6 * n) Filter.atTop

theorem main : H1 → H2 →
    type_of% @Erdos1182.erdos_1182.variants.brandt_expects := by
  intro h1 h2
  exact h1.and h2

end OMA.R_Erdos1182_erdos_1182_variants_brandt_expects_R1
