import FormalConjectures.ErdosProblems.«360»

/-!
# Reduction of the Alon–Erdős bounds for Erdős 360

The target is a conjunction of two independent asymptotic estimates sandwiching `f(n)` between
two explicit functions of `n`. Each inequality is its own step.
-/

-- Reduction Erdos360.erdos_360.variants.alon_erdos.R1
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1

/-- The lower bound: `n^(1/3) / (log n)^(4/3) ≪ f(n)`. -/
def H1 : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (4 / 3 : ℝ))
    (fun n : ℕ => (Erdos360.f n : ℝ))

/-- The upper bound: `f(n) ≪ n^(1/3) / (log n)^(1/3) * (log log n)^(1/3)`. -/
def H2 : Prop :=
  Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (Erdos360.f n : ℝ))
    (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (1 / 3 : ℝ) *
      Real.log (Real.log n) ^ (1 / 3 : ℝ))

theorem main : H1 → H2 → type_of% @Erdos360.erdos_360.variants.alon_erdos := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos360_erdos_360_variants_alon_erdos_R1
