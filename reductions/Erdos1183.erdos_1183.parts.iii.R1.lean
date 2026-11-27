import FormalConjectures.ErdosProblems.«1183»

-- Reduction Erdos1183.erdos_1183.parts.iii.R1 of Erdős Problem 1183, part iii.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target sandwiches `F n` between `n ^ c` for every fixed `c` (a lower bound beating every
-- polynomial) and `(1 + eps) ^ n` (an exponential upper bound). The two sides are independent
-- estimates on the same function, so each is its own step.

namespace OMA.R_Erdos1183_erdos_1183_parts_iii_R1

/-- Lower bound: `F n` eventually beats `n ^ c` for every real `c`. -/
def H1 : Prop :=
  ∀ c : ℝ,
    Filter.Eventually (fun n : ℕ => (n : ℝ) ^ c < (Erdos1183.F n : ℝ)) Filter.atTop

/-- Upper bound: `F n` is eventually below every exponential `(1 + eps) ^ n`, `eps > 0`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Eventually (fun n : ℕ => (Erdos1183.F n : ℝ) < (1 + ε) ^ n) Filter.atTop

theorem main : H1 → H2 → type_of% @Erdos1183.erdos_1183.parts.iii := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos1183_erdos_1183_parts_iii_R1
