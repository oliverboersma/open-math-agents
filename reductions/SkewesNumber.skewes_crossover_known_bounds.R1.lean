import FormalConjectures.Wikipedia.SkewesNumber

/-!
# Reduction of the known bounds on the first Skewes crossover

The target is a conjunction of two independent facts about the sign change of `li(n) - π(n)`:
a verified computation that `π(n) < li(n)` up to `10 ^ 19`, and Skewes' existence bound giving some
`n` below `exp(727.95134)` where the inequality reverses. Different sources, different methods, so
each is its own step.
-/

-- Reduction SkewesNumber.skewes_crossover_known_bounds.R1
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_SkewesNumber_skewes_crossover_known_bounds_R1

/-- The verified range: no crossover below `10 ^ 19`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 10 ^ 19 → (Nat.primeCounting n : ℝ) < Real.logIntegral (n : ℝ)

/-- Skewes' existence bound: some `n` below `exp(727.95134)` has the reversed inequality. -/
def H2 : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) < Real.exp (72795134 / 100000) ∧
    Real.logIntegral (n : ℝ) < (Nat.primeCounting n : ℝ)

theorem main : H1 → H2 → type_of% @SkewesNumber.skewes_crossover_known_bounds := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_SkewesNumber_skewes_crossover_known_bounds_R1
