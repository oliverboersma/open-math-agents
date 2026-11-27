import FormalConjectures.ErdosProblems.«50»

-- Reduction Erdos50.erdos_50_singular.R1 of Erdős Problem 50 — erdos 50 singular
-- Credit: @tamoghnokandar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Split: H1 is the continuity half (the distribution has no atoms), H2 is the singularity half
-- (derivative zero almost everywhere), which may assume continuity.

namespace OMA.R_Erdos50_erdos_50_singular_R1

/-- The distribution function of `φ(n)/n` is continuous on `[0, 1]`. -/
def H1 : Prop :=
  ∀ f : ℝ → ℝ, Erdos50.IsDistributionOfPhiRatio f → ContinuousOn f (Set.Icc 0 1)

/-- Given continuity, its derivative within `[0, 1]` vanishes almost everywhere on `[0, 1]`. -/
def H2 : Prop :=
  ∀ f : ℝ → ℝ, Erdos50.IsDistributionOfPhiRatio f → ContinuousOn f (Set.Icc 0 1) →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      derivWithin f (Set.Icc 0 1) x = 0

theorem main : H1 → H2 → type_of% @Erdos50.erdos_50_singular := by
  intro h1 h2 f hf
  exact ⟨h1 f hf, h2 f hf (h1 f hf)⟩

end OMA.R_Erdos50_erdos_50_singular_R1
