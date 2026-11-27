import FormalConjectures.ErdosProblems.«748»

-- Reduction Erdos748.erdos_748.variants.asymptotic.R1 of Erdős Problem 748 — asymptotic
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target says that the two parity subsequences of the normalised count of sum-free sets
-- converge, with positive limits. Each subsequence is an independent convergence claim, so the
-- existence of the two constants is split per parity.

namespace OMA.R_Erdos748_erdos_748_variants_asymptotic_R1

open Erdos748 Filter

/-- The even subsequence `m ↦ f (2 * m) / 2 ^ m` converges to a positive limit. -/
def H1 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
    Tendsto (fun m : ℕ => (f (2 * m) : ℝ) / 2 ^ m) atTop (nhds c₀)

/-- The odd subsequence `m ↦ f (2 * m + 1) / 2 ^ ((2 * m + 1) / 2)` converges to a positive
limit. -/
def H2 : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧
    Tendsto (fun m : ℕ => (f (2 * m + 1) : ℝ) / 2 ^ ((2 * m + 1 : ℝ) / 2)) atTop (nhds c₁)

theorem main : H1 → H2 → type_of% @Erdos748.erdos_748.variants.asymptotic := by
  rintro ⟨c₀, hc₀, h1⟩ ⟨c₁, hc₁, h2⟩
  exact ⟨c₀, c₁, hc₀, hc₁, h1, h2⟩

end OMA.R_Erdos748_erdos_748_variants_asymptotic_R1
