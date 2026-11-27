import FormalConjectures.GreensOpenProblems.«91»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green91_green_91_variants_fknss_R1
open Green91 Filter Asymptotics
open scoped Topology

/-- The fixed-error probabilistic estimate for friendly bisections. -/
def H1 : Prop :=
  ∀ k : ℕ, Tendsto (fun n : ℕ ↦ prob n fun G ↦
    ∃ s : Finset (Fin n), s.card = n / 2 ∧
      (n : ℝ) - (1 / ((k : ℝ) + 1)) * n ≤ numFriendly G s) atTop (𝓝 1)

/-- Select a diverging accuracy index while preserving convergence in probability values. -/
def H2 : Prop :=
  ∀ P : ℕ → ℕ → ENNReal, (∀ k, Tendsto (P k) atTop (𝓝 1)) →
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ Tendsto (fun n ↦ P (k n) n) atTop (𝓝 1)

theorem main : H1 → H2 → type_of% @Green91.green_91.variants.fknss := by
  intro fixed diag
  let P (k n : ℕ) := prob n fun G ↦ ∃ s : Finset (Fin n), s.card = n / 2 ∧
    (n : ℝ) - (1 / ((k : ℝ) + 1)) * n ≤ numFriendly G s
  obtain ⟨k,hk,hd⟩ := diag P fixed
  refine ⟨fun n ↦ (1 / ((k n : ℝ) + 1)) * n, ?_, hd⟩
  have hz : Tendsto (fun n ↦ 1 / ((k n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  simpa only [one_mul] using
    ((isLittleO_one_iff ℝ).2 hz).mul_isBigO (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)

end OMA.R_Green91_green_91_variants_fknss_R1
