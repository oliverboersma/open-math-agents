import Mathlib

/-!
# Asymptotics of the running standard deviation

Source: https://math.stackexchange.com/questions/4190405

The sequence x is indexed from zero, so x 0 is the source's initial x₁.
The root r determines the unique exponent in (0,1/2) satisfying the displayed
polynomial. The explicit absolutely convergent series specifies the amplitude.
-/

namespace OMA.S_mse_4190405

open Filter
open scoped BigOperators Topology

noncomputable def ratio : ℕ → ℝ
  | 0 => 1
  | n+1 =>
    let t : ℝ := ((n : ℝ) + 2)⁻¹
    (ratio n + t) / Real.sqrt (1 + t * (1 + (ratio n - 1)^2))

noncomputable def correction (r : ℝ) (n : ℕ) : ℝ :=
  let t : ℝ := ((n : ℝ) + 2)⁻¹
  Real.log (1 + t / ratio n) - r⁻¹ * Real.log (1 + t)

noncomputable def amplitude (r : ℝ) : ℝ :=
  Real.exp (∑' n, correction r n) / (r * (2 : ℝ) ^ r⁻¹)

def evolves (x : ℕ → ℝ) : Prop :=
  ∀ n, x (n+1) = Real.sqrt
    ((∑ j ∈ Finset.range (n+1), (x j)^2) / ((n : ℝ)+1) -
      ((∑ j ∈ Finset.range (n+1), x j) / ((n : ℝ)+1))^2)

/-- Equivalent to the question's radical formula, with z = τ / 2^(2/3). -/
noncomputable def exponent : ℝ :=
  let z := (((13+3*Real.sqrt 33)/4 : ℝ) ^ (1/3 : ℝ))
  (2+2/z-z)/3

theorem main :
    ∃ r ∈ Set.Ioo (1 : ℝ) 2, r * (1 + (r - 1)^2) = 2 ∧
      let α := 1 - r⁻¹
      α ∈ Set.Ioo (0 : ℝ) (1/2) ∧ α^2 = (1 - 2*α) * (1-α)^2 ∧
      α = exponent ∧ Summable (fun n => |correction r n|) ∧ 0 < amplitude r ∧
      ∀ x : ℕ → ℝ, 0 < x 0 → evolves x →
        Tendsto (fun n : ℕ => ((n : ℝ)+1)^α * x n / x 0) atTop (𝓝 (amplitude r)) := by
  sorry

end OMA.S_mse_4190405
