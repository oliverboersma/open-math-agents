import Mathlib

/-!
# Sums of independent random variables with unbounded variance

Source: https://www.openproblemgarden.org/op/sums_of_independent_random_variables_with_unbounded_variance
Credit: @koolkao

Conjecture (Feige). If `X₁, …, Xₙ ≥ 0` are independent random variables with `𝔼[Xᵢ] ≤ μ`, then
`Pr(∑ Xᵢ - 𝔼[∑ Xᵢ] < δ μ) ≥ min((1 + δ)⁻¹ δ, e⁻¹)`.

Reading of the source (the conventions of Feige, STOC 2004, where the problem appears):
* `δ > 0` and `μ > 0`. The source leaves both implicit. With `μ = 0` every `Xᵢ` is `0` almost surely
  and the event is empty, and with `δ < -1` the bound `δ / (1 + δ)` exceeds `1`, so both readings
  are needed for the statement to make sense. Feige's theorem is stated for every `δ > 0`.
* `𝔼[Xᵢ] ≤ μ` presupposes that the expectation is finite, so each `Xᵢ` is assumed integrable.
  In Lean, the integral of a non-integrable function is `0`, so this hypothesis must be explicit.
* `n` is arbitrary (`n = 0` holds trivially), and the variables live on an arbitrary probability space
  (in `Type`, which loses no generality for real-valued random variables).
* Feige proved the bound with `1/13` in place of `e⁻¹`. The conjecture is that `e⁻¹` works.
  The value `e⁻¹` would be sharp, as the source shows with `δ = 𝔼[Xᵢ] = 1` and `Xᵢ` equal to `n + 1`
  with probability `(n + 1)⁻¹` and `0` otherwise.
-/

namespace OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance

open MeasureTheory ProbabilityTheory

theorem main :
    ∀ (n : ℕ) (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Fin n → Ω → ℝ) (μ δ : ℝ), 0 < μ → 0 < δ →
      iIndepFun X ℙ → (∀ i ω, 0 ≤ X i ω) → (∀ i, Integrable (X i)) → (∀ i, 𝔼[X i] ≤ μ) →
      min (δ / (1 + δ)) (Real.exp (-1)) ≤
        (ℙ {ω | ∑ i, X i ω - 𝔼[fun ω' => ∑ i, X i ω'] < δ * μ}).toReal := by
  sorry

end OMA.S_opg_sums_of_independent_random_variables_with_unbounded_variance
