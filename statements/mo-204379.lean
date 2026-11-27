import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The largest gap under averaging parallel sums

Source: https://mathoverflow.net/questions/204379
Credit: @LDJAI

For positive inputs, the quotient defining each term is the parallel sum in
the question. The existential quantifier identifies a unique maximizing
parameter among all strictly positive real numbers.
-/

namespace OMA.S_mo_204379

open scoped BigOperators

noncomputable def D {n : ℕ} (b : Fin n → ℝ) (a : ℝ) : ℝ :=
  ((n : ℝ) * a) * (∑ i, b i) / ((n : ℝ) * a + ∑ i, b i) -
    ∑ i, a * b i / (a + b i)

theorem main : ∀ (n : ℕ), 0 < n → ∀ (b : Fin n → ℝ),
    (∀ i, 0 < b i) → (∃ i j, b i ≠ b j) →
    ∃! a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → D b x ≤ D b a := by
  sorry

end OMA.S_mo_204379
