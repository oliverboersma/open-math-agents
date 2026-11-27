import Mathlib

/-!
# Unimodality of a function of a non-negative matrix

Source: https://mathoverflow.net/questions/348551
Question by geo.wolfer. Lean statement by OpenAI Codex.

The two divisions in the question require positive time and positive Perron
root. The latter restriction is also noted in the comments on the question.
Eigenvalues are listed with algebraic multiplicity and in decreasing order.
The source describes a unit upper bound as an observation, not a hypothesis.
-/

namespace OMA.S_mo_348551

noncomputable section

/-- The positive Perron root: a real eigenvalue that bounds the modulus of
every complex eigenvalue. -/
def IsPositivePerronRoot {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (r : ℝ) : Prop :=
  0 < r ∧ A.charpoly.eval r = 0 ∧
    ∀ z : ℂ, (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 → ‖z‖ ≤ r

/-- The normalized Gram matrix of the k-th power. -/
def normalizedGram {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (r : ℝ) (k : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (r ^ (2 * k))⁻¹ • (A.transpose ^ k * A ^ k)

/-- A list of all the eigenvalues, including multiplicities, in spectral order. -/
def IsOrderedSpectrum {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) : Prop :=
  Antitone s ∧ M.charpoly = ∏ j : Fin d, (Polynomial.X - Polynomial.C (s j))

/-- Zero-based adjacent indices i and i+1 encode the source's one-based indices. -/
def gap {d : ℕ} (s : ℕ → Fin d → ℝ) (i : ℕ) (hi : i + 1 < d) (k : ℕ) : ℝ :=
  (s k ⟨i, by omega⟩ - s k ⟨i + 1, hi⟩) / (k : ℝ)

theorem main :
    ∀ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ u v, 0 ≤ A u v) (r : ℝ) (hr : IsPositivePerronRoot A r)
    (s : ℕ → Fin d → ℝ) (hs : ∀ k, 0 < k → IsOrderedSpectrum (normalizedGram A r k) (s k))
    (i : ℕ) (hi : i + 1 < d),
    ∃ k₀ : ℕ, 0 < k₀ ∧
      (∀ k, 0 < k → k < k₀ → gap s i hi k ≤ gap s i hi (k + 1)) ∧
      (∀ k, k₀ ≤ k → gap s i hi (k + 1) ≤ gap s i hi k) := by
  sorry

end

end OMA.S_mo_348551
