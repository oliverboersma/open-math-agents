import Mathlib

/-!
# A trace-constrained Lyapunov maximization problem

Source: https://mathoverflow.net/questions/309804 (Ludwig, 4 September 2018).
Credit: @LDJAI.

For a real upper triangular matrix its diagonal entries are exactly its
eigenvalues, with multiplicity. Thus negative diagonal entries express the
Hurwitz assumption here. The dimension is positive so trace-one inputs exist.
The set contains the objective values of all feasible input and Gramian pairs.
Uniqueness of the Lyapunov solution for a Hurwitz matrix makes its supremum
identical to the one over inputs in the question.
-/

namespace OMA.S_mo_309804

noncomputable def values {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {y | ∃ X P : Matrix (Fin n) (Fin n) ℝ,
    X.PosDef ∧ X.trace = 1 ∧ P.PosDef ∧
    A * P + P * A.transpose = -X ∧ y = (X * (1 + P)⁻¹).trace}

theorem main : ∀ (n : ℕ) (_ : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ),
    A.IsUpperTriangular → (∀ i, A i i < 0) →
    (2 * A.trace) / (2 * A.trace - 1) ≤ sSup (values A) := by
  sorry

end OMA.S_mo_309804
