import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symmetric extremal matrices in OEIS A072567

Source: https://oeis.org/A072567 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

Max Alekseyev conjectures that a symmetric binary matrix attains the maximum
number of ones among square binary matrices with no all-ones rectangle.
Diagonal entries are allowed as in OEIS A350189.
-/

namespace OMA.S_oeis_a072567

def rectangleFree {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∀ i i' j j', i ≠ i' → j ≠ j' →
    ¬ (A i j = true ∧ A i j' = true ∧ A i' j = true ∧ A i' j' = true)

def numberOfOnes {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => A p.1 p.2 = true).card

theorem main : ∀ n : ℕ, 0 < n →
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B := by
  sorry

end OMA.S_oeis_a072567
