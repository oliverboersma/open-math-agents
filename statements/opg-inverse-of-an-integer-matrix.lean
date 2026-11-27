import Mathlib

/-!
# An integer right inverse for a diagonal block extended by columns

Source: https://www.openproblemgarden.org/op/inverse_of_an_integer_matrix
Credit: @rleshner

Gregory asks for necessary and sufficient conditions and suggests relative
primality in each row. We state that proposed characterization as an equivalence.
Positive diagonal integers are represented by naturals at least two.
-/

namespace OMA.S_opg_inverse_of_an_integer_matrix

def block {m n : ℕ} (d : Fin m → ℕ) (X : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin m ⊕ Fin n) ℤ :=
  (Matrix.diagonal fun i => (d i : ℤ)).fromCols X

def admitsRightInverse {m n : ℕ} (d : Fin m → ℕ) (X : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ R : Matrix (Fin m ⊕ Fin n) (Fin m) ℤ, block d X * R = 1

def primitiveRows {m n : ℕ} (d : Fin m → ℕ) (X : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ (i : Fin m) (q : ℤ), (∀ k, q ∣ block d X i k) → q ∣ 1

theorem main :
    ∀ (m n : ℕ), m ≤ n → ∀ (d : Fin m → ℕ) (X : Matrix (Fin m) (Fin n) ℤ),
      (∀ i, 2 ≤ d i) → (admitsRightInverse d X ↔ primitiveRows d X) := by
  sorry

end OMA.S_opg_inverse_of_an_integer_matrix
