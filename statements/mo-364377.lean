import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Data.Real.Basic

/-!
# Entrywise motion toward a nearest signed permutation

Source: https://mathoverflow.net/questions/364377
Credit: @LDJAI

This is the original nearest-target question. Squared Frobenius distance
gives the same minimizers and neighborhoods as Frobenius distance.
-/

namespace OMA.S_mo_364377

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def orthogonal {n : ℕ} (A : Mat n) : Prop := A.transpose * A = 1

def signedPermutation {n : ℕ} (P : Mat n) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ),
    (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, P i j = if j = σ i then s i else 0

noncomputable def frobSq {n : ℕ} (A B : Mat n) : ℝ :=
  ∑ i, ∑ j, (A i j - B i j)^2

theorem main : ∀ (n : ℕ) (A P : Mat n), orthogonal A →
    (¬ signedPermutation A) → signedPermutation P →
    (∀ Q : Mat n, signedPermutation Q → frobSq A P ≤ frobSq A Q) →
    ∀ δ : ℝ, 0 < δ → ∃ B : Mat n, orthogonal B ∧ frobSq A B < δ ∧
      (∀ i j, P i j ≠ 0 → |A i j| ≤ |B i j|) ∧
      (∃ i j, P i j ≠ 0 ∧ |A i j| < |B i j|) ∧
      (∀ i j, P i j = 0 → |B i j| ≤ |A i j|) := by
  sorry

end OMA.S_mo_364377
