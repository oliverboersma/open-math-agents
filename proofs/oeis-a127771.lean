import OMAStatements.S_oeis_a127771
import Mathlib

namespace A127771Aux
open OMA.S_oeis_a127771

def U (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun i j =>
  if (j : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * j then 1 else 0

lemma det_U (N : ℕ) : (U N).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    have h : ((i : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * i) := ⟨le_refl _, by omega⟩
    show (if (i : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * i then (1 : ℤ) else 0) = 1
    rw [if_pos h]
  · intro i j hij
    have hlt : i < j := hij
    have h : ¬ ((j : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * j) := by
      intro h'
      have : (i : ℕ) < j := hlt
      omega
    show (if (j : ℕ) ≤ i ∧ (i : ℕ) ≤ 2 * j then (1 : ℤ) else 0) = 0
    rw [if_neg h]

lemma U_mul_inv (N : ℕ) : U N * (U N)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [det_U]; exact isUnit_one)

noncomputable def B (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ :=
  (U N)⁻¹ * Matrix.diagonal (fun i : Fin (N + 1) => (((i : ℕ) + 1).totient : ℤ))

lemma A_eq (N : ℕ) : A N =
    Matrix.diagonal (fun i : Fin (N + 1) => (1 : ℚ) / (((i : ℕ) + 1).totient : ℚ)) *
      (U N).map (Int.castRingHom ℚ) := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [A, U, Matrix.map_apply]
  split_ifs <;> simp

end A127771Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a127771.main := by
  intro N i j
  have hinv : (OMA.S_oeis_a127771.A N)⁻¹ = (A127771Aux.B N).map (Int.castRingHom ℚ) := by
    apply Matrix.inv_eq_right_inv
    rw [A127771Aux.A_eq]
    unfold A127771Aux.B
    rw [Matrix.map_mul (f := Int.castRingHom ℚ), Matrix.mul_assoc,
      ← Matrix.mul_assoc ((A127771Aux.U N).map (Int.castRingHom ℚ)), ← Matrix.map_mul (f := Int.castRingHom ℚ),
      A127771Aux.U_mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
      Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    have hpos : 0 < ((k : ℕ) + 1).totient := Nat.totient_pos.mpr (Nat.succ_pos (k : ℕ))
    have hne : (((k : ℕ) + 1).totient : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    simp only [eq_intCast, Int.cast_natCast]
    field_simp
  refine ⟨A127771Aux.B N i j, ?_⟩
  rw [hinv]
  simp
