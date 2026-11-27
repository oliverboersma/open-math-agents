import OMAStatements.S_oeis_a078712

namespace OMA.P_a078712

open Matrix OMA.S_oeis_a078712

def M : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 0; 0, 1, -1]

lemma M_cube : M ^ 3 = -(M ^ 2) + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

lemma tr_rec (n : ℕ) : trace (M ^ (n + 3)) = -trace (M ^ (n + 2)) + trace (M ^ n) := by
  have h : M ^ (n + 3) = -(M ^ (n + 2)) + M ^ n := by
    rw [pow_add, M_cube, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_one, ← pow_add]
  rw [h, trace_add, trace_neg]

lemma a_eq (n : ℕ) : a n = -trace (M ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a, trace]
    | 1, _ => simp [a, M, trace, Fin.sum_univ_three]
    | 2, _ => simp [a, M, trace, Fin.sum_univ_three, pow_two]
    | n + 3, ih =>
      rw [a, ih (n + 2) (by omega), ih n (by omega), tr_rec]
      ring

theorem main : ∀ p : ℕ, p.Prime → a p ≡ 1 [ZMOD p] := by
  intro p hp
  have := Fact.mk hp
  rw [← ZMod.intCast_eq_intCast_iff, a_eq]
  have hmap : ((M ^ p).map (Int.cast : ℤ → ZMod p)) = (M.map (Int.cast : ℤ → ZMod p)) ^ p :=
    Matrix.map_pow M (Int.castRingHom (ZMod p)) p
  have htr : ((trace (M ^ p) : ℤ) : ZMod p) = trace ((M ^ p).map (Int.cast : ℤ → ZMod p)) := by
    simp [trace, Matrix.map_apply]
  have h1 : trace (M.map (Int.cast : ℤ → ZMod p)) = -1 := by
    simp [trace, M, Fin.sum_univ_three]
  push_cast
  rw [htr, hmap, ZMod.trace_pow_card, h1, ZMod.pow_card]
  simp

end OMA.P_a078712

theorem OMA.solution : type_of% @OMA.S_oeis_a078712.main := OMA.P_a078712.main
