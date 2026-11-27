import OMAStatements.S_opg_inverse_of_an_integer_matrix

-- Problem: opg-inverse-of-an-integer-matrix.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- Counterexample with m = n = 2: d = (2, 2) and X = [[1, 0], [1, 0]], so the block matrix is
-- [[2, 0, 1, 0], [0, 2, 1, 0]]. Each row contains the entry 1, so the rows are primitive.
-- A right inverse R would give 2 R(0,0) + R(2,0) = 1 and 2 R(1,0) + R(2,0) = 0 in the first
-- column, which is impossible modulo 2.

open OMA.S_opg_inverse_of_an_integer_matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_inverse_of_an_integer_matrix.main) := by
  intro h
  have key := h 2 2 le_rfl (fun _ => 2) !![1, 0; 1, 0] (fun _ => le_rfl)
  have hprim : primitiveRows (fun _ : Fin 2 => 2) !![1, 0; 1, 0] := by
    intro i q hq
    have h1 := hq (Sum.inr 0)
    have e : block (fun _ : Fin 2 => 2) !![1, 0; 1, 0] i (Sum.inr 0) = 1 := by
      unfold block
      fin_cases i <;> simp
    rw [e] at h1
    exact h1
  obtain ⟨R, hR⟩ := key.mpr hprim
  have h00 := congrFun (congrFun hR 0) 0
  have h10 := congrFun (congrFun hR 1) 0
  simp [block, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.diagonal_apply] at h00 h10
  omega
