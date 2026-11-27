import OMAStatements.S_oeis_a265739
import Mathlib

/-!
# Proof of OEIS A265739 conjecture

Credit: @AkiRA-COM-FP
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a265739.main := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  let error (j : ℕ) : ℝ := |(j : ℝ) * Real.pi - (round ((j : ℝ) * Real.pi) : ℝ)|
  obtain ⟨j, hj, hmin⟩ :=
    Set.exists_min_image (Set.Icc 1 (N + 1)) error (Set.finite_Icc 1 (N + 1))
      ⟨1, Set.mem_Icc.mpr ⟨le_rfl, Nat.succ_pos N⟩⟩
  have hjpos : 0 < error j := by
    have hj0 : j ≠ 0 := Nat.ne_of_gt (Set.mem_Icc.mp hj).1
    exact abs_pos.mpr (sub_ne_zero.mpr
      ((irrational_pi.natCast_mul hj0).ne_int (round ((j : ℝ) * Real.pi))))
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / error j)
  have hMpos : 0 < M := Nat.cast_pos.mp ((one_div_pos.mpr hjpos).trans hM)
  obtain ⟨k, hkpos, hkM, herr⟩ := Real.exists_nat_abs_mul_sub_round_le Real.pi hMpos
  change error k ≤ 1 / ((M : ℝ) + 1) at herr
  have hsmall : 1 / ((M : ℝ) + 1) < error j :=
    (one_div_lt (add_pos (Nat.cast_pos.mpr hMpos) zero_lt_one) hjpos).mpr
      (hM.trans (lt_add_one _))
  have hNk : N < k := by
    by_contra! hkN
    have hkj := hmin k (Set.mem_Icc.mpr ⟨hkpos, hkN.trans (Nat.le_succ N)⟩)
    exact (not_lt_of_ge hkj) (herr.trans_lt hsmall)
  have hbound : 1 / ((M : ℝ) + 1) ≤ 1 / (k : ℝ) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr hkpos)
      ((Nat.cast_le.mpr hkM).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨k, ⟨hkpos, round ((k : ℝ) * Real.pi), ?_⟩, hNk⟩
  rw [mul_comm Real.pi]
  exact herr.trans hbound
