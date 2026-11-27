import OMAStatements.S_mo_363072
import Mathlib.Analysis.Convex.Birkhoff

theorem OMA.solution : type_of% @OMA.S_mo_363072.main := by
  intro n A B hrow hcol hB σ hon hoff hmax
  classical
  set m : ℝ := 1 + ∑ i, A i (σ i) with hm
  have hdiag : ∀ i, A i (σ i) ≤ ∑ k, A k (σ k) :=
    fun i => Finset.single_le_sum (f := fun k => A k (σ k)) (fun k _ => hon k) (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ k, A k (σ k) := Finset.sum_nonneg (fun k _ => hon k)
  have mpos : 0 < m := by rw [hm]; linarith
  let S : Matrix (Fin n) (Fin n) ℝ := fun i j => (if j = σ i then 1 else 0) - A i j / m
  have hS : S ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases h : j = σ i
      · subst h
        have := hdiag i
        simp only [S, if_true]
        rw [sub_nonneg, div_le_one mpos]; rw [hm]; linarith
      · simp only [S, h, if_false]
        have := hoff i j h
        have : A i j / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg this mpos.le
        linarith
    · intro i
      simp only [S, Finset.sum_sub_distrib, ← Finset.sum_div, hrow i]
      simp
    · intro j
      simp only [S, Finset.sum_sub_distrib, ← Finset.sum_div, hcol j]
      have e : ∀ x, (j = σ x) ↔ (σ.symm j = x) := fun x => (Equiv.symm_apply_eq σ).symm
      simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp
  have hle : ∑ i, ∑ j, S i j * B i j ≤ ∑ i, B i (σ i) := by
    obtain ⟨w, hw0, hw1, hw3⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
    have hSij : ∀ i j, S i j = ∑ τ, w τ * (if τ i = j then 1 else 0) := by
      intro i j
      have := congrFun (congrFun hw3 i) j
      rw [← this]
      simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    have h1 : ∀ i, ∑ j, S i j * B i j = ∑ τ, w τ * B i (τ i) := by
      intro i
      simp only [hSij, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp [ite_mul, Finset.sum_ite_eq]
    have h2 : ∑ i, ∑ j, S i j * B i j = ∑ τ, w τ * ∑ i, B i (τ i) := by
      simp only [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.mul_sum]
    rw [h2]
    calc ∑ τ, w τ * ∑ i, B i (τ i) ≤ ∑ τ, w τ * ∑ i, B i (σ i) :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hmax τ) (hw0 τ)
      _ = ∑ i, B i (σ i) := by rw [← Finset.sum_mul, hw1, one_mul]
  have key : ∑ i, ∑ j, A i j * B i j = m * (∑ i, B i (σ i) - ∑ i, ∑ j, S i j * B i j) := by
    have e : ∑ i, ∑ j, S i j * B i j = ∑ i, B i (σ i) - (∑ i, ∑ j, A i j * B i j) / m := by
      simp only [S, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [e]
    field_simp
    ring
  rw [key]
  exact mul_nonneg mpos.le (by linarith)
