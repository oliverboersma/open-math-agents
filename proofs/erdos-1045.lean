import OMAStatements.S_erdos_1045

namespace OMA.Diameter
open Finset Matrix Polynomial
open scoped RealInnerProductSpace ComplexConjugate

-- Hadamard's inequality in matrix coordinates, following the proof of Green 27.
theorem abs_det_le_prod_euclidean_row_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin d))‖ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d) := ⟨by simp⟩
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
    EuclideanSpace.basisFun (Fin d) ℝ
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin d)) (Fin d) := b.toBasis.orientation
  let v : Fin d → EuclideanSpace ℝ (Fin d) := fun i => WithLp.toLp 2 (A i)
  have h := o.abs_volumeForm_apply_le v
  rw [o.volumeForm_robust' b v] at h
  have hd : b.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply]
    rw [show b.toBasis.toMatrix v = Aᵀ by
      ext i j
      simp [b, v, Module.Basis.toMatrix_apply], Matrix.det_transpose]
  rwa [hd] at h


lemma chebDegreeMonic (k : ℕ) :
    (Chebyshev.C ℝ (k : ℤ)).natDegree = k ∧
      (k ≠ 0 → (Chebyshev.C ℝ (k : ℤ)).Monic) := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more k hk hs =>
    have hm := hs.2 (Nat.succ_ne_zero _)
    have hdeg : (X * Chebyshev.C ℝ ((k+1 : ℕ) : ℤ)).natDegree = k+2 := by
      rw [natDegree_mul (by exact X_ne_zero) hm.ne_zero, natDegree_X, hs.1]
      omega
    have hlt : (Chebyshev.C ℝ (k : ℤ)).natDegree <
        (X * Chebyshev.C ℝ ((k+1 : ℕ) : ℤ)).natDegree := by rw [hdeg, hk.1]; omega
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.C_add_two, ← Nat.cast_add_one]
    exact ⟨(natDegree_sub_eq_left_of_natDegree_lt hlt).trans hdeg,
      fun _ => (monic_X.mul hm).sub_of_left (degree_lt_degree hlt)⟩

noncomputable def p (k : ℕ) : ℝ[X] := if k = 0 then 1 else Chebyshev.C ℝ (k : ℤ)

lemma p_properties (k : ℕ) : (p k).natDegree = k ∧ (p k).Monic := by
  by_cases h : k = 0
  · simp [h, p]
  · simpa [p, h] using And.intro (chebDegreeMonic k).1 ((chebDegreeMonic k).2 h)

lemma p_bound (k : ℕ) (x : ℝ) (hx : |x| ≤ 2) : |(p k).eval x| ≤ 2 := by
  by_cases hk : k = 0
  · norm_num [p, hk]
  obtain ⟨hx₁,hx₂⟩ := abs_le.mp hx
  let θ := Real.arccos (x / 2)
  have he : 2 * Real.cos θ = x := by
    dsimp [θ]
    rw [Real.cos_arccos (by linarith) (by linarith)]
    ring
  rw [p, if_neg hk, ← he, Chebyshev.C_two_mul_real_cos, abs_mul]
  have := Real.abs_cos_le_one ((k : ℤ) * θ)
  norm_num at *
  linarith

lemma realVander {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 2) :
    |(vandermonde x).det| ≤ (2 * Real.sqrt n) ^ n := by
  let A := Matrix.of (fun i j : Fin n => (p j.val).eval (x i))
  have he : (vandermonde x).det = A.det :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x (fun j => p j.val)
      (fun j => (p_properties _).1) (fun j => (p_properties _).2)
  rw [he]
  refine (abs_det_le_prod_euclidean_row_norm A).trans ?_
  calc
    _ ≤ ∏ _i : Fin n, 2 * Real.sqrt n := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i _
      let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A i)
      change ‖v‖ ≤ _
      have hsq : ‖v‖ ^ 2 ≤ ∑ _j : Fin n, (4:ℝ) := by
        rw [EuclideanSpace.real_norm_sq_eq]
        apply sum_le_sum
        intro j _
        change ((p j.val).eval (x i)) ^ 2 ≤ 4
        obtain ⟨h₁,h₂⟩ := abs_le.mp (p_bound j.val _ (hx i))
        nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - (p j.val).eval (x i))
          (by linarith : 0 ≤ 2 + (p j.val).eval (x i))]
      simp at hsq
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n:ℝ), norm_nonneg v]
    _ = _ := by simp

lemma projectNorm (w d : ℂ) (hw : ‖w‖ = 1) :
    ‖d + w^2 * conj d‖ = |2 * (conj w * d).re| := by
  have hwc : w * conj w = 1 := by simp [Complex.mul_conj', hw]
  have hid : d + w^2 * conj d = w * (↑(2 * (conj w * d).re) : ℂ) := by
    rw [← Complex.add_conj, map_mul]
    simp only [starRingEnd_apply, star_star] at *
    linear_combination -d * hwc
  rw [hid, norm_mul, hw, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma detBound {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i j, ‖z i - z j‖ ≤ 2) :
    ‖(vandermonde z).det‖ ≤ (2 * Real.sqrt n)^n := by
  classical
  cases n with
  | zero => simp
  | succ m =>
    let F := fun w : ℂ => ∏ i : Fin (m+1), ∏ j ∈ Ioi i,
      (z j - z i + w^2 * conj (z j - z i))
    have hF : Differentiable ℂ F := by dsimp [F]; fun_prop
    have hb : ∀ w ∈ frontier (Metric.ball (0:ℂ) 1), ‖F w‖ ≤ (2 * Real.sqrt (m+1))^(m+1) := by
      intro w hw
      have hw' : ‖w‖ = 1 := by simpa [frontier_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0),
        Metric.mem_sphere] using hw
      let r := fun i => 2 * (conj w * z i).re
      obtain ⟨a, _, ha⟩ := exists_min_image (univ : Finset (Fin (m+1))) r univ_nonempty
      let x := fun i => r i - (r a + 2)
      have hx : ∀ i, |x i| ≤ 2 := by
        intro i
        have hr : (conj w * (z i - z a)).re ≤ 2 := calc
          _ ≤ ‖conj w * (z i - z a)‖ := Complex.re_le_norm _
          _ = ‖z i - z a‖ := by simp [hw']
          _ ≤ 2 := hz i a
        rw [mul_sub, Complex.sub_re] at hr
        have hmin := ha i (mem_univ _)
        dsimp [x, r] at hmin ⊢
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      calc
        ‖F w‖ = |(vandermonde x).det| := by
          simp only [F, Matrix.det_vandermonde, norm_prod, Finset.abs_prod]
          apply prod_congr rfl
          intro i _
          apply prod_congr rfl
          intro j _
          rw [projectNorm w _ hw']
          congr 1
          simp only [x, r, mul_sub, Complex.sub_re]
          ring
        _ ≤ _ := by simpa using realVander x hx
    have hzero := Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball (x := (0:ℂ)) (r := (1:ℝ))) hF.diffContOnCl hb
      (subset_closure (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1)))
    simpa [F, Matrix.det_vandermonde] using hzero

lemma deltaSq {n : ℕ} (z : Fin n → ℂ) :
    OMA.S_erdos_1045.delta z = ‖(vandermonde z).det‖ ^ 2 := by
  classical
  rw [OMA.S_erdos_1045.delta, Matrix.det_vandermonde]
  simp only [norm_prod]
  have hsplit (i : Fin n) : univ.erase i = Iio i ∪ Ioi i := by
    ext j
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]
    exact ne_iff_lt_or_gt
  have hd (i : Fin n) : Disjoint (Iio i) (Ioi i) := by
    exact disjoint_left.mpr fun j hj hk => (asymm (mem_Iio.mp hj)) (mem_Ioi.mp hk)
  simp_rw [hsplit, prod_union (hd _)]
  rw [Finset.prod_mul_distrib, pow_two]
  congr 1
  · apply Finset.prod_comm' (fun i j => by simp)
  · apply prod_congr rfl
    intro i _
    apply prod_congr rfl
    intro j _
    exact norm_sub_rev _ _

end OMA.Diameter

theorem OMA.solution : type_of% @OMA.S_erdos_1045.main := by
  refine ⟨4, by norm_num, ?_⟩
  intro n z hz
  rw [OMA.Diameter.deltaSq]
  calc
    _ ≤ ((2 * Real.sqrt n)^n)^2 := pow_le_pow_left₀ (norm_nonneg _) (OMA.Diameter.detBound z hz) 2
    _ = 4^n * (n:ℝ)^n := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_pow]
      norm_num
