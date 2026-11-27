import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1

/-! Port of Jacob Parish (Plasma AI), plasma-ai/erdos-173 at 4a368a652753, Apache-2.0.
The ODE, Taylor estimates and rational sample values prove the two-scale Bessel bound. -/
-- Credit: @marcusbuffett

namespace ParishBessel

open Real


noncomputable def besselJ0 (x : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)


noncomputable def besselJ0Deriv (x : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ))


noncomputable def besselJ0Deriv2 (x : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ))


theorem abs_besselJ0_le_one (x : ℝ) : |besselJ0 x| ≤ 1 :=
  OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1.abs_besselJ0_le_one x

theorem abs_besselJ0Deriv_le_one (x : ℝ) : |besselJ0Deriv x| ≤ 1 := by
  rw [besselJ0Deriv, abs_neg]
  refine OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1.abs_inv_two_pi_mul_integral_le_one fun θ => ?_
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (abs_sin_le_one _)


theorem hasDerivAt_besselJ0 (x : ℝ) : HasDerivAt besselJ0 (besselJ0Deriv x) x :=
  OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1.hasDerivAt_besselJ0 x

theorem hasDerivAt_besselJ0Deriv (x : ℝ) : HasDerivAt besselJ0Deriv (besselJ0Deriv2 x) x := by
  exact ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => cos θ * sin (x * cos θ)) (F' := fun x θ => cos θ ^ 2 * cos (x * cos θ))
    (μ := MeasureTheory.volume) (x₀ := x) (bound := fun _ => 1) (a := 0) (b := 2 * π)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous fun θ => cos θ * sin (x * cos θ)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => cos θ * sin (x * cos θ)).intervalIntegrable _ _)
    (by fun_prop : Continuous fun θ => cos θ ^ 2 * cos (x * cos θ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ y _ => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _)
        (pow_le_one₀ (abs_nonneg _) (abs_cos_le_one _))).trans (abs_cos_le_one _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ y _ => by
      convert! ((hasDerivAt_mul_const (cos θ)).sin.const_mul (cos θ) :
        HasDerivAt (fun y => cos θ * sin (y * cos θ)) _ y) using 1
      ring)).2.const_mul (2 * π)⁻¹).neg


theorem continuous_besselJ0 : Continuous besselJ0 :=
  OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1.continuous_besselJ0


theorem besselJ0_ode (x : ℝ) : x * besselJ0Deriv2 x + besselJ0Deriv x + x * besselJ0 x = 0 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ => sin θ * sin (x * cos θ))
      (cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) θ := fun θ _ => by
    convert! (hasDerivAt_sin θ).mul ((hasDerivAt_cos θ).const_mul x).sin using 1
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun θ =>
      cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)).intervalIntegrable _ _)
  simp only [sin_two_pi, sin_zero, zero_mul, sub_zero] at hint
  have hsplit : (∫ θ in (0 : ℝ)..2 * π,
      cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) =
      (∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ)) -
        x * ((∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)) -
          ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)) := by
    have hcongr : (fun θ => cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) =
        fun θ => cos θ * sin (x * cos θ) -
          x * (cos (x * cos θ) - cos θ ^ 2 * cos (x * cos θ)) := by
      ext θ
      rw [sin_sq]
      ring
    rw [hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub] <;> exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsplit] at hint
  simp only [besselJ0, besselJ0Deriv, besselJ0Deriv2]
  linear_combination (-(2 * π)⁻¹) * hint

end ParishBessel

namespace ParishBessel

open Real Finset


noncomputable def cosTaylor (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ)


noncomputable def sinTaylor (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)


lemma hasDerivAt_pow_div_factorial (m : ℕ) (y : ℝ) :
    HasDerivAt (fun y => y ^ (m + 1) / ((m + 1).factorial : ℝ))
      (y ^ m / (m.factorial : ℝ)) y := by
  convert! (hasDerivAt_pow (m + 1) y).div_const ((m + 1).factorial : ℝ) using 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring


lemma hasDerivAt_sinTaylor (N : ℕ) (y : ℝ) :
    HasDerivAt (sinTaylor N) (cosTaylor N y) y := by
  have h := HasDerivAt.fun_sum (u := range N) (x := y)
    (A := fun k y => (-1) ^ k * (y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    (A' := fun k => (-1) ^ k * (y ^ (2 * k) / ((2 * k).factorial : ℝ)))
    fun k _ => (hasDerivAt_pow_div_factorial (2 * k) y).const_mul _
  convert! h using 1
  · ext y
    simp only [sinTaylor, mul_div_assoc]
  · simp only [cosTaylor, mul_div_assoc]


lemma hasDerivAt_cosTaylor_succ (N : ℕ) (y : ℝ) :
    HasDerivAt (cosTaylor (N + 1)) (-sinTaylor N y) y := by
  have h := (HasDerivAt.fun_sum (u := range N) (x := y)
    (A := fun k y => (-1) ^ (k + 1) * (y ^ (2 * k + 1 + 1) / ((2 * k + 1 + 1).factorial : ℝ)))
    (A' := fun k => (-1) ^ (k + 1) * (y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    fun k _ => (hasDerivAt_pow_div_factorial (2 * k + 1) y).const_mul _).add_const 1
  convert! h using 1
  · ext y
    simp only [cosTaylor, sum_range_succ', mul_div_assoc]
    norm_num [mul_add, pow_succ]
  · simp only [sinTaylor, ← sum_neg_distrib, mul_div_assoc, pow_succ]
    ring_nf


lemma abs_le_of_abs_deriv_le {f f' : ℝ → ℝ} {m : ℕ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hb : ∀ t, |f' t| ≤ |t| ^ m / (m.factorial : ℝ)) (y : ℝ) :
    |f y| ≤ |y| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  wlog hy : 0 ≤ y generalizing f f' y
  · have h := this (f := fun t => f (-t)) (f' := fun t => -f' (-t))
      (fun t => by
        have := (hf (-t)).comp t (hasDerivAt_neg t)
        simpa [Function.comp_def] using this) (by simpa using h0)
      (fun t => by simpa [abs_neg] using hb (-t)) (-y) (by linarith)
    simpa [abs_neg] using h
  set g : ℝ → ℝ := fun y => y ^ (m + 1) / ((m + 1).factorial : ℝ)
  have hg := hasDerivAt_pow_div_factorial m
  have hmono (s : ℝ) (hs : s = 1 ∨ s = -1) : MonotoneOn (fun t => g t + s * f t) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => ((hg t).add ((hf t).const_mul s)).continuousAt.continuousWithinAt)
      (fun t _ => ((hg t).add ((hf t).const_mul s)).hasDerivWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    have hb' := abs_le.mp (hb t)
    rw [abs_of_pos ht] at hb'
    rcases hs with rfl | rfl <;> linarith
  have h1 := hmono 1 (Or.inl rfl) Set.self_mem_Ici hy hy
  have h2 := hmono (-1) (Or.inr rfl) Set.self_mem_Ici hy hy
  simp only [g, h0, mul_zero, add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, zero_div] at h1 h2
  rw [abs_of_nonneg hy, abs_le]
  constructor <;> linarith


lemma abs_sin_sub_sinTaylor_le_of_cos {N : ℕ}
    (hc : ∀ y, |cos y - cosTaylor N y| ≤ |y| ^ (2 * N) / ((2 * N).factorial : ℝ)) (y : ℝ) :
    |sin y - sinTaylor N y| ≤ |y| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) :=
  abs_le_of_abs_deriv_le (fun t => (hasDerivAt_sin t).sub (hasDerivAt_sinTaylor N t))
    (by simp [sinTaylor]) hc y


theorem abs_cos_sub_cosTaylor_le (N : ℕ) (y : ℝ) :
    |cos y - cosTaylor N y| ≤ |y| ^ (2 * N) / ((2 * N).factorial : ℝ) := by
  induction N generalizing y with
  | zero => simpa [cosTaylor] using abs_cos_le_one y
  | succ N ih =>
    have h := abs_le_of_abs_deriv_le (m := 2 * N + 1)
      (fun t => (hasDerivAt_cos t).sub (hasDerivAt_cosTaylor_succ N t))
      (by simp [cosTaylor, sum_range_succ']) (fun t => ?_) y
    · simpa [mul_add] using h
    · rw [show -sin t - -sinTaylor N t = -(sin t - sinTaylor N t) by ring, abs_neg]
      exact abs_sin_sub_sinTaylor_le_of_cos ih t


theorem abs_sin_sub_sinTaylor_le (N : ℕ) (y : ℝ) :
    |sin y - sinTaylor N y| ≤ |y| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) :=
  abs_sin_sub_sinTaylor_le_of_cos (abs_cos_sub_cosTaylor_le N) y

end ParishBessel

namespace ParishBessel

open Real Finset


noncomputable def j0Partial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * (x / 2) ^ (2 * k) / (k.factorial : ℝ) ^ 2


noncomputable def j1Partial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range N,
    (-1) ^ k * (x / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))


lemma integral_cos_pow_two_mul (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, cos θ ^ (2 * k) =
      2 * π * ((2 * k).factorial : ℝ) / (4 ^ k * (k.factorial : ℝ) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_cos_pow, ih]
    simp only [sin_zero, sin_two_pi, mul_zero, sub_zero, zero_div, zero_add]
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    push_cast
    field_simp
    ring


lemma integral_even_term (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, y ^ (2 * k) / ((2 * k).factorial : ℝ) * cos θ ^ (2 * k) =
      2 * π * ((y / 2) ^ (2 * k) / (k.factorial : ℝ) ^ 2) := by
  rw [intervalIntegral.integral_const_mul, integral_cos_pow_two_mul, div_pow, pow_mul,
    pow_mul 2]
  field_simp
  norm_num


lemma integral_odd_term (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π,
      y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * cos θ ^ (2 * (k + 1)) =
      2 * π * ((y / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))) := by
  have h2 : (2 : ℝ) ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [intervalIntegral.integral_const_mul, integral_cos_pow_two_mul,
    show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ k, div_pow, h2, pow_succ (4 : ℝ)]
  push_cast
  field_simp
  ring


lemma continuous_cosTaylor (N : ℕ) : Continuous (cosTaylor N) := by
  unfold cosTaylor
  fun_prop


lemma continuous_sinTaylor (N : ℕ) : Continuous (sinTaylor N) := by
  unfold sinTaylor
  fun_prop


lemma integral_cosTaylor (N : ℕ) (x : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cosTaylor N (x * cos θ) = 2 * π * j0Partial N x := by
  simp only [cosTaylor, j0Partial, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun θ =>
      (-1) ^ k * (x * cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)).intervalIntegrable _ _]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun θ => (-1) ^ k * (x * cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)) =
      fun θ => (-1) ^ k * (x ^ (2 * k) / ((2 * k).factorial : ℝ) * cos θ ^ (2 * k)) := by
    ext θ
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_even_term]
  ring


lemma integral_cos_mul_sinTaylor (N : ℕ) (x : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cos θ * sinTaylor N (x * cos θ) = 2 * π * j1Partial N x := by
  simp only [sinTaylor, j1Partial, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun θ =>
      cos θ * ((-1) ^ k * (x * cos θ) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ))).intervalIntegrable _ _]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun θ => cos θ * ((-1) ^ k * (x * cos θ) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ))) = fun θ => (-1) ^ k *
        (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * cos θ ^ (2 * (k + 1))) := by
    ext θ
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_odd_term]
  ring


theorem abs_besselJ0_sub_j0Partial_le (N : ℕ) (x : ℝ) :
    |besselJ0 x - j0Partial N x| ≤ (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by
  have hπ := two_pi_pos
  have hc := continuous_cosTaylor N
  have hdiff : besselJ0 x - j0Partial N x = (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ)) := by
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun θ =>
      cos (x * cos θ)).intervalIntegrable _ _) ((by fun_prop : Continuous fun θ =>
        cosTaylor N (x * cos θ)).intervalIntegrable _ _), integral_cosTaylor, besselJ0,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
  have hle : |∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ))| ≤
      ∫ θ in (0 : ℝ)..2 * π, x ^ (2 * N) / ((2 * N).factorial : ℝ) * cos θ ^ (2 * N) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos (x * cos θ) - cosTaylor N (x * cos θ)|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ =>
        x ^ (2 * N) / ((2 * N).factorial : ℝ) * cos θ ^ (2 * N)).intervalIntegrable _ _
    · have h := abs_cos_sub_cosTaylor_le N (x * cos θ)
      rw [(even_two_mul N).pow_abs, mul_pow] at h
      exact h.trans_eq (by ring)
  rw [integral_even_term] at hle
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ))|
      ≤ (2 * π)⁻¹ * (2 * π * ((x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2)) := by gcongr
    _ = (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by field_simp


theorem abs_besselJ0Deriv_add_j1Partial_le (N : ℕ) (x : ℝ) :
    |besselJ0Deriv x + j1Partial N x| ≤
      |x / 2| ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)) := by
  have hπ := two_pi_pos
  have hs := continuous_sinTaylor N
  have hdiff : besselJ0Deriv x + j1Partial N x = -((2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun θ =>
      cos θ * sin (x * cos θ)).intervalIntegrable _ _) ((by fun_prop : Continuous fun θ =>
        cos θ * sinTaylor N (x * cos θ)).intervalIntegrable _ _), integral_cos_mul_sinTaylor,
      besselJ0Deriv, mul_sub, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
    ring
  have hle : |∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))| ≤
      ∫ θ in (0 : ℝ)..2 * π,
        |x| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) * cos θ ^ (2 * (N + 1)) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ =>
        |x| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) * cos θ ^ (2 * (N + 1))).intervalIntegrable
          _ _
    · have h := abs_sin_sub_sinTaylor_le N (x * cos θ)
      have hcos : cos θ ^ (2 * (N + 1)) = |cos θ| * |cos θ| ^ (2 * N + 1) := by
        rw [← pow_succ', show 2 * N + 1 + 1 = 2 * (N + 1) by ring,
          (even_two_mul (N + 1)).pow_abs]
      rw [hcos, abs_mul (cos θ)]
      calc |cos θ| * |sin (x * cos θ) - sinTaylor N (x * cos θ)|
          ≤ |cos θ| * (|x| ^ (2 * N + 1) * |cos θ| ^ (2 * N + 1) /
            ((2 * N + 1).factorial : ℝ)) := by gcongr; rwa [abs_mul, mul_pow] at h
        _ = _ := by ring
  rw [integral_odd_term] at hle
  rw [hdiff, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hπ), abs_div, abs_two]
  calc (2 * π)⁻¹ *
        |∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))|
      ≤ (2 * π)⁻¹ * (2 * π * ((|x| / 2) ^ (2 * N + 1) /
        ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)))) := by gcongr
    _ = _ := by field_simp

end ParishBessel

namespace ParishBessel

open Real Set


theorem abs_besselJ0Deriv2_le_half (x : ℝ) : |besselJ0Deriv2 x| ≤ 1 / 2 := by
  have hπ := two_pi_pos
  have hle : |∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)| ≤
      ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos θ ^ 2 * cos (x * cos θ)|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ => cos θ ^ 2).intervalIntegrable _ _
    · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (abs_cos_le_one _)
  rw [integral_cos_sq] at hle
  simp only [cos_two_pi, sin_two_pi, cos_zero, sin_zero, mul_zero, sub_zero,
    zero_add] at hle
  rw [besselJ0Deriv2, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)|
      ≤ (2 * π)⁻¹ * ((2 * π) / 2) := by gcongr
    _ = 1 / 2 := by field_simp


theorem abs_besselJ0Deriv_sub_le (s t : ℝ) :
    |besselJ0Deriv t - besselJ0Deriv s| ≤ |t - s| / 2 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := besselJ0Deriv) (s := univ) (x := s) (y := t) (C := 1 / 2)
    (fun x _ => (hasDerivAt_besselJ0Deriv x).hasDerivWithinAt)
    (fun x _ => abs_besselJ0Deriv2_le_half x) convex_univ (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs] at h
  linarith


theorem abs_besselJ0_sub_le (s t : ℝ) : |besselJ0 t - besselJ0 s| ≤ |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := besselJ0) (s := univ) (x := s) (y := t) (C := 1)
    (fun x _ => (hasDerivAt_besselJ0 x).hasDerivWithinAt)
    (fun x _ => abs_besselJ0Deriv_le_one x) convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs, one_mul] using h


theorem besselJ0Deriv_nonpos_of_le_pi {t : ℝ} (ht : 0 ≤ t) (htπ : t ≤ π) :
    besselJ0Deriv t ≤ 0 := by
  rw [besselJ0Deriv, neg_nonpos]
  refine mul_nonneg (inv_nonneg.mpr two_pi_pos.le)
    (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => ?_)
  have h1 := neg_one_le_cos θ
  have h2 := cos_le_one θ
  rcases le_or_gt 0 (cos θ) with hc | hc
  · exact mul_nonneg hc (sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ht hc) (by nlinarith))
  · exact mul_nonneg_of_nonpos_of_nonpos hc.le
      (sin_nonpos_of_nonpos_of_neg_pi_le (mul_nonpos_of_nonneg_of_nonpos ht hc.le)
        (by nlinarith))


theorem antitoneOn_besselJ0 {a b : ℝ} (h : ∀ t ∈ Icc a b, besselJ0Deriv t ≤ 0) :
    AntitoneOn besselJ0 (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) continuous_besselJ0.continuousOn
    (fun t _ => (hasDerivAt_besselJ0 t).hasDerivWithinAt) fun t ht => h t (interior_subset ht)


theorem monotoneOn_besselJ0 {a b : ℝ} (h : ∀ t ∈ Icc a b, 0 ≤ besselJ0Deriv t) :
    MonotoneOn besselJ0 (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) continuous_besselJ0.continuousOn
    (fun t _ => (hasDerivAt_besselJ0 t).hasDerivWithinAt) fun t ht => h t (interior_subset ht)


noncomputable def besselEnergy (t : ℝ) : ℝ :=
  besselJ0 t ^ 2 + besselJ0Deriv t ^ 2


theorem antitoneOn_besselEnergy {s : ℝ} (hs : 0 < s) : AntitoneOn besselEnergy (Ici s) := by
  have hd (t : ℝ) : HasDerivAt besselEnergy
      (2 * besselJ0 t * besselJ0Deriv t + 2 * besselJ0Deriv t * besselJ0Deriv2 t) t := by
    convert! ((hasDerivAt_besselJ0 t).pow 2).add ((hasDerivAt_besselJ0Deriv t).pow 2) using 1
    norm_num
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici s)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
    fun t ht => ?_
  rw [interior_Ici] at ht
  have ht0 : 0 < t := hs.trans ht
  have key : t * (2 * besselJ0 t * besselJ0Deriv t + 2 * besselJ0Deriv t * besselJ0Deriv2 t) =
      -2 * besselJ0Deriv t ^ 2 := by
    linear_combination (2 * besselJ0Deriv t) * besselJ0_ode t
  nlinarith [sq_nonneg (besselJ0Deriv t)]


theorem sq_besselJ0_le_energy {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    besselJ0 t ^ 2 ≤ besselJ0 s ^ 2 + besselJ0Deriv s ^ 2 := by
  have h := antitoneOn_besselEnergy hs self_mem_Ici hst hst
  simp only [besselEnergy] at h
  nlinarith [sq_nonneg (besselJ0Deriv t)]

end ParishBessel

namespace ParishBessel

open Finset


lemma le_besselJ0_of_partial {N : ℕ} {x c : ℝ}
    (h : c ≤ j0Partial N x - (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2) : c ≤ besselJ0 x := by
  linarith [(abs_le.mp (abs_besselJ0_sub_j0Partial_le N x)).1]


lemma besselJ0_le_of_partial {N : ℕ} {x c : ℝ}
    (h : j0Partial N x + (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 ≤ c) : besselJ0 x ≤ c := by
  linarith [(abs_le.mp (abs_besselJ0_sub_j0Partial_le N x)).2]


lemma le_besselJ0Deriv_of_partial {N : ℕ} {x c : ℝ} (hx : 0 ≤ x)
    (h : c ≤ -j1Partial N x -
      (x / 2) ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ))) :
    c ≤ besselJ0Deriv x := by
  have h' := (abs_le.mp (abs_besselJ0Deriv_add_j1Partial_le N x)).1
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h'
  linarith


lemma besselJ0Deriv_le_of_partial {N : ℕ} {x c : ℝ} (hx : 0 ≤ x)
    (h : -j1Partial N x +
      (x / 2) ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)) ≤ c) :
    besselJ0Deriv x ≤ c := by
  have h' := (abs_le.mp (abs_besselJ0Deriv_add_j1Partial_le N x)).2
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h'
  linarith





theorem besselJ0_three : -261 / 1000 ≤ besselJ0 3 :=
  le_besselJ0_of_partial (N := 8) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0Deriv_three : besselJ0Deriv 3 ≤ -33 / 100 :=
  besselJ0Deriv_le_of_partial (N := 8) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0_sixteen_fifths : -321 / 1000 ≤ besselJ0 (16 / 5) :=
  le_besselJ0_of_partial (N := 9) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0Deriv_seven_halves : besselJ0Deriv (7 / 2) ≤ -13 / 100 :=
  besselJ0Deriv_le_of_partial (N := 9) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0_fifteen_quarters :
    -4015 / 10000 ≤ besselJ0 (15 / 4) ∧ besselJ0 (15 / 4) ≤ 0 :=
  ⟨le_besselJ0_of_partial (N := 9) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num),
    besselJ0_le_of_partial (N := 9) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)⟩


theorem besselJ0Deriv_fifteen_quarters :
    -334 / 10000 ≤ besselJ0Deriv (15 / 4) ∧ besselJ0Deriv (15 / 4) ≤ 334 / 10000 :=
  ⟨le_besselJ0Deriv_of_partial (N := 9) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num),
    besselJ0Deriv_le_of_partial (N := 9) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)⟩


theorem besselJ0_nine_halves : -321 / 1000 ≤ besselJ0 (9 / 2) :=
  le_besselJ0_of_partial (N := 10) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0Deriv_nine_halves : 23 / 100 ≤ besselJ0Deriv (9 / 2) :=
  le_besselJ0Deriv_of_partial (N := 10) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0_twenty_four_fifths : -241 / 1000 ≤ besselJ0 (24 / 5) :=
  le_besselJ0_of_partial (N := 11) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0Deriv_eleven_halves : 34 / 100 ≤ besselJ0Deriv (11 / 2) :=
  le_besselJ0Deriv_of_partial (N := 12) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0_thirteen_halves : 1 / 4 ≤ besselJ0 (13 / 2) :=
  le_besselJ0_of_partial (N := 13) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0_fifteen_halves : 1 / 4 ≤ besselJ0 (15 / 2) :=
  le_besselJ0_of_partial (N := 15) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0Deriv_seventeen_halves : besselJ0Deriv (17 / 2) ≤ -27 / 100 :=
  besselJ0Deriv_le_of_partial (N := 16) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0Deriv_nine : besselJ0Deriv 9 ≤ -24 / 100 :=
  besselJ0Deriv_le_of_partial (N := 17) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)


theorem besselJ0_forty_six_fifths :
    -137 / 1000 ≤ besselJ0 (46 / 5) ∧ besselJ0 (46 / 5) ≤ 0 :=
  ⟨le_besselJ0_of_partial (N := 17) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num),
    besselJ0_le_of_partial (N := 17) (by simp only [j0Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)⟩


theorem besselJ0Deriv_forty_six_fifths :
    -218 / 1000 ≤ besselJ0Deriv (46 / 5) ∧ besselJ0Deriv (46 / 5) ≤ 218 / 1000 :=
  ⟨le_besselJ0Deriv_of_partial (N := 17) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num),
    besselJ0Deriv_le_of_partial (N := 17) (by norm_num) (by simp only [j1Partial, sum_range_succ, sum_range_zero, Nat.factorial]; norm_num)⟩

end ParishBessel

namespace ParishBessel

open Real Set


lemma besselJ0Deriv_nonpos_of_near {p c t : ℝ} (hp : besselJ0Deriv p ≤ -c)
    (ht : |t - p| ≤ 2 * c) : besselJ0Deriv t ≤ 0 := by
  linarith [(abs_le.mp (abs_besselJ0Deriv_sub_le p t)).2]


lemma besselJ0Deriv_nonneg_of_near {p c t : ℝ} (hp : c ≤ besselJ0Deriv p)
    (ht : |t - p| ≤ 2 * c) : 0 ≤ besselJ0Deriv t := by
  linarith [(abs_le.mp (abs_besselJ0Deriv_sub_le p t)).1]


theorem antitoneOn_besselJ0_zero_fifteen_quarters :
    AntitoneOn besselJ0 (Icc 0 (15 / 4)) := by
  refine antitoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t 3 with h3 | h3
  · exact besselJ0Deriv_nonpos_of_le_pi ht.1 (h3.trans pi_gt_three.le)
  rcases le_or_gt t (18 / 5) with h4 | h4
  · exact besselJ0Deriv_nonpos_of_near (p := 3) (c := 33 / 100)
      (by linarith [besselJ0Deriv_three])
      (abs_le.mpr ⟨by linarith, by linarith⟩)
  · exact besselJ0Deriv_nonpos_of_near (p := 7 / 2) (c := 13 / 100)
      (by linarith [besselJ0Deriv_seven_halves])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)


theorem monotoneOn_besselJ0_nine_halves_sixty_one_tenths :
    MonotoneOn besselJ0 (Icc (9 / 2) (61 / 10)) := by
  refine monotoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t (49 / 10) with h | h
  · exact besselJ0Deriv_nonneg_of_near (p := 9 / 2) (c := 23 / 100)
      (by linarith [besselJ0Deriv_nine_halves])
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · exact besselJ0Deriv_nonneg_of_near (p := 11 / 2) (c := 34 / 100)
      (by linarith [besselJ0Deriv_eleven_halves])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)


theorem antitoneOn_besselJ0_eight_forty_six_fifths :
    AntitoneOn besselJ0 (Icc 8 (46 / 5)) := by
  refine antitoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t 9 with h | h
  · exact besselJ0Deriv_nonpos_of_near (p := 17 / 2) (c := 27 / 100)
      (by linarith [besselJ0Deriv_seventeen_halves])
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · exact besselJ0Deriv_nonpos_of_near (p := 9) (c := 24 / 100)
      (by linarith [besselJ0Deriv_nine])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)


lemma neg_le_besselJ0_of_energy {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (hc : 0 ≤ c)
    (hE : besselJ0 s ^ 2 + besselJ0Deriv s ^ 2 ≤ c ^ 2) : -c ≤ besselJ0 t :=
  (abs_le_of_sq_le_sq' ((sq_besselJ0_le_energy hs hst).trans hE) hc).1


theorem le_besselJ0_of_nonneg {t : ℝ} (ht : 0 ≤ t) : -403 / 1000 ≤ besselJ0 t := by
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_fifteen_quarters
  rcases le_or_gt t (15 / 4) with h | h
  · linarith [antitoneOn_besselJ0_zero_fifteen_quarters ⟨ht, h⟩ ⟨by norm_num, le_rfl⟩ h]
  · obtain ⟨hD₁, hD₂⟩ := besselJ0Deriv_fifteen_quarters
    refine le_trans (le_of_eq (by norm_num))
      (neg_le_besselJ0_of_energy (c := 403 / 1000) (by norm_num) h.le (by norm_num) ?_)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0 (15 / 4) + 4015 / 10000)
      (by linarith : (0 : ℝ) ≤ -besselJ0 (15 / 4)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0Deriv (15 / 4) + 334 / 10000)
      (by linarith : (0 : ℝ) ≤ 334 / 10000 - besselJ0Deriv (15 / 4))]


theorem le_besselJ0_of_le_three {t : ℝ} (ht : 0 ≤ t) (h3 : t ≤ 3) :
    -261 / 1000 ≤ besselJ0 t :=
  besselJ0_three.trans
    (antitoneOn_besselJ0_zero_fifteen_quarters ⟨ht, by linarith⟩ ⟨by norm_num, by norm_num⟩ h3)


theorem le_besselJ0_of_twenty_four_fifths_le {t : ℝ} (ht : 24 / 5 ≤ t) :
    -261 / 1000 ≤ besselJ0 t := by
  rcases le_or_gt t (61 / 10) with h | h
  · linarith [besselJ0_twenty_four_fifths, monotoneOn_besselJ0_nine_halves_sixty_one_tenths
      ⟨by norm_num, by norm_num⟩ ⟨by linarith, h⟩ ht]
  rcases le_or_gt t 7 with h7 | h7
  · have := (abs_le.mp (abs_besselJ0_sub_le (13 / 2) t)).1
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -(1 / 2) ≤ t - 13 / 2 ∧ t - 13 / 2 ≤ 1 / 2)
    linarith [besselJ0_thirteen_halves]
  rcases le_or_gt t 8 with h8 | h8
  · have := (abs_le.mp (abs_besselJ0_sub_le (15 / 2) t)).1
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -(1 / 2) ≤ t - 15 / 2 ∧ t - 15 / 2 ≤ 1 / 2)
    linarith [besselJ0_fifteen_halves]
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_forty_six_fifths
  rcases le_or_gt t (46 / 5) with h9 | h9
  · linarith [antitoneOn_besselJ0_eight_forty_six_fifths ⟨h8.le, h9⟩ ⟨by norm_num, le_rfl⟩ h9]
  · obtain ⟨hD₁, hD₂⟩ := besselJ0Deriv_forty_six_fifths
    refine le_trans (le_of_eq (by norm_num))
      (neg_le_besselJ0_of_energy (c := 261 / 1000) (by norm_num) h9.le (by norm_num) ?_)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0 (46 / 5) + 137 / 1000)
      (by linarith : (0 : ℝ) ≤ -besselJ0 (46 / 5)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0Deriv (46 / 5) + 218 / 1000)
      (by linarith : (0 : ℝ) ≤ 218 / 1000 - besselJ0Deriv (46 / 5))]


theorem besselJ0_add_lower {x : ℝ} (hx : 3 / 2 ≤ x) {t : ℝ} (ht : 0 ≤ t) :
    -83 / 125 ≤ besselJ0 t + besselJ0 (x * t) := by
  have hxt : 3 / 2 * t ≤ x * t := mul_le_mul_of_nonneg_right hx ht
  have hs : 0 ≤ x * t := by linarith
  have hG₁ := le_besselJ0_of_nonneg ht
  have hG₂ := le_besselJ0_of_nonneg hs
  
  rcases le_or_gt t 3 with h | h₁
  · linarith [le_besselJ0_of_le_three ht h]
  rcases le_or_gt (24 / 5) t with h | h₂
  · linarith [le_besselJ0_of_twenty_four_fifths_le h]
  rcases le_or_gt (x * t) 3 with h | h₃
  · linarith [le_besselJ0_of_le_three hs h]
  rcases le_or_gt (24 / 5) (x * t) with h | h₄
  · linarith [le_besselJ0_of_twenty_four_fifths_le h]
  
  have hJ₁ := antitoneOn_besselJ0_zero_fifteen_quarters ⟨by linarith, by linarith⟩
    ⟨by norm_num, by norm_num⟩ (by linarith : t ≤ 16 / 5)
  have hJ₂ := monotoneOn_besselJ0_nine_halves_sixty_one_tenths ⟨le_rfl, by norm_num⟩
    ⟨by linarith, by linarith⟩ (by linarith : 9 / 2 ≤ x * t)
  linarith [besselJ0_sixteen_fifths, besselJ0_nine_halves]

end ParishBessel

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1.H1 := fun _ hx _ ht => ParishBessel.besselJ0_add_lower hx ht
