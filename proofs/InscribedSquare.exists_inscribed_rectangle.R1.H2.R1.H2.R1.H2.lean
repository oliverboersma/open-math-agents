import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1_H2_R1
import Mathlib

/-! An odd complex-valued function on the two-sphere cannot be nowhere zero. -/

open Set Metric Complex

namespace HemisphereLog

private noncomputable def v (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * z.re / (1 + normSq z), 2 * z.im / (1 + normSq z),
    (1 - normSq z) / (1 + normSq z)]

private theorem norm_v (z : ℂ) : ‖v z‖ = 1 := by
  have hd : 0 < 1 + normSq z := by linarith [normSq_nonneg z]
  have hsq : ‖v z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change (2 * z.re / (1 + normSq z))^2 +
      (2 * z.im / (1 + normSq z))^2 + ((1 - normSq z) / (1 + normSq z))^2 = 1
    field_simp
    rw [Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (v z)]

private noncomputable def spherePoint (z : ℂ) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨v z, by simp [norm_v]⟩

private theorem point_continuous : Continuous spherePoint := by
  have hd : ∀ z : ℂ, 1 + normSq z ≠ 0 := fun z =>
    (by linarith [normSq_nonneg z] : 0 < 1 + normSq z).ne'
  apply Continuous.subtype_mk
  unfold v
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop (disch := exact hd _)

private theorem equator (z : ℂ) (hz : normSq z = 1) :
    (spherePoint (-z)).val = -(spherePoint z).val := by
  change v (-z) = -(v z)
  ext i
  fin_cases i <;>
    simp [v, Complex.normSq_neg, hz, neg_div, mul_neg]

theorem odd_zero (f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ)
    (hc : Continuous f) (odd : ∀ x y, x.val = -y.val → f x = -f y) :
    ∃ x, f x = 0 := by
  by_contra! hnone
  let g : ℂ → ℂ := f ∘ spherePoint
  have hg : Continuous g := hc.comp point_continuous
  have hnonzero (z : ℂ) : g z ≠ 0 := hnone (spherePoint z)
  have hsc : IsSimplyConnected (univ : Set ℂ) := by
    change SimplyConnectedSpace (univ : Set ℂ)
    let _ : ContractibleSpace (univ : Set ℂ) :=
      (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace univ_nonempty
    infer_instance
  obtain ⟨L, hL, hLift⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ
    hg.continuousOn (by simpa [Set.mem_image] using hnonzero)
  have hLc : Continuous L := continuousOn_univ.mp hL
  have he (z : ℂ) : Complex.exp (L z) = g z := hLift (mem_univ z)
  let ζ (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have hζc : Continuous ζ := by unfold ζ; fun_prop
  have hζ (t : ℝ) : normSq (ζ t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hex (t : ℝ) : Complex.exp (L (-ζ t) - L (ζ t)) = -1 := by
    have h := odd (spherePoint (-ζ t)) (spherePoint (ζ t)) (equator _ (hζ t))
    rw [Complex.exp_sub, he, he]
    change f (spherePoint (-ζ t)) / g (ζ t) = -1
    rw [h]
    change -g (ζ t) / g (ζ t) = -1
    rw [neg_div, div_self (hnonzero _)]
  let d (t : ℝ) : ℝ := (L (-ζ t) - L (ζ t)).im
  have hd : Continuous d := Complex.continuous_im.comp ((hLc.comp hζc.neg).sub (hLc.comp hζc))
  have h0 : ζ 0 = 1 := by simp [ζ]
  have hπ : ζ Real.pi = -1 := Complex.exp_pi_mul_I
  have flip : d Real.pi = -d 0 := by
    simp only [d, hπ, h0, neg_neg, Complex.sub_im]
    ring
  have hz : ∃ t, d t = 0 := by
    by_cases hh : d 0 ≤ 0
    · exact intermediate_value_univ 0 Real.pi hd (show (0 : ℝ) ∈ Icc (d 0) (d Real.pi) from
        ⟨hh, by rw [flip]; linarith⟩)
    · exact intermediate_value_univ Real.pi 0 hd (show (0 : ℝ) ∈ Icc (d Real.pi) (d 0) from
        ⟨by rw [flip]; linarith, by linarith⟩)
  obtain ⟨t, ht⟩ := hz
  have h := congrArg Complex.re (hex t)
  rw [Complex.exp_re, show (L (-ζ t) - L (ζ t)).im = 0 from ht,
    Real.cos_zero, mul_one, Complex.neg_re, Complex.one_re] at h
  linarith [Real.exp_pos (L (-ζ t) - L (ζ t)).re]

end HemisphereLog

/-- An odd map on the sphere must vanish by lifting from the stereographic plane. -/
theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1_H2_R1.H2 := HemisphereLog.odd_zero