import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1

-- Reduction WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1.H2.R1 of step WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1.H2
-- Credit: @carterleffen

/-!
The target is modularity of every elliptic curve over ℚ: a weight-two cusp form for some
Γ₀(N) whose q-expansion coefficients are the coefficients a_n of the registry L-series.
This file proves it from two statements about Dirichlet series, by Hecke's converse argument.
Neither hypothesis mentions a modular form, the upper half-plane or a slash action.

Write Λ(r, s) = (2π)^(-s) Γ(s) ∑ a_n e(n r) n^(-s) for the completed additive twist at r.

H1 (analytic continuation). The Dirichlet series ∑ a_n n^(-s) converges absolutely on
   Re s > 3/2, and for every rational r the function Λ(r, ·), defined there by the series,
   extends to an entire function that is bounded on the strip 0 ≤ Re s ≤ 2.
H2 (functional equations). There is one level N ≥ 1 such that for all integers A, B, C, D with
   AD - BC = 1, N ∣ C and C ≠ 0, any entire extensions L₁ of Λ(-D/C, ·) and L₂ of Λ(A/C, ·)
   satisfy L₁(s) = -(C²)^(1 - s) L₂(2 - s).

The first conjunct of H1 is hypothesis H1 of the parent reduction
WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1.

Proof of main. Put f(τ) = ∑ a_n exp(2πinτ) and K_r(y) = f(r + iy). Absolute convergence gives
|f(τ)| ≤ C (Im τ)^(-7/4), holomorphy of f, and Mellin K_r = Λ(r, ·) on Re s > 7/4. For
γ = [A, B; C, D] in Γ₀(N) with C ≠ 0, the function L₁ of H1 at r = -D/C equals Mellin K_(-D/C)
on Re s = 2 and, by H2, equals the Mellin transform of y ↦ -(Cy)^(-2) K_(A/C)(1/(C²y)) on
Re s = 0. Phragmén–Lindelöf turns boundedness in the strip into decay O(1/|Im s|), Cauchy's
theorem moves the line of Mellin inversion from Re s = 2 to Re s = 0, and the two kernels are
equal. This is f ∣[2] γ = f on the vertical line through -D/C, hence everywhere by the
identity theorem. For C = 0 the identity is the periodicity of f. The bound on f makes every
slash of f vanish at i∞, so f is a cusp form for Γ₀(N), and its q-expansion coefficients are
the a_n.

A reduction file may declare no definition besides the hypotheses, so each auxiliary function
(the q-series, the kernels, the completed twist) is introduced as the witness `foo_ex.choose`
of an existence lemma `foo_ex`, with defining equation `foo_ex.choose_spec`.

Provenance: assembled from the author's Lean development BSD.RationalModularAdditiveStrip,
BSD.RationalModularQSeries, BSD.RationalModularAdditiveKernel, BSD.RationalModularAdditiveMellin
and BSD.RationalModularAdditiveConverse, which carry no licence header of their own. The file
depends on Mathlib and on formal-conjectures, both under the Apache License 2.0, and is
contributed under the terms of this repository.
-/

namespace OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1_H2_R1

def H1 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    (∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (fun n : ℕ ↦ (E.LFunction n : ℂ)) s) ∧
    ∀ r : ℚ, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∃ M : ℝ, ∀ s : ℂ, s.re ∈ Set.Icc (0 : ℝ) 2 → ‖L s‖ ≤ M) ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        L s = ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
          LSeries (fun n : ℕ ↦ (E.LFunction n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * n * ((r : ℝ) : ℂ))) s

def H2 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    ∃ N : ℕ, 0 < N ∧ ∀ A B C D : ℤ, A * D - B * C = 1 → (N : ℤ) ∣ C → C ≠ 0 →
      ∀ L₁ L₂ : ℂ → ℂ, Differentiable ℂ L₁ → Differentiable ℂ L₂ →
        (∀ s : ℂ, 3 / 2 < s.re →
          L₁ s = ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
            LSeries (fun n : ℕ ↦ (E.LFunction n : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * n * ((-(D : ℝ) / (C : ℝ) : ℝ) : ℂ))) s) →
        (∀ s : ℂ, 3 / 2 < s.re →
          L₂ s = ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
            LSeries (fun n : ℕ ↦ (E.LFunction n : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * n * (((A : ℝ) / (C : ℝ) : ℝ) : ℂ))) s) →
        ∀ s : ℂ, L₁ s = -(((C : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s) * L₂ (2 - s)

/- ## Mellin uniqueness across a vertical strip -/

section Strip

open Complex Filter Set MeasureTheory
open scoped Topology Real

/- ### Contour shift -/

/-- **Shifting a vertical line of integration across a strip.** -/
theorem integral_vertical_eq_of_strip {h : ℂ → ℂ} {σ₂ σ₁ : ℝ} (hσ : σ₂ ≤ σ₁)
    (hc : ContinuousOn h (re ⁻¹' Icc σ₂ σ₁)) (hd : DifferentiableOn ℂ h (re ⁻¹' Ioo σ₂ σ₁))
    (h1 : Integrable fun t : ℝ ↦ h (σ₁ + t * I)) (h2 : Integrable fun t : ℝ ↦ h (σ₂ + t * I))
    (hdecay : ∃ C, ∀ s : ℂ, s.re ∈ Icc σ₂ σ₁ → ‖h s‖ * |s.im| ≤ C) :
    ∫ t : ℝ, h (σ₁ + t * I) = ∫ t : ℝ, h (σ₂ + t * I) := by
  obtain ⟨C, hC⟩ := hdecay
  -- the horizontal sides tend to zero
  have hH : ∀ u : ℝ → ℝ, (∀ T, |u T| = |T|) →
      Tendsto (fun T : ℝ ↦ ∫ x in σ₂..σ₁, h (x + (u T : ℂ) * I)) atTop (𝓝 0) := by
    intro u hu
    have hb : ∀ᶠ T : ℝ in atTop,
        ‖∫ x in σ₂..σ₁, h (x + (u T : ℂ) * I)‖ ≤ C / T * |σ₁ - σ₂| := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ ?_
      rw [uIoc_of_le hσ] at hx
      have hre : ((x : ℂ) + (u T : ℂ) * I).re = x := by simp
      have him : |((x : ℂ) + (u T : ℂ) * I).im| = T := by
        simp [hu T, abs_of_pos hT]
      have h3 := hC ((x : ℂ) + (u T : ℂ) * I) (by rw [hre]; exact ⟨hx.1.le, hx.2⟩)
      rw [him] at h3
      rwa [le_div_iff₀ hT]
    have ht : Tendsto (fun T : ℝ ↦ C / T * |σ₁ - σ₂|) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const |σ₁ - σ₂|
    exact squeeze_zero_norm' hb ht
  -- Cauchy's theorem on the rectangle
  have hkey : ∀ T : ℝ,
      I * (∫ t in (-T)..T, h (σ₁ + t * I)) - I * (∫ t in (-T)..T, h (σ₂ + t * I)) =
        (∫ x in σ₂..σ₁, h (x + (T : ℂ) * I)) - ∫ x in σ₂..σ₁, h (x + ((-T : ℝ) : ℂ) * I) := by
    intro T
    have Hc : ContinuousOn h (uIcc σ₂ σ₁ ×ℂ uIcc (-T) T) := by
      refine hc.mono fun s hs ↦ ?_
      have h3 : s.re ∈ uIcc σ₂ σ₁ := hs.1
      rwa [uIcc_of_le hσ] at h3
    have Hd : DifferentiableOn ℂ h
        (Ioo (min σ₂ σ₁) (max σ₂ σ₁) ×ℂ Ioo (min (-T) T) (max (-T) T)) := by
      refine hd.mono fun s hs ↦ ?_
      have h3 : s.re ∈ Ioo (min σ₂ σ₁) (max σ₂ σ₁) := hs.1
      rwa [min_eq_left hσ, max_eq_right hσ] at h3
    have h3 : (∫ x in σ₂..σ₁, h (x + ((-T : ℝ) : ℂ) * I)) -
        (∫ x in σ₂..σ₁, h (x + (T : ℂ) * I)) + I • (∫ t in (-T)..T, h (σ₁ + t * I)) -
        I • (∫ t in (-T)..T, h (σ₂ + t * I)) = 0 :=
      integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn h ⟨σ₂, -T⟩ ⟨σ₁, T⟩ Hc Hd
    simp only [smul_eq_mul] at h3
    linear_combination h3
  have hJ₁ : Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, h (σ₁ + t * I)) atTop
      (𝓝 (∫ t : ℝ, h (σ₁ + t * I))) :=
    intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  have hJ₂ : Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, h (σ₂ + t * I)) atTop
      (𝓝 (∫ t : ℝ, h (σ₂ + t * I))) :=
    intervalIntegral_tendsto_integral h2 tendsto_neg_atTop_atBot tendsto_id
  have hlim1 := (hJ₁.const_mul I).sub (hJ₂.const_mul I)
  have hlim2 : Tendsto (fun T : ℝ ↦
      I * (∫ t in (-T)..T, h (σ₁ + t * I)) - I * (∫ t in (-T)..T, h (σ₂ + t * I))) atTop
      (𝓝 0) := by
    have h3 := (hH (fun T ↦ T) fun _ ↦ rfl).sub (hH (fun T ↦ -T) fun T ↦ abs_neg T)
    rw [sub_zero] at h3
    exact h3.congr fun T ↦ (hkey T).symm
  have h4 := tendsto_nhds_unique hlim1 hlim2
  rw [← mul_sub] at h4
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 I_ne_zero
  · exact sub_eq_zero.mp h5

/- ### Mellin uniqueness -/

/-- `x ^ (-u) ≤ x ^ (-σ₁) + x ^ (-σ₂)` for `σ₂ ≤ u ≤ σ₁`. -/
theorem rpow_neg_le_add {x : ℝ} (hx : 0 < x) {σ₂ σ₁ u : ℝ} (h2 : σ₂ ≤ u) (h1 : u ≤ σ₁) :
    x ^ (-u) ≤ x ^ (-σ₁) + x ^ (-σ₂) := by
  have p1 : 0 < x ^ (-σ₁) := Real.rpow_pos_of_pos hx _
  have p2 : 0 < x ^ (-σ₂) := Real.rpow_pos_of_pos hx _
  rcases le_total 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg h2)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg h1)
    linarith

/-- **Mellin uniqueness across a strip.** If the Mellin transforms of `F` on `Re s = σ₁` and of
`G` on `Re s = σ₂` are the boundary values of one function `Λ`, continuous on the closed strip,
holomorphic inside, integrable on both lines, and with `‖Λ s‖ |Im s|` bounded on the strip,
then `F = G` at every point of continuity. -/
theorem eq_of_mellin_strip {F G : ℝ → ℂ} {Λ : ℂ → ℂ} {σ₂ σ₁ : ℝ} (hσ : σ₂ ≤ σ₁)
    (hF : MellinConvergent F σ₁) (hG : MellinConvergent G σ₂)
    (hc : ContinuousOn Λ (re ⁻¹' Icc σ₂ σ₁)) (hd : DifferentiableOn ℂ Λ (re ⁻¹' Ioo σ₂ σ₁))
    (hΛF : ∀ s : ℂ, s.re = σ₁ → Λ s = mellin F s) (hΛG : ∀ s : ℂ, s.re = σ₂ → Λ s = mellin G s)
    (h1 : VerticalIntegrable Λ σ₁) (h2 : VerticalIntegrable Λ σ₂)
    (hdecay : ∃ C, ∀ s : ℂ, s.re ∈ Icc σ₂ σ₁ → ‖Λ s‖ * |s.im| ≤ C)
    {x : ℝ} (hx : 0 < x) (hFx : ContinuousAt F x) (hGx : ContinuousAt G x) : F x = G x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have eF : (fun t : ℝ ↦ mellin F (σ₁ + t * I)) = fun t : ℝ ↦ Λ (σ₁ + t * I) :=
    funext fun t ↦ (hΛF _ (by simp)).symm
  have eG : (fun t : ℝ ↦ mellin G (σ₂ + t * I)) = fun t : ℝ ↦ Λ (σ₂ + t * I) :=
    funext fun t ↦ (hΛG _ (by simp)).symm
  have iF : VerticalIntegrable (mellin F) σ₁ := by
    rw [VerticalIntegrable, eF]
    exact h1
  have iG : VerticalIntegrable (mellin G) σ₂ := by
    rw [VerticalIntegrable, eG]
    exact h2
  have invF := mellinInv_mellin_eq σ₁ F hx hF iF hFx
  have invG := mellinInv_mellin_eq σ₂ G hx hG iG hGx
  rw [← invF, ← invG, mellinInv, mellinInv]
  congr 1
  simp only [smul_eq_mul]
  rw [show (fun y : ℝ ↦ (x : ℂ) ^ (-((σ₁ : ℂ) + y * I)) * mellin F (σ₁ + y * I)) =
      fun y : ℝ ↦ (x : ℂ) ^ (-((σ₁ : ℂ) + y * I)) * Λ (σ₁ + y * I) from
      funext fun t ↦ by rw [hΛF _ (by simp)],
    show (fun y : ℝ ↦ (x : ℂ) ^ (-((σ₂ : ℂ) + y * I)) * mellin G (σ₂ + y * I)) =
      fun y : ℝ ↦ (x : ℂ) ^ (-((σ₂ : ℂ) + y * I)) * Λ (σ₂ + y * I) from
      funext fun t ↦ by rw [hΛG _ (by simp)]]
  have hpc : Continuous fun s : ℂ ↦ (x : ℂ) ^ (-s) := continuous_neg.const_cpow (Or.inl hx0)
  have hpd : Differentiable ℂ fun s : ℂ ↦ (x : ℂ) ^ (-s) :=
    differentiable_neg.const_cpow (Or.inl hx0)
  have hnorm : ∀ s : ℂ, ‖(x : ℂ) ^ (-s)‖ = x ^ (-s.re) := fun s ↦ by
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  have hint : ∀ σ : ℝ, VerticalIntegrable Λ σ →
      Integrable fun t : ℝ ↦ (x : ℂ) ^ (-((σ : ℂ) + t * I)) * Λ (σ + t * I) := by
    intro σ hσi
    refine Integrable.bdd_mul (c := x ^ (-σ)) hσi ?_ (Eventually.of_forall fun t ↦ ?_)
    · exact (hpc.comp (by fun_prop)).aestronglyMeasurable
    · rw [hnorm]
      simp
  obtain ⟨C, hC⟩ := hdecay
  refine integral_vertical_eq_of_strip (h := fun s ↦ (x : ℂ) ^ (-s) * Λ s) hσ
    (hpc.continuousOn.mul hc) (hpd.differentiableOn.mul hd) (hint σ₁ h1) (hint σ₂ h2)
    ⟨(x ^ (-σ₁) + x ^ (-σ₂)) * max C 0, fun s hs ↦ ?_⟩
  rw [norm_mul, hnorm, mul_assoc]
  have h3 : ‖Λ s‖ * |s.im| ≤ max C 0 := (hC s hs).trans (le_max_left _ _)
  have h4 : 0 ≤ ‖Λ s‖ * |s.im| := by positivity
  have h5 : 0 ≤ x ^ (-σ₁) + x ^ (-σ₂) := by positivity
  exact mul_le_mul (rpow_neg_le_add hx hs.1 hs.2) h3 h4 h5

/- ### Decay from boundedness -/

/-- **Phragmén–Lindelöf decay in a strip.** A function bounded on an open vertical strip, with
`‖Λ s‖ ‖s‖` bounded on the two boundary lines, has `‖Λ s‖ |Im s|` bounded on the closed strip. -/
theorem decay_of_bounded_strip {Λ : ℂ → ℂ} {σ₂ σ₁ : ℝ} (hσ : σ₂ < σ₁)
    (hd : DiffContOnCl ℂ Λ (re ⁻¹' Ioo σ₂ σ₁))
    (hM : ∃ M, ∀ s : ℂ, s.re ∈ Ioo σ₂ σ₁ → ‖Λ s‖ ≤ M)
    (hB : ∃ B, ∀ s : ℂ, (s.re = σ₂ ∨ s.re = σ₁) → ‖Λ s‖ * ‖s‖ ≤ B) :
    ∃ C, ∀ s : ℂ, s.re ∈ Icc σ₂ σ₁ → ‖Λ s‖ * |s.im| ≤ C := by
  obtain ⟨M, hM⟩ := hM
  obtain ⟨B, hB⟩ := hB
  refine ⟨B, fun s hs ↦ ?_⟩
  have hw : 0 < σ₁ - σ₂ := sub_pos.mpr hσ
  set c : ℝ := π / (2 * (σ₁ - σ₂)) with hcdef
  have hc0 : 0 < c := by positivity
  have hcπ : c < π / (σ₁ - σ₂) := by
    rw [hcdef]
    exact div_lt_div_of_pos_left Real.pi_pos hw (by linarith)
  set R : ℝ := |σ₁| + |σ₂| with hR
  have hR0 : 0 ≤ R := by positivity
  have hΨ : DiffContOnCl ℂ (fun s : ℂ ↦ s • Λ s) (re ⁻¹' Ioo σ₂ σ₁) :=
    differentiable_id.diffContOnCl.smul hd
  have hgrow : (fun s : ℂ ↦ s • Λ s) =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo σ₂ σ₁)]
      fun z ↦ Real.exp (1 * Real.exp (c * |z.im|)) := by
    refine Asymptotics.IsBigO.of_bound ((R + 1 / c) * |M|)
      (eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ ?_))
    have hs' : s.re ∈ Ioo σ₂ σ₁ := hs
    have hre : |s.re| ≤ R := by
      rw [hR, abs_le]
      constructor
      · have := neg_abs_le σ₂
        have := abs_nonneg σ₁
        linarith [hs'.1]
      · have := le_abs_self σ₁
        have := abs_nonneg σ₂
        linarith [hs'.2]
    have hns : ‖s‖ ≤ R + |s.im| := (norm_le_abs_re_add_abs_im s).trans (by linarith)
    have hΛ : ‖Λ s‖ ≤ |M| := (hM s hs').trans (le_abs_self M)
    have ht0 : 0 ≤ c * |s.im| := by positivity
    have hexp1 : 1 + c * |s.im| ≤ Real.exp (c * |s.im|) := by
      linarith [Real.add_one_le_exp (c * |s.im|)]
    have hexp2 : Real.exp (c * |s.im|) ≤ Real.exp (1 * Real.exp (c * |s.im|)) := by
      rw [one_mul]
      linarith [Real.add_one_le_exp (Real.exp (c * |s.im|))]
    have hlin : R + |s.im| ≤ (R + 1 / c) * (1 + c * |s.im|) := by
      have h1 : 1 / c * (c * |s.im|) = |s.im| := by field_simp
      have h2 : 0 ≤ R * (c * |s.im|) := by positivity
      have h3 : 0 ≤ 1 / c := by positivity
      nlinarith
    have hK0 : 0 ≤ R + 1 / c := by positivity
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc ‖s‖ * ‖Λ s‖ ≤ (R + |s.im|) * |M| :=
          mul_le_mul hns hΛ (norm_nonneg _) (by positivity)
      _ ≤ ((R + 1 / c) * Real.exp (1 * Real.exp (c * |s.im|))) * |M| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg M)
          exact hlin.trans (mul_le_mul_of_nonneg_left (hexp1.trans hexp2) hK0)
      _ = _ := by ring
  have hPL := PhragmenLindelof.vertical_strip (C := B) hΨ ⟨c, hcπ, 1, hgrow⟩
    (fun z hz ↦ by
      rw [norm_smul, mul_comm]
      exact hB z (Or.inl hz))
    (fun z hz ↦ by
      rw [norm_smul, mul_comm]
      exact hB z (Or.inr hz)) hs.1 hs.2
  rw [norm_smul, mul_comm] at hPL
  exact (mul_le_mul_of_nonneg_left (abs_im_le_norm s) (norm_nonneg _)).trans hPL

/- ### Bounds for the Gamma function on vertical lines -/

/-- `|Γ(s)| ≤ Γ(Re s)` for `Re s > 0`. -/
theorem norm_Gamma_le {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- `|Γ(s)| |s| ≤ Γ(Re s + 1)` for `Re s > 0`. -/
theorem norm_Gamma_mul_norm_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ * ‖s‖ ≤ Real.Gamma (s.re + 1) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have h1 : ‖Complex.Gamma (s + 1)‖ ≤ Real.Gamma (s + 1).re :=
    norm_Gamma_le (by simp; linarith)
  rw [Complex.Gamma_add_one s hs0, norm_mul] at h1
  simpa [mul_comm] using h1

/-- `|Γ(s)| |s|² ≤ Γ(Re s + 2)` for `Re s > 0`. -/
theorem norm_Gamma_mul_sq_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ * (s.re ^ 2 + s.im ^ 2) ≤ Real.Gamma (s.re + 2) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have h1 := norm_Gamma_mul_norm_le hs1
  rw [Complex.Gamma_add_one s hs0, norm_mul] at h1
  have h2 : (s + 1).re + 1 = s.re + 2 := by simp; ring
  rw [h2] at h1
  have h3 : ‖s‖ ≤ ‖s + 1‖ := by
    have h6 : ‖s‖ ^ 2 ≤ ‖s + 1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
      simp only [add_re, one_re, add_im, one_im, add_zero]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h6
  have h4 : s.re ^ 2 + s.im ^ 2 = ‖s‖ * ‖s‖ := by
    rw [← sq, Complex.sq_norm, normSq_apply]
    ring
  rw [h4]
  have h5 : 0 ≤ ‖Complex.Gamma s‖ * ‖s‖ := by positivity
  calc ‖Complex.Gamma s‖ * (‖s‖ * ‖s‖) = ‖Complex.Gamma s‖ * ‖s‖ * ‖s‖ := by ring
    _ ≤ ‖Complex.Gamma s‖ * ‖s‖ * ‖s + 1‖ := mul_le_mul_of_nonneg_left h3 h5
    _ = ‖s‖ * ‖Complex.Gamma s‖ * ‖s + 1‖ := by ring
    _ ≤ _ := h1

/-- `|Γ(σ + it)| ≤ C / (1 + t²)` on a vertical line `σ > 0`. -/
theorem norm_Gamma_le_inv_one_add_sq {σ : ℝ} (hσ : 0 < σ) (s : ℂ) (hs : s.re = σ) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (σ + 2) / min 1 (σ ^ 2) * (1 + s.im ^ 2)⁻¹ := by
  have hm : 0 < min 1 (σ ^ 2) := lt_min one_pos (by positivity)
  have h1 := norm_Gamma_mul_sq_le (s := s) (by rw [hs]; exact hσ)
  rw [hs] at h1
  have h2 : min 1 (σ ^ 2) * (1 + s.im ^ 2) ≤ σ ^ 2 + s.im ^ 2 := by
    have ha : min 1 (σ ^ 2) ≤ 1 := min_le_left _ _
    have hb : min 1 (σ ^ 2) ≤ σ ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg s.im]
  have h3 : ‖Complex.Gamma s‖ * (min 1 (σ ^ 2) * (1 + s.im ^ 2)) ≤ Real.Gamma (σ + 2) :=
    (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans h1
  have h4 : 0 < 1 + s.im ^ 2 := by positivity
  rw [div_mul_eq_mul_div, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity),
    mul_comm (1 + s.im ^ 2)]
  exact h3

end Strip

/- ## The q-series and automatic cuspidality -/

section QSeries

open Complex Filter Set CongruenceSubgroup WeierstrassCurve Function Matrix
  Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm Manifold Real

/- ### Real estimates -/

/-- `x ^ b e ^ (-x) ≤ 2` for `0 ≤ b ≤ 2`. -/
theorem rpow_mul_exp_neg_le {b x : ℝ} (hb0 : 0 ≤ b) (hb2 : b ≤ 2) (hx : 0 ≤ x) :
    x ^ b * Real.exp (-x) ≤ 2 := by
  have h1 : x ^ b ≤ 1 + x ^ 2 := by
    rcases le_total x 1 with h | h
    · exact (Real.rpow_le_one hx h hb0).trans (by nlinarith [sq_nonneg x])
    · calc x ^ b ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hb2
        _ = x ^ 2 := Real.rpow_two x
        _ ≤ _ := by linarith
  have h2 : 1 + x ^ 2 ≤ 2 * Real.exp x := by
    nlinarith [Real.quadratic_le_exp_of_nonneg hx]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos x)]
  linarith

/-- `n ^ b e ^ (-2π n y) ≤ 2 y ^ (-b)`. -/
theorem natCast_rpow_mul_exp_le {b y : ℝ} (hb0 : 0 ≤ b) (hb2 : b ≤ 2) (hy : 0 < y) (n : ℕ) :
    (n : ℝ) ^ b * Real.exp (-(2 * π * n * y)) ≤ 2 * y ^ (-b) := by
  have hπ : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hx : 0 ≤ 2 * π * n * y := by positivity
  have hn : (n : ℝ) = (2 * π * n * y) / (2 * π * y) := by field_simp
  have hpos : 0 < (2 * π * y) ^ b := by positivity
  have hle : y ^ b ≤ (2 * π * y) ^ b :=
    Real.rpow_le_rpow hy.le (by nlinarith) hb0
  have hyb : 0 < y ^ b := by positivity
  calc
    _ = (2 * π * n * y) ^ b * Real.exp (-(2 * π * n * y)) / (2 * π * y) ^ b := by
      have hnb : (n : ℝ) ^ b = (2 * π * n * y) ^ b / (2 * π * y) ^ b := by
        rw [← Real.div_rpow hx (by positivity), ← hn]
      rw [hnb]
      ring
    _ ≤ 2 / (2 * π * y) ^ b := div_le_div_of_nonneg_right (rpow_mul_exp_neg_le hb0 hb2 hx) hpos.le
    _ ≤ 2 / y ^ b := div_le_div_of_nonneg_left (by norm_num) hyb hle
    _ = _ := by rw [Real.rpow_neg hy.le, div_eq_mul_inv]

/-- The identity behind the cusp estimate. -/
theorem rpow_cusp_identity {y D : ℝ} (b : ℝ) (hy : 0 < y) (hD : 0 < D) :
    (y / D ^ 2) ^ (-b) * (D ^ 2)⁻¹ = y ^ (-b) * D ^ (2 * b - 2) := by
  have h2 : (D ^ 2) ^ b = D ^ (2 * b) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hD.le]
  have hDb : 0 < D ^ (2 * b) := by positivity
  have hyb : 0 < y ^ b := by positivity
  rw [Real.rpow_neg (by positivity), Real.div_rpow hy.le (by positivity), h2, Real.rpow_neg hy.le,
    Real.rpow_sub hD, Real.rpow_two]
  field_simp

/- ### The q-series -/

/-- The q-series `∑ a n q ^ n`, `q = exp (2πiτ)`, on the upper half-plane. A reduction file
declares no auxiliary definition, so the function is the witness of this lemma. -/
theorem qSeries_ex : ∃ f : (ℕ → ℂ) → ℍ → ℂ,
    ∀ (a : ℕ → ℂ) (τ : ℍ), f a τ = ∑' n : ℕ, a n * Periodic.qParam 1 τ ^ n :=
  ⟨fun a τ ↦ ∑' n : ℕ, a n * Periodic.qParam 1 τ ^ n, fun _ _ ↦ rfl⟩

theorem norm_qParam_pow (w : ℂ) (n : ℕ) :
    ‖Periodic.qParam 1 w ^ n‖ = Real.exp (-(2 * π * n * w.im)) := by
  rw [norm_pow, Periodic.norm_qParam, ← Real.exp_nat_mul]
  congr 1
  ring

section Series

variable {a : ℕ → ℂ} {b : ℝ}

/-- Termwise bound on a half-plane `y ≤ Im w`. -/
theorem qSeries_term_le (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2) {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hw : y ≤ w.im) (n : ℕ) :
    ‖a n * Periodic.qParam 1 w ^ n‖ ≤ ‖a n‖ / (n : ℝ) ^ b * (2 * y ^ (-b)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ha0]
  have hnpos : 0 < (n : ℝ) ^ b := by positivity
  have hexp : Real.exp (-(2 * π * n * w.im)) ≤ Real.exp (-(2 * π * n * y)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ 2 * π * (n : ℝ) := by positivity
    nlinarith
  rw [norm_mul, norm_qParam_pow]
  calc
    _ ≤ ‖a n‖ * Real.exp (-(2 * π * n * y)) := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = ‖a n‖ / (n : ℝ) ^ b * ((n : ℝ) ^ b * Real.exp (-(2 * π * n * y))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (natCast_rpow_mul_exp_le hb0 hb2 hy n) (by positivity)

variable (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
  (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b)

include ha0 hb0 hb2 hS

/-- **Absolute convergence** of the q-series on the upper half-plane. -/
theorem qSeries_summable_norm (τ : ℍ) : Summable fun n : ℕ ↦ ‖a n * Periodic.qParam 1 τ ^ n‖ :=
  (hS.mul_right _).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (qSeries_term_le ha0 hb0 hb2 τ.im_pos le_rfl)

/-- The q-series sums to `qSeries a τ`, with the given coefficients. -/
theorem qSeries_hasSum (τ : ℍ) : HasSum (fun n : ℕ ↦ a n • Periodic.qParam 1 τ ^ n) (qSeries_ex.choose a τ) := by
  rw [qSeries_ex.choose_spec]
  exact (qSeries_summable_norm ha0 hb0 hb2 hS τ).of_norm.hasSum

/-- **Uniform bound** `‖f τ‖ ≤ 2 S (Im τ) ^ (-b)`. -/
theorem qSeries_norm_le (τ : ℍ) :
    ‖qSeries_ex.choose a τ‖ ≤ 2 * (∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ b) * τ.im ^ (-b) := by
  have hsum := qSeries_summable_norm ha0 hb0 hb2 hS τ
  rw [qSeries_ex.choose_spec]
  calc
    _ ≤ ∑' n : ℕ, ‖a n * Periodic.qParam 1 τ ^ n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ b * (2 * τ.im ^ (-b)) :=
      hsum.tsum_le_tsum (qSeries_term_le ha0 hb0 hb2 τ.im_pos le_rfl) (hS.mul_right _)
    _ = _ := by rw [tsum_mul_right]; ring

/-- **Vanishing at `i∞`.** -/
theorem qSeries_isZeroAtImInfty (hb : 0 < b) : IsZeroAtImInfty (qSeries_ex.choose a) := by
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have ht : Tendsto (fun τ : ℍ ↦ 2 * (∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ b) * τ.im ^ (-b))
      atImInfty (𝓝 (2 * (∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ b) * 0)) :=
    ((tendsto_rpow_neg_atTop hb).comp tendsto_comap).const_mul _
  rw [mul_zero] at ht
  exact squeeze_zero_norm (qSeries_norm_le ha0 hb0 hb2 hS) ht

omit ha0 hb0 hb2 hS in
/-- **Period one.** -/
theorem qSeries_periodic (a : ℕ → ℂ) : Periodic (qSeries_ex.choose a ∘ ofComplex) ((1 : ℝ) : ℂ) := by
  intro w
  have hq : Periodic.qParam 1 (w + 1) = Periodic.qParam 1 w := by
    simp [Periodic.qParam, mul_add, Complex.exp_add, Complex.exp_two_pi_mul_I]
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + ((1 : ℝ) : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw, qSeries_ex.choose_spec]
    simp [hq]
  · have hw' : w.im ≤ 0 := not_lt.mp hw
    have hw1 : (w + ((1 : ℝ) : ℂ)).im ≤ 0 := by simpa using hw'
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw']

/-- **Holomorphy** on the upper half-plane. -/
theorem qSeries_mdifferentiable : MDiff (qSeries_ex.choose a) := by
  rw [mdifferentiable_iff]
  intro w hw
  have hw2 : 0 < w.im / 2 := half_pos hw
  let U : Set ℂ := {v | w.im / 2 < v.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hwU : w ∈ U := show w.im / 2 < w.im from half_lt_self hw
  have hd : DifferentiableOn ℂ (fun v : ℂ ↦ ∑' n : ℕ, a n * Periodic.qParam 1 v ^ n) U :=
    differentiableOn_tsum_of_summable_norm (hS.mul_right (2 * (w.im / 2) ^ (-b)))
      (fun n ↦ ((Periodic.differentiable_qParam.pow n).const_mul (a n)).differentiableOn) hU
      (fun n v hv ↦ qSeries_term_le ha0 hb0 hb2 hw2 (le_of_lt hv) n)
  refine ((hd w hwU).differentiableAt (hU.mem_nhds hwU)).differentiableWithinAt.congr_of_eventuallyEq
    ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hwU)] with v hv
    have hv0 : 0 < v.im := hw2.trans hv
    simp [qSeries_ex.choose_spec, ofComplex_apply_of_im_pos hv0]
  · simp [qSeries_ex.choose_spec, ofComplex_apply_of_im_pos hw]

end Series

/- ### Vanishing at every cusp from a power bound -/

/-- A function with `‖f τ‖ ≤ C (Im τ) ^ (-b)` for some `1 ≤ b < 2` whose weight-two slash by
`γ ∈ SL(2, ℤ)` is periodic has slash vanishing at `i∞`. Indeed
`‖(f ∣[2] γ) τ‖ ≤ C y ^ (-b) ‖cτ + d‖ ^ (2b - 2) = O(y ^ (b - 2))` on a period strip. -/
theorem isZeroAtImInfty_slash_of_bound {f : ℍ → ℂ} {C b h : ℝ} (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hh : 0 < h) (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C * τ.im ^ (-b)) (γ : SL(2, ℤ))
    (hper : Periodic ((f ∣[(2 : ℤ)] γ) ∘ ofComplex) (h : ℂ)) :
    IsZeroAtImInfty (f ∣[(2 : ℤ)] γ) := by
  set g := f ∣[(2 : ℤ)] γ with hg
  let c : ℝ := ((γ 1 0 : ℤ) : ℝ)
  let d : ℝ := ((γ 1 1 : ℤ) : ℝ)
  let K : ℝ := |c| * (h + 1) + |d|
  have hK0 : 0 ≤ K := by positivity
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hf UpperHalfPlane.I)
    exact nonneg_of_mul_nonneg_left h1 (by positivity)
  have hbound : ∀ z : ℍ, 1 ≤ z.im → ‖g z‖ ≤ C * K ^ (2 * b - 2) * z.im ^ (-(2 - b)) := by
    intro z hz
    have hy : 0 < z.im := z.im_pos
    let m : ℤ := ⌊z.re / h⌋
    let w : ℂ := (z : ℂ) - m * h
    have hwim : w.im = z.im := by simp [w]
    have hwre : w.re = z.re - m * h := by simp [w]
    have hm1 : (m : ℝ) * h ≤ z.re := by
      have := Int.floor_le (z.re / h)
      exact (le_div_iff₀ hh).mp this
    have hm2 : z.re < ((m : ℝ) + 1) * h := by
      have := Int.lt_floor_add_one (z.re / h)
      exact (div_lt_iff₀ hh).mp this
    have hw0 : 0 < w.im := by rw [hwim]; exact hy
    let z₀ : ℍ := ⟨w, hw0⟩
    have hz₀im : z₀.im = z.im := hwim
    have e : g z = g z₀ := by
      have h1 := hper.sub_int_mul_eq (x := (z : ℂ)) m
      simp only [Function.comp_apply] at h1
      rw [ofComplex_apply, ofComplex_apply_of_im_pos hw0] at h1
      exact h1.symm
    set D : ℝ := ‖denom γ z₀‖ with hDdef
    have hD : 0 < D := norm_pos_iff.mpr (denom_ne_zero _ _)
    have him : (γ • z₀).im = z.im / D ^ 2 := by
      rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, hz₀im]
    have hDK : D ≤ K * z.im := by
      have hden : denom γ z₀ = (c : ℂ) * w + (d : ℂ) := by
        rw [ModularGroup.denom_apply]
        simp [c, d, z₀]
      have hw_norm : ‖w‖ ≤ h + z.im := by
        refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
        rw [hwim, hwre, abs_of_pos hy, abs_of_nonneg (by linarith)]
        nlinarith
      have h1 : D ≤ |c| * (h + z.im) + |d| := by
        rw [hDdef, hden]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
      have hc0 : 0 ≤ |c| := abs_nonneg c
      have hd0 : 0 ≤ |d| := abs_nonneg d
      have h2 : |c| * (h + z.im) ≤ |c| * (h + 1) * z.im := by
        have : h + z.im ≤ (h + 1) * z.im := by nlinarith
        nlinarith
      have h3 : |d| ≤ |d| * z.im := by nlinarith
      calc D ≤ |c| * (h + z.im) + |d| := h1
        _ ≤ |c| * (h + 1) * z.im + |d| * z.im := add_le_add h2 h3
        _ = K * z.im := by simp only [K]; ring
    have hpow : D ^ (2 * b - 2) ≤ K ^ (2 * b - 2) * z.im ^ (2 * b - 2) := by
      rw [← Real.mul_rpow hK0 hy.le]
      exact Real.rpow_le_rpow hD.le hDK (by linarith)
    have hyy : z.im ^ (-b) * z.im ^ (2 * b - 2) = z.im ^ (-(2 - b)) := by
      rw [← Real.rpow_add hy]
      congr 1
      ring
    have hfz : ‖f (γ • z₀)‖ ≤ C * (z.im / D ^ 2) ^ (-b) := by
      have := hf (γ • z₀)
      rwa [him] at this
    have hDinv : ‖denom γ z₀ ^ (-(2 : ℤ))‖ = (D ^ 2)⁻¹ := by
      rw [norm_zpow, _root_.zpow_neg]
      rfl
    rw [e, hg, ModularForm.SL_slash_apply, norm_mul, hDinv]
    calc
      _ ≤ C * (z.im / D ^ 2) ^ (-b) * (D ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hfz (by positivity)
      _ = C * (z.im ^ (-b) * D ^ (2 * b - 2)) := by
        rw [mul_assoc, rpow_cusp_identity b hy hD]
      _ ≤ C * (z.im ^ (-b) * (K ^ (2 * b - 2) * z.im ^ (2 * b - 2))) := by
        gcongr
      _ = _ := by rw [← hyy]; ring
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have ht : Tendsto (fun z : ℍ ↦ C * K ^ (2 * b - 2) * z.im ^ (-(2 - b)))
      atImInfty (𝓝 (C * K ^ (2 * b - 2) * 0)) :=
    ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 - b)).comp tendsto_comap).const_mul _
  rw [mul_zero] at ht
  refine squeeze_zero_norm' ?_ ht
  exact (atImInfty_mem _).mpr ⟨1, hbound⟩

/- ### Uniqueness of q-expansion coefficients -/

/-- Function-level uniqueness of q-expansion coefficients at width one. -/
theorem qExpansion_coeff_of_hasSum {f : ℍ → ℂ} {c : ℕ → ℂ}
    (han : AnalyticAt ℂ (cuspFunction 1 f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (f τ)) (m : ℕ) :
    (qExpansion 1 f).coeff m = c m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos han hf).hasFPowerSeriesAt
  have h2 := han.hasFPowerSeriesAt
  have h3 := congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at h3
  rw [qExpansion_coeff, h3, div_eq_mul_inv, mul_comm]

/- ### Periodicity of the slashes -/

theorem mapGL_T_zpow (n : ℤ) :
    mapGL ℝ (ModularGroup.T ^ n) = Matrix.GeneralLinearGroup.upperRightHom ((n : ℤ) : ℝ) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have h : (mapGL ℝ (ModularGroup.T ^ n)) i j =
      algebraMap ℤ ℝ ((ModularGroup.T ^ n).1 i j) := rfl
  rw [h, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom]

open ConjAct Pointwise in
/-- If `f` is invariant under a group containing `Γ(N)`, each slash `f ∣[2] γ` has period `N`,
because `γ T ^ N γ⁻¹ ∈ Γ(N)`. -/
theorem slash_periodic_of_Gamma_le {N : ℕ} {Γ : Subgroup SL(2, ℤ)} (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    {f : ℍ → ℂ} {k : ℤ} (hinv : ∀ γ ∈ Γ, f ∣[k] γ = f) (γ : SL(2, ℤ)) :
    Periodic ((f ∣[k] γ) ∘ ofComplex) (((N : ℝ)) : ℂ) := by
  let F : SlashInvariantForm (Γ.map (mapGL ℝ)) k :=
    ⟨f, by rintro _ ⟨δ, hδ, rfl⟩; exact hinv δ hδ⟩
  refine SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate F (mapGL ℝ γ)) ?_
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    toConjAct_smul]
  refine ⟨γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹, hΓ ((Gamma_normal N).conj_mem _ ?_ γ), ?_⟩
  · simpa using ModularGroup_T_pow_mem_Gamma N N dvd_rfl
  · rw [map_mul, map_mul, map_inv, mapGL_T_zpow]
    simp

end QSeries

/- ## The transformation law on a vertical line -/

section VerticalLine

open Complex Filter Set CongruenceSubgroup WeierstrassCurve Function Matrix
  Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm Manifold Real

/- ### The kernel -/

/-- The additive-twist kernel `K_r(y) = ∑ a n e(n r) exp (-2π n y)`: the q-series on the
vertical line `Re τ = r`. -/
theorem additiveKernel_ex : ∃ K : (ℕ → ℂ) → ℝ → ℝ → ℂ, ∀ (a : ℕ → ℂ) (r y : ℝ),
    K a r y = ∑' n : ℕ, a n * (cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * y)) : ℂ)) :=
  ⟨fun a r y ↦ ∑' n : ℕ, a n * (cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * y)) : ℂ)),
    fun _ _ _ ↦ rfl⟩

/-- The point `r + iy` of the upper half-plane. -/
theorem vertical_ex : ∃ v : (r y : ℝ) → 0 < y → ℍ,
    ∀ (r y : ℝ) (hy : 0 < y), ((v r y hy : ℍ) : ℂ) = r + y * I :=
  ⟨fun r y hy ↦ ⟨(r : ℂ) + y * I, by simpa using hy⟩, fun _ _ _ ↦ rfl⟩

theorem coe_vertical (r y : ℝ) (hy : 0 < y) : ((vertical_ex.choose r y hy : ℍ) : ℂ) = r + y * I :=
  vertical_ex.choose_spec r y hy

theorem qParam_pow_vertical (r y : ℝ) (n : ℕ) :
    Periodic.qParam 1 ((r : ℂ) + y * I) ^ n =
      cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * y)) : ℂ) := by
  rw [Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (2 * π * n * y : ℂ) * I_mul_I

/-- The q-series on a vertical line is the additive-twist kernel. -/
theorem qSeries_vertical (a : ℕ → ℂ) (r y : ℝ) (hy : 0 < y) :
    qSeries_ex.choose a (vertical_ex.choose r y hy) = additiveKernel_ex.choose a r y := by
  simp only [qSeries_ex.choose_spec, additiveKernel_ex.choose_spec, coe_vertical, qParam_pow_vertical]

/- ### The Möbius action on a vertical line through a cusp -/

theorem moebius_vertical_aux {A B C D y : ℂ} (hC : C ≠ 0) (hy : y ≠ 0)
    (hdet : A * D - B * C = 1) :
    (A * (-D / C + y * I) + B) / (C * (-D / C + y * I) + D) = A / C + 1 / (C ^ 2 * y) * I := by
  have h1 : C * (-D / C + y * I) + D = C * y * I := by
    field_simp
    ring
  have h2 : (A / C + 1 / (C ^ 2 * y) * I) * (C * y * I) = A * y * I - 1 / C := by
    have h3 : (A / C + 1 / (C ^ 2 * y) * I) * (C * y * I) =
        A / C * C * (y * I) + 1 / (C ^ 2 * y) * (C * y) * (I * I) := by ring
    rw [h3, I_mul_I]
    have h4 : A / C * C = A := by field_simp
    have h5 : 1 / (C ^ 2 * y) * (C * y) = 1 / C := by field_simp
    rw [h4, h5]
    ring
  have h6 : A * (-D / C + y * I) + B = A * y * I - 1 / C := by
    field_simp
    linear_combination (-1 : ℂ) * hdet
  rw [h1, div_eq_iff (mul_ne_zero (mul_ne_zero hC hy) I_ne_zero), h2, h6]

theorem det_complex (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) - ((γ 0 1 : ℤ) : ℂ) * ((γ 1 0 : ℤ) : ℂ) = 1 := by
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

theorem kernel_arg_pos {γ : SL(2, ℤ)} (hc : γ 1 0 ≠ 0) {y : ℝ} (hy : 0 < y) :
    0 < 1 / (((γ 1 0 : ℤ) : ℝ) ^ 2 * y) := by
  have : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
  positivity

/-- `γ (-D/C + iy) = A/C + i/(C² y)`. -/
theorem smul_vertical (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) {y : ℝ} (hy : 0 < y) :
    γ • vertical_ex.choose (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y hy =
      vertical_ex.choose (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) (1 / (((γ 1 0 : ℤ) : ℝ) ^ 2 * y))
        (kernel_arg_pos hc hy) := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_vertical, coe_vertical]
  have hC : ((γ 1 0 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have := moebius_vertical_aux hC hy' (det_complex γ)
  simp only [algebraMap_int_eq, eq_intCast, ofReal_intCast, ofReal_div, ofReal_neg, ofReal_one,
    ofReal_mul, ofReal_pow]
  exact this

/-- `Cz + D = iCy` at `z = -D/C + iy`. -/
theorem denom_vertical (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) {y : ℝ} (hy : 0 < y) :
    denom γ (vertical_ex.choose (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y hy) =
      ((γ 1 0 : ℤ) : ℂ) * y * I := by
  have hC : ((γ 1 0 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [ModularGroup.denom_apply, coe_vertical]
  push_cast
  field_simp
  ring

/-- **The weight-two slash on the vertical line through the cusp `-D/C`.** -/
theorem slash_vertical (f : ℍ → ℂ) (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) {y : ℝ} (hy : 0 < y) :
    (f ∣[(2 : ℤ)] γ) (vertical_ex.choose (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y hy) =
      -f (vertical_ex.choose (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) (1 / (((γ 1 0 : ℤ) : ℝ) ^ 2 * y))
        (kernel_arg_pos hc hy)) / ((((γ 1 0 : ℤ) : ℝ) * y : ℝ) : ℂ) ^ 2 := by
  rw [ModularForm.SL_slash_apply, smul_vertical γ hc hy, denom_vertical γ hc hy]
  have hI : (((γ 1 0 : ℤ) : ℂ) * y * I) ^ (-(2 : ℤ)) = -((((γ 1 0 : ℤ) : ℂ) * y) ^ 2)⁻¹ := by
    rw [_root_.zpow_neg, zpow_ofNat, mul_pow, I_sq, mul_neg_one, inv_neg]
  rw [hI]
  push_cast
  ring

/- ### The identity theorem on a vertical line -/

/-- Two holomorphic functions on the upper half-plane that agree on a vertical line are
equal. -/
theorem eq_of_eq_on_vertical {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g) (r : ℝ)
    (h : ∀ (y : ℝ) (hy : 0 < y), f (vertical_ex.choose r y hy) = g (vertical_ex.choose r y hy)) : f = g := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have hfa := hf.analyticOnNhd hU
  have hga := hg.analyticOnNhd hU
  have hpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  let φ : ℝ → ℂ := fun y ↦ (r : ℂ) + y * I
  have hφ : Continuous φ := by fun_prop
  have hz₀ : φ 1 ∈ {z : ℂ | 0 < z.im} := by simp [φ]
  have hinj : Function.Injective φ := by
    intro y₁ y₂ h12
    have := congr_arg Complex.im h12
    simpa [φ] using this
  have htend : Tendsto φ (𝓝[≠] 1) (𝓝[≠] (φ 1)) :=
    hφ.continuousAt.continuousWithinAt.tendsto_nhdsWithin fun y hy ↦ hinj.ne hy
  have hev : ∀ᶠ y in 𝓝[≠] (1 : ℝ), (f ∘ ofComplex) (φ y) = (g ∘ ofComplex) (φ y) := by
    have hpos : ∀ᶠ y in 𝓝 (1 : ℝ), 0 < y := lt_mem_nhds one_pos
    filter_upwards [mem_nhdsWithin_of_mem_nhds hpos] with y hy
    have hy' : 0 < (φ y).im := by simpa [φ] using hy
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hy']
    have hv : vertical_ex.choose r y hy = ⟨φ y, hy'⟩ := UpperHalfPlane.ext (coe_vertical r y hy)
    have h1 := h y hy
    rw [hv] at h1
    exact h1
  have hfreq : ∃ᶠ z in 𝓝[≠] (φ 1), (f ∘ ofComplex) z = (g ∘ ofComplex) z :=
    htend.frequently (p := fun z ↦ (f ∘ ofComplex) z = (g ∘ ofComplex) z) hev.frequently
  have heq := hfa.eqOn_of_preconnected_of_frequently_eq hga hpc hz₀ hfreq
  funext τ
  have := heq τ.im_pos
  simpa [ofComplex_apply] using this

/- ### The kernel criterion -/

section Criterion

variable {a : ℕ → ℂ} {b : ℝ}

/-- **The exact kernel criterion.** For `γ` with nonzero lower-left entry, the weight-two
transformation identity of the q-series is the kernel identity. -/
theorem qSeries_slash_eq_iff_kernelIdentity (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    qSeries_ex.choose a ∣[(2 : ℤ)] γ = qSeries_ex.choose a ↔ (∀ y : ℝ, 0 < y →
      additiveKernel_ex.choose a (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) (1 / (((γ 1 0 : ℤ) : ℝ) ^ 2 * y)) =
        -((((γ 1 0 : ℤ) : ℝ) * y) ^ 2 : ℝ) *
          additiveKernel_ex.choose a (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y) := by
  have hne : ∀ y : ℝ, 0 < y → ((((γ 1 0 : ℤ) : ℝ) * y : ℝ) : ℂ) ^ 2 ≠ 0 := by
    intro y hy
    have hc' : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
    exact pow_ne_zero _ (ofReal_ne_zero.mpr (mul_ne_zero hc' hy.ne'))
  constructor
  · intro h y hy
    have h1 := congr_fun h (vertical_ex.choose (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y hy)
    rw [slash_vertical _ γ hc hy, qSeries_vertical, qSeries_vertical, div_eq_iff (hne y hy)] at h1
    push_cast at h1 ⊢
    linear_combination (-1 : ℂ) * h1
  · intro h
    have hf : MDiff (qSeries_ex.choose a) := qSeries_mdifferentiable ha0 hb0 hb2 hS
    have hg : MDiff (qSeries_ex.choose a ∣[(2 : ℤ)] γ) := by
      rw [ModularForm.SL_slash]
      exact hf.slash 2 _
    refine eq_of_eq_on_vertical hg hf (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) fun y hy ↦ ?_
    rw [slash_vertical _ γ hc hy, qSeries_vertical, qSeries_vertical, div_eq_iff (hne y hy),
      h y hy]
    push_cast
    ring

end Criterion

/-- For `γ` with zero lower-left entry the transformation identity holds for every q-series:
`γ` is `± T ^ m`. -/
theorem qSeries_slash_of_lowerLeft_eq_zero (a : ℕ → ℂ) (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    qSeries_ex.choose a ∣[(2 : ℤ)] γ = qSeries_ex.choose a := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    simpa [hc] using h
  funext τ
  rw [ModularForm.SL_slash_apply]
  have hden : denom γ τ = ((γ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
    simp [hc]
  have hsm : ((γ • τ : ℍ) : ℂ) = τ + ((γ 0 1 * γ 1 1 : ℤ) : ℂ) := by
    rw [coe_specialLinearGroup_apply]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [hc, h1, h2]
    · simp [hc, h1, h2]
      ring
  have hq : Periodic.qParam 1 ((γ • τ : ℍ) : ℂ) = Periodic.qParam 1 τ := by
    rw [hsm]
    simp only [Periodic.qParam, ofReal_one, div_one]
    rw [mul_add, Complex.exp_add,
      show 2 * π * I * ((γ 0 1 * γ 1 1 : ℤ) : ℂ) = ((γ 0 1 * γ 1 1 : ℤ) : ℂ) * (2 * π * I) by ring,
      exp_int_mul_two_pi_mul_I, mul_one]
  have hval : qSeries_ex.choose a (γ • τ) = qSeries_ex.choose a τ := by simp only [qSeries_ex.choose_spec, hq]
  have hd2 : (((γ 1 1 : ℤ) : ℂ)) ^ (-(2 : ℤ)) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp [h2]
  rw [hval, hden, hd2, mul_one]

end VerticalLine

/- ## Mellin transforms of the kernels -/

section MellinKernel

open Complex Filter Set MeasureTheory Function
open UpperHalfPlane hiding I
open scoped Topology Real Manifold MatrixGroups

/- ### The additive twist -/

/-- The additive twist `a n e(n r)` of a coefficient sequence. -/
theorem additiveTwist_ex : ∃ t : (ℕ → ℂ) → ℝ → ℕ → ℂ,
    ∀ (a : ℕ → ℂ) (r : ℝ) (n : ℕ), t a r n = a n * cexp (2 * π * I * n * r) :=
  ⟨fun a r n ↦ a n * cexp (2 * π * I * n * r), fun _ _ _ ↦ rfl⟩

theorem norm_additiveChar (n : ℕ) (r : ℝ) : ‖cexp (2 * π * I * n * r)‖ = 1 := by
  rw [show (2 * π * I * n * r : ℂ) = ((2 * π * n * r : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I]

theorem norm_additiveTwist (a : ℕ → ℂ) (r : ℝ) (n : ℕ) : ‖additiveTwist_ex.choose a r n‖ = ‖a n‖ := by
  rw [additiveTwist_ex.choose_spec, norm_mul, norm_additiveChar, mul_one]

/-- **The completed additive twist** `(2π) ^ (-s) Γ(s) ∑ a n e(n r) n ^ (-s)`. -/
theorem completedAdditiveL_ex : ∃ L : (ℕ → ℂ) → ℝ → ℂ → ℂ, ∀ (a : ℕ → ℂ) (r : ℝ) (s : ℂ),
    L a r s = ((2 * π : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * LSeries (additiveTwist_ex.choose a r) s :=
  ⟨fun a r s ↦ ((2 * π : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * LSeries (additiveTwist_ex.choose a r) s,
    fun _ _ _ ↦ rfl⟩

theorem im_vertical (r y : ℝ) (hy : 0 < y) : (vertical_ex.choose r y hy).im = y := by
  rw [← UpperHalfPlane.coe_im, coe_vertical]
  simp

section Kernel

variable {a : ℕ → ℂ} {b : ℝ}

theorem summable_norm_div_rpow (ha0 : a 0 = 0) (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b)
    {σ : ℝ} (hσ : b ≤ σ) : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ σ := by
  refine hS.of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ha0]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h2 : 0 < (n : ℝ) ^ b := by positivity
    exact div_le_div_of_nonneg_left (norm_nonneg _) h2
      (Real.rpow_le_rpow_of_exponent_le h1 hσ)

/-- The kernel as a sum of exponentials. -/
theorem hasSum_additiveKernel (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ additiveTwist_ex.choose a r n * (Real.exp (-(2 * π * n) * t) : ℂ))
      (additiveKernel_ex.choose a r t) := by
  have h := qSeries_hasSum ha0 hb0 hb2 hS (vertical_ex.choose r t ht)
  rw [qSeries_vertical] at h
  refine h.congr_fun fun n ↦ ?_
  rw [coe_vertical, qParam_pow_vertical, additiveTwist_ex.choose_spec, smul_eq_mul, mul_assoc, neg_mul]

theorem norm_kernel_term (a : ℕ → ℂ) (n : ℕ) (r t : ℝ) :
    ‖a n * (cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * t)) : ℂ))‖ =
      ‖a n‖ * Real.exp (-(2 * π * n * t)) := by
  rw [norm_mul, norm_mul, norm_additiveChar, one_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]

/-- `‖K_r(t)‖ ≤ 2 S t ^ (-b)` for `t > 0`. -/
theorem norm_additiveKernel_le (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖additiveKernel_ex.choose a r t‖ ≤ 2 * (∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ b) * t ^ (-b) := by
  have h := qSeries_norm_le ha0 hb0 hb2 hS (vertical_ex.choose r t ht)
  rwa [qSeries_vertical, im_vertical] at h

theorem summable_norm_mul_exp (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) :
    Summable fun n : ℕ ↦ ‖a n‖ * Real.exp (-(2 * π * n)) := by
  refine (qSeries_summable_norm ha0 hb0 hb2 hS (vertical_ex.choose 0 1 one_pos)).congr fun n ↦ ?_
  rw [norm_mul, norm_qParam_pow, coe_vertical]
  simp

/-- Exponential decay: `‖K_r(t)‖ ≤ S₁ exp (-2π (t - 1))` for `t ≥ 1`. -/
theorem norm_additiveKernel_le_exp (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ‖additiveKernel_ex.choose a r t‖ ≤
      (∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * π * n))) * Real.exp (-(2 * π * (t - 1))) := by
  have hs1 := summable_norm_mul_exp ha0 hb0 hb2 hS
  have hle : ∀ n : ℕ, ‖a n * (cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * t)) : ℂ))‖ ≤
      ‖a n‖ * Real.exp (-(2 * π * n)) * Real.exp (-(2 * π * (t - 1))) := by
    intro n
    rw [norm_kernel_term]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    · rw [mul_assoc ‖a n‖, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have h2 : 0 ≤ ((n : ℝ) - 1) * (t - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg Real.pi_pos.le h2]
  have hsum : Summable fun n : ℕ ↦
      ‖a n * (cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * t)) : ℂ))‖ :=
    (hs1.mul_right _).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [additiveKernel_ex.choose_spec]
  calc _ ≤
        ∑' n : ℕ, ‖a n * (cexp (2 * π * I * n * r) * (Real.exp (-(2 * π * n * t)) : ℂ))‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * π * n)) * Real.exp (-(2 * π * (t - 1))) :=
        hsum.tsum_le_tsum hle (hs1.mul_right _)
    _ = _ := tsum_mul_right

theorem continuousOn_additiveKernel (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) :
    ContinuousOn (additiveKernel_ex.choose a r) (Ioi 0) := by
  have hmd := qSeries_mdifferentiable ha0 hb0 hb2 hS
  rw [UpperHalfPlane.mdifferentiable_iff] at hmd
  have hφ : ContinuousOn (fun t : ℝ ↦ (r : ℂ) + t * I) (Ioi 0) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (r : ℂ) + t * I) (Ioi 0) {z : ℂ | 0 < z.im} :=
    fun t ht ↦ by simpa using ht
  refine (hmd.continuousOn.comp hφ hmaps).congr fun t ht ↦ ?_
  have ht' : 0 < ((r : ℂ) + t * I).im := by simpa using ht
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos ht']
  have hv : vertical_ex.choose r t ht = ⟨(r : ℂ) + t * I, ht'⟩ := UpperHalfPlane.ext (coe_vertical r t ht)
  exact (qSeries_vertical a r t ht).symm.trans (congrArg (qSeries_ex.choose a) hv)

theorem isBigO_additiveKernel_atTop (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) :
    additiveKernel_ex.choose a r =O[atTop] fun t : ℝ ↦ Real.exp (-(2 * π) * t) := by
  refine Asymptotics.IsBigO.of_bound
    ((∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * π * n))) * Real.exp (2 * π)) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  refine (norm_additiveKernel_le_exp ha0 hb0 hb2 hS r ht).trans (le_of_eq ?_)
  have he : Real.exp (-(2 * π * (t - 1))) = Real.exp (2 * π) * Real.exp (-(2 * π) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, he]
  ring

theorem isBigO_additiveKernel_zero (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) :
    additiveKernel_ex.choose a r =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-b) := by
  refine Asymptotics.IsBigO.of_bound (2 * (∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ b)) ?_
  refine eventually_nhdsWithin_of_forall fun t ht ↦ ?_
  have ht' : 0 < t := ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht'.le _)]
  exact norm_additiveKernel_le ha0 hb0 hb2 hS r ht'

/-- The Mellin transform of the kernel converges on `Re s > b`. -/
theorem mellinConvergent_additiveKernel (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) {s : ℂ} (hs : b < s.re) :
    MellinConvergent (additiveKernel_ex.choose a r) s :=
  mellinConvergent_of_isBigO_rpow_exp (a := 2 * π) (by positivity)
    ((continuousOn_additiveKernel ha0 hb0 hb2 hS r).locallyIntegrableOn measurableSet_Ioi)
    (isBigO_additiveKernel_atTop ha0 hb0 hb2 hS r) (isBigO_additiveKernel_zero ha0 hb0 hb2 hS r)
    hs

/-- **The Mellin transform of the kernel is the completed additive twist** on `Re s > b`. -/
theorem mellin_additiveKernel (ha0 : a 0 = 0) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) {s : ℂ} (hs : b < s.re) :
    mellin (additiveKernel_ex.choose a r) s = completedAdditiveL_ex.choose a r s := by
  have hs0 : 0 < s.re := hb0.trans_lt hs
  have hsum : Summable fun n : ℕ ↦ ‖additiveTwist_ex.choose a r n‖ / (2 * π * (n : ℝ)) ^ s.re := by
    have h1 := (summable_norm_div_rpow ha0 hS hs.le).mul_left ((2 * π) ^ (-s.re))
    refine h1.congr fun n ↦ ?_
    rw [norm_additiveTwist, Real.mul_rpow (x := 2 * π) (y := (n : ℝ)) (by positivity)
      (by positivity), Real.rpow_neg (by positivity)]
    ring
  have hp : ∀ n : ℕ, additiveTwist_ex.choose a r n = 0 ∨ 0 < 2 * π * (n : ℝ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact Or.inl (by simp [additiveTwist_ex.choose_spec, ha0])
    · exact Or.inr (by positivity)
  have h := hasSum_mellin (a := additiveTwist_ex.choose a r) (p := fun n : ℕ ↦ 2 * π * (n : ℝ))
    (F := additiveKernel_ex.choose a r) (s := s) hp hs0
    (fun t ht ↦ hasSum_additiveKernel ha0 hb0 hb2 hS r ht) hsum
  rw [← h.tsum_eq, completedAdditiveL_ex.choose_spec, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [additiveTwist_ex.choose_spec, ha0]
  · rw [LSeries.term_of_ne_zero hn]
    have e : ((2 * π * (n : ℝ) : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) * ((n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, mul_cpow_ofReal_nonneg (by positivity) (by positivity), cpow_neg, ofReal_natCast]
    ring

/-- On a vertical line `Re s = σ ≥ b` the completed additive twist is bounded by a constant
times `‖Γ(s)‖`. -/
theorem norm_completedAdditiveL_le (ha0 : a 0 = 0)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (r : ℝ) {σ : ℝ} (hσ : b ≤ σ) (s : ℂ)
    (hs : s.re = σ) :
    ‖completedAdditiveL_ex.choose a r s‖ ≤
      ((2 * π) ^ (-σ) * ∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ σ) * ‖Complex.Gamma s‖ := by
  have hterm : ∀ n : ℕ, ‖LSeries.term (additiveTwist_ex.choose a r) s n‖ = ‖a n‖ / (n : ℝ) ^ σ := by
    intro n
    rw [LSeries.norm_term_eq, hs, norm_additiveTwist]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    · simp [hn]
  have hsum : Summable fun n : ℕ ↦ ‖LSeries.term (additiveTwist_ex.choose a r) s n‖ := by
    simp only [hterm]
    exact summable_norm_div_rpow ha0 hS hσ
  have hL : ‖LSeries (additiveTwist_ex.choose a r) s‖ ≤ ∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ σ := by
    calc ‖LSeries (additiveTwist_ex.choose a r) s‖ ≤ ∑' n : ℕ, ‖LSeries.term (additiveTwist_ex.choose a r) s n‖ :=
          norm_tsum_le_tsum_norm hsum
      _ = _ := by simp only [hterm]
  rw [completedAdditiveL_ex.choose_spec, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (by positivity),
    neg_re, hs]
  have h0 : 0 ≤ (2 * π) ^ (-σ) * ‖Complex.Gamma s‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL h0]

end Kernel

/- ### The reflected kernel -/

/-- `reflectKernel q K y = -(q y²)⁻¹ K(1 / (q y))`, written so that Mathlib's change of
variables lemmas for the Mellin transform apply. -/
theorem reflectKernel_ex : ∃ R : ℝ → (ℝ → ℂ) → ℝ → ℂ, ∀ (q : ℝ) (K : ℝ → ℂ) (t : ℝ),
    R q K t = (-(q : ℂ)⁻¹) • ((t : ℂ) ^ (-2 : ℂ) • K ((q * t) ^ (-1 : ℝ))) :=
  ⟨fun q K t ↦ (-(q : ℂ)⁻¹) • ((t : ℂ) ^ (-2 : ℂ) • K ((q * t) ^ (-1 : ℝ))), fun _ _ _ ↦ rfl⟩

theorem reflectKernel_fun (q : ℝ) (K : ℝ → ℂ) :
    reflectKernel_ex.choose q K = fun t : ℝ ↦ (-(q : ℂ)⁻¹) • ((t : ℂ) ^ (-2 : ℂ) • K ((q * t) ^ (-1 : ℝ))) :=
  funext fun t ↦ reflectKernel_ex.choose_spec q K t

theorem reflectKernel_apply {q : ℝ} (hq : 0 < q) (K : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    reflectKernel_ex.choose q K t = -K (1 / (q * t)) / ((q * t ^ 2 : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hq0 : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  have h2 : (t : ℂ) ^ (-2 : ℂ) = ((t : ℂ) ^ 2)⁻¹ := by
    rw [cpow_neg, Complex.cpow_ofNat]
  rw [reflectKernel_ex.choose_spec, Real.rpow_neg_one, one_div, h2, smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp

/-- **The Mellin transform of the reflected kernel.** -/
theorem mellin_reflectKernel {q : ℝ} (hq : 0 < q) (K : ℝ → ℂ) (s : ℂ) :
    mellin (reflectKernel_ex.choose q K) s = -(q : ℂ) ^ (1 - s) * mellin K (2 - s) := by
  have hq0 : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  have he : (s + -2) / ((-1 : ℝ) : ℂ) = 2 - s := by
    push_cast
    ring
  have h1 : mellin (fun t : ℝ ↦ K (t ^ (-1 : ℝ))) (s + -2) = mellin K (2 - s) := by
    rw [mellin_comp_rpow, he]
    simp
  have h2 : mellin (fun t : ℝ ↦ K ((q * t) ^ (-1 : ℝ))) (s + -2) =
      (q : ℂ) ^ (-(s + -2)) • mellin K (2 - s) := by
    rw [← h1]
    exact mellin_comp_mul_left (fun t : ℝ ↦ K (t ^ (-1 : ℝ))) (s + -2) hq
  have h3 : mellin (fun t : ℝ ↦ (t : ℂ) ^ (-2 : ℂ) • K ((q * t) ^ (-1 : ℝ))) s =
      mellin (fun t : ℝ ↦ K ((q * t) ^ (-1 : ℝ))) (s + -2) :=
    mellin_cpow_smul _ s (-2)
  have h4 : mellin (reflectKernel_ex.choose q K) s =
      (-(q : ℂ)⁻¹) • mellin (fun t : ℝ ↦ (t : ℂ) ^ (-2 : ℂ) • K ((q * t) ^ (-1 : ℝ))) s := by
    rw [reflectKernel_fun]
    exact mellin_const_smul _ s (-(q : ℂ)⁻¹)
  rw [h4, h3, h2, smul_eq_mul, smul_eq_mul]
  have h5 : (q : ℂ) ^ (1 - s) = (q : ℂ)⁻¹ * (q : ℂ) ^ (-(s + -2)) := by
    rw [← cpow_neg_one, ← cpow_add _ _ hq0]
    congr 1
    ring
  rw [h5]
  ring

theorem mellinConvergent_reflectKernel {q : ℝ} (hq : 0 < q) (K : ℝ → ℂ) (s : ℂ)
    (h : MellinConvergent K (2 - s)) : MellinConvergent (reflectKernel_ex.choose q K) s := by
  have he : (s + -2) / ((-1 : ℝ) : ℂ) = 2 - s := by
    push_cast
    ring
  have h1 : MellinConvergent (fun t : ℝ ↦ K (t ^ (-1 : ℝ))) (s + -2) := by
    rw [MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0), he]
    exact h
  have h2 : MellinConvergent (fun t : ℝ ↦ K ((q * t) ^ (-1 : ℝ))) (s + -2) :=
    (MellinConvergent.comp_mul_left (f := fun t : ℝ ↦ K (t ^ (-1 : ℝ))) hq).mpr h1
  have h3 : MellinConvergent (fun t : ℝ ↦ (t : ℂ) ^ (-2 : ℂ) • K ((q * t) ^ (-1 : ℝ))) s :=
    MellinConvergent.cpow_smul.mpr h2
  rw [reflectKernel_fun]
  exact h3.const_smul (-(q : ℂ)⁻¹)

theorem continuousAt_reflectKernel {q : ℝ} (hq : 0 < q) {K : ℝ → ℂ}
    (hK : ContinuousOn K (Ioi 0)) {x : ℝ} (hx : 0 < x) : ContinuousAt (reflectKernel_ex.choose q K) x := by
  have hne : q * x ≠ 0 := (mul_pos hq hx).ne'
  have h1 : ContinuousAt (fun t : ℝ ↦ 1 / (q * t)) x :=
    continuousAt_const.div (continuousAt_const.mul continuousAt_id) hne
  have hpos : (0 : ℝ) < 1 / (q * x) := by positivity
  have h2 : ContinuousAt K (1 / (q * x)) := hK.continuousAt (Ioi_mem_nhds hpos)
  have h3 : ContinuousAt (fun t : ℝ ↦ K (1 / (q * t))) x :=
    ContinuousAt.comp (g := K) (f := fun t : ℝ ↦ 1 / (q * t)) h2 h1
  have hden : ((q * x ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have h4 : ContinuousAt (fun t : ℝ ↦ -K (1 / (q * t)) / ((q * t ^ 2 : ℝ) : ℂ)) x :=
    h3.neg.div (by fun_prop) hden
  refine h4.congr ?_
  filter_upwards [Ioi_mem_nhds hx] with t ht
  exact (reflectKernel_apply hq K ht).symm

/- ### The kernel identity as a reflection -/

/-- The kernel identity for `γ = [A, B; C, D]` says that `K_{-D/C}` is the reflection of
`K_{A/C}` with parameter `C²`. -/
theorem kernelIdentity_iff_reflectKernel (a : ℕ → ℂ) (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    (∀ y : ℝ, 0 < y →
      additiveKernel_ex.choose a (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) (1 / (((γ 1 0 : ℤ) : ℝ) ^ 2 * y)) =
        -((((γ 1 0 : ℤ) : ℝ) * y) ^ 2 : ℝ) *
          additiveKernel_ex.choose a (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y) ↔ ∀ y : ℝ, 0 < y →
      additiveKernel_ex.choose a (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) y =
        reflectKernel_ex.choose (((γ 1 0 : ℤ) : ℝ) ^ 2)
          (additiveKernel_ex.choose a (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ))) y := by
  have hc' : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
  have hq : 0 < ((γ 1 0 : ℤ) : ℝ) ^ 2 := by positivity
  refine forall₂_congr fun y hy ↦ ?_
  have hcy : ((((γ 1 0 : ℤ) : ℝ) ^ 2 * y ^ 2 : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (by positivity)
  rw [reflectKernel_apply hq _ hy, eq_div_iff hcy]
  constructor
  · intro h
    rw [h]
    push_cast
    ring
  · intro h
    have h' := congr_arg Neg.neg h
    rw [neg_neg] at h'
    rw [← h']
    push_cast
    ring

end MellinKernel

/- ## The Hecke converse -/

section HeckeConverse

open Complex Filter Set MeasureTheory Function CongruenceSubgroup WeierstrassCurve
  Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Topology Real MatrixGroups ModularForm Manifold

variable {a : ℕ → ℂ} {b : ℝ}

/-- **Hecke's converse argument for one pair of additive twists.** Let `Λ` be holomorphic in
the open strip `2 - σ < Re s < σ`, continuous on its closure and bounded on it, equal to the
completed twist at `r₁` on the right edge and to the reflected completed twist at `r₂` on the
left edge. Then `K_{r₁} = reflectKernel q K_{r₂}` on `(0, ∞)`. Vertical integrability on the two
edges and the decay `Λ(s) = O(1 / |Im s|)` in the strip are proved, not assumed: the first from
`|Γ(s)| |s|² ≤ Γ(Re s + 2)`, the second from Phragmén–Lindelöf. -/
theorem additiveKernel_eq_reflectKernel_of_continuation (ha0 : a 0 = 0) (hb0 : 0 ≤ b)
    (hb2 : b ≤ 2) (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) {q r₁ r₂ σ : ℝ} {Λ : ℂ → ℂ}
    (hq : 0 < q) (hσb : b < σ) (hσ1 : 1 < σ) (hdc : DiffContOnCl ℂ Λ (Complex.re ⁻¹' Ioo (2 - σ) σ))
    (hbd : ∃ M, ∀ s : ℂ, s.re ∈ Ioo (2 - σ) σ → ‖Λ s‖ ≤ M)
    (her : ∀ s : ℂ, s.re = σ → Λ s = completedAdditiveL_ex.choose a r₁ s)
    (hel : ∀ s : ℂ, s.re = 2 - σ → Λ s = -(q : ℂ) ^ (1 - s) * completedAdditiveL_ex.choose a r₂ (2 - s))
    {y : ℝ} (hy : 0 < y) :
    additiveKernel_ex.choose a r₁ y = reflectKernel_ex.choose q (additiveKernel_ex.choose a r₂) y := by
  have hσ0 : 0 < σ := by linarith
  have hlt : 2 - σ < σ := by linarith
  have hcl : closure (Complex.re ⁻¹'Ioo (2 - σ) σ) = Complex.re ⁻¹'Icc (2 - σ) σ := by
    rw [closure_preimage_re, closure_Ioo hlt.ne]
  have hc : ContinuousOn Λ (Complex.re ⁻¹'Icc (2 - σ) σ) := hcl ▸ hdc.continuousOn
  have hd := hdc.differentiableOn
  -- the two edges are Mellin transforms
  have hF : ∀ s : ℂ, s.re = σ → Λ s = mellin (additiveKernel_ex.choose a r₁) s := fun s hs ↦ by
    rw [her s hs, mellin_additiveKernel ha0 hb0 hb2 hS r₁ (by rw [hs]; exact hσb)]
  have hG : ∀ s : ℂ, s.re = 2 - σ →
      Λ s = mellin (reflectKernel_ex.choose q (additiveKernel_ex.choose a r₂)) s := fun s hs ↦ by
    have h2 : b < (2 - s).re := by
      have : (2 - s).re = σ := by simp [hs]
      rw [this]
      exact hσb
    rw [hel s hs, mellin_reflectKernel hq, mellin_additiveKernel ha0 hb0 hb2 hS r₂ h2]
  -- bounds on the edges
  obtain ⟨S, hS0, hSdef⟩ : ∃ S : ℝ, 0 ≤ S ∧
      S = (2 * π) ^ (-σ) * ∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ σ :=
    ⟨_, mul_nonneg (by positivity) (tsum_nonneg fun n ↦ by positivity), rfl⟩
  have hqσ : 0 ≤ q ^ (σ - 1) := Real.rpow_nonneg hq.le _
  have bR : ∀ s : ℂ, s.re = σ → ‖Λ s‖ ≤ S * ‖Complex.Gamma s‖ := fun s hs ↦ by
    rw [hSdef, her s hs]
    exact norm_completedAdditiveL_le ha0 hS r₁ hσb.le s hs
  have bL : ∀ s : ℂ, s.re = 2 - σ → ‖Λ s‖ ≤ q ^ (σ - 1) * S * ‖Complex.Gamma (2 - s)‖ :=
    fun s hs ↦ by
      have h2 : (2 - s).re = σ := by simp [hs]
      have h3 : (1 - s).re = σ - 1 := by
        simp [hs]
        ring
      rw [hel s hs, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hq, h3, mul_assoc (q ^ (σ - 1)),
        hSdef]
      exact mul_le_mul_of_nonneg_left (norm_completedAdditiveL_le ha0 hS r₂ hσb.le _ h2) hqσ
  -- vertical integrability on the edges
  have hGam := norm_Gamma_le_inv_one_add_sq hσ0
  have hmeas : ∀ σ' ∈ Icc (2 - σ) σ, Continuous fun t : ℝ ↦ Λ ((σ' : ℂ) + t * I) :=
    fun σ' h' ↦ hc.comp_continuous (by fun_prop) fun t ↦ by simpa using h'
  have h1 : VerticalIntegrable Λ σ := by
    show Integrable fun t : ℝ ↦ Λ ((σ : ℂ) + t * I)
    refine Integrable.mono'
      (g := fun t : ℝ ↦ S * (Real.Gamma (σ + 2) / min 1 (σ ^ 2) * (1 + t ^ 2)⁻¹))
      ((integrable_inv_one_add_sq.const_mul _).const_mul S)
      (hmeas σ ⟨hlt.le, le_rfl⟩).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    have hs : ((σ : ℂ) + t * I).re = σ := by simp
    have h3 := hGam _ hs
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [him] at h3
    exact (bR _ hs).trans (mul_le_mul_of_nonneg_left h3 hS0)
  have h2 : VerticalIntegrable Λ (2 - σ) := by
    show Integrable fun t : ℝ ↦ Λ (((2 - σ : ℝ) : ℂ) + t * I)
    refine Integrable.mono'
      (g := fun t : ℝ ↦ q ^ (σ - 1) * S * (Real.Gamma (σ + 2) / min 1 (σ ^ 2) * (1 + t ^ 2)⁻¹))
      ((integrable_inv_one_add_sq.const_mul _).const_mul _)
      (hmeas (2 - σ) ⟨le_rfl, hlt.le⟩).aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
    have hs : (((2 - σ : ℝ) : ℂ) + t * I).re = 2 - σ := by simp
    have hs' : (2 - (((2 - σ : ℝ) : ℂ) + t * I)).re = σ := by simp
    have h3 := hGam _ hs'
    have him : (2 - (((2 - σ : ℝ) : ℂ) + t * I)).im = -t := by simp
    rw [him, neg_sq] at h3
    exact (bL _ hs).trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg hqσ hS0))
  -- decay in the strip
  have hBR : ∀ s : ℂ, s.re = σ → ‖Λ s‖ * ‖s‖ ≤ S * Real.Gamma (σ + 1) := fun s hs ↦ by
    have h3 := norm_Gamma_mul_norm_le (s := s) (by rw [hs]; exact hσ0)
    rw [hs] at h3
    calc ‖Λ s‖ * ‖s‖ ≤ S * ‖Complex.Gamma s‖ * ‖s‖ :=
          mul_le_mul_of_nonneg_right (bR s hs) (norm_nonneg _)
      _ = S * (‖Complex.Gamma s‖ * ‖s‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hS0
  have hBL : ∀ s : ℂ, s.re = 2 - σ →
      ‖Λ s‖ * ‖s‖ ≤ q ^ (σ - 1) * S * (Real.Gamma (σ + 1) + 2 * Real.Gamma σ) := fun s hs ↦ by
    have hs' : (2 - s).re = σ := by simp [hs]
    have h3 := norm_Gamma_mul_norm_le (s := 2 - s) (by rw [hs']; exact hσ0)
    have h4 := norm_Gamma_le (s := 2 - s) (by rw [hs']; exact hσ0)
    rw [hs'] at h3 h4
    have h5 : ‖s‖ ≤ ‖2 - s‖ + 2 := by
      have h6 := norm_sub_le (2 : ℂ) (2 - s)
      simpa [add_comm] using h6
    have hK : 0 ≤ q ^ (σ - 1) * S := mul_nonneg hqσ hS0
    calc ‖Λ s‖ * ‖s‖ ≤ q ^ (σ - 1) * S * ‖Complex.Gamma (2 - s)‖ * (‖2 - s‖ + 2) :=
          mul_le_mul (bL s hs) h5 (norm_nonneg _) (by positivity)
      _ = q ^ (σ - 1) * S *
          (‖Complex.Gamma (2 - s)‖ * ‖2 - s‖ + 2 * ‖Complex.Gamma (2 - s)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
  have hdecay := decay_of_bounded_strip hlt hdc hbd
    ⟨max (q ^ (σ - 1) * S * (Real.Gamma (σ + 1) + 2 * Real.Gamma σ)) (S * Real.Gamma (σ + 1)),
      fun s hs ↦ by
        rcases hs with hs | hs
        · exact (hBL s hs).trans (le_max_left _ _)
        · exact (hBR s hs).trans (le_max_right _ _)⟩
  have hF' : MellinConvergent (additiveKernel_ex.choose a r₁) (σ : ℂ) :=
    mellinConvergent_additiveKernel ha0 hb0 hb2 hS r₁ (by simpa using hσb)
  have hG' : MellinConvergent (reflectKernel_ex.choose q (additiveKernel_ex.choose a r₂)) ((2 - σ : ℝ) : ℂ) :=
    mellinConvergent_reflectKernel hq _ _
      (mellinConvergent_additiveKernel ha0 hb0 hb2 hS r₂ (by simpa using hσb))
  exact eq_of_mellin_strip hlt.le hF' hG' hc hd hF hG h1 h2 hdecay hy
    ((continuousOn_additiveKernel ha0 hb0 hb2 hS r₁).continuousAt (Ioi_mem_nhds hy))
    (continuousAt_reflectKernel hq (continuousOn_additiveKernel ha0 hb0 hb2 hS r₂) hy)

/-- The completed additive twist, written out. -/
theorem completedAdditiveL_eq (a : ℕ → ℂ) (r : ℝ) (s : ℂ) :
    completedAdditiveL_ex.choose a r s = ((2 * π : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
      LSeries (fun n : ℕ ↦ a n * cexp (2 * π * I * n * r)) s := by
  have h : additiveTwist_ex.choose a r = fun n : ℕ ↦ a n * cexp (2 * π * I * n * r) :=
    funext fun n ↦ additiveTwist_ex.choose_spec a r n
  rw [completedAdditiveL_ex.choose_spec, h]

/-- **Hecke converse for one matrix.** For `γ = [A, B; C, D]` with `C ≠ 0`, a function on the
strip `2 - σ ≤ Re s ≤ σ` that interpolates between the completed twist at `-D/C` on the right
edge and `-(C²) ^ (1 - s)` times the completed twist at `A/C`, evaluated at `2 - s`, on the left
edge gives the weight-two transformation identity of the q-series under `γ`. -/
theorem qSeries_slash_of_functionalEquation {a : ℕ → ℂ} {b : ℝ} (ha0 : a 0 = 0) (hb0 : 0 ≤ b)
    (hb2 : b ≤ 2) (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) {σ : ℝ} (hσb : b < σ) (hσ1 : 1 < σ) {Λ : ℂ → ℂ}
    (hdc : DiffContOnCl ℂ Λ (Complex.re ⁻¹' Ioo (2 - σ) σ))
    (hbd : ∃ M, ∀ s : ℂ, s.re ∈ Ioo (2 - σ) σ → ‖Λ s‖ ≤ M)
    (her : ∀ s : ℂ, s.re = σ →
      Λ s = completedAdditiveL_ex.choose a (-((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) s)
    (hel : ∀ s : ℂ, s.re = 2 - σ →
      Λ s = -((((γ 1 0 : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s) *
        completedAdditiveL_ex.choose a (((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ)) (2 - s)) :
    qSeries_ex.choose a ∣[(2 : ℤ)] γ = qSeries_ex.choose a := by
  have hc' : ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
  have hq : (0 : ℝ) < ((γ 1 0 : ℤ) : ℝ) ^ 2 := by positivity
  exact (qSeries_slash_eq_iff_kernelIdentity ha0 hb0 hb2 hS γ hc).mpr
    ((kernelIdentity_iff_reflectKernel a γ hc).mpr fun y hy ↦
      additiveKernel_eq_reflectKernel_of_continuation ha0 hb0 hb2 hS hq hσb hσ1 hdc hbd her hel hy)

theorem Gamma_le_Gamma0 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ Gamma0 N :=
  fun _ h ↦ Gamma0_mem.mpr (Gamma_mem.mp h).2.2.1

/-- **Automatic cuspidality.** If the coefficients satisfy `a 0 = 0` and
`∑ ‖a n‖ / n ^ b < ∞` for some `1 ≤ b < 2`, and the q-series is weight-two slash invariant
under a subgroup `Γ ⊇ Γ(N)` of `SL(2, ℤ)`, then it is a cusp form for `Γ` with q-expansion
coefficients `a n`: holomorphy and vanishing at every cusp need no further input. -/
theorem exists_cuspForm_of_slashInvariant {a : ℕ → ℂ} {b : ℝ} {N : ℕ} [NeZero N]
    {Γ : Subgroup SL(2, ℤ)} (ha0 : a 0 = 0) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hS : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ b) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (hinv : ∀ γ ∈ Γ, qSeries_ex.choose a ∣[(2 : ℤ)] γ = qSeries_ex.choose a) :
    ∃ f : CuspForm (Γ.map (mapGL ℝ)) 2, ∀ n : ℕ, (qExpansion 1 f).coeff n = a n := by
  have hb0 : 0 ≤ b := by linarith
  let f : CuspForm (Γ.map (mapGL ℝ)) 2 :=
    { toFun := qSeries_ex.choose a
      slash_action_eq' := by rintro _ ⟨δ, hδ, rfl⟩; exact hinv δ hδ
      holo' := qSeries_mdifferentiable ha0 hb0 hb2.le hS
      zero_at_cusps' := fun {c} hc ↦ by
        have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
        have hc' := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
        rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
        intro γ _
        exact isZeroAtImInfty_slash_of_bound hb1 hb2 (Nat.cast_pos.mpr (NeZero.pos N))
          (qSeries_norm_le ha0 hb0 hb2.le hS) γ (slash_periodic_of_Gamma_le hΓ hinv γ) }
  refine ⟨f, fun n ↦ ?_⟩
  have han : AnalyticAt ℂ (cuspFunction 1 (qSeries_ex.choose a)) 0 :=
    analyticAt_cuspFunction_zero one_pos (qSeries_periodic a)
      (qSeries_mdifferentiable ha0 hb0 hb2.le hS)
      (qSeries_isZeroAtImInfty ha0 hb0 hb2.le hS (by linarith)).isBoundedAtImInfty
  exact qExpansion_coeff_of_hasSum han (qSeries_hasSum ha0 hb0 hb2.le hS) n

theorem main : H1 → H2 → OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1.H2 := by
  intro h1 h2 E _
  obtain ⟨hsum, hcont⟩ := h1 E
  obtain ⟨N, hN, hfe⟩ := h2 E
  have : NeZero N := ⟨hN.ne'⟩
  have ha0 : (fun n : ℕ ↦ (E.LFunction n : ℂ)) 0 = 0 := by simp
  have hS : Summable fun n : ℕ ↦
      ‖(fun n : ℕ ↦ (E.LFunction n : ℂ)) n‖ / (n : ℝ) ^ (7 / 4 : ℝ) := by
    have h := hsum ((7 / 4 : ℝ) : ℂ) (by rw [Complex.ofReal_re]; norm_num)
    refine h.norm.congr fun n ↦ ?_
    rw [LSeries.norm_term_eq, Complex.ofReal_re]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn]
  have hinv : ∀ γ ∈ Gamma0 N,
      qSeries_ex.choose (fun n : ℕ ↦ (E.LFunction n : ℂ)) ∣[(2 : ℤ)] γ =
        qSeries_ex.choose (fun n : ℕ ↦ (E.LFunction n : ℂ)) := by
    intro γ hγ
    by_cases hc : γ 1 0 = 0
    · exact qSeries_slash_of_lowerLeft_eq_zero _ γ hc
    · obtain ⟨L₁, hd₁, ⟨M, hM⟩, he₁⟩ := hcont (-((γ 1 1 : ℤ) : ℚ) / ((γ 1 0 : ℤ) : ℚ))
      obtain ⟨L₂, hd₂, -, he₂⟩ := hcont (((γ 0 0 : ℤ) : ℚ) / ((γ 1 0 : ℤ) : ℚ))
      have hr₁ : ((-((γ 1 1 : ℤ) : ℚ) / ((γ 1 0 : ℤ) : ℚ) : ℚ) : ℝ) =
          -((γ 1 1 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ) := by push_cast; ring
      have hr₂ : ((((γ 0 0 : ℤ) : ℚ) / ((γ 1 0 : ℤ) : ℚ) : ℚ) : ℝ) =
          ((γ 0 0 : ℤ) : ℝ) / ((γ 1 0 : ℤ) : ℝ) := by push_cast; ring
      rw [hr₁] at he₁
      rw [hr₂] at he₂
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := γ.det_coe
        rw [Matrix.det_fin_two] at h
        exact h
      have hdvd : (N : ℤ) ∣ γ 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp hγ)
      have hfe' := hfe (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) hdet hdvd hc L₁ L₂ hd₁ hd₂ he₁ he₂
      refine qSeries_slash_of_functionalEquation (b := 7 / 4) (σ := 2) (Λ := L₁) ha0
        (by norm_num) (by norm_num) hS γ hc (by norm_num) (by norm_num) hd₁.diffContOnCl
        ⟨M, fun s hs ↦ hM s ⟨by linarith [hs.1], hs.2.le⟩⟩ (fun s hs ↦ ?_) (fun s hs ↦ ?_)
      · rw [completedAdditiveL_eq]
        exact he₁ s (by rw [hs]; norm_num)
      · have h2 : (3 / 2 : ℝ) < (2 - s).re := by
          rw [Complex.sub_re, hs]
          norm_num
        rw [hfe' s, he₂ (2 - s) h2, completedAdditiveL_eq]
  obtain ⟨f, hf⟩ := exists_cuspForm_of_slashInvariant ha0 (by norm_num) (by norm_num) hS
    (Gamma_le_Gamma0 N) hinv
  exact ⟨N, hN, f, fun n _ ↦ hf n⟩

end HeckeConverse

end OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1_H2_R1
