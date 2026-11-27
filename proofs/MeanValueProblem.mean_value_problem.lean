import FormalConjectures.Wikipedia.MeanValueProblem
import Mathlib

/-! A polynomial counterexample constructed from a cubic lemniscate. -/

open Polynomial Filter Set Metric
open scoped Topology NNReal BigOperators

namespace MVPProof

noncomputable section

private def s : ℝ := Real.sqrt 1297
private def b : ℂ := 36 * Complex.I
private def a : ℂ := 13 / 12 + 3 * Complex.I
private def q : ℂ[X] := (X ^ 3 + C b) * C (s : ℂ)⁻¹
private def D (z : ℂ) : ℂ := 1 + b * z ^ 3
private def α : ℂ := b / (s : ℂ)
private def g (u : ℂ) : ℂ := Complex.exp (-(1 / 3 : ℂ) * Complex.log (1 + α * u))
private def V (z : ℂ) : ℂ :=
  Complex.exp ((1 / 3 : ℂ) * Complex.log (D 1 / 1297)) * g (q.eval z)
private def W (z : ℂ) : ℂ := z * V z
private def Wd (z : ℂ) : ℂ := V z / D z
private def K : Set ℂ := {z | ‖q.eval z‖ ≤ 1}

private lemma s_sq : s ^ 2 = 1297 := Real.sq_sqrt (by norm_num)
private lemma s_pos : 0 < s := Real.sqrt_pos.2 (by norm_num)
private lemma s_gt : 36 < s := by nlinarith [s_sq, s_pos]
private lemma s_ne : (s : ℂ) ≠ 0 := by exact_mod_cast s_pos.ne'
private lemma cs_sq : (s : ℂ) ^ 2 = 1297 := by exact_mod_cast s_sq

private lemma b_sq : b ^ 2 = -1296 := by
  simp [b, mul_pow, Complex.I_sq]
  norm_num

private lemma b_norm : ‖b‖ = 36 := by norm_num [b, norm_mul]

private lemma Db_norm : ‖1 + b‖ = s := by
  have h : ‖1 + b‖ ^ 2 = 1297 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, b, Complex.mul_re, Complex.mul_im]
  nlinarith [s_sq, s_pos, norm_nonneg (1 + b)]

private lemma q_eval (z : ℂ) : q.eval z = (z ^ 3 + b) / (s : ℂ) := by
  simp [q, div_eq_mul_inv]

private lemma qd_eval (z : ℂ) : q.derivative.eval z = 3 * z ^ 2 / (s : ℂ) := by
  simp [q, derivative_mul, div_eq_mul_inv]
  ring

private lemma q_norm (z : ℂ) : ‖q.eval z‖ = ‖z ^ 3 + b‖ / s := by
  rw [q_eval, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s_pos]

private lemma q_one : ‖q.eval 1‖ = 1 := by
  simp [q_norm, Db_norm, s_pos.ne']

private lemma q_a : ‖q.eval a‖ < 1 := by
  rw [q_norm, div_lt_one s_pos]
  have h : ‖a ^ 3 + b‖ ^ 2 < 1297 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply, a, b, pow_succ,
      div_eq_mul_inv, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  nlinarith [norm_nonneg (a ^ 3 + b), s_sq, s_pos]

private lemma D_id (z : ℂ) : 1 + α * q.eval z = D z / 1297 := by
  have hs : (s : ℂ) * (s : ℂ) = 1297 := by simpa [pow_two] using cs_sq
  rw [α, q_eval, D, div_mul_div_comm, hs]
  linear_combination b_sq / 1297

private lemma α_norm : ‖α‖ = 36 / s := by
  rw [α, norm_div, b_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s_pos]

private lemma radius_gt : (1 : ℝ) < s / 36 := by
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 36)]
  simpa using s_gt

private lemma slit (u : ℂ) (hu : ‖u‖ < s / 36) : 1 + α * u ∈ Complex.slitPlane := by
  have hn : ‖α * u‖ < 1 := by
    rw [norm_mul, α_norm]
    calc
      36 / s * ‖u‖ < 36 / s * (s / 36) :=
        mul_lt_mul_of_pos_left hu (div_pos (by norm_num) s_pos)
      _ = 1 := by field_simp [s_pos.ne']
  have hr := (abs_le.mp (Complex.abs_re_le_norm (α * u))).1
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.add_re, Complex.one_re]
  linarith

private lemma D_ne (z : ℂ) (hz : ‖q.eval z‖ < s / 36) : D z ≠ 0 := by
  have h := Complex.slitPlane_ne_zero (slit _ hz)
  rw [D_id] at h
  exact fun e => h (by simp [e])

private lemma V_ne (z : ℂ) : V z ≠ 0 := by
  unfold V g
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

private lemma W_one : W 1 = 1 := by
  simp only [W, V, g, D_id, one_mul]
  rw [← Complex.exp_add]
  rw [show (1 / 3 : ℂ) * Complex.log (D 1 / 1297) +
    -(1 / 3 : ℂ) * Complex.log (D 1 / 1297) = 0 by ring, Complex.exp_zero]

private lemma W_cube (z : ℂ) (hz : ‖q.eval z‖ < s / 36) :
    W z ^ 3 = (1 + b) * z ^ 3 / D z := by
  have hd := D_ne z hz
  have hd1 : D 1 ≠ 0 := D_ne 1 (q_one ▸ radius_gt)
  have h1 : D 1 / 1297 ≠ 0 := div_ne_zero hd1 (by norm_num)
  have h2 : D z / 1297 ≠ 0 := div_ne_zero hd (by norm_num)
  unfold W V g
  rw [D_id, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  rw [show (3 : ℂ) * (1 / 3 * Complex.log (D 1 / 1297)) =
      Complex.log (D 1 / 1297) by ring,
    show (3 : ℂ) * (-(1 / 3) * Complex.log (D z / 1297)) =
      -(Complex.log (D z / 1297)) by ring,
    Complex.exp_log h1, Complex.exp_neg, Complex.exp_log h2]
  simp only [D, one_pow, mul_one] at *
  field_simp

private lemma norm_identity (v : ℂ) :
    ‖1 + b * v‖ ^ 2 - 1297 * ‖v‖ ^ 2 = 1297 - ‖v + b‖ ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply, b, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im]
  ring

private lemma W_norm_cube (z : ℂ) (hz : ‖q.eval z‖ < s / 36) :
    ‖W z‖ ^ 3 = s * ‖z‖ ^ 3 / ‖D z‖ := by
  rw [← norm_pow, W_cube z hz, norm_div, norm_mul, Db_norm, norm_pow]

private lemma W_norm_le (z : ℂ) (hz : z ∈ K) : ‖W z‖ ≤ 1 := by
  have hq : ‖q.eval z‖ ≤ 1 := hz
  have hr := hq.trans_lt radius_gt
  have hn := norm_identity (z ^ 3)
  rw [norm_pow] at hn
  change ‖D z‖ ^ 2 - 1297 * (‖z‖ ^ 3) ^ 2 = 1297 - ‖z ^ 3 + b‖ ^ 2 at hn
  have hb : ‖z ^ 3 + b‖ ≤ s := by
    rwa [q_norm, div_le_one s_pos] at hq
  have hD : s * ‖z‖ ^ 3 ≤ ‖D z‖ := by
    have hh : (s * ‖z‖ ^ 3) ^ 2 ≤ ‖D z‖ ^ 2 := by
      rw [mul_pow, s_sq]
      have hl := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [s_sq] at hl
      linarith only [hn, hl]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hh
  have hh : ‖W z‖ ^ 3 ≤ 1 ^ 3 := by
    rw [W_norm_cube z hr, one_pow, div_le_one (norm_pos_iff.mpr (D_ne z hr))]
    exact hD
  exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by norm_num) hh

private lemma W_norm_eq (z : ℂ) (hz : ‖q.eval z‖ = 1) : ‖W z‖ = 1 := by
  have hr : ‖q.eval z‖ < s / 36 := hz ▸ radius_gt
  have hb : ‖z ^ 3 + b‖ = s := by rwa [q_norm, div_eq_iff s_pos.ne', one_mul] at hz
  have hn := norm_identity (z ^ 3)
  rw [norm_pow, hb, s_sq, sub_self] at hn
  change ‖D z‖ ^ 2 - 1297 * (‖z‖ ^ 3) ^ 2 = 0 at hn
  have hD : ‖D z‖ = s * ‖z‖ ^ 3 := by
    have hh : ‖D z‖ ^ 2 = (s * ‖z‖ ^ 3) ^ 2 := by
      rw [mul_pow, s_sq]
      linarith
    exact pow_left_inj₀ (norm_nonneg _) (mul_nonneg s_pos.le (by positivity)) two_ne_zero |>.mp hh
  have hp := W_norm_cube z hr
  rw [← hD, div_self (norm_ne_zero_iff.mpr (D_ne z hr))] at hp
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (by simpa using hp)

private lemma W_norm_a : ‖W a‖ < 1 := by
  have hr := q_a.trans radius_gt
  have hb := (div_lt_one s_pos).1 ((q_norm a) ▸ q_a)
  have hn := norm_identity (a ^ 3)
  rw [norm_pow] at hn
  change ‖D a‖ ^ 2 - 1297 * (‖a‖ ^ 3) ^ 2 = 1297 - ‖a ^ 3 + b‖ ^ 2 at hn
  have hD : s * ‖a‖ ^ 3 < ‖D a‖ := by
    have hh : (s * ‖a‖ ^ 3) ^ 2 < ‖D a‖ ^ 2 := by
      rw [mul_pow, s_sq]
      have hl := pow_lt_pow_left₀ hb (norm_nonneg _) two_ne_zero
      rw [s_sq] at hl
      linarith only [hn, hl]
    by_contra! h
    exact hh.not_ge (pow_le_pow_left₀ (norm_nonneg _) h 2)
  have hp := W_norm_cube a hr
  by_contra! h
  have := pow_le_pow_left₀ zero_le_one h 3
  rw [one_pow] at this
  rw [hp] at this
  exact ((div_lt_one (norm_pos_iff.mpr (D_ne a hr))).2 hD).not_ge this

private lemma W_inj_one (z : ℂ) (hz : z ∈ K) (hw : W z = 1) : z = 1 := by
  have hq : ‖q.eval z‖ ≤ 1 := hz
  have hr := hq.trans_lt radius_gt
  have h := W_cube z hr
  rw [hw, one_pow, eq_div_iff (D_ne z hr), one_mul, D] at h
  have hz3 : z ^ 3 = 1 := by linear_combination -h
  have he : q.eval z = q.eval 1 := by simp [q_eval, hz3]
  have hv : V z = V 1 := by simp only [V, he]
  have hv1 : V 1 = 1 := by simpa [W] using W_one
  simpa [W, hv, hv1] using hw

private lemma hasDeriv_g (u : ℂ) (hu : ‖u‖ < s / 36) :
    HasDerivAt g (g u * (-(1 / 3 : ℂ) * ((1 + α * u)⁻¹ * α))) u := by
  have hl := (Complex.hasDerivAt_log (slit u hu)).comp u
    (((hasDerivAt_id u).const_mul α).const_add 1)
  have he : HasDerivAt g _ u := (hl.const_mul (-(1 / 3 : ℂ))).cexp
  change HasDerivAt g
    (g u * (-(1 / 3 : ℂ) * ((1 + α * u)⁻¹ * (α * 1)))) u at he
  rwa [mul_one] at he

private lemma hasDeriv_V (z : ℂ) (hz : ‖q.eval z‖ < s / 36) :
    HasDerivAt V (-V z * (b * z ^ 2) / D z) z := by
  have hh : HasDerivAt V _ z := ((hasDeriv_g _ hz).comp z (q.hasDerivAt z)).const_mul
    (Complex.exp ((1 / 3 : ℂ) * Complex.log (D 1 / 1297)))
  convert hh using 1
  rw [qd_eval, D_id, α]
  have hD := D_ne z hz
  unfold V
  simp only [← div_eq_mul_inv, ← mul_assoc]
  field_simp [s_ne, hD]
  rw [cs_sq]
  ring

private lemma hasDeriv_W (z : ℂ) (hz : ‖q.eval z‖ < s / 36) :
    HasDerivAt W (Wd z) z := by
  have hh : HasDerivAt W _ z := (hasDerivAt_id z).mul (hasDeriv_V z hz)
  convert hh using 1
  change Wd z = 1 * V z + z * (-V z * (b * z ^ 2) / D z)
  unfold Wd
  have hD := D_ne z hz
  field_simp [hD]
  unfold D
  ring

private lemma compact_q (R : ℝ) : IsCompact {z : ℂ | ‖q.eval z‖ ≤ R} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by fun_prop) continuous_const
  · apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := max 1 (R * s + 36))).subset
    intro z hz
    have hq : ‖q.eval z‖ ≤ R := hz
    have hb : ‖z ^ 3 + b‖ ≤ R * s := (div_le_iff₀ s_pos).1 (q_norm z ▸ hq)
    have hn := norm_sub_le (z ^ 3 + b) b
    rw [add_sub_cancel_right, norm_pow, b_norm] at hn
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : ‖z‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · have hp : ‖z‖ ≤ ‖z‖ ^ 3 := by
        simpa using (pow_le_pow_right₀ (le_of_not_ge h) (show 1 ≤ 3 by decide))
      exact hp.trans (le_max_of_le_right (by linarith))

private lemma compact_lower {S : Set ℂ} {u : ℂ → ℝ} (hS : IsCompact S)
    (hu : ContinuousOn u S) (hp : ∀ z ∈ S, 0 < u z) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ S, m ≤ u z := by
  rcases S.eq_empty_or_nonempty with rfl | h
  · exact ⟨1, zero_lt_one, by simp⟩
  obtain ⟨z, hz, hm⟩ := hS.exists_isMinOn h hu
  exact ⟨u z, hp z hz, fun _ hw => hm hw⟩

private lemma compact_upper {S : Set ℂ} {u : ℂ → ℝ} (hS : IsCompact S)
    (hu : ContinuousOn u S) : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ S, u z ≤ M := by
  obtain ⟨M, hM⟩ := hS.bddAbove_image hu
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z hz => ?_⟩
  exact (hM (mem_image_of_mem u hz)).trans (le_max_right _ _)

private lemma Wd_ne (z : ℂ) (hz : z ∈ K) : Wd z ≠ 0 :=
  div_ne_zero (V_ne z) (D_ne z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt))

private lemma V_one : V 1 = 1 := by simpa [W] using W_one

/- Pull back the inverse-coordinate expression to the lemniscate. -/
private def J (z : ℂ) : ℂ := (z - a) * Wd z

private lemma hasDeriv_D (z : ℂ) : HasDerivAt D (3 * b * z ^ 2) z := by
  have h : HasDerivAt D _ z := (((hasDerivAt_id z).pow 3).const_mul b).const_add 1
  convert h using 1
  simp
  ring

private lemma hasDeriv_Wd (z : ℂ) (hz : ‖q.eval z‖ < s / 36) :
    HasDerivAt Wd (-4 * b * z ^ 2 * V z / D z ^ 2) z := by
  have h : HasDerivAt Wd _ z := (hasDeriv_V z hz).div (hasDeriv_D z) (D_ne z hz)
  convert h using 1
  field_simp [D_ne z hz]
  ring

private lemma Wd_one : Wd 1 = (1 + b)⁻¹ := by
  simp [Wd, V_one, D, one_div]

private lemma J_one : J 1 = -(1 / 12 : ℂ) := by
  have hn := D_ne 1 (q_one ▸ radius_gt)
  simp only [D, one_pow, mul_one] at hn
  rw [J, Wd_one, ← div_eq_mul_inv]
  apply (div_eq_iff hn).2
  unfold a b
  ring

private def j : ℂ := 1 + 12 * Complex.I

private lemma hasDeriv_J_one : HasDerivAt J (j * Wd 1) 1 := by
  have h : HasDerivAt J _ 1 :=
    ((hasDerivAt_id (1 : ℂ)).sub_const a).mul (hasDeriv_Wd 1 (q_one ▸ radius_gt))
  convert h using 1
  simp only [id_eq, V_one, D, one_pow, mul_one, one_mul, Wd_one]
  have hb : 1 + b ≠ 0 := by simpa [D] using D_ne 1 (q_one ▸ radius_gt)
  field_simp [hb]
  unfold j a b
  ring

private lemma local_J :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, dist z 1 < δ →
      ‖J z - J 1 - j * (W z - 1)‖ ≤ (1 / 4 : ℝ) * ‖W z - 1‖ := by
  have hw := hasDeriv_W 1 (q_one ▸ radius_gt)
  have hpos : 0 < ‖Wd 1‖ := norm_pos_iff.mpr (Wd_ne 1 (q_one.le))
  have he : HasDerivAt (fun z => J z - j * (W z - 1)) 0 1 := by
    have h : HasDerivAt (fun z => J z - j * (W z - 1)) _ 1 :=
      hasDeriv_J_one.sub ((hw.sub_const 1).const_mul j)
    rwa [sub_self] at h
  have hw' := hw.isLittleO.bound (half_pos hpos)
  have he' := he.isLittleO.bound (show 0 < ‖Wd 1‖ / 8 by positivity)
  have h := hw'.and he'
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ, hδ, fun z hz => ?_⟩
  obtain ⟨h₁, h₂⟩ := hball (show z ∈ ball 1 δ from hz)
  have ht := norm_sub_norm_le ((z - 1) * Wd 1) (W z - 1)
  rw [norm_mul, norm_sub_rev ((z - 1) * Wd 1)] at ht
  simp only [W_one, smul_eq_mul] at h₁
  simp only [W_one, sub_self, mul_zero, sub_zero, smul_zero] at h₂
  rw [show J z - J 1 - j * (W z - 1) = J z - j * (W z - 1) - J 1 by ring]
  nlinarith only [h₁, h₂, ht]

private def N (ε : ℝ) (z : ℂ) : ℂ :=
  -(1 - (ε : ℂ)) * (W z - 1) ^ 2 + (ε : ℂ) ^ 2 * W z +
    (ε * (2 - ε) : ℝ) * J z

private lemma disk_re (w : ℂ) (hw : ‖w‖ ≤ 1) : (w - 1).re ≤ 0 := by
  have h := (abs_le.mp (Complex.abs_re_le_norm w)).2
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private lemma local_N_ne (ε : ℝ) (hε : 0 < ε) (ht : ε < 1 / 10) (z : ℂ)
    (hw : ‖W z‖ ≤ 1)
    (hJ : ‖J z - J 1 - j * (W z - 1)‖ ≤ (1 / 4 : ℝ) * ‖W z - 1‖) :
    N ε z ≠ 0 := by
  let x := W z - 1
  let R := J z - J 1 - j * x
  let t : ℝ := ε * (2 - ε)
  have htpos : 0 < t := mul_pos hε (by linarith)
  let A : ℝ := t / 12 - ε ^ 2
  have hA : 0 < A := by
    change 0 < ε * (2 - ε) / 12 - ε ^ 2
    nlinarith [mul_pos hε (show 0 < 2 - 13 * ε by linarith)]
  have hR : ‖R‖ ≤ (1 / 4 : ℝ) * ‖x‖ := hJ
  have hW : W z = 1 + x := by dsimp [x]; ring
  have hJz : J z = -(1 / 12 : ℂ) + j * x + R := by dsimp [R]; rw [J_one]; ring
  intro hN
  have heq : (1 - (ε : ℂ)) * x ^ 2 + (A : ℂ) =
      (t : ℂ) * (j * x + R) + (ε : ℂ) ^ 2 * x := by
    unfold N at hN
    change -(1 - (ε : ℂ)) * x ^ 2 + (ε : ℂ) ^ 2 * W z + (t : ℂ) * J z = 0 at hN
    rw [hW, hJz] at hN
    dsimp [A]
    push_cast
    linear_combination -hN
  have hx : x ≠ 0 := by
    intro hx
    have he := hR
    rw [hx, norm_zero, mul_zero, norm_le_zero_iff] at he
    have hzero : (A : ℂ) = 0 := by simpa [hx, he] using heq
    exact hA.ne' (by exact_mod_cast hzero)
  have hdiv : (1 - (ε : ℂ)) * x + (A : ℂ) * x⁻¹ =
      (t : ℂ) * (j + R / x) + (ε : ℂ) ^ 2 := by
    field_simp [hx]
    linear_combination heq
  have hxr : x.re ≤ 0 := disk_re _ hw
  have hxi : x⁻¹.re ≤ 0 := by
    rw [Complex.inv_re]
    exact div_nonpos_of_nonpos_of_nonneg hxr (Complex.normSq_nonneg _)
  have hsmall : ‖R / x‖ ≤ 1 / 4 := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hx)]
    exact hR
  have hp : 0 < 1 + (R / x).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm (R / x))).1
    linarith
  have hre := congrArg Complex.re hdiv
  have hj : j.re = 1 := by norm_num [j, Complex.mul_re]
  rw [show (1 - (ε : ℂ)) * x = ((1 - ε : ℝ) : ℂ) * x by push_cast; ring,
    ← Complex.ofReal_pow] at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hj] at hre
  have hleft := add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - ε) hxr)
    (mul_nonpos_of_nonneg_of_nonpos hA.le hxi)
  have hright := add_pos_of_pos_of_nonneg (mul_pos htpos hp) (sq_nonneg ε)
  linarith only [hre, hleft, hright]

private lemma small_N :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 10 ∧ ‖W a‖ < 1 - ε ∧ ∀ z ∈ K, N ε z ≠ 0 := by
  have hK : IsCompact K := compact_q 1
  have hV : ContinuousOn V K := fun z hz =>
    (hasDeriv_V z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)).continuousAt.continuousWithinAt
  have hD : Continuous D := by unfold D; fun_prop
  have hWd : ContinuousOn Wd K := hV.div hD.continuousOn fun z hz =>
    D_ne z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)
  have hJ : ContinuousOn J K := (show ContinuousOn (fun z : ℂ => z - a) K by fun_prop).mul hWd
  have hW : ContinuousOn W K := continuous_id.continuousOn.mul hV
  obtain ⟨δ, hδ, hloc⟩ := local_J
  let S := K ∩ (ball (1 : ℂ) δ)ᶜ
  have hS : IsCompact S := hK.inter_right isOpen_ball.isClosed_compl
  obtain ⟨m, hm, hml⟩ := compact_lower hS
    ((hW.mono inter_subset_left).sub continuous_const.continuousOn).norm (by
      intro z hz
      apply norm_pos_iff.mpr
      intro he
      have hz1 := W_inj_one z hz.1 (sub_eq_zero.mp he)
      exact hz.2 (hz1 ▸ mem_ball_self hδ))
  obtain ⟨M, hM, hMb⟩ := compact_upper hK hJ.norm
  let eta := min (1 / 10) (min (1 - ‖W a‖) (m ^ 2 / (4 * (1 + 2 * M))))
  have heta : 0 < eta := lt_min (by norm_num) (lt_min (by linarith [W_norm_a]) (by positivity))
  obtain ⟨ε, hε, hεη⟩ := exists_between heta
  have ht : ε < 1 / 10 := hεη.trans_le (min_le_left _ _)
  have ha : ε < 1 - ‖W a‖ := hεη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he : ε < m ^ 2 / (4 * (1 + 2 * M)) :=
    hεη.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, ht, by linarith, fun z hz => ?_⟩
  by_cases hzδ : z ∈ ball (1 : ℂ) δ
  · exact local_N_ne ε hε ht z (W_norm_le z hz) (hloc z hzδ)
  intro hN
  have hx : m ≤ ‖W z - 1‖ := hml z ⟨hz, hzδ⟩
  have heq : (1 - (ε : ℂ)) * (W z - 1) ^ 2 =
      (ε : ℂ) ^ 2 * W z + ((ε * (2 - ε) : ℝ) : ℂ) * J z := by
    unfold N at hN
    linear_combination -hN
  have hn := norm_add_le ((ε : ℂ) ^ 2 * W z) (((ε * (2 - ε) : ℝ) : ℂ) * J z)
  rw [← heq, show 1 - (ε : ℂ) = ((1 - ε : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_pow] at hn
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [abs_of_pos (show 0 < 1 - ε by linarith), abs_of_pos hε,
    abs_of_pos (show 0 < 2 - ε by linarith)] at hn
  have hl := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm.le hx 2)
    (show 0 ≤ 1 - ε by linarith)
  have hr₁ := mul_le_of_le_one_right (sq_nonneg ε) (W_norm_le z hz)
  have hr₂ := mul_le_mul_of_nonneg_left (hMb z hz)
    (mul_nonneg hε.le (show 0 ≤ 2 - ε by linarith))
  have he' := (lt_div_iff₀ (show 0 < 4 * (1 + 2 * M) by positivity)).1 he
  have hp := mul_pos (show 0 < 1 - ε by linarith) hε
  have hq := mul_nonneg (sq_nonneg ε) hM.le
  have hs := mul_pos (show 0 < 3 / 4 - ε by linarith) (sq_pos_of_pos hm)
  nlinarith only [hn, hl, hr₁, hr₂, he', hp, hq, hs]

private def B (r : ℝ) (w : ℂ) : ℂ := (w - (r : ℂ)) / (1 - (r : ℂ) * w)
private def Bd (r : ℝ) (w : ℂ) : ℂ := (1 - (r : ℂ) ^ 2) / (1 - (r : ℂ) * w) ^ 2

private lemma B_den (r : ℝ) (hr : 0 < r) (w : ℂ) (hw : r * ‖w‖ < 1) :
    1 - (r : ℂ) * w ≠ 0 := by
  intro he
  have h := congrArg norm (sub_eq_zero.mp he)
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  linarith

private lemma hasDeriv_B (r : ℝ) (hr : 0 < r) (w : ℂ) (hw : r * ‖w‖ < 1) :
    HasDerivAt (B r) (Bd r w) w := by
  have h : HasDerivAt (B r) _ w := ((hasDerivAt_id w).sub_const (r : ℂ)).div
    (((hasDerivAt_id w).const_mul (r : ℂ)).const_sub 1) (B_den r hr w hw)
  convert h using 1
  unfold Bd
  congr 1
  simp
  ring

private lemma B_id (r : ℝ) (w : ℂ) :
    ‖1 - (r : ℂ) * w‖ ^ 2 - ‖w - (r : ℂ)‖ ^ 2 =
      (1 - r ^ 2) * (1 - ‖w‖ ^ 2) := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im]
  ring

private lemma B_norm_eq (r : ℝ) (hr : 0 < r) (hr' : r < 1) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖B r w‖ = 1 := by
  have h := B_id r w
  rw [hw] at h
  have he : ‖w - (r : ℂ)‖ = ‖1 - (r : ℂ) * w‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by linarith)
  have hd := B_den r hr w (by simpa [hw] using hr')
  rw [B, norm_div, he, div_self (norm_ne_zero_iff.mpr hd)]

private lemma B_norm_lt (r : ℝ) (hr : 0 < r) (hr' : r < 1) (w : ℂ) (hw : ‖w‖ < 1) :
    ‖B r w‖ < 1 := by
  have hd := B_den r hr w (by nlinarith [mul_pos hr (sub_pos.mpr hw)])
  rw [B, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have hp := mul_pos (show 0 < 1 - r ^ 2 by nlinarith) (show 0 < 1 - ‖w‖ ^ 2 by
    nlinarith [norm_nonneg w])
  have hn := B_id r w
  by_contra! he
  have hh := pow_le_pow_left₀ (norm_nonneg _) he 2
  linarith only [hp, hn, hh]

private def H (r : ℝ) (z : ℂ) : ℂ := B r (W z)
private def Hd (r : ℝ) (z : ℂ) : ℂ := Bd r (W z) * Wd z

private lemma H_deriv (r : ℝ) (hr : 0 < r) (hr' : r < 1) (z : ℂ) (hz : z ∈ K) :
    HasDerivAt (H r) (Hd r z) z :=
  (hasDeriv_B r hr (W z) ((mul_le_of_le_one_right hr.le (W_norm_le z hz)).trans_lt hr')).comp z
    (hasDeriv_W z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt))

private lemma H_nonzero_model (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10)
    (hN : ∀ z ∈ K, N ε z ≠ 0) (z : ℂ) (hz : z ∈ K) :
    H (1 - ε) z + (z - a) * Hd (1 - ε) z ≠ 0 := by
  have hr : 0 < 1 - ε := by linarith
  have hd := B_den (1 - ε) hr (W z)
    ((mul_le_of_le_one_right hr.le (W_norm_le z hz)).trans_lt (by linarith))
  have he : H (1 - ε) z + (z - a) * Hd (1 - ε) z =
    N ε z / (1 - ((1 - ε : ℝ) : ℂ) * W z) ^ 2 := by
    have hd' : 1 - (1 - (ε : ℂ)) * W z ≠ 0 := by exact_mod_cast hd
    unfold H Hd B Bd N J
    push_cast
    field_simp [hd']
    ring
  rw [he]
  exact div_ne_zero (hN z hz) (pow_ne_zero _ hd)

/- Integrate Taylor polynomials of the derivative to control both uniform errors. -/
private lemma disk_polys {f fd : ℂ → ℂ} {ρ R : ℝ≥0} (hρ : 0 < ρ) (hR : ρ < R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) (ρ : ℝ), HasDerivAt f (fd z) z)
    (hd : DifferentiableOn ℂ fd (closedBall 0 (R : ℝ))) :
    ∃ p : ℕ → ℂ[X],
      TendstoUniformlyOn (fun n z => (p n).eval z) f atTop (closedBall 0 (ρ : ℝ)) ∧
      TendstoUniformlyOn (fun n z => (p n).derivative.eval z) fd atTop (closedBall 0 (ρ : ℝ)) := by
  obtain ⟨r, hr, hr'⟩ := exists_between hR
  let ps := cauchyPowerSeries fd 0 (R : ℝ)
  let c (n : ℕ) := ps n (fun _ => 1)
  let p (n : ℕ) : ℂ[X] := C (f 0) +
    ∑ k ∈ Finset.range n, C (c k / ((k + 1 : ℕ) : ℂ)) * X ^ (k + 1)
  have hp0 (n : ℕ) : (p n).eval 0 = f 0 := by
    simp [p, eval_finsetSum, pow_succ]
  have hpd (n : ℕ) (z : ℂ) : (p n).derivative.eval z = ps.partialSum n z := by
    simp only [p, derivative_add, derivative_C, zero_add, derivative_sum,
      eval_finsetSum, derivative_C_mul_X_pow, eval_mul, eval_C, eval_pow, eval_X, Nat.add_sub_cancel]
    unfold FormalMultilinearSeries.partialSum
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [div_mul_cancel₀ _ hk]
    have he := (ps k).map_smul_univ (fun _ => z) (fun _ => (1 : ℂ))
    simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin, mul_comm] using he.symm
  have hh := (hd.hasFPowerSeriesOnBall (hρ.trans hR)).tendstoUniformlyOn
    (ENNReal.coe_lt_coe.mpr hr')
  have hdd : TendstoUniformlyOn (fun n z => (p n).derivative.eval z) fd atTop
      (closedBall 0 (ρ : ℝ)) := by
    have hsub : closedBall (0 : ℂ) (ρ : ℝ) ⊆ ball 0 (r : ℝ) :=
      closedBall_subset_ball (by exact_mod_cast hr)
    simpa only [zero_add, hpd] using hh.mono hsub
  refine ⟨p, Metric.tendstoUniformlyOn_iff.2 (fun ε hε => ?_), hdd⟩
  let η : ℝ := ε / (2 * (ρ : ℝ))
  have hρ' : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  have hη : 0 < η := div_pos hε (mul_pos two_pos hρ')
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hdd η hη] with n hn z hz
  let S := closedBall (0 : ℂ) (ρ : ℝ)
  have hh (w : ℂ) (hw : w ∈ S) :
      HasDerivWithinAt (fun x => f x - (p n).eval x)
        (fd w - (p n).derivative.eval w) S w :=
    ((hf w hw).sub ((p n).hasDerivAt w)).hasDerivWithinAt
  have hn' (w : ℂ) (hw : w ∈ S) : ‖fd w - (p n).derivative.eval w‖ ≤ η := by
    simpa only [dist_eq_norm] using (hn w hw).le
  have h0 : (0 : ℂ) ∈ S := mem_closedBall_self hρ'.le
  have hb := (convex_closedBall (0 : ℂ) (ρ : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hh hn' h0 hz
  have hnorm : ‖z‖ ≤ (ρ : ℝ) := by simpa [Metric.mem_closedBall] using hz
  simp only [hp0, sub_self, sub_zero] at hb
  rw [dist_eq_norm]
  refine hb.trans_lt ((mul_le_mul_of_nonneg_left hnorm hη.le).trans_lt ?_)
  dsimp [η]
  calc
    ε / (2 * (ρ : ℝ)) * (ρ : ℝ) = ε / 2 := by field_simp [hρ'.ne']
    _ < ε := by linarith

private lemma uniform_fixed {S : Set ℂ} (f : ℂ → ℂ) :
    TendstoUniformlyOn (fun (_ : ℕ) z => f z) f atTop S :=
  Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
    Eventually.of_forall fun _ _ _ => by simpa using hε

private lemma uniform_prod {S : Set ℂ} {F G : ℕ → ℂ → ℂ} {f g₁ : ℂ → ℂ}
    (hS : IsCompact S) (hf : ContinuousOn f S) (hg : ContinuousOn g₁ S)
    (hF : TendstoUniformlyOn F f atTop S) (hG : TendstoUniformlyOn G g₁ atTop S) :
    TendstoUniformlyOn (fun n z => F n z * G n z) (fun z => f z * g₁ z) atTop S := by
  obtain ⟨M, hM, hb⟩ := compact_upper hS hf.norm
  obtain ⟨L, hL, hc⟩ := compact_upper hS hg.norm
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  let δ := min 1 (ε / (M + L + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hd₁ : δ ≤ 1 := min_le_left _ _
  have hd₂ : δ * (M + L + 1) ≤ ε :=
    (le_div_iff₀ (show 0 < M + L + 1 by positivity)).1 (min_le_right _ _)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hF δ hδ,
    Metric.tendstoUniformlyOn_iff.1 hG δ hδ] with n hn hm z hz
  have h₁ := hn z hz
  have h₂ := hm z hz
  simp only [dist_eq_norm] at h₁ h₂ ⊢
  have hGn : ‖G n z‖ ≤ L + 1 := by
    have hh := norm_sub_norm_le (G n z) (g₁ z)
    rw [norm_sub_rev] at hh
    linarith [hc z hz]
  calc
    ‖f z * g₁ z - F n z * G n z‖ =
        ‖f z * (g₁ z - G n z) + (f z - F n z) * G n z‖ := by congr 1; ring
    _ ≤ ‖f z‖ * ‖g₁ z - G n z‖ + ‖f z - F n z‖ * ‖G n z‖ := by
      simpa only [norm_mul] using norm_add_le (f z * (g₁ z - G n z)) ((f z - F n z) * G n z)
    _ < M * δ + δ * (L + 1) := add_lt_add
      ((mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg _)).trans_lt (mul_lt_mul_of_pos_left h₂ hM))
      ((mul_le_mul_of_nonneg_left hGn (norm_nonneg _)).trans_lt (mul_lt_mul_of_pos_right h₁ (by positivity)))
    _ ≤ ε := by linarith only [hd₂]

private lemma uniform_comp {S T : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {G : ℕ → ℂ → ℂ} {g₁ : ℂ → ℂ}
    (hT : IsCompact T) (hg : ContinuousOn g₁ T)
    (hf : ∀ z ∈ S, f z ∈ T)
    (hm : ∀ᶠ n in atTop, ∀ z ∈ S, F n z ∈ T)
    (hF : TendstoUniformlyOn F f atTop S) (hG : TendstoUniformlyOn G g₁ atTop T) :
    TendstoUniformlyOn (fun n z => G n (F n z)) (fun z => g₁ (f z)) atTop S := by
  have h := UniformContinuousOn.comp_tendstoUniformlyOn_eventually hm hf
    (hT.uniformContinuousOn_of_continuous hg) hF
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h (ε / 2) (half_pos hε),
    Metric.tendstoUniformlyOn_iff.1 hG (ε / 2) (half_pos hε), hm] with n hn ho hp z hz
  exact (dist_triangle _ (g₁ (F n z)) _).trans_lt (by
    linarith [hn z hz, ho (F n z) (hp z hz)])

private def Gd (u : ℂ) : ℂ := g u * (-(1 / 3 : ℂ) * ((1 + α * u)⁻¹ * α))

private lemma g_polys :
    ∃ p : ℕ → ℂ[X],
      TendstoUniformlyOn (fun n z => (p n).eval z) g atTop (closedBall 0 1) ∧
      TendstoUniformlyOn (fun n z => (p n).derivative.eval z) Gd atTop (closedBall 0 1) := by
  obtain ⟨r, hr, hr'⟩ := exists_between radius_gt
  let R : ℝ≥0 := ⟨r, zero_le_one.trans hr.le⟩
  have hR : (1 : ℝ≥0) < R := hr
  apply disk_polys (by norm_num : (0 : ℝ≥0) < 1) hR
  · intro u hu
    apply hasDeriv_g
    have h : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hu
    exact h.trans_lt radius_gt
  · intro u hu
    have h : ‖u‖ ≤ r := by
      change dist u (0 : ℂ) ≤ r at hu
      simpa only [dist_zero_right] using hu
    have hg := hasDeriv_g u (h.trans_lt hr')
    have hi : DifferentiableAt ℂ (fun z : ℂ => (1 + α * z)⁻¹) u :=
      DifferentiableAt.inv (by fun_prop) (Complex.slitPlane_ne_zero (slit u (h.trans_lt hr')))
    unfold Gd
    exact (hg.differentiableAt.mul
      ((hi.mul (differentiableAt_const α)).const_mul _)).differentiableWithinAt

private lemma W_polys :
    ∃ p : ℕ → ℂ[X],
      TendstoUniformlyOn (fun n z => (p n).eval z) W atTop K ∧
      TendstoUniformlyOn (fun n z => (p n).derivative.eval z) Wd atTop K := by
  obtain ⟨p, hp, hpd⟩ := g_polys
  let c := Complex.exp ((1 / 3 : ℂ) * Complex.log (D 1 / 1297))
  let P n := C c * X * (p n).comp q
  have hK : IsCompact K := compact_q 1
  have hq : K ⊆ (fun z => q.eval z) ⁻¹' closedBall (0 : ℂ) 1 := by
    intro z hz
    simpa [Metric.mem_closedBall] using (show ‖q.eval z‖ ≤ 1 from hz)
  have hg := (hp.comp (fun z => q.eval z)).mono hq
  have hd := (hpd.comp (fun z => q.eval z)).mono hq
  have hgc : ContinuousOn (fun z => g (q.eval z)) K := by
    intro z hz
    have hg' := hasDeriv_g (q.eval z) ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)
    exact (hg'.comp z (q.hasDerivAt z)).continuousAt.continuousWithinAt
  have hgd : ContinuousOn (fun z => Gd (q.eval z)) K := by
    unfold Gd
    refine hgc.mul (continuous_const.continuousOn.mul
      ((ContinuousOn.inv₀ (by fun_prop) (fun z hz => ?_)).mul continuous_const.continuousOn))
    exact Complex.slitPlane_ne_zero (slit _ ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt))
  have hcx : Continuous (fun z : ℂ => c * z) := by fun_prop
  have H₁ := uniform_prod hK hcx.continuousOn hgc (uniform_fixed _) hg
  have H₂ := uniform_prod hK q.derivative.continuous.continuousOn hgd (uniform_fixed _) hd
  have H₃ := uniform_prod hK hcx.continuousOn
    (q.derivative.continuous.continuousOn.mul hgd) (uniform_fixed _) H₂
  have H₄ := uniform_prod hK (show ContinuousOn (fun _ : ℂ => c) K from continuous_const.continuousOn) hgc (uniform_fixed _) hg
  refine ⟨P, ?_, ?_⟩
  · exact (H₁.congr (Eventually.of_forall fun n z _ => by simp [P, Function.comp_apply])).congr_right
      (fun z _ => by simp [W, V, c]; ring)
  · refine ((H₄.add H₃).congr (Eventually.of_forall fun n z _ => ?_)).congr_right ?_
    · simp [P, derivative_mul, derivative_comp, Function.comp_apply]
    · intro z hz
      have hz' := (show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt
      have H : HasDerivAt W (c * g (q.eval z) +
          c * z * (q.derivative.eval z * Gd (q.eval z))) z := by
        have hg' := hasDeriv_g (q.eval z) hz'
        have he := ((hasDerivAt_id z).const_mul c).mul (hg'.comp z (q.hasDerivAt z))
        have hw : (fun z => c * z * g (q.eval z)) = W := by
          funext y
          simp [W, V, c]
          ring
        change HasDerivAt (fun z => c * z * g (q.eval z)) _ z at he
        rw [hw] at he
        exact he.congr_deriv (by simp only [Gd, Function.comp_apply, id_eq, mul_one]; ring)
      exact H.unique (hasDeriv_W z hz')

private lemma H_polys (r : ℝ) (hr : 0 < r) (hr' : r < 1) :
    ∃ p : ℕ → ℂ[X],
      TendstoUniformlyOn (fun n z => (p n).eval z) (H r) atTop K ∧
      TendstoUniformlyOn (fun n z => (p n).derivative.eval z) (Hd r) atTop K := by
  have hrI : 1 < r⁻¹ := (one_lt_inv₀ hr).2 hr'
  obtain ⟨t, ht, ht'⟩ := exists_between hrI
  obtain ⟨R, hR, hR'⟩ := exists_between ht'
  let ρ : ℝ≥0 := ⟨t, zero_le_one.trans ht.le⟩
  let R₀ : ℝ≥0 := ⟨R, ρ.2.trans hR.le⟩
  have hw (z : ℂ) (hz : ‖z‖ ≤ R) : r * ‖z‖ < 1 := by
    rw [← lt_div_iff₀' hr, one_div]
    exact hz.trans_lt hR'
  let T := closedBall (0 : ℂ) t
  have hT : IsCompact T := isCompact_closedBall _ _
  have hBd : ContinuousOn (Bd r) (closedBall (0 : ℂ) R) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact pow_ne_zero _ (B_den r hr z (hw z (by simpa [Metric.mem_closedBall] using hz)))
  obtain ⟨p, hp, hd⟩ := disk_polys (show 0 < ρ from zero_lt_one.trans ht)
    (show ρ < R₀ from hR) (f := B r) (fd := Bd r) (by
      intro z hz
      change dist z (0 : ℂ) ≤ t at hz
      rw [dist_zero_right] at hz
      exact hasDeriv_B r hr z (hw z (hz.trans hR.le)))
    (by
      intro z hz
      change dist z (0 : ℂ) ≤ R at hz
      rw [dist_zero_right] at hz
      apply DifferentiableAt.differentiableWithinAt
      unfold Bd
      exact DifferentiableAt.div (by fun_prop) (by fun_prop)
        (pow_ne_zero _ (B_den r hr z (hw z hz))))
  obtain ⟨P, hP, hPd⟩ := W_polys
  have hW : ∀ z ∈ K, W z ∈ T := fun z hz => by
    simpa [T, Metric.mem_closedBall] using (W_norm_le z hz).trans ht.le
  have he : ∀ᶠ n in atTop, ∀ z ∈ K, (P n).eval z ∈ T := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hP (t - 1) (sub_pos.mpr ht)] with n hn z hz
    have hh := norm_sub_norm_le ((P n).eval z) (W z)
    rw [norm_sub_rev] at hh
    have h := hn z hz
    rw [dist_eq_norm] at h
    have hl : ‖(P n).eval z‖ ≤ t := by linarith [W_norm_le z hz]
    simpa [T, Metric.mem_closedBall] using hl
  have hBc : ContinuousOn (B r) T := fun z hz =>
    (hasDeriv_B r hr z (hw z ((show ‖z‖ ≤ t by simpa [T, Metric.mem_closedBall] using hz).trans hR.le))).continuousAt.continuousWithinAt
  have hBdc : ContinuousOn (Bd r) T := hBd.mono (closedBall_subset_closedBall hR.le)
  have hK : IsCompact K := compact_q 1
  have hWc : ContinuousOn W K := fun z hz =>
    (hasDeriv_W z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)).continuousAt.continuousWithinAt
  have hWdc : ContinuousOn Wd K := fun z hz =>
    (hasDeriv_Wd z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)).continuousAt.continuousWithinAt
  refine ⟨fun n => (p n).comp (P n), ?_, ?_⟩
  · exact (uniform_comp hT hBc hW he hP hp).congr (Eventually.of_forall fun n z _ => by simp)
  · have hU := uniform_comp hT hBdc hW he hP hd
    exact (uniform_prod hK hWdc (hBdc.comp hWc hW) hPd hU).congr
      (Eventually.of_forall fun n z _ => by simp [derivative_comp])
      |>.congr_right (fun z _ => mul_comm _ _)

private lemma model_polynomial :
    ∃ G : ℂ[X], G.eval a = 1 ∧
      (∀ z ∈ K, ((X - C a) * G).derivative.eval z ≠ 0) ∧
      (∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖G.eval z‖) := by
  obtain ⟨ε, hε, hε', _, hN⟩ := small_N
  let r := 1 - ε
  have hr : 0 < r := by dsimp [r]; linarith
  have hr' : r < 1 := by dsimp [r]; linarith
  have hK : IsCompact K := compact_q 1
  have ha : a ∈ K := q_a.le
  have hnc := H_nonzero_model ε hε hε' hN
  have hH : ContinuousOn (H r) K := fun z hz =>
    (H_deriv r hr hr' z hz).continuousAt.continuousWithinAt
  have hHd : ContinuousOn (Hd r) K := by
    unfold Hd Bd
    have hW : ContinuousOn W K := fun z hz =>
      (hasDeriv_W z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)).continuousAt.continuousWithinAt
    have hWd : ContinuousOn Wd K := fun z hz =>
      (hasDeriv_Wd z ((show ‖q.eval z‖ ≤ 1 from hz).trans_lt radius_gt)).continuousAt.continuousWithinAt
    exact (continuous_const.continuousOn.div ((continuous_const.continuousOn.sub
      (continuous_const.continuousOn.mul hW)).pow 2) (fun z hz => pow_ne_zero _
        (B_den r hr _ ((mul_le_of_le_one_right hr.le (W_norm_le z hz)).trans_lt hr')))).mul hWd
  obtain ⟨m, hm, hmin⟩ := compact_lower hK (hH.add
    ((show ContinuousOn (fun z : ℂ => z - a) K by fun_prop).mul hHd)).norm
    (fun z hz => norm_pos_iff.mpr (hnc z hz))
  have ha₀ : 0 < ‖H r a‖ := norm_pos_iff.mpr (by simpa using hnc a ha)
  have ha₁ : ‖H r a‖ < 1 := B_norm_lt r hr hr' _ W_norm_a
  obtain ⟨p, hp, hd⟩ := H_polys r hr hr'
  have hu := hp.add (uniform_prod hK (show ContinuousOn (fun z : ℂ => z - a) K by fun_prop)
    hHd (uniform_fixed _) hd)
  let δ := min (‖H r a‖ / 2) ((1 - ‖H r a‖) / 3)
  have hδ : 0 < δ := lt_min (half_pos ha₀) (div_pos (sub_pos.mpr ha₁) (by norm_num))
  obtain ⟨n, hn, hn'⟩ := ((Metric.tendstoUniformlyOn_iff.1 hp δ hδ).and
    (Metric.tendstoUniformlyOn_iff.1 hu m hm)).exists
  have hb := hn a ha
  rw [dist_eq_norm] at hb
  have ha' : (p n).eval a ≠ 0 := by
    intro he
    simp [he] at hb
    linarith [min_le_left (‖H r a‖ / 2) ((1 - ‖H r a‖) / 3)]
  let G := p n * C ((p n).eval a)⁻¹
  refine ⟨G, by simp [G, ha'], ?_, ?_⟩
  · intro z hz he
    have he' : (p n).eval z + (z - a) * (p n).derivative.eval z = 0 := by
      simpa [G, ← mul_assoc, derivative_mul, ha', ← add_mul] using he
    have hh := hn' z hz
    change dist (H r z + (z - a) * Hd r z) ((p n).eval z + (z - a) * (p n).derivative.eval z) < m at hh
    rw [he', dist_zero_right] at hh
    exact hh.not_ge (hmin z hz)
  · intro z hz
    have hbz := hn z hz.le
    rw [dist_eq_norm] at hbz
    have hB : ‖H r z‖ = 1 := B_norm_eq r hr hr' _ (W_norm_eq z hz)
    have h₁ := norm_sub_norm_le (H r z) ((p n).eval z)
    have h₂ := norm_sub_norm_le ((p n).eval a) (H r a)
    rw [norm_sub_rev] at h₂
    simp only [G, eval_mul, eval_C, ← div_eq_mul_inv, norm_div]
    rw [lt_div_iff₀ (norm_pos_iff.mpr ha'), one_mul]
    linarith [min_le_right (‖H r a‖ / 2) ((1 - ‖H r a‖) / 3)]

private lemma q_size (z : ℂ) : ‖z‖ ^ 3 ≤ s * ‖q.eval z‖ + 36 := by
  have h := norm_sub_le (z ^ 3 + b) b
  rw [add_sub_cancel_right, norm_pow, b_norm] at h
  have he : s * ‖q.eval z‖ = ‖z ^ 3 + b‖ := by
    rw [q_norm]
    field_simp [s_pos.ne']
  rwa [he]

private lemma derivative_lower (t : ℝ) (ht : 36 / s < t) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ z : ℂ, t ≤ ‖q.eval z‖ → μ ≤ ‖q.derivative.eval z‖ := by
  have hts : 36 < t * s := (div_lt_iff₀ s_pos).1 ht
  let l := min 1 (t * s - 36)
  have hl : 0 < l := lt_min zero_lt_one (sub_pos.mpr hts)
  refine ⟨3 * l ^ 2 / s, div_pos (mul_pos (by norm_num) (sq_pos_of_pos hl)) s_pos, ?_⟩
  intro z hz
  have hq : s * t ≤ ‖z ^ 3 + b‖ := by
    rw [q_norm, le_div_iff₀ s_pos] at hz
    simpa only [mul_comm] using hz
  have hu := norm_add_le (z ^ 3) b
  rw [norm_pow, b_norm] at hu
  have hzl : l ≤ ‖z‖ := by
    by_contra! hn
    have hz1 : ‖z‖ ≤ 1 := hn.le.trans (min_le_left _ _)
    have hp : ‖z‖ ^ 3 ≤ ‖z‖ := by
      nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz1),
        mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.mpr hz1)]
    have hb : l ≤ t * s - 36 := min_le_right _ _
    linarith
  rw [qd_eval, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s_pos]
  have hthree : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [hthree, div_le_div_iff_of_pos_right s_pos]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hzl 2) (by norm_num)

private lemma eval_growth (p : ℂ[X]) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ z : ℂ, 1 ≤ ‖q.eval z‖ →
      ‖p.eval z‖ ≤ C₀ * ‖q.eval z‖ ^ p.natDegree := by
  let d := p.natDegree
  let L := s + 36
  have hL : 1 ≤ L := by dsimp [L]; linarith [s_gt]
  let M := ∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨1 + M * L ^ d, by positivity, fun z hz => ?_⟩
  let v := ‖q.eval z‖
  have hLv : 1 ≤ L * v := one_le_mul_of_one_le_of_one_le hL hz
  have hzb : ‖z‖ ≤ L * v := by
    by_cases h : ‖z‖ ≤ 1
    · exact h.trans hLv
    have h₁ : ‖z‖ ≤ ‖z‖ ^ 3 := by
      simpa using pow_le_pow_right₀ (le_of_not_ge h) (show 1 ≤ (3 : ℕ) by decide)
    refine h₁.trans ((q_size z).trans ?_)
    change s * v + 36 ≤ (s + 36) * v
    linarith
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ i ∈ Finset.range (d + 1), p.coeff i * z ^ i‖ ≤
        ∑ i ∈ Finset.range (d + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖ * (L * v) ^ d := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul, norm_pow]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (pow_le_pow_left₀ (norm_nonneg _) hzb i).trans
        (pow_le_pow_right₀ hLv (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))
    _ = (M * L ^ d) * v ^ d := by rw [← Finset.sum_mul, mul_pow, mul_assoc]
    _ ≤ (1 + M * L ^ d) * v ^ d :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (norm_nonneg _) _)

private lemma collar (G : ℂ[X]) (hG : ∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖G.eval z‖) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 / 2 ∧
      ‖q.eval a‖ < 1 - δ ∧ 36 / s < 1 - δ ∧
      ∀ z : ℂ, 1 - δ ≤ ‖q.eval z‖ → ‖q.eval z‖ ≤ 1 + δ → 1 + L ≤ ‖G.eval z‖ := by
  let S : Set ℂ := {z | ‖q.eval z‖ = 1}
  have hS : IsCompact S := by
    apply (compact_q 2).of_isClosed_subset (isClosed_eq (by fun_prop) continuous_const)
    intro z hz
    change ‖q.eval z‖ = 1 at hz
    change ‖q.eval z‖ ≤ 2
    linarith
  obtain ⟨m, hm, hmb⟩ := compact_lower hS
    (u := fun z => ‖G.eval z‖ - 1) (by fun_prop) (fun z hz => sub_pos.mpr (hG z hz))
  let T : Set ℂ := {z | ‖q.eval z‖ ≤ 2} ∩ {z | ‖G.eval z‖ ≤ 1 + m / 2}
  have hT : IsCompact T := (compact_q 2).inter_right (isClosed_le (by fun_prop) continuous_const)
  obtain ⟨η, hη, he⟩ := compact_lower hT (u := fun z => |‖q.eval z‖ - 1|) (by fun_prop) (by
    intro z hz
    apply abs_pos.mpr
    intro hh
    have hh' := sub_eq_zero.mp hh
    have h := hmb z hh'
    have hz' : ‖G.eval z‖ ≤ 1 + m / 2 := hz.2
    linarith)
  have hq0 : 36 / s < 1 := (div_lt_one s_pos).2 s_gt
  let d := min η (min (1 / 2) (min (1 - ‖q.eval a‖) (1 - 36 / s)))
  have hd : 0 < d := lt_min hη (lt_min (by norm_num) (lt_min (sub_pos.mpr q_a) (sub_pos.mpr hq0)))
  obtain ⟨δ, hδ, hδd⟩ := exists_between hd
  have hδη := hδd.trans_le (min_le_left _ _)
  have hδ' := hδd.trans_le (min_le_right _ _)
  have hδ2 := hδ'.trans_le (min_le_left _ _)
  have hδa := hδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ0 := hδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨m / 2, δ, half_pos hm, hδ, hδ2, by linarith, by linarith, ?_⟩
  intro z hz₁ hz₂
  by_contra! hz
  have hzT : z ∈ T := ⟨by change ‖q.eval z‖ ≤ 2; linarith, hz.le⟩
  have hw : |‖q.eval z‖ - 1| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
  exact hδη.not_ge ((he z hzT).trans hw)

private def P (f : ℂ[X]) (k : ℕ) : ℂ[X] :=
  f + (q ^ (k + 1) - C (q.eval a ^ (k + 1))) * C (((k + 1 : ℕ) : ℂ)⁻¹)

private lemma P_eval (f : ℂ[X]) (k : ℕ) (z : ℂ) :
    (P f k).eval z = f.eval z + (q.eval z ^ (k + 1) - q.eval a ^ (k + 1)) /
      ((k + 1 : ℕ) : ℂ) := by
  simp [P, div_eq_mul_inv]

private lemma P_deriv (f : ℂ[X]) (k : ℕ) (z : ℂ) :
    (P f k).derivative.eval z = f.derivative.eval z + q.eval z ^ k * q.derivative.eval z := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [P, derivative_add, derivative_mul, derivative_C, mul_zero, add_zero, derivative_sub,
    sub_zero, derivative_pow_succ, eval_add, eval_mul, eval_C, eval_pow, Nat.cast_add, Nat.cast_one]
  congr 1
  field_simp [hk]

private lemma P_deg (f : ℂ[X]) (k : ℕ) (hk : f.natDegree ≤ k) :
    2 ≤ (P f k).degree := by
  have hq : q.natDegree = 3 := by
    unfold q
    rw [natDegree_mul_C (inv_ne_zero s_ne), natDegree_X_pow_add_C]
  have hq0 : q ≠ 0 := fun he => by simp [he] at hq
  have hp : (q ^ (k + 1)).natDegree = (k + 1) * 3 := by
    rw [natDegree_pow' (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hq0)), hq]
  have hpos : 0 < (k + 1) * 3 := by omega
  have hN : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hd : ((q ^ (k + 1) - C (q.eval a ^ (k + 1))) * C (((k + 1 : ℕ) : ℂ)⁻¹)).natDegree =
      (k + 1) * 3 := by
    rw [natDegree_mul_C (inv_ne_zero hN), natDegree_sub_eq_left_of_natDegree_lt, hp]
    simpa only [natDegree_C, hp] using hpos
  have hP : (P f k).natDegree = (k + 1) * 3 := by
    unfold P
    rw [natDegree_add_eq_right_of_natDegree_lt, hd]
    rw [hd]
    omega
  have hP₀ : P f k ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hP
    omega
  rw [degree_eq_natDegree hP₀, hP]
  exact_mod_cast (show 2 ≤ (k + 1) * 3 by omega)

/- High powers force the critical points into a collar of the lemniscate. -/
private lemma transfer (G : ℂ[X]) (ha : G.eval a = 1)
    (hf : ∀ z ∈ K, ((X - C a) * G).derivative.eval z ≠ 0)
    (hG : ∀ z : ℂ, ‖q.eval z‖ = 1 → 1 < ‖G.eval z‖) :
    ∃ p : ℂ[X], 2 ≤ p.degree ∧ ∀ z : ℂ, p.derivative.eval z = 0 →
      ‖p.derivative.eval a‖ < ‖p.eval a - p.eval z‖ / ‖a - z‖ := by
  let f := (X - C a) * G
  have hfa : f.eval a = 0 := by simp [f]
  have hfda : f.derivative.eval a = 1 := by simp [f, derivative_mul, ha]
  have hK : IsCompact K := compact_q 1
  obtain ⟨L, δ, hL, hδ, hδ₂, hδa, hδ₀, hcoll⟩ := collar G hG
  obtain ⟨μ, hμ, hμb⟩ := derivative_lower (1 - δ) hδ₀
  obtain ⟨m, hm, hmb⟩ := compact_lower hK
    (u := fun z => ‖f.derivative.eval z‖) f.derivative.continuous.norm.continuousOn
    (fun z hz => norm_pos_iff.mpr (hf z hz))
  obtain ⟨Q, hQ, hQb⟩ := compact_upper hK q.derivative.continuous.norm.continuousOn
  obtain ⟨F, hF, hFb⟩ := compact_upper (compact_q 2) f.derivative.continuous.norm.continuousOn
  obtain ⟨C₀, _, hC₀⟩ := eval_growth f.derivative
  let d := f.derivative.natDegree
  let S : Set ℂ := {z | ‖q.eval z‖ ≤ 2} ∩ {z | 1 - δ ≤ ‖q.eval z‖}
  have hS : IsCompact S := (compact_q 2).inter_right (isClosed_le continuous_const (by fun_prop))
  obtain ⟨A, hA, hAb⟩ := compact_lower hS (u := fun z => ‖a - z‖)
    (by fun_prop) (by
      intro z hz
      apply norm_pos_iff.mpr
      intro he
      have hh : 1 - δ ≤ ‖q.eval z‖ := hz.2
      rw [← sub_eq_zero.mp he] at hh
      exact hδa.not_ge hh)
  let M := 2 * F / μ
  have hi : ∀ᶠ n : ℕ in atTop, (1 - δ) ^ (n + d) * Q < min m (L / 4) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ 1 - δ by linarith)
      (show 1 - δ < 1 by linarith)).comp (tendsto_add_atTop_nat d)).mul_const Q
    rw [zero_mul] at h
    exact h.eventually_lt_const (lt_min hm (by linarith))
  have ho : ∀ᶠ n : ℕ in atTop, C₀ / μ < (1 + δ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (show 1 < 1 + δ by linarith)).eventually_gt_atTop _
  have hN : ∀ᶠ n : ℕ in atTop, (M + 1) / (L / 4 * A) < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  obtain ⟨n, hn₁, hn₂, hn₃, hn₄⟩ := (hi.and (ho.and (hN.and
    (eventually_ge_atTop f.natDegree)))).exists
  let k := n + d
  let p := P f k
  have hkc : ((k + 1 : ℕ) : ℝ) > 0 := by positivity
  have hsmall (z : ℂ) (hz : ‖q.eval z‖ ≤ 1 - δ) :
      ‖q.eval z ^ k * q.derivative.eval z‖ < min m (L / 4) := by
    have hzK : z ∈ K := hz.trans (by linarith)
    rw [norm_mul, norm_pow]
    have hb : ‖q.eval z‖ ^ k ≤ (1 - δ) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hz k
    exact (mul_le_mul hb (hQb z hzK) (norm_nonneg _)
      (pow_nonneg (by linarith : 0 ≤ 1 - δ) _)).trans_lt hn₁
  refine ⟨p, P_deg f k (by dsimp [k]; omega), fun z hz => ?_⟩
  have hroot : f.derivative.eval z + q.eval z ^ k * q.derivative.eval z = 0 := by
    simpa only [p, P_deriv] using hz
  have heq : q.eval z ^ k * q.derivative.eval z = -f.derivative.eval z :=
    eq_neg_of_add_eq_zero_right hroot
  have hnorm := congrArg norm heq
  rw [norm_neg] at hnorm
  have hz₁ : 1 - δ ≤ ‖q.eval z‖ := by
    by_contra! hh
    have hu := hsmall z hh.le
    rw [hnorm] at hu
    exact (hu.trans_le (min_le_left _ _)).not_ge (hmb z (hh.le.trans (by linarith)))
  have hz₂ : ‖q.eval z‖ ≤ 1 + δ := by
    by_contra! hh
    have hv : 1 ≤ ‖q.eval z‖ := by linarith
    have hpow : C₀ < ‖q.eval z‖ ^ n * μ := by
      have ht := (div_lt_iff₀ hμ).1 hn₂
      exact ht.trans_le (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + δ) hh.le n) hμ.le)
    have hpow' := mul_lt_mul_of_pos_right hpow (pow_pos (zero_lt_one.trans_le hv) d)
    have hb := hC₀ z hv
    rw [norm_mul, norm_pow, show k = n + d from rfl, pow_add] at hnorm
    have hlt : C₀ * ‖q.eval z‖ ^ f.derivative.natDegree <
        ‖q.eval z‖ ^ n * ‖q.eval z‖ ^ d * ‖q.derivative.eval z‖ := by
      refine hpow'.trans_le ?_
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_left (hμb z hz₁) (by positivity)
    exact hlt.not_ge (hnorm.trans_le hb)
  have hz2' : ‖q.eval z‖ ≤ 2 := hz₂.trans (by linarith)
  have hzS : z ∈ S := ⟨hz2', hz₁⟩
  have hdza : 0 < ‖a - z‖ := hA.trans_le (hAb z hzS)
  have hqz : ‖q.eval z ^ (k + 1)‖ ≤ M := by
    have h := calc
      ‖q.eval z ^ (k + 1)‖ * μ ≤
          ‖q.eval z ^ (k + 1)‖ * ‖q.derivative.eval z‖ :=
        mul_le_mul_of_nonneg_left (hμb z hz₁) (norm_nonneg _)
      _ = ‖q.eval z‖ * ‖f.derivative.eval z‖ := by
        rw [pow_succ, norm_mul, mul_right_comm ‖q.eval z ^ k‖,
          ← norm_mul (q.eval z ^ k) (q.derivative.eval z), hnorm, mul_comm]
      _ ≤ 2 * F := mul_le_mul hz2' (hFb z hz2') (norm_nonneg _) (by norm_num)
    exact (le_div_iff₀ hμ).2 h
  have hqa : ‖q.eval a ^ (k + 1)‖ ≤ 1 := by
    rw [norm_pow]
    simpa using pow_le_pow_left₀ (norm_nonneg _) q_a.le (k + 1)
  have hpn : (M + 1) / ((k + 1 : ℕ) : ℝ) < L / 4 * A := by
    have hla : 0 < L / 4 * A := by positivity
    have hnle : (n : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show n ≤ k + 1 by dsimp [k]; omega)
    exact (div_lt_iff₀ hkc).2 ((div_lt_iff₀ hla).1 (hn₃.trans_le hnle) |>.trans_eq (mul_comm _ _))
  have herror : ‖p.eval z - f.eval z‖ < L / 4 * A := by
    simp only [p, P_eval, add_sub_cancel_left, norm_div]
    have hcast : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := by
      rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkc.le]
    rw [hcast]
    exact (div_le_div_of_nonneg_right ((norm_sub_le _ _).trans
      (add_le_add hqz hqa)) hkc.le).trans_lt hpn
  have hpa : p.eval a = 0 := by simp [p, P_eval, hfa]
  have hpda : ‖p.derivative.eval a‖ < 1 + L / 4 := by
    rw [show p = P f k from rfl, P_deriv, hfda]
    exact (norm_add_le _ _).trans_lt (by
      rw [norm_one]
      exact add_lt_add_right ((hsmall a hδa.le).trans_le (min_le_right _ _)) 1)
  have hef : ‖f.eval z‖ = ‖a - z‖ * ‖G.eval z‖ := by
    simp only [f, eval_mul, eval_sub, eval_X, eval_C, norm_mul]
    rw [norm_sub_rev]
  have hval := mul_le_mul_of_nonneg_left (hcoll z hz₁ hz₂) (norm_nonneg (a - z))
  have herr := herror.trans_le (mul_le_mul_of_nonneg_left (hAb z hzS) (by positivity : 0 ≤ L / 4))
  have hbound := norm_sub_norm_le (f.eval z) (p.eval z)
  rw [hef, norm_sub_rev (f.eval z) (p.eval z)] at hbound
  have hratio : 1 + L / 4 < ‖p.eval a - p.eval z‖ / ‖a - z‖ := by
    rw [hpa, zero_sub, norm_neg, lt_div_iff₀ hdza]
    nlinarith only [hbound, hval, herr, mul_pos hL hdza]
  exact hpda.trans hratio

lemma counterexample :
    ∃ p : ℂ[X], 2 ≤ p.degree ∧ ∃ z : ℂ, ∀ c : ℂ, p.derivative.eval c = 0 →
      ‖p.derivative.eval z‖ < ‖p.eval z - p.eval c‖ / ‖z - c‖ := by
  obtain ⟨G, ha, hf, hG⟩ := model_polynomial
  obtain ⟨p, hdeg, hp⟩ := transfer G ha hf hG
  exact ⟨p, hdeg, a, hp⟩

end

end MVPProof

theorem OMA.disproof : ¬ (type_of% @MeanValueProblem.mean_value_problem) := by
  intro h
  obtain ⟨p, hdeg, z, hp⟩ := MVPProof.counterexample
  obtain ⟨c, hc, hle⟩ := h p hdeg z 1
  exact (hp c hc).not_ge hle