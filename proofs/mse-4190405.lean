import OMAStatements.S_mse_4190405

-- Problem: Asymptotic behavior of recurrence x_{n+1} = Stdev(x_1, ..., x_n)
-- Upstream: statements/mse-4190405.lean (declaration OMA.S_mse_4190405.main)
-- Credit: @bluesky314

open Filter Finset
open scoped BigOperators Topology

section Mse4190405Proof

private noncomputable def wVal : ℝ := (13 + 3 * Real.sqrt 33) / 4
private noncomputable def zVal : ℝ := wVal ^ (1 / 3 : ℝ)
private noncomputable def rVal : ℝ := (1 - OMA.S_mse_4190405.exponent)⁻¹
private noncomputable def gStep (t y : ℝ) : ℝ :=
  (y + t) / Real.sqrt (1 + t * (1 + (y - 1) ^ 2))

private lemma sqrt33_bounds :
    (5744 : ℝ) / 1000 < Real.sqrt 33 ∧ Real.sqrt 33 < 5745 / 1000 := by
  have hsq : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  constructor <;> nlinarith

private lemma zVal_pos_and_cube : 0 < zVal ∧ zVal ^ 3 = wVal := by
  have hw : 0 < wVal := by
    unfold wVal
    linarith [sqrt33_bounds.1]
  have hz : 0 < zVal := Real.rpow_pos_of_pos hw (1 / 3 : ℝ)
  refine ⟨hz, ?_⟩
  unfold zVal
  rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
  norm_num

private lemma zVal_bounds : (1962 : ℝ) / 1000 < zVal ∧ zVal < 1963 / 1000 := by
  obtain ⟨hz, hcube⟩ := zVal_pos_and_cube
  obtain ⟨hs1, hs2⟩ := sqrt33_bounds
  have hw1 : (1962 / 1000 : ℝ) ^ 3 < zVal ^ 3 := by
    rw [hcube]; unfold wVal; linarith
  have hw2 : zVal ^ 3 < (1963 / 1000 : ℝ) ^ 3 := by
    rw [hcube]; unfold wVal; linarith
  constructor
  · by_contra hle
    have hle' : zVal ≤ 1962 / 1000 := le_of_not_gt hle
    have : zVal ^ 3 ≤ (1962 / 1000 : ℝ) ^ 3 := by nlinarith [sq_nonneg zVal]
    linarith
  · by_contra hge
    have hge' : (1963 : ℝ) / 1000 ≤ zVal := le_of_not_gt hge
    have : (1963 / 1000 : ℝ) ^ 3 ≤ zVal ^ 3 := by nlinarith [sq_nonneg zVal]
    linarith

private lemma zVal_sextic : 2 * zVal ^ 6 - 13 * zVal ^ 3 - 16 = 0 := by
  have hcube := zVal_pos_and_cube.2
  have hsq : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  have hw2 : 2 * wVal ^ 2 - 13 * wVal - 16 = 0 := by
    unfold wVal
    linear_combination (9 / 8 : ℝ) * hsq
  calc
    2 * zVal ^ 6 - 13 * zVal ^ 3 - 16 = 2 * (zVal ^ 3) ^ 2 - 13 * zVal ^ 3 - 16 := by ring
    _ = 2 * wVal ^ 2 - 13 * wVal - 16 := by rw [hcube]
    _ = 0 := hw2

private lemma exponent_eq_zVal :
    OMA.S_mse_4190405.exponent = (2 + 2 / zVal - zVal) / 3 := by
  rfl

private lemma exponent_bounds :
    (3519 : ℝ) / 10000 < OMA.S_mse_4190405.exponent ∧
      OMA.S_mse_4190405.exponent < 3526 / 10000 := by
  obtain ⟨hz1, hz2⟩ := zVal_bounds
  have hz : 0 < zVal := zVal_pos_and_cube.1
  rw [exponent_eq_zVal]
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hdiv : 2 / (1963 / 1000 : ℝ) < 2 / zVal := by
      rw [div_lt_div_iff₀ (by norm_num) hz]
      linarith
    linarith
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hdiv : 2 / zVal < 2 / (1962 / 1000 : ℝ) := by
      rw [div_lt_div_iff₀ hz (by norm_num)]
      linarith
    linarith

private lemma exponent_cubic :
    OMA.S_mse_4190405.exponent ^ 2 =
      (1 - 2 * OMA.S_mse_4190405.exponent) * (1 - OMA.S_mse_4190405.exponent) ^ 2 := by
  have hz : zVal ≠ 0 := zVal_pos_and_cube.1.ne'
  have h6 := zVal_sextic
  rw [exponent_eq_zVal]
  field_simp [hz]
  linear_combination -h6

private lemma rVal_props :
    (1542 : ℝ) / 1000 < rVal ∧ rVal < 1545 / 1000 ∧
      1 - rVal⁻¹ = OMA.S_mse_4190405.exponent ∧
      rVal * (1 + (rVal - 1) ^ 2) = 2 := by
  obtain ⟨he1, he2⟩ := exponent_bounds
  have h1mr_pos : 0 < 1 - OMA.S_mse_4190405.exponent := by linarith
  have hinv : 1 - rVal⁻¹ = OMA.S_mse_4190405.exponent := by
    unfold rVal
    rw [inv_inv]
    ring
  have hr1 : (1542 : ℝ) / 1000 < rVal := by
    unfold rVal
    rw [lt_inv_comm₀ (by norm_num) h1mr_pos]
    linarith
  have hr2 : rVal < 1545 / 1000 := by
    unfold rVal
    rw [inv_lt_comm₀ h1mr_pos (by norm_num)]
    linarith
  have hrcub : rVal * (1 + (rVal - 1) ^ 2) = 2 := by
    have hcub := exponent_cubic
    have hne : 1 - OMA.S_mse_4190405.exponent ≠ 0 := h1mr_pos.ne'
    unfold rVal
    field_simp [hne]
    linear_combination hcub
  exact ⟨hr1, hr2, hinv, hrcub⟩

private lemma div_sqrt_ge_of_sq {a b d : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hd : 0 < d)
    (hsq : a ^ 2 * d ≤ b ^ 2) : a ≤ b / Real.sqrt d := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [le_div_iff₀ hs]
  have hdsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hmul : (a * Real.sqrt d) ^ 2 ≤ b ^ 2 := by rw [mul_pow, hdsq]; exact hsq
  have ha0 : 0 ≤ a * Real.sqrt d := mul_nonneg ha hs.le
  nlinarith

private lemma div_sqrt_le_of_sq {b c d : ℝ} (_hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (hsq : b ^ 2 ≤ c ^ 2 * d) : b / Real.sqrt d ≤ c := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [div_le_iff₀ hs]
  have hdsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hmul : b ^ 2 ≤ (c * Real.sqrt d) ^ 2 := by rw [mul_pow, hdsq]; exact hsq
  have hc0 : 0 ≤ c * Real.sqrt d := mul_nonneg hc hs.le
  nlinarith

private lemma gStep_mono {t y1 y2 : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2)
    (hy1 : 1 ≤ y1) (hy12 : y1 ≤ y2) (hy2 : y2 ≤ 2) :
    gStep t y1 ≤ gStep t y2 := by
  unfold gStep
  set d1 : ℝ := 1 + t * (1 + (y1 - 1) ^ 2)
  set d2 : ℝ := 1 + t * (1 + (y2 - 1) ^ 2)
  have hd1 : 0 < d1 := by positivity
  have hd2 : 0 < d2 := by positivity
  have hs1 : 0 < Real.sqrt d1 := Real.sqrt_pos.mpr hd1
  have hs2 : 0 < Real.sqrt d2 := Real.sqrt_pos.mpr hd2
  rw [div_le_div_iff₀ hs1 hs2]
  have hdsq1 : Real.sqrt d1 ^ 2 = d1 := Real.sq_sqrt hd1.le
  have hdsq2 : Real.sqrt d2 ^ 2 = d2 := Real.sq_sqrt hd2.le
  have hpoly : 0 ≤ (y2 + t) ^ 2 * d1 - (y1 + t) ^ 2 * d2 := by
    have hfac :
        (y2 + t) ^ 2 * d1 - (y1 + t) ^ 2 * d2 =
          (t + 1) * (y2 - y1) *
            ((y1 + y2) + 2 * t - t * (2 * y1 * y2 - y1 - y2) - t ^ 2 * (y1 + y2 - 2)) := by
      dsimp [d1, d2]
      ring
    rw [hfac]
    have hbr : 0 ≤ (y1 + y2) + 2 * t - t * (2 * y1 * y2 - y1 - y2) - t ^ 2 * (y1 + y2 - 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show 1 ≤ y2 by linarith)),
        mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hbr
  have hsq_diff :
      ((y1 + t) * Real.sqrt d2) ^ 2 ≤ ((y2 + t) * Real.sqrt d1) ^ 2 := by
    rw [mul_pow, mul_pow, hdsq1, hdsq2]
    linarith
  have hp1 : 0 ≤ (y1 + t) * Real.sqrt d2 := mul_nonneg (by linarith) hs2.le
  have hp2 : 0 ≤ (y2 + t) * Real.sqrt d1 := mul_nonneg (by linarith) hs1.le
  nlinarith

private lemma ratio_eq_gStep (n : ℕ) :
    OMA.S_mse_4190405.ratio (n + 1) =
      gStep (((n : ℝ) + 2)⁻¹) (OMA.S_mse_4190405.ratio n) := rfl

private lemma ratio_mem_Icc (n : ℕ) :
    1 ≤ OMA.S_mse_4190405.ratio n ∧ OMA.S_mse_4190405.ratio n ≤ 2 := by
  induction n with
  | zero =>
    simp [OMA.S_mse_4190405.ratio]
  | succ n ih =>
    rw [ratio_eq_gStep]
    set t : ℝ := ((n : ℝ) + 2)⁻¹
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 / 2 := by
      dsimp [t]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hlo : 1 ≤ gStep t 1 := by
      unfold gStep
      apply div_sqrt_ge_of_sq (by norm_num) (by positivity) (by positivity)
      nlinarith
    have hhi : gStep t 2 ≤ 2 := by
      unfold gStep
      apply div_sqrt_le_of_sq (by positivity) (by norm_num) (by positivity)
      nlinarith
    exact ⟨hlo.trans (gStep_mono ht0 ht1 le_rfl ih.1 ih.2),
      (gStep_mono ht0 ht1 ih.1 ih.2 le_rfl).trans hhi⟩

private lemma ratio_one_two_three_lower :
    (6 : ℝ) / 5 ≤ OMA.S_mse_4190405.ratio 1 ∧
      (13 : ℝ) / 10 ≤ OMA.S_mse_4190405.ratio 2 ∧
      (23 : ℝ) / 20 ≤ OMA.S_mse_4190405.ratio 3 := by
  have h1 : (6 : ℝ) / 5 ≤ OMA.S_mse_4190405.ratio 1 := by
    have heq : OMA.S_mse_4190405.ratio 1 = gStep (1 / 2) 1 := by
      rw [ratio_eq_gStep 0]; simp [OMA.S_mse_4190405.ratio]
    rw [heq]; unfold gStep
    apply div_sqrt_ge_of_sq (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have h2 : (13 : ℝ) / 10 ≤ OMA.S_mse_4190405.ratio 2 := by
    have heq : OMA.S_mse_4190405.ratio 2 = gStep (1 / 3) (OMA.S_mse_4190405.ratio 1) := by
      rw [ratio_eq_gStep 1]; norm_num
    rw [heq]
    have hg : (13 : ℝ) / 10 ≤ gStep (1 / 3) (6 / 5) := by
      unfold gStep
      apply div_sqrt_ge_of_sq (by norm_num) (by norm_num) (by norm_num)
      norm_num
    exact hg.trans (gStep_mono (by norm_num) (by norm_num) (by norm_num) h1 (ratio_mem_Icc 1).2)
  have h3 : (23 : ℝ) / 20 ≤ OMA.S_mse_4190405.ratio 3 := by
    have heq : OMA.S_mse_4190405.ratio 3 = gStep (1 / 4) (OMA.S_mse_4190405.ratio 2) := by
      rw [ratio_eq_gStep 2]; norm_num
    rw [heq]
    have hg : (23 : ℝ) / 20 ≤ gStep (1 / 4) (13 / 10) := by
      unfold gStep
      apply div_sqrt_ge_of_sq (by norm_num) (by norm_num) (by norm_num)
      norm_num
    exact hg.trans (gStep_mono (by norm_num) (by norm_num) (by norm_num) h2 (ratio_mem_Icc 2).2)
  exact ⟨h1, h2, h3⟩

private lemma ratio_three_bounds :
    rVal - 2 / 5 ≤ OMA.S_mse_4190405.ratio 3 ∧
      OMA.S_mse_4190405.ratio 3 ≤ rVal + 2 / 5 := by
  obtain ⟨hr1, hr2, _, _⟩ := rVal_props
  have h3lo := ratio_one_two_three_lower.2.2
  have h1 : gStep (1 / 4) 2 ≤ 194 / 100 := by
    unfold gStep
    apply div_sqrt_le_of_sq (by norm_num) (by norm_num) (by norm_num)
    norm_num
  have hmono := gStep_mono (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    (ratio_mem_Icc 2).1 (ratio_mem_Icc 2).2 le_rfl
  have heq : OMA.S_mse_4190405.ratio 3 = gStep (1 / 4) (OMA.S_mse_4190405.ratio 2) := by
    rw [ratio_eq_gStep 2]; norm_num
  exact ⟨by linarith, by linarith⟩

private lemma gStep_inductive_lo_aux (r : ℝ) (hr1 : (1542 : ℝ) / 1000 < r)
    (hr2 : r < 1545 / 1000) (hrc : r ^ 3 - 2 * r ^ 2 + 2 * r - 2 = 0) (k : ℕ) :
    r - 2 / ((k : ℝ) + 6) ≤ gStep (((k : ℝ) + 5)⁻¹) (r - 2 / ((k : ℝ) + 5)) := by
  have hr_lo : (3 : ℝ) / 2 < r := by linarith
  have hr_hi : r < 8 / 5 := by linarith
  have hsq_lo : (9 : ℝ) / 4 < r ^ 2 := by nlinarith
  have hsq_hi : r ^ 2 < 64 / 25 := by nlinarith
  set tk : ℝ := (k : ℝ)
  have htk : 0 ≤ tk := Nat.cast_nonneg k
  set m : ℝ := tk + 5
  have hm_pos : 0 < m := by linarith
  have hm1_pos : 0 < m + 1 := by linarith
  set L : ℝ := r - 2 / m
  set Ln : ℝ := r - 2 / (m + 1)
  have hL_pos : 0 ≤ L := by
    dsimp [L]
    have : 2 / m ≤ 2 / 5 := by rw [div_le_div_iff₀ hm_pos (by norm_num)]; linarith
    linarith
  have hLn_pos : 0 ≤ Ln := by
    dsimp [Ln]
    have : 2 / (m + 1) ≤ 2 / 6 := by rw [div_le_div_iff₀ hm1_pos (by norm_num)]; linarith
    linarith
  unfold gStep
  have heq6 : tk + 6 = m + 1 := by dsimp [m]; ring
  rw [heq6]
  set d : ℝ := 1 + m⁻¹ * (1 + (L - 1) ^ 2)
  have hd : 0 < d := by positivity
  apply div_sqrt_ge_of_sq hLn_pos (by positivity) hd
  suffices hmul : 0 ≤ m ^ 3 * (m + 1) ^ 2 * ((L + m⁻¹) ^ 2 - Ln ^ 2 * d) by
    have hpos : 0 < m ^ 3 * (m + 1) ^ 2 := by positivity
    nlinarith
  have hpoly :
      m ^ 3 * (m + 1) ^ 2 * ((L + m⁻¹) ^ 2 - Ln ^ 2 * d) =
        (r * (-tk ^ 4 - 22 * tk ^ 3 - 181 * tk ^ 2 - 660 * tk - 900) +
            8 * tk ^ 3 + 132 * tk ^ 2 + 724 * tk + 1320) *
            (r ^ 3 - 2 * r ^ 2 + 2 * r - 2) +
          ((4 * r ^ 2 - 12 * r + 13) * tk ^ 3 +
            (44 * r ^ 2 - 176 * r + 213) * tk ^ 2 +
            (120 * r ^ 2 - 820 * r + 1148) * tk +
            (-4 * r ^ 2 - 1184 * r + 2024)) := by
    dsimp [L, Ln, d, m]
    field_simp [hm_pos.ne', hm1_pos.ne']
    ring
  rw [hpoly, hrc]
  have hc3 : 0 < 4 * r ^ 2 - 12 * r + 13 := by linarith [sq_nonneg (2 * r - 3)]
  have hc2 : 0 < 44 * r ^ 2 - 176 * r + 213 := by linarith [sq_nonneg (2 * r - 4)]
  have hc1 : 0 < 120 * r ^ 2 - 820 * r + 1148 := by linarith
  have hc0 : 0 < -4 * r ^ 2 - 1184 * r + 2024 := by linarith
  have hp3 : 0 ≤ (4 * r ^ 2 - 12 * r + 13) * tk ^ 3 := by positivity
  have hp2 : 0 ≤ (44 * r ^ 2 - 176 * r + 213) * tk ^ 2 := by positivity
  have hp1 : 0 ≤ (120 * r ^ 2 - 820 * r + 1148) * tk := by positivity
  linarith

private lemma gStep_inductive_hi_aux (r : ℝ) (hr1 : (1542 : ℝ) / 1000 < r)
    (hr2 : r < 1545 / 1000) (hrc : r ^ 3 - 2 * r ^ 2 + 2 * r - 2 = 0) (k : ℕ) :
    gStep (((k : ℝ) + 5)⁻¹) (r + 2 / ((k : ℝ) + 5)) ≤ r + 2 / ((k : ℝ) + 6) := by
  have hr_lo : (3 : ℝ) / 2 < r := by linarith
  have hr_hi : r < 8 / 5 := by linarith
  have hsq_lo : (9 : ℝ) / 4 < r ^ 2 := by nlinarith
  set tk : ℝ := (k : ℝ)
  have htk : 0 ≤ tk := Nat.cast_nonneg k
  set m : ℝ := tk + 5
  have hm_pos : 0 < m := by linarith
  have hm1_pos : 0 < m + 1 := by linarith
  set U : ℝ := r + 2 / m
  set Un : ℝ := r + 2 / (m + 1)
  have hUn_pos : 0 ≤ Un := by dsimp [Un]; positivity
  unfold gStep
  have heq6 : tk + 6 = m + 1 := by dsimp [m]; ring
  rw [heq6]
  set d : ℝ := 1 + m⁻¹ * (1 + (U - 1) ^ 2)
  have hd : 0 < d := by positivity
  apply div_sqrt_le_of_sq (by dsimp [U]; positivity) hUn_pos hd
  suffices hmul : 0 ≤ m ^ 3 * (m + 1) ^ 2 * (Un ^ 2 * d - (U + m⁻¹) ^ 2) by
    have hpos : 0 < m ^ 3 * (m + 1) ^ 2 := by positivity
    nlinarith
  have hpoly :
      m ^ 3 * (m + 1) ^ 2 * (Un ^ 2 * d - (U + m⁻¹) ^ 2) =
        (r * (tk ^ 4 + 22 * tk ^ 3 + 181 * tk ^ 2 + 660 * tk + 900) +
            8 * tk ^ 3 + 132 * tk ^ 2 + 724 * tk + 1320) *
            (r ^ 3 - 2 * r ^ 2 + 2 * r - 2) +
          ((4 * r ^ 2 - 12 * r + 11) * tk ^ 3 +
            (92 * r ^ 2 - 224 * r + 179) * tk ^ 2 +
            (648 * r ^ 2 - 1332 * r + 948) * tk +
            (1444 * r ^ 2 - 2544 * r + 1656)) := by
    dsimp [U, Un, d, m]
    field_simp [hm_pos.ne', hm1_pos.ne']
    ring
  rw [hpoly, hrc]
  have hc3 : 0 < 4 * r ^ 2 - 12 * r + 11 := by linarith [sq_nonneg (2 * r - 3)]
  have hc2 : 0 < 92 * r ^ 2 - 224 * r + 179 := by linarith [sq_nonneg (2 * r - 2)]
  have hc1 : 0 < 648 * r ^ 2 - 1332 * r + 948 := by linarith
  have hc0 : 0 < 1444 * r ^ 2 - 2544 * r + 1656 := by linarith
  have hp3 : 0 ≤ (4 * r ^ 2 - 12 * r + 11) * tk ^ 3 := by positivity
  have hp2 : 0 ≤ (92 * r ^ 2 - 224 * r + 179) * tk ^ 2 := by positivity
  have hp1 : 0 ≤ (648 * r ^ 2 - 1332 * r + 948) * tk := by positivity
  linarith

private lemma ratio_rate_from_three (k : ℕ) :
    rVal - 2 / ((k : ℝ) + 5) ≤ OMA.S_mse_4190405.ratio (k + 3) ∧
      OMA.S_mse_4190405.ratio (k + 3) ≤ rVal + 2 / ((k : ℝ) + 5) := by
  obtain ⟨hr1, hr2, _, hrcub⟩ := rVal_props
  have hrc : rVal ^ 3 - 2 * rVal ^ 2 + 2 * rVal - 2 = 0 := by linear_combination hrcub
  induction k with
  | zero =>
    simpa using ratio_three_bounds
  | succ k ih =>
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have heq : OMA.S_mse_4190405.ratio (k + 1 + 3) =
        gStep (((k : ℝ) + 5)⁻¹) (OMA.S_mse_4190405.ratio (k + 3)) := by
      have : k + 1 + 3 = (k + 3) + 1 := by omega
      rw [this, ratio_eq_gStep]
      congr 1
      push_cast
      ring
    rw [heq]
    have ht0 : 0 < ((k : ℝ) + 5)⁻¹ := by positivity
    have ht1 : ((k : ℝ) + 5)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hL1 : 1 ≤ rVal - 2 / ((k : ℝ) + 5) := by
      have : 2 / ((k : ℝ) + 5) ≤ 2 / 5 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hU2 : rVal + 2 / ((k : ℝ) + 5) ≤ 2 := by
      have : 2 / ((k : ℝ) + 5) ≤ 2 / 5 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    have hlo := (gStep_inductive_lo_aux rVal hr1 hr2 hrc k).trans
      (gStep_mono ht0 ht1 hL1 ih.1 (ih.2.trans hU2))
    have hhi := (gStep_mono ht0 ht1 (hL1.trans ih.1) ih.2 hU2).trans
      (gStep_inductive_hi_aux rVal hr1 hr2 hrc k)
    have hcast : ((k + 1 : ℕ) : ℝ) + 5 = (k : ℝ) + 6 := by push_cast; ring
    rw [hcast]
    exact ⟨hlo, hhi⟩

private lemma ratio_abs_sub_le (n : ℕ) :
    |OMA.S_mse_4190405.ratio n - rVal| ≤ 2 / ((n : ℝ) + 2) := by
  obtain ⟨hr1, hr2, _, _⟩ := rVal_props
  obtain ⟨h1lo, h2lo, _⟩ := ratio_one_two_three_lower
  rcases lt_or_ge n 3 with hn | hn
  · interval_cases n
    · simp [OMA.S_mse_4190405.ratio]
      rw [abs_le]; constructor <;> linarith
    · have hb := (ratio_mem_Icc 1).2
      norm_num
      rw [abs_le]; constructor <;> linarith
    · have hb := (ratio_mem_Icc 2).2
      norm_num
      rw [abs_le]; constructor <;> linarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hk := ratio_rate_from_three k
    have hcast : ((3 + k : ℕ) : ℝ) + 2 = (k : ℝ) + 5 := by push_cast; ring
    have hadd : 3 + k = k + 3 := by omega
    rw [hcast, hadd, abs_le]
    constructor <;> linarith

private lemma ratio_tendsto : Tendsto OMA.S_mse_4190405.ratio atTop (𝓝 rVal) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ratio_abs_sub_le n) ?_
  have h1 : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).mpr (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hrew : (fun n : ℕ => 2 / ((n : ℝ) + 2)) = fun n : ℕ => (2 : ℝ) * (((n + 2 : ℕ) : ℝ))⁻¹ := by
    ext n; push_cast; ring
  rw [hrew]
  simpa using h1.const_mul (2 : ℝ)

private lemma log_one_add_bounds {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  have h1u : 0 < 1 + u := by linarith
  have hhi : Real.log (1 + u) ≤ u := by
    linarith [Real.log_le_sub_one_of_pos h1u]
  have hlo : u - u ^ 2 ≤ Real.log (1 + u) := by
    have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr h1u)
    rw [Real.log_inv] at hinv
    have halg : (u - u ^ 2) * (1 + u) ≤ u := by nlinarith [pow_nonneg hu 3]
    have hfrac : u - u ^ 2 ≤ u / (1 + u) := (le_div_iff₀ h1u).mpr halg
    have heq : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp [h1u.ne']; ring
    linarith
  exact ⟨hlo, hhi⟩

private lemma abs_correction_le (n : ℕ) :
    |OMA.S_mse_4190405.correction rVal n| ≤ 4 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨hr1, hr2, _, _⟩ := rVal_props
  have hr_pos : 0 < rVal := by linarith
  have hrat := ratio_mem_Icc n
  have hrat_pos : 0 < OMA.S_mse_4190405.ratio n := by linarith
  set t : ℝ := ((n : ℝ) + 2)⁻¹
  have ht_pos : 0 < t := by positivity
  have hb1 := log_one_add_bounds (div_nonneg ht_pos.le hrat_pos.le)
  have hb2 := log_one_add_bounds ht_pos.le
  have hr_inv_pos : 0 < rVal⁻¹ := inv_pos.mpr hr_pos
  have hr_inv_lt1 : rVal⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hdiff_le :
      |OMA.S_mse_4190405.correction rVal n| ≤
        |t / OMA.S_mse_4190405.ratio n - rVal⁻¹ * t| +
          (t / OMA.S_mse_4190405.ratio n) ^ 2 + rVal⁻¹ * t ^ 2 := by
    unfold OMA.S_mse_4190405.correction
    dsimp only []
    change |Real.log (1 + t / OMA.S_mse_4190405.ratio n) - rVal⁻¹ * Real.log (1 + t)| ≤ _
    have h2lo : rVal⁻¹ * (t - t ^ 2) ≤ rVal⁻¹ * Real.log (1 + t) :=
      mul_le_mul_of_nonneg_left hb2.1 hr_inv_pos.le
    have h2hi : rVal⁻¹ * Real.log (1 + t) ≤ rVal⁻¹ * t :=
      mul_le_mul_of_nonneg_left hb2.2 hr_inv_pos.le
    rw [abs_le]
    constructor
    · linarith [le_abs_self (rVal⁻¹ * t - t / OMA.S_mse_4190405.ratio n),
        abs_sub_comm (t / OMA.S_mse_4190405.ratio n) (rVal⁻¹ * t)]
    · linarith [le_abs_self (t / OMA.S_mse_4190405.ratio n - rVal⁻¹ * t)]
  have hlin : |t / OMA.S_mse_4190405.ratio n - rVal⁻¹ * t| ≤ 2 * t ^ 2 := by
    have heq : t / OMA.S_mse_4190405.ratio n - rVal⁻¹ * t =
        t * (rVal - OMA.S_mse_4190405.ratio n) / (OMA.S_mse_4190405.ratio n * rVal) := by
      field_simp [hrat_pos.ne', hr_pos.ne']
    rw [heq, abs_div, abs_mul, abs_of_pos ht_pos, abs_of_pos (mul_pos hrat_pos hr_pos),
      abs_sub_comm]
    have habs : |OMA.S_mse_4190405.ratio n - rVal| ≤ 2 * t := by
      simpa [t, div_eq_mul_inv] using ratio_abs_sub_le n
    have hden : 1 ≤ OMA.S_mse_4190405.ratio n * rVal := by nlinarith
    rw [div_le_iff₀ (mul_pos hrat_pos hr_pos)]
    nlinarith
  have hsq1 : (t / OMA.S_mse_4190405.ratio n) ^ 2 ≤ t ^ 2 := by
    have : t / OMA.S_mse_4190405.ratio n ≤ t := div_le_self ht_pos.le hrat.1
    nlinarith [div_nonneg ht_pos.le hrat_pos.le]
  have hsq2 : rVal⁻¹ * t ^ 2 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have h4t2 : |OMA.S_mse_4190405.correction rVal n| ≤ 4 * t ^ 2 := by linarith
  have ht2_le : 4 * t ^ 2 ≤ 4 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp [t]
    rw [inv_pow, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact h4t2.trans ht2_le

private lemma summable_abs_correction :
    Summable (fun n => |OMA.S_mse_4190405.correction rVal n|) := by
  have hp : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hp4 : Summable (fun n : ℕ => 4 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [div_eq_mul_inv] using hp.mul_left (4 : ℝ)
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_correction_le hp4

private lemma welford_invariants {x : ℕ → ℝ} (hx0 : 0 < x 0) (hev : OMA.S_mse_4190405.evolves x) :
    x 1 = 0 ∧ x 2 = x 0 / 2 ∧
      ∀ k : ℕ, 0 < x (k + 2) ∧
        (∑ j ∈ range (k + 2), x j) = ((k : ℝ) + 2) * OMA.S_mse_4190405.ratio k * x (k + 2) := by
  have hx1 : x 1 = 0 := by
    simpa using hev 0
  have hx2 : x 2 = x 0 / 2 := by
    have h1 := hev 1
    simp [Finset.sum_range_succ, hx1] at h1
    norm_num at h1
    rw [h1]
    have hrew : x 0 ^ 2 / 2 - (x 0 / 2) ^ 2 = (x 0 / 2) ^ 2 := by ring
    rw [hrew, Real.sqrt_sq (by positivity)]
  refine ⟨hx1, hx2, ?_⟩
  intro k
  induction k with
  | zero =>
    refine ⟨by linarith, ?_⟩
    simp [Finset.sum_range_succ, hx1, hx2, OMA.S_mse_4190405.ratio]
    ring
  | succ k ih =>
    obtain ⟨hk_pos, hk_sum⟩ := ih
    set m : ℝ := (k : ℝ) + 2
    have hm_pos : 0 < m := by positivity
    have hrat_pos : 0 < OMA.S_mse_4190405.ratio k := by linarith [(ratio_mem_Icc k).1]
    have hev_prev := hev (k + 1)
    have hsq_prev : x (k + 2) ^ 2 =
        (∑ j ∈ range (k + 2), x j ^ 2) / m - ((∑ j ∈ range (k + 2), x j) / m) ^ 2 := by
      have hm_eq : ((k + 1 : ℕ) : ℝ) + 1 = m := by dsimp [m]; push_cast; ring
      have hev_sq : x (k + 2) = Real.sqrt
          ((∑ j ∈ range (k + 2), x j ^ 2) / m - ((∑ j ∈ range (k + 2), x j) / m) ^ 2) := by
        rw [← hm_eq]
        exact hev_prev
      have harg_nn : 0 ≤ (∑ j ∈ range (k + 2), x j ^ 2) / m - ((∑ j ∈ range (k + 2), x j) / m) ^ 2 := by
        by_contra hneg
        have hneg' : (∑ j ∈ range (k + 2), x j ^ 2) / m - ((∑ j ∈ range (k + 2), x j) / m) ^ 2 < 0 :=
          lt_of_not_ge hneg
        have hzero : x (k + 2) = 0 := by rw [hev_sq]; exact Real.sqrt_eq_zero_of_nonpos hneg'.le
        linarith
      rw [hev_sq, Real.sq_sqrt harg_nn]
    have hQ : ∑ j ∈ range (k + 2), x j ^ 2 =
        m * x (k + 2) ^ 2 * (1 + OMA.S_mse_4190405.ratio k ^ 2) := by
      rw [hk_sum] at hsq_prev
      field_simp [hm_pos.ne'] at hsq_prev ⊢
      linear_combination -hsq_prev
    have hev_next := hev (k + 2)
    have hm1_eq : ((k + 2 : ℕ) : ℝ) + 1 = m + 1 := by dsimp [m]; push_cast; ring
    have hm1_pos : 0 < m + 1 := by positivity
    set t : ℝ := m⁻¹
    set D : ℝ := 1 + t * (1 + (OMA.S_mse_4190405.ratio k - 1) ^ 2)
    have hD_pos : 0 < D := by dsimp [D, t]; positivity
    have hsum_q3 : ∑ j ∈ range (k + 3), x j ^ 2 =
        (∑ j ∈ range (k + 2), x j ^ 2) + x (k + 2) ^ 2 :=
      Finset.sum_range_succ _ (k + 2)
    have hsum_s3 : ∑ j ∈ range (k + 3), x j =
        (∑ j ∈ range (k + 2), x j) + x (k + 2) :=
      Finset.sum_range_succ _ (k + 2)
    have hinside :
        (∑ j ∈ range (k + 3), x j ^ 2) / (m + 1) - ((∑ j ∈ range (k + 3), x j) / (m + 1)) ^ 2 =
          (m / (m + 1) * x (k + 2)) ^ 2 * D := by
      rw [hsum_q3, hsum_s3, hQ, hk_sum]
      dsimp [D, t]
      field_simp [hm_pos.ne', hm1_pos.ne']
      ring
    have hx_next : x (k + 3) = m / (m + 1) * x (k + 2) * Real.sqrt D := by
      have hev_n : x (k + 3) = Real.sqrt
          ((∑ j ∈ range (k + 3), x j ^ 2) / (m + 1) - ((∑ j ∈ range (k + 3), x j) / (m + 1)) ^ 2) := by
        rw [← hm1_eq]
        exact hev_next
      rw [hev_n, hinside, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hx_next_pos : 0 < x (k + 3) := by
      rw [hx_next]
      have hsD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
      positivity
    refine ⟨hx_next_pos, ?_⟩
    have hm1_cast : ((k + 1 : ℕ) : ℝ) + 2 = m + 1 := by dsimp [m]; push_cast; ring
    rw [hsum_s3, hk_sum, hm1_cast, ratio_eq_gStep, hx_next]
    unfold gStep
    change m * OMA.S_mse_4190405.ratio k * x (k + 2) + x (k + 2) =
      (m + 1) * ((OMA.S_mse_4190405.ratio k + t) / Real.sqrt D) *
        (m / (m + 1) * x (k + 2) * Real.sqrt D)
    have hsD_ne : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD_pos).ne'
    dsimp [t]
    field_simp [hm_pos.ne', hm1_pos.ne', hsD_ne]

private lemma correction_sum_eq {x : ℕ → ℝ} (hx0 : 0 < x 0) (hev : OMA.S_mse_4190405.evolves x)
    (k : ℕ) :
    ∑ j ∈ range k, OMA.S_mse_4190405.correction rVal j =
      Real.log ((∑ i ∈ range (k + 2), x i) / x 0) - rVal⁻¹ * Real.log (((k : ℝ) + 2) / 2) := by
  obtain ⟨hx1, _, hinv⟩ := welford_invariants hx0 hev
  induction k with
  | zero =>
    simp [Finset.sum_range_succ, hx1, div_self hx0.ne']
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    set m : ℝ := (k : ℝ) + 2
    have hm_pos : 0 < m := by positivity
    have hrat_pos : 0 < OMA.S_mse_4190405.ratio k := by linarith [(ratio_mem_Icc k).1]
    obtain ⟨hk_pos, hk_sum⟩ := hinv k
    have hsum_pos : 0 < ∑ i ∈ range (k + 2), x i := by rw [hk_sum]; positivity
    have hsum_next : ∑ i ∈ range (k + 3), x i =
        (∑ i ∈ range (k + 2), x i) * (1 + m⁻¹ / OMA.S_mse_4190405.ratio k) := by
      rw [Finset.sum_range_succ _ (k + 2), hk_sum]
      field_simp [hm_pos.ne', hrat_pos.ne']
      ring
    have hfac_pos : 0 < 1 + m⁻¹ / OMA.S_mse_4190405.ratio k := by positivity
    have hlog1 :
        Real.log ((∑ i ∈ range (k + 3), x i) / x 0) =
          Real.log ((∑ i ∈ range (k + 2), x i) / x 0) +
            Real.log (1 + m⁻¹ / OMA.S_mse_4190405.ratio k) := by
      rw [hsum_next, mul_div_right_comm, Real.log_mul (div_pos hsum_pos hx0).ne' hfac_pos.ne']
    have hlog2 :
        Real.log ((((k + 1 : ℕ) : ℝ) + 2) / 2) =
          Real.log (m / 2) + Real.log (1 + m⁻¹) := by
      have hrew : (((k + 1 : ℕ) : ℝ) + 2) / 2 = (m / 2) * (1 + m⁻¹) := by
        dsimp [m]; push_cast; field_simp [hm_pos.ne']; ring
      rw [hrew, Real.log_mul (by positivity) (by positivity)]
    unfold OMA.S_mse_4190405.correction
    dsimp only []
    change _ + (Real.log (1 + m⁻¹ / OMA.S_mse_4190405.ratio k) - rVal⁻¹ * Real.log (1 + m⁻¹)) = _
    rw [hlog1, hlog2]
    dsimp [m]
    ring

private lemma scaled_term_formula {x : ℕ → ℝ} (hx0 : 0 < x 0) (hev : OMA.S_mse_4190405.evolves x)
    (k : ℕ) :
    (((k + 2 : ℕ) : ℝ) + 1) ^ (1 - rVal⁻¹) * x (k + 2) / x 0 =
      ((((k : ℝ) + 3) / ((k : ℝ) + 2)) ^ (1 - rVal⁻¹)) *
        (Real.exp (∑ j ∈ range k, OMA.S_mse_4190405.correction rVal j) /
          (OMA.S_mse_4190405.ratio k * (2 : ℝ) ^ rVal⁻¹)) := by
  obtain ⟨_, _, hinv⟩ := welford_invariants hx0 hev
  obtain ⟨hk_pos, hk_sum⟩ := hinv k
  set m : ℝ := (k : ℝ) + 2
  have hm_pos : 0 < m := by positivity
  have hm1_pos : 0 < (k : ℝ) + 3 := by positivity
  have hrat_pos : 0 < OMA.S_mse_4190405.ratio k := by linarith [(ratio_mem_Icc k).1]
  have hsum_pos : 0 < ∑ i ∈ range (k + 2), x i := by rw [hk_sum]; positivity
  have hcs := correction_sum_eq hx0 hev k
  have hexp :
      Real.exp (∑ j ∈ range k, OMA.S_mse_4190405.correction rVal j) =
        ((∑ i ∈ range (k + 2), x i) / x 0) / ((m / 2) ^ rVal⁻¹) := by
    rw [hcs, Real.exp_sub, Real.exp_log (div_pos hsum_pos hx0)]
    congr 1
    rw [mul_comm, Real.rpow_def_of_pos (by positivity : 0 < m / 2)]
  have hm2_rpow : (m / 2) ^ rVal⁻¹ = m ^ rVal⁻¹ / (2 : ℝ) ^ rVal⁻¹ :=
    Real.div_rpow hm_pos.le (by norm_num) _
  have hm_split : m ^ (1 - rVal⁻¹) * m ^ rVal⁻¹ = m := by
    rw [← Real.rpow_add hm_pos]
    simp
  have hcast3 : ((k + 2 : ℕ) : ℝ) + 1 = (k : ℝ) + 3 := by push_cast; ring
  have hrpow_div : (((k : ℝ) + 3) / m) ^ (1 - rVal⁻¹) =
      ((k : ℝ) + 3) ^ (1 - rVal⁻¹) / m ^ (1 - rVal⁻¹) :=
    Real.div_rpow hm1_pos.le hm_pos.le _
  have hm_rpow_pos : 0 < m ^ (1 - rVal⁻¹) := Real.rpow_pos_of_pos hm_pos _
  have hm_rinv_pos : 0 < m ^ rVal⁻¹ := Real.rpow_pos_of_pos hm_pos _
  have h2_rinv_pos : 0 < (2 : ℝ) ^ rVal⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  rw [hcast3, hexp, hm2_rpow, hrpow_div, hk_sum]
  dsimp [m] at hm_split hm_pos hm_rpow_pos hm_rinv_pos ⊢
  field_simp [hx0.ne', hm_pos.ne', hrat_pos.ne', hm_rpow_pos.ne', hm_rinv_pos.ne', h2_rinv_pos.ne']
  simpa [one_div] using hm_split

end Mse4190405Proof

theorem OMA.solution : type_of% @OMA.S_mse_4190405.main := by
  obtain ⟨hr1, hr2, hinv, hrcub⟩ := rVal_props
  obtain ⟨he1, he2⟩ := exponent_bounds
  have hr_mem : rVal ∈ Set.Ioo (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hexp_mem : OMA.S_mse_4190405.exponent ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    ⟨by linarith, by linarith⟩
  have hsum_abs : Summable (fun n => |OMA.S_mse_4190405.correction rVal n|) :=
    summable_abs_correction
  have hsum : Summable (fun n => OMA.S_mse_4190405.correction rVal n) := hsum_abs.of_abs
  have hamp_pos : 0 < OMA.S_mse_4190405.amplitude rVal := by
    unfold OMA.S_mse_4190405.amplitude
    have hr_pos : 0 < rVal := by linarith
    have h2_pos : 0 < (2 : ℝ) ^ rVal⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨rVal, hr_mem, hrcub, ?_⟩
  dsimp only []
  refine ⟨?_, ?_, hinv, hsum_abs, hamp_pos, ?_⟩
  · rw [hinv]; exact hexp_mem
  · rw [hinv]; exact exponent_cubic
  · intro x hx0 hev
    rw [← tendsto_add_atTop_iff_nat 2]
    have hfun :
        (fun k : ℕ => (((k + 2 : ℕ) : ℝ) + 1) ^ (1 - rVal⁻¹) * x (k + 2) / x 0) =
          fun k : ℕ =>
            ((((k : ℝ) + 3) / ((k : ℝ) + 2)) ^ (1 - rVal⁻¹)) *
              (Real.exp (∑ j ∈ range k, OMA.S_mse_4190405.correction rVal j) /
                (OMA.S_mse_4190405.ratio k * (2 : ℝ) ^ rVal⁻¹)) := by
      ext k
      exact scaled_term_formula hx0 hev k
    rw [hfun]
    have hrat_ratio : Tendsto (fun k : ℕ => ((k : ℝ) + 3) / ((k : ℝ) + 2)) atTop (𝓝 1) := by
      have hrew : (fun k : ℕ => ((k : ℝ) + 3) / ((k : ℝ) + 2)) =
          fun k : ℕ => 1 + ((((k + 2 : ℕ) : ℝ))⁻¹) := by
        ext k
        have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        push_cast
        field_simp [hpos.ne']
        ring
      rw [hrew]
      have h0 : Tendsto (fun k : ℕ => (((k + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat 2).mpr (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
    have hfac1 :
        Tendsto (fun k : ℕ => ((((k : ℝ) + 3) / ((k : ℝ) + 2)) ^ (1 - rVal⁻¹))) atTop (𝓝 1) := by
      have hcont : ContinuousAt (fun u : ℝ => u ^ (1 - rVal⁻¹)) 1 :=
        Real.continuousAt_rpow_const 1 (1 - rVal⁻¹) (Or.inl one_ne_zero)
      have hc := hcont.tendsto.comp hrat_ratio
      rw [Real.one_rpow] at hc
      exact hc
    have hexp_lim :
        Tendsto (fun k : ℕ => Real.exp (∑ j ∈ range k, OMA.S_mse_4190405.correction rVal j))
          atTop (𝓝 (Real.exp (∑' n, OMA.S_mse_4190405.correction rVal n))) :=
      (Real.continuous_exp.tendsto _).comp hsum.hasSum.tendsto_sum_nat
    have hden_ne : rVal * (2 : ℝ) ^ rVal⁻¹ ≠ 0 := by
      have hr_pos : 0 < rVal := by linarith
      have h2_pos : 0 < (2 : ℝ) ^ rVal⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    have hden_lim :
        Tendsto (fun k : ℕ => OMA.S_mse_4190405.ratio k * (2 : ℝ) ^ rVal⁻¹)
          atTop (𝓝 (rVal * (2 : ℝ) ^ rVal⁻¹)) :=
      ratio_tendsto.mul tendsto_const_nhds
    have hfac2 :
        Tendsto
          (fun k : ℕ =>
            Real.exp (∑ j ∈ range k, OMA.S_mse_4190405.correction rVal j) /
              (OMA.S_mse_4190405.ratio k * (2 : ℝ) ^ rVal⁻¹))
          atTop (𝓝 (OMA.S_mse_4190405.amplitude rVal)) := by
      unfold OMA.S_mse_4190405.amplitude
      exact hexp_lim.div hden_lim hden_ne
    simpa [one_mul] using hfac1.mul hfac2
