import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1

-- Step Erdos1109.erdos_1109.variants.konyagin_upper.R1.H2: hypothesis H2 of reduction Erdos1109.erdos_1109.variants.konyagin_upper.R1

/-!
Chebyshev's lower bound `(n log 2 - log (n + 1)) / log n ≤ π n` gives `n / (2 log n) ≤ π n`
for large `n`. With `X = ⌊N ^ (4/15)⌋` we have `X ≥ N ^ (4/15) / 2` and `log X ≤ log N`, so
`π X ≥ N ^ (4/15) / (4 log N)`, and `4 log N ≤ N ^ η` for large `N`.
-/

open Filter

namespace OMA

theorem pi_lower :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 / Real.log (n : ℝ) ≤ (Nat.primeCounting n : ℝ) := by
  have h0 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (9 / 100 : ℝ) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have h1 : ∀ᶠ n : ℕ in atTop,
      ‖Real.log ((n : ℝ) + 1)‖ ≤ (9 / 100 : ℝ) * ‖(n : ℝ) + 1‖ :=
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))).eventually h0
  filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hl : Real.log ((n : ℝ) + 1) ≤ 9 / 100 * ((n : ℝ) + 1) := by
    have h := (Real.le_norm_self _).trans hn
    rwa [Real.norm_of_nonneg (by linarith)] at h
  have h2 := Chebyshev.pi_ge n
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : (n : ℝ) * 0.6931471803 ≤ (n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2.le (by linarith)
  refine le_trans ?_ h2
  rw [div_le_div_iff₀ hlogpos hlogpos]
  apply mul_le_mul_of_nonneg_right _ hlogpos.le
  linarith

end OMA

theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1.H2 := by
  unfold OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1.H2
  intro η hη
  have hX : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hA : ∀ᶠ N : ℕ in atTop,
      ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) / 2 /
          Real.log ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) ≤
        (Nat.primeCounting ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℝ) ∧
      2 ≤ ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ :=
    hX.eventually (OMA.pi_lower.and (eventually_ge_atTop 2))
  have hB : ∀ᶠ N : ℕ in atTop, ‖Real.log (N : ℝ)‖ ≤ (1 / 4 : ℝ) * ‖(N : ℝ) ^ η‖ :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      ((isLittleO_log_rpow_atTop hη).bound (by norm_num))
  filter_upwards [hA, hB, eventually_ge_atTop 2] with N hA hB hN2
  obtain ⟨hpi, hX2⟩ := hA
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hP : (0 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 15) := Real.rpow_nonneg hNpos.le _
  have hXle : ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 15) :=
    Nat.floor_le hP
  have hXgt : (N : ℝ) ^ ((4 : ℝ) / 15) < ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hXr : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hX2
  have hcard : ((Finset.range (⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ + 1)).filter Nat.Prime).card =
      Nat.primeCounting ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hcard]
  generalize ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ = X at hpi hX2 hXle hXgt hXr ⊢
  have hPN : (N : ℝ) ^ ((4 : ℝ) / 15) ≤ N := by
    calc (N : ℝ) ^ ((4 : ℝ) / 15) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogle : Real.log (X : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hNη : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos hNpos _
  have h4 : 4 * Real.log (N : ℝ) ≤ (N : ℝ) ^ η := by
    rw [Real.norm_of_nonneg hlogN.le, Real.norm_of_nonneg hNη.le] at hB
    linarith
  refine le_trans ?_ hpi
  rw [Real.rpow_sub hNpos, div_le_div_iff₀ hNη hlogX]
  have h5 : (N : ℝ) ^ ((4 : ℝ) / 15) ≤ 2 * (X : ℝ) := by linarith
  have h6 : Real.log (X : ℝ) ≤ (N : ℝ) ^ η / 4 := by linarith
  calc (N : ℝ) ^ ((4 : ℝ) / 15) * Real.log (X : ℝ)
      ≤ (2 * (X : ℝ)) * ((N : ℝ) ^ η / 4) := mul_le_mul h5 h6 hlogX.le (by linarith)
    _ = (X : ℝ) / 2 * (N : ℝ) ^ η := by ring
