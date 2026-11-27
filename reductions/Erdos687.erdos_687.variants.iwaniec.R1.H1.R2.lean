import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1

-- Reduction Erdos687.erdos_687.variants.iwaniec.R1.H1.R2 of step Erdos687.erdos_687.variants.iwaniec.R1.H1
-- Credit: @my-other-github-account

/-!
# Iwaniec's `x²` window theorem with elementary Mertens and Chebyshev inputs

`H1` is Iwaniec's shifted-sieve theorem at its natural scale: every window of length `A x²`
contains an integer free of primes `≤ x` (H. Iwaniec, *On the problem of Jacobsthal*, 1978).
`H2` is the elementary Mertens-type inequality `log (x+1) ≤ ∏_{p≤x} (1-1/p)⁻¹`, and `H3` is a
Chebyshev lower bound for `π(x)`. `main` turns the target scale `π(x)² log π(x) / ∏ (1-1/p)`
into a constant multiple of `x²`, isolating the sieve theorem from the prime-counting inputs.
-/

namespace OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2

open Real Finset Filter

/-- Iwaniec scale: windows of length `A x²` contain an `x`-rough integer. -/
def H1 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ M : ℕ,
    ∃ i : ℕ, (i : ℝ) < A * (x : ℝ) ^ 2 ∧ ∀ p ≤ x, p.Prime → ¬ p ∣ M + 1 + i

/-- Elementary Mertens-type lower bound for the inverse Euler product. -/
def H2 : Prop :=
  ∀ x : ℕ, Real.log ((x : ℝ) + 1) ≤
    (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))⁻¹

/-- Chebyshev lower bound for the prime-counting function. -/
def H3 : Prop :=
  ∀ x : ℕ, 64 ≤ x → (x : ℝ) / Real.log x ≤ 4 * (Nat.primeCounting x : ℝ)

lemma log_pi_lower (pi_lower : H3) (x : ℕ) (hx : 2 ^ 12 ≤ x) :
    Real.log x / 2 ≤ Real.log (Nat.primeCounting x : ℝ) := by
  have h : (4096:ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 < Real.log (x:ℝ) := log_pos (by linarith)
  have hL : (8:ℝ) ≤ Real.log x := by
    have h4096 : Real.log (4096:ℝ) = 12 * Real.log 2 := by
      rw [show (4096:ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    have ht : (2/3:ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have := Real.log_le_log (by norm_num) h
    linarith
  have hpi := pi_lower x (by omega)
  have hq : 0 < (x:ℝ) / (4 * Real.log x) := by positivity
  have hpi' : (x:ℝ) / (4 * Real.log x) ≤ Nat.primeCounting x := by
    rw [div_mul_eq_div_div_swap] at *
    have := div_le_div_of_nonneg_right hpi (show (0:ℝ) ≤ 4 by norm_num)
    rw [mul_div_cancel_left₀ _ (by norm_num : (4:ℝ) ≠ 0)] at this
    simpa [div_div, mul_comm] using this
  have hmono := Real.log_le_log hq hpi'
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) hl.ne'] at hmono
  -- log log x ≤ log 8 + log x / 8 - 1
  have hll := log_le_sub_one_of_pos (show 0 < Real.log x / 8 by positivity)
  rw [Real.log_div hl.ne' (by norm_num)] at hll
  have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h8 : Real.log (8:ℝ) = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_lt_d9
  linarith

/-- The target follows from Iwaniec scale and the two prime-counting inputs. -/
theorem main : H1 → H2 → H3 → OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.H1 := by
  intro H log_le_inv_euler pi_lower
  obtain ⟨A, hA, hev⟩ := H
  refine ⟨32 * A, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ 12 : ℕ), hev] with x hx hs
  intro M y hy
  have hxr : (4096:ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 < Real.log (x:ℝ) := log_pos (by linarith)
  set V := ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) with hVdef
  set P : ℝ := ((Nat.primeCounting x : ℕ) : ℝ) with hPdef
  have hV := OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.eulerProd_pos x
  have hVinv : Real.log x ≤ V⁻¹ :=
    (Real.log_le_log (by positivity) (by linarith)).trans (log_le_inv_euler x)
  have hpi := pi_lower x (by omega)
  have hlp := log_pi_lower pi_lower x hx
  have hP : 0 < P := by
    have : 0 < (x:ℝ) / Real.log x := by positivity
    linarith
  -- y ≥ 32 A P^2 log P / V ≥ 32 A (x/(4L))^2 (L/2) L = A x^2
  have hP2 : ((x:ℝ) / (4 * Real.log x)) ^ 2 ≤ P ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [div_le_iff₀ (by positivity), hPdef]
    have := (div_le_iff₀ hl).mp hpi
    linarith
  have hlogP : 0 ≤ Real.log P := le_trans (by positivity) hlp
  have key : A * (x:ℝ) ^ 2 ≤ 32 * A * (P ^ 2 * Real.log P) / V := by
    rw [div_eq_mul_inv]
    have e1 : A * (x:ℝ) ^ 2 =
        32 * A * (((x:ℝ) / (4 * Real.log x)) ^ 2 * (Real.log x / 2)) * Real.log x := by
      field_simp; ring
    rw [e1]
    apply mul_le_mul _ hVinv hl.le (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hP2 hlp (by positivity) (by positivity)
  obtain ⟨i, hi, hi'⟩ := hs M
  have hiy : (i:ℝ) < y := lt_of_lt_of_le hi (key.trans hy)
  have hiy' : i < y := by exact_mod_cast hiy
  exact ⟨M + 1 + i, mem_Icc.mpr ⟨by omega, by omega⟩, hi'⟩

end OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2
