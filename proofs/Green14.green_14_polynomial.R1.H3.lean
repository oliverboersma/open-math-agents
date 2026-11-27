import OMAReductions.R_Green14_green_14_polynomial_R1
import Mathlib

/-! # Fourier hitting lemma for long arithmetic progressions on the torus

We prove step H3 of the Hunter (2021) reduction for Ben Green's Open Problem 14
using a finite walk-sum expansion of the Green--Hunter cosine-power bump polynomial
weighted by a discrete Fejer kernel, together with a Cauchy--Schwarz lower bound on
closed walks.
-/

namespace Green14PolyH3Proof

open scoped Classical

noncomputable section

-- 1. Elementary Nat power inequalities
private lemma pow_ge_two_mul_pred_pow (M : ℕ) (hM : 1 ≤ M) :
    2 * (M - 1) ^ M ≤ M ^ M := by
  have hMeq : (M - 1) + 1 = M := by omega
  have hexp : M ^ M = ∑ j ∈ Finset.range (M + 1), (M - 1) ^ j * 1 ^ (M - j) * M.choose j := by
    conv_lhs => rw [← hMeq]
    rw [add_pow]
    simp only [hMeq, Nat.cast_id]
  by_cases hM1 : M = 1
  · subst hM1; norm_num
  · have hMmem : M ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
    have hMm1mem : M - 1 ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
    have hMne : M ≠ M - 1 := by omega
    have hsub : ({M, M - 1} : Finset ℕ) ⊆ Finset.range (M + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hsum := Finset.sum_le_sum_of_subset
      (f := fun j => (M - 1) ^ j * 1 ^ (M - j) * M.choose j) hsub
    rw [Finset.sum_pair hMne] at hsum
    simp only [one_pow, mul_one, Nat.choose_self] at hsum hexp
    have hchoose : M.choose (M - 1) = M := by
      rw [← Nat.choose_symm (by omega : M - 1 ≤ M)]
      have hsub1 : M - (M - 1) = 1 := by omega
      rw [hsub1, Nat.choose_one_right]
    rw [hchoose] at hsum
    have hterm : (M - 1) ^ M ≤ (M - 1) ^ (M - 1) * M := by
      conv_lhs => rw [← hMeq, pow_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    linarith

private lemma three_mul_D_pow_13_le_two_pow {t : ℕ} (ht : 20 ≤ t) :
    3 * (200 * t) ^ 13 ≤ 2 ^ (8 * t) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t h20 ih =>
    have hpow_step : (20 * (200 * (t + 1))) ^ 13 ≤ (21 * (200 * t)) ^ 13 := by
      have hlin : 20 * (200 * (t + 1)) ≤ 21 * (200 * t) := by omega
      exact Nat.pow_le_pow_left hlin 13
    have h21_13 : 21 ^ 13 ≤ 256 * 20 ^ 13 := by norm_num
    have hmul : 20 ^ 13 * (3 * (200 * (t + 1)) ^ 13) ≤ 20 ^ 13 * 2 ^ (8 * (t + 1)) := by
      calc 20 ^ 13 * (3 * (200 * (t + 1)) ^ 13)
          = 3 * (20 * (200 * (t + 1))) ^ 13 := by
            rw [mul_pow 20 (200 * (t + 1)) 13, mul_left_comm]
        _ ≤ 3 * (21 * (200 * t)) ^ 13 := Nat.mul_le_mul_left 3 hpow_step
        _ = 21 ^ 13 * (3 * (200 * t) ^ 13) := by
            rw [mul_pow 21 (200 * t) 13, mul_left_comm]
        _ ≤ (256 * 20 ^ 13) * 2 ^ (8 * t) := Nat.mul_le_mul h21_13 ih
        _ = 20 ^ 13 * (2 ^ 8 * 2 ^ (8 * t)) := by
            have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
            rw [h256]
            ring
        _ = 20 ^ 13 * 2 ^ (8 * (t + 1)) := by rw [← pow_add]; congr 2; ring
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)

-- 2. Cauchy-Schwarz on Finset in Nat
private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) ^ 2 ≤ s.card * ∑ x ∈ s, (f x) ^ 2 := by
  have hreal : (∑ x ∈ s, (f x : ℝ)) ^ 2 ≤
      (∑ _x ∈ s, (1 : ℝ) ^ 2) * ∑ x ∈ s, (f x : ℝ) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun x => (f x : ℝ))
  have hcast : (((∑ x ∈ s, f x) ^ 2 : ℕ) : ℝ) ≤
      ((s.card * ∑ x ∈ s, (f x) ^ 2 : ℕ) : ℝ) := by
    simpa using hreal
  exact_mod_cast hcast

-- 3. Rounding and trigonometric bounds
private lemma dist_round_le_of_int (x : ℝ) (m : ℤ) :
    |x - (round x : ℝ)| ≤ |x - (m : ℝ)| := by
  by_cases heq : round x = m
  · rw [heq]
  · have hdiff : (1 : ℝ) ≤ |(round x : ℝ) - (m : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |round x - m| := by rw [le_abs]; omega
      exact_mod_cast h1
    have hhalf : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have htri : |(round x : ℝ) - (m : ℝ)| ≤ |x - (round x : ℝ)| + |x - (m : ℝ)| := by
      have hsub : (round x : ℝ) - (m : ℝ) = ((round x : ℝ) - x) + (x - (m : ℝ)) := by ring
      rw [hsub]
      exact (abs_add_le _ _).trans_eq (by rw [abs_sub_comm])
    linarith

private lemma sin_sq_pi_sub_int (x : ℝ) (m : ℤ) :
    (Real.sin (Real.pi * x)) ^ 2 = (Real.sin (Real.pi * (x - (m : ℝ)))) ^ 2 := by
  have hsplit : Real.pi * x = Real.pi * (x - (m : ℝ)) + (m : ℝ) * Real.pi := by ring
  rw [hsplit, Real.sin_add_int_mul_pi, mul_pow]
  have h1 : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [sq, ← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), ← two_mul, zpow_mul]
    norm_num
  rw [h1, one_mul]

private lemma cos_sq_pi_sub_int (x : ℝ) (m : ℤ) :
    (Real.cos (Real.pi * x)) ^ 2 = (Real.cos (Real.pi * (x - (m : ℝ)))) ^ 2 := by
  rw [Real.cos_sq', Real.cos_sq', sin_sq_pi_sub_int x m]

private lemma four_mul_sq_le_sin_sq_pi {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * t ^ 2 ≤ (Real.sin (Real.pi * t)) ^ 2 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h0 : 0 ≤ Real.pi * |t| := mul_nonneg hpi_pos.le (abs_nonneg t)
  have h1 : Real.pi * |t| ≤ Real.pi / 2 := by
    have := mul_le_mul_of_nonneg_left ht hpi_pos.le
    linarith
  have hjordan := Real.mul_le_sin h0 h1
  have hmul : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp [hpi_pos.ne']
  rw [hmul] at hjordan
  have hsq : (2 * |t|) ^ 2 ≤ (Real.sin (Real.pi * |t|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hjordan 2
  have hsin_sq : (Real.sin (Real.pi * |t|)) ^ 2 = (Real.sin (Real.pi * t)) ^ 2 := by
    rcases le_or_gt 0 t with htnn | htneg
    · rw [abs_of_nonneg htnn]
    · rw [abs_of_neg htneg, mul_neg, Real.sin_neg, neg_sq]
  have hlhs : (2 * |t|) ^ 2 = 4 * t ^ 2 := by
    rw [mul_pow, sq_abs]
    norm_num
  linarith

private lemma cos_sq_pi_le_one_sub (x : ℝ) :
    (Real.cos (Real.pi * x)) ^ 2 ≤ 1 - 4 * (x - (round x : ℝ)) ^ 2 := by
  rw [cos_sq_pi_sub_int x (round x), Real.cos_sq']
  have hsin := four_mul_sq_le_sin_sq_pi (abs_sub_round x)
  linarith

private lemma cos_two_pi_neg_nonneg_of_close {x : ℝ}
    (hx : |x - (round x : ℝ)| < 1 / 100) :
    0 ≤ Real.cos (2 * Real.pi * (-x)) := by
  set d : ℝ := x - (round x : ℝ)
  have harg : 2 * Real.pi * (-x) = -(2 * Real.pi * d + (round x : ℝ) * (2 * Real.pi)) := by
    dsimp only [d]
    ring
  rw [harg, Real.cos_neg, Real.cos_add_int_mul_two_pi]
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hd_abs : |2 * Real.pi * d| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have h1 : 2 * Real.pi * |d| < 2 * 4 * (1 / 100) := by nlinarith [abs_nonneg d]
    linarith
  exact Real.cos_nonneg_of_mem_Icc ⟨(abs_le.mp hd_abs).1, (abs_le.mp hd_abs).2⟩

-- 4. Complex character eChar and Fejer kernel
private def eChar (θ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)

private lemma eChar_zero : eChar 0 = 1 := by
  simp [eChar]

private lemma eChar_add (a b : ℝ) : eChar (a + b) = eChar a * eChar b := by
  dsimp only [eChar]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eChar_neg (a : ℝ) : eChar (-a) = star (eChar a) := by
  dsimp only [eChar]
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  norm_num

private lemma eChar_norm (a : ℝ) : ‖eChar a‖ = 1 := by
  dsimp only [eChar]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * a)

private lemma eChar_re (a : ℝ) : (eChar a).re = Real.cos (2 * Real.pi * a) := by
  dsimp only [eChar]
  exact Complex.exp_ofReal_mul_I_re (2 * Real.pi * a)

private lemma four_cos_sq_eq_eChar (x : ℝ) :
    ((4 * (Real.cos (Real.pi * x)) ^ 2 : ℝ) : ℂ) = 1 + 1 + eChar x + eChar (-x) := by
  apply Complex.ext
  · have hcos2 : Real.cos (2 * Real.pi * x) = 2 * (Real.cos (Real.pi * x)) ^ 2 - 1 := by
      have harg : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
      rw [harg, Real.cos_two_mul]
    rw [Complex.ofReal_re, eChar_neg]
    simp only [Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re, eChar_re]
    linarith
  · rw [Complex.ofReal_im, eChar_neg]
    simp only [Complex.add_im, Complex.one_im, Complex.star_def, Complex.conj_im]
    ring

private def WFejer (L : ℕ) (β : ℝ) : ℝ :=
  ‖∑ m ∈ Finset.range L, eChar ((m : ℝ) * β)‖ ^ 2

private lemma WFejer_nonneg (L : ℕ) (β : ℝ) : 0 ≤ WFejer L β := sq_nonneg _

private lemma WFejer_zero (L : ℕ) : WFejer L 0 = (L : ℝ) ^ 2 := by
  dsimp only [WFejer]
  simp [eChar_zero]

private lemma WFejer_cast_eq_double_sum (L : ℕ) (β : ℝ) :
    ((WFejer L β : ℝ) : ℂ) =
      ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
        eChar ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * β) := by
  set S : ℂ := ∑ m ∈ Finset.range L, eChar ((m : ℝ) * β)
  have hnorm : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * star S := by
    rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj]
  change ((‖S‖ ^ 2 : ℝ) : ℂ) = _
  rw [hnorm]
  dsimp only [S]
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [← eChar_neg, ← eChar_add]
  congr 1
  push_cast
  ring

private lemma geom_eChar_telescope (L : ℕ) (β : ℝ) :
    (1 - eChar β) * ∑ m ∈ Finset.range L, eChar ((m : ℝ) * β) =
      1 - eChar ((L : ℝ) * β) := by
  induction L with
  | zero => simp [eChar_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hstep : eChar (((n + 1 : ℕ) : ℝ) * β) = eChar β * eChar ((n : ℝ) * β) := by
      rw [← eChar_add]
      congr 1
      push_cast
      ring
    rw [hstep]
    ring

private lemma norm_sq_one_sub_eChar (β : ℝ) :
    ‖1 - eChar β‖ ^ 2 = 4 * (Real.sin (Real.pi * β)) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  have him : (eChar β).im = Real.sin (2 * Real.pi * β) :=
    Complex.exp_ofReal_mul_I_im (2 * Real.pi * β)
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, eChar_re, Complex.sub_im, Complex.one_im,
    zero_sub, him]
  have hcos : Real.cos (2 * Real.pi * β) = 1 - 2 * (Real.sin (Real.pi * β)) ^ 2 := by
    have harg : 2 * Real.pi * β = 2 * (Real.pi * β) := by ring
    rw [harg, Real.cos_two_mul, Real.cos_sq']
    ring
  have hpyth := Real.sin_sq_add_cos_sq (2 * Real.pi * β)
  calc (1 - Real.cos (2 * Real.pi * β)) * (1 - Real.cos (2 * Real.pi * β)) +
        -Real.sin (2 * Real.pi * β) * -Real.sin (2 * Real.pi * β)
      = 1 - 2 * Real.cos (2 * Real.pi * β) +
          ((Real.sin (2 * Real.pi * β)) ^ 2 + (Real.cos (2 * Real.pi * β)) ^ 2) := by ring
    _ = 2 - 2 * Real.cos (2 * Real.pi * β) := by rw [hpyth]; ring
    _ = 4 * (Real.sin (Real.pi * β)) ^ 2 := by rw [hcos]; ring

private lemma WFejer_le_inv_sq {L : ℕ} {β δ : ℝ} (hδ : 0 < δ)
    (hdist : δ < |β - (round β : ℝ)|) :
    WFejer L β ≤ 1 / δ ^ 2 := by
  have htele := congrArg norm (geom_eChar_telescope L β)
  rw [norm_mul] at htele
  have hrhs : ‖1 - eChar ((L : ℝ) * β)‖ ≤ 2 := by
    calc ‖1 - eChar ((L : ℝ) * β)‖
        ≤ ‖(1 : ℂ)‖ + ‖eChar ((L : ℝ) * β)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, eChar_norm]; norm_num
  have hprod_le : ‖1 - eChar β‖ * ‖∑ m ∈ Finset.range L, eChar ((m : ℝ) * β)‖ ≤ 2 :=
    htele.le.trans hrhs
  have hsq_le : ‖1 - eChar β‖ ^ 2 * WFejer L β ≤ 4 := by
    dsimp only [WFejer]
    have hnn : 0 ≤ ‖1 - eChar β‖ * ‖∑ m ∈ Finset.range L, eChar ((m : ℝ) * β)‖ := by positivity
    have := pow_le_pow_left₀ hnn hprod_le 2
    linarith [mul_pow ‖1 - eChar β‖ ‖∑ m ∈ Finset.range L, eChar ((m : ℝ) * β)‖ 2]
  have hsin_ge : 4 * δ ^ 2 < (Real.sin (Real.pi * β)) ^ 2 := by
    rw [sin_sq_pi_sub_int β (round β)]
    have hlt_sq : 4 * δ ^ 2 < 4 * (β - (round β : ℝ)) ^ 2 := by
      have hsq : δ ^ 2 < |β - (round β : ℝ)| ^ 2 := pow_lt_pow_left₀ hdist hδ.le (by omega)
      rw [sq_abs] at hsq
      linarith
    exact lt_of_lt_of_le hlt_sq (four_mul_sq_le_sin_sq_pi (abs_sub_round β))
  have hnorm_gt : 4 * δ ^ 2 ≤ ‖1 - eChar β‖ ^ 2 := by
    rw [norm_sq_one_sub_eChar]
    linarith [sq_nonneg δ]
  have hW_nn : 0 ≤ WFejer L β := WFejer_nonneg L β
  have hmul_le : 4 * δ ^ 2 * WFejer L β ≤ 4 :=
    (mul_le_mul_of_nonneg_right hnorm_gt hW_nn).trans hsq_le
  rw [le_div_iff₀ (pow_pos hδ 2)]
  linarith

-- 5. Walk expansion and Cauchy-Schwarz closed-walk lower bound
private abbrev Step (D : ℕ) := Fin D × Fin 4

private def stepVec {D : ℕ} (a : Step D) : Fin D → ℤ :=
  if a.2.val = 2 then Pi.single a.1 1
  else if a.2.val = 3 then -Pi.single a.1 1
  else 0

private lemma abs_stepVec_le {D : ℕ} (a : Step D) (b : Fin D) :
    |stepVec a b| ≤ 1 := by
  dsimp only [stepVec]
  split_ifs
  · by_cases h : b = a.1 <;> simp [h]
  · by_cases h : b = a.1 <;> simp [h]
  · simp

private def walkVec {D m : ℕ} (ω : Fin m → Step D) : Fin D → ℤ :=
  fun b => ∑ j : Fin m, stepVec (ω j) b

private lemma abs_walkVec_le {D m : ℕ} (ω : Fin m → Step D) (b : Fin D) :
    |walkVec ω b| ≤ (m : ℤ) := by
  dsimp only [walkVec]
  calc |∑ j : Fin m, stepVec (ω j) b|
      ≤ ∑ j : Fin m, |stepVec (ω j) b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, (1 : ℤ) := Finset.sum_le_sum fun j _ => abs_stepVec_le (ω j) b
    _ = (m : ℤ) := by simp

private def baseSum {D : ℕ} (w : Fin D → ℝ) : ℝ :=
  ∑ b : Fin D, 4 * (Real.cos (Real.pi * w b)) ^ 2

private lemma baseSum_cast_eq_step_sum {D : ℕ} (w : Fin D → ℝ) :
    ((baseSum w : ℝ) : ℂ) =
      ∑ a : Step D, eChar (∑ b : Fin D, (stepVec a b : ℝ) * w b) := by
  dsimp only [baseSum, Step]
  rw [Complex.ofReal_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.sum_univ_four, four_cos_sq_eq_eChar (w b)]
  have h0 : ∑ c : Fin D, (stepVec (b, 0) c : ℝ) * w c = 0 := by simp [stepVec]
  have h1 : ∑ c : Fin D, (stepVec (b, 1) c : ℝ) * w c = 0 := by simp [stepVec]
  have h2 : ∑ c : Fin D, (stepVec (b, 2) c : ℝ) * w c = w b := by simp [stepVec, Pi.single_apply]
  have h3 : ∑ c : Fin D, (stepVec (b, 3) c : ℝ) * w c = -w b := by simp [stepVec, Pi.single_apply]
  rw [h0, h1, h2, h3, eChar_zero]

private lemma pow_baseSum_cast_eq_walk_sum {D : ℕ} (m : ℕ) (w : Fin D → ℝ) :
    ((baseSum w ^ m : ℝ) : ℂ) =
      ∑ ω : (Fin m → Step D), eChar (∑ b : Fin D, (walkVec ω b : ℝ) * w b) := by
  induction m with
  | zero =>
    simp [walkVec, eChar_zero]
  | succ n ih =>
    rw [pow_succ', Complex.ofReal_mul, baseSum_cast_eq_step_sum w, ih, Finset.sum_mul]
    have heq := (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Step D))
      (fun p : Step D × (Fin n → Step D) =>
        eChar (∑ b : Fin D, (stepVec p.1 b : ℝ) * w b) *
          eChar (∑ b : Fin D, (walkVec p.2 b : ℝ) * w b))
      (fun ω : Fin (n + 1) → Step D =>
        eChar (∑ b : Fin D, (walkVec ω b : ℝ) * w b))
      (fun p => by
        rw [← eChar_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        dsimp only [Fin.consEquiv, walkVec]
        simp only [Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        push_cast
        ring)).symm
    conv_rhs => rw [heq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]

private abbrev WalkPairs (D m : ℕ) := (Fin m → Step D) × (Fin m → Step D)

private def pairVec {D m : ℕ} (p : WalkPairs D m) : Fin D → ℤ :=
  fun b => walkVec p.1 b - walkVec p.2 b

private lemma abs_pairVec_le {D m : ℕ} (p : WalkPairs D m) (b : Fin D) :
    |pairVec p b| ≤ (2 * m : ℤ) := by
  dsimp only [pairVec]
  have h1 := abs_walkVec_le p.1 b
  have h2 := abs_walkVec_le p.2 b
  calc |walkVec p.1 b - walkVec p.2 b|
      ≤ |walkVec p.1 b| + |walkVec p.2 b| := abs_sub _ _
    _ ≤ (m : ℤ) + (m : ℤ) := add_le_add h1 h2
    _ = (2 * m : ℤ) := by ring

private lemma pow_two_mul_baseSum_cast {D m : ℕ} (w : Fin D → ℝ) :
    ((baseSum w ^ (2 * m) : ℝ) : ℂ) =
      ∑ p : WalkPairs D m, eChar (∑ b : Fin D, (pairVec p b : ℝ) * w b) := by
  have hpow : baseSum w ^ (2 * m) = baseSum w ^ m * baseSum w ^ m := by
    rw [two_mul, pow_add]
  have hconj : star ((baseSum w ^ m : ℝ) : ℂ) = ((baseSum w ^ m : ℝ) : ℂ) := by
    simp
  conv_lhs =>
    rw [hpow, Complex.ofReal_mul]
    arg 2
    rw [← hconj]
  rw [pow_baseSum_cast_eq_walk_sum m w, star_sum, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω₂ _ => ?_
  rw [← eChar_neg, ← eChar_add]
  congr 1
  dsimp only [pairVec]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

private lemma double_sum_baseSum_eq_fejer {D m L : ℕ} (z α : Fin D → ℝ) :
    ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
      baseSum (fun b => z b + ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * α b)) ^ (2 * m) =
      ∑ p : WalkPairs D m,
        Real.cos (2 * Real.pi * ∑ b : Fin D, (pairVec p b : ℝ) * z b) *
          WFejer L (∑ b : Fin D, (pairVec p b : ℝ) * α b) := by
  have hcast : (((∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
      baseSum (fun b => z b + ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * α b)) ^ (2 * m) : ℝ) : ℂ)).re =
      ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
        baseSum (fun b => z b + ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * α b)) ^ (2 * m) :=
    Complex.ofReal_re _
  rw [← hcast]
  have hcomplex : ((∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
      baseSum (fun b => z b + ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * α b)) ^ (2 * m) : ℝ) : ℂ) =
      ∑ p : WalkPairs D m,
        eChar (∑ b : Fin D, (pairVec p b : ℝ) * z b) *
          ((WFejer L (∑ b : Fin D, (pairVec p b : ℝ) * α b) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum, pow_two_mul_baseSum_cast]
    conv_lhs =>
      arg 2; ext m₁
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [WFejer_cast_eq_double_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [← eChar_add]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hcomplex, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Complex.mul_re, eChar_re]

private def closedPairs (D m : ℕ) : Finset (WalkPairs D m) :=
  Finset.univ.filter (fun p : WalkPairs D m => walkVec p.1 = walkVec p.2)

private lemma card_closedPairs_bound (D m : ℕ) :
    (4 * D) ^ (2 * m) ≤ (2 * m + 1) ^ D * (closedPairs D m).card := by
  let box : Finset (Fin D → ℤ) :=
    Fintype.piFinset (fun _ : Fin D => Finset.Icc (-(m : ℤ)) (m : ℤ))
  let fib (ξ : Fin D → ℤ) : Finset (Fin m → Step D) :=
    Finset.univ.filter (fun ω => walkVec ω = ξ)
  have hmem_box : ∀ ω : Fin m → Step D, walkVec ω ∈ box := by
    intro ω
    refine Fintype.mem_piFinset.mpr fun b => ?_
    rw [Finset.mem_Icc]
    exact abs_le.mp (abs_walkVec_le ω b)
  have huniv_bi : (Finset.univ : Finset (Fin m → Step D)) = box.biUnion fib := by
    ext ω
    simp only [Finset.mem_univ, Finset.mem_biUnion, fib, Finset.mem_filter, true_and, true_iff]
    exact ⟨walkVec ω, hmem_box ω, rfl⟩
  have hdisj_fib : (box : Set (Fin D → ℤ)).PairwiseDisjoint fib := by
    intro ξ₁ _ ξ₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro ω h₁ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact hne (h₁.2.symm.trans h₂.2)
  have hsum_fib : ∑ ξ ∈ box, (fib ξ).card = (4 * D) ^ m := by
    have hc : (Finset.univ : Finset (Fin m → Step D)).card = (4 * D) ^ m := by
      simp [Step, mul_comm]
    rw [← hc, huniv_bi, Finset.card_biUnion hdisj_fib]
  have hclosed_bi : closedPairs D m = box.biUnion (fun ξ => fib ξ ×ˢ fib ξ) := by
    ext p
    simp only [closedPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product, fib]
    constructor
    · intro hp
      exact ⟨walkVec p.1, hmem_box p.1, rfl, hp.symm⟩
    · rintro ⟨ξ, _, h1, h2⟩
      exact h1.trans h2.symm
  have hdisj_prod : (box : Set (Fin D → ℤ)).PairwiseDisjoint (fun ξ => fib ξ ×ˢ fib ξ) := by
    intro ξ₁ _ ξ₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    rw [Finset.mem_product, Finset.mem_filter] at hp₁ hp₂
    exact hne (hp₁.1.2.symm.trans hp₂.1.2)
  have hsum_sq : ∑ ξ ∈ box, (fib ξ).card ^ 2 = (closedPairs D m).card := by
    rw [hclosed_bi, Finset.card_biUnion hdisj_prod]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.card_product, sq]
  have hbox_card : box.card = (2 * m + 1) ^ D := by
    have hIcc : (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
      rw [Int.card_Icc]
      omega
    simp [box, hIcc]
  have hcs := sq_sum_le_card_mul_sum_sq box (fun ξ => (fib ξ).card)
  rw [hsum_fib, hbox_card, hsum_sq, ← pow_mul, mul_comm m 2] at hcs
  exact hcs

private lemma add_sq_le_two_mul_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  linarith

-- 6. Modular sublemmas for H3
private lemma baseSum_pow_le_of_fail {D k : ℕ} {ρ : ℝ} (hD_pos : 0 < D)
    (hρ : ρ = ((D : ℝ) ^ 4)⁻¹)
    {α x0 y u : Fin D → ℝ} (hu : ∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2)
    (s : ℤ)
    (hfail : (ρ / 5) ^ 2 ≤ ∑ b : Fin D, ((x0 b + (s : ℝ) * α b - y b) -
      (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2) :
    baseSum (fun b => (x0 b - y b - u b) + (s : ℝ) * α b) ^ k ≤
      (4 : ℝ) ^ k * ((D : ℝ) - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹) ^ k := by
  have hD_real_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD_pos
  let w : Fin D → ℝ := fun b => (x0 b - y b - u b) + (s : ℝ) * α b
  have hw_sum_gt : (ρ / 10) ^ 2 < ∑ b : Fin D, (w b - (round (w b) : ℝ)) ^ 2 := by
    by_contra hw_le
    push Not at hw_le
    have hsum_lt : ∑ b : Fin D, ((x0 b + (s : ℝ) * α b - y b) -
        (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2 < (ρ / 5) ^ 2 := by
      have hterm_le : ∀ b : Fin D,
          ((x0 b + (s : ℝ) * α b - y b) -
            (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2 ≤
            2 * (w b - (round (w b) : ℝ)) ^ 2 + 2 * (u b) ^ 2 := by
        intro b
        have hd := dist_round_le_of_int (x0 b + (s : ℝ) * α b - y b) (round (w b))
        have hsq1 : ((x0 b + (s : ℝ) * α b - y b) -
            (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2 ≤
            ((x0 b + (s : ℝ) * α b - y b) - (round (w b) : ℝ)) ^ 2 := by
          rw [← sq_abs, ← sq_abs ((x0 b + (s : ℝ) * α b - y b) - (round (w b) : ℝ))]
          exact pow_le_pow_left₀ (abs_nonneg _) hd 2
        have hident : (x0 b + (s : ℝ) * α b - y b) - (round (w b) : ℝ) =
            (w b - (round (w b) : ℝ)) + u b := by
          dsimp only [w]
          ring
        rw [hident] at hsq1
        exact hsq1.trans (add_sq_le_two_mul_sq (w b - (round (w b) : ℝ)) (u b))
      calc ∑ b : Fin D, ((x0 b + (s : ℝ) * α b - y b) -
              (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2
          ≤ ∑ b : Fin D, (2 * (w b - (round (w b) : ℝ)) ^ 2 + 2 * (u b) ^ 2) :=
            Finset.sum_le_sum fun b _ => hterm_le b
        _ = 2 * ∑ b : Fin D, (w b - (round (w b) : ℝ)) ^ 2 + 2 * ∑ b : Fin D, (u b) ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ < 2 * (ρ / 10) ^ 2 + 2 * (ρ / 10) ^ 2 := by linarith
        _ = (ρ / 5) ^ 2 := by ring
    exact not_lt_of_ge hfail hsum_lt
  have hρ10_eq : (ρ / 10) ^ 2 = ∑ _b : Fin D, ((100 : ℝ) * (D : ℝ) ^ 9)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hρ]
    have hD_ne : (D : ℝ) ≠ 0 := hD_real_pos.ne'
    have hpow8 : ((D : ℝ) ^ 4) ^ 2 = (D : ℝ) ^ 8 := by rw [← pow_mul]
    have hpow9 : (D : ℝ) ^ 9 = (D : ℝ) * (D : ℝ) ^ 8 := pow_succ' (D : ℝ) 8
    rw [div_pow, inv_pow, hpow8, hpow9]
    field_simp [hD_ne]
    ring
  rw [hρ10_eq] at hw_sum_gt
  obtain ⟨b₀, _, hb₀⟩ := Finset.exists_lt_of_sum_lt hw_sum_gt
  have hcos_sum_le : ∑ b : Fin D, (Real.cos (Real.pi * w b)) ^ 2 ≤
      (D : ℝ) - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹ := by
    have hb₀_cos : (Real.cos (Real.pi * w b₀)) ^ 2 ≤ 1 - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹ := by
      have hc := cos_sq_pi_le_one_sub (w b₀)
      have h4 : (4 : ℝ) * ((100 : ℝ) * (D : ℝ) ^ 9)⁻¹ = ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹ := by
        rw [mul_inv, mul_inv]
        ring
      linarith
    have hother : ∀ b ∈ (Finset.univ : Finset (Fin D)).erase b₀,
        (Real.cos (Real.pi * w b)) ^ 2 ≤ 1 := fun b _ => Real.cos_sq_le_one _
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun b : Fin D => (Real.cos (Real.pi * w b)) ^ 2) (Finset.mem_univ b₀)).symm
    rw [hsplit]
    have herase_sum : ∑ b ∈ (Finset.univ : Finset (Fin D)).erase b₀,
        (Real.cos (Real.pi * w b)) ^ 2 ≤ ((D : ℝ) - 1) := by
      calc ∑ b ∈ (Finset.univ : Finset (Fin D)).erase b₀, (Real.cos (Real.pi * w b)) ^ 2
          ≤ ∑ _b ∈ (Finset.univ : Finset (Fin D)).erase b₀, (1 : ℝ) :=
            Finset.sum_le_sum hother
        _ = (((Finset.univ : Finset (Fin D)).erase b₀).card : ℝ) := by simp
        _ = (D : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ b₀), Finset.card_univ, Fintype.card_fin]
            rw [Nat.cast_sub hD_pos]
            simp
    linarith
  have hbase_nn : 0 ≤ baseSum w := Finset.sum_nonneg fun b _ => by positivity
  have hbase_le : baseSum w ≤ 4 * ((D : ℝ) - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹) := by
    dsimp only [baseSum]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hcos_sum_le (by positivity)
  rw [← mul_pow]
  exact pow_le_pow_left₀ hbase_nn hbase_le k

private lemma tcut_le_bound {t D k M q : ℕ} (ht : 20 ≤ t) (hD : D = 200 * t)
    (hM : M = 25 * D ^ 10) (hq : q = 8 * t * D) (hk : k = M * q) :
    (4 : ℝ) ^ k * ((D : ℝ) - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹) ^ k ≤
      (4 * (D : ℝ)) ^ k / (3 * (D : ℝ) ^ (13 * D)) := by
  have hD_pos : 0 < D := by omega
  have hD_real_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD_pos
  have hM_ge : 2 ≤ M := by
    have : 1 ≤ D ^ 10 := Nat.one_le_pow 10 D hD_pos
    omega
  have hpred_pow : 2 ^ q * (M - 1) ^ k ≤ M ^ k := by
    rw [hk, pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (pow_ge_two_mul_pred_pow M (by omega)) q
  have h3D13_le_2q : 3 * D ^ (13 * D) ≤ 2 ^ q := by
    have hstep := three_mul_D_pow_13_le_two_pow ht
    rw [← hD] at hstep
    have hpowD : (3 * D ^ 13) ^ D ≤ (2 ^ (8 * t)) ^ D := Nat.pow_le_pow_left hstep D
    rw [mul_pow, ← pow_mul, ← pow_mul, ← hq] at hpowD
    have h3_le : 3 ≤ 3 ^ D := by
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ D := Nat.pow_le_pow_right (by omega) hD_pos
    exact (Nat.mul_le_mul_right _ h3_le).trans hpowD
  have hnat_ineq : 3 * D ^ (13 * D) * (M - 1) ^ k ≤ M ^ k :=
    (Nat.mul_le_mul_right _ h3D13_le_2q).trans hpred_pow
  have hreal_ineq : 3 * (D : ℝ) ^ (13 * D) * (((M : ℝ) - 1) ^ k) ≤ (M : ℝ) ^ k := by
    have hsub_cast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
    have hcast : ((3 * D ^ (13 * D) * (M - 1) ^ k : ℕ) : ℝ) ≤ ((M ^ k : ℕ) : ℝ) :=
      Nat.cast_le.mpr hnat_ineq
    simpa [hsub_cast] using hcast
  have hdiff_eq : (D : ℝ) - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹ =
      (D : ℝ) * (((M : ℝ) - 1) / (M : ℝ)) := by
    have hM_real : (M : ℝ) = 25 * ((D : ℝ) * (D : ℝ) ^ 9) := by
      rw [hM, pow_succ' D 9]
      push_cast
      rfl
    have hD_ne : (D : ℝ) ≠ 0 := hD_real_pos.ne'
    have hD9_ne : (D : ℝ) ^ 9 ≠ 0 := pow_ne_zero 9 hD_ne
    rw [hM_real]
    field_simp [hD_ne, hD9_ne]
  have hM_pos_real : (0 : ℝ) < (M : ℝ) ^ k := by
    have : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  have hratio_le : (((M : ℝ) - 1) / (M : ℝ)) ^ k ≤ 1 / (3 * (D : ℝ) ^ (13 * D)) := by
    rw [div_pow, div_le_div_iff₀ hM_pos_real (by positivity)]
    linarith
  rw [hdiff_eq, mul_pow, ← mul_assoc, ← mul_pow 4 (D : ℝ) k]
  calc (4 * (D : ℝ)) ^ k * (((M : ℝ) - 1) / (M : ℝ)) ^ k
      ≤ (4 * (D : ℝ)) ^ k * (1 / (3 * (D : ℝ) ^ (13 * D))) :=
        mul_le_mul_of_nonneg_left hratio_le (by positivity)
    _ = (4 * (D : ℝ)) ^ k / (3 * (D : ℝ) ^ (13 * D)) := by ring

private lemma h3_for_params (t D X L m M q : ℕ) (ρ : ℝ) (ht : 20 ≤ t)
    (hD : D = 200 * t) (hρ : ρ = ((D : ℝ) ^ 4)⁻¹) (hX : X = D ^ (10000 * t))
    (hL : L = X / 10) (hm : m = 25 * D ^ 10 * (800 * t ^ 2))
    (hM : M = 25 * D ^ 10) (hq : q = 8 * t * D) :
    ∀ (α x0 y u : Fin D → ℝ),
      (∑ b : Fin D, (u b) ^ 2 < (ρ / 10) ^ 2) →
      (∀ ξ : Fin D → ℤ, (∀ b : Fin D, |ξ b| ≤ (D : ℤ) ^ 12) →
        |(∑ b : Fin D, (ξ b : ℝ) * α b) - (round (∑ b : Fin D, (ξ b : ℝ) * α b) : ℝ)| ≤
          (D : ℝ) ^ (8 * D) / (X : ℝ) →
        |(∑ b : Fin D, (ξ b : ℝ) * (y b + u b - x0 b)) -
          (round (∑ b : Fin D, (ξ b : ℝ) * (y b + u b - x0 b)) : ℝ)| < 1 / 100) →
      ∃ s : ℤ, |s| ≤ (X : ℤ) / 5 ∧
        ∑ b : Fin D, ((x0 b + (s : ℝ) * α b - y b) -
          (round (x0 b + (s : ℝ) * α b - y b) : ℝ)) ^ 2 < (ρ / 5) ^ 2 := by
  intro α x0 y u hu hclose
  have hD_ge : 4000 ≤ D := by omega
  have hD_pos : 0 < D := by omega
  have hD_real_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD_pos
  have h10_dvd_X : 10 ∣ X := by
    have h10_dvd_D : 10 ∣ D := ⟨20 * t, by omega⟩
    rw [hX]
    exact dvd_pow h10_dvd_D (by omega : 10000 * t ≠ 0)
  have h10L : 10 * L = X := by
    rw [hL]
    exact Nat.mul_div_cancel' h10_dvd_X
  have hX_pos : 0 < X := hX ▸ pow_pos hD_pos _
  have hL_pos : 0 < L := by omega
  have hL_real_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
  have h2m_eq_D12 : 2 * m = D ^ 12 := by
    have hD12 : D ^ 12 = D ^ 10 * (D * D) := by rw [← sq, ← pow_add]
    rw [hm, hD12]
    generalize D ^ 10 = u10
    rw [hD]
    ring
  have h2m_eq_Mq : 2 * m = M * q := by
    rw [hm, hM, hq]
    generalize D ^ 10 = u10
    rw [hD]
    ring
  let z : Fin D → ℝ := fun b => x0 b - y b - u b
  let Tcut : ℝ := (4 : ℝ) ^ (2 * m) * ((D : ℝ) - ((25 : ℝ) * (D : ℝ) ^ 9)⁻¹) ^ (2 * m)
  by_contra hno_hit
  push Not at hno_hit
  have hpointwise_le : ∀ m₁ ∈ Finset.range L, ∀ m₂ ∈ Finset.range L,
      baseSum (fun b => z b + ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * α b)) ^ (2 * m) ≤ Tcut := by
    intro m₁ hm₁ m₂ hm₂
    rw [Finset.mem_range] at hm₁ hm₂
    let s : ℤ := (m₁ : ℤ) - (m₂ : ℤ)
    have hs_abs : |s| ≤ (X : ℤ) / 5 := by
      have hs_lt : |s| ≤ (L : ℤ) := by
        rw [abs_le]
        dsimp only [s]
        omega
      have hLX : (L : ℤ) ≤ (X : ℤ) / 5 := by
        have : (10 : ℤ) * (L : ℤ) = (X : ℤ) := by exact_mod_cast h10L
        omega
      exact hs_lt.trans hLX
    exact baseSum_pow_le_of_fail hD_pos hρ hu s (hno_hit s hs_abs)
  let Stotal : ℝ := ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
    baseSum (fun b => z b + ((((m₁ : ℤ) - (m₂ : ℤ) : ℤ) : ℝ) * α b)) ^ (2 * m)
  have hStotal_le_Tcut : Stotal ≤ (L : ℝ) ^ 2 * Tcut := by
    calc Stotal
        ≤ ∑ _m₁ ∈ Finset.range L, ∑ _m₂ ∈ Finset.range L, Tcut :=
          Finset.sum_le_sum fun m₁ hm₁ => Finset.sum_le_sum fun m₂ hm₂ =>
            hpointwise_le m₁ hm₁ m₂ hm₂
      _ = (L : ℝ) ^ 2 * Tcut := by simp [sq, mul_assoc]
  have hTcut_bound : Tcut ≤ (4 * (D : ℝ)) ^ (2 * m) / (3 * (D : ℝ) ^ (13 * D)) :=
    tcut_le_bound ht hD hM hq h2m_eq_Mq
  -- Step D: Lower bound Stotal via walk-Fejer identity
  let δ_bohr : ℝ := (D : ℝ) ^ (8 * D) / (X : ℝ)
  have hδ_bohr_pos : 0 < δ_bohr := by
    dsimp only [δ_bohr]
    have : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX_pos
    positivity
  let term (p : WalkPairs D m) : ℝ :=
    Real.cos (2 * Real.pi * ∑ b : Fin D, (pairVec p b : ℝ) * z b) *
      WFejer L (∑ b : Fin D, (pairVec p b : ℝ) * α b)
  have hStotal_eq : Stotal = ∑ p : WalkPairs D m, term p :=
    double_sum_baseSum_eq_fejer z α
  let goodPairs : Finset (WalkPairs D m) := Finset.univ.filter fun p =>
    |(∑ b : Fin D, (pairVec p b : ℝ) * α b) -
      (round (∑ b : Fin D, (pairVec p b : ℝ) * α b) : ℝ)| ≤ δ_bohr
  -- Good pairs lower bound
  have hclosed_sub : closedPairs D m ⊆ goodPairs := by
    intro p hp
    rw [closedPairs, Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hp0 : ∀ b : Fin D, pairVec p b = 0 := by
      intro b
      dsimp only [pairVec]
      rw [congrFun hp.2 b, sub_self]
    simp [hp0, hδ_bohr_pos.le]
  have hgood_nonneg : ∀ p ∈ goodPairs, p ∉ closedPairs D m → 0 ≤ term p := by
    intro p hp _
    rw [Finset.mem_filter] at hp
    have hξ_bound : ∀ b : Fin D, |pairVec p b| ≤ (D : ℤ) ^ 12 := by
      intro b
      have h1 := abs_pairVec_le p b
      have h2 : (2 * m : ℤ) = (D : ℤ) ^ 12 := by exact_mod_cast h2m_eq_D12
      rwa [h2] at h1
    have hcl := hclose (pairVec p) hξ_bound hp.2
    have hneg_z : ∑ b : Fin D, (pairVec p b : ℝ) * z b =
        -(∑ b : Fin D, (pairVec p b : ℝ) * (y b + u b - x0 b)) := by
      dsimp only [z]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    dsimp only [term]
    rw [hneg_z]
    exact mul_nonneg (cos_two_pi_neg_nonneg_of_close hcl) (WFejer_nonneg L _)
  have hclosed_val : ∀ p ∈ closedPairs D m, term p = (L : ℝ) ^ 2 := by
    intro p hp
    rw [closedPairs, Finset.mem_filter] at hp
    have hp0 : ∀ b : Fin D, pairVec p b = 0 := by
      intro b
      dsimp only [pairVec]
      rw [congrFun hp.2 b, sub_self]
    dsimp only [term]
    simp [hp0, WFejer_zero]
  have hclosed_card_real : (4 * (D : ℝ)) ^ (2 * m) / (D : ℝ) ^ (13 * D) ≤
      ((closedPairs D m).card : ℝ) := by
    have hcs := card_closedPairs_bound D m
    have h2m1_le : (2 * m + 1) ^ D ≤ D ^ (13 * D) := by
      have h1 : 2 * m + 1 ≤ D ^ 13 := by
        rw [h2m_eq_D12]
        have hpos12 : 1 ≤ D ^ 12 := Nat.one_le_pow 12 D hD_pos
        calc D ^ 12 + 1 ≤ 2 * D ^ 12 := by omega
          _ ≤ D * D ^ 12 := Nat.mul_le_mul_right _ (by omega : 2 ≤ D)
          _ = D ^ 13 := (pow_succ' D 12).symm
      rw [show 13 * D = 13 * D from rfl, pow_mul]
      exact Nat.pow_le_pow_left h1 D
    have hnat : (4 * D) ^ (2 * m) ≤ D ^ (13 * D) * (closedPairs D m).card :=
      hcs.trans (Nat.mul_le_mul_right _ h2m1_le)
    rw [div_le_iff₀ (by positivity)]
    have hcast : (((4 * D) ^ (2 * m) : ℕ) : ℝ) ≤
        ((D ^ (13 * D) * (closedPairs D m).card : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    simpa [mul_comm] using hcast
  have hgood_sum_ge : (4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (D : ℝ) ^ (13 * D) ≤
      ∑ p ∈ goodPairs, term p := by
    have hsub_sum := Finset.sum_le_sum_of_subset_of_nonneg hclosed_sub hgood_nonneg
    have hclosed_sum : ∑ p ∈ closedPairs D m, term p = ((closedPairs D m).card : ℝ) * (L : ℝ) ^ 2 := by
      rw [Finset.sum_congr rfl hclosed_val]
      simp
    calc (4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (D : ℝ) ^ (13 * D)
        = ((4 * (D : ℝ)) ^ (2 * m) / (D : ℝ) ^ (13 * D)) * (L : ℝ) ^ 2 := by ring
      _ ≤ ((closedPairs D m).card : ℝ) * (L : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hclosed_card_real (sq_nonneg _)
      _ = ∑ p ∈ closedPairs D m, term p := hclosed_sum.symm
      _ ≤ ∑ p ∈ goodPairs, term p := hsub_sum
  -- Bad pairs lower bound
  let badPairs : Finset (WalkPairs D m) := Finset.univ.filter fun p =>
    ¬ |(∑ b : Fin D, (pairVec p b : ℝ) * α b) -
      (round (∑ b : Fin D, (pairVec p b : ℝ) * α b) : ℝ)| ≤ δ_bohr
  have hbad_term_ge : ∀ p ∈ badPairs,
      -(100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D)) ≤ term p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hgt : δ_bohr < |(∑ b : Fin D, (pairVec p b : ℝ) * α b) -
        (round (∑ b : Fin D, (pairVec p b : ℝ) * α b) : ℝ)| := not_le.mp hp.2
    have hW_le := WFejer_le_inv_sq (L := L) hδ_bohr_pos hgt
    have hinv_eq : 1 / δ_bohr ^ 2 = 100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D) := by
      dsimp only [δ_bohr]
      have hX_real : (X : ℝ) = 10 * (L : ℝ) := by exact_mod_cast h10L.symm
      have hD8_sq : ((D : ℝ) ^ (8 * D)) ^ 2 = (D : ℝ) ^ (16 * D) := by
        rw [← pow_mul]
        congr 1
        ring
      have hD_ne : (D : ℝ) ≠ 0 := hD_real_pos.ne'
      rw [hX_real, div_pow, one_div_div, hD8_sq]
      ring
    rw [hinv_eq] at hW_le
    have habs_term : |term p| ≤ 100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D) := by
      dsimp only [term]
      rw [abs_mul, abs_of_nonneg (WFejer_nonneg L _)]
      calc |Real.cos (2 * Real.pi * ∑ b : Fin D, (pairVec p b : ℝ) * z b)| *
            WFejer L (∑ b : Fin D, (pairVec p b : ℝ) * α b)
          ≤ 1 * (100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D)) :=
            mul_le_mul (Real.abs_cos_le_one _) hW_le (WFejer_nonneg L _) zero_le_one
        _ = 100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D) := one_mul _
    exact neg_le_of_abs_le habs_term
  have hbad_sum_gt : -((4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (3 * (D : ℝ) ^ (13 * D))) <
      ∑ p ∈ badPairs, term p := by
    have hcard_le : (badPairs.card : ℝ) ≤ (4 * (D : ℝ)) ^ (2 * m) := by
      have hc : badPairs.card ≤ Fintype.card (WalkPairs D m) := Finset.card_le_univ _
      have huniv_c : Fintype.card (WalkPairs D m) = (4 * D) ^ (2 * m) := by
        simp only [WalkPairs, Step, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
        rw [mul_comm D 4, ← pow_add, ← two_mul]
      rw [huniv_c] at hc
      exact_mod_cast hc
    have hsum_ge : -((4 * (D : ℝ)) ^ (2 * m) * (100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D))) ≤
        ∑ p ∈ badPairs, term p := by
      calc -((4 * (D : ℝ)) ^ (2 * m) * (100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D)))
          ≤ -((badPairs.card : ℝ) * (100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D))) :=
            neg_le_neg (mul_le_mul_of_nonneg_right hcard_le (by positivity))
        _ = ∑ _p ∈ badPairs, -(100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D)) := by simp
        _ ≤ ∑ p ∈ badPairs, term p := Finset.sum_le_sum hbad_term_ge
    have hD3D_gt : (300 : ℝ) < (D : ℝ) ^ (3 * D) := by
      have h1 : 300 < D := by omega
      have h2 : D ≤ D ^ (3 * D) :=
        calc D = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ (3 * D) := Nat.pow_le_pow_right hD_pos (by omega)
      exact_mod_cast lt_of_lt_of_le h1 h2
    have hfrac_lt : 100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D) <
        (L : ℝ) ^ 2 / (3 * (D : ℝ) ^ (13 * D)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hpow_split : (D : ℝ) ^ (16 * D) = (D : ℝ) ^ (3 * D) * (D : ℝ) ^ (13 * D) := by
        rw [← pow_add]
        congr 1
        ring
      rw [hpow_split]
      have hpos_rhs : 0 < (L : ℝ) ^ 2 * (D : ℝ) ^ (13 * D) := by positivity
      calc 100 * (L : ℝ) ^ 2 * (3 * (D : ℝ) ^ (13 * D))
          = 300 * ((L : ℝ) ^ 2 * (D : ℝ) ^ (13 * D)) := by ring
        _ < (D : ℝ) ^ (3 * D) * ((L : ℝ) ^ 2 * (D : ℝ) ^ (13 * D)) :=
            mul_lt_mul_of_pos_right hD3D_gt hpos_rhs
        _ = (L : ℝ) ^ 2 * ((D : ℝ) ^ (3 * D) * (D : ℝ) ^ (13 * D)) := by ring
    have hstrict : -((4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (3 * (D : ℝ) ^ (13 * D))) <
        -((4 * (D : ℝ)) ^ (2 * m) * (100 * (L : ℝ) ^ 2 / (D : ℝ) ^ (16 * D))) := by
      have hpos4D : 0 < (4 * (D : ℝ)) ^ (2 * m) := by positivity
      have hm1 := mul_lt_mul_of_pos_left hfrac_lt hpos4D
      have heq_rhs : (4 * (D : ℝ)) ^ (2 * m) * ((L : ℝ) ^ 2 / (3 * (D : ℝ) ^ (13 * D))) =
          (4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (3 * (D : ℝ) ^ (13 * D)) := by ring
      linarith
    exact lt_of_lt_of_le hstrict hsum_ge
  -- Combine goodPairs + badPairs to contradict hStotal_le_Tcut
  have hsplit_all : Stotal = (∑ p ∈ goodPairs, term p) + (∑ p ∈ badPairs, term p) := by
    rw [hStotal_eq, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : WalkPairs D m =>
      |(∑ b : Fin D, (pairVec p b : ℝ) * α b) -
        (round (∑ b : Fin D, (pairVec p b : ℝ) * α b) : ℝ)| ≤ δ_bohr)]
  have hQ_pos : 0 < (4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (D : ℝ) ^ (13 * D) := by positivity
  have hbad_div3 : (4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (3 * (D : ℝ) ^ (13 * D)) =
      ((4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (D : ℝ) ^ (13 * D)) / 3 := by ring
  rw [hbad_div3] at hbad_sum_gt
  have hTcut_L2_le : (L : ℝ) ^ 2 * Tcut ≤
      ((4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (D : ℝ) ^ (13 * D)) / 3 := by
    calc (L : ℝ) ^ 2 * Tcut
        ≤ (L : ℝ) ^ 2 * ((4 * (D : ℝ)) ^ (2 * m) / (3 * (D : ℝ) ^ (13 * D))) :=
          mul_le_mul_of_nonneg_left hTcut_bound (sq_nonneg _)
      _ = ((4 * (D : ℝ)) ^ (2 * m) * (L : ℝ) ^ 2 / (D : ℝ) ^ (13 * D)) / 3 := by ring
  linarith

end

end Green14PolyH3Proof

theorem OMA.solution : OMA.R_Green14_green_14_polynomial_R1.H3 := by
  exact ⟨20, fun t ht =>
    Green14PolyH3Proof.h3_for_params t _ _ _ _ _ _ _ ht rfl rfl rfl rfl rfl rfl rfl⟩
