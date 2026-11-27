import OMAReductions.R_OeisA218585_conjecture_3_R1
import Mathlib

/-! The log-weighted prime number theorem for nonprincipal angular Hecke characters
and the ordinary prime number theorem modulo three suffice. The sector geometry and
continuous cosine criterion are adapted from @PanPapag (#1373). We remove the log
weight by comparison with the total Chebyshev prime counting discrepancy. -/

namespace OMA.R_OeisA218585_conjecture_3_R1_H1_R1

open OeisA218585 Real Filter MeasureTheory Finset
open scoped Topology BigOperators

def H1 : Prop :=
  let primes (N : ℕ) := (range N).filter fun p => p.Prime ∧ p % 3 = 1
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  ∀ k : ℕ, k ≠ 0 → Tendsto (fun N =>
    (∑ p ∈ primes N, log p * cos ((k : ℝ) * (6 * (z p).arg))) / N) atTop (𝓝 0)

def H2 : Prop :=
  let primes (N : ℕ) := (range N).filter fun p => p.Prime ∧ p % 3 = 1
  Tendsto (fun N => (∑ p ∈ primes N, log p) / N) atTop (𝓝 (1/2 : ℝ))

lemma ordinate_le_abscissa (p : ℕ) : yp p ≤ xp p := by
  let hasOrdinate (u : ℕ) := (List.range u).any fun v =>
    0 < v && u ^ 2 + u * v + v ^ 2 == p
  let hasAbscissa (v : ℕ) := 0 < v && (List.Ico (v + 1) p).any fun u =>
    u ^ 2 + u * v + v ^ 2 == p
  change ((List.range p).find? hasAbscissa).getD 0 ≤ ((List.range p).find? hasOrdinate).getD 0
  cases hy : (List.range p).find? hasAbscissa with
  | none => simp
  | some y =>
    obtain ⟨hypos, u, ⟨hyu, hup⟩, hu⟩ :
        0 < y ∧ ∃ u, (y + 1 ≤ u ∧ u < p) ∧ u ^ 2 + u * y + y ^ 2 = p := by
      simpa [hasAbscissa] using List.find?_some hy
    have hX : hasOrdinate u := by simpa [hasOrdinate] using
      (show ∃ v < u, 0 < v ∧ u ^ 2 + u * v + v ^ 2 = p from ⟨y, by omega, hypos, hu⟩)
    cases hx : (List.range p).find? hasOrdinate with
    | none => exact False.elim ((List.find?_eq_none.mp hx u (List.mem_range.mpr hup)) hX)
    | some x =>
      obtain ⟨v, hvx, _, hv⟩ : ∃ v < x, 0 < v ∧ x ^ 2 + x * v + v ^ 2 = p := by
        simpa [hasOrdinate] using List.find?_some hx
      change y ≤ x
      by_contra! h
      have hxu : x < u := by omega
      have hvy : v < y := by omega
      nlinarith [Nat.pow_lt_pow_left hxu (by decide : 2 ≠ 0),
        Nat.mul_le_mul hxu.le hvy.le, Nat.pow_le_pow_left hvy.le 2]

lemma sector_angle (p : ℕ) :
    (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg ∈
      Set.Icc 0 (π / 6) := by
  let x : ℝ := xp p
  let y : ℝ := yp p
  let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
  change z.arg ∈ _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hxy : y ≤ x := by dsimp [x, y]; exact_mod_cast ordinate_le_abscissa p
  have hx : 0 ≤ x := hy.trans hxy
  have hs : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨Complex.arg_nonneg_iff.mpr (show 0 ≤ √3 * y / 2 by positivity), ?_⟩
  by_cases hz : z = 0
  · rw [hz, Complex.arg_zero]; positivity
  have hn := norm_pos_iff.mpr hz
  have hns : ‖z‖ ^ 2 = x ^ 2 + x * y + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    linear_combination (y ^ 2 / 4) * hs
  have bound : √3 * y ≤ ‖z‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x + 2 * y by positivity),
      show (√3 * y) ^ 2 = 3 * y ^ 2 by rw [mul_pow, hs]]
  rw [Complex.arg_of_re_nonneg (show 0 ≤ x + y / 2 by positivity),
      ← Real.arcsin_sin (x := π / 6) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      Real.sin_pi_div_six]
  apply Real.monotone_arcsin
  apply (div_le_iff₀ hn).mpr
  change √3 * y / 2 ≤ _
  linarith

open Polynomial Polynomial.Chebyshev

/-- Finite cosine sums are uniformly dense on the fundamental sector. -/
lemma cosine_approximation (f : ℝ → ℝ) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K : ℕ) (c : ℕ → ℝ), ∀ t ∈ Set.Icc 0 (π / 6),
      |(∑ k ∈ Finset.range K, c k * cos (k * (6 * t))) - f t| < δ := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun u => f (arccos u / 6)) (by fun_prop) δ hδ
  let K := p.natDegree + 1
  have hmem : p ∈ degreeLT ℝ K := by
    rw [mem_degreeLT]
    exact p.degree_le_natDegree.trans_lt (by dsimp [K]; exact_mod_cast Nat.lt_succ_self _)
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio K = (Finset.range K : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨K, c, fun t ht => ?_⟩
  have h := hp (cos (6 * t)) (cos_mem_Icc _)
  rw [arccos_cos (by linarith [ht.1]) (by linarith [ht.2]),
    show 6 * t / 6 = t by ring, ← hc] at h
  simpa [eval_finsetSum, eval_smul, chebyshevTsequence, smul_eq_mul] using h

lemma integral_cosine_mode (k : ℕ) (hk : k ≠ 0) :
    (∫ t in 0..π / 6, cos (k * (6 * t))) = 0 := by
  have h : (k : ℝ) * 6 ≠ 0 := by positivity
  simp_rw [← mul_assoc]
  rw [intervalIntegral.integral_comp_mul_left _ h, integral_cos, mul_zero,
    show (k : ℝ) * 6 * (π / 6) = k * π by ring, Real.sin_nat_mul_pi, Real.sin_zero]
  simp

/-- A weighted Weyl criterion on the sector, using the real parts of the angular characters. -/
lemma sector_criterion (P : ℕ → Finset ℕ) (θ : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (hθ : ∀ p, θ p ∈ Set.Icc 0 (π / 6)) (hw : ∀ n p, 0 ≤ w n p)
    (hunit : ∀ᶠ n in atTop, ∑ p ∈ P n, w n p = 1)
    (modes : ∀ k : ℕ, k ≠ 0 → Tendsto
      (fun n => ∑ p ∈ P n, w n p * cos (k * (6 * θ p))) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∑ p ∈ P n, w n p * f (θ p)) atTop
      (𝓝 ((6 / π) * ∫ t in 0..π / 6, f t)) := by
  let M (n : ℕ) (g : ℝ → ℝ) := ∑ p ∈ P n, w n p * g (θ p)
  let J (g : ℝ → ℝ) := (6 / π) * ∫ t in 0..π / 6, g t
  let mode (k : ℕ) (t : ℝ) := cos ((k : ℝ) * (6 * t))
  have hmode (k : ℕ) : Tendsto (fun n => M n (mode k)) atTop (𝓝 (J (mode k))) := by
    by_cases hk : k = 0
    · subst k
      have one : J (mode 0) = 1 := by simp [J, mode]
      rw [one]
      apply tendsto_const_nhds.congr'
      filter_upwards [hunit] with n hn
      simpa [M, mode] using hn.symm
    · simpa [J, mode, integral_cosine_mode k hk] using modes k hk
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, c, happ⟩ := cosine_approximation f hf δ hδ
  let g (t : ℝ) := ∑ k ∈ Finset.range K, c k * mode k t
  have hg : Continuous g := by dsimp [g, mode]; fun_prop
  have rearrange (n : ℕ) : M n g = ∑ k ∈ Finset.range K, c k * M n (mode k) := by
    dsimp [M, g]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have integrate : J g = ∑ k ∈ Finset.range K, c k * J (mode k) := by
    dsimp [J, g]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (show Continuous (fun t => c k * mode k t) by dsimp [mode]; fun_prop).intervalIntegrable _ _)]
    simp_rw [intervalIntegral.integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlim : Tendsto (fun n => M n g) atTop (𝓝 (J g)) := by
    simp_rw [rearrange, integrate]
    exact tendsto_finsetSum _ fun k _ => (hmode k).const_mul _
  have hi : |J g - J f| ≤ δ := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π / 6)
      (C := δ) (f := fun t => g t - f t) (by
        intro t ht
        rw [Set.uIoc_of_le (by positivity : 0 ≤ π / 6)] at ht
        exact (happ t ⟨ht.1.le, ht.2⟩).le)
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _)] at hI
    dsimp [J]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 / π)]
    apply (mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 6 / π)).trans
    rw [sub_zero, abs_of_pos (by positivity : 0 < π / 6)]
    apply le_of_eq
    field_simp
  filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ, hunit] with n hn hu
  have he : |M n g - M n f| ≤ δ := calc
    _ = |∑ p ∈ P n, w n p * (g (θ p) - f (θ p))| := by simp [M, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ P n, |w n p * (g (θ p) - f (θ p))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P n, w n p * δ := Finset.sum_le_sum fun p _ => by
      rw [abs_mul, abs_of_nonneg (hw n p)]
      exact mul_le_mul_of_nonneg_left (happ _ (hθ p)).le (hw n p)
    _ = δ := by rw [← Finset.sum_mul, hu, one_mul]
  change dist (M n f) (J f) < ε
  rw [Real.dist_eq] at hn ⊢
  have h₁ := abs_le.mp he
  have h₂ := abs_le.mp hi
  have h₃ := abs_lt.mp hn
  dsimp [δ] at *
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

lemma log_gap_tendsto :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, (log N - log p)) / (N:ℝ)) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := (Chebyshev.primeCounting_sub_theta_div_log_isBigO.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).exists_pos
  have hlim : Tendsto (fun N : ℕ => C / log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hC.2.bound,eventually_ge_atTop 2] with N hn hN
  have pos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have lp : 0 < log N := log_pos (by exact_mod_cast (show 1 < N by omega))
  change ‖(Nat.primeCounting ⌊(N:ℝ)⌋₊:ℝ) - Chebyshev.theta N / log N‖ ≤ C * ‖(N:ℝ) / log N ^ 2‖ at hn
  rw [Nat.floor_natCast,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (N:ℝ) / log N ^ 2)] at hn
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting,
    ← Chebyshev.theta_eq_sum_primesLE_log]
  rw [Real.norm_eq_abs,abs_div,abs_of_pos pos,div_le_div_iff₀ pos lp]
  have he : (Nat.primeCounting N : ℝ)*log N - Chebyshev.theta N =
      ((Nat.primeCounting N:ℝ)-Chebyshev.theta N / log N)*log N := by field_simp
  rw [he,abs_mul,abs_of_pos lp]
  calc
    _ ≤ (C * ((N:ℝ) / log N ^ 2)) * log N * log N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn lp.le) lp.le
    _ = _ := by field_simp

lemma remove_log_weight (P : ℕ → Finset ℕ) (hP : ∀ N,P N ⊆ Nat.primesLE N)
    (v : ℕ → ℝ) (hv : ∀ p, |v p| ≤ 1) (L : ℝ)
    (hw : Tendsto (fun N => (∑ p ∈ P N, log p * v p) / (N:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => log N * (∑ p ∈ P N, v p) / (N:ℝ)) atTop (𝓝 L) := by
  let E (N : ℕ) := (∑ p ∈ P N, (log N-log p)*v p) / (N:ℝ)
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ log_gap_tendsto
    filter_upwards with N
    have gap (p : ℕ) (hp : p ∈ Nat.primesLE N) : 0 ≤ log N - log p := by
      obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
      exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hle))
    change ‖(∑ p ∈ P N, (log N-log p)*v p) / (N:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (hP N) (fun p hp _ => gap p hp))
    apply sum_le_sum
    intro p hp
    rw [abs_mul, abs_of_nonneg (gap p (hP N hp))]
    exact mul_le_of_le_one_right (gap p (hP N hp)) (hv p)
  have h := hE.add hw
  rw [zero_add] at h
  apply h.congr
  intro N
  simp only [E,sub_mul,sum_sub_distrib,← Finset.mul_sum,← add_div]
  ring

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_3_R1.H1 := by
  intro modes mass f hf
  let P (N : ℕ) := (range N).filter fun p => p.Prime ∧ p % 3 = 1
  let θ (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ)/2, √3 * (yp p : ℝ)/2⟩ : ℂ).arg
  have sub (N : ℕ) : P N ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hp,hp',_⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(mem_range.mp hp).le,hp'⟩
  have den : Tendsto (fun N : ℕ => log N * (P N).card / (N:ℝ)) atTop (𝓝 (1/2:ℝ)) := by
    simpa using remove_log_weight P sub (fun _ => 1) (by simp) _ (by simpa [P,H2] using mass)
  have cardpos : ∀ᶠ N in atTop, (P N).Nonempty := by
    filter_upwards [eventually_ge_atTop 8] with N hn
    exact ⟨7,mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩⟩
  let w (N p : ℕ) : ℝ := ((P N).card : ℝ)⁻¹
  have hu : ∀ᶠ N in atTop, ∑ p ∈ P N, w N p = 1 := by
    filter_upwards [cardpos] with N hn
    simp [w,hn.card_ne_zero]
  have hc (k : ℕ) (hk : k ≠ 0) : Tendsto
      (fun N => ∑ p ∈ P N, w N p * cos ((k:ℝ)*(6*θ p))) atTop (𝓝 0) := by
    let v (p : ℕ) := cos ((k:ℝ)*(6*θ p))
    have raw := remove_log_weight P sub v (fun p => abs_cos_le_one _) 0 (modes k hk)
    have divlim := raw.div den (by norm_num)
    rw [zero_div] at divlim
    apply divlim.congr'
    filter_upwards [eventually_ge_atTop 2] with N hn
    have l : log N ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have n : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [w,← Finset.mul_sum]
    change log N * (∑ p ∈ P N, v p) / N / (log N * (P N).card / N) = _ * (∑ p ∈ P N,v p)
    by_cases h : (P N).card = 0
    · simp [h]
    · field_simp [l,n,h]
  have he := sector_criterion P θ w sector_angle (by intro n p; dsimp [w]; positivity) hu hc f hf
  change Tendsto (fun n => (∑ p ∈ P n, f (θ p)) / (P n).card) atTop _
  simpa only [w,← Finset.mul_sum,div_eq_inv_mul] using he

end OMA.R_OeisA218585_conjecture_3_R1_H1_R1
