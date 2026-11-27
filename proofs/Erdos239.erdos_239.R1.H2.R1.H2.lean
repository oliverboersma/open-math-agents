import OMAReductions.R_Erdos239_erdos_239_R1_H2_R1
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The uniform-distance Halász mean-value estimate for bounded real multiplicative functions

The proof first removes the summable prime-power correction. For the completely
multiplicative core it combines two arithmetic log-weight expansions with smooth
Fourier inversion, unit-band mean-square estimates, and Euler product decay.
The cutoff is then removed via its discrete error estimate.

The analytic structure is inspired by Granville, Harper and Soundararajan,
arXiv:1706.03755. The target uniform-distance formulation is the upstream
Erdős 239 reduction by Marcus Buffett.
-/

namespace OMA239Independent

/- Source section: 239-smoothed-convergence.lean -/
section


/- Source section: 239-smoothed-limit.lean -/
section


/- Source section: 239-mangoldt-score-product.lean -/
section


/- Source section: 239-lseries-energy.lean -/
section
open MeasureTheory
open Finset MeasureTheory
open scoped ComplexConjugate
open Finset
open scoped ArithmeticFunction


/- Source section: 239-shifted-band.lean -/
section



theorem tent_cosine_integral (a M : ℝ) (ha : a ≠ 0) :
    (∫ t in (0 : ℝ)..M, (M-t)*Real.cos (a*t)) = (1-Real.cos (a*M))/a^2 := by
  let F (t : ℝ) := (M-t)*Real.sin (a*t)/a - Real.cos (a*t)/a^2
  have hd (t : ℝ) : HasDerivAt F ((M-t)*Real.cos (a*t)) t := by
    have hsub : HasDerivAt (fun x : ℝ => M-x) (-1) t :=
      by simpa [Pi.sub_def, id] using (hasDerivAt_const t M).sub (hasDerivAt_id t)
    have hmul : HasDerivAt (fun x : ℝ => a*x) a t := by
      simpa using (hasDerivAt_id t).const_mul a
    have hs : HasDerivAt (fun x : ℝ => Real.sin (a*x)) (Real.cos (a*t)*a) t :=
      (Real.hasDerivAt_sin (a*t)).comp t hmul
    have hc : HasDerivAt (fun x : ℝ => Real.cos (a*x)) (-Real.sin (a*t)*a) t :=
      (Real.hasDerivAt_cos (a*t)).comp t hmul
    have hD := ((hsub.mul hs).div_const a).sub (hc.div_const (a^2))
    change HasDerivAt (fun x : ℝ => (M-x)*Real.sin (a*x)/a - Real.cos (a*x)/a^2) _ t at hD
    convert hD using 1
    field_simp
    <;> ring
  have hcont : Continuous (fun t : ℝ => (M-t)*Real.cos (a*t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hcont.intervalIntegrable _ _)]
  simp only [F, sub_self, zero_mul, zero_div, zero_sub, mul_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem tent_cosine_integral_abs_le (a M : ℝ) (ha : a ≠ 0) :
    |∫ t in (0 : ℝ)..M, (M-t)*Real.cos (a*t)| ≤ 2/a^2 := by
  rw [tent_cosine_integral a M ha, abs_of_nonneg]
  · apply div_le_div_of_nonneg_right _ (sq_nonneg a)
    linarith [Real.neg_one_le_cos (a*M)]
  · exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)


theorem tent_cosine_energy_bound (a M : ℝ) (hM : 0 ≤ M) :
    |∫ t in (0 : ℝ)..M, (M-t)*Real.cos (a*t)| ≤ M^2/2 := by
  have hi : (∫ t in (0 : ℝ)..M, (M-t)*Real.cos (a*t)) ≥ 0 := by
    by_cases ha : a = 0
    · simp only [ha, zero_mul, Real.cos_zero, mul_one]
      apply intervalIntegral.integral_nonneg hM
      intro t ht
      exact sub_nonneg.mpr ht.2
    · rw [tent_cosine_integral _ _ ha]
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _)
  rw [abs_of_nonneg hi]
  have hI : (∫ t in (0 : ℝ)..M, M-t) = M^2/2 := by
    have hc : IntervalIntegrable (fun _ : ℝ => M) volume 0 M := continuous_const.intervalIntegrable _ _
    have ht : IntervalIntegrable (fun t : ℝ => t) volume 0 M := continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hc ht, intervalIntegral.integral_const, integral_id]
    simp [smul_eq_mul]
    ring
  rw [← hI]
  have hc : Continuous (fun t : ℝ => (M-t)*Real.cos (a*t)) := by fun_prop
  have hC : Continuous (fun t : ℝ => M-t) := by fun_prop
  exact intervalIntegral.integral_mono_on hM (hc.intervalIntegrable ..) (hC.intervalIntegrable ..)
    (fun t ht => mul_le_of_le_one_right (sub_nonneg.mpr ht.2) (Real.cos_le_one _))


noncomputable def tentBinKernel (M : ℝ) (k : ℤ) : ℝ :=
  (M^2+16)/(1+(k : ℝ)^2)

theorem tentBinKernel_nonneg (M : ℝ) (k : ℤ) : 0 ≤ tentBinKernel M k := by
  unfold tentBinKernel
  positivity

theorem tentBinKernel_even (M : ℝ) (k : ℤ) : tentBinKernel M (-k) = tentBinKernel M k := by
  simp [tentBinKernel]

theorem tentBinKernel_summable (M : ℝ) : Summable (tentBinKernel M) := by
  classical
  let z : ℤ → ℝ := fun k => if k=0 then M^2+16 else 0
  have hz : Summable z := by
    apply summable_of_finite_support
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro k hk
    by_contra h
    have hn : k ≠ 0 := by simpa using h
    exact hk (by simp [z,hn])
  have hs : Summable (fun k : ℤ => (M^2+16)*(1/(k : ℝ)^2) + z k) :=
    ((Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left _).add hz
  refine hs.of_nonneg_of_le (tentBinKernel_nonneg M) ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simp [tentBinKernel,z]
  have hr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hr2 : 0 < (k : ℝ)^2 := sq_pos_of_ne_zero hr
  simp only [z, if_neg hk, add_zero, tentBinKernel, mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) hr2 (by linarith)

theorem tent_integral_le_bin_kernel (M x y : ℝ) (i j : ℤ) (hM : 0 ≤ M)
    (hix : (i : ℝ) ≤ x) (hxi : x < (i : ℝ)+1)
    (hjy : (j : ℝ) ≤ y) (hyj : y < (j : ℝ)+1) :
    |∫ t in (0 : ℝ)..M, (M-t)*Real.cos ((x-y)*t)| ≤ tentBinKernel M (i-j) := by
  have he : ((i-j : ℤ) : ℝ) = (i : ℝ)-(j : ℝ) := by push_cast; rfl
  rw [tentBinKernel, he]
  let D := |(i : ℝ)-(j : ℝ)|
  have hD : 0 ≤ D := abs_nonneg _
  have hsqD : D^2 = ((i : ℝ)-(j : ℝ))^2 := sq_abs _
  rw [← hsqD]
  by_cases hsmall : D ≤ 1
  · refine (tent_cosine_energy_bound (x-y) M hM).trans ?_
    apply (le_div_iff₀ (by positivity)).2
    have hm := mul_nonneg (sq_nonneg M) (show 0 ≤ 1-D^2 by nlinarith)
    nlinarith only [hm]
  have hD2 : 2 ≤ D := by
    have hdint : |i-j| ≥ (2 : ℤ) := by
      have hh : (1 : ℤ) < |i-j| := by
        have h := lt_of_not_ge hsmall
        change (1 : ℝ) < |(i : ℝ)-(j : ℝ)| at h
        exact_mod_cast h
      omega
    have hh : (2 : ℝ) ≤ ((|i-j| : ℤ) : ℝ) := by exact_mod_cast hdint
    simpa [D,Int.cast_abs] using hh
  have hdist : D-1 ≤ |x-y| := by
    rcases abs_cases ((i : ℝ)-(j : ℝ)) with ⟨h,_⟩ | ⟨h,_⟩
    · dsimp [D]
      rw [h]
      linarith [le_abs_self (x-y)]
    · dsimp [D]
      rw [h]
      linarith [neg_le_abs (x-y)]
  have hdpos : 0 < |x-y| := by linarith
  have hne : x-y ≠ 0 := abs_pos.mp hdpos
  refine (tent_cosine_integral_abs_le (x-y) M hne).trans ?_
  have hx2 : (D/2)^2 ≤ (x-y)^2 := by
    rw [← sq_abs (x-y)]
    have hh : D/2 ≤ |x-y| := by linarith
    exact pow_le_pow_left₀ (by positivity) hh 2
  calc
    _ ≤ 2/(D/2)^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hx2
    _ = 8/D^2 := by field_simp; ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have ha := mul_nonneg (sq_nonneg M) (sq_nonneg D)
      nlinarith only [ha, hD2, sq_nonneg (D-2)]



noncomputable def exponentialScore {ι : Type*} (s : Finset ι) (a freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, (a i : ℂ) * Complex.exp (((freq i*t : ℝ) : ℂ) * Complex.I)

theorem exponentialScore_pair_re (a b x y t : ℝ) :
    (((a : ℂ) * Complex.exp (((x*t : ℝ) : ℂ) * Complex.I)) *
      conj ((b : ℂ) * Complex.exp (((y*t : ℝ) : ℂ) * Complex.I))).re =
      a*b*Real.cos ((x-y)*t) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  have he : ((a : ℂ) * Complex.exp (((x*t : ℝ) : ℂ) * Complex.I)) *
      ((b : ℂ) * Complex.exp (((y*t : ℝ) : ℂ) * (-Complex.I))) =
      ((a*b : ℝ) : ℂ) * Complex.exp ((((x-y)*t : ℝ) : ℂ) * Complex.I) := by
    have hExp : (((x*t : ℝ) : ℂ)*Complex.I) + (((y*t : ℝ) : ℂ)*(-Complex.I)) =
        (((x-y)*t : ℝ) : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [mul_mul_mul_comm, ← Complex.exp_add, hExp, ← Complex.ofReal_mul]
  rw [he, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem norm_exponentialScore_sq {ι : Type*} (s : Finset ι) (a freq : ι → ℝ) (t : ℝ) :
    ‖exponentialScore s a freq t‖^2 =
      ∑ i ∈ s, ∑ j ∈ s, a i*a j*Real.cos ((freq i-freq j)*t) := by
  let z := exponentialScore s a freq t
  have hz : ‖z‖^2 = (z * conj z).re := by
    rw [Complex.mul_conj, Complex.sq_norm, Complex.ofReal_re]
  rw [hz]
  simp only [z, exponentialScore, map_sum, sum_mul, mul_sum, Complex.re_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [exponentialScore_pair_re, mul_comm (a j) (a i),
    show (freq j-freq i)*t = -((freq i-freq j)*t) by ring, Real.cos_neg]

theorem tent_exponential_energy_identity {ι : Type*} (s : Finset ι)
    (a freq : ι → ℝ) (M : ℝ) :
    (∫ t in (0 : ℝ)..M, (M-t)*‖exponentialScore s a freq t‖^2) =
      ∑ i ∈ s, ∑ j ∈ s, a i*a j*(∫ t in (0 : ℝ)..M, (M-t)*Real.cos ((freq i-freq j)*t)) := by
  have hs : (fun t : ℝ => (M-t)*‖exponentialScore s a freq t‖^2) =
      fun t : ℝ => ∑ i ∈ s, ∑ j ∈ s, (a i*a j)*((M-t)*Real.cos ((freq i-freq j)*t)) := by
    funext t
    rw [norm_exponentialScore_sq, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hs, intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
    · intro j hj
      exact (show Continuous (fun t : ℝ => (a i*a j)*((M-t)*Real.cos ((freq i-freq j)*t))) by
        fun_prop).intervalIntegrable _ _
  · intro i hi
    have h : ∀ j ∈ s, IntervalIntegrable
        (fun t : ℝ => (a i*a j)*((M-t)*Real.cos ((freq i-freq j)*t))) volume 0 M := by
      intro j hj
      exact (show Continuous (fun t : ℝ => (a i*a j)*((M-t)*Real.cos ((freq i-freq j)*t))) by
        fun_prop).intervalIntegrable _ _
    have he : (∑ j ∈ s, fun t : ℝ => (a i*a j)*((M-t)*Real.cos ((freq i-freq j)*t))) =
        fun t : ℝ => ∑ j ∈ s, (a i*a j)*((M-t)*Real.cos ((freq i-freq j)*t)) := by
      funext t
      rw [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum s h



theorem finite_symmetric_row_bound {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (K : ι → ι → ℝ) (C : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, K i j ≤ C) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * b i * b j) ≤ C * ∑ i ∈ s, (b i)^2 := by
  have hpoint (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      K i j * b i * b j ≤ (K i j * (b i)^2 + K i j * (b j)^2)/2 := by
    have hsq : 0 ≤ K i j * (b i-b j)^2 := mul_nonneg (hK i hi j hj) (sq_nonneg _)
    nlinarith only [hsq]
  have hswap :
      (∑ i ∈ s, ∑ j ∈ s, K i j * (b j)^2) =
      (∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (K i j * (b i)^2 + K i j * (b j)^2)/2 := by
      exact sum_le_sum fun i hi => sum_le_sum fun j hj => hpoint i j hi hj
    _ = ∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2 := by
      simp only [div_eq_mul_inv, add_mul, sum_add_distrib, ← sum_mul, hswap]
      ring
    _ = ∑ i ∈ s, (∑ j ∈ s, K i j) * (b i)^2 := by simp only [sum_mul]
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)


theorem symmetric_difference_kernel_bound (s : Finset ℤ) (b : ℤ → ℝ)
    (K : ℤ → ℝ) (hK : ∀ n, 0 ≤ K n) (heven : ∀ n, K (-n) = K n)
    (hsum : Summable K) :
    (∑ i ∈ s, ∑ j ∈ s, K (i-j) * b i * b j) ≤
      (∑' n : ℤ, K n) * ∑ i ∈ s, (b i)^2 := by
  classical
  refine finite_symmetric_row_bound s b (fun i j => K (i-j)) _ (fun i _ j _ => hK (i-j)) ?_ ?_
  · intro i hi j hj
    rw [show i-j = -(j-i) by omega, heven]
  · intro i hi
    let f (j : ℤ) := i-j
    have hinj : Function.Injective f := by
      intro j k h
      dsimp [f] at h
      omega
    calc
      _ = ∑ k ∈ s.image f, K k := (sum_image hinj.injOn).symm
      _ ≤ _ := hsum.sum_le_tsum _ fun n _ => hK n


theorem binned_quadratic_identity {ι : Type*} (A : Finset ι) (I : Finset ℤ)
    (b : ι → ℤ) (w : ι → ℝ) (K : ℤ → ℝ) (h : ∀ a ∈ A, b a ∈ I) :
    (∑ a ∈ A, ∑ c ∈ A, K (b a-b c)*w a*w c) =
      ∑ i ∈ I, ∑ j ∈ I, K (i-j)*
        (∑ a ∈ A.filter (fun a => b a=i), w a)*
        (∑ c ∈ A.filter (fun c => b c=j), w c) := by
  classical
  rw [← sum_fiberwise_of_maps_to h]
  apply sum_congr rfl
  intro i hi
  have hnormalize : ∀ a ∈ A.filter (fun a => b a=i),
      (∑ c ∈ A, K (b a-b c)*w a*w c) =
        ∑ j ∈ I, K (i-j)*w a*(∑ c ∈ A.filter (fun c => b c=j), w c) := by
    intro a ha
    rw [(mem_filter.mp ha).2, ← sum_fiberwise_of_maps_to h]
    apply sum_congr rfl
    intro j hj
    rw [mul_sum]
    apply sum_congr rfl
    intro c hc
    rw [(mem_filter.mp hc).2]
  rw [sum_congr rfl hnormalize, sum_comm]
  apply sum_congr rfl
  intro j hj
  simp only [mul_sum, sum_mul]
  rw [sum_comm]

theorem binned_quadratic_bound {ι : Type*} (A : Finset ι) (I : Finset ℤ)
    (b : ι → ℤ) (w : ι → ℝ) (K : ℤ → ℝ) (C : ℝ)
    (h : ∀ a ∈ A, b a ∈ I) (hK : ∀ n, 0 ≤ K n) (heven : ∀ n, K (-n) = K n)
    (hsum : Summable K) (_hC : 0 ≤ C)
    (hw : ∀ i ∈ I, |∑ a ∈ A.filter (fun a => b a=i), w a| ≤ C) :
    (∑ a ∈ A, ∑ c ∈ A, K (b a-b c)*w a*w c) ≤
      (∑' n : ℤ, K n) * (I.card * C^2) := by
  rw [binned_quadratic_identity A I b w K h]
  refine (symmetric_difference_kernel_bound I (fun i => ∑ a ∈ A.filter (fun a => b a=i), w a)
    K hK heven hsum).trans ?_
  apply mul_le_mul_of_nonneg_left _ (tsum_nonneg hK)
  calc
    _ ≤ ∑ i ∈ I, C^2 := by
      apply sum_le_sum
      intro i hi
      have hsq := pow_le_pow_left₀ (abs_nonneg _) (hw i hi) 2
      simpa using hsq
    _ = _ := by simp [nsmul_eq_mul]


theorem tent_band_energy_bound {ι : Type*} (A : Finset ι) (I : Finset ℤ)
    (a freq : ι → ℝ) (b : ι → ℤ) (C M : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbin : ∀ k ∈ A, b k ∈ I)
    (hf : ∀ k ∈ A, (b k : ℝ) ≤ freq k ∧ freq k < (b k : ℝ)+1)
    (hw : ∀ i ∈ I, (∑ k ∈ A.filter (fun k => b k=i), |a k|) ≤ C) :
    (∫ t in (0 : ℝ)..M, (M-t)*‖exponentialScore A a freq t‖^2) ≤
      (∑' n : ℤ, tentBinKernel M n) * (I.card * C^2) := by
  rw [tent_exponential_energy_identity]
  calc
    _ ≤ ∑ i ∈ A, ∑ j ∈ A, tentBinKernel M (b i-b j) * |a i| * |a j| := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      let J : ℝ := ∫ t in (0 : ℝ)..M, (M-t)*Real.cos ((freq i-freq j)*t)
      change a i*a j*J ≤ _
      have hk : |J| ≤ tentBinKernel M (b i-b j) :=
        tent_integral_le_bin_kernel M _ _ _ _ hM (hf i hi).1 (hf i hi).2 (hf j hj).1 (hf j hj).2
      calc
        _ ≤ |a i*a j*J| := le_abs_self _
        _ = |a i| * |a j| * |J| := by rw [abs_mul, abs_mul]
        _ ≤ |a i| * |a j| * tentBinKernel M (b i-b j) :=
          mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = _ := by ring
    _ ≤ _ := binned_quadratic_bound A I b (fun k => |a k|) (tentBinKernel M) C hbin
      (tentBinKernel_nonneg M) (tentBinKernel_even M) (tentBinKernel_summable M) hC
      (fun i hi => by
        rw [abs_of_nonneg (sum_nonneg fun _ _ => abs_nonneg _)]
        exact hw i hi)

theorem band_energy_bound {ι : Type*} (A : Finset ι) (I : Finset ℤ)
    (a freq : ι → ℝ) (b : ι → ℤ) (C T : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hbin : ∀ k ∈ A, b k ∈ I)
    (hf : ∀ k ∈ A, (b k : ℝ) ≤ freq k ∧ freq k < (b k : ℝ)+1)
    (hw : ∀ i ∈ I, (∑ k ∈ A.filter (fun k => b k=i), |a k|) ≤ C) :
    (∫ t in (0 : ℝ)..T, ‖exponentialScore A a freq t‖^2) ≤
      ((∑' n : ℤ, tentBinKernel (2*T) n) * (I.card * C^2))/T := by
  let E (t : ℝ) := ‖exponentialScore A a freq t‖^2
  let W (t : ℝ) := (2*T-t)*E t
  have hE : Continuous E := by
    unfold E exponentialScore
    fun_prop
  have hW : Continuous W := (continuous_const.sub continuous_id).mul hE
  have h1 : T*(∫ t in (0 : ℝ)..T, E t) ≤ ∫ t in (0 : ℝ)..T, W t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT.le
      ((continuous_const.mul hE).intervalIntegrable _ _) (hW.intervalIntegrable _ _) ?_
    intro t ht
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) (sq_nonneg _)
  have h2 : (∫ t in (0 : ℝ)..T, W t) ≤ ∫ t in (0 : ℝ)..(2*T), W t := by
    have hnon : 0 ≤ ∫ t in T..(2*T), W t := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro t ht
      exact mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg _)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hW.intervalIntegrable 0 T) (hW.intervalIntegrable T (2*T))]
    linarith
  have h3 := tent_band_energy_bound A I a freq b C (2*T) (by positivity) hC hbin hf hw
  apply (le_div_iff₀ hT).2
  rw [mul_comm]
  exact h1.trans (h2.trans h3)


noncomputable def complexScore {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, a i * Complex.exp (((freq i*t : ℝ) : ℂ) * Complex.I)

theorem complexScore_add_time {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ) (T t : ℝ) :
    complexScore s a freq (t+T) =
      complexScore s (fun i => a i*Complex.exp (((freq i*T : ℝ) : ℂ)*Complex.I)) freq t := by
  unfold complexScore
  apply sum_congr rfl
  intro i hi
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

theorem complexScore_real_imag {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    complexScore s a freq t = exponentialScore s (fun i => (a i).re) freq t +
      exponentialScore s (fun i => (a i).im) freq t * Complex.I := by
  unfold complexScore exponentialScore
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have he := Complex.re_add_im (a i)
  nth_rw 1 [← he]
  ring

theorem complexScore_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    ‖complexScore s a freq t‖^2 ≤
      2*‖exponentialScore s (fun i => (a i).re) freq t‖^2 +
      2*‖exponentialScore s (fun i => (a i).im) freq t‖^2 := by
  rw [complexScore_real_imag]
  let Q := exponentialScore s (fun i => (a i).re) freq t
  let R := exponentialScore s (fun i => (a i).im) freq t
  have h := norm_add_le Q (R*Complex.I)
  rw [norm_mul, Complex.norm_I, mul_one] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  change ‖Q+R*Complex.I‖^2 ≤ _
  exact hsq.trans (by nlinarith only [sq_nonneg (‖Q‖-‖R‖)])

theorem shifted_complex_band_energy {ι : Type*} (A : Finset ι) (I : Finset ℤ)
    (a : ι → ℂ) (freq : ι → ℝ) (b : ι → ℤ) (C T x : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hbin : ∀ k ∈ A, b k ∈ I)
    (hf : ∀ k ∈ A, (b k : ℝ) ≤ freq k ∧ freq k < (b k : ℝ)+1)
    (hw : ∀ i ∈ I, (∑ k ∈ A.filter (fun k => b k=i), ‖a k‖) ≤ C) :
    (∫ t in x..(T+x), ‖complexScore A a freq t‖^2) ≤
      4*(((∑' n : ℤ, tentBinKernel (2*T) n)*(I.card*C^2))/T) := by
  let a' (i : ι) : ℂ := a i*Complex.exp (((freq i*x : ℝ) : ℂ)*Complex.I)
  have ha' (i : ι) : ‖a' i‖ = ‖a i‖ := by
    dsimp only [a']
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hh := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := T)
    (fun t : ℝ => ‖complexScore A a freq t‖^2) x
  simp only [zero_add] at hh
  rw [← hh]
  have htranslate :
      (∫ t in (0:ℝ)..T, ‖complexScore A a freq (t+x)‖^2) =
      ∫ t in (0:ℝ)..T, ‖complexScore A a' freq t‖^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖complexScore A a freq (t+x)‖^2 = ‖complexScore A a' freq t‖^2
    rw [complexScore_add_time]
  rw [htranslate]
  let Q (t : ℝ) : ℝ := ‖exponentialScore A (fun i => (a' i).re) freq t‖^2
  let R (t : ℝ) : ℝ := ‖exponentialScore A (fun i => (a' i).im) freq t‖^2
  let W (t : ℝ) : ℝ := ‖complexScore A a' freq t‖^2
  have hQ : Continuous Q := by unfold Q exponentialScore; fun_prop
  have hR : Continuous R := by unfold R exponentialScore; fun_prop
  have hW : Continuous W := by unfold W complexScore; fun_prop
  have hQR : Continuous (fun t => 2*Q t+2*R t) :=
    (continuous_const.mul hQ).add (continuous_const.mul hR)
  have hQr := band_energy_bound A I (fun i => (a' i).re) freq b C T hT hC hbin hf (by
    intro i hi
    refine (sum_le_sum fun j hj => ?_).trans (hw i hi)
    rw [← ha' j]
    exact Complex.abs_re_le_norm _)
  have hRr := band_energy_bound A I (fun i => (a' i).im) freq b C T hT hC hbin hf (by
    intro i hi
    refine (sum_le_sum fun j hj => ?_).trans (hw i hi)
    rw [← ha' j]
    exact Complex.abs_im_le_norm _)
  calc
    _ ≤ ∫ t in (0:ℝ)..T, (2*Q t+2*R t) :=
      intervalIntegral.integral_mono_on hT.le (hW.intervalIntegrable ..) (hQR.intervalIntegrable ..)
        (fun t _ => complexScore_energy _ _ _ _)
    _ = 2*(∫ t in (0:ℝ)..T, Q t)+2*(∫ t in (0:ℝ)..T, R t) := by
      have hq : IntervalIntegrable (fun t => (2:ℝ)*Q t) volume 0 T :=
        (continuous_const.mul hQ).intervalIntegrable _ _
      have hr : IntervalIntegrable (fun t => (2:ℝ)*R t) volume 0 T :=
        (continuous_const.mul hR).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hq hr,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      change (2 * (∫ t in (0:ℝ)..T, Q t) + 2 * (∫ t in (0:ℝ)..T, R t)) ≤ _
      linarith [hQr,hRr]

end

/- Source section: 239-mangoldt-tail-mass.lean -/
section


noncomputable def mangoldtLogScoreCoeff (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  c n * Λ n / (n : ℝ)

theorem chebyshev_bin_mass (A : Finset ℕ) (c : ℕ → ℝ) (i : ℤ)
    (hA : ∀ n ∈ A, 0 < n) (hc : ∀ n ∈ A, |c n| ≤ 1) :
    (∑ n ∈ A.filter (fun n : ℕ => ⌊Real.log (n : ℝ)⌋=i), |mangoldtLogScoreCoeff c n|) ≤
      (Real.log 4+4)*Real.exp 1 := by
  let U := Real.exp ((i : ℝ)+1)
  let D := A.filter (fun n : ℕ => ⌊Real.log (n : ℝ)⌋=i)
  have hbin (n : ℕ) (hn : n ∈ D) : Real.exp (i : ℝ) ≤ n ∧ (n : ℝ) < U := by
    obtain ⟨hm,he⟩ := mem_filter.mp hn
    have hp : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (hA n hm)
    have h1 := Int.floor_le (Real.log (n : ℝ))
    have h2 := Int.lt_floor_add_one (Real.log (n : ℝ))
    rw [he] at h1 h2
    refine ⟨?_,?_⟩
    · simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr h1
    · simpa only [U, Real.exp_log hp] using Real.exp_lt_exp.mpr h2
  have hsubset : D ⊆ Icc 0 ⌊U⌋₊ := by
    intro n hn
    exact mem_Icc.mpr ⟨Nat.zero_le _, (Nat.le_floor_iff (Real.exp_nonneg _)).2 (hbin n hn).2.le⟩
  have h₁ (n : ℕ) (hn : n ∈ D) :
      |mangoldtLogScoreCoeff c n| ≤ (Real.exp (i : ℝ))⁻¹ * Λ n := by
    obtain ⟨hm,he⟩ := mem_filter.mp hn
    rw [mangoldtLogScoreCoeff, abs_div, abs_mul,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)),
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    calc
      _ ≤ (1 : ℝ)*Λ n/(n : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hc n hm)
          ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg _)
      _ ≤ Λ n / Real.exp (i : ℝ) := by
        rw [one_mul]
        exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
          (Real.exp_pos _) (hbin n hn).1
      _ = _ := by rw [div_eq_inv_mul]
  calc
    _ ≤ ∑ n ∈ D, (Real.exp (i : ℝ))⁻¹*Λ n := sum_le_sum h₁
    _ ≤ ∑ n ∈ Icc 0 ⌊U⌋₊, (Real.exp (i : ℝ))⁻¹*Λ n :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun n hn hnot => by positivity)
    _ = (Real.exp (i : ℝ))⁻¹*Chebyshev.psi U := by
      rw [← mul_sum, ← Chebyshev.psi_eq_sum_Icc]
    _ ≤ (Real.exp (i : ℝ))⁻¹*((Real.log 4+4)*U) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (Real.exp_nonneg _)) (by positivity)
    _ = _ := by
      rw [show U = Real.exp (i : ℝ)*Real.exp 1 from Real.exp_add _ _]
      field_simp


theorem mangoldt_log_interval_mass (A : Finset ℕ) (lo hi : ℝ) (hlo : lo ≤ hi)
    (hA : ∀ n ∈ A, 0 < n ∧ lo ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ hi) :
    (∑ n ∈ A, Λ n/(n : ℝ)) ≤ (hi-lo+2)*((Real.log 4+4)*Real.exp 1) := by
  classical
  let b (n : ℕ) : ℤ := ⌊Real.log (n : ℝ)⌋
  let I : Finset ℤ := Icc ⌊lo⌋ ⌊hi⌋
  let C := (Real.log 4+4)*Real.exp 1
  have hC : 0 ≤ C := by
    dsimp [C]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hbin : ∀ n ∈ A, b n ∈ I := by
    intro n hn
    exact mem_Icc.mpr ⟨Int.floor_mono (hA n hn).2.1, Int.floor_mono (hA n hn).2.2⟩
  have hcard : (I.card : ℝ) ≤ hi-lo+2 := by
    have hI : (I.card : ℤ) = ⌊hi⌋ + 1 - ⌊lo⌋ :=
      Int.card_Icc_of_le (a := ⌊lo⌋) (b := ⌊hi⌋) ((Int.floor_mono hlo).trans (by omega))
    have hR : (I.card : ℝ) = (⌊hi⌋ : ℤ) + 1 - (⌊lo⌋ : ℤ) := by exact_mod_cast hI
    rw [hR]
    linarith [Int.floor_le hi, Int.lt_floor_add_one lo]
  rw [← sum_fiberwise_of_maps_to hbin (fun n => Λ n/(n : ℝ))]
  calc
    _ ≤ ∑ i ∈ I, C := by
      apply sum_le_sum
      intro i hi'
      have h := chebyshev_bin_mass A (fun _ => 1) i (fun n hn => (hA n hn).1)
        (fun n hn => by norm_num)
      have heq : (∑ n ∈ A.filter (fun n => b n=i), Λ n/(n : ℝ)) =
          ∑ n ∈ A.filter (fun n => b n=i), |mangoldtLogScoreCoeff (fun _ => 1) n| := by
        apply sum_congr rfl
        intro n hn
        simp only [mangoldtLogScoreCoeff, one_mul]
        rw [abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))]
      rw [heq]
      exact h
    _ = (I.card : ℝ)*C := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

end

/- Source section: 239-smooth-lseries.lean -/
section



noncomputable def twistedWeight (c : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℂ :=
  (((c n / (n : ℝ) : ℝ) : ℂ) * Complex.exp (((t*Real.log n : ℝ) : ℂ)*Complex.I))

theorem norm_twistedWeight (c : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ‖twistedWeight c t n‖ = |c n|/(n : ℝ) := by
  rw [twistedWeight, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_div, show |(n : ℝ)| = (n : ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]

theorem twistedWeight_multiplicative (c : ℕ → ℝ) (t : ℝ)
    (hc : ∀ a b : ℕ, c (a*b) = c a*c b) (a b : ℕ) :
    twistedWeight c t (a*b) = twistedWeight c t a * twistedWeight c t b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [twistedWeight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [twistedWeight]
  rw [twistedWeight, twistedWeight, twistedWeight, hc, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  have he :
      (((t*(Real.log a+Real.log b) : ℝ) : ℂ)*Complex.I) =
      (((t*Real.log a : ℝ) : ℂ)*Complex.I) + (((t*Real.log b : ℝ) : ℂ)*Complex.I) := by
    rw [mul_add, Complex.ofReal_add, add_mul]
  rw [he, Complex.exp_add,
    show c a*c b/((a : ℝ)*(b : ℝ)) = (c a/(a : ℝ))*(c b/(b : ℝ)) by rw [div_mul_div_comm],
    Complex.ofReal_mul, mul_mul_mul_comm]

noncomputable def twistedWeightHom (c : ℕ → ℝ) (t : ℝ) (h1 : c 1 = 1)
    (hc : ∀ a b : ℕ, c (a*b) = c a*c b) : ℕ →* ℂ where
  toFun := twistedWeight c t
  map_one' := by simp [twistedWeight,h1]
  map_mul' := twistedWeight_multiplicative c t hc

theorem smooth_twisted_euler (c : ℕ → ℝ) (t : ℝ) (N : ℕ) (h1 : c 1 = 1)
    (hc : ∀ a b : ℕ, c (a*b) = c a*c b) (hb : ∀ n : ℕ, |c n| ≤ 1) :
    Summable (fun n : (N+1).smoothNumbers => ‖twistedWeight c t n.val‖) ∧
      HasSum (fun n : (N+1).smoothNumbers => twistedWeight c t n.val)
        (∏ p ∈ N.primesLE, (1-twistedWeight c t p)⁻¹) := by
  let m := twistedWeightHom c t h1 hc
  have hp (p : ℕ) (h : p.Prime) : ‖m p‖ < 1 := by
    change ‖twistedWeight c t p‖ < 1
    rw [norm_twistedWeight]
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast h.one_lt
    exact (div_lt_iff₀ (by linarith : (0 : ℝ) < p)).2 (by simpa using (hb p).trans_lt hpR)
  exact EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := m) (fun {p} => hp p) (N+1)



noncomputable def LPhasePoint (t : ℝ) : ℂ := 1-((t : ℝ) : ℂ)*Complex.I

noncomputable def LPhaseTerm (a : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  (a n/(n : ℂ)) * Complex.exp (((t*Real.log n : ℝ) : ℂ)*Complex.I)

theorem LSeries_term_phase (a : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    LSeries.term a (LPhasePoint t) n = LPhaseTerm a t n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LPhaseTerm]
  rw [LSeries.term_def, if_neg hn, div_eq_mul_inv, ← Complex.cpow_neg, LPhaseTerm,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]
  have harg :
      ((Real.log n : ℝ) : ℂ) * (-LPhasePoint t) =
        -((Real.log n : ℝ) : ℂ) + (((t*Real.log n : ℝ) : ℂ)*Complex.I) := by
    unfold LPhasePoint
    rw [Complex.ofReal_mul]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)),
      Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_assoc]

theorem LSeries_phase (a : ℕ → ℂ) (t : ℝ) :
    LSeries a (LPhasePoint t) = ∑' n : ℕ, LPhaseTerm a t n := by
  unfold LSeries
  apply tsum_congr
  intro n
  exact LSeries_term_phase a t n

theorem phaseSummable (a : ℕ → ℂ) (t : ℝ)
    (hs : Summable (fun n : ℕ => ‖a n / (n : ℂ)‖)) :
    LSeriesSummable a (LPhasePoint t) := by
  unfold LSeriesSummable
  apply Summable.of_norm
  refine hs.congr fun n => ?_
  rw [LSeries_term_phase, LPhaseTerm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem triple_LSeries_phase (a b c : ArithmeticFunction ℂ) (t : ℝ)
    (ha : LSeriesSummable a (LPhasePoint t)) (hb : LSeriesSummable b (LPhasePoint t))
    (hc : LSeriesSummable c (LPhasePoint t)) :
    (∑' n : ℕ, LPhaseTerm (a*(b*c) : ArithmeticFunction ℂ) t n) =
      (∑' n : ℕ, LPhaseTerm a t n) * (∑' n : ℕ, LPhaseTerm b t n) *
        (∑' n : ℕ, LPhaseTerm c t n) := by
  simp only [← LSeries_phase]
  rw [ArithmeticFunction.LSeries_mul' ha (ArithmeticFunction.LSeriesSummable_mul hb hc),
    ArithmeticFunction.LSeries_mul' hb hc, mul_assoc]


noncomputable def arithOfReal (f : ArithmeticFunction ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => ((f n : ℝ) : ℂ), by simp⟩

theorem arithOfReal_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithOfReal f n = ((f n : ℝ) : ℂ) := rfl

theorem arithOfReal_mul (f g : ArithmeticFunction ℝ) :
    arithOfReal (f*g) = arithOfReal f * arithOfReal g := by
  ext n
  simp only [arithOfReal_apply, ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

noncomputable def smoothPart (f : ArithmeticFunction ℝ) (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n∈(N+1).smoothNumbers then f n else 0, by
    split_ifs <;> simp⟩

theorem smoothPart_agrees (f : ArithmeticFunction ℝ) (N n : ℕ) (hn : n ≤ N) :
    smoothPart f N n = f n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  change (if n∈(N+1).smoothNumbers then f n else 0) = f n
  rw [if_pos (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0) (Nat.lt_succ_of_le hn))]

theorem convolution_agrees_below (f g F G : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ n ≤ N, f n=F n) (hg : ∀ n ≤ N, g n=G n) :
    ∀ n ≤ N, (f*g) n = (F*G) n := by
  intro n hn
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply sum_congr rfl
  intro uv huv
  have h := Nat.mem_divisorsAntidiagonal.mp huv
  rw [hf _ ((Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) ⟨uv.2,h.1.symm⟩).trans hn),
    hg _ ((Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) ⟨uv.1,by rw [mul_comm,h.1]⟩).trans hn)]

theorem normSum_smoothPart (f : ArithmeticFunction ℝ) (N : ℕ)
    (h1 : f 1 = 1) (hm : ∀ m n : ℕ, f (m*n) = f m * f n) (hf : ∀ n : ℕ, |f n| ≤ 1) :
    Summable (fun n : ℕ => ‖arithOfReal (smoothPart f N) n/(n : ℂ)‖) := by
  have hs := (smooth_twisted_euler f 0 N h1 hm hf).1
  have hS : Summable (((N+1).smoothNumbers).indicator (fun n : ℕ => ‖twistedWeight f 0 n‖)) :=
    summable_subtype_iff_indicator.mp hs
  refine hS.congr fun n => ?_
  by_cases hn : n∈(N+1).smoothNumbers
  · rw [Set.indicator_of_mem hn, norm_twistedWeight, arithOfReal_apply]
    change _ = ‖(((if n∈(N+1).smoothNumbers then f n else 0) : ℝ) : ℂ)/(n : ℂ)‖
    rw [if_pos hn, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_of_nonneg (show (0:ℝ) ≤ n by positivity)]
  · rw [Set.indicator_of_notMem hn]
    change 0 = ‖(((if n∈(N+1).smoothNumbers then f n else 0) : ℝ) : ℂ)/(n : ℂ)‖
    simp [hn]

theorem smoothPart_LSeries_product (f : ArithmeticFunction ℝ) (N : ℕ) (t : ℝ)
    (h1 : f 1 = 1) (hm : ∀ m n : ℕ, f (m*n) = f m * f n) (hf : ∀ n : ℕ, |f n| ≤ 1) :
    LSeries (arithOfReal (smoothPart f N)) (LPhasePoint t) =
      ∏ p ∈ N.primesLE, (1-twistedWeight f t p)⁻¹ := by
  have hs := (smooth_twisted_euler f t N h1 hm hf).2.tsum_eq
  rw [_root_.tsum_subtype] at hs
  rw [LSeries_phase, ← hs]
  apply tsum_congr
  intro n
  by_cases hn : n∈(N+1).smoothNumbers
  · rw [Set.indicator_of_mem hn, LPhaseTerm, arithOfReal_apply]
    change ((((if n∈(N+1).smoothNumbers then f n else 0) : ℝ) : ℂ)/(n : ℂ)) * _ = _
    rw [if_pos hn, twistedWeight, Complex.ofReal_div, Complex.ofReal_natCast]
  · rw [Set.indicator_of_notMem hn, LPhaseTerm, arithOfReal_apply]
    change ((((if n∈(N+1).smoothNumbers then f n else 0) : ℝ) : ℂ)/(n : ℂ)) * _ = 0
    simp [hn]

end


theorem LSeries_finite_score (g : ArithmeticFunction ℝ) (A : Finset ℕ) (t : ℝ)
    (hg : ∀ n ∉ A, g n = 0) :
    LSeries (arithOfReal g) (LPhasePoint t) =
      complexScore A (fun n : ℕ => (((g n/(n : ℝ) : ℝ) : ℂ)))
        (fun n : ℕ => Real.log n) t := by
  rw [LSeries_phase, tsum_eq_sum (s := A)]
  · apply sum_congr rfl
    intro n hn
    rw [LPhaseTerm, arithOfReal_apply, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
    ring
  · intro n hn
    simp [LPhaseTerm, arithOfReal_apply, hg n hn]

theorem mangoldt_LSeries_unit_energy (g : ArithmeticFunction ℝ) (A : Finset ℕ) (N : ℕ)
    (D : ℝ) (hN : 0 < N) (hD : 0 ≤ D)
    (hA : A ⊆ Icc 1 N) (hs : ∀ n ∉ A, g n=0)
    (hg : ∀ n ∈ A, |g n| ≤ D*Λ n) (k : ℤ) :
    (∫ t in (k : ℝ)..((k : ℝ)+1),
      ‖LSeries (arithOfReal g) (LPhasePoint (2*Real.pi*t))‖^2) ≤
      (2*Real.pi)⁻¹ * (4*(((∑' z : ℤ, tentBinKernel (2*(2*Real.pi)) z)*
        ((Real.log N+1)*(D*((Real.log 4+4)*Real.exp 1))^2))/(2*Real.pi))) := by
  let I : Finset ℤ := Icc 0 ⌊Real.log (N : ℝ)⌋
  let f (n : ℕ) : ℝ := Real.log (n : ℝ)
  let b (n : ℕ) : ℤ := ⌊f n⌋
  let C := (Real.log 4+4)*Real.exp 1
  let a (n : ℕ) : ℂ := (((g n/(n : ℝ) : ℝ) : ℂ))
  have hC : 0 ≤ C := by
    dsimp [C]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hbin : ∀ n ∈ A, b n ∈ I := by
    intro n hn
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp (hA hn)
    exact mem_Icc.mpr ⟨Int.floor_nonneg.mpr (Real.log_nonneg (by exact_mod_cast hn1)),
      Int.floor_mono (Real.log_le_log (Nat.cast_pos.mpr hn1) (by exact_mod_cast hnN))⟩
  have hfreq : ∀ n ∈ A, (b n : ℝ) ≤ f n ∧ f n < (b n : ℝ)+1 :=
    fun n _ => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have hmass : ∀ i ∈ I, (∑ n ∈ A.filter (fun n => b n=i), ‖a n‖) ≤ D*C := by
    intro i hi
    have hC' := chebyshev_bin_mass A (fun _ => 1) i
      (fun n hn => (mem_Icc.mp (hA hn)).1) (fun n hn => by norm_num)
    calc
      _ ≤ ∑ n ∈ A.filter (fun n => b n=i), D*|mangoldtLogScoreCoeff (fun _ => 1) n| := by
        apply sum_le_sum
        intro n hn
        have hnA := (mem_filter.mp hn).1
        change ‖((g n / (n : ℝ) : ℝ) : ℂ)‖ ≤ _
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n), mangoldtLogScoreCoeff, one_mul,
          abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (hg n hnA) (Nat.cast_nonneg _)
      _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hC' hD
  have hcard : (I.card : ℝ) ≤ Real.log N+1 := by
    have hcardI : (I.card : ℤ) = ⌊Real.log (N : ℝ)⌋+1 := by
      have hNf : 0 ≤ ⌊Real.log (N : ℝ)⌋ := Int.floor_nonneg.mpr hlog
      simpa [I] using (Int.card_Icc_of_le (a := (0 : ℤ)) (b := ⌊Real.log (N : ℝ)⌋) (by omega))
    have hcardR : (I.card : ℝ) = (⌊Real.log (N : ℝ)⌋ : ℤ) + 1 := by exact_mod_cast hcardI
    rw [hcardR]
    linarith [Int.floor_le (Real.log (N : ℝ))]
  have hT : 0 < 2*Real.pi := by positivity
  simp_rw [LSeries_finite_score g A _ hs]
  let F (t : ℝ) : ℝ := ‖complexScore A a f t‖^2
  have hh := intervalIntegral.integral_comp_mul_left F (a := (k : ℝ)) (b := (k : ℝ)+1) hT.ne'
  change (∫ t in (k : ℝ)..((k : ℝ)+1), F (2*Real.pi*t)) ≤ _
  rw [hh, smul_eq_mul]
  rw [show 2*Real.pi*((k : ℝ)+1) = 2*Real.pi+2*Real.pi*(k : ℝ) by ring]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hT.le)
  refine (shifted_complex_band_energy A I a f b (D*C) (2*Real.pi)
    (2*Real.pi*(k : ℝ)) hT (mul_nonneg hD hC) hbin hfreq hmass).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply div_le_div_of_nonneg_right _ hT.le
  apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))
  exact tsum_nonneg (tentBinKernel_nonneg _)

end

/- Source section: 239-cell-product-bound.lean -/
section
open Filter MeasureTheory
open scoped Topology


theorem summable_cells_limit (J : ℕ → ℤ → ℝ) (B : ℤ → ℝ)
    (hB : Summable B) (hdom : ∀ᶠ N : ℕ in atTop, ∀ k : ℤ, ‖J N k‖ ≤ B k)
    (hlim : ∀ k : ℤ, Tendsto (fun N => J N k) atTop (𝓝 0)) :
    Tendsto (fun N => ∑' k : ℤ, J N k) atTop (𝓝 0) := by
  simpa using tendsto_tsum_of_dominated_convergence hB hlim hdom

theorem band_dominated_integral_limit (P Y : ℕ → ℝ → ℝ) (W : ℝ → ℝ)
    (B : ℤ → ℝ) (C G : ℝ)
    (hp : ∀ N t, 0 ≤ P N t) (hy : ∀ N t, 0 ≤ Y N t) (hw : ∀ t, 0 ≤ W t)
    (hB0 : ∀ k : ℤ, 0 ≤ B k) (hB : Summable B) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hW : ∀ (k : ℤ) (t : ℝ), t ∈ Set.Icc (k : ℝ) ((k : ℝ)+1) → W t ≤ B k)
    (hY : ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, Y N t ≤ G)
    (hYloc : ∀ (k : ℤ) (ε : ℝ), 0 < ε → ∀ᶠ N : ℕ in atTop,
       ∀ t : ℝ, t ∈ Set.Icc (k : ℝ) ((k : ℝ)+1) → Y N t ≤ ε)
    (hP : ∀ᶠ N : ℕ in atTop, ∀ k : ℤ, (∫ t in (k : ℝ)..((k : ℝ)+1), P N t) ≤ C)
    (hiP : ∀ N : ℕ, ∀ k : ℤ, IntervalIntegrable (P N) volume (k : ℝ) ((k : ℝ)+1))
    (hiF : ∀ N : ℕ, Integrable (fun t : ℝ => W t*Y N t*P N t)) :
    Tendsto (fun N : ℕ => ∫ t : ℝ, W t*Y N t*P N t) atTop (𝓝 0) := by
  let J (N : ℕ) (k : ℤ) := ∫ t in (k : ℝ)..((k : ℝ)+1), W t*Y N t*P N t
  have hJn (N : ℕ) (k : ℤ) : 0 ≤ J N k := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact mul_nonneg (mul_nonneg (hw t) (hy N t)) (hp N t)
  have hJbound (N : ℕ) (k : ℤ) (M : ℝ) (hM : 0 ≤ M)
      (hNM : ∀ t : ℝ, t ∈ Set.Icc (k : ℝ) ((k : ℝ)+1) → Y N t ≤ M)
      (hNP : (∫ t in (k : ℝ)..((k : ℝ)+1), P N t) ≤ C) :
      J N k ≤ B k*M*C := by
    calc
      _ ≤ ∫ t in (k : ℝ)..((k : ℝ)+1), (B k*M)*P N t := by
        refine intervalIntegral.integral_mono_on (by linarith)
          ((hiF N).intervalIntegrable ..) ((hiP N k).const_mul _) ?_
        intro t ht
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hW k t ht) (hNM t ht) (hy N t) (hB0 k)) (hp N t)
      _ = (B k*M)*(∫ t in (k : ℝ)..((k : ℝ)+1), P N t) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hNP (mul_nonneg (hB0 k) hM)
  have hd : ∀ᶠ N : ℕ in atTop, ∀ k : ℤ, ‖J N k‖ ≤ (G*C)*B k := by
    filter_upwards [hY,hP] with N hNY hNP k
    rw [Real.norm_eq_abs, abs_of_nonneg (hJn N k)]
    convert hJbound N k G hG (fun t _ => hNY t) (hNP k) using 1
    ring
  have hl (k : ℤ) : Tendsto (fun N => J N k) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨?_,?_⟩
    · intro b hb
      exact Eventually.of_forall fun N => hb.trans_le (hJn N k)
    · intro b hb
      have hD : 0 < B k*C+1 := by linarith [mul_nonneg (hB0 k) hC]
      let e := b/(B k*C+1)
      have he : 0 < e := div_pos hb hD
      filter_upwards [hYloc k e he,hP] with N hNY hNP
      have hlt : B k*e*C < b := by
        have hnum : (B k*C)*b < b*(B k*C+1) := by nlinarith only [hb]
        rw [show B k*e*C = ((B k*C)*b)/(B k*C+1) by dsimp [e]; ring]
        exact (div_lt_iff₀ hD).2 hnum
      exact (hJbound N k e he.le hNY (hNP k)).trans_lt hlt
  refine (summable_cells_limit J _ (hB.mul_left (G*C)) hd hl).congr fun N => ?_
  simpa only [J, zero_add] using ((hiF N).hasSum_intervalIntegral 0).tsum_eq


theorem interval_product_by_squares (P Q : ℝ → ℝ) (a b D : ℝ) (hab : a ≤ b) (hD : 0 < D)
    (hP : Continuous P) (hQ : Continuous Q) :
    (∫ t in a..b, P t*Q t) ≤
      ((D^2)*(∫ t in a..b, (P t)^2)+(∫ t in a..b, (Q t)^2))/(2*D) := by
  have hpot (t : ℝ) : (2*D)*(P t*Q t) ≤ (D^2)*(P t)^2+(Q t)^2 := by
    nlinarith only [sq_nonneg (D*P t-Q t)]
  have hC₁ : Continuous (fun t => (2*D)*(P t*Q t)) := continuous_const.mul (hP.mul hQ)
  have hC₂ : Continuous (fun t => (D^2)*(P t)^2+(Q t)^2) :=
    (continuous_const.mul (hP.pow 2)).add (hQ.pow 2)
  have hh : (∫ t in a..b, (2*D)*(P t*Q t)) ≤
      ∫ t in a..b, (D^2)*(P t)^2+(Q t)^2 :=
    intervalIntegral.integral_mono_on hab (hC₁.intervalIntegrable ..)
      (hC₂.intervalIntegrable ..) (fun t _ => hpot t)
  have hI₁ : IntervalIntegrable (fun t => (D^2)*(P t)^2) volume a b :=
    (continuous_const.mul (hP.pow 2)).intervalIntegrable _ _
  have hI₂ : IntervalIntegrable (fun t => (Q t)^2) volume a b :=
    (hQ.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hI₁ hI₂,
    intervalIntegral.integral_const_mul] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2*D)).2
  linarith

end

open Finset MeasureTheory
open scoped ArithmeticFunction

noncomputable def cellScoreConstant : ℝ :=
  let T := 2*Real.pi
  T⁻¹*4*((∑' z : ℤ, tentBinKernel (2*T) z)*((Real.log 4+4)*Real.exp 1)^2/T)

theorem cellScoreConstant_nonneg : 0 ≤ cellScoreConstant := by
  unfold cellScoreConstant
  have hs : 0 ≤ ∑' z : ℤ, tentBinKernel (2*(2*Real.pi)) z :=
    tsum_nonneg (tentBinKernel_nonneg _)
  have hp : 0 < Real.pi := Real.pi_pos
  positivity

theorem score_energy_simple (g : ArithmeticFunction ℝ) (A : Finset ℕ) (N : ℕ)
    (D : ℝ) (hN : 0 < N) (hD : 0 ≤ D)
    (hA : A ⊆ Icc 1 N) (hs : ∀ n ∉ A, g n=0)
    (hg : ∀ n ∈ A, |g n| ≤ D*Λ n) (k : ℤ) :
    (∫ t in (k : ℝ)..((k : ℝ)+1),
      ‖LSeries (arithOfReal g) (LPhasePoint (2*Real.pi*t))‖^2) ≤
        cellScoreConstant*(Real.log N+1)*D^2 := by
  refine (mangoldt_LSeries_unit_energy g A N D hN hD hA hs hg k).trans_eq ?_
  dsimp [cellScoreConstant]
  ring

theorem continuous_finite_LScore (g : ArithmeticFunction ℝ) (A : Finset ℕ)
    (hg : ∀ n ∉ A, g n=0) :
    Continuous (fun t : ℝ => LSeries (arithOfReal g) (LPhasePoint (2*Real.pi*t))) := by
  simp_rw [LSeries_finite_score g A _ hg]
  unfold complexScore
  fun_prop

theorem mangoldt_two_score_cell (a b : ArithmeticFunction ℝ) (A B : Finset ℕ)
    (N : ℕ) (K : ℝ) (hN : 0 < N) (hl : 1 ≤ Real.log (N : ℝ)) (hK : 0 ≤ K)
    (hA : A ⊆ Icc 1 N) (hB : B ⊆ Icc 1 N)
    (ha : ∀ n ∉ A, a n=0) (hb : ∀ n ∉ B, b n=0)
    (hca : ∀ n ∈ A, |a n| ≤ (K/Real.log N)*Λ n)
    (hcb : ∀ n ∈ B, |b n| ≤ Λ n) (k : ℤ) :
    (∫ t in (k : ℝ)..((k : ℝ)+1),
      ‖LSeries (arithOfReal a) (LPhasePoint (2*Real.pi*t))‖ *
      ‖LSeries (arithOfReal b) (LPhasePoint (2*Real.pi*t))‖) ≤
      cellScoreConstant*(K^2+1) := by
  let P (t : ℝ) := ‖LSeries (arithOfReal a) (LPhasePoint (2*Real.pi*t))‖
  let Q (t : ℝ) := ‖LSeries (arithOfReal b) (LPhasePoint (2*Real.pi*t))‖
  let L := Real.log (N : ℝ)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hl
  have hEp := score_energy_simple a A N (K/L) hN
    (div_nonneg hK hL.le) hA ha hca k
  have hEq := score_energy_simple b B N 1 hN zero_le_one hB hb
    (fun n hn => by simpa using hcb n hn) k
  refine (interval_product_by_squares P Q _ _ L (by linarith) hL
    ((continuous_finite_LScore a A ha).norm) ((continuous_finite_LScore b B hb).norm)).trans ?_
  apply (div_le_iff₀ (by positivity : 0 < 2*L)).2
  calc
    _ ≤ L^2*(cellScoreConstant*(L+1)*(K/L)^2)+cellScoreConstant*(L+1)*1^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hEp (sq_nonneg L)) hEq
    _ = (L+1)*(cellScoreConstant*(K^2+1)) := by field_simp
    _ ≤ _ := by
      rw [mul_comm (cellScoreConstant*(K^2+1)) (2*L)]
      have htwo : L+1 ≤ 2*L := by dsimp [L] at *; linarith
      exact mul_le_mul_of_nonneg_right htwo
        (mul_nonneg cellScoreConstant_nonneg (by positivity))

end

/- Source section: 239-smooth-product-bounds.lean -/
section


/- Source section: 239-euler-main-bound.lean -/
section
open Finset
open Filter
open Filter Finset
open scoped Topology
open scoped ArithmeticFunction



theorem inv_one_add_le_exp_neg_half (d : ℝ) (hd : 0 ≤ d) (hD : d ≤ 1) :
    (1+d)⁻¹ ≤ Real.exp (-d/2) := by
  have hpos : 0 < 1+d := by linarith
  have hdiv : d / 2 ≤ d / (1+d) :=
    div_le_div_of_nonneg_left hd hpos (by linarith)
  have he : d / (1+d) = 1-(1+d)⁻¹ := by
    field_simp
    ring
  have hlog : d/2 ≤ Real.log (1+d) :=
    hdiv.trans (he.le.trans (Real.one_sub_inv_le_log_of_pos hpos))
  calc
    _ = Real.exp (-Real.log (1+d)) := by rw [Real.exp_neg, Real.exp_log hpos]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem normalized_euler_factor (r : ℝ) (z : ℂ)
    (hr : 0 ≤ r) (hR : r ≤ (1/2 : ℝ)) (hz : ‖z‖ ≤ r) :
    (1-r) / ‖1-z‖ ≤ Real.exp (-(r-z.re)/2) := by
  let d := r-z.re
  have hd : 0 ≤ d := by
    dsimp [d]
    linarith [Complex.re_le_norm z]
  have hD : d ≤ 1 := by
    dsimp [d]
    linarith [(abs_le.mp (Complex.abs_re_le_norm z)).1]
  have hden : 1-r+d ≤ ‖1-z‖ := by
    have h := Complex.re_le_norm (1-z)
    simp only [Complex.sub_re, Complex.one_re] at h
    dsimp [d]
    linarith
  have hr' : 0 < 1-r := by linarith
  have hlower : (1-r)*(1+d) ≤ ‖1-z‖ := by
    have hm := mul_nonneg hr hd
    nlinarith
  have hlpos : 0 < (1-r)*(1+d) :=
    mul_pos hr' (by linarith)
  calc
    _ ≤ (1-r)/((1-r)*(1+d)) := div_le_div_of_nonneg_left hr'.le hlpos hlower
    _ = (1+d)⁻¹ := by
      have h1 : 1+d ≠ 0 := by linarith
      field_simp
    _ ≤ _ := inv_one_add_le_exp_neg_half d hd hD

theorem normalized_euler_product {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ j ∈ s, 0 ≤ r j) (hR : ∀ j ∈ s, r j ≤ (1/2 : ℝ))
    (hz : ∀ j ∈ s, ‖z j‖ ≤ r j) :
    (∏ j ∈ s, (1-r j)/‖1-z j‖) ≤
      Real.exp (-(∑ j ∈ s, (r j-(z j).re))/2) := by
  calc
    _ ≤ ∏ j ∈ s, Real.exp (-(r j-(z j).re)/2) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact div_nonneg (by linarith [hR j hj]) (norm_nonneg _)
      · intro j hj
        exact normalized_euler_factor (r j) (z j) (hr j hj) (hR j hj) (hz j hj)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [div_eq_mul_inv]
      simp only [div_eq_mul_inv, ← sum_mul, sum_neg_distrib]


noncomputable def primeTwist (f : ℕ → ℝ) (t : ℝ) (p : ℕ) : ℂ :=
  (((f p / (p : ℝ) : ℝ) : ℂ) * Complex.exp (((t*Real.log p : ℝ) : ℂ) * Complex.I))

theorem primeTwist_re (f : ℕ → ℝ) (t : ℝ) (p : ℕ) :
    (primeTwist f t p).re = f p * Real.cos (t*Real.log p) / (p : ℝ) := by
  rw [primeTwist, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  ring

theorem norm_primeTwist (f : ℕ → ℝ) (t : ℝ) (p : ℕ) :
    ‖primeTwist f t p‖ = |f p| / (p : ℝ) := by
  rw [primeTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]

theorem normalized_prime_product_bound (s : Finset ℕ) (f : ℕ → ℝ) (t : ℝ)
    (hp : ∀ p ∈ s, p.Prime) (hf : ∀ p ∈ s, |f p| ≤ 1) :
    (∏ p ∈ s, (1-(p : ℝ)⁻¹)/‖1-primeTwist f t p‖) ≤
      Real.exp (-(∑ p ∈ s, (1-f p*Real.cos (t*Real.log p))/(p : ℝ))/2) := by
  have h := normalized_euler_product s (fun p => (p : ℝ)⁻¹) (primeTwist f t)
    (fun p _ => by positivity)
    (fun p hP => by
      have hR : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hP).two_le
      rw [one_div]
      exact (inv_le_inv₀ (show (0 : ℝ) < p by linarith) (by norm_num)).2 hR)
    (fun p hP => by
      rw [norm_primeTwist, ← one_div]
      exact div_le_div_of_nonneg_right (hf p hP) (Nat.cast_nonneg p))
  refine h.trans_eq ?_
  congr 3
  apply sum_congr rfl
  intro p hP
  rw [primeTwist_re, ← one_div, ← sub_div]


theorem uniform_normalized_euler_decay (f : ℕ → ℝ) (T : Set ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (hD : ∀ B : ℝ, ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ t ∈ T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ t ∈ T,
      (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)/‖1-primeTwist f t p‖) < ε := by
  intro ε hε
  obtain ⟨S,hSp,hS⟩ := hD (-2*Real.log ε)
  filter_upwards [eventually_ge_atTop (S.sup id)] with N hN t ht
  have hs : S ⊆ N.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(le_sup (f := id) hp).trans hN, hSp p hp⟩
  have hprime : ∀ p ∈ N.primesLE, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hmono :
      (∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ)) ≤
      ∑ p ∈ N.primesLE, (1-f p*Real.cos (t*Real.log p))/(p : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg hs
    intro p hp hn
    apply div_nonneg _ (by positivity)
    apply sub_nonneg.mpr
    calc
      f p * Real.cos (t*Real.log p) ≤ |f p * Real.cos (t*Real.log p)| := le_abs_self _
      _ = |f p| * |Real.cos (t*Real.log p)| := abs_mul _ _
      _ ≤ 1 := mul_le_one₀ (hf _ (hprime _ hp)) (abs_nonneg _) (Real.abs_cos_le_one _)
  have hdist := (hS t ht).trans_le hmono
  refine (normalized_prime_product_bound _ f t hprime (fun p hp => hf p (hprime p hp))).trans_lt ?_
  rw [← Real.exp_log hε]
  exact Real.exp_lt_exp.mpr (by linarith)



theorem weightedDilatedMean (F g : ℕ → ℝ) (L : ℝ)
    (hF0 : F 0 = 0) (hg0 : g 0 = 0)
    (hF : ∀ N, |F N| ≤ N)
    (hL : Tendsto (fun N : ℕ => F N / (N : ℝ)) atTop (𝓝 L))
    (hs : Summable (fun d : ℕ => |g d| / (d : ℝ))) :
    Tendsto (fun N : ℕ => (∑ d ∈ range (N+1), g d * F (N/d)) / (N : ℝ))
      atTop (𝓝 (∑' d : ℕ, g d * (L / (d : ℝ)))) := by
  let w (N d : ℕ) : ℝ := g d * F (N/d) / (N : ℝ)
  have hp (d : ℕ) : Tendsto (fun N => w N d) atTop (𝓝 (g d * (L/(d : ℝ)))) := by
    by_cases hd : d = 0
    · subst d
      simp [w, hg0]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have ht : Tendsto (fun N : ℕ => N/d) atTop atTop := by
      refine tendsto_atTop.2 fun k => ?_
      filter_upwards [eventually_ge_atTop (k*d)] with N hN
      exact (Nat.le_div_iff_mul_le hdpos).2 hN
    have hq : Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ)/(N : ℝ)) atTop (𝓝 (d : ℝ)⁻¹) := by
      have h := (tendsto_nat_floor_mul_div_atTop
        (show 0 ≤ (d : ℝ)⁻¹ by positivity)).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, mul_comm (d : ℝ)⁻¹, ← div_eq_mul_inv,
        Nat.floor_div_eq_div] using h
    have hmul := ((hL.comp ht).mul hq).const_mul (g d)
    rw [← div_eq_mul_inv] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop d] with N hN
    have hdiv : (0 : ℝ) < ((N/d : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.div_pos hN hdpos)
    change g d * (F (N/d) / ((N/d : ℕ) : ℝ) * (((N/d : ℕ) : ℝ)/(N : ℝ))) = _
    simp only [w]
    field_simp
  have hb : ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, ‖w N d‖ ≤ |g d| / (d : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN d
    rw [show ‖w N d‖ = |g d| * |F (N/d)| / (N : ℝ) by
      simp [w, Real.norm_eq_abs]]
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    calc
      |g d| * |F (N/d)| / (N : ℝ) ≤ |g d| * ((N/d : ℕ) : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)) hN'.le
      _ ≤ |g d| * ((N : ℝ)/(d : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le (abs_nonneg _)) hN'.le
      _ = |g d| / (d : ℝ) := by rw [mul_div_assoc, div_div, mul_comm (d : ℝ), ← div_div,
        div_self hN'.ne', ← mul_div_assoc, mul_one]
  have h := tendsto_tsum_of_dominated_convergence hs hp hb
  refine h.congr' (Eventually.of_forall fun N => ?_)
  rw [tsum_eq_sum (s := range (N+1))]
  · simp only [w, div_eq_mul_inv, Finset.sum_mul]
  · intro d hd
    have hlt : N < d := by simpa using hd
    simp [w, Nat.div_eq_of_lt hlt, hF0]


theorem convolution_sum (g c : ArithmeticFunction ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (g*c) n) =
      ∑ d ∈ range (N+1), g d * ∑ j ∈ Icc 1 (N/d), c j := by
  classical
  have hrewrite (n : ℕ) (hn : n ∈ Icc 1 N) :
      (g*c) n = ∑ d ∈ range (N+1), if d ∣ n then g d * c (n/d) else 0 := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => g a * c b),
      ← sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_range]
    obtain ⟨hp, hle⟩ := mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    exact ⟨fun h => ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) h.1).trans hle), h.1⟩,
      fun h => ⟨h.2, hn0⟩⟩
  rw [sum_congr rfl hrewrite, sum_comm]
  apply sum_congr rfl
  intro d _
  by_cases hd : d = 0
  · subst d
    simp
  have hdp : 0 < d := Nat.pos_of_ne_zero hd
  rw [← sum_filter, mul_sum]
  symm
  apply sum_bij (fun j _ => d*j)
  · intro j hj
    obtain ⟨h1,h2⟩ := mem_Icc.mp hj
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩, dvd_mul_right d j⟩
    · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hd (by omega))
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hdp).1 h2
  · intro a ha b hb h
    exact Nat.eq_of_mul_eq_mul_left hdp h
  · intro n hn
    obtain ⟨hn, hdiv⟩ := mem_filter.mp hn
    obtain ⟨h1,h2⟩ := mem_Icc.mp hn
    have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdiv
    refine ⟨n/d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right h2⟩, hmul⟩
    apply Nat.one_le_iff_ne_zero.2
    intro hz
    rw [hz, mul_zero] at hmul
    omega
  · intro j hj
    rw [Nat.mul_div_cancel_left j hdp]

theorem convolution_preserves_mean (g c : ArithmeticFunction ℝ) (L : ℝ)
    (hc : ∀ n : ℕ, |c n| ≤ 1)
    (hL : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, c n) / (N : ℝ)) atTop (𝓝 L))
    (hs : Summable (fun d : ℕ => |g d| / (d : ℝ))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (g*c) n) / (N : ℝ)) atTop
      (𝓝 (∑' d : ℕ, g d * (L / (d : ℝ)))) := by
  let F (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, c n
  have hF0 : F 0 = 0 := by simp [F]
  have hF (N : ℕ) : |F N| ≤ N := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |c n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Icc 1 N, (1 : ℝ) := sum_le_sum fun n _ => hc n
      _ = N := by simp
  refine (weightedDilatedMean F g L hF0 g.map_zero hF hL hs).congr ?_
  intro N
  rw [convolution_sum]



theorem half_div_le_floor (N d : ℕ) (hd : 0 < d) (hle : d ≤ N) :
    (N : ℝ)/(2*(d : ℝ)) ≤ ((N/d : ℕ) : ℝ) := by
  have hq : 1 ≤ N/d := Nat.div_pos hle hd
  have h1 := Nat.div_add_mod N d
  have h2 := Nat.mod_lt N hd
  have h3 : d ≤ d * (N/d) := by
    simpa using Nat.mul_le_mul_left d hq
  have h4 : N ≤ 2 * (d * (N/d)) := by omega
  apply (div_le_iff₀ (by positivity)).2
  have h4R : (N : ℝ) ≤ 2 * ((d : ℝ) * ((N/d : ℕ) : ℝ)) := by exact_mod_cast h4
  nlinarith only [h4R]

theorem sum_mangoldt_log (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log n) =
      ∑ d ∈ range (N+1), Λ d * ((N/d : ℕ) : ℝ) := by
  have h := convolution_sum Λ (ArithmeticFunction.zeta : ArithmeticFunction ℝ) N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
  simp only [ArithmeticFunction.log_apply] at h
  rw [h]
  apply sum_congr rfl
  intro d hd
  congr 1
  calc
    _ = ∑ _ ∈ Icc 1 (N/d), (1 : ℝ) := by
      apply sum_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
      simp [ArithmeticFunction.zeta_apply_ne hj0]
    _ = _ := by simp [nsmul_eq_mul]

theorem sum_primeLog_div_le_twice (N : ℕ) (hN : 0 < N) :
    (∑ p ∈ N.primesLE, Real.log p/(p : ℝ)) ≤ 2*Real.log N := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsub : N.primesLE ⊆ range (N+1) := by
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1)
  have hterm : ∀ p ∈ N.primesLE, (N : ℝ)/2 * (Real.log p/(p : ℝ)) ≤
      Λ p * ((N/p : ℕ) : ℝ) := by
    intro p hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesLE.mp hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpr]
    have hpR1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_le
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
    calc
      _ = Real.log p * ((N : ℝ)/(2*(p : ℝ))) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (half_div_le_floor N p hpr.pos hpN)
        (Real.log_nonneg hpR1)
  have hmain : (N : ℝ)/2 * (∑ p ∈ N.primesLE, Real.log p/(p : ℝ)) ≤
      (N : ℝ) * Real.log N := by
    rw [mul_sum]
    calc
      _ ≤ ∑ p ∈ N.primesLE, Λ p * ((N/p : ℕ) : ℝ) := sum_le_sum hterm
      _ ≤ ∑ d ∈ range (N+1), Λ d * ((N/d : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
      _ = ∑ n ∈ Icc 1 N, Real.log n := (sum_mangoldt_log N).symm
      _ ≤ ∑ _ ∈ Icc 1 N, Real.log N := by
        apply sum_le_sum
        intro n hp
        obtain ⟨hn1,hnN⟩ := mem_Icc.mp hp
        exact Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hnN)
      _ = _ := by simp [nsmul_eq_mul]
  nlinarith



theorem euler_shift_factor (r u : ℝ) (hr : 0 ≤ r) (hR : r ≤ 1/2) (hu : 0 ≤ u) :
    (1-r*Real.exp (-u))/(1-r) ≤ Real.exp (2*r*u) := by
  have h1 : 0 < 1-r := by linarith
  have hu' : 1-Real.exp (-u) ≤ u := by linarith [Real.add_one_le_exp (-u)]
  have hm : r*(1-Real.exp (-u)) ≤ r*u :=
    mul_le_mul_of_nonneg_left hu' hr
  have hsmall : r*u/(1-r) ≤ 2*r*u := by
    apply (div_le_iff₀ h1).2
    have hmul := mul_nonneg (mul_nonneg hr hu) (show 0 ≤ 1-2*r by linarith)
    nlinarith only [hmul]
  calc
    _ = 1 + r*(1-Real.exp (-u))/(1-r) := by field_simp; ring
    _ ≤ 1 + r*u/(1-r) := add_le_add_right (div_le_div_of_nonneg_right hm h1.le) 1
    _ ≤ 1+2*r*u := by linarith
    _ ≤ _ := by linarith [Real.add_one_le_exp (2*r*u)]

theorem prime_euler_shift (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))/(1-(p : ℝ)⁻¹)) ≤
      Real.exp (2*δ*(∑ p ∈ N.primesLE, Real.log p/(p : ℝ))) := by
  have hinv (p : ℕ) (hp : p ∈ N.primesLE) : (p : ℝ)⁻¹ ≤ 1/2 := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.two_le_of_mem_primesLE hp)
    rw [one_div]
    exact (inv_le_inv₀ (show (0 : ℝ) < p by linarith) (by norm_num)).2 hpR
  have hlog (p : ℕ) (hp : p ∈ N.primesLE) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  calc
    _ ≤ ∏ p ∈ N.primesLE, Real.exp (2*(p : ℝ)⁻¹*(δ*Real.log p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have he : Real.exp (-(δ*Real.log p)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hδ (hlog p hp)))
        have hi : 0 ≤ (p : ℝ)⁻¹ := by positivity
        apply div_nonneg
        · have hh := mul_le_mul_of_nonneg_left he hi
          linarith [hinv p hp]
        · linarith [hinv p hp]
      · intro p hp
        exact euler_shift_factor _ _ (by positivity) (hinv p hp) (mul_nonneg hδ (hlog p hp))
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [div_eq_mul_inv]
      ring



noncomputable def zetaShift (δ : ℝ) : ℂ := ((1+δ : ℝ) : ℂ)

theorem shifted_real_prime (p : ℕ) (hp : p.Prime) (δ : ℝ) :
    (p : ℂ)^(-zetaShift δ) =
      (((p : ℝ)⁻¹ * Real.exp (-(δ*Real.log p)) : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  rw [zetaShift, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow hpos.le]
  congr 1
  rw [Real.rpow_def_of_pos hpos]
  rw [show Real.log (p : ℝ) * -(1+δ) = -Real.log p + -(δ*Real.log p) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hpos]

theorem shifted_real_factor_ge_one (p : ℕ) (hp : p.Prime) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 ≤ (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hi : (p : ℝ)⁻¹ ≤ 1/2 := by
    rw [one_div]
    exact (inv_le_inv₀ (show (0 : ℝ) < p by linarith) (by norm_num)).2 hp2
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have he : Real.exp (-(δ*Real.log p)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hδ hlog))
  have hx := mul_le_mul_of_nonneg_left he (show 0 ≤ (p : ℝ)⁻¹ by positivity)
  have hh : 0 ≤ (p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)) := by positivity
  exact (one_le_inv₀ (by linarith)).2 (by linarith)

theorem shifted_real_factor_norm (p : ℕ) (hp : p.Prime) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖(1-(p : ℂ)^(-zetaShift δ))⁻¹‖ =
      (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))⁻¹ := by
  rw [shifted_real_prime p hp δ, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans (shifted_real_factor_ge_one p hp hδ))

theorem shifted_product_le_zeta (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))⁻¹) ≤
      ‖riemannZeta (zetaShift δ)‖ := by
  have hz : 1 < (zetaShift δ).re := by simp [zetaShift, hδ]
  have ht := (riemannZeta_eulerProduct hz).norm
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop (N+1)] with M hM
  rw [norm_prod]
  have hS : N.primesLE ⊆ M.primesBelow := by
    intro p hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨(Nat.lt_succ_of_le hpN).trans_le hM, hpr⟩
  calc
    _ = ∏ p ∈ N.primesLE, ‖(1-(p : ℂ)^(-zetaShift δ))⁻¹‖ := by
      exact prod_congr rfl fun p hp =>
        (shifted_real_factor_norm p (Nat.mem_primesLE.mp hp).2 hδ.le).symm
    _ ≤ _ := by
      refine prod_le_prod_of_subset_of_one_le hS (fun _ _ => norm_nonneg _) ?_
      intro p hp hn
      have hprime := (Nat.mem_primesBelow.mp hp).2
      rw [shifted_real_factor_norm p hprime hδ.le]
      exact shifted_real_factor_ge_one p hprime hδ.le


theorem zeta_inv_log_le_eventually :
    ∀ᶠ N : ℕ in atTop, ‖riemannZeta (zetaShift (Real.log N)⁻¹)‖ ≤ 2*Real.log N := by
  have hδ : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hz : Tendsto (fun N : ℕ => zetaShift (Real.log N)⁻¹) atTop (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have ht : Continuous (fun x : ℝ => 1 + x) := continuous_const.add continuous_id
      have hreal : Tendsto (fun N : ℕ => (1 : ℝ) + (Real.log N)⁻¹) atTop (𝓝 1) := by
        simpa [Function.comp_def] using ht.continuousAt.tendsto.comp hδ
      simpa [zetaShift, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    · filter_upwards [hpos] with N hN
      have hδpos : 0 < (Real.log (N : ℝ))⁻¹ := inv_pos.mpr hN
      intro h
      change zetaShift (Real.log N)⁻¹ = (1 : ℂ) at h
      have hr := congrArg Complex.re h
      simp only [zetaShift, Complex.ofReal_re, Complex.one_re] at hr
      linarith
  have hzeta := (riemannZeta_residue_one.comp hz).norm
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(zetaShift (Real.log N)⁻¹-1)*riemannZeta (zetaShift (Real.log N)⁻¹)‖ < 2 := by
    apply (tendsto_order.1 (show Tendsto _ atTop (𝓝 (1 : ℝ)) by simpa [Function.comp_def] using hzeta)).2
    norm_num
  filter_upwards [hpos,hbound] with N hN hB
  have he : zetaShift (Real.log N)⁻¹ - 1 = (((Real.log (N : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [zetaShift, Complex.ofReal_add, Complex.ofReal_one]
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hN)] at hB
  have hb : ‖riemannZeta (zetaShift (Real.log N)⁻¹)‖ / Real.log N < 2 := by
    rwa [div_eq_inv_mul]
  exact ((div_lt_iff₀ hN).1 hb).le


theorem base_euler_log_bound :
    ∀ᶠ N : ℕ in atTop,
      (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)⁻¹) ≤ (2*Real.exp 4)*Real.log N := by
  filter_upwards [zeta_inv_log_le_eventually, eventually_ge_atTop 2] with N hz hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let δ := (Real.log (N : ℝ))⁻¹
  have hδ : 0 < δ := inv_pos.mpr hl
  have hnum : 2*δ*(∑ p ∈ N.primesLE, Real.log p/(p : ℝ)) ≤ 4 := by
    calc
      _ ≤ (2*δ)*(2*Real.log N) :=
        mul_le_mul_of_nonneg_left (sum_primeLog_div_le_twice N (by omega)) (by positivity)
      _ = _ := by dsimp [δ]; field_simp; norm_num
  have hshift := (prime_euler_shift N δ hδ.le).trans (Real.exp_le_exp.mpr hnum)
  have hinv (p : ℕ) (hp : p ∈ N.primesLE) :
      (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p))) ≠ 0 := by
    have h := shifted_real_factor_ge_one p (Nat.prime_of_mem_primesLE hp) hδ.le
    intro hz0
    norm_num [hz0] at h
  have hprod :
      (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)⁻¹) =
        (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))/(1-(p : ℝ)⁻¹)) *
        (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))⁻¹) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    rw [div_eq_mul_inv, mul_comm (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p))), mul_assoc,
      mul_inv_cancel₀ (hinv p hp), mul_one]
  rw [hprod]
  have hnonneg : 0 ≤ ∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹*Real.exp (-(δ*Real.log p)))⁻¹ :=
    prod_nonneg fun p hp => (zero_le_one : (0 : ℝ) ≤ 1).trans
      (shifted_real_factor_ge_one p (Nat.prime_of_mem_primesLE hp) hδ.le)
  calc
    _ ≤ Real.exp 4 * ‖riemannZeta (zetaShift δ)‖ :=
      mul_le_mul hshift (shifted_product_le_zeta N hδ) hnonneg (Real.exp_nonneg _)
    _ ≤ Real.exp 4 * (2*Real.log N) := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = _ := by ring

theorem uniform_twisted_euler_sublog (f : ℕ → ℝ) (T : Set ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (hD : ∀ B : ℝ, ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ t ∈ T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ t ∈ T,
      (∏ p ∈ N.primesLE, ‖1-primeTwist f t p‖⁻¹) < ε*Real.log N := by
  intro ε hε
  let C := 2*Real.exp 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall := uniform_normalized_euler_decay f T hf hD (ε/C) (div_pos hε hC)
  filter_upwards [hsmall,base_euler_log_bound,eventually_ge_atTop 2] with N hN hB h2 t ht
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbase (p : ℕ) (hp : p ∈ N.primesLE) : (1-(p : ℝ)⁻¹) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.two_le_of_mem_primesLE hp)
    have hi : (p : ℝ)⁻¹ ≤ 1/2 := by
      rw [one_div]
      exact (inv_le_inv₀ (show (0 : ℝ) < p by linarith) (by norm_num)).2 hp2
    linarith
  have hp :
      (∏ p ∈ N.primesLE, ‖1-primeTwist f t p‖⁻¹) =
        (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)/‖1-primeTwist f t p‖) *
        (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)⁻¹) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    rw [div_eq_mul_inv, mul_comm (1-(p : ℝ)⁻¹), mul_assoc,
      mul_inv_cancel₀ (hbase p hp), mul_one]
  have hnonneg : 0 ≤ ∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)/‖1-primeTwist f t p‖ := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.two_le_of_mem_primesLE hp)
    have hi : (p : ℝ)⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (show (0 : ℝ) < p by linarith)).2 (by linarith)
    exact div_nonneg (by linarith) (norm_nonneg _)
  calc
    _ = _ := hp
    _ ≤ (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)/‖1-primeTwist f t p‖) * (C*Real.log N) :=
      mul_le_mul_of_nonneg_left hB hnonneg
    _ < (ε/C)*(C*Real.log N) := mul_lt_mul_of_pos_right (hN t ht) (mul_pos hC hlog)
    _ = _ := by field_simp

end

/- Source section: 239-smooth-lseries.lean -/
section
open Finset



end
open Finset Filter
open scoped Topology
theorem smoothLSeries_global_le (f : ArithmeticFunction ℝ) (N : ℕ) (t : ℝ)
    (h1 : f 1 = 1) (hm : ∀ m n : ℕ, f (m*n) = f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1) :
    ‖LSeries (arithOfReal (smoothPart f N)) (LPhasePoint t)‖ ≤
      ∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)⁻¹ := by
  rw [smoothPart_LSeries_product f N t h1 hm hf, norm_prod]
  apply Finset.prod_le_prod
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.two_le_of_mem_primesLE hp)
    have hp0 : (0 : ℝ) < p := by linarith
    have hpinv : (p : ℝ)⁻¹ ≤ 1/2 := by
      rw [one_div]
      exact (inv_le_inv₀ hp0 (by norm_num)).2 hpR
    have hnorm : ‖twistedWeight f t p‖ ≤ (p : ℝ)⁻¹ := by
      rw [norm_twistedWeight, ← one_div]
      exact div_le_div_of_nonneg_right (hf p) hp0.le
    have hden : 1-(p : ℝ)⁻¹ ≤ ‖1-twistedWeight f t p‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (twistedWeight f t p)
      rw [norm_one] at h
      linarith
    have hn : 0 < 1-(p : ℝ)⁻¹ := by linarith
    rw [norm_inv]
    exact (inv_le_inv₀ (hn.trans_le hden) hn).2 hden

theorem smoothLSeries_normalized_global (f : ArithmeticFunction ℝ)
    (h1 : f 1 = 1) (hm : ∀ m n : ℕ, f (m*n) = f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      ‖LSeries (arithOfReal (smoothPart f N)) (LPhasePoint t)‖ / Real.log N ≤ 2*Real.exp 4 := by
  filter_upwards [base_euler_log_bound,eventually_ge_atTop 2] with N hB hN t
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact (div_le_iff₀ hlog).2 ((smoothLSeries_global_le f N t h1 hm hf).trans hB)

theorem smoothLSeries_normalized_local (f : ArithmeticFunction ℝ) (T : Set ℝ)
    (h1 : f 1 = 1) (hm : ∀ m n : ℕ, f (m*n) = f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1)
    (hd : ∀ B : ℝ, ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ t ∈ T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ t ∈ T,
      ‖LSeries (arithOfReal (smoothPart f N)) (LPhasePoint t)‖ / Real.log N < ε := by
  intro ε hε
  have h := uniform_twisted_euler_sublog f T (fun p _ => hf p) hd ε hε
  filter_upwards [h,eventually_ge_atTop 2] with N hB hN t ht
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [smoothPart_LSeries_product f N t h1 hm hf, norm_prod]
  simp only [norm_inv]
  exact (div_lt_iff₀ hlog).2 (hB t ht)

end

/- Source section: 239-complex-integral-limit.lean -/
section

open Filter MeasureTheory
open scoped Topology

theorem complex_integral_limit_of_real_majorant (g : ℕ → ℝ → ℂ) (w : ℕ → ℝ → ℝ)
    (hw : ∀ N, Integrable (w N)) (hg : ∀ N, AEStronglyMeasurable (g N) volume)
    (hb : ∀ N t, ‖g N t‖ ≤ w N t)
    (hl : Tendsto (fun N : ℕ => ∫ t : ℝ, w N t) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ t : ℝ, g N t) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hl
  have hi : Integrable (g N) := (hw N).mono' (hg N) (Filter.Eventually.of_forall (hb N))
  exact (norm_integral_le_integral_norm _).trans (integral_mono hi.norm (hw N) (hb N))

end

/- Source section: 239-schwartz-cells.lean -/
section

open MeasureTheory

theorem schwartz_cell_envelope (f : SchwartzMap ℝ ℂ) :
    ∃ B : ℤ → ℝ, (∀ k, 0 ≤ B k) ∧ Summable B ∧
      ∀ (k : ℤ) (t : ℝ), t ∈ Set.Icc (k : ℝ) ((k : ℝ)+1) → ‖f t‖ ≤ B k := by
  let D := SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ 2 0 f
  have hD : 0 ≤ D := add_nonneg (apply_nonneg ..) (apply_nonneg ..)
  let B (k : ℤ) := (3*D/16)*tentBinKernel 0 k
  refine ⟨B, fun k => mul_nonneg (by positivity) (tentBinKernel_nonneg _ _),
    (tentBinKernel_summable 0).mul_left _, ?_⟩
  intro k t ht
  have h0 := SchwartzMap.norm_le_seminorm ℝ f t
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 t
  rw [Real.norm_eq_abs, sq_abs] at h2
  have hfreq : 1+(k : ℝ)^2 ≤ 3*(1+t^2) := by
    have hd : 0 ≤ t-(k : ℝ) := sub_nonneg.mpr ht.1
    have hb : t-(k : ℝ) ≤ 1 := by linarith [ht.2]
    have hs : (t-(k : ℝ))^2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (t+(t-(k : ℝ)))]
  change ‖f t‖ ≤ (3*D/16)*tentBinKernel 0 k
  have he : (3*D/16)*tentBinKernel 0 k = (3*D)/(1+(k : ℝ)^2) := by
    unfold tentBinKernel
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0), zero_add]
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).2
  have hu : ‖f t‖*(1+t^2) ≤ D := by dsimp [D]; nlinarith only [h0,h2]
  calc
    _ ≤ ‖f t‖*(3*(1+t^2)) := mul_le_mul_of_nonneg_left hfreq (norm_nonneg _)
    _ = 3*(‖f t‖*(1+t^2)) := by ring
    _ ≤ 3*D := mul_le_mul_of_nonneg_left hu (by norm_num)

end

open Finset Filter MeasureTheory
open scoped ArithmeticFunction FourierTransform Topology

theorem finite_LScore_norm_le (g : ArithmeticFunction ℝ) (A : Finset ℕ)
    (hs : ∀ n ∉ A, g n=0) (t : ℝ) :
    ‖LSeries (arithOfReal g) (LPhasePoint t)‖ ≤ ∑ n ∈ A, |g n|/(n : ℝ) := by
  rw [LSeries_finite_score g A t hs]
  unfold complexScore
  refine (norm_sum_le _ _).trans_eq ?_
  apply sum_congr rfl
  intro n hn
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_div]
  rw [abs_of_nonneg (show (0:ℝ) ≤ n by positivity)]

theorem smoothPart_LSeries_continuous (f : ArithmeticFunction ℝ) (N : ℕ)
    (h1 : f 1=1) (hm : ∀ m n : ℕ, f (m*n)=f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1) :
    Continuous (fun t : ℝ => LSeries (arithOfReal (smoothPart f N)) (LPhasePoint (2*Real.pi*t))) := by
  simp_rw [smoothPart_LSeries_product f N _ h1 hm hf]
  apply continuous_finset_prod
  intro p hp
  apply Continuous.inv₀
  · unfold twistedWeight
    fun_prop
  · intro t
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp)
    have hn : ‖twistedWeight f (2*Real.pi*t) p‖ < 1 := by
      rw [norm_twistedWeight]
      exact (div_lt_iff₀ (by linarith : (0:ℝ) < p)).2 (by simpa using (hf p).trans_lt hpR)
    intro hz
    have he : twistedWeight f (2*Real.pi*t) p = 1 := (sub_eq_zero.mp hz).symm
    simpa [he] using hn

theorem smoothed_product_halasz_limit (f : ArithmeticFunction ℝ)
    (h1 : f 1=1) (hm : ∀ m n : ℕ, f (m*n)=f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1)
    (Hdist : ∀ (T B : ℝ), ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
        ∀ t ∈ Set.Icc (-T) T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ))
    (a b : ℕ → ArithmeticFunction ℝ) (A B : ℕ → Finset ℕ)
    (hA : ∀ N, A N ⊆ Icc 1 N) (hB : ∀ N, B N ⊆ Icc 1 N)
    (ha : ∀ N n, n ∉ A N → a N n=0) (hb : ∀ N n, n ∉ B N → b N n=0)
    (K : ℝ) (hK : 0 ≤ K)
    (hca : ∀ᶠ N : ℕ in atTop, ∀ n ∈ A N, |a N n| ≤ (K/Real.log N)*Λ n)
    (hcb : ∀ N n, n∈B N → |b N n| ≤ Λ n)
    (h : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => ∫ t : ℝ,
      LSeries (arithOfReal (a N)) (LPhasePoint (2*Real.pi*t)) *
      LSeries (arithOfReal (b N)) (LPhasePoint (2*Real.pi*t)) *
      (LSeries (arithOfReal (smoothPart f N)) (LPhasePoint (2*Real.pi*t)) / (Real.log N : ℂ)) *
      Complex.exp (((-2*Real.pi*t*Real.log N : ℝ) : ℂ)*Complex.I) *
      (𝓕 (h : ℝ → ℂ)) t) atTop (𝓝 0) := by
  let U (N : ℕ) (t : ℝ) := LSeries (arithOfReal (a N)) (LPhasePoint (2*Real.pi*t))
  let V (N : ℕ) (t : ℝ) := LSeries (arithOfReal (b N)) (LPhasePoint (2*Real.pi*t))
  let F (N : ℕ) (t : ℝ) := LSeries (arithOfReal (smoothPart f N)) (LPhasePoint (2*Real.pi*t))
  let P (N : ℕ) (t : ℝ) := ‖U N t‖*‖V N t‖
  let Y (N : ℕ) (t : ℝ) := ‖F N t‖ / Real.log N
  let W (t : ℝ) := ‖(𝓕 (h : ℝ → ℂ)) t‖
  have hlog0 (N : ℕ) : 0 ≤ Real.log (N : ℝ) := by
    rcases eq_or_ne N 0 with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hp (N : ℕ) (t : ℝ) : 0 ≤ P N t := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hy (N : ℕ) (t : ℝ) : 0 ≤ Y N t := div_nonneg (norm_nonneg _) (hlog0 N)
  have hw (t : ℝ) : 0 ≤ W t := norm_nonneg _
  have hcontU (N : ℕ) : Continuous (U N) := continuous_finite_LScore _ _ (ha N)
  have hcontV (N : ℕ) : Continuous (V N) := continuous_finite_LScore _ _ (hb N)
  have hcontF (N : ℕ) : Continuous (F N) := smoothPart_LSeries_continuous f N h1 hm hf
  have hcontP (N : ℕ) : Continuous (P N) := (hcontU N).norm.mul (hcontV N).norm
  have hcontY (N : ℕ) : Continuous (Y N) := (hcontF N).norm.div_const _
  obtain ⟨Env,hEnv0,hEnv,hWe⟩ := schwartz_cell_envelope (𝓕 h)
  let C := cellScoreConstant*(K^2+1)
  let G := 2*Real.exp 4
  have hCe : 0 ≤ C := mul_nonneg cellScoreConstant_nonneg (by positivity)
  have hGe : 0 ≤ G := by dsimp [G]; positivity
  have hY : ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, Y N t ≤ G :=
    (smoothLSeries_normalized_global f h1 hm hf).mono (fun N h t => h _)
  have hYloc (k : ℤ) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
        t ∈ Set.Icc (k : ℝ) ((k : ℝ)+1) → Y N t ≤ ε := by
    let T := 2*Real.pi*(|(k : ℝ)|+1)
    have hD := smoothLSeries_normalized_local f (Set.Icc (-T) T) h1 hm hf (Hdist T) ε hε
    filter_upwards [hD] with N hN t ht
    apply (hN (2*Real.pi*t) ?_).le
    have ht' : |t| ≤ |(k : ℝ)|+1 := by
      apply abs_le.mpr
      constructor <;> linarith [ht.1,ht.2,le_abs_self (k : ℝ),neg_le_abs (k : ℝ)]
    have hh := (abs_le.mp ht')
    have hπ : 0 ≤ 2*Real.pi := by positivity
    exact ⟨by dsimp [T]; nlinarith [mul_le_mul_of_nonneg_left hh.1 hπ],
      mul_le_mul_of_nonneg_left hh.2 hπ⟩
  have hP : ∀ᶠ N : ℕ in atTop, ∀ k : ℤ,
      (∫ t in (k : ℝ)..((k : ℝ)+1), P N t) ≤ C := by
    have hLg : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    filter_upwards [hca,hLg,eventually_ge_atTop 2] with N hα hL hN k
    exact mangoldt_two_score_cell _ _ _ _ N K (by omega) hL hK (hA N) (hB N)
      (ha N) (hb N) hα (hcb N) k
  have hiF (N : ℕ) : Integrable (fun t : ℝ => W t*Y N t*P N t) := by
    let aN := ∑ n ∈ A N, |a N n|/(n : ℝ)
    let bN := ∑ n ∈ B N, |b N n|/(n : ℝ)
    let fN := (∏ p ∈ N.primesLE, (1-(p : ℝ)⁻¹)⁻¹) / Real.log N
    have ha0 : 0 ≤ aN := sum_nonneg (fun _ _ => by positivity)
    have hb0 : 0 ≤ bN := sum_nonneg (fun _ _ => by positivity)
    have H (t : ℝ) : Y N t ≤ fN := div_le_div_of_nonneg_right
      (smoothLSeries_global_le f N _ h1 hm hf) (hlog0 N)
    have hF0 : 0 ≤ fN := (hy N 0).trans (H 0)
    have hWi : Integrable W := (𝓕 h).integrable.norm
    refine (hWi.mul_const (fN*(aN*bN))).mono' ?_ ?_
    · exact ((𝓕 h).continuous.norm.mul (hcontY N) |>.mul (hcontP N)).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hw t) (hy N t)) (hp N t))]
        have ha' : ‖U N t‖ ≤ aN := finite_LScore_norm_le _ _ (ha N) _
        have hb' : ‖V N t‖ ≤ bN := finite_LScore_norm_le _ _ (hb N) _
        have hPQ : P N t ≤ aN*bN := mul_le_mul ha' hb' (norm_nonneg _) ha0
        calc
          W t*Y N t*P N t ≤ (W t*fN)*(aN*bN) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (H t) (hw t)) hPQ (hp N t)
              (mul_nonneg (hw t) hF0)
          _ = W t*(fN*(aN*bN)) := by ring
  have hlimit := band_dominated_integral_limit P Y W Env C G hp hy hw hEnv0 hEnv hCe hGe
    hWe hY hYloc hP (fun N k => (hcontP N).intervalIntegrable ..) hiF
  refine complex_integral_limit_of_real_majorant _ _ hiF ?_ ?_ hlimit
  · intro N
    have hph : Continuous (fun t : ℝ => Complex.exp (((-2*Real.pi*t*Real.log N : ℝ) : ℂ)*Complex.I)) := by fun_prop
    exact (((hcontU N).mul (hcontV N)).mul ((hcontF N).div_const _) |>.mul hph |>.mul
      (𝓕 h).continuous).aestronglyMeasurable
  · intro N t
    simp only [norm_mul,norm_div,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (hlog0 N)]
    dsimp [U,V,F,P,Y,W]
    apply le_of_eq
    ring

end

/- Source section: 239-triple-mellin-integral.lean -/
section


open Finset MeasureTheory
open scoped FourierTransform

noncomputable def phase (y t : ℝ) : ℂ :=
  Complex.exp (((2*Real.pi*t*y : ℝ) : ℂ)*Complex.I)

theorem norm_phase (y t : ℝ) : ‖phase y t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase_sub (x y t : ℝ) : phase (x-y) t = phase x t * phase (-y) t := by
  unfold phase
  rw [← Complex.exp_add]
  have he : 2*Real.pi*t*(x-y) = 2*Real.pi*t*x + 2*Real.pi*t*(-y) := by ring
  rw [he, Complex.ofReal_add, add_mul]

theorem integrable_fourier_phase (h : SchwartzMap ℝ ℂ) (y : ℝ) :
    Integrable (fun t : ℝ => phase y t * (𝓕 (h : ℝ → ℂ)) t) := by
  have hf : Integrable (𝓕 (h : ℝ → ℂ)) := (𝓕 h).integrable
  refine hf.bdd_mul ?_ (c := (1 : ℝ)) ?_
  · exact (show Continuous (fun t : ℝ => phase y t) by unfold phase; fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => (norm_phase y t).le

theorem schwartz_phase_inversion (h : SchwartzMap ℝ ℂ) (y : ℝ) :
    h y = ∫ t : ℝ, phase y t * (𝓕 (h : ℝ → ℂ)) t := by
  have hf : Integrable (𝓕 (h : ℝ → ℂ)) := (𝓕 h).integrable
  have he := h.integrable.fourierInv_fourier_eq hf h.continuous.continuousAt (v := y)
  rw [Real.fourierInv_eq'] at he
  rw [← he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    simp only [phase, smul_eq_mul, RCLike.inner_apply, show (starRingEnd ℝ) t = t from rfl, Complex.ofReal_mul]
    congr 1
    ring

theorem finite_smoothed_mellin {ι : Type*} (A : Finset ι) (w : ι → ℂ) (freq : ι → ℝ)
    (shift : ℝ) (h : SchwartzMap ℝ ℂ) :
    (∑ n ∈ A, w n * h (freq n-shift)) =
      ∫ t : ℝ, ((∑ n ∈ A, w n*phase (freq n) t)*phase (-shift) t)*(𝓕 (h : ℝ → ℂ)) t := by
  have hs : (fun t : ℝ => ((∑ n ∈ A, w n*phase (freq n) t)*phase (-shift) t)*(𝓕 (h : ℝ → ℂ)) t)
      = fun t : ℝ => ∑ n ∈ A, w n*(phase (freq n-shift) t*(𝓕 (h : ℝ → ℂ)) t) := by
    funext t
    rw [sum_mul, sum_mul]
    apply sum_congr rfl
    intro n hn
    rw [phase_sub]
    ring
  rw [hs, integral_finsetSum A]
  · apply sum_congr rfl
    intro n hn
    rw [integral_const_mul, ← schwartz_phase_inversion]
  · intro n hn
    exact (integrable_fourier_phase h _).const_mul _


theorem smoothed_mellin {ι : Type*} [Countable ι] (w : ι → ℂ) (freq : ι → ℝ)
    (shift : ℝ) (h : SchwartzMap ℝ ℂ) (hw : Summable (fun a => ‖w a‖)) :
    (∑' n : ι, w n * h (freq n-shift)) =
      ∫ t : ℝ, ((∑' n : ι, w n*phase (freq n) t)*phase (-shift) t)*(𝓕 (h : ℝ → ℂ)) t := by
  let F (n : ι) (t : ℝ) := w n*(phase (freq n-shift) t*(𝓕 (h : ℝ → ℂ)) t)
  have hi (n : ι) : Integrable (F n) := (integrable_fourier_phase h _).const_mul _
  have hs : Summable (fun n : ι => ∫ t : ℝ, ‖F n t‖) := by
    have he (n : ι) : (∫ t : ℝ, ‖F n t‖) = ‖w n‖ * (∫ t : ℝ, ‖(𝓕 (h : ℝ → ℂ)) t‖) := by
      simp only [F, norm_mul, norm_phase, one_mul, integral_const_mul]
    exact (hw.mul_right _).congr (fun n => (he n).symm)
  calc
    _ = ∑' n : ι, ∫ t : ℝ, F n t := by
      apply tsum_congr
      intro n
      rw [schwartz_phase_inversion h (freq n-shift), ← integral_const_mul]
    _ = ∫ t : ℝ, ∑' n : ι, F n t := integral_tsum_of_summable_integral_norm hi hs
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [F, phase_sub]
        simp_rw [← mul_assoc]
        rw [tsum_mul_right, tsum_mul_right]


open Finset

open scoped ContDiff
noncomputable def cutoffBump (ε : ℝ) (he : 0 < ε) (hE : ε < 1/4) :
    ContDiffBump (1/2 : ℝ) :=
  ⟨1/2-ε, 1/2-ε/2, by linarith, by linarith⟩

theorem cutoffBump_one (ε : ℝ) (he : 0 < ε) (hE : ε < 1/4)
    (x : ℝ) (hx : ε ≤ x) (hX : x ≤ 1-ε) :
    cutoffBump ε he hE x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  dsimp [cutoffBump]
  constructor <;> linarith

theorem cutoffBump_zero_outside (ε : ℝ) (he : 0 < ε) (hE : ε < 1/4)
    (x : ℝ) (hx : x ≤ ε/2 ∨ 1-ε/2 ≤ x) :
    cutoffBump ε he hE x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  dsimp [cutoffBump]
  rcases hx with hx | hx
  · linarith [neg_le_abs (x-1/2)]
  · linarith [le_abs_self (x-1/2)]

noncomputable def cutoffMellinFun (ε : ℝ) (he : 0 < ε) (hE : ε < 1/4)
    (y : ℝ) : ℂ :=
  ((Real.exp y * cutoffBump ε he hE (Real.exp y) : ℝ) : ℂ)

theorem cutoffMellinFun_compact (ε : ℝ) (he : 0 < ε) (hE : ε < 1/4) :
    HasCompactSupport (cutoffMellinFun ε he hE) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.log (ε/2)) (b := Real.log (1-ε/2)))
  intro y hy
  have hp : 0 < ε/2 := by linarith
  have hq : 0 < 1-ε/2 := by linarith
  have hnonzero : cutoffBump ε he hE (Real.exp y) ≠ 0 := by
    intro h
    exact hy (by simp [cutoffMellinFun,h])
  constructor
  · by_contra! h
    have hx : Real.exp y ≤ ε/2 := by
      rw [← Real.exp_log hp]
      exact Real.exp_le_exp.mpr h.le
    exact hnonzero (cutoffBump_zero_outside ε he hE _ (Or.inl hx))
  · by_contra! h
    have hx : 1-ε/2 ≤ Real.exp y := by
      rw [← Real.exp_log hq]
      exact Real.exp_le_exp.mpr h.le
    exact hnonzero (cutoffBump_zero_outside ε he hE _ (Or.inr hx))

noncomputable def cutoffMellinSchwartz (ε : ℝ) (he : 0 < ε) (hE : ε < 1/4) :
    SchwartzMap ℝ ℂ :=
  (cutoffMellinFun_compact ε he hE).toSchwartzMap (by
    unfold cutoffMellinFun
    apply Complex.ofRealCLM.contDiff.comp
    exact Real.contDiff_exp.mul ((cutoffBump ε he hE).contDiff.comp Real.contDiff_exp))


open Finset

theorem cutoff_discrete_error (a : ℕ → ℝ) (B ε : ℝ) (N : ℕ)
    (hN : 0 < N) (he : 0 < ε) (hE : ε < 1/4)
    (hB : 0 ≤ B) (ha : ∀ n ∈ Icc 1 N, |a n| ≤ B) :
    |(∑ n ∈ Icc 1 N, a n) -
       (∑ n ∈ Icc 1 N, a n * cutoffBump ε he hE ((n : ℝ)/N))|
      ≤ (2*(ε*N)+2)*B := by
  classical
  let Q := Icc 1 N
  let bad := Q.filter (fun n : ℕ => (n : ℝ) < ε*N ∨ (1-ε)*N < n)
  let K := ⌊ε*(N : ℝ)⌋₊
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hK : (K : ℝ) ≤ ε*N := Nat.floor_le (by positivity)
  have hcard : bad.card ≤ K+1+(K+1) := by
    let low := Q.filter (fun n : ℕ => (n : ℝ) < ε*N)
    let high := Q.filter (fun n : ℕ => (1-ε)*N < n)
    have heq : bad = low∪high := by
      ext n
      simp [bad,low,high,and_or_left]
    have hl : low ⊆ range (K+1) := by
      intro n hn
      obtain ⟨h1,h2⟩ := mem_filter.mp hn
      exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff
        (show 0 ≤ ε*(N : ℝ) by positivity)).2 h2.le))
    have hh : high.image (fun n => N-n) ⊆ range (K+1) := by
      intro d hd
      obtain ⟨n,hn,rfl⟩ := mem_image.mp hd
      obtain ⟨h1,h2⟩ := mem_filter.mp hn
      have hle := (mem_Icc.mp h1).2
      have hr : ((N-n : ℕ) : ℝ) ≤ ε*N := by
        rw [Nat.cast_sub hle]
        nlinarith
      exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff
        (show 0 ≤ ε*(N : ℝ) by positivity)).2 hr))
    have hinj : Set.InjOn (fun n : ℕ => N-n) (high : Set ℕ) := by
      intro n hn m hm hnm
      change N-n = N-m at hnm
      have hn' := (mem_Icc.mp (mem_filter.mp hn).1).2
      have hm' := (mem_Icc.mp (mem_filter.mp hm).1).2
      omega
    have hc₁ : low.card ≤ K+1 := by simpa using card_le_card hl
    have hc₂ : high.card ≤ K+1 := by
      rw [← card_image_of_injOn hinj]
      simpa using card_le_card hh
    rw [heq]
    exact (card_union_le _ _).trans (Nat.add_le_add hc₁ hc₂)
  have hcardR : (bad.card : ℝ) ≤ 2*(ε*N)+2 := by
    have hc : (bad.card : ℝ) ≤ (K : ℝ)+1+((K : ℝ)+1) := by exact_mod_cast hcard
    linarith
  let b := cutoffBump ε he hE
  have hterm (n : ℕ) (hn : n ∈ Q) :
      |a n-a n*b ((n : ℝ)/N)| ≤ if n∈bad then B else 0 := by
    by_cases hbad : n ∈ bad
    · rw [if_pos hbad]
      have h0 : 0 ≤ b ((n : ℝ)/N) := b.nonneg
      have h1 : b ((n : ℝ)/N) ≤ 1 := b.le_one
      rw [show a n-a n*b ((n : ℝ)/N)=a n*(1-b ((n : ℝ)/N)) by ring,
        abs_mul, abs_of_nonneg (show 0 ≤ 1-b ((n : ℝ)/N) by linarith)]
      exact (mul_le_of_le_one_right (abs_nonneg _) (by linarith)).trans (ha n hn)
    · rw [if_neg hbad]
      have h : ¬((n : ℝ) < ε*N ∨ (1-ε)*N < n) := fun hx => hbad (mem_filter.mpr ⟨hn,hx⟩)
      have hL : ε ≤ (n : ℝ)/N := (le_div_iff₀ hNR).2 (le_of_not_gt fun hx => h (Or.inl hx))
      have hU : (n : ℝ)/N ≤ 1-ε := (div_le_iff₀ hNR).2 (le_of_not_gt fun hx => h (Or.inr hx))
      rw [show b ((n : ℝ)/N) = 1 from cutoffBump_one ε he hE _ hL hU]
      simp
  change |(∑ n ∈ Q, a n) - (∑ n ∈ Q, a n*b ((n : ℝ)/N))| ≤ _
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Q, |a n-a n*b ((n : ℝ)/N)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Q, if n∈bad then B else 0 := sum_le_sum hterm
    _ = (bad.card : ℝ)*B := by
      rw [← sum_filter]
      have h : Q.filter (fun n => n∈bad) = bad := by
        ext n
        simp only [mem_filter]
        exact ⟨fun hn=>hn.2, fun hn=>⟨(mem_filter.mp hn).1,hn⟩⟩
      rw [h]
      simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardR hB


theorem smoothed_triple_integral (a b c : ArithmeticFunction ℂ) (N : ℕ) (h : SchwartzMap ℝ ℂ)
    (ha : Summable (fun n : ℕ => ‖a n/(n : ℂ)‖))
    (hb : Summable (fun n : ℕ => ‖b n/(n : ℂ)‖))
    (hc : Summable (fun n : ℕ => ‖c n/(n : ℂ)‖))
    (hC : Summable (fun n : ℕ => ‖(a*(b*c)) n/(n : ℂ)‖)) :
    (∑' n : ℕ, ((a*(b*c)) n/(n : ℂ))*h (Real.log n-Real.log N)) =
      ∫ t : ℝ, (((LSeries a (LPhasePoint (2*Real.pi*t))) *
        (LSeries b (LPhasePoint (2*Real.pi*t))) *
        (LSeries c (LPhasePoint (2*Real.pi*t)))) *
        phase (-Real.log N) t)*(𝓕 (h : ℝ → ℂ)) t := by
  rw [smoothed_mellin (fun n : ℕ => (a*(b*c)) n/(n : ℂ))
      (fun n : ℕ => Real.log n) (Real.log N) h hC]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have he : (∑' n : ℕ, (a*(b*c)) n/(n : ℂ)*phase (Real.log n) t) =
        (∑' n : ℕ, LPhaseTerm (a*(b*c) : ArithmeticFunction ℂ) (2*Real.pi*t) n) := rfl
    change ((∑' n : ℕ, (a*(b*c)) n/(n : ℂ)*phase (Real.log n) t)*phase (-Real.log N) t)*(𝓕 (h : ℝ → ℂ)) t = _
    rw [he, triple_LSeries_phase a b c _ (phaseSummable _ _ ha)
      (phaseSummable _ _ hb) (phaseSummable _ _ hc)]
    simp only [← LSeries_phase]


theorem cutoff_weighted_coeff (d : ℕ → ℂ) (N : ℕ) (hN : N ≠ 0) (ε : ℝ)
    (he : 0 < ε) (hE : ε < 1/4) :
    (∑' n : ℕ, (d n/(n : ℂ))*cutoffMellinSchwartz ε he hE (Real.log n-Real.log N)) =
      (∑ n ∈ Icc 1 N, d n*((cutoffBump ε he hE ((n : ℝ)/N) : ℝ) : ℂ))/(N : ℂ) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [tsum_eq_sum (s := Icc 1 N)]
  · rw [div_eq_mul_inv, sum_mul]
    apply sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (mem_Icc.mp hn).1
    have hx : Real.exp (Real.log (n : ℝ)-Real.log N) = (n : ℝ)/N := by
      rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hNR]
    change (d n/(n : ℂ)) *
      (((Real.exp (Real.log (n : ℝ)-Real.log N)*cutoffBump ε he hE
        (Real.exp (Real.log (n : ℝ)-Real.log N))) : ℝ) : ℂ) = _
    rw [hx, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hn).1)
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp
  · intro n hn
    by_cases hzero : n = 0
    · simp [hzero]
    have hgt : N < n := by
      by_contra! h
      exact hn (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hzero,h⟩)
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
    have hx : Real.exp (Real.log (n : ℝ)-Real.log N) = (n : ℝ)/N := by
      rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hNR]
    have hratio : (1 : ℝ) ≤ (n : ℝ)/N := (one_le_div hNR).2 (by exact_mod_cast hgt.le)
    have hz : cutoffBump ε he hE ((n : ℝ)/N) = 0 :=
      cutoffBump_zero_outside ε he hE _ (Or.inr (by linarith))
    change (d n/(n : ℂ)) *
      (((Real.exp (Real.log (n : ℝ)-Real.log N)*cutoffBump ε he hE
        (Real.exp (Real.log (n : ℝ)-Real.log N))) : ℝ) : ℂ) = 0
    rw [hx,hz]
    simp

end

/- Source section: 239-sharp-approx.lean -/
section


/- Source section: 239-mean-expansion.lean -/
section


open Finset
open scoped ArithmeticFunction

noncomputable def logWeighted (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log n, by simp⟩

noncomputable def mangoldtWeighted (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Λ n, by simp⟩

theorem logWeighted_convolution (f g : ArithmeticFunction ℝ) :
    logWeighted (f*g) = logWeighted f * g + f * logWeighted g := by
  ext n
  change ((f*g) n) * Real.log n = (logWeighted f*g) n + (f*logWeighted g) n
  simp only [ArithmeticFunction.mul_apply, sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  obtain ⟨hp,hN⟩ := Nat.mem_divisorsAntidiagonal.mp hu
  have hm : u.1 ≠ 0 := fun h => hN (by simpa [h] using hp.symm)
  have hn : u.2 ≠ 0 := fun h => hN (by simpa [h] using hp.symm)
  change f u.1 * g u.2 * Real.log n =
    (f u.1 * Real.log u.1) * g u.2 + f u.1 * (g u.2 * Real.log u.2)
  rw [← hp, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem complete_log_convolution (f : ArithmeticFunction ℝ)
    (hf : ∀ a b : ℕ, f (a*b) = f a * f b) :
    logWeighted f = mangoldtWeighted f * f := by
  ext n
  change f n * Real.log n = (mangoldtWeighted f * f) n
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => mangoldtWeighted f a * f b)]
  apply sum_congr rfl
  intro d hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hmul : d * (n/d) = n := Nat.mul_div_cancel' hdvd
  change f n * Λ d = f d * Λ d * f (n/d)
  conv_lhs => rw [← hmul, hf]
  ring

theorem complete_log_square_convolution (f : ArithmeticFunction ℝ)
    (hf : ∀ a b : ℕ, f (a*b) = f a * f b) :
    logWeighted (logWeighted f) =
      logWeighted (mangoldtWeighted f) * f + mangoldtWeighted f * (mangoldtWeighted f*f) := by
  calc
    _ = logWeighted (mangoldtWeighted f * f) := congrArg logWeighted (complete_log_convolution f hf)
    _ = logWeighted (mangoldtWeighted f) * f + mangoldtWeighted f * logWeighted f :=
      logWeighted_convolution _ _
    _ = _ := by rw [complete_log_convolution f hf]


theorem log_step_bound (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) * (Real.log (n+1 : ℝ) - Real.log n) ≤ 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [← Real.log_div (by positivity) hnR.ne']
  have he : 0 < (n+1 : ℝ)/(n : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos he
  apply (mul_le_mul_of_nonneg_left h hnR.le).trans
  rw [show (n+1 : ℝ)/(n : ℝ)-1 = 1/(n : ℝ) by
    field_simp
    ring]
  rw [mul_one_div_cancel hnR.ne']

theorem sum_log_error (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log n) ≤ (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : Icc 1 (N+1) = insert (N+1) (Icc 1 N) := by
      ext n
      simp only [mem_Icc, mem_insert]
      omega
    rw [hs, sum_insert (by simp)]
    rw [show Real.log ((N+1 : ℕ) : ℝ) - Real.log ((N+1 : ℕ) : ℝ) = 0 by exact sub_self _, zero_add]
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    have he : (∑ n ∈ Icc 1 N, (Real.log ((N+1 : ℕ) : ℝ) - Real.log n)) =
        (∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log n)) +
          (N : ℝ) * (Real.log (N+1 : ℝ) - Real.log N) := by
      have hterm : ∀ n : ℕ,
          Real.log ((N+1 : ℕ) : ℝ) - Real.log n =
          (Real.log (N : ℝ) - Real.log n) + (Real.log (N+1 : ℝ) - Real.log N) := by
        intro n; rw [Nat.cast_add, Nat.cast_one]; ring
      rw [show (∑ n ∈ Icc 1 N, (Real.log ((N+1 : ℕ) : ℝ) - Real.log n)) =
        ∑ n ∈ Icc 1 N, ((Real.log (N : ℝ) - Real.log n) +
          (Real.log (N+1 : ℝ) - Real.log N)) from sum_congr rfl fun n _ => hterm n]
      rw [sum_add_distrib]
      simp [nsmul_eq_mul]
      ring
    rw [he, Nat.cast_add, Nat.cast_one]
    exact add_le_add ih (log_step_bound N hN)

theorem linear_log_weight_error (f : ℕ → ℝ) (hf : ∀ n ≥ 1, |f n| ≤ 1) (N : ℕ) :
    |Real.log (N : ℝ) * (∑ n ∈ Icc 1 N, f n) -
        (∑ n ∈ Icc 1 N, f n * Real.log n)| ≤ (N : ℝ) := by
  rw [mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |Real.log (N : ℝ) * f n - f n * Real.log n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log n) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hnd : 0 ≤ Real.log (N : ℝ) - Real.log n :=
        sub_nonneg.mpr (Real.log_le_log hnR (by exact_mod_cast hnN))
      rw [show Real.log (N : ℝ) * f n - f n * Real.log n =
        f n * (Real.log (N : ℝ) - Real.log n) by ring, abs_mul, abs_of_nonneg hnd]
      exact mul_le_of_le_one_left hnd (hf n hn1)
    _ ≤ _ := sum_log_error N


open Filter Finset
open scoped Topology

noncomputable def sumTo (f : ArithmeticFunction ℝ) (N : ℕ) := ∑ n ∈ Icc 1 N, f n

theorem complete_first_mean_expansion (f : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ m n : ℕ, f (m*n) = f m * f n)
    (hb : ∀ n : ℕ, |f n| ≤ 1) :
    |Real.log (N : ℝ)*sumTo f N -
        (∑ d ∈ range (N+1), mangoldtWeighted f d*sumTo f (N/d))| ≤ (N : ℝ) := by
  have hsum := convolution_sum (mangoldtWeighted f) f N
  rw [← complete_log_convolution f hf] at hsum
  unfold sumTo
  rw [← hsum]
  exact linear_log_weight_error f (fun n _ => hb n) N

theorem abs_sumTo_le (f : ArithmeticFunction ℝ) (hb : ∀ n : ℕ, |f n| ≤ 1) (N : ℕ) :
    |sumTo f N| ≤ (N : ℝ) := by
  unfold sumTo
  calc
    _ ≤ ∑ n ∈ Icc 1 N, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, (1 : ℝ) := sum_le_sum fun n _ => hb n
    _ = _ := by simp

open scoped ArithmeticFunction

theorem complete_second_mean_expansion_error (f : ArithmeticFunction ℝ) (N : ℕ) (P : Finset ℕ)
    (hf : ∀ m n : ℕ, f (m*n) = f m * f n)
    (hb : ∀ n : ℕ, |f n| ≤ 1)
    (hp : ∀ d ∈ P, 0 < d ∧ 1 < N/d) :
    |(∑ d ∈ P, mangoldtWeighted f d*sumTo f (N/d)) -
        (∑ d ∈ P, (mangoldtWeighted f d/Real.log ((N/d : ℕ) : ℝ)) *
          ∑ q ∈ range (N/d+1), mangoldtWeighted f q*sumTo f ((N/d)/q))| ≤
      ∑ d ∈ P, (Λ d * ((N/d : ℕ) : ℝ)) / Real.log ((N/d : ℕ) : ℝ) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
  let Q := N/d
  let c := mangoldtWeighted f d
  let S := sumTo f Q
  let A := ∑ q ∈ range (Q+1), mangoldtWeighted f q*sumTo f (Q/q)
  let L := Real.log (Q : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (hp d hd).2)
  have h0 : |L*S-A| ≤ Q := complete_first_mean_expansion f Q hf hb
  have hc : |c| ≤ Λ d := by
    change |f d*Λ d| ≤ Λ d
    rw [abs_mul, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n:=d))]
    exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (hb d)
  change |c*S - (c/L)*A| ≤ (Λ d * (Q : ℝ))/L
  have he : c*S - (c/L)*A = (c*(L*S-A))/L := by
    field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hL]
  exact div_le_div_of_nonneg_right
    (mul_le_mul hc h0 (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg) hL.le


noncomputable def restrictArith (f : ArithmeticFunction ℝ) (P : Finset ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ P then f n else 0, by simp⟩

theorem convolution_sum_restrict (a b : ArithmeticFunction ℝ) (P : Finset ℕ) (N : ℕ)
    (hP : P ⊆ range (N+1)) :
    sumTo (restrictArith a P*b) N = ∑ d ∈ P, a d*sumTo b (N/d) := by
  unfold sumTo
  rw [convolution_sum]
  simp only [restrictArith]
  change (∑ d ∈ range (N+1), (if d∈P then a d else 0) * ∑ n ∈ Icc 1 (N/d), b n) = _
  simp_rw [ite_mul, zero_mul, ← sum_filter]
  have hF : (range (N+1)).filter (fun d => d∈P) = P := by
    ext d
    exact ⟨fun hd => (mem_filter.mp hd).2, fun hd => mem_filter.mpr ⟨hP hd,hd⟩⟩
  rw [hF]

noncomputable def mangoldtLogDenom (f : ArithmeticFunction ℝ) (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => mangoldtWeighted f d/Real.log ((N/d : ℕ) : ℝ), by simp⟩

theorem complete_second_expansion_is_triple (f : ArithmeticFunction ℝ) (N : ℕ) (P : Finset ℕ)
    (hP : P ⊆ range (N+1)) :
    (∑ d ∈ P, (mangoldtWeighted f d/Real.log ((N/d : ℕ) : ℝ)) *
          ∑ q ∈ range (N/d+1), mangoldtWeighted f q*sumTo f ((N/d)/q)) =
      sumTo (restrictArith (mangoldtLogDenom f N) P * (mangoldtWeighted f * f)) N := by
  rw [convolution_sum_restrict (mangoldtLogDenom f N) (mangoldtWeighted f * f) P N hP]
  apply sum_congr rfl
  intro d hd
  change (mangoldtLogDenom f N) d * _ = (mangoldtLogDenom f N) d * _
  congr 1
  unfold sumTo
  rw [convolution_sum]

end

/- Source section: 239-discarded-divisors.lean -/
section


open Filter Finset
open scoped Topology

open scoped ArithmeticFunction
open Finset
open scoped ArithmeticFunction
noncomputable def largeDenominatorSet (N : ℕ) (η : ℝ) : Finset ℕ :=
  (Icc 1 N).filter (fun d : ℕ => η*Real.log N ≤ Real.log ((N/d : ℕ) : ℝ))

theorem largeDenominator_properties (N : ℕ) (η : ℝ) (hN : 1 < N) (hη : 0 < η)
    (d : ℕ) (hd : d ∈ largeDenominatorSet N η) :
    0 < d ∧ d ≤ N ∧ 1 < N/d ∧ η*Real.log N ≤ Real.log ((N/d : ℕ) : ℝ) := by
  obtain ⟨hdI,hlog⟩ := mem_filter.mp hd
  obtain ⟨hd1,hdN⟩ := mem_Icc.mp hdI
  have hpos : 0 < η*Real.log (N : ℝ) := mul_pos hη (Real.log_pos (by exact_mod_cast hN))
  have hl1 := hpos.trans_le hlog
  have hl : (1 : ℝ) < ((N/d : ℕ) : ℝ) :=
    (Real.log_pos_iff (show 0 ≤ ((N/d : ℕ) : ℝ) by positivity)).mp hl1
  exact ⟨hd1,hdN,by exact_mod_cast hl,hlog⟩

theorem log_div_floor_lower (N d : ℕ) (hd : 0 < d) (hND : d ≤ N) :
    Real.log (N : ℝ) - Real.log 2 - Real.log (d : ℝ) ≤ Real.log ((N/d : ℕ) : ℝ) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (hd.trans_le hND)
  have hdiv := Real.log_le_log (div_pos hNR (mul_pos (by norm_num) hdR))
    (half_div_le_floor N d hd hND)
  rwa [Real.log_div hNR.ne' (by positivity), Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hdR.ne',
    ← sub_sub] at hdiv

theorem discarded_divisors_mass (N : ℕ) (η : ℝ) (hN : 1 < N) (hη : 0 < η) :
    (∑ d ∈ Icc 1 N \ largeDenominatorSet N η, Λ d/(d : ℝ)) ≤
      (η*Real.log N+Real.log 2+2)*((Real.log 4+4)*Real.exp 1) := by
  classical
  let lo := Real.log (N : ℝ) - Real.log 2 - η*Real.log N
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlo : lo ≤ Real.log N := by
    dsimp [lo]
    linarith [mul_nonneg hη.le hlN.le, Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  have hA (d : ℕ) (hd : d ∈ Icc 1 N \ largeDenominatorSet N η) :
      0 < d ∧ lo ≤ Real.log (d : ℝ) ∧ Real.log (d : ℝ) ≤ Real.log N := by
    obtain ⟨hdI,hnot⟩ := mem_sdiff.mp hd
    obtain ⟨hd1,hdN⟩ := mem_Icc.mp hdI
    have hg : Real.log ((N/d : ℕ) : ℝ) < η*Real.log N := lt_of_not_ge
      (fun h => hnot (mem_filter.mpr ⟨hdI,h⟩))
    have hlog := log_div_floor_lower N d hd1 hdN
    refine ⟨hd1, ?_, Real.log_le_log (Nat.cast_pos.mpr hd1) (by exact_mod_cast hdN)⟩
    dsimp [lo]
    linarith
  refine (mangoldt_log_interval_mass _ lo _ hlo hA).trans_eq ?_
  dsimp [lo]
  ring

end

open Finset
open scoped ArithmeticFunction

noncomputable def outerScore (f : ArithmeticFunction ℝ) (N : ℕ) (η : ℝ) : ArithmeticFunction ℝ :=
  restrictArith (mangoldtLogDenom f N) (largeDenominatorSet N η)

noncomputable def innerScore (f : ArithmeticFunction ℝ) (N : ℕ) : ArithmeticFunction ℝ :=
  restrictArith (mangoldtWeighted f) (Icc 1 N)

theorem mangoldtWeighted_abs (f : ArithmeticFunction ℝ) (hb : ∀ n : ℕ, |f n| ≤ 1) (d : ℕ) :
    |mangoldtWeighted f d| ≤ Λ d := by
  change |f d*Λ d| ≤ Λ d
  rw [abs_mul,abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := d))]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (hb d)

theorem outerScore_bound (f : ArithmeticFunction ℝ) (hb : ∀ n, |f n| ≤ 1)
    (N : ℕ) (hN : 1 < N) (η : ℝ) (hη : 0 < η) (d : ℕ) :
    |outerScore f N η d| ≤ ((1/η)/Real.log N)*Λ d := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hl : 0 < η*Real.log N := mul_pos hη hlog
  change |if d ∈ largeDenominatorSet N η then mangoldtWeighted f d /
    Real.log ((N/d : ℕ) : ℝ) else 0| ≤ _
  by_cases hd : d ∈ largeDenominatorSet N η
  · have h := (largeDenominator_properties N η hN hη d hd).2.2.2
    have hdpos := hl.trans_le h
    rw [if_pos hd,abs_div,abs_of_pos hdpos]
    calc
      _ ≤ Λ d / Real.log ((N/d : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (mangoldtWeighted_abs f hb d) hdpos.le
      _ ≤ Λ d / (η*Real.log N) :=
        div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hl h
      _ = _ := by field_simp
  · rw [if_neg hd,abs_zero]
    exact mul_nonneg (div_nonneg (by positivity) hlog.le) ArithmeticFunction.vonMangoldt_nonneg

theorem innerScore_bound (f : ArithmeticFunction ℝ) (hb : ∀ n, |f n| ≤ 1)
    (N d : ℕ) : |innerScore f N d| ≤ Λ d := by
  change |if d∈Icc 1 N then mangoldtWeighted f d else 0| ≤ _
  split_ifs
  · exact mangoldtWeighted_abs f hb d
  · simpa using (ArithmeticFunction.vonMangoldt_nonneg (n:=d))

theorem trimmed_first_error (f : ArithmeticFunction ℝ) (hb : ∀ n : ℕ, |f n| ≤ 1)
    (N : ℕ) (hN : 1 < N) (η : ℝ) (hη : 0 < η) :
    |(∑ d ∈ range (N+1), mangoldtWeighted f d*sumTo f (N/d)) -
       (∑ d ∈ largeDenominatorSet N η, mangoldtWeighted f d*sumTo f (N/d))|
     ≤ (N : ℝ)*((η*Real.log N+Real.log 2+2)*((Real.log 4+4)*Real.exp 1)) := by
  classical
  let P := largeDenominatorSet N η
  let Q := Icc 1 N
  have hP : P ⊆ Q := filter_subset _ _
  let w (d : ℕ) : ℝ := mangoldtWeighted f d*sumTo f (N/d)
  have hI : range (N+1) = insert 0 Q := by
    ext d
    simp [Q,Nat.lt_succ_iff]
    omega
  have hw : w 0 = 0 := by simp [w]
  have he : (∑ d ∈ range (N+1), w d) - (∑ d ∈ P, w d) = ∑ d ∈ Q \ P, w d := by
    rw [hI,sum_insert (by simp [Q]),hw,zero_add]
    have ht := sum_sdiff hP (f:=w)
    linarith
  change |(∑ d ∈ range (N+1), w d)-(∑ d ∈ P,w d)| ≤ _
  rw [he]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ d ∈ Q \ P, (N : ℝ)*(Λ d/(d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdP := (mem_sdiff.mp hd).1
      have hd1 : 0 < d := (mem_Icc.mp hdP).1
      dsimp [w]
      rw [abs_mul]
      calc
        _ ≤ Λ d * ((N/d : ℕ) : ℝ) :=
          mul_le_mul (mangoldtWeighted_abs f hb d) (abs_sumTo_le f hb _) (abs_nonneg _)
            ArithmeticFunction.vonMangoldt_nonneg
        _ ≤ Λ d*((N : ℝ)/(d : ℝ)) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
        _ = _ := by ring
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (discarded_divisors_mass N η hN hη) (Nat.cast_nonneg _)

end

/- Source section: 239-triple-coefficient-bound.lean -/
section

open Finset
open scoped ArithmeticFunction

theorem convolution_abs_le (a b A B : ArithmeticFunction ℝ)
    (ha : ∀ n : ℕ, |a n| ≤ A n) (hb : ∀ n : ℕ, |b n| ≤ B n) (n : ℕ) :
    |(a*b) n| ≤ (A*B) n := by
  simp only [ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ d ∈ n.divisorsAntidiagonal, |a d.1 * b d.2| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul (ha _) (hb _) (abs_nonneg _) ((abs_nonneg _).trans (ha _))

theorem nonnegative_convolution (a b : ArithmeticFunction ℝ)
    (ha : ∀ n : ℕ, 0 ≤ a n) (hb : ∀ n : ℕ, 0 ≤ b n) (n : ℕ) :
    0 ≤ (a*b) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun d _ => mul_nonneg (ha _) (hb _)

noncomputable def zetaReal : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

theorem zetaReal_of_ne_zero (n : ℕ) (h : n ≠ 0) : zetaReal n = 1 := by
  simp [zetaReal, ArithmeticFunction.zeta_apply_ne h]

theorem zetaReal_complete (m n : ℕ) : zetaReal (m*n) = zetaReal m*zetaReal n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [zetaReal_of_ne_zero _ (mul_ne_zero hm hn), zetaReal_of_ne_zero _ hm, zetaReal_of_ne_zero _ hn]
  exact (one_mul _).symm

theorem mangoldtWeighted_zetaReal : mangoldtWeighted zetaReal = Λ := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  change zetaReal n*Λ n = Λ n
  rw [zetaReal_of_ne_zero _ hn, one_mul]

theorem mangoldt_triple_domination (f a b : ArithmeticFunction ℝ)
    (hf : ∀ n : ℕ, |f n| ≤ 1) (ha : ∀ n : ℕ, |a n| ≤ Λ n)
    (hb : ∀ n : ℕ, |b n| ≤ Λ n) {n : ℕ} (hn : n ≠ 0) :
    |(a*(b*f)) n| ≤ (Real.log n)^2 := by
  have hzf (d : ℕ) : |f d| ≤ zetaReal d := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    rw [zetaReal_of_ne_zero _ hd]
    exact hf _
  have h₁ := convolution_abs_le a (b*f) Λ (Λ*zetaReal) ha
    (convolution_abs_le b f Λ zetaReal hb hzf) n
  have hz := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (complete_log_square_convolution zetaReal zetaReal_complete)
  rw [mangoldtWeighted_zetaReal] at hz
  change (zetaReal n * Real.log n) * Real.log n =
    (logWeighted Λ*zetaReal) n + (Λ*(Λ*zetaReal)) n at hz
  rw [zetaReal_of_ne_zero _ hn, one_mul] at hz
  have hn' : 0 ≤ (logWeighted Λ*zetaReal) n := by
    apply nonnegative_convolution
    · intro d
      change 0 ≤ Λ d * Real.log d
      apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      rcases eq_or_ne d 0 with rfl | hd
      · simp
      · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hd))
    · intro d
      rcases eq_or_ne d 0 with rfl | hd
      · simp
      rw [zetaReal_of_ne_zero _ hd]
      norm_num
  nlinarith

end

open Finset Filter MeasureTheory
open scoped ArithmeticFunction FourierTransform Topology

theorem normSum_finite_arith (f : ArithmeticFunction ℝ) (A : Finset ℕ)
    (hf : ∀ n ∉ A, f n = 0) :
    Summable (fun n : ℕ => ‖arithOfReal f n/(n : ℂ)‖) := by
  apply summable_of_hasFiniteSupport
  apply A.finite_toSet.subset
  intro n hn
  by_contra hnot
  exact hn (by change ‖arithOfReal f n/(n : ℂ)‖ = 0; rw [arithOfReal_apply,hf n hnot]; simp)

theorem normSum_triple_arith (a b c : ArithmeticFunction ℂ)
    (ha : Summable (fun n : ℕ => ‖a n/(n : ℂ)‖))
    (hb : Summable (fun n : ℕ => ‖b n/(n : ℂ)‖))
    (hc : Summable (fun n : ℕ => ‖c n/(n : ℂ)‖)) :
    Summable (fun n : ℕ => ‖(a*(b*c)) n/(n : ℂ)‖) := by
  have h := ArithmeticFunction.LSeriesSummable_mul (phaseSummable _ 0 ha)
    (ArithmeticFunction.LSeriesSummable_mul (phaseSummable _ 0 hb) (phaseSummable _ 0 hc))
  unfold LSeriesSummable at h
  have H := h.norm
  simpa only [LSeries_term_phase,LPhaseTerm,zero_mul,Complex.ofReal_zero,
    Complex.exp_zero,mul_one] using H

theorem smoothed_cutoff_limit (f : ArithmeticFunction ℝ)
    (h1 : f 1=1) (hm : ∀ m n : ℕ, f (m*n)=f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1)
    (Hdist : ∀ (T B : ℝ), ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
        ∀ t ∈ Set.Icc (-T) T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ))
    (η ε : ℝ) (hη : 0 < η) (he : 0 < ε) (hE : ε < 1/4) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, (outerScore f N η*(innerScore f N*f)) n *
        cutoffBump ε he hE ((n : ℝ)/N)) / ((N : ℝ)*Real.log N)) atTop (𝓝 0) := by
  let a := fun N => outerScore f N η
  let b := innerScore f
  let A := fun N => largeDenominatorSet N η
  let B := fun N : ℕ => Icc 1 N
  let h := cutoffMellinSchwartz ε he hE
  have hA (N : ℕ) : A N ⊆ Icc 1 N := filter_subset _ _
  have ha (N n : ℕ) (hn : n ∉ A N) : a N n = 0 := by
    change (if n∈A N then mangoldtLogDenom f N n else 0) = 0
    rw [if_neg hn]
  have hb (N n : ℕ) (hn : n ∉ B N) : b N n = 0 := by
    change (if n∈B N then mangoldtWeighted f n else 0) = 0
    rw [if_neg hn]
  have hca : ∀ᶠ N : ℕ in atTop, ∀ n∈A N, |a N n| ≤ ((1/η)/Real.log N)*Λ n := by
    filter_upwards [eventually_ge_atTop 2] with N hN n hn
    exact outerScore_bound f hf N (by omega) η hη n
  have hh := smoothed_product_halasz_limit f h1 hm hf Hdist a b A B hA
    (fun _ => Subset.rfl) ha hb (1/η) (by positivity) hca
    (fun N n _ => innerScore_bound f hf N n) h
  rw [← tendsto_ofReal_iff, Complex.ofReal_zero]
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  let c := smoothPart f N
  let α := arithOfReal (a N)
  let β := arithOfReal (b N)
  let γ := arithOfReal c
  have hα := normSum_finite_arith (a N) (A N) (ha N)
  have hβ := normSum_finite_arith (b N) (B N) (hb N)
  have hγ := normSum_smoothPart f N h1 hm hf
  have hM := smoothed_triple_integral α β γ N h hα hβ hγ
    (normSum_triple_arith α β γ hα hβ hγ)
  rw [show h = cutoffMellinSchwartz ε he hE from rfl, cutoff_weighted_coeff _ N (by omega)] at hM
  have hcon : ∀ n ≤ N, (a N*(b N*c)) n = (a N*(b N*f)) n :=
    convolution_agrees_below _ _ _ _ N (fun _ _=>rfl)
      (convolution_agrees_below _ _ _ _ N (fun _ _=>rfl) (smoothPart_agrees f N))
  have hconv (n : ℕ) (hn : n ∈ Icc 1 N) :
      (α*(β*γ)) n = (((a N*(b N*f)) n : ℝ) : ℂ) := by
    change (arithOfReal (a N)*(arithOfReal (b N)*arithOfReal c)) n = _
    rw [← arithOfReal_mul, ← arithOfReal_mul, arithOfReal_apply, hcon n (mem_Icc.mp hn).2]
  have hsum :
      (∑ n ∈ Icc 1 N, (α*(β*γ)) n * ((cutoffBump ε he hE ((n : ℝ)/N) : ℝ) : ℂ)) =
        (((∑ n ∈ Icc 1 N, (a N*(b N*f)) n * cutoffBump ε he hE ((n : ℝ)/N)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro n hn
    rw [hconv n hn, Complex.ofReal_mul]
  rw [hsum] at hM
  change (∫ t : ℝ, _) = _
  have hI : (∫ t : ℝ,
      LSeries α (LPhasePoint (2*Real.pi*t))*LSeries β (LPhasePoint (2*Real.pi*t))*
      (LSeries γ (LPhasePoint (2*Real.pi*t))/(Real.log N : ℂ))*
      Complex.exp (((-2*Real.pi*t*Real.log N : ℝ) : ℂ)*Complex.I)*
      (𝓕 (h : ℝ → ℂ)) t) =
      (∫ t : ℝ, (LSeries α (LPhasePoint (2*Real.pi*t))*LSeries β (LPhasePoint (2*Real.pi*t))*
        LSeries γ (LPhasePoint (2*Real.pi*t)))*phase (-Real.log N) t*(𝓕 (h : ℝ → ℂ)) t) /
        (Real.log N : ℂ) := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      have hp : Complex.exp (((-2*Real.pi*t*Real.log N : ℝ) : ℂ)*Complex.I) =
          phase (-Real.log N) t := by
        unfold phase
        congr 2
        ring
      simp only [hp,div_eq_mul_inv]
      ring
  rw [hI, ← hM, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, div_div]


noncomputable def scaleArith (k : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => k*f n,by simp⟩

theorem scaleArith_mul (k : ℝ) (a b : ArithmeticFunction ℝ) :
    scaleArith k a*b = scaleArith k (a*b) := by
  ext n
  have h₁ (f : ArithmeticFunction ℝ) (m : ℕ) : scaleArith k f m = k*f m := rfl
  simp only [ArithmeticFunction.mul_apply,h₁, mul_assoc, Finset.mul_sum]

theorem sharp_triple_coeff_bound (f : ArithmeticFunction ℝ) (hf : ∀ n, |f n| ≤ 1)
    (N : ℕ) (η : ℝ) (hN : 1 < N) (hη : 0 < η) (n : ℕ) (hn : n ∈ Icc 1 N) :
    |(outerScore f N η*(innerScore f N*f)) n| ≤ Real.log N/η := by
  let L := η*Real.log (N : ℝ)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hL : 0 < L := mul_pos hη hlog
  have hscale (d : ℕ) : |scaleArith L (outerScore f N η) d| ≤ Λ d := by
    change |L*outerScore f N η d| ≤ _
    rw [abs_mul,abs_of_pos hL]
    have h := mul_le_mul_of_nonneg_left (outerScore_bound f hf N hN η hη d) hL.le
    refine h.trans_eq ?_
    dsimp [L]
    field_simp
  have h0 : n ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hn).1
  have hs := mangoldt_triple_domination f _ _ hf hscale (innerScore_bound f hf N) h0
  rw [scaleArith_mul] at hs
  change |L*(outerScore f N η*(innerScore f N*f)) n| ≤ (Real.log n)^2 at hs
  rw [abs_mul,abs_of_pos hL] at hs
  have hnlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hn).1)
  have hnL : Real.log (n : ℝ) ≤ Real.log N :=
    Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2)
  apply (le_div_iff₀ hη).2
  have hh := hs.trans (pow_le_pow_left₀ hnlog hnL 2)
  dsimp [L] at hh
  apply (le_of_mul_le_mul_right _ hlog)
  calc
    _ = η*Real.log N*|(outerScore f N η*(innerScore f N*f)) n| := by ring
    _ ≤ _ := by simpa [pow_two] using hh

theorem sharp_triple_limit (f : ArithmeticFunction ℝ)
    (h1 : f 1=1) (hm : ∀ m n : ℕ, f (m*n)=f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1)
    (Hdist : ∀ (T B : ℝ), ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
        ∀ t ∈ Set.Icc (-T) T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => sumTo (outerScore f N η*(innerScore f N*f)) N /
      ((N : ℝ)*Real.log N)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero,Real.norm_eq_abs]
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun _ => hx.trans_le (abs_nonneg _),?_⟩
  intro δ hδ
  let ε := min (1/8 : ℝ) (η*δ/16)
  have he : 0 < ε := lt_min (by norm_num) (by positivity)
  have hE : ε < 1/4 := (min_le_left _ _).trans_lt (by norm_num)
  let Sm (N : ℕ) := (∑ n ∈ Icc 1 N, (outerScore f N η*(innerScore f N*f)) n *
      cutoffBump ε he hE ((n : ℝ)/N))/((N:ℝ)*Real.log N)
  have hSm : Tendsto Sm atTop (𝓝 0) := smoothed_cutoff_limit f h1 hm hf Hdist η ε hη he hE
  have hNorm : Tendsto (fun N => |Sm N|) atTop (𝓝 0) := by simpa [Real.norm_eq_abs] using hSm.norm
  have hSmB : ∀ᶠ N : ℕ in atTop, |Sm N| < δ/2 :=
    (tendsto_order.1 hNorm).2 _ (by positivity)
  have hInv0 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun N : ℕ => 2/(η*(N : ℝ))) atTop (𝓝 0) := by
    have heq : (fun N : ℕ => 2/(η*(N : ℝ))) = fun N : ℕ => (2/η)*(N : ℝ)⁻¹ := by
      funext N
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [heq]
    simpa only [mul_zero] using hInv0.const_mul (2/η)
  have hInvB : ∀ᶠ N : ℕ in atTop, 2/(η*(N : ℝ)) < δ/4 :=
    (tendsto_order.1 hInv).2 _ (by positivity)
  filter_upwards [hSmB,hInvB,eventually_ge_atTop 2] with N hs hi hN
  let T := outerScore f N η*(innerScore f N*f)
  have hN' : 1 < N := by omega
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN')
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hden := mul_pos hNR hlog
  have hh := cutoff_discrete_error (fun n => T n) (Real.log N/η) ε N (by omega) he hE
    (div_nonneg hlog.le hη.le) (fun n hn => sharp_triple_coeff_bound f hf N η hN' hη n hn)
  have hdiff : |sumTo T N/((N:ℝ)*Real.log N)-Sm N| ≤ 2*ε/η+2/(η*(N : ℝ)) := by
    unfold Sm sumTo
    rw [← sub_div,abs_div,abs_of_pos hden]
    refine (div_le_div_of_nonneg_right hh hden.le).trans_eq ?_
    field_simp
    <;> ring
  have hside : 2*ε/η ≤ δ/8 := by
    apply (div_le_iff₀ hη).2
    have := min_le_right (1/8 : ℝ) (η*δ/16)
    dsimp [ε]
    nlinarith
  change |sumTo T N/((N:ℝ)*Real.log N)| < δ
  have ht := abs_add_le (sumTo T N/((N:ℝ)*Real.log N)-Sm N) (Sm N)
  rw [sub_add_cancel] at ht
  linarith


theorem trimmed_second_error (f : ArithmeticFunction ℝ) (N : ℕ)
    (hf : ∀ m n : ℕ, f (m*n) = f m * f n)
    (hb : ∀ n : ℕ, |f n| ≤ 1) (η : ℝ) (hη : 0 < η)
    (hN : 1 < N) (hL : 1 ≤ Real.log (N : ℝ)) :
    |(∑ d ∈ largeDenominatorSet N η, mangoldtWeighted f d*sumTo f (N/d)) -
      sumTo (outerScore f N η*(innerScore f N*f)) N| ≤
      (N : ℝ)*(3*((Real.log 4+4)*Real.exp 1)/η) := by
  let P := largeDenominatorSet N η
  have hp (d : ℕ) (hd : d ∈ P) := largeDenominator_properties N η hN hη d hd
  have hP : P ⊆ range (N+1) := fun d hd => mem_range.mpr (Nat.lt_succ_of_le (hp d hd).2.1)
  have hab := complete_second_mean_expansion_error f N P hf hb
    (fun d hd => ⟨(hp d hd).1,(hp d hd).2.2.1⟩)
  rw [complete_second_expansion_is_triple f N P hP] at hab
  have hcon : ∀ n ≤ N,
      (outerScore f N η*(mangoldtWeighted f*f)) n =
      (outerScore f N η*(innerScore f N*f)) n := by
    apply convolution_agrees_below _ _ _ _ N (fun _ _=>rfl)
    apply convolution_agrees_below _ _ _ _ N _ (fun _ _=>rfl)
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have h := mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0,hn⟩
    change mangoldtWeighted f n = if n ∈ Icc 1 N then mangoldtWeighted f n else 0
    rw [if_pos h]
  have hEq : sumTo (outerScore f N η*(mangoldtWeighted f*f)) N =
      sumTo (outerScore f N η*(innerScore f N*f)) N := by
    unfold sumTo
    exact sum_congr rfl fun n hn => hcon n (mem_Icc.mp hn).2
  change |(∑ d∈P, mangoldtWeighted f d*sumTo f (N/d)) -
    sumTo (outerScore f N η*(mangoldtWeighted f*f)) N| ≤ _ at hab
  rw [hEq] at hab
  refine hab.trans ?_
  let L := Real.log (N : ℝ)
  let C := (Real.log 4+4)*Real.exp 1
  have hlog : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hηL : 0 < η*L := mul_pos hη hlog
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    positivity
  have hmass : ∑ d∈P, Λ d/(d : ℝ) ≤ (L+2)*C := by
    have H (d : ℕ) (hd : d∈P) :
        0 < d ∧ 0 ≤ Real.log (d : ℝ) ∧ Real.log (d : ℝ) ≤ L := by
      have hdP := hp d hd
      exact ⟨hdP.1, Real.log_nonneg (by exact_mod_cast hdP.1),
        Real.log_le_log (Nat.cast_pos.mpr hdP.1) (by exact_mod_cast hdP.2.1)⟩
    simpa [sub_zero] using mangoldt_log_interval_mass P 0 L hlog.le H
  calc
    _ ≤ ∑ d∈P, ((N : ℝ)/(η*L))*(Λ d/(d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdl : η*L ≤ Real.log ((N/d : ℕ) : ℝ) := (hp d hd).2.2.2
      have hdp : 0 < (d : ℝ) := Nat.cast_pos.mpr (hp d hd).1
      have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
      calc
        _ ≤ (Λ d*((N : ℝ)/(d : ℝ)))/Real.log ((N/d : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left Nat.cast_div_le hΛ) (hηL.trans_le hdl).le
        _ ≤ (Λ d*((N : ℝ)/(d : ℝ)))/(η*L) :=
          div_le_div_of_nonneg_left (by positivity) hηL hdl
        _ = _ := by ring
    _ ≤ ((N : ℝ)/(η*L))*((L+2)*C) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ ((N : ℝ)/(η*L))*(3*L*C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hC
      dsimp [L] at *
      linarith
    _ = _ := by dsimp [C]; field_simp


theorem complete_mean_zero_uniform (f : ArithmeticFunction ℝ)
    (h1 : f 1=1) (hm : ∀ m n : ℕ, f (m*n)=f m*f n) (hf : ∀ n : ℕ, |f n| ≤ 1)
    (Hdist : ∀ (T B : ℝ), ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
        ∀ t ∈ Set.Icc (-T) T, B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p))/(p : ℝ)) :
    Tendsto (fun N : ℕ => sumTo f N/(N:ℝ)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero,Real.norm_eq_abs]
  refine tendsto_order.2 ⟨fun z hz => Eventually.of_forall fun _ => hz.trans_le (abs_nonneg _),?_⟩
  intro δ hδ
  let C := (Real.log 4+4)*Real.exp 1
  have hC : 0 ≤ C := by
    dsimp [C]
    have := Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)
    positivity
  let η := δ/(4*(C+1))
  have hη : 0 < η := div_pos hδ (by positivity)
  have hηC : η*C ≤ δ/4 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 4*(C+1))).2
    calc
      δ*C ≤ δ*(C+1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = _ := by ring
  let K := 1+C*(Real.log 2+2)+3*C/η
  have hK : 0 ≤ K := by
    dsimp [K]
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    positivity
  have hInv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hK0 : Tendsto (fun N : ℕ => K/Real.log N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hInv.const_mul K
  have hKB : ∀ᶠ N : ℕ in atTop, K/Real.log N < δ/4 :=
    (tendsto_order.1 hK0).2 _ (by positivity)
  have hLB : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  let sharp (N : ℕ) := sumTo (outerScore f N η*(innerScore f N*f)) N
  have hs := (sharp_triple_limit f h1 hm hf Hdist η hη).norm
  have hsN : Tendsto (fun N => |sharp N/((N:ℝ)*Real.log N)|) atTop (𝓝 0) := by
    simpa only [sharp,Real.norm_eq_abs,norm_zero] using hs
  have hsB : ∀ᶠ N : ℕ in atTop, |sharp N/((N:ℝ)*Real.log N)| < δ/4 :=
    (tendsto_order.1 hsN).2 _ (by positivity)
  filter_upwards [hKB,hLB,hsB,eventually_ge_atTop 2] with N hkn hLn hsN hN
  let L := Real.log (N : ℝ)
  let U := L*sumTo f N
  let V := ∑ d ∈ range (N+1), mangoldtWeighted f d*sumTo f (N/d)
  let W := ∑ d ∈ largeDenominatorSet N η, mangoldtWeighted f d*sumTo f (N/d)
  have hN' : 1 < N := by omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hLn
  have hden : 0 < (N:ℝ)*L := mul_pos hNR hL
  have h1' : |U-V| ≤ (N:ℝ) := complete_first_mean_expansion f N hm hf
  have h2' : |V-W| ≤ (N:ℝ)*((η*L+Real.log 2+2)*C) :=
    trimmed_first_error f hf N hN' η hη
  have h3' : |W-sharp N| ≤ (N:ℝ)*(3*C/η) :=
    trimmed_second_error f N hm hf η hη hN' hLn
  have hsharp : |U| ≤ |sharp N|+(N:ℝ)*(η*L*C+K) := by
    have ht₁ := abs_add_le (U-V) V
    have ht₂ := abs_add_le (V-W) W
    have ht₃ := abs_add_le (W-sharp N) (sharp N)
    rw [sub_add_cancel] at ht₁ ht₂ ht₃
    have htotal : (N:ℝ)+(N:ℝ)*((η*L+Real.log 2+2)*C)+(N:ℝ)*(3*C/η) =
        (N:ℝ)*(η*L*C+K) := by dsimp [K]; ring
    linarith only [ht₁, ht₂, ht₃, h1', h2', h3', htotal]
  have hU : |sumTo f N/(N:ℝ)| = |U|/((N:ℝ)*L) := by
    dsimp [U]
    rw [abs_mul,abs_of_pos hL,abs_div,abs_of_pos hNR]
    field_simp [hL.ne',hNR.ne']
  rw [hU]
  refine (div_le_div_of_nonneg_right hsharp hden.le).trans_lt ?_
  have hsplit : (|sharp N|+(N:ℝ)*(η*L*C+K))/((N:ℝ)*L) =
      |sharp N/((N:ℝ)*L)|+η*C+K/L := by
    rw [abs_div,abs_of_pos hden]
    field_simp [hL.ne',hNR.ne']
    <;> ring
  rw [hsplit]
  have hkn' : K/L < δ/4 := hkn
  have hsN' : |sharp N/((N:ℝ)*L)| < δ/4 := hsN
  linarith only [hkn',hsN',hηC,hδ]

end

/- Source section: 239-complete-core-bridge-narrow.lean -/
section


open scoped BigOperators

noncomputable def primeExtension (a : ℕ → ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod a, if_pos rfl⟩

theorem primeExtension_apply (a : ℕ → ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    primeExtension a n = n.factorization.prod a := if_neg hn

theorem primeExtension_one (a : ℕ → ℕ → ℝ) : primeExtension a 1 = 1 := by
  rw [primeExtension_apply a one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]

theorem primeExtension_multiplicative (a : ℕ → ℕ → ℝ) :
    (primeExtension a).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2
    ⟨primeExtension_one a, fun {m n} hm hn hmn => ?_⟩
  rw [primeExtension_apply a (mul_ne_zero hm hn), primeExtension_apply a hm,
    primeExtension_apply a hn, Nat.factorization_mul hm hn]
  have h : Disjoint m.factorization.support n.factorization.support := hmn.disjoint_primeFactors
  rw [Finsupp.prod_add_index_of_disjoint h]

theorem primeExtension_power (a : ℕ → ℕ → ℝ) (ha : ∀ p, a p 0 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeExtension a (p^k) = a p k := by
  rw [primeExtension_apply a (pow_ne_zero _ hp.ne_zero), Nat.Prime.factorization_pow hp,
    Finsupp.prod_single_index (ha p)]

noncomputable def completeCore (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  primeExtension (fun p k => f p ^ k)

theorem completeCore_mul (f : ℕ → ℝ) (m n : ℕ) :
    completeCore f (m*n) = completeCore f m * completeCore f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  unfold completeCore
  rw [primeExtension_apply _ (mul_ne_zero hm hn), primeExtension_apply _ hm,
    primeExtension_apply _ hn, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun p => pow_zero (f p)) (fun p k l => pow_add (f p) k l)

theorem completeCore_power (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    completeCore f (p^k) = f p ^ k :=
  primeExtension_power _ (fun _ => pow_zero _) hp k

theorem abs_completeCore_le_one (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (n : ℕ) :
    |completeCore f n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [completeCore, primeExtension_apply _ hn]
  change |∏ p ∈ n.factorization.support, f p ^ (n.factorization p)| ≤ 1
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro p hp
    exact abs_nonneg _
  · intro p hp
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hf p (Nat.prime_of_mem_primeFactors hp))


noncomputable def correctionCoeff (f : ℕ → ℝ) (p : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => f (p^(k+1)) - f p * f (p^k)

noncomputable def primeCorrection (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  primeExtension (correctionCoeff f)

theorem correction_power (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeCorrection f (p^k) = correctionCoeff f p k :=
  primeExtension_power _ (fun _ => rfl) hp k

theorem correction_at_prime (f : ℕ → ℝ) (h1 : f 1 = 1) {p : ℕ} (hp : p.Prime) :
    primeCorrection f p = 0 := by
  rw [← pow_one p, correction_power f hp 1]
  simp [correctionCoeff, h1]

theorem correction_coeff_bound (f : ℕ → ℝ) (hf : ∀ n ≥ 1, |f n| ≤ 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : |correctionCoeff f p k| ≤ 2 := by
  cases k with
  | zero => norm_num [correctionCoeff]
  | succ k =>
    rw [correctionCoeff]
    have hpos (i : ℕ) : 1 ≤ p^i := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
    calc
      _ ≤ |f (p^(k+1))| + |f p * f (p^k)| := abs_sub _ _
      _ ≤ 1 + 1 := by
        rw [abs_mul]
        exact add_le_add (hf _ (hpos _))
          (mul_le_one₀ (hf _ hp.one_le) (abs_nonneg _) (hf _ (hpos _)))
      _ = 2 := by ring

theorem correction_telescopes (f : ℕ → ℝ) (h1 : f 1 = 1) (p k : ℕ) :
    (∑ i ∈ Finset.range (k+1), correctionCoeff f p i * f p ^ (k-i)) = f (p^k) := by
  induction k with
  | zero => simp [correctionCoeff, h1]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ i ∈ Finset.range (k+1),
        correctionCoeff f p i * f p ^ (k+1-i)) =
        (∑ i ∈ Finset.range (k+1), correctionCoeff f p i * f p ^ (k-i)) * f p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [show k+1-i = (k-i)+1 by omega, pow_succ, mul_assoc]
    rw [he, ih]
    simp only [Nat.sub_self, pow_zero, mul_one, correctionCoeff]
    ring


theorem correction_convolution (f : ArithmeticFunction ℝ) (hf : f.IsMultiplicative) :
    primeCorrection f * completeCore f = f := by
  have hm : (primeCorrection f * completeCore f).IsMultiplicative :=
    (primeExtension_multiplicative _).mul (primeExtension_multiplicative _)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hm _ hf).2
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => primeCorrection f a * completeCore f b), Nat.sum_divisors_prime_pow hp]
  trans ∑ i ∈ Finset.range (k+1), correctionCoeff f p i * f p ^ (k-i)
  · apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hd : p^k / p^i = p^(k-i) := by
      have hmul : p^(k-i) * p^i = p^k := by
        rw [← pow_add, Nat.sub_add_cancel hik]
      rw [← hmul, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
    rw [hd, correction_power f hp, completeCore_power f hp]
  · exact correction_telescopes f hf.1 p k


open Finset

noncomputable def correctionMajorant (p : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | k+2 => 2 * ((p : ℝ)⁻¹) ^ (k+2)

theorem correctionMajorant_nonnegative (p k : ℕ) : 0 ≤ correctionMajorant p k := by
  rcases k with _ | _ | k <;> simp [correctionMajorant]

theorem correctionMajorant_sum (p K : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ range K, correctionMajorant p k ≤
      1 + 2/((p : ℝ) * ((p : ℝ)-1)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hq1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 (by linarith)
  have hpos : 0 ≤ 2/((p : ℝ)*((p : ℝ)-1)) := div_nonneg (by norm_num) (mul_nonneg hp0.le (by linarith))
  rcases K with _ | _ | K
  · simp; linarith
  · simpa [correctionMajorant] using hpos
  rw [sum_range_succ', sum_range_succ']
  simp only [correctionMajorant]
  have hs := summable_geometric_of_lt_one hq hq1
  have hb := hs.sum_le_tsum (range K) (fun i _ => pow_nonneg hq i)
  rw [tsum_geometric_of_lt_one hq hq1] at hb
  have ht : (∑ i ∈ range K, 2*((p : ℝ)⁻¹) ^ (i+1+1)) ≤
      2/((p : ℝ)*((p : ℝ)-1)) := by
    have he : (∑ i ∈ range K, 2*((p : ℝ)⁻¹) ^ (i+1+1)) =
        ∑ i ∈ range K, (2*((p : ℝ)⁻¹)^2) * ((p : ℝ)⁻¹)^i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show i+1+1 = 2+i by omega, pow_add, mul_assoc]
    rw [he]
    rw [← mul_sum]
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
    have hne : (p : ℝ) ≠ 0 := hp0.ne'
    have hsub : (p : ℝ)-1 ≠ 0 := by linarith
    have hinv : 1-(p : ℝ)⁻¹ ≠ 0 := by linarith
    field_simp
  linarith

noncomputable def eulerCap (i : ℕ) : ℝ :=
    2 / (((i : ℝ)+2) * ((i : ℝ)+1))

theorem eulerCap_nonneg (i : ℕ) : 0 ≤ eulerCap i := by
  unfold eulerCap
  positivity

theorem sum_eulerCap (K : ℕ) : (∑ i ∈ range K, eulerCap i) = 2 - 2/((K : ℝ)+1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_succ, eulerCap]
    have h1 : (K : ℝ)+1 ≠ 0 := by positivity
    have h2 : (K : ℝ)+2 ≠ 0 := by positivity
    have h3 : (K : ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

theorem prod_eulerCap_le (K : ℕ) : (∏ i ∈ range K, (1+eulerCap i)) ≤ Real.exp 2 := by
  refine (Real.prod_one_add_le_exp_sum _ eulerCap_nonneg).trans ?_
  apply Real.exp_le_exp.mpr
  rw [sum_eulerCap]
  have h : 0 ≤ (2 : ℝ)/((K : ℝ)+1) := by positivity
  linarith

theorem eulerBound_Icc (N K : ℕ) :
    (∏ p ∈ Icc 2 N, ∑ k ∈ range K, correctionMajorant p k) ≤ Real.exp 2 := by
  calc
    _ ≤ ∏ p ∈ Icc 2 N, (1 + 2 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      apply prod_le_prod
      · intro p hp
        exact sum_nonneg fun _ _ => correctionMajorant_nonnegative _ _
      · exact fun p hp => correctionMajorant_sum p K (mem_Icc.mp hp).1
    _ = ∏ i ∈ range (N+1-2), (1+eulerCap i) := by
      rw [show Icc 2 N = Ico 2 (N+1) by ext x; simp, prod_Ico_eq_prod_range]
      apply prod_congr rfl
      intro i hi
      rw [eulerCap, Nat.cast_add]
      congr 2 <;> ring
    _ ≤ _ := prod_eulerCap_le _

theorem factorization_support_subset {N n : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    n.factorization.support ⊆ Icc 2 N := by
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact mem_Icc.mpr ⟨hprime.two_le,
    (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).trans hN⟩

theorem primeCorrection_term_le (f : ℕ → ℝ) (hf : ∀ n ≥ 1, |f n| ≤ 1)
    (h1 : f 1 = 1) {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    |primeCorrection f n| / (n : ℝ) ≤
      ∏ p ∈ Icc 2 N, correctionMajorant p (n.factorization p) := by
  have hs := factorization_support_subset hn hN
  rw [primeCorrection, primeExtension_apply _ hn.ne']
  rw [Finsupp.prod_of_support_subset _ hs _ (fun _ _ => rfl)]
  have hnp : (n : ℝ) = ∏ p ∈ Icc 2 N, (p : ℝ) ^ n.factorization p := by
    have h := Nat.prod_factorization_pow_eq_self hn.ne'
    rw [Finsupp.prod_of_support_subset _ hs _ (fun _ _ => pow_zero _)] at h
    exact_mod_cast h.symm
  rw [hnp, abs_prod, ← prod_div_distrib]
  apply prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    by_cases hzero : n.factorization p = 0
    · simp [hzero, correctionCoeff, correctionMajorant]
    have hpmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hzero
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpp : 0 < (p : ℝ) := Nat.cast_pos.mpr hprime.pos
    cases e : n.factorization p with
    | zero => contradiction
    | succ k =>
      cases k with
      | zero =>
        have hz : correctionCoeff f p 1 = 0 := by
          rw [← correction_power f hprime 1, pow_one, correction_at_prime f h1 hprime]
        simp [hz, correctionMajorant]
      | succ j =>
        change |correctionCoeff f p (j+1+1)| / (p : ℝ)^(j+1+1) ≤
          2 * ((p : ℝ)⁻¹)^(j+1+1)
        rw [inv_pow, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right (correction_coeff_bound f hf hprime _) (pow_nonneg hpp.le _)


theorem finite_correction_majorants (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∏ p ∈ Icc 2 N, correctionMajorant p (n.factorization p))
      ≤ ∏ p ∈ Icc 2 N, ∑ k ∈ range (N+1), correctionMajorant p k := by
  classical
  let S := Icc 2 N
  let D := Icc 1 N
  let enc (n : ℕ) : ∀ p ∈ S, ℕ := fun p _ => n.factorization p
  let weight (v : ∀ p ∈ S, ℕ) : ℝ := ∏ p ∈ S.attach, correctionMajorant p.val (v p.val p.property)
  have henc : Set.InjOn enc (D : Set ℕ) := by
    intro n hn m hm h
    change n ∈ D at hn
    change m ∈ D at hm
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    have hns : n.factorization.support ⊆ S := factorization_support_subset (by omega) hnN
    have hms : m.factorization.support ⊆ S := factorization_support_subset (by omega) hmN
    have he : n.factorization = m.factorization := by
      ext p
      by_cases hp : p ∈ S
      · exact congrFun (congrFun h p) hp
      · have hnp : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (fun ht => hp (hns ht))
        have hmp : m.factorization p = 0 := Finsupp.notMem_support_iff.mp (fun ht => hp (hms ht))
        rw [hnp,hmp]
    calc
      n = n.factorization.prod (· ^ ·) := (Nat.prod_factorization_pow_eq_self (by omega)).symm
      _ = m.factorization.prod (· ^ ·) := by rw [he]
      _ = m := Nat.prod_factorization_pow_eq_self (by omega)
  have hsub : D.image enc ⊆ S.pi (fun _ => range (N+1)) := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hv
    rw [mem_pi]
    intro p hp
    change n.factorization p ∈ range (N+1)
    obtain ⟨hn1,hnN⟩ := mem_Icc.mp hn
    by_cases hz : n.factorization p = 0
    · simp [hz]
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hz)
    have hpow : p ^ n.factorization p ∣ n :=
      (hp'.pow_dvd_iff_le_factorization (by omega)).2 le_rfl
    rw [mem_range]
    exact (Nat.lt_pow_self hp'.one_lt).trans_le
      ((Nat.le_of_dvd (by omega) hpow).trans (Nat.le_succ_of_le hnN))
  calc
    _ = ∑ n ∈ D, weight (enc n) := by
      apply sum_congr rfl
      intro n hn
      exact (prod_attach S (fun p => correctionMajorant p (n.factorization p))).symm
    _ = ∑ v ∈ D.image enc, weight v := (sum_image henc).symm
    _ ≤ ∑ v ∈ S.pi (fun _ => range (N+1)), weight v :=
      sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ =>
        prod_nonneg fun p _ => correctionMajorant_nonnegative _ _)
    _ = _ := (prod_sum S (fun _ => range (N+1)) correctionMajorant).symm

theorem primeCorrection_summable (f : ℕ → ℝ) (hf : ∀ n ≥ 1, |f n| ≤ 1)
    (h1 : f 1 = 1) : Summable (fun d : ℕ => |primeCorrection f d| / (d : ℝ)) := by
  refine summable_of_sum_le (c := Real.exp 2) (fun d => by positivity) fun s => ?_
  let N := s.sup id
  have hs : s ⊆ insert 0 (Icc 1 N) := by
    intro d hd
    by_cases hz : d = 0
    · simp [hz]
    have hN : d ≤ N := le_sup (f := id) hd
    exact mem_insert_of_mem (mem_Icc.mpr ⟨by omega, hN⟩)
  calc
    _ ≤ ∑ d ∈ insert 0 (Icc 1 N), |primeCorrection f d| / (d : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ = ∑ d ∈ Icc 1 N, |primeCorrection f d| / (d : ℝ) := by
      rw [sum_insert (by simp)]
      simp
    _ ≤ ∑ d ∈ Icc 1 N, ∏ p ∈ Icc 2 N, correctionMajorant p (d.factorization p) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
      exact primeCorrection_term_le f hf h1 (by omega) hdN
    _ ≤ _ := (finite_correction_majorants N).trans (eulerBound_Icc N (N+1))


open Filter Finset
open scoped Topology

def CompleteBoundedMean : Prop :=
  ∀ c : ArithmeticFunction ℝ, c 1 = 1 →
    (∀ m n : ℕ, c (m*n) = c m * c n) →
    (∀ n : ℕ, |c n| ≤ 1) →
    ∃ L, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, c n) / (N : ℝ)) atTop (𝓝 L)

theorem original_of_completeBoundedMean (h : CompleteBoundedMean) :
    ∀ f : ℕ → ℝ,
    (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
    (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
    f 1 = 1 →
    ∃ L, Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Icc 1 N, f n) / N) atTop (𝓝 L) := by
  intro f hf
  obtain ⟨hv, hm, h1⟩ := hf
  let fa : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else f n, if_pos rfl⟩
  have hfa (n : ℕ) (hn : n ≠ 0) : fa n = f n := if_neg hn
  have hf1 : fa 1 = 1 := (hfa 1 one_ne_zero).trans h1
  have hfabs (n : ℕ) (hn : 1 ≤ n) : |fa n| ≤ 1 := by
    rw [hfa n (by omega)]
    rcases hv n hn with H | H <;> simp [H]
  have hfm : fa.IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2 ⟨hf1, fun {m n} hM hN hcop => ?_⟩
    rw [hfa _ (mul_ne_zero hM hN), hfa _ hM, hfa _ hN, hm _ _ hcop]
  have hc1 : completeCore fa 1 = 1 := primeExtension_one _
  have hcc : ∀ n, |completeCore fa n| ≤ 1 :=
    abs_completeCore_le_one _ fun p hp => hfabs p hp.one_le
  obtain ⟨L, hL⟩ := h _ hc1 (completeCore_mul _) hcc
  have ht := convolution_preserves_mean (primeCorrection fa) (completeCore fa) L hcc hL
    (primeCorrection_summable _ hfabs hf1)
  rw [correction_convolution fa hfm] at ht
  refine ⟨_, ht.congr fun N => ?_⟩
  congr 1
  apply sum_congr rfl
  intro n hn
  exact hfa n (by have := (mem_Icc.mp hn).1; omega)

end

open Filter Finset
open scoped Topology

theorem completely_multiplicative_core_mean_zero
    (f : ℕ → ℝ) (hf : ∀ n ≥ 1, |f n| ≤ 1)
    (hm : ∀ m n : ℕ, m.Coprime n → f (m*n)=f m*f n)
    (h1 : f 1=1)
    (hd : ∀ T B : ℝ, ∃ S : Finset Nat.Primes, ∀ t ∈ Set.Icc (-T) T,
      B < ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p.val))/(p.val : ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f n)/(N:ℝ)) atTop (𝓝 0) := by
  let fa : ArithmeticFunction ℝ := ⟨fun n => if n=0 then 0 else f n, if_pos rfl⟩
  have hfa (n : ℕ) (hn : n ≠ 0) : fa n = f n := if_neg hn
  have hf1 : fa 1=1 := (hfa 1 one_ne_zero).trans h1
  have hfb (n : ℕ) (hn : 1 ≤ n) : |fa n| ≤ 1 := by
    rw [hfa n (by omega)]
    exact hf n hn
  have hfm : fa.IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2 ⟨hf1,fun {m n} hM hN hcop => ?_⟩
    rw [hfa _ (mul_ne_zero hM hN), hfa _ hM,hfa _ hN,hm _ _ hcop]
  let c := completeCore fa
  have hc1 : c 1=1 := primeExtension_one _
  have hcM (m n : ℕ) : c (m*n)=c m*c n := completeCore_mul _ _ _
  have hcB : ∀ n, |c n| ≤ 1 :=
    abs_completeCore_le_one _ fun p hp => hfb p hp.one_le
  have hcP (p : ℕ) (hp : p.Prime) : c p=f p := by
    change completeCore fa p=f p
    rw [← pow_one p, completeCore_power fa hp 1, pow_one, pow_one, hfa p hp.ne_zero]
  have hD : ∀ T B : ℝ, ∃ S : Finset ℕ, (∀ p ∈ S,p.Prime) ∧
      ∀ t ∈ Set.Icc (-T) T, B < ∑ p ∈ S, (1-c p*Real.cos (t*Real.log p))/(p:ℝ) := by
    intro T B
    obtain ⟨S,hS⟩ := hd T B
    let e : Nat.Primes ↪ ℕ := ⟨Subtype.val,Subtype.val_injective⟩
    refine ⟨S.map e,?_,?_⟩
    · intro p hp
      obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
      exact q.property
    · intro t ht
      rw [sum_map]
      have heq : (∑ p ∈ S, (1-c (e p)*Real.cos (t*Real.log (e p)))/(e p:ℝ)) =
          ∑ p ∈ S, (1-f p*Real.cos (t*Real.log p.val))/(p.val:ℝ) := by
        apply sum_congr rfl
        intro p hp
        change (1-c p.val*Real.cos (t*Real.log p.val))/(p.val:ℝ) = _
        rw [hcP p.val p.property]
      rw [heq]
      exact hS t ht
  have hmean := complete_mean_zero_uniform c hc1 hcM hcB hD
  have hlim := convolution_preserves_mean (primeCorrection fa) c 0 hcB hmean
    (primeCorrection_summable fa hfb hf1)
  have hconv : primeCorrection fa*c = fa := correction_convolution fa hfm
  rw [hconv] at hlim
  simp only [zero_div,mul_zero,tsum_zero] at hlim
  refine hlim.congr fun N => ?_
  congr 1
  apply sum_congr rfl
  intro n hn
  exact hfa n (by have := (mem_Icc.mp hn).1; omega)

end OMA239Independent

theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1_H2_R1.H2 :=
  OMA239Independent.completely_multiplicative_core_mean_zero
