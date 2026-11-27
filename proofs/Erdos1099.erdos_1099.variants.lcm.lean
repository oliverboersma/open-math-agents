import FormalConjectures.ErdosProblems.«1099»
import Mathlib

/-! Bounded divisor-gap energy along the least common multiples.
The polynomial-scale Fourier decay uses distinct products of M+1 primes.
It is combined with Gaussian smoothing and the telescoping divisor-gap
bound of Tenenbaum. The central arc and the intermediate reductions are
adapted from @marcusbuffett, and the general divisor-gap summation is
adapted from @dk8827. The arithmetic-function factorization is also
used here to bound the complementary frequencies. -/

section
-- Adapted from the factorial reduction by dk8827. H1 is the central divisor
-- estimate for least common multiples. H2 is Tenenbaum's general summation
-- theorem. The LCM increment divides k times the preceding LCM, giving the
-- logarithmic weight needed for the convergent majorant.

open Finset
open scoped BigOperators

namespace OMA.R_Erdos1099_erdos_1099_variants_lcm_R1

def H1 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ M : ℝ, 0 < M ∧
    ∀ k : ℕ, 2 ≤ k → ∀ x : ℝ,
      Real.sqrt (((Icc 1 (k - 1)).lcm id : ℕ) : ℝ) < x →
      x ≤ Real.sqrt (((Icc 1 k).lcm id : ℕ) : ℝ) →
      ∃ d : ℕ, d ∣ (Icc 1 k).lcm id ∧ x < (d : ℝ) ∧
        (d : ℝ) ≤ (1 + M * (k : ℝ) ^ (-β)) * x

def H2 : Prop :=
  ∀ α : ℝ, 1 < α → ∀ (N : ℕ → ℕ) (ε : ℕ → ℝ),
    N 0 = 1 → N 1 = 1 → (∀ k, 0 < N k) → (∀ k, N k ∣ N (k + 1)) →
    (∀ k ≥ 2, 0 < ε k) →
    (∀ k ≥ 2, ∀ x : ℝ, Real.sqrt (N (k - 1) : ℝ) < x → x ≤ Real.sqrt (N k : ℝ) →
      ∃ d : ℕ, d ∣ N k ∧ x < (d : ℝ) ∧ (d : ℝ) ≤ (1 + ε k) * x) →
    ∀ n, Erdos1099.h α (N n) ≤
      ∑ k ∈ Icc 2 n, (1 + ε k) * (α * (ε k) ^ (α - 1)) *
        Real.log ((N k : ℝ) / (N (k - 1) : ℝ))

theorem main : H1 → H2 → type_of% @Erdos1099.erdos_1099.variants.lcm := by
  intro admissible sum_bound α hα
  let L (k : ℕ) := (Icc 1 k).lcm id
  have hpos (k : ℕ) : 0 < L k := by
    apply Nat.pos_of_ne_zero
    exact lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (mem_Icc.mp hi).1
  have hstep (k : ℕ) : L k ∣ L (k + 1) := by
    apply Finset.lcm_dvd
    intro i hi
    exact Finset.dvd_lcm (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, Nat.le_succ_of_le (mem_Icc.mp hi).2⟩)
  have hproduct (k : ℕ) : L k ∣ k * L (k - 1) := by
    apply Finset.lcm_dvd
    intro i hi
    by_cases he : i = k
    · subst i
      exact dvd_mul_right _ _
    · have hle := (mem_Icc.mp hi).2
      have hd : i ∣ L (k - 1) := Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, by omega⟩)
      exact hd.trans (dvd_mul_left _ _)
  have hα1 : 0 < α - 1 := by linarith
  let β : ℝ := 3 / (α - 1)
  have hβ : 0 < β := by positivity
  obtain ⟨M, hM, hAdm⟩ := admissible β hβ
  let ε : ℕ → ℝ := fun k => M * (k : ℝ) ^ (-β)
  have εpos (k : ℕ) (hk : 2 ≤ k) : 0 < ε k := by
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_pos hM (Real.rpow_pos_of_pos hkpos _)
  let K := (1 + M) * (α * M ^ (α - 1))
  have hK : 0 ≤ K := by
    have hα0 : 0 < α := by linarith
    dsimp only [K]
    positivity
  have term_le (k : ℕ) (hk : 2 ≤ k) :
      (1 + ε k) * (α * (ε k) ^ (α - 1)) *
          Real.log ((L k : ℝ) / (L (k - 1) : ℝ)) ≤
        K * (k : ℝ) ^ (-2 : ℝ) := by
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkone
    have hden : (0 : ℝ) < L (k - 1) := by exact_mod_cast hpos (k - 1)
    have hrat : (L k : ℝ) / (L (k - 1) : ℝ) ≤ k := by
      apply (div_le_iff₀ hden).mpr
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (by omega) (hpos (k - 1))) (hproduct k)
    have hεle : ε k ≤ M := by
      simpa only [ε, mul_one] using mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hkone (neg_nonpos.mpr hβ.le)) hM.le
    have hexp : (-β) * (α - 1) = -3 := by
      dsimp only [β]
      field_simp [hα1.ne']
    have hpow : (ε k) ^ (α - 1) = M ^ (α - 1) * (k : ℝ) ^ (-3 : ℝ) := by
      dsimp only [ε]
      rw [Real.mul_rpow hM.le (by positivity), ← Real.rpow_mul hkpos.le, hexp]
    have hlog : Real.log (k : ℝ) ≤ k := by
      linarith [Real.log_le_sub_one_of_pos hkpos]
    have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hkone
    have hweight : 0 ≤ α * (ε k) ^ (α - 1) := by
      have hα0 : 0 < α := by linarith
      exact mul_nonneg hα0.le (Real.rpow_nonneg (εpos k hk).le _)
    have harg : (0 : ℝ) < (L k : ℝ) / L (k - 1) := div_pos (by exact_mod_cast hpos k) hden
    calc
      _ ≤ (1 + M) * (α * (ε k) ^ (α - 1)) * (k : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left (Real.log_le_log harg hrat) (by positivity)) <| mul_le_mul
          (mul_le_mul_of_nonneg_right (add_le_add_right hεle 1) hweight)
          hlog hlog0 (by positivity)
      _ = K * ((k : ℝ) ^ (-3 : ℝ) * (k : ℝ) ^ (1 : ℝ)) := by
        rw [hpow, Real.rpow_one]
        dsimp only [K]
        ring
      _ = _ := by
        rw [← Real.rpow_add hkpos]
        norm_num
  have hs : Summable (fun k : ℕ => K * (k : ℝ) ^ (-2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left K
  refine ⟨∑' k : ℕ, K * (k : ℝ) ^ (-2 : ℝ), fun n => ?_⟩
  calc
    Erdos1099.h α (L n) ≤ _ :=
      sum_bound α hα L ε (by simp [L]) (by simp [L]) hpos hstep εpos hAdm n
    _ ≤ ∑ k ∈ Icc 2 n, K * (k : ℝ) ^ (-2 : ℝ) :=
      sum_le_sum (fun k hk => term_le k (mem_Icc.1 hk).1)
    _ ≤ _ := hs.sum_le_tsum _ (fun k _ => mul_nonneg hK (Real.rpow_nonneg (by positivity) _))

end OMA.R_Erdos1099_erdos_1099_variants_lcm_R1
end
section
/-! After Tenenbaum, Sur un problème extrémal en arithmétique, Section 4.
Gaussian smoothing splits the divisor sum into its central frequency integral
and the complementary integral. The Gaussian identity converts a positive
lower bound back into the existence of a divisor in the desired interval.
The elementary lcm increment argument follows the parent by @marcusbuffett. -/
namespace OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1

open Real Filter Finset ProbabilityTheory MeasureTheory
open scoped Topology

/-- The central Gaussian integral of the divisor sum. -/
def H1 : Prop :=
  let L (k : ℕ) := (Icc 1 k).lcm id
  let R (k m : ℕ) := (k:ℝ)^(m+2)
  let arc (k m : ℕ) := Set.Icc (-(1/(R k m*(1+log k)^2))) (1/(R k m*(1+log k)^2))
  let wave (k m : ℕ) (y t : ℝ) := ∑ d ∈ (L k).divisors, cos ((R k m*(log d-y))*t)
  ∀ m : ℕ, ∀ᶠ k : ℕ in atTop, ∀ y : ℝ, |y-log (L k)/2| ≤ log k+1 →
  2*((L k).divisors.card:ℝ)/(R k m*(k:ℝ)^2) ≤
    ∫ t in arc k m, wave k m y t ∂(gaussianReal 0 1)

/-- Cancellation away from the central arc, up to polynomial frequencies. -/
def H2 : Prop :=
  let L (k : ℕ) := (Icc 1 k).lcm id
  let R (k m : ℕ) := (k:ℝ)^(m+2)
  let arc (k m : ℕ) := Set.Icc (-(1/(R k m*(1+log k)^2))) (1/(R k m*(1+log k)^2))
  let wave (k m : ℕ) (y t : ℝ) := ∑ d ∈ (L k).divisors, cos ((R k m*(log d-y))*t)
  ∀ m : ℕ, ∀ᶠ k : ℕ in atTop, ∀ y : ℝ, |y-log (L k)/2| ≤ log k+1 →
  |∫ t in (arc k m)ᶜ, wave k m y t ∂(gaussianReal 0 1)| ≤
    ((L k).divisors.card:ℝ)/(R k m*(k:ℝ)^2)

lemma lpos (k : ℕ) : 0<(Icc 1 k).lcm id := Nat.pos_of_ne_zero <|
  lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (mem_Icc.mp hi).1

lemma lstep (k : ℕ) (hk : 0<k) :
    let L (k : ℕ) := (Icc 1 k).lcm id
    L k ≤ k*L (k-1) := by
  intro L
  apply Nat.le_of_dvd (Nat.mul_pos hk (lpos _))
  apply Finset.lcm_dvd
  intro i hi
  by_cases h : i=k
  · subst i; exact dvd_mul_right _ _
  · have bound := (mem_Icc.mp hi).2
    have hd : i ∣ L (k-1) := Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨(mem_Icc.mp hi).1,by omega⟩)
    exact hd.trans (dvd_mul_left _ _)

private lemma cos_int (z : ℝ) :
    Integrable (fun t : ℝ => cos (z*t)) (gaussianReal 0 1) ∧
    (∫ t : ℝ, cos (z*t) ∂(gaussianReal 0 1)) = exp (-z^2/2) := by
  let f (t : ℝ) := Complex.exp ((z:ℂ)*t*Complex.I)
  have fi : Integrable f (gaussianReal 0 1) := by
    apply (integrable_const (1:ℝ)).mono' (by dsimp [f]; fun_prop)
    filter_upwards with t
    simp [f,Complex.norm_exp]
  have re (t : ℝ) : RCLike.re (f t)=cos (z*t) := by simp [f,Complex.exp_re]
  refine ⟨by simpa only [re] using fi.re,?_⟩
  simp_rw [←re]
  rw [integral_re fi]
  have h := charFun_gaussianReal (μ:=0) (v:=1) z
  rw [charFun_apply_real] at h
  change (∫ t, f t ∂(gaussianReal 0 1)) = _ at h
  rw [h]
  simp [Complex.exp_re,←Complex.ofReal_pow]
  <;> ring_nf

lemma close_divisor (h₁ : H1) (h₂ : H2) (m : ℕ) :
    let L (k : ℕ) := (Icc 1 k).lcm id
    let R (k m : ℕ) := (k:ℝ)^(m+2)
    ∀ᶠ k : ℕ in atTop,
    ∀ y : ℝ, |y-log (L k)/2| ≤ log k+1 → ∃ d ∈ (L k).divisors,
    |log d-y| < (k:ℝ)/R k m := by
  intro L R
  let arc (k m : ℕ) := Set.Icc (-(1/(R k m*(1+log k)^2))) (1/(R k m*(1+log k)^2))
  let wave (k m : ℕ) (y t : ℝ) := ∑ d ∈ (L k).divisors, cos ((R k m*(log d-y))*t)
  have decay : Tendsto (fun k : ℕ => (k:ℝ)^(m+4)*exp (-(k:ℝ))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero (m+4)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h₁ m,h₂ m,eventually_ge_atTop 2,decay.eventually_lt_const zero_lt_one] with k low high hk he
  intro y hy
  have kp : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have k2 : (2:ℝ)≤k := by exact_mod_cast hk
  have rp : 0 < R k m := by dsimp [R]; positivity
  let D := (L k).divisors
  let W := wave k m y
  have wi : Integrable W (gaussianReal 0 1) := integrable_finsetSum _ fun d _ => (cos_int _).1
  have total : (∫ t, W t ∂(gaussianReal 0 1)) =
      ∑ d ∈ D, exp (-(R k m*(log d-y))^2/2) := by
    unfold W wave
    rw [integral_finsetSum _ (fun d _ => (cos_int _).1)]
    exact sum_congr rfl fun d _ => (cos_int _).2
  have parts := integral_add_compl (μ:=gaussianReal 0 1) (f:=W) (s:=arc k m) measurableSet_Icc wi
  have lb : (D.card:ℝ)/(R k m*(k:ℝ)^2) ≤ ∫ t, W t ∂(gaussianReal 0 1) := by
    have a := low y hy
    have b := (abs_le.mp (high y hy)).1
    change 2*(D.card:ℝ)/_ ≤ ∫ t in arc k m, W t ∂(gaussianReal 0 1) at a
    change -((D.card:ℝ)/_) ≤ ∫ t in (arc k m)ᶜ, W t ∂(gaussianReal 0 1) at b
    rw [mul_div_assoc] at a
    linarith only [a,b,parts]
  by_contra! bad
  have each (d : ℕ) (hd : d ∈ D) : exp (-(R k m*(log d-y))^2/2) ≤ exp (-(k:ℝ)) := by
    apply exp_le_exp.mpr
    have large := (div_le_iff₀ rp).mp (bad d hd)
    have sq := mul_self_le_mul_self kp.le large
    rw [mul_pow] at *
    nlinarith only [sq,sq_abs (log d-y),mul_nonneg (sub_nonneg.mpr k2) kp.le,
      congrArg (fun v : ℝ => v*(R k m)^2) (sq_abs (log d-y))]
  have ub := sum_le_sum (s:=D) (fun d hd => each d hd)
  rw [sum_const,nsmul_eq_mul] at ub
  rw [total] at lb
  have cpos : (0:ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr (show D.Nonempty from ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,(lpos k).ne'⟩⟩)
  have lt : exp (-(k:ℝ)) < 1/(R k m*(k:ℝ)^2) := by
    apply (lt_div_iff₀ (mul_pos rp (sq_pos_of_pos kp))).mpr
    change (k:ℝ)^(m+4)*exp (-(k:ℝ)) < 1 at he
    dsimp [R]
    rw [show m+4=m+2+2 by omega,pow_add _ (m+2) 2] at he
    linarith only [he]
  have clash := mul_lt_mul_of_pos_left lt cpos
  rw [mul_one_div] at clash
  exact (lt_irrefl _) ((ub.trans_lt clash).trans_le lb)

theorem main : H1 → H2 → OMA.R_Erdos1099_erdos_1099_variants_lcm_R1.H1 := by
  intro low high β hb
  let L (k : ℕ) := (Icc 1 k).lcm id
  let R (k m : ℕ) := (k:ℝ)^(m+2)
  let m := ⌈β⌉₊
  have hm : β ≤ (m:ℝ) := Nat.le_ceil β
  have eventuallyGood : ∀ᶠ k : ℕ in atTop, ∀ x : ℝ,
      sqrt (L (k-1)) < x → x ≤ sqrt (L k) → ∃ d : ℕ, d ∣ L k ∧
      x < (d:ℝ) ∧ (d:ℝ) ≤ (1+(k:ℝ)^(-β))*x := by
    filter_upwards [close_divisor low high m,eventually_ge_atTop 4] with k nearby hk
    intro x xl xu
    have kp : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
    have k4 : (4:ℝ)≤k := by exact_mod_cast hk
    have k1 : (1:ℝ)≤k := by linarith
    have lp : 0 < (L k:ℝ) := by exact_mod_cast lpos k
    have prev : 0 < (L (k-1):ℝ) := by exact_mod_cast lpos _
    have xp : 0<x := (sqrt_nonneg _).trans_lt xl
    let u := (k:ℝ)^(-β)
    let s := (k:ℝ)/R k m
    have up : 0<u := rpow_pos_of_pos kp _
    have u1 : u≤1 := rpow_le_one_of_one_le_of_nonpos k1 (neg_nonpos.mpr hb.le)
    have rp : 0<R k m := by dsimp [R]; positivity
    have sp : 0<s := div_pos kp rp
    have off : s*(k:ℝ) ≤ u := by
      have cmp := rpow_le_rpow_of_exponent_le k1 (neg_le_neg hm)
      change _ ≤ (k:ℝ)^(-β)
      apply le_trans _ cmp
      rw [rpow_neg kp.le,rpow_natCast]
      dsimp [s,R]
      rw [show m+2=m+1+1 by omega,pow_succ,pow_succ]
      field_simp
      ring_nf
      <;> norm_num
    have loglow : u/2 ≤ log (1+u) := by
      apply le_trans _ (one_sub_inv_le_log_of_pos (by linarith : 0<1+u))
      have h : 0 < 1+u := by linarith
      apply (mul_le_mul_iff_of_pos_right h).mp
      field_simp
      nlinarith only [mul_nonneg up.le (sub_nonneg.mpr u1)]
    have ssmall : 2*s ≤ log (1+u) := by
      apply le_trans _ loglow
      nlinarith only [off,mul_le_mul_of_nonneg_left k4 sp.le]
    have s1 : s ≤ 1 := by nlinarith only [off,u1,mul_le_mul_of_nonneg_left k1 sp.le]
    let y := log x+s
    have rat : (L k:ℝ) ≤ k* (L (k-1):ℝ) := by exact_mod_cast lstep k (by omega)
    have ll := log_le_log lp rat
    rw [log_mul kp.ne' prev.ne'] at ll
    have lx := log_le_log (sqrt_pos.mpr prev) xl.le
    have ux := log_le_log xp xu
    rw [log_sqrt prev.le] at lx
    rw [log_sqrt lp.le] at ux
    have hy : |y-log (L k)/2|≤log k+1 := by
      dsimp only [y]
      rw [abs_le]
      constructor <;> linarith [log_nonneg k1]
    obtain ⟨d,hd,hnear⟩ := nearby y hy
    obtain ⟨hlo,hhi⟩ := abs_lt.mp hnear
    change -s < log d-y at hlo
    change log d-y < s at hhi
    dsimp only [y] at hlo hhi
    have dp : 0<(d:ℝ) := by exact_mod_cast (Nat.pos_of_mem_divisors hd)
    refine ⟨d,Nat.dvd_of_mem_divisors hd,(log_lt_log_iff xp dp).mp (by linarith),?_⟩
    apply (log_le_log_iff dp (mul_pos (by linarith : 0<1+u) xp)).mp
    rw [log_mul (by linarith : 1+u≠0) xp.ne']
    linarith
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventuallyGood
  let B := (range (K+1)).sup L
  let M := max 1 ((B:ℝ)*(K:ℝ)^β)
  have M1 : 1 ≤ M := le_max_left _ _
  refine ⟨M,zero_lt_one.trans_le M1,?_⟩
  intro k hk x xl xu
  have k1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1≤k by omega)
  have kp := zero_lt_one.trans_le k1
  have xp : 1≤x := by
    apply le_trans _ xl.le
    apply Real.one_le_sqrt.mpr
    exact_mod_cast lpos (k-1)
  have up := rpow_pos_of_pos kp (-β)
  by_cases kbig : K ≤ k
  · obtain ⟨d,hd,dx,du⟩ := hK k kbig x xl xu
    refine ⟨d,hd,dx,du.trans ?_⟩
    gcongr
    simpa using mul_le_mul_of_nonneg_right M1 up.le
  · have lbound : L k ≤ B := Finset.le_sup (f:=L) (mem_range.mpr (by omega : k<K+1))
    have kL : k ∣ L k := Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨by omega,le_rfl⟩)
    have strong : 1 < (L k:ℝ) := by exact_mod_cast (show 1<L k by have bound : k≤L k := Nat.le_of_dvd (lpos k) kL; omega)
    have dk : (B:ℝ) * (k:ℝ)^β ≤ M := (mul_le_mul_of_nonneg_left
      (rpow_le_rpow kp.le (by exact_mod_cast (show k≤K by omega)) hb.le) (Nat.cast_nonneg B)).trans (le_max_right _ _)
    have scale : (B:ℝ) ≤ M*(k:ℝ)^(-β) := by
      rw [rpow_neg kp.le,←div_eq_mul_inv]
      exact (le_div_iff₀ (rpow_pos_of_pos kp _)).mpr dk
    refine ⟨L k,dvd_rfl,xu.trans_lt (by nlinarith [Real.sq_sqrt (show 0≤(L k:ℝ) by positivity), mul_pos (sub_pos.mpr strong) (show 0<(L k:ℝ) by linarith)] : sqrt (L k)<(L k:ℝ)),?_⟩
    have lb : (L k:ℝ) ≤ B := by exact_mod_cast lbound
    apply le_trans (lb.trans scale)
    have nneg : 0 ≤ 1+M*(k:ℝ)^(-β) := by positivity
    linarith [mul_le_mul_of_nonneg_left xp nneg]

end OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1
end
section
/-! Tenenbaum, Sur un problème extrémal en arithmétique, section 4.
Primes above the square root contribute two-point factors to the Fourier
transform. A phase loss of order log k on each polynomial frequency range
suffices: beyond that range the Gaussian second moment controls the tail. -/
namespace OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1
open Real Filter Finset ProbabilityTheory MeasureTheory
open scoped Topology

private lemma gaussian_window (W : ℝ → ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    {D Z : ℝ} (hD : 0≤D) (hZ : 1≤Z) (wi : Integrable W (gaussianReal 0 1))
    (trivial : ∀ t, |W t| ≤ D) (small : ∀ t∈A, |t|≤2*Z → |W t| ≤ D/(2*Z)) :
    |∫ t in A, W t ∂(gaussianReal 0 1)| ≤ D/Z := by
  let μ := gaussianReal 0 1
  have zp : 0<Z := by linarith
  have si : Integrable (fun t : ℝ => t^2) μ :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  have se : (∫ t : ℝ, t^2 ∂μ)=1 := by
    have hv := variance_fun_id_gaussianReal (μ:=0) (v:=1)
    rw [variance_eq_integral measurable_id'.aemeasurable] at hv
    simpa [μ] using hv
  let f (t:ℝ) := D/(2*Z)*(1+t^2)
  have fi : Integrable f μ := ((integrable_const (1:ℝ)).add si).const_mul _
  have fm (t : ℝ) : 0≤f t := by dsimp [f]; positivity
  have fd (t : ℝ) (ht : t∈A) : |W t| ≤ f t := by
    by_cases hb : |t| ≤ 2*Z
    · exact (small t ht hb).trans (by dsimp [f]; nlinarith [mul_nonneg (show 0≤D/(2*Z) by positivity) (sq_nonneg t)])
    have hs : 2*Z ≤ t^2 := by
      have hg := (sq_le_sq₀ (by positivity : 0≤2*Z) (abs_nonneg t)).mpr (le_of_not_ge hb)
      rw [sq_abs] at hg
      nlinarith [mul_nonneg (sub_nonneg.mpr hZ) (by positivity : 0≤Z)]
    apply (trivial t).trans
    dsimp [f]
    rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]
    nlinarith only [hD,mul_le_mul_of_nonneg_left hs hD]
  calc
    |∫ t in A, W t ∂μ| ≤ ∫ t in A, |W t| ∂μ := by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ:=μ.restrict A) W)
    _ ≤ ∫ t in A, f t ∂μ := setIntegral_mono_on wi.abs.integrableOn fi.integrableOn hA fd
    _ ≤ ∫ t, f t ∂μ := setIntegral_le_integral fi (ae_of_all _ fm)
    _ = D/Z := by
      dsimp [f]
      rw [integral_const_mul,integral_add (integrable_const _) si,integral_const,se]
      simp [μ]
      <;> ring

-- The necessary prime-phase dispersion, only up to a fixed polynomial.
def H1 : Prop :=
  let loss := fun (k : ℕ) (s : ℝ) => ∑ p ∈ (Ioc k.sqrt k).filter Nat.Prime, (1-|cos (s*log p/2)|)
  ∀ M : ℕ, ∀ᶠ k : ℕ in atTop, ∀ s : ℝ, 1/(1+log k)^2 ≤ |s| →
    |s| ≤ (k:ℝ)^M → (M:ℝ)*log k ≤ loss k s

-- A pointwise finite estimate, independent of any distribution of primes.
def H2 : Prop :=
  let loss := fun (k : ℕ) (s : ℝ) => ∑ p ∈ (Ioc k.sqrt k).filter Nat.Prime, (1-|cos (s*log p/2)|)
  ∀ k : ℕ, 2≤k → ∀ s y : ℝ,
    |∑ d ∈ (Nat.lcmUpto k).divisors, cos (s*(log d-y))| ≤
      ((Nat.lcmUpto k).divisors.card:ℝ)*exp (-(loss k s))

theorem main : H1 → H2 → OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1.H2 := by
  intro hprime hdiv m
  let M := 2*m+8
  filter_upwards [hprime M,eventually_ge_atTop 2] with k hk hk2
  intro y _
  let x : ℝ := k
  let R := x^(m+2)
  let Z := R*x^2
  let D : ℝ := (Nat.lcmUpto k).divisors.card
  let W (t:ℝ) := ∑ d ∈ (Nat.lcmUpto k).divisors, cos ((R*(log d-y))*t)
  let A := (Set.Icc (-(1/(R*(1+log x)^2))) (1/(R*(1+log x)^2)))ᶜ
  have hx : 2≤x := by dsimp [x]; exact_mod_cast hk2
  have xp : 0<x := by linarith
  have hx1 : 1≤x := by linarith
  have rp : 0<R := pow_pos xp _
  have rz : 1≤R := one_le_pow₀ hx1
  have zp : 0<Z := by dsimp [Z]; positivity
  have hz : 1≤Z := one_le_mul_of_one_le_of_one_le rz (one_le_pow₀ hx1)
  have d0 : 0≤D := by dsimp [D]; positivity
  have wi : Integrable W (gaussianReal 0 1) := by
    apply integrable_finsetSum _ fun d _ => ?_
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards with t
    simpa [Real.norm_eq_abs] using abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  change |∫ t in A, W t ∂(gaussianReal 0 1)| ≤ D/Z
  apply gaussian_window W A measurableSet_Icc.compl d0 hz wi
  · intro t
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ d ∈ (Nat.lcmUpto k).divisors, (1:ℝ) := sum_le_sum fun d _ =>
        abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
      _ = D := by simp [D]
  · intro t ht hb
    have lp : 0<1+log x := by linarith [log_nonneg hx1]
    have outside : 1/(R*(1+log x)^2) < |t| := lt_of_not_ge fun h =>
      ht (abs_le.mp h)
    have a : 1/(1+log x)^2 ≤ |R*t| := by
      rw [abs_mul,abs_of_pos rp]
      calc
        _ = R*(1/(R*(1+log x)^2)) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left outside.le rp.le
    have ident : R*(2*Z)=2*x^(2*m+6) := by
      dsimp [Z,R]; ring
    have hB : R*(2*Z) ≤ x^M := by
      rw [ident,show M=2*m+6+2 by rfl,pow_add x (2*m+6) 2,mul_comm 2]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg xp.le _)
      nlinarith only [hx,sq_nonneg (x-2)]
    have b : |R*t| ≤ x^M := by rw [abs_mul,abs_of_pos rp]; exact (mul_le_mul_of_nonneg_left hb rp.le).trans hB
    have pp := hk (R*t) a b
    have fall := Real.exp_le_exp.mpr (neg_le_neg pp)
    have ei : exp (-((M:ℝ)*log x)) = 1/x^M := by
      rw [Real.exp_neg,←Real.log_pow,Real.exp_log (pow_pos xp _),one_div]
    rw [show log k=log x by rfl,ei] at fall
    have more : 2*Z ≤ x^M := by
      have := mul_le_mul_of_nonneg_right rz (by positivity : 0≤2*Z)
      simpa only [one_mul] using this.trans hB
    have hw := hdiv k hk2 (R*t) y
    change |W t|≤D/(2*Z)
    have we : |W t| = |∑ d ∈ (Nat.lcmUpto k).divisors, cos ((R*t)*(log d-y))| := by simp only [W,mul_right_comm R t]
    calc
      _ ≤ _ := we ▸ hw
      _ ≤ D*(1/x^M) := mul_le_mul_of_nonneg_left fall d0
      _ ≤ D*(1/(2*Z)) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) more) d0
      _ = _ := by ring

end OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1
end
section
/-!
The logarithms of the divisors form a partition symmetric about half the
logarithm of the integer. Cut the lower half at the logarithms of the
square roots of the earlier terms of the divisibility sequence. On each
piece, admissibility bounds the derivative of the gap cost by the
specified coefficient. Summing the piece lengths proves Tenenbaum's
Theorem 2 for power costs.
-/

-- Credit: @dk8827

open Finset Real
open scoped BigOperators

namespace OMA.DivisorGaps

private noncomputable def clip (a b x : ℝ) : ℝ := max a (min b x)

private theorem clip_mono (a b : ℝ) : Monotone (clip a b) :=
  fun _ _ h => max_le_max le_rfl (min_le_min le_rfl h)

private theorem clip_bounds {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ clip a b x ∧ clip a b x ≤ b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

private theorem clip_reflect {a b : ℝ} (hab : a ≤ b) (M x : ℝ) :
    clip (M - b) (M - a) (M - x) = M - clip a b x := by
  rcases le_or_gt x a with hxa | hax
  · have hxb : x ≤ b := hxa.trans hab
    have hax' : M - a ≤ M - x := sub_le_sub_left hxa _
    have hba' : M - b ≤ M - a := sub_le_sub_left hab _
    simp [clip, min_eq_right hxb, min_eq_left hax', max_eq_right hba', max_eq_left hxa]
  · rcases le_or_gt b x with hbx | hxb
    · have hxb' : M - x ≤ M - b := sub_le_sub_left hbx _
      have hxa' : M - x ≤ M - a := hxb'.trans (sub_le_sub_left hab _)
      simp [clip, min_eq_left hbx, min_eq_right hxa', max_eq_left hxb', max_eq_right hab]
    · have hxa' : M - x ≤ M - a := sub_le_sub_left hax.le _
      have hbx' : M - b ≤ M - x := sub_le_sub_left hxb.le _
      simp [clip, min_eq_right hxb.le, min_eq_right hxa', max_eq_right hbx',
        max_eq_right hax.le]

private theorem clip_hinge {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    clip a b x - a = max 0 (x - a) - max 0 (x - b) := by
  by_cases hxa : x ≤ a
  · have hxb := hxa.trans hab
    simp [clip, min_eq_right hxb, max_eq_left hxa, max_eq_left (sub_nonpos.2 hxa),
      max_eq_left (sub_nonpos.2 hxb)]
  · have hax : a < x := lt_of_not_ge hxa
    by_cases hxb : x ≤ b
    · simp [clip, min_eq_right hxb, max_eq_right hax.le, max_eq_right (sub_nonneg.2 hax.le),
        max_eq_left (sub_nonpos.2 hxb)]
    · have hbx := (lt_of_not_ge hxb).le
      rw [clip, min_eq_left hbx, max_eq_right hab, max_eq_right (sub_nonneg.2 hax.le),
        max_eq_right (sub_nonneg.2 hbx)]
      ring

private theorem sum_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, (f (i + 1) - f i)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

private theorem sum_clip {A : ℕ → ℝ} {m : ℕ} (hA : ∀ i < m, A i ≤ A (i + 1))
    {x y : ℝ} (hx : A 0 ≤ x) (hxm : x ≤ A m) (hy : A 0 ≤ y) (hym : y ≤ A m) :
    (∑ i ∈ range m, (clip (A i) (A (i + 1)) y - clip (A i) (A (i + 1)) x)) = y - x := by
  have key (u : ℝ) (hu : A 0 ≤ u) (hum : u ≤ A m) :
      (∑ i ∈ range m, (clip (A i) (A (i + 1)) u - A i)) = u - A 0 := by
    calc
      _ = ∑ i ∈ range m, (max 0 (u - A i) - max 0 (u - A (i + 1))) := by
        exact sum_congr rfl (fun i hi => clip_hinge (hA i (mem_range.1 hi)) u)
      _ = max 0 (u - A 0) - max 0 (u - A m) := by
        simpa only [neg_sub_neg] using (sum_differences (fun i => -(max 0 (u - A i))) m)
      _ = _ := by simp [max_eq_right (sub_nonneg.2 hu), max_eq_left (sub_nonpos.2 hum)]
  calc
    _ = (∑ i ∈ range m, (clip (A i) (A (i + 1)) y - A i)) -
          (∑ i ∈ range m, (clip (A i) (A (i + 1)) x - A i)) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl (fun i _ => by ring)
    _ = _ := by rw [key _ hy hym, key _ hx hxm]; ring

private noncomputable def score (α d : ℝ) : ℝ := (Real.exp d - 1) ^ α

private theorem score_superadditive {α x y : ℝ} (hα : 1 ≤ α) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    score α x + score α y ≤ score α (x + y) := by
  have ex : 0 ≤ Real.exp x - 1 := sub_nonneg.2 (Real.one_le_exp hx)
  have ey : 0 ≤ Real.exp y - 1 := sub_nonneg.2 (Real.one_le_exp hy)
  calc
    _ ≤ ((Real.exp x - 1) + (Real.exp y - 1)) ^ α := Real.add_rpow_le_rpow_add ex ey hα
    _ ≤ _ := Real.rpow_le_rpow (add_nonneg ex ey) (by
      rw [Real.exp_add]
      nlinarith only [mul_nonneg ex ey]) (by linarith)

private theorem reflected_gap {α a b M : ℝ} (hα : 1 ≤ α) (hab : a ≤ b) :
    score α (b - a) ≤
      (score α (b - a) - score α (b - clip a b (M / 2))) +
        (score α ((M - a) - (M - b)) -
          score α ((M - a) - clip (M - b) (M - a) (M / 2))) := by
  have hmid : M - M / 2 = M / 2 := by ring
  have he := clip_reflect hab M (M / 2)
  rw [hmid] at he
  rw [he]
  have he₁ : (M - a) - (M - b) = b - a := by ring
  have he₂ : (M - a) - (M - clip a b (M / 2)) = clip a b (M / 2) - a := by ring
  rw [he₁, he₂]
  have h := score_superadditive hα
    (sub_nonneg.2 (clip_bounds hab (M / 2)).2) (sub_nonneg.2 (clip_bounds hab (M / 2)).1)
  rw [show (b - clip a b (M / 2)) + (clip a b (M / 2) - a) = b - a by ring] at h
  linarith only [h]

private theorem shell_bound {α a b u v ε : ℝ}
    (hα : 1 < α) (hab : a ≤ b) (huv : u ≤ v) (hε : 0 < ε)
    (hclose : ∀ x : ℝ, u < x → x < v → a < x → x < b → Real.exp (b - x) ≤ 1 + ε) :
    score α (b - clip a b u) - score α (b - clip a b v) ≤
      (1 + ε) * (α * ε ^ (α - 1)) * (clip a b v - clip a b u) := by
  let x := clip a b u
  let y := clip a b v
  have hxy : x ≤ y := clip_mono a b huv
  rcases eq_or_lt_of_le hxy with h | h
  · simp [show clip a b u = clip a b v from h]
  have hxu : u ≤ x := by
    have hub : u ≤ b := by
      by_contra! hub
      have he : x = b := by simp [x, clip, min_eq_left hub.le, max_eq_right hab]
      have hyb : y ≤ b := (clip_bounds hab v).2
      rw [← he] at hyb
      exact (not_lt_of_ge hyb) h
    exact (min_eq_right hub ▸ le_max_right a (min b u))
  have hyv : y ≤ v := by
    apply max_le _ (min_le_right _ _)
    by_contra! hva
    have he : y = a := by
      have : min b v ≤ a := (min_le_right _ _).trans hva.le
      simp [y, clip, max_eq_left this]
    have hax : a ≤ x := (clip_bounds hab u).1
    rw [← he] at hax
    exact (not_lt_of_ge hax) h
  let f (t : ℝ) := score α (b - t)
  let f' (t : ℝ) := -Real.exp (b - t) * (α * (Real.exp (b - t) - 1) ^ (α - 1))
  have hbase : Differentiable ℝ (fun t : ℝ => Real.exp (b - t) - 1) := by fun_prop
  have hf : ContinuousOn f (Set.Icc x y) :=
    (hbase.rpow_const (fun _ => Or.inr hα.le)).continuous.continuousOn
  have hf' (t : ℝ) (_ : t ∈ Set.Ioo x y) : HasDerivAt f (f' t) t := by
    have hlin := (hasDerivAt_const t b).sub (hasDerivAt_id t)
    have hexp := ((Real.hasDerivAt_exp (b - t)).comp t hlin).sub_const 1
    have hd := (Real.hasDerivAt_rpow_const (p := α)
      (x := Real.exp (b - t) - 1) (Or.inr hα.le)).comp t hexp
    convert hd using 1 <;> first
    | rfl
    | simp [f', mul_comm, mul_left_comm]
  obtain ⟨t, ht, hderiv⟩ := exists_hasDerivAt_eq_slope f f' h hf hf'
  have hnear : Real.exp (b - t) ≤ 1 + ε :=
    hclose t (hxu.trans_lt ht.1) (ht.2.trans_le hyv)
      ((clip_bounds hab u).1.trans_lt ht.1) (ht.2.trans_le (clip_bounds hab v).2)
  have hnonneg : 0 ≤ Real.exp (b - t) - 1 :=
    sub_nonneg.2 (Real.one_le_exp (sub_nonneg.2 (ht.2.trans_le (clip_bounds hab v).2).le))
  have hpow : (Real.exp (b - t) - 1) ^ (α - 1) ≤ ε ^ (α - 1) :=
    Real.rpow_le_rpow hnonneg (by linarith only [hnear]) (by linarith)
  have hmul : Real.exp (b - t) * (α * (Real.exp (b - t) - 1) ^ (α - 1)) ≤
      (1 + ε) * (α * ε ^ (α - 1)) := by
    have hα0 : 0 < α := by linarith
    apply mul_le_mul hnear (mul_le_mul_of_nonneg_left hpow hα0.le)
      (mul_nonneg hα0.le (Real.rpow_nonneg hnonneg _))
      (by linarith)
  have hfv := (eq_div_iff (sub_pos.2 h).ne').1 hderiv
  change _ ≤ _ * (y - x)
  have hstep := mul_le_mul_of_nonneg_right hmul (sub_nonneg.2 h.le)
  dsimp only [f', f] at hfv
  linarith only [hfv, hstep]


theorem partition_bound (α : ℝ) (hα : 1 < α)
    (A S : ℕ → ℝ) (m r : ℕ) (ε : ℕ → ℝ)
    (hA : MonotoneOn A (Set.Iic m)) (hA0 : A 0 = 0)
    (hR : ∀ i ≤ m, A (m - i) = A m - A i)
    (hs : Monotone S) (hs0 : S 0 = 0) (hsr : S r = A m / 2)
    (hε : ∀ j < r, 0 < ε j)
    (hclose : ∀ i < m, ∀ j < r, ∀ x : ℝ,
      S j < x → x < S (j + 1) → A i < x → x < A (i + 1) →
      Real.exp (A (i + 1) - x) ≤ 1 + ε j) :
    (∑ i ∈ range m, score α (A (i + 1) - A i)) ≤
      2 * ∑ j ∈ range r, (1 + ε j) * (α * (ε j) ^ (α - 1)) * (S (j + 1) - S j) := by
  let H (i : ℕ) := score α (A (i + 1) - A i)
  let G (i : ℕ) := H i - score α (A (i + 1) - clip (A i) (A (i + 1)) (A m / 2))
  have hA' (i : ℕ) (hi : i < m) : A i ≤ A (i + 1) :=
    hA (by exact hi.le) (by exact hi) (Nat.le_succ _)
  have hmid (i : ℕ) (hi : i < m) : H i ≤ G i + G (m - 1 - i) := by
    have hlo : A (m - 1 - i) = A m - A (i + 1) := by
      rw [show m - 1 - i = m - (i + 1) by omega]
      exact hR _ (by omega)
    have hhi : A (m - 1 - i + 1) = A m - A i := by
      rw [show m - 1 - i + 1 = m - i by omega]
      exact hR i hi.le
    dsimp only [H, G]
    rw [hlo, hhi]
    exact reflected_gap hα.le (hA' i hi)
  have hsymmetric : (∑ i ∈ range m, H i) ≤ 2 * ∑ i ∈ range m, G i := by
    calc
      _ ≤ ∑ i ∈ range m, (G i + G (m - 1 - i)) :=
        sum_le_sum (fun i hi => hmid i (mem_range.1 hi))
      _ = _ := by rw [sum_add_distrib, sum_range_reflect G m, two_mul]
  let C (i j : ℕ) := clip (A i) (A (i + 1)) (S j)
  let L (i j : ℕ) := score α (A (i + 1) - C i j)
  let K (j : ℕ) := (1 + ε j) * (α * (ε j) ^ (α - 1))
  have hsplit (i : ℕ) (hi : i < m) :
      G i = ∑ j ∈ range r, (L i j - L i (j + 1)) := by
    have h := sum_differences (fun j => -(L i j)) r
    simp only [neg_sub_neg] at h
    have hleft : C i 0 = A i := by
      have hAi : 0 ≤ A i := by
        rw [← hA0]
        exact hA (by exact Nat.zero_le _) (by exact hi.le) (Nat.zero_le _)
      have hBi := hAi.trans (hA' i hi)
      simp [C, clip, hs0, min_eq_right hBi, max_eq_left hAi]
    have hright : C i r = clip (A i) (A (i + 1)) (A m / 2) := by simp [C, hsr]
    simpa only [G, L, H, hleft, hright] using h.symm
  have hterm (i : ℕ) (hi : i < m) (j : ℕ) (hj : j < r) :
      L i j - L i (j + 1) ≤ K j * (C i (j + 1) - C i j) :=
    shell_bound hα (hA' i hi) (hs (Nat.le_succ _)) (hε j hj) (hclose i hi j hj)
  have hC (j : ℕ) (hj : j < r) :
      (∑ i ∈ range m, (C i (j + 1) - C i j)) = S (j + 1) - S j := by
    have hAm : 0 ≤ A m := by rw [← hA0]; exact hA (by exact Nat.zero_le _) (by exact Nat.le_refl _) (Nat.zero_le _)
    have upper (k : ℕ) (hk : k ≤ r) : S k ≤ A m := by
      have h := hs hk
      rw [hsr] at h
      linarith only [h, hAm]
    have lower (k : ℕ) : A 0 ≤ S k := by
      rw [hA0, ← hs0]
      exact hs (Nat.zero_le _)
    exact sum_clip hA' (lower j) (upper j hj.le) (lower _) (upper _ hj)
  apply hsymmetric.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (∑ i ∈ range m, G i) = ∑ i ∈ range m, ∑ j ∈ range r, (L i j - L i (j + 1)) :=
      sum_congr rfl (fun i hi => hsplit i (mem_range.1 hi))
    _ ≤ ∑ i ∈ range m, ∑ j ∈ range r, K j * (C i (j + 1) - C i j) :=
      sum_le_sum (fun i hi => sum_le_sum (fun j hj => hterm i (mem_range.1 hi) j (mem_range.1 hj)))
    _ = ∑ j ∈ range r, ∑ i ∈ range m, K j * (C i (j + 1) - C i j) := Finset.sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [← mul_sum, hC j (mem_range.1 hj)]

private theorem sorted_divisors (M : ℕ) :
    M.divisorsAntidiagonalList.map Prod.fst = M.divisors.sort := by
  apply Nat.sortedLT_map_fst_divisorsAntidiagonalList.eq_of_mem_iff (sortedLT_sort _)
  intro d
  simp only [List.mem_map, mem_sort, Nat.mem_divisorsAntidiagonalList, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨he, hM⟩, rfl⟩
    exact ⟨⟨b, he.symm⟩, hM⟩
  · rintro ⟨hD, hM⟩
    obtain ⟨q, hq⟩ := hD
    exact ⟨(d, q), ⟨hq.symm, hM⟩, rfl⟩

private theorem divisor_finite {M : ℕ} (hM : M ≠ 0) :
    (Set.ofPred (fun k : ℕ => k ∣ M)).Finite :=
  M.divisors.finite_toSet.subset (fun _ h => Nat.mem_divisors.2 ⟨h, hM⟩)

private theorem divisors_toFinset {M : ℕ} (hM : M ≠ 0) :
    (divisor_finite hM).toFinset = M.divisors := by
  ext x
  simp [Nat.mem_divisors, hM]

private theorem reciprocal_nth {M i : ℕ} (hM : M ≠ 0) (hi : i < M.divisors.card) :
    Nat.nth (· ∣ M) (M.divisors.card - 1 - i) * Nat.nth (· ∣ M) i = M := by
  let L := M.divisorsAntidiagonalList
  have hsort : L.map Prod.fst = M.divisors.sort := sorted_divisors M
  have hlen : L.length = M.divisors.card := by
    simpa using congrArg List.length hsort
  have hiL : i < L.length := by rwa [hlen]
  have hrev : i < L.reverse.length := by simpa using hiL
  have hit (j : ℕ) (hj : j < L.length) : Nat.nth (· ∣ M) j = L[j].1 := by
    rw [Nat.nth_eq_getD_sort (divisor_finite hM), divisors_toFinset hM, ← hsort]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  have himap : i < (L.map Prod.swap).length := by simpa using hiL
  have hflip : L[L.length - 1 - i] = L[i].swap := by
    calc
      _ = L.reverse[i] := (List.getElem_reverse hrev).symm
      _ = (L.map Prod.swap)[i] :=
        List.getElem_of_eq (Nat.reverse_divisorsAntidiagonalList M) hrev
      _ = _ := by rw [List.getElem_map]
  have hprod : L[i].1 * L[i].2 = M :=
    (Nat.mem_divisorsAntidiagonalList.1 (List.getElem_mem hiL)).1
  rw [← hlen, hit i hiL, hit (L.length - 1 - i) (by omega)]
  exact (by rw [hflip]; simpa [mul_comm] using hprod)

end OMA.DivisorGaps

set_option maxHeartbeats 1000000 in
theorem OMA.divisor_summation : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1.H2 := by
  classical
  intro α hα N ε hN0 hN1 hNpos hdiv hε hadm n
  by_cases hn0 : n = 0
  · subst n
    rw [hN0]
    unfold Erdos1099.h
    rw [Nat.divisors_one, Finset.card_singleton, Nat.sub_self, Fin.sum_univ_zero]
    simp
  have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
  let M := N n
  have hM : M ≠ 0 := (hNpos n).ne'
  let m := M.divisors.card - 1
  let d : ℕ → ℕ := Nat.nth (· ∣ M)
  let A (i : ℕ) := Real.log (d i : ℝ)
  let hf := OMA.DivisorGaps.divisor_finite hM
  have hfin : hf.toFinset = M.divisors := OMA.DivisorGaps.divisors_toFinset hM
  have hcard : 0 < M.divisors.card :=
    card_pos.2 ⟨1, Nat.mem_divisors.2 ⟨one_dvd M, hM⟩⟩
  have hidx (i : ℕ) (hi : i ≤ m) : i < hf.toFinset.card := by
    rw [hfin]
    dsimp only [m] at hi
    omega
  have hdvd (i : ℕ) (hi : i ≤ m) : d i ∣ M := Nat.nth_mem_of_lt_card hf (hidx i hi)
  have hdpos (i : ℕ) (hi : i ≤ m) : (0 : ℝ) < d i := by
    exact_mod_cast Nat.pos_of_mem_divisors (Nat.mem_divisors.2 ⟨hdvd i hi, hM⟩)
  have dmono (i j : ℕ) (hij : i ≤ j) (hj : j ≤ m) : d i ≤ d j :=
    Nat.nth_le_nth_of_lt_card hf hij (hidx j hj)
  have hd0 : d 0 = 1 := by
    refine le_antisymm ?_ (by exact_mod_cast hdpos 0 (Nat.zero_le _))
    exact (Nat.isLeast_nth_of_lt_card hf (hidx 0 (Nat.zero_le _))).2
      ⟨one_dvd M, fun k hk => (Nat.not_lt_zero _ hk).elim⟩
  have hdm : d m = M := by
    refine le_antisymm (Nat.le_of_dvd (hNpos n) (hdvd m le_rfl)) ?_
    obtain ⟨i, hi, he⟩ := Nat.exists_lt_card_finite_nth_eq hf (dvd_refl M)
    rw [hfin] at hi
    have him : i ≤ m := by dsimp only [m]; omega
    have hm := dmono i m him le_rfl
    change d i = M at he
    rwa [he] at hm
  have hA : MonotoneOn A (Set.Iic m) := by
    intro i hi j hj hij
    exact Real.log_le_log (hdpos i hi) (by exact_mod_cast dmono i j hij hj)
  have hA0 : A 0 = 0 := by simp [A, hd0]
  have hAm : A m = Real.log (M : ℝ) := by simp [A, hdm]
  have hR (i : ℕ) (hi : i ≤ m) : A (m - i) = A m - A i := by
    have hi' : i < M.divisors.card := by
      have := hidx i hi
      rwa [hfin] at this
    have he : d (m - i) * d i = M := OMA.DivisorGaps.reciprocal_nth hM hi'
    have hcast : (d (m - i) : ℝ) * (d i : ℝ) = (M : ℝ) := by exact_mod_cast he
    have hlog := congrArg Real.log hcast
    rw [Real.log_mul (hdpos _ (Nat.sub_le _ _)).ne' (hdpos _ hi).ne'] at hlog
    change A (m - i) + A i = Real.log (M : ℝ) at hlog
    linarith only [hlog, hAm]
  have hDvd (i j : ℕ) (hij : i ≤ j) : N i ∣ N j := by
    induction hij with
    | refl => exact dvd_refl _
    | step _ ih => exact ih.trans (hdiv _)
  have hNmono : Monotone N := fun i j hij => Nat.le_of_dvd (hNpos j) (hDvd i j hij)
  let S (j : ℕ) := Real.log (N (j + 1) : ℝ) / 2
  let r := n - 1
  have hs : Monotone S := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    exact Real.log_le_log (by exact_mod_cast hNpos (i + 1))
      (by exact_mod_cast hNmono (Nat.add_le_add_right hij 1))
  have hs0 : S 0 = 0 := by simp [S, hN1]
  have hsr : S r = A m / 2 := by
    change Real.log (N (n - 1 + 1) : ℝ) / 2 = _
    rw [Nat.sub_add_cancel hn, hAm]
  have es (j : ℕ) : Real.exp (S j) = √((N (j + 1) : ℕ) : ℝ) := by
    have hpositive : 0 < √((N (j + 1) : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hNpos (j + 1))
    rw [show S j = Real.log (√((N (j + 1) : ℕ) : ℝ)) by
      rw [Real.log_sqrt (by positivity)], Real.exp_log hpositive]
  have eA (i : ℕ) (hi : i ≤ m) : Real.exp (A i) = (d i : ℝ) :=
    Real.exp_log (hdpos i hi)
  have hclose : ∀ i < m, ∀ j < r, ∀ x : ℝ,
      S j < x → x < S (j + 1) → A i < x → x < A (i + 1) →
      Real.exp (A (i + 1) - x) ≤ 1 + ε (j + 2) := by
    intro i hi j hj x hjs hxj hix _hx
    have hjn : j + 2 ≤ n := by dsimp only [r] at hj; omega
    have hjpred : j + 2 - 1 = j + 1 := by omega
    have hleft : √((N (j + 2 - 1) : ℕ) : ℝ) < Real.exp x := by
      rw [hjpred, ← es j]
      exact Real.exp_lt_exp.2 hjs
    have hright : Real.exp x ≤ √((N (j + 2) : ℕ) : ℝ) := by
      rw [← es (j + 1)]
      exact (Real.exp_lt_exp.2 hxj).le
    obtain ⟨b, hb, hxb, hub⟩ := hadm (j + 2) (by omega) (Real.exp x) hleft hright
    have hbM : b ∣ M := hb.trans (hDvd _ _ hjn)
    have hdb : d i < b := by
      have ht := Real.exp_lt_exp.2 hix
      rw [eA i hi.le] at ht
      exact_mod_cast ht.trans hxb
    have hnext : d (i + 1) ≤ b :=
      (Nat.isLeast_nth_of_lt_card hf (hidx _ hi)).2
        ⟨hbM, fun k hk => (dmono k i (by omega) hi.le).trans_lt hdb⟩
    rw [Real.exp_sub, eA _ hi]
    apply (div_le_iff₀ (Real.exp_pos x)).2
    exact (show (d (i + 1) : ℝ) ≤ (b : ℝ) by exact_mod_cast hnext).trans hub
  let W (k : ℕ) := (1 + ε k) * (α * (ε k) ^ (α - 1))
  have hscore (i : ℕ) (hi : i < m) :
      OMA.DivisorGaps.score α (A (i + 1) - A i) =
        ((d (i + 1) : ℝ) / (d i : ℝ) - 1) ^ α := by
    unfold OMA.DivisorGaps.score
    rw [Real.exp_sub, eA _ hi, eA _ hi.le]
  have hpart := OMA.DivisorGaps.partition_bound α hα A S m r (fun j => ε (j + 2))
    hA hA0 hR hs hs0 hsr (fun j _ => hε (j + 2) (by omega)) hclose
  calc
    Erdos1099.h α (N n) = ∑ i ∈ range m, OMA.DivisorGaps.score α (A (i + 1) - A i) := by
      change (∑ i : Fin m, ((d ((i : ℕ) + 1) : ℝ) / (d i : ℝ) - 1) ^ α) = _
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((d (i + 1) : ℝ) / (d i : ℝ) - 1) ^ α)]
      apply sum_congr rfl
      intro i hi
      exact (hscore i (mem_range.1 hi)).symm
    _ ≤ 2 * ∑ j ∈ range r, W (j + 2) * (S (j + 1) - S j) := hpart
    _ = ∑ k ∈ Icc 2 n, W k * Real.log ((N k : ℝ) / (N (k - 1) : ℝ)) := by
      have hI : Icc 2 n = Ico 2 (r + 2) := by
        ext k
        simp only [mem_Icc, mem_Ico]
        dsimp only [r]
        omega
      rw [hI, ← Finset.sum_Ico_add' (fun k => W k * Real.log ((N k : ℝ) / (N (k - 1) : ℝ))) 0 r
        (c := 2), Nat.Ico_zero_eq_range, mul_sum]
      apply sum_congr rfl
      intro j _
      rw [Real.log_div (by exact_mod_cast (hNpos (j + 2)).ne')
        (by exact_mod_cast (hNpos (j + 2 - 1)).ne')]
      have hj : j + 2 - 1 = j + 1 := by omega
      rw [hj]
      dsimp only [S]
      ring
end
section
/-! The small-frequency divisor sum for lcm(1,...,k). The centered sum
factors over prime powers. Every local factor is real and nonnegative on
the central arc. A shorter interval around zero supplies its mass. -/
open Real Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace OMA.MajorArc1099

private noncomputable def ph (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)
private lemma ph_add (x y : ℝ) : ph (x+y)=ph x*ph y := by
  simp only [ph,Complex.ofReal_add,add_mul,Complex.exp_add]
private noncomputable def chi (s : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n=0 then 0 else ph (s*log n),by simp⟩
private lemma chi_apply {n : ℕ} (hn : n≠0) (s : ℝ) : chi s n = ph (s*log n) :=
  if_neg hn
private lemma chi_mult (s : ℝ) : (chi s).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [chi_apply,ph],?_⟩
  intro a b ha hb _
  rw [chi_apply (Nat.mul_ne_zero ha hb),chi_apply ha,chi_apply hb,Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb),mul_add,ph_add]

private lemma log_other {n d : ℕ} (hd : d∈n.divisors) :
    log (n/d:ℕ) = log n - log d := by
  obtain ⟨hv,hn⟩ := Nat.mem_divisors.mp hd
  have dp : 0<d := Nat.pos_of_dvd_of_pos hv (Nat.pos_of_ne_zero hn)
  rw [Nat.cast_div hv (Nat.cast_ne_zero.mpr dp.ne'), Real.log_div (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr dp.ne')]

private lemma sine_zero (n : ℕ) (s : ℝ) :
    (∑ d ∈ n.divisors, sin (s*(log d-log n/2)))=0 := by
  let f (d:ℕ) := sin (s*(log d-log n/2))
  have h := Nat.sum_div_divisors n f
  have e : (∑ d ∈ n.divisors, f (n/d)) = -(∑ d ∈ n.divisors, f d) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun d hd => ?_
    dsimp [f]
    rw [log_other hd, ← Real.sin_neg]
    congr 1
    ring
  change (∑ d ∈ n.divisors, f d)=0
  linarith

private noncomputable def centered (s : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, cos (s*(log d-log n/2))

private lemma center_eval (s : ℝ) (n : ℕ) :
    (chi (s/2)*chi (-s/2)) n = (centered s n : ℂ) := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => chi (s/2) a * chi (-s/2) b)]
  have e (d : ℕ) (hd : d∈n.divisors) :
      chi (s/2) d * chi (-s/2) (n/d) = ph (s*(log d-log n/2)) := by
    obtain ⟨dv,hn⟩ := Nat.mem_divisors.mp hd
    have np := Nat.pos_of_ne_zero hn
    have dp := Nat.pos_of_dvd_of_pos dv np
    have dq := Nat.div_pos (Nat.le_of_dvd np dv) dp
    rw [chi_apply dp.ne',chi_apply dq.ne',←ph_add,log_other hd]
    congr 1
    ring
  rw [sum_congr rfl e]
  apply Complex.ext
  · simp only [Complex.re_sum,ph,centered,Complex.exp_ofReal_mul_I_re,Complex.ofReal_re]
  · simpa only [Complex.im_sum,ph,Complex.exp_ofReal_mul_I_im,Complex.ofReal_im] using sine_zero n s

private lemma center_prod (s : ℝ) {n : ℕ} (hn : n≠0) :
    centered s n = ∏ p ∈ n.primeFactors, centered s (p^n.factorization p) := by
  let F := chi (s/2)*chi (-s/2)
  have mt : F.IsMultiplicative := (chi_mult _).mul (chi_mult _)
  have h := mt.multiplicative_factorization F hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  change (chi (s/2)*chi (-s/2)) n = ∏ p ∈ n.primeFactors, (chi (s/2)*chi (-s/2)) (p^n.factorization p) at h
  simp_rw [center_eval] at h
  exact_mod_cast h

private lemma cos_half {x : ℝ} (h : |x| ≤ 1) : 1/2 ≤ cos x := by
  have hab := abs_le.mp h
  nlinarith only [Real.one_sub_sq_div_two_le_cos (x:=x),mul_nonneg (by linarith only [hab.1] : 0≤1+x) (by linarith only [hab.2] : 0≤1-x)]

private lemma center_pos {k : ℕ} (hk : 1≤k) {s : ℝ} (hs : |s| *(1+log k) ≤ 1) :
    0 ≤ centered s (Nat.lcmUpto k) := by
  rw [center_prod s (Nat.lcmUpto_ne_zero k)]
  apply prod_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  let v := (Nat.lcmUpto k).factorization p
  have hv : p^v ≤ k := by
    dsimp [v]
    rw [Nat.factorization_lcmUpto k hprime]
    exact Nat.pow_log_le_self _ (by omega)
  apply sum_nonneg
  intro d hd
  have hpd : 0<d := Nat.pos_of_mem_divisors hd
  have hpk : 0<p^v := pow_pos hprime.pos _
  have dl : d≤p^v := Nat.le_of_dvd hpk (Nat.mem_divisors.mp hd).1
  have l1 := log_le_log (by exact_mod_cast hpd) (by exact_mod_cast dl : (d:ℝ) ≤ (p^v:ℕ))
  have l2 := log_le_log (by exact_mod_cast hpk) (by exact_mod_cast hv : (p^v:ℕ) ≤ (k:ℝ))
  have bound : |log d-log (p^v:ℕ)/2| ≤ 1+log k :=
    abs_le.mpr ⟨by linarith [log_natCast_nonneg d, log_natCast_nonneg k],by linarith [log_natCast_nonneg (p^v)]⟩
  exact (by norm_num : (0:ℝ)≤1/2).trans (cos_half (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left bound (abs_nonneg s)).trans hs))

private lemma wave_pos {k : ℕ} (hk : 1≤k) (s y : ℝ)
    (hs : |s| *(1+log k)≤1) (hy : |y-log (Nat.lcmUpto k)/2| ≤ log k+1) :
    0 ≤ ∑ d ∈ (Nat.lcmUpto k).divisors, cos (s*(log d-y)) := by
  let L := Nat.lcmUpto k
  let a := s*(log L/2-y)
  have ha : |a|≤1 := by
    rw [show |a|=|s| *|y-log L/2| by dsimp [a]; rw [abs_mul,abs_sub_comm]]
    exact (mul_le_mul_of_nonneg_left (by linarith only [hy] : |y-log L/2|≤1+log k) (abs_nonneg s)).trans hs
  have e : (∑ d ∈ L.divisors, cos (s*(log d-y))) = centered s L*cos a := by
    have h (d:ℕ) : s*(log d-y)=s*(log d-log L/2)+a := by dsimp [a]; ring
    simp_rw [h, Real.cos_add]
    rw [sum_sub_distrib,← sum_mul,← sum_mul,sine_zero]
    simp [centered]
  rw [e]
  exact mul_nonneg (center_pos hk hs) ((by norm_num : (0:ℝ)≤1/2).trans (cos_half ha))

private lemma mass {h : ℝ} (hp : 0<h) (hh : h≤1) :
    gaussianPDFReal 0 1 1*(2*h) ≤ (gaussianReal 0 1).real (Set.Icc (-h) h) := by
  rw [measureReal_def,gaussianReal_apply_eq_integral _ (v:=1) (by norm_num),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc (fun x _ => gaussianPDFReal_nonneg _ _ _))]
  have hl (x : ℝ) (hx : x∈Set.Icc (-h) h) : gaussianPDFReal 0 1 1 ≤ gaussianPDFReal 0 1 x := by
    have xl := hx.1
    have xu := hx.2
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,one_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0≤1+x by linarith) (show 0≤1-x by linarith)]
  have h0 := setIntegral_ge_of_const_le_real (μ:=volume) measurableSet_Icc
    (isCompact_Icc.measure_lt_top.ne) hl (integrable_gaussianPDFReal 0 1).integrableOn
  rwa [Real.volume_real_Icc_of_le (by linarith : -h≤h),show h-(-h)=2*h by ring] at h0

private lemma scale {k : ℕ} (hk : 1≤k) : (1+log k)^2 ≤ 16*(k:ℝ) := by
  have hp : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have ls := Real.log_le_sub_one_of_pos (sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at ls
  have h := sq_le_sq₀ (by linarith [log_natCast_nonneg k] : 0≤1+log k)
    (by positivity : 0≤2*sqrt (k:ℝ))
  have hs := h.mpr (by linarith)
  nlinarith [Real.sq_sqrt hp.le]

private lemma major (k : ℕ) (hk : 1≤k) (R y : ℝ) (hR : 1≤R)
    (hy : |y-log (Nat.lcmUpto k)/2| ≤ log k+1)
    (hK : 32≤gaussianPDFReal 0 1 1*(k:ℝ)) :
    2*((Nat.lcmUpto k).divisors.card:ℝ)/(R*(k:ℝ)^2) ≤
    ∫ t in Set.Icc (-(1/(R*(1+log k)^2))) (1/(R*(1+log k)^2)),
      (∑ d ∈ (Nat.lcmUpto k).divisors, cos ((R*(log d-y))*t)) ∂(gaussianReal 0 1) := by
  let x : ℝ := k
  let L := Nat.lcmUpto k
  let D : ℝ := L.divisors.card
  let h := 1/(16*R*x)
  let B := 1/(R*(1+log k)^2)
  let W (t:ℝ) := ∑ d ∈ L.divisors, cos ((R*(log d-y))*t)
  let μ := gaussianReal 0 1
  have hx : 1≤x := by dsimp [x]; exact_mod_cast hk
  have xp : 0<x := by linarith
  have rp : 0<R := by linarith
  have lh := log_natCast_nonneg k
  have lp : 0<1+log k := by linarith
  have hp : 0<h := by dsimp [h]; positivity
  have hsmall : h≤1 := by
    dsimp [h]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul hR hx (by norm_num : (0:ℝ)≤1) rp.le]
  have hB : h≤B := by
    dsimp [h,B]
    apply one_div_le_one_div_of_le (by positivity)
    have hs := mul_le_mul_of_nonneg_left (scale hk) rp.le
    change _ ≤ 16*R*x
    nlinarith only [hs]
  have intW : Integrable W μ := by
    apply integrable_finsetSum _ fun d _ => ?_
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards with t
    simpa [Real.norm_eq_abs] using abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have wpos (t : ℝ) (ht : t∈Set.Icc (-B) B) : 0≤W t := by
    have atb := abs_le.mpr ht
    have sB : B*(R*(1+log k)^2)=1 := by dsimp [B]; field_simp
    have he := mul_le_mul_of_nonneg_right atb (show 0≤R*(1+log k)^2 by positivity)
    have hi : |R*t| *(1+log k)≤1 := by
      rw [abs_mul, abs_of_pos rp]
      have hz : 1+log k ≤ (1+log k)^2 := by nlinarith [sq_nonneg (log (k:ℝ))]
      have hz' := mul_le_mul_of_nonneg_left hz (mul_nonneg rp.le (abs_nonneg t))
      nlinarith only [he,sB,hz']
    have e := wave_pos hk (R*t) y hi hy
    simpa only [W,L,mul_right_comm R t] using e
  have near (t : ℝ) (ht : t∈Set.Icc (-h) h) : D/2≤W t := by
    have hL : log L ≤ 7*x := by
      rw [show log L=Chebyshev.psi k from (Chebyshev.psi_eq_log_lcmUpto k).symm]
      have h := Chebyshev.psi_le_const_mul_self (x:=x) xp.le
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]) xp.le)
    have hLy := abs_le.mp hy
    have lk := Real.log_le_sub_one_of_pos xp
    have ww (d : ℕ) (hd : d∈L.divisors) : 1/2≤cos ((R*(log d-y))*t) := by
      have dpos := Nat.pos_of_mem_divisors hd
      have ldl := log_le_log (by exact_mod_cast dpos : (0:ℝ)<d)
        (by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos k) (Nat.dvd_of_mem_divisors hd) : (d:ℝ) ≤ L)
      have hy' : |log d-y|≤16*x := by
        have hy1 : -(log x+1) ≤ y-log L/2 := hLy.1
        have hy2 : y-log L/2 ≤ log x+1 := hLy.2
        exact abs_le.mpr ⟨by linarith [hy2,log_natCast_nonneg d],by linarith [hy1,log_natCast_nonneg L]⟩
      apply cos_half
      rw [abs_mul,abs_mul,abs_of_pos rp]
      calc
        _ ≤ (R*(16*x))*h := mul_le_mul (mul_le_mul_of_nonneg_left hy' rp.le) (abs_le.mpr ht) (abs_nonneg t) (by positivity)
        _ = 1 := by dsimp [h]; field_simp <;> ring
    calc
      D/2 = ∑ _d ∈ L.divisors, (1/2:ℝ) := by simp [D]; ring
      _ ≤ W t := sum_le_sum ww
  let Y := Set.Icc (-h) h
  let Z := Set.Icc (-B) B
  have hm := mass hp hsmall
  change gaussianPDFReal 0 1 1*(2*h) ≤ μ.real Y at hm
  have nonD : 0≤D := by dsimp [D]; positivity
  change 2*D/(R*x^2) ≤ ∫ t in Z, W t ∂μ
  calc
    _ ≤ D/2*(gaussianPDFReal 0 1 1*(2*h)) := by
      dsimp [h]
      field_simp
      nlinarith only [mul_nonneg nonD (sub_nonneg.mpr hK)]
    _ ≤ D/2*μ.real Y := mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ ∫ t in Y, W t ∂μ := setIntegral_ge_of_const_le_real measurableSet_Icc
      (measure_ne_top _ _) near intW.integrableOn
    _ ≤ ∫ t in Z, W t ∂μ := setIntegral_mono_set intW.integrableOn
      ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ wpos))
      ((Set.Icc_subset_Icc (neg_le_neg hB) hB).eventuallyLE)

end OMA.MajorArc1099

theorem OMA.central_mass : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1.H1 := by
  intro m
  have hC := gaussianPDFReal_pos 0 1 1 (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_gt (32/gaussianPDFReal 0 1 1)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 1] with k hk hk1
  intro y hy
  apply OMA.MajorArc1099.major k hk1 _ y (one_le_pow₀ (by exact_mod_cast hk1)) hy
  have h := (div_lt_iff₀ hC).mp (hK.trans_le (by exact_mod_cast hk : (K:ℝ)≤k))
  linarith
end
section
/-! Angular concentration for a large set of primes would give too many distinct
products of fixed length in the short intervals where the logarithmic phases
are close to multiples of two pi. The binomial lower bound is adapted from
OpenAI, TotientFibers/FiniteFiber.lean at adc7f1241b42e322a6451854ab7e4b4c146bf78a
(Apache-2.0). -/
open Finset Filter Real
open scoped Classical Topology

namespace LogPrimePacking

lemma log_separation {a n : ℕ} (ha : 0<a) (han : a≤n) :
    (n:ℝ)-(a:ℝ) ≤ (n:ℝ)*(log (n:ℝ)-log (a:ℝ)) := by
  have ap : (0:ℝ)<a := by exact_mod_cast ha
  have np : (0:ℝ)<n := by exact_mod_cast ha.trans_le han
  have h := Real.log_le_sub_one_of_pos (div_pos ap np)
  rw [Real.log_div ap.ne' np.ne'] at h
  have hh := mul_le_mul_of_nonneg_right h np.le
  simp only [sub_mul,div_mul_cancel₀ _ np.ne',one_mul] at hh
  linarith only [hh]

lemma pack (S : Finset ℕ) (z : ℕ → ℕ) (q Y H : ℝ) (hq : 0<q) (Y1 : 1≤Y) (H0 : 0≤H)
    (hS : ∀ n ∈ S, 0<n ∧ (n:ℝ)≤Y ∧ |q*log n-2*π*(z n)|≤H) :
    (S.card:ℝ) ≤ (q*log Y+H+1)*(2*H*Y/q+1) := by
  let K := ⌊q*log Y+H⌋₊
  have dest (n : ℕ) (hn : n∈S) : z n ∈ range (K+1) := by
    obtain ⟨np,ny,bd⟩ := hS n hn
    have logle := log_le_log (by exact_mod_cast np) ny
    have zm : (z n:ℝ) ≤ 2*π*(z n) := le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith [Real.pi_gt_three])
    apply mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    linarith [(abs_le.mp bd).1,mul_le_mul_of_nonneg_left logle hq.le]
  have fiber (j : ℕ) : ((S.filter (fun n=>z n=j)).card:ℝ) ≤ 2*H*Y/q+1 := by
    let T := S.filter (fun n=>z n=j)
    have non : 0 ≤ 2*H*Y/q := by positivity
    by_cases ne : T.Nonempty
    · let a := T.min' ne
      have am : a∈T := min'_mem _ _
      obtain ⟨as,az⟩ := mem_filter.mp am
      obtain ⟨ap,_,ab⟩ := hS a as
      have inj : T.card ≤ (range (⌊2*H*Y/q⌋₊ + 1)).card := by
        apply card_le_card_of_injOn (fun n : ℕ => n-a)
        · intro n hn
          obtain ⟨ns,nz⟩ := mem_filter.mp hn
          obtain ⟨np,ny,nb⟩ := hS n ns
          have an : a≤n := min'_le _ _ hn
          have both : q*(log n-log a)≤2*H := by
            rw [az] at ab
            rw [nz] at nb
            linarith [(abs_le.mp nb).2,(abs_le.mp ab).1]
          have lp : 0≤log n-log a := sub_nonneg.mpr (log_le_log (by exact_mod_cast ap) (by exact_mod_cast an))
          have eq := log_separation ap an
          have dist : (n:ℝ)-(a:ℝ)≤ Y*(2*H/q) :=
            eq.trans (mul_le_mul ny ((le_div_iff₀ hq).2 (by linarith only [both])) lp (by linarith))
          apply mem_range.mpr
          apply Nat.lt_succ_of_le
          apply Nat.le_floor
          rw [Nat.cast_sub an]
          exact dist.trans_eq (by ring)
        · intro n hn m hm e
          have := min'_le T n hn
          have := min'_le T m hm
          change n-a=m-a at e
          omega
      have cast : (T.card:ℝ) ≤ (⌊2*H*Y/q⌋₊:ℝ)+1 := by exact_mod_cast (by simpa using inj : T.card ≤ ⌊2*H*Y/q⌋₊+1)
      exact cast.trans (by linarith [Nat.floor_le non])
    · have te := not_nonempty_iff_eq_empty.mp ne
      change (T.card:ℝ) ≤ _
      simp only [te,card_empty,Nat.cast_zero]
      linarith
  have count := Finset.card_eq_sum_card_fiberwise dest
  have up : (S.card:ℝ) ≤ (K+1:ℝ)*(2*H*Y/q+1) := by
    rw [count,Nat.cast_sum]
    calc
      _ ≤ ∑ _j ∈ range (K+1), (2*H*Y/q+1) := sum_le_sum fun j _ => fiber j
      _ = _ := by simp <;> ring
  refine up.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have bn : 0 ≤ q*log Y+H := add_nonneg (mul_nonneg hq.le (Real.log_nonneg Y1)) H0
  linarith only [show (K:ℝ)≤q*log Y+H from Nat.floor_le bn]

lemma product_packing (G : Finset ℕ) (k d : ℕ) (q η : ℝ) (hq : 0<q) (he : 0≤η) (he1 : η≤1)
    (k1 : 1≤k) (hG : ∀ p∈G, p.Prime ∧ p≤k ∧ ∃ z : ℤ, |q*log p-2*π*z|≤η) :
    (G.card.choose d : ℝ) ≤ (q*log ((k:ℝ)^d) + d*η+1)*(2*(d*η)*(k:ℝ)^d/q+1) := by
  classical
  let prodP (Q : Finset ℕ) := ∏ p ∈ Q, p
  let S := (G.powersetCard d).image prodP
  have unique {Q W : Finset ℕ} (hQ : Q⊆G) (hW : W⊆G) (e : prodP Q=prodP W) : Q=W := by
    simpa only [prodP,Nat.primeFactors_prod (fun p hp => (hG p (hQ hp)).1),
      Nat.primeFactors_prod (fun p hp => (hG p (hW hp)).1)] using congrArg Nat.primeFactors e
  have cardS : S.card=G.card.choose d := by
    dsimp only [S]
    rw [card_image_of_injOn,card_powersetCard]
    intro Q hQ W hW e
    exact unique (mem_powersetCard.mp hQ).1 (mem_powersetCard.mp hW).1 e
  have each (p : ℕ) (hp : p∈G) : ∃ z : ℕ, |q*log p-2*π*z|≤η := by
    obtain ⟨pr,_,z,hz⟩ := hG p hp
    have zn : 0≤z := by
      by_contra! neg
      have zz : (z:ℝ)≤ -1 := by exact_mod_cast (by omega : z ≤ -1)
      have ql := mul_nonneg hq.le (Real.log_natCast_nonneg p)
      have := mul_le_mul_of_nonneg_left zz (show 0≤2*π by positivity)
      linarith [(abs_le.mp hz).2,pi_gt_three]
    refine ⟨z.toNat,?_⟩
    have eq : (z.toNat:ℝ) = (z:ℝ) := by exact_mod_cast Int.toNat_of_nonneg zn
    rwa [eq]
  have existZ (n : ℕ) (hn : n∈S) : ∃ z : ℕ, 0<n ∧ (n:ℝ)≤(k:ℝ)^d ∧ |q*log n-2*π*z|≤d*η := by
    obtain ⟨Q,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨sub,cs⟩ := mem_powersetCard.mp hm
    let f (p : ℕ) := if h : p∈G then (each p h).choose else 0
    have pz (p : ℕ) (hp : p∈Q) : |q*log p-2*π*(f p)|≤η := by simpa [f,sub hp] using (each p (sub hp)).choose_spec
    have pp (p : ℕ) (hp : p∈Q) : 0<p := (hG p (sub hp)).1.pos
    have nn : 0<prodP Q := Finset.prod_pos pp
    refine ⟨∑ p∈Q,f p,nn,?_,?_⟩
    · have u : prodP Q ≤ k^Q.card := Finset.prod_le_pow_card _ _ _ (fun p hp => (hG p (sub hp)).2.1)
      rw [cs] at u
      exact_mod_cast u
    · have logprod : log (prodP Q) = ∑ p∈Q,log p := by
        simp only [prodP,Nat.cast_prod]
        exact Real.log_prod (fun p hp => (Nat.cast_ne_zero.mpr (pp p hp).ne' : (p:ℝ)≠0))
      rw [logprod,Nat.cast_sum,Finset.mul_sum,Finset.mul_sum,←sum_sub_distrib]
      calc
        _ ≤ ∑ p∈Q,|q*log p-2*π*(f p)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p∈Q,η := sum_le_sum pz
        _ = _ := by simp [cs]
  let z (n : ℕ) := if h : n∈S then (existZ n h).choose else 0
  have result := pack S z q ((k:ℝ)^d) (d*η) hq (one_le_pow₀ (by exact_mod_cast k1)) (by positivity)
    (fun n hn => by simpa [z,hn] using (existZ n hn).choose_spec)
  simpa only [cardS] using result
lemma polylog_small (C : ℝ) (m : ℕ) :
    ∀ᶠ k : ℕ in atTop, C*(1+log k)^m ≤ (k:ℝ) := by
  let c := (max C 1)*2^m
  have cp : 0<c := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (by positivity)
  have natlim := tendsto_natCast_atTop_atTop (R:=ℝ)
  have H := (isLittleO_log_rpow_rpow_atTop (m:ℝ) (show (0:ℝ)<1 by norm_num)).bound (inv_pos.mpr cp)
  filter_upwards [natlim.eventually H,(tendsto_log_atTop.comp natlim).eventually_ge_atTop 1] with k H L
  change 1 ≤ log (k:ℝ) at L
  change ‖(log (k:ℝ))^(m:ℝ)‖ ≤ c⁻¹*‖(k:ℝ)^(1:ℝ)‖ at H
  rw [rpow_natCast,rpow_one,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (Nat.cast_nonneg _)] at H
  calc
    _ ≤ (max C 1)*((2*log k)^m) := mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (le_trans zero_le_one (le_max_right _ _))
    _ = c*(log k)^m := by dsimp [c]; ring
    _ ≤ c*(c⁻¹*(k:ℝ)) := mul_le_mul_of_nonneg_left H cp.le
    _ = _ := by field_simp

lemma prime_mass : ∀ᶠ k : ℕ in atTop, (k:ℝ) ≤
    4*((((Ioc k.sqrt k).filter Nat.Prime).card:ℝ)*(1+log k)) := by
  filter_upwards [polylog_small 10000 2,eventually_ge_atTop 2] with k small hk
  let P := (Ioc k.sqrt k).filter Nat.Prime
  let U := k.sqrt.primesLE
  have ku : k.sqrt≤k := Nat.sqrt_le_self _
  have sub : U ⊆ k.primesLE := by
    intro p hp
    obtain ⟨pl,pr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨pl.trans ku,pr⟩
  have setId : k.primesLE \ U = P := by
    apply Finset.ext
    intro p
    change p ∈ (k.primesLE \ k.sqrt.primesLE : Finset ℕ) ↔ p ∈ (Ioc k.sqrt k).filter Nat.Prime
    rw [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE,Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨pk,pp⟩,bad⟩
      exact ⟨⟨lt_of_not_ge (fun h => bad ⟨h,pp⟩),pk⟩,pp⟩
    · rintro ⟨⟨lt,pk⟩,pp⟩
      exact ⟨⟨pk,pp⟩,fun h => lt.not_ge h.1⟩
  have full : U.card + P.card = k.primeCounting := by
    rw [←Nat.primesLE_card_eq_primeCounting,←setId,add_comm,card_sdiff_add_card_eq_card sub]
  have uBound : U.card ≤ k.sqrt := by
    dsimp [U]
    rw [Nat.primesLE_eq_filter_Icc_one]
    simpa using card_filter_le (Icc 1 k.sqrt) Nat.Prime
  have xp : (1:ℝ)<k := by exact_mod_cast (by omega : 1<k)
  have lpos := log_pos xp
  have lower := (div_le_iff₀ lpos).mp (Chebyshev.pi_ge k)
  have upperLog : log ((k:ℝ)+1) ≤ 1+log k := by
    calc _ ≤ log ((k:ℝ)*2) := log_le_log (by positivity) (by linarith)
         _ ≤ _ := by rw [log_mul (by positivity) (by norm_num)]; linarith [log_two_lt_d9]
  have rootsq : (k.sqrt:ℝ)^2 ≤ (k:ℝ) := by exact_mod_cast (by simpa [pow_two] using Nat.sqrt_le k)
  have sqrtMul : (U.card:ℝ)*(1+log k) ≤ (k:ℝ)/10 := by
    have cu : (U.card:ℝ) ≤ k.sqrt := by exact_mod_cast uBound
    have cs := mul_le_mul_of_nonneg_right cu (show 0≤1+log k by linarith)
    nlinarith only [cs,rootsq,small,sq_nonneg ((k.sqrt:ℝ)-10*(1+log k)),sq_nonneg (1+log (k:ℝ))]
  have ctot : (U.card:ℝ)+(P.card:ℝ) = k.primeCounting := by exact_mod_cast full
  have l2 := mul_le_mul_of_nonneg_left (show (1/2:ℝ)≤log 2 by linarith [log_two_gt_d9]) (Nat.cast_nonneg k)
  have smallL : 1+log k ≤ (k:ℝ)/10 := by nlinarith [sq_nonneg (log (k:ℝ))]
  change (k:ℝ) ≤ 4*((P.card:ℝ)*(1+log k))
  rw [←ctot] at lower
  nlinarith only [lower,upperLog,l2,smallL,sqrtMul,Nat.cast_nonneg U.card (α:=ℝ),Nat.cast_nonneg P.card (α:=ℝ)]

lemma lattice_phase (w : ℝ) : ∃ j : ℤ, |w-2*π*j|^2 ≤ 2*π^2*(1-|cos (w/2)|) := by
  let u := w/(2*π)
  let j := round u
  let v := π*(u-j)
  have near := abs_sub_round u
  have vb : |v| ≤ π/2 := by
    dsimp [v]
    rw [abs_mul,abs_of_pos pi_pos]
    linarith [mul_le_mul_of_nonneg_left near pi_pos.le]
  have cs := cos_nonneg_of_mem_Icc ⟨(abs_le.mp vb).1,(abs_le.mp vb).2⟩
  have eq : w/2 = v+(j:ℝ)*π := by dsimp [u,v]; field_simp <;> ring
  have cosEq : |cos (w/2)|=cos v := by
    simp only [eq,cos_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul,abs_of_nonneg cs]
  have bound := cos_le_one_sub_mul_cos_sq (vb.trans (by linarith [pi_pos]))
  have hj : w-2*π*(j:ℝ)=2*v := by linarith only [eq]
  refine ⟨j,?_⟩
  rw [hj,sq_abs,cosEq]
  have pb := mul_le_mul_of_nonneg_left bound (sq_nonneg π)
  field_simp at pb
  nlinarith only [pb]
theorem binomial_ge_ratio {M k : ℕ} (hkM : k ≤ M) :
    ((M : ℝ) / k) ^ k ≤ (M.choose k : ℝ) := by
  have hid : (∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ)) =
      (M.choose k : ℝ) := by
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    exact mul_div_cancel_left₀ _ hfact
  calc
    ((M : ℝ) / k) ^ k = ∏ j ∈ Finset.range k, ((M : ℝ) / k) := by simp [div_pow]
    _ ≤ ∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ) := by
      apply Finset.prod_le_prod (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjM : j ≤ M := hjk.le.trans hkM
      have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
      have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
      rw [Nat.cast_sub hjM, Nat.cast_sub hjk.le, div_le_div_iff₀ hkpos (sub_pos.mpr hjk')]
      nlinarith [mul_nonneg (sub_nonneg.mpr hkM') (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = (M.choose k : ℝ) := hid



lemma packing_contradiction {K R d q η A Y V Z : ℝ} (kp : 0<K) (r1 : 1≤R)
    (dp : 0≤d) (qp : 0<q) (ep : 0≤η) (ap : 0≤A) (yp : 0<Y) (oneV : 1≤V)
    (dy : d*η ≤ 1) (yid : Y=K*V) (ql : 1/R^2≤q) (qu : q≤V)
    (tol : A*(2*d^2*R+4*d*R^2)*η ≤ 1/4) (cut : A*(d*R+2) ≤ K/4)
    (lo : Y ≤ A*Z) (hi : Z ≤ (q*d*R+d*η+1)*(2*(d*η)*Y/q+1)) : False := by
  have rp : 0<R := by linarith
  have invq : 1/q ≤ R^2 := (div_le_iff₀ qp).2 (by
    have hh := (div_le_iff₀ (sq_pos_of_pos rp)).mp ql
    linarith only [hh])
  have w0 : 0 ≤ 2*(d*η)*Y/q+1 := by positivity
  have hi' := hi.trans (mul_le_mul_of_nonneg_right (show q*d*R+d*η+1 ≤ q*d*R+2 by linarith) w0)
  have norm : (q*d*R+2)*(2*(d*η)*Y/q+1) =
      (2*d^2*R)*η*Y + (4*d*η*Y)*(1/q) + q*d*R+2 := by field_simp; ring
  rw [norm] at hi'
  have mid := mul_le_mul_of_nonneg_left invq (show 0≤4*d*η*Y by positivity)
  have big := mul_le_mul_of_nonneg_right qu (show 0≤d*R by positivity)
  have vp := zero_le_one.trans oneV
  have coarse : Z ≤ (2*d^2*R+4*d*R^2)*η*Y + (d*R+2)*V := by linarith only [hi',mid,big,oneV]
  have all := lo.trans (mul_le_mul_of_nonneg_left coarse ap)
  have h1 := mul_le_mul_of_nonneg_right tol yp.le
  have h2 := mul_le_mul_of_nonneg_right cut vp
  rw [yid] at all h1 yp
  linarith only [all,h1,h2,yp]

lemma good_count (P : Finset ℕ) (q M R K L : ℝ) (A : ℕ) (qp : 0<q) (lp : 0<L)
    (r1 : 1≤R) (pcount : K ≤ 4*((P.card:ℝ)*R))
    (saving : (16*π^2*M*L^2)*R^(2*A+2) ≤ K)
    (low : ∑ p∈P,(1-|cos (q*log p/2)|) < M*R) :
    let η := 1/(L*R^A)
    let G := P.filter fun p : ℕ => ∃ z:ℤ, |q*log p-2*π*z|≤η
    K ≤ 8*((G.card:ℝ)*R) := by
  let η := 1/(L*R^A)
  let G := P.filter fun p : ℕ => ∃ z:ℤ, |q*log p-2*π*z|≤η
  let V := P \ G
  have ep : 0<η := by dsimp [η]; positivity
  have cost : (V.card:ℝ)*η^2 ≤ 2*π^2*(M*R) := by
    calc
      _ = ∑ _p∈V,η^2 := by simp
      _ ≤ ∑ p∈V,(2*π^2)*(1-|cos (q*log p/2)|) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨pp,pg⟩ := mem_sdiff.mp hp
        obtain ⟨z,hz⟩ := lattice_phase (q*log p)
        have far : η < |q*log p-2*π*z| := lt_of_not_ge fun a => pg (mem_filter.mpr ⟨pp,z,a⟩)
        exact (pow_le_pow_left₀ ep.le far.le _).trans hz
      _ ≤ _ := by
        rw [←mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ => sub_nonneg.mpr (abs_cos_le_one _))).trans low.le
  have total : (V.card:ℝ)+G.card=P.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (filter_subset (fun p:ℕ=>∃z:ℤ,|q*log p-2*π*z|≤η) P)
  have identity : η^2*(L^2*R^(2*A)*R)=R := by
    dsimp [η]; rw [Nat.mul_comm 2 A,pow_mul]; field_simp
  have tmp := mul_le_mul_of_nonneg_right cost (show 0≤L^2*R^(2*A)*R by positivity)
  rw [mul_assoc (V.card:ℝ),identity] at tmp
  rw [pow_add,pow_two] at saving
  change K≤8*((G.card:ℝ)*R)
  nlinarith only [tmp,saving,pcount,congrArg (fun x:ℝ=>x*R) total]

end LogPrimePacking
open LogPrimePacking

theorem OMA.prime_dispersion : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H1 := by
  intro M
  let d := M+1
  let C := (8*(d:ℝ))^d
  let L := 32*C*((d:ℝ)+1)^2
  let A := d+2
  have dn : 0<d := Nat.succ_pos M
  have dr : (0:ℝ)<d := by exact_mod_cast dn
  have d1 : (1:ℝ)≤d := by exact_mod_cast dn
  have c1 : 1≤C := one_le_pow₀ (by linarith)
  have cp : 0<C := by linarith
  have lp : 0<L := by dsimp [L]; positivity
  filter_upwards [prime_mass,polylog_small (16*π^2*M*L^2) (2*A+2),
    polylog_small (4*C*((d:ℝ)+2)) (d+1),polylog_small (8*(d:ℝ)) 1,
    eventually_ge_atTop 2] with k mass saving cutoff enough k2
  intro s hl hu
  let R := 1+log (k:ℝ)
  let η := 1/(L*R^A)
  let P := (Ioc k.sqrt k).filter Nat.Prime
  let q := |s|
  have r1 : 1≤R := by dsimp [R]; linarith [log_natCast_nonneg k]
  have rp : 0<R := by linarith
  have kp : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have k1 : (1:ℝ)≤k := by exact_mod_cast (by omega : 1≤k)
  have qp : 0<q := lt_of_lt_of_le (by positivity : 0<1/R^2) hl
  have ep : 0<η := by dsimp [η]; positivity
  have eD : (d:ℝ)*η≤1 := by
    dsimp [η]
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    have dpow := one_le_pow₀ (n:=A) r1
    have hL : (d:ℝ) ≤ L := by
      have h := mul_le_mul_of_nonneg_right c1 (sq_nonneg ((d:ℝ)+1))
      dsimp [L]; nlinarith [sq_nonneg (d:ℝ)]
    linarith [mul_le_mul_of_nonneg_left dpow lp.le]
  have e1 : η≤1 := (le_mul_of_one_le_left ep.le d1).trans eD
  have eqL (p : ℕ) : |cos (s*log p/2)|=|cos (q*log p/2)| := by
    rcases le_or_gt 0 s with hs|hs
    · simp [q,abs_of_nonneg hs]
    · simp [q,abs_of_neg hs,neg_mul,neg_div,cos_neg]
  change (M:ℝ)*log k ≤ ∑ p∈P,(1-|cos (s*log p/2)|)
  simp_rw [eqL]
  by_contra! bad
  have badR := bad.trans_le (mul_le_mul_of_nonneg_left (by dsimp [R]; linarith : log (k:ℝ)≤R) (Nat.cast_nonneg M))
  let G := P.filter fun p : ℕ => ∃ z:ℤ, |q*log p-2*π*z|≤η
  have many : (k:ℝ)≤8*((G.card:ℝ)*R) := good_count P q M R k L A qp lp r1 mass saving badR
  have gd : d≤G.card := by
    change 8*(d:ℝ)*R^1≤k at enough
    rw [pow_one] at enough
    exact_mod_cast (le_of_not_gt (fun h : (G.card:ℝ)<d => by nlinarith only [many,enough,mul_lt_mul_of_pos_right h rp]) : (d:ℝ)≤G.card)
  have ratio : (k:ℝ) ≤ (8*d*R)*((G.card:ℝ)/d) := many.trans_eq (by field_simp)
  have raised := pow_le_pow_left₀ kp.le ratio d
  rw [mul_pow,mul_pow] at raised
  have comb := binomial_ge_ratio gd
  have low : (k:ℝ)^d ≤ (C*R^d)*(G.card.choose d:ℝ) := by
    change (k:ℝ)^d ≤ (C*R^d)*((G.card:ℝ)/d)^d at raised
    exact raised.trans (mul_le_mul_of_nonneg_left comb (by positivity))
  have up := product_packing G k d q η qp ep.le e1 (by omega)
    (fun p hp => by
      obtain ⟨hP,z,hz⟩ := mem_filter.mp hp
      obtain ⟨hi,pp⟩ := mem_filter.mp hP
      exact ⟨pp,(mem_Ioc.mp hi).2,z,hz⟩)
  rw [Real.log_pow] at up
  have up' : (G.card.choose d:ℝ) ≤ (q*d*R+d*η+1)*(2*(d*η)*(k:ℝ)^d/q+1) := up.trans (by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hR : log (k:ℝ) ≤ R := by dsimp [R]; linarith
    linarith only [mul_le_mul_of_nonneg_left hR (show 0 ≤ q*d by positivity)])
  have tol : (C*R^d)*(2*(d:ℝ)^2*R+4*d*R^2)*η ≤ 1/4 := by
    dsimp only [η,L,A]
    rw [pow_add R d 2,mul_one_div,div_le_iff₀ (by positivity)]
    have t1 := mul_le_mul_of_nonneg_left (show R≤R^2 by nlinarith only [mul_le_mul_of_nonneg_left r1 rp.le])
      (show 0≤2*(d:ℝ)^2 by positivity)
    have h : 2*(d:ℝ)^2*R+4*d*R^2 ≤ 8*((d:ℝ)+1)^2*R^2 := by nlinarith only [t1,sq_nonneg ((d:ℝ)*R),sq_nonneg R,mul_nonneg dr.le (sq_nonneg R)]
    linarith only [mul_le_mul_of_nonneg_left h (show 0≤C*R^d by positivity)]
  have cut : (C*R^d)*((d:ℝ)*R+2)≤(k:ℝ)/4 := by
    change 4*C*((d:ℝ)+2)*R^(d+1) ≤ k at cutoff
    rw [pow_succ] at cutoff
    linarith only [cutoff,mul_le_mul_of_nonneg_left r1 (show 0≤C*R^d by positivity)]
  exact packing_contradiction kp r1 dr.le qp ep.le (by positivity) (by positivity)
    (one_le_pow₀ k1) eD (show (k:ℝ)^d=(k:ℝ)*(k:ℝ)^M by dsimp [d]; ring)
    hl hu tol cut low up'
end

namespace OMA.MajorArc1099
open Finset Real
open scoped Classical

theorem fourierEnvelope : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H2 := by
  intro k hk s y
  let n := Nat.lcmUpto k
  let U := n.primeFactors
  let P := (Ioc k.sqrt k).filter Nat.Prime
  let v (p:ℕ) := n.factorization p
  let loss (p:ℕ) := 1-|cos (s*log p/2)|
  have nz : n≠0 := Nat.lcmUpto_ne_zero k
  have sub : P ⊆ U := by
    intro p hp
    obtain ⟨h,pr⟩ := mem_filter.mp hp
    change p∈(Nat.lcmUpto k).primeFactors
    rw [Nat.primeFactors_lcmUpto]
    exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp h).2,pr⟩
  have absW : |∑ d∈n.divisors,cos (s*(log d-y))| ≤ |centered s n| := by
    let b := s*(log n/2-y)
    have idd (d:ℕ) : s*(log d-y) = s*(log d-log n/2)+b := by dsimp [b]; ring
    simp_rw [idd,cos_add]
    rw [sum_sub_distrib,←sum_mul,←sum_mul,sine_zero,zero_mul,sub_zero,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have factor (p:ℕ) (hp:p∈U) : |centered s (p^(v p))| ≤
      (((p^(v p)).divisors.card:ℝ))*exp (if p∈P then -loss p else 0) := by
    by_cases h : p∈P
    · obtain ⟨intv,pr⟩ := mem_filter.mp h
      have b := mem_Ioc.mp intv
      have v1 : v p=1 := by
        change (Nat.lcmUpto k).factorization p=1
        rw [Nat.factorization_lcmUpto k pr]
        exact (Nat.log_eq_iff (Or.inl one_ne_zero)).2 ⟨by simpa using b.2,Nat.sqrt_lt'.mp b.1⟩
      rw [if_pos h,v1,pow_one]
      have divs : p.divisors={1,p} := by
        rw [←pow_one p,Nat.divisors_prime_pow pr,show range (1+1)={0,1} by decide]
        simp
      have eval : centered s p = 2*cos (s*log p/2) := by
        rw [centered,divs,Finset.sum_pair pr.ne_one.symm]
        simp only [Nat.cast_one,log_one,zero_sub,mul_neg,cos_neg]
        rw [show log (p:ℝ)-log p/2=log p/2 by ring,←mul_div_assoc]
        ring
      have hExp := Real.add_one_le_exp (|cos (s*log p/2)|-1)
      rw [eval,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),divs,Finset.card_pair pr.ne_one.symm]
      dsimp [loss]
      rw [neg_sub]
      push_cast
      linarith only [hExp]
    · rw [if_neg h,Real.exp_zero,mul_one,centered]
      exact (abs_sum_le_sum_abs _ _).trans (by simpa using
        (sum_le_sum (s:=(p^(v p)).divisors) (fun d _ => abs_cos_le_one (s*(log d-log (p^(v p):ℕ)/2)))))
  have cardEq : (n.divisors.card:ℝ) = ∏ p∈U, ((p^(v p)).divisors.card:ℝ) := by
    simpa [centered,U,v] using (center_prod 0 nz)
  have exEq : (∏ p∈U,exp (if p∈P then -loss p else 0))=exp (-(∑ p∈P,loss p)) := by
    rw [←Real.exp_sum,←sum_filter]
    have eq : U.filter (·∈P)=P := by ext p; simp only [mem_filter]; exact ⟨And.right,fun h=>⟨sub h,h⟩⟩
    rw [eq,sum_neg_distrib]
  change |∑ d∈n.divisors,cos (s*(log d-y))| ≤ (n.divisors.card:ℝ)*exp (-(∑ p∈P,loss p))
  refine absW.trans ?_
  rw [center_prod s nz,Finset.abs_prod,cardEq,←exEq,←prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _=>abs_nonneg _) factor

end OMA.MajorArc1099

theorem OMA.solution : type_of% @Erdos1099.erdos_1099.variants.lcm :=
  OMA.R_Erdos1099_erdos_1099_variants_lcm_R1.main (OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1.main OMA.central_mass
    (OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.main OMA.prime_dispersion OMA.MajorArc1099.fourierEnvelope)) OMA.divisor_summation
