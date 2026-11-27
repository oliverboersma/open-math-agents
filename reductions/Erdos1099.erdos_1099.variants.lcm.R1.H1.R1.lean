import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1
import Mathlib

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
