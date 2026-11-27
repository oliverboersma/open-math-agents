import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1

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

theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1.H1 := by
  intro m
  have hC := gaussianPDFReal_pos 0 1 1 (by norm_num)
  obtain ⟨K,hK⟩ := exists_nat_gt (32/gaussianPDFReal 0 1 1)
  filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 1] with k hk hk1
  intro y hy
  apply OMA.MajorArc1099.major k hk1 _ y (one_le_pow₀ (by exact_mod_cast hk1)) hy
  have h := (div_lt_iff₀ hC).mp (hK.trans_le (by exact_mod_cast hk : (K:ℝ)≤k))
  linarith
