import FormalConjectures.ErdosProblems.«513»
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! An explicit uniform gap below two over pi in the maximum-term problem. -/

section
/- Stability of the Fourier coefficient profile at a maximum-term tie. -/

/- The arithmetic obstruction at two successive maximum-term ties. -/

namespace MaximumTerm

noncomputable section

/-- Relative coefficient magnitudes of the extremizer for a pair of tied terms. -/
def profile (m d k : ℤ) : ℝ :=
  if d ∣ k-m then 1 / |(2 * ((k-m)/d) + 1 : ℤ)| else 0

theorem profile_multiple (m d q : ℤ) (hd : 0 < d) :
    profile m d (m+d*q) = 1 / |(2*q+1 : ℤ)| := by
  unfold profile
  rw [add_comm m, add_sub_cancel_right, if_pos (dvd_mul_right _ _)]
  have he : (d*q)/d = q := by
    apply Int.eq_of_mul_eq_mul_left hd.ne'
    rw [Int.mul_comm d, Int.ediv_mul_cancel (dvd_mul_right _ _)]
  rw [he]

/-- Consecutive ties cannot both have their normalized coefficients close to the ideal profile. -/
theorem consecutive_ties_obstruction (u v : ℤ → ℝ) (n m p : ℤ) (ρ : ℝ)
    (hnm : n < m) (hmp : m < p) (hρ : 0 < ρ)
    (hu : ∀ j, 0 ≤ u j ∧ u j ≤ 1) (hv : ∀ j, v j ≤ 1) (hvp : v p = 1)
    (hscale : ∀ j, v j = u j * ρ^(j-m))
    (hfirst : ∀ j, |u j - profile m (m-n) j| ≤ 1/100)
    (hnext : ∀ j, |v j - profile p (p-m) j| ≤ 1/100) : False := by
  let d := m-n
  let e := p-m
  have hd : 0 < d := sub_pos.mpr hnm
  have he : 0 < e := sub_pos.mpr hmp
  let t : ℝ := ρ^e
  have ht : 0 < t := zpow_pos hρ _
  have hup : u p * t = 1 := (hscale p).symm.trans hvp
  have htinv : t⁻¹ = u p := by
    apply (eq_div_iff ht.ne').2 at hup
    simpa only [one_div] using hup.symm
  have hbackIndex : 2*m-p = p+e*(-2) := by dsimp [e]; ring
  have hbackProfile : profile p e (2*m-p) = 1/3 := by
    rw [hbackIndex, profile_multiple p e (-2) he]
    norm_num
  have hback : 1/3-1/100 ≤ v (2*m-p) := by
    have hh := (abs_le.mp (hnext (2*m-p))).1
    change -(1/100 : ℝ) ≤ v (2*m-p) - profile p e (2*m-p) at hh
    rw [hbackProfile] at hh
    linarith
  have hrev : v (2*m-p) = u (2*m-p) * u p := by
    rw [hscale, show 2*m-p-m = -e by dsimp [e]; ring, zpow_neg]
    exact congrArg (u (2*m-p) * ·) htinv
  have hupLower : 1/3-1/100 ≤ u p := by
    calc
      _ ≤ v (2*m-p) := hback
      _ = u (2*m-p) * u p := hrev
      _ ≤ u p := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu (2*m-p)).2 (hu p).1
  have hnz : d ∣ e := by
    by_contra hn
    have hb := (abs_le.mp (hfirst p)).2
    change u p - profile m d p ≤ 1/100 at hb
    simp [profile, show p-m=e from rfl, hn] at hb
    linarith
  obtain ⟨q,hq⟩ := hnz
  have hqpos : 0 < q := by
    by_contra! hneg
    have hh := mul_nonpos_of_nonneg_of_nonpos hd.le hneg
    rw [← hq] at hh
    omega
  have hP : p = m+d*q := by dsimp [e] at hq; omega
  have hap := (abs_le.mp (hfirst p)).2
  change u p - profile m d p ≤ 1/100 at hap
  have hprofileP : profile m d p = 1 / |(2*q+1 : ℤ)| := by rw [hP,profile_multiple _ _ _ hd]
  rw [hprofileP] at hap
  have hq1 : q = 1 := by
    by_contra qne
    have hb : (5 : ℝ) ≤ ((2*q+1 : ℤ) : ℝ) := by exact_mod_cast (show (5:ℤ) ≤ 2*q+1 by omega)
    have hbound : (1 : ℝ) / |(2*q+1 : ℤ)| ≤ 1/5 := by
      rw [abs_of_nonneg (by omega : (0:ℤ) ≤ 2*q+1)]
      exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hb
    linarith
  have hupUpper : u p ≤ 1/3+1/100 := by
    rw [hq1] at hap
    norm_num at hap
    linarith
  have heq : e = d := by simpa [hq1] using hq
  have hidx : 2*p-m = m+d*2 := by dsimp [e] at heq; omega
  have hthird : 1/5-1/100 ≤ u (2*p-m) := by
    have hb := (abs_le.mp (hfirst (2*p-m))).1
    change -(1/100 : ℝ) ≤ u (2*p-m) - profile m d (2*p-m) at hb
    rw [hidx, profile_multiple _ _ _ hd] at hb
    norm_num at hb
    rw [← hidx] at hb
    linarith
  have hforward : v (2*p-m) * (u p)^2 = u (2*p-m) := by
    rw [hscale, show 2*p-m-m = e+e by dsimp [e]; ring, zpow_add₀ hρ.ne']
    change u (2*p-m) * (t*t) * (u p)^2 = _
    calc
      _ = u (2*p-m) * (u p * t)^2 := by ring
      _ = _ := by rw [hup,one_pow,mul_one]
  have hsmall : u (2*p-m) ≤ (1/3+1/100)^2 := calc
    _ = v (2*p-m) * (u p)^2 := hforward.symm
    _ ≤ (u p)^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hv (2*p-m)) (sq_nonneg (u p))
    _ ≤ (1/3+1/100)^2 := by
      nlinarith only [sq_nonneg (u p-(1/3+1/100)),
        mul_nonneg (sub_nonneg.mpr hupUpper) (add_nonneg (hu p).1 (by norm_num : 0 ≤ (1/3+1/100 : ℝ)))]
  nlinarith

end

end MaximumTerm

/- Fourier coefficients of the ideal boundary function for a maximum-term tie. -/

open Complex Set MeasureTheory Filter Function
open scoped ComplexConjugate Interval Topology

namespace MaximumTerm

noncomputable section

def phase (x : ℝ) : ℂ := exp ((x : ℂ) * I)

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := norm_exp_ofReal_mul_I x

theorem phase_conj (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  simp only [← Complex.exp_conj, map_mul, conj_ofReal, conj_I, mul_neg, ofReal_neg, neg_mul]

theorem integer_period_phase (k : ℤ) : phase ((k : ℝ)*(2*Real.pi)) = 1 := by
  unfold phase
  rw [ofReal_mul, ofReal_intCast, ofReal_mul,ofReal_ofNat,mul_assoc]
  exact exp_int_mul_two_pi_mul_I k

private theorem phase_two_pi : Periodic phase (2*Real.pi) := by
  intro x
  have h : phase (2*Real.pi) = 1 := by
    simpa only [Int.cast_one, one_mul] using (integer_period_phase 1)
  rw [phase_add,h,mul_one]

def wave (x : ℝ) : ℂ := 1 + phase x

def ideal (x : ℝ) : ℂ := conj (wave x) / (‖wave x‖ : ℂ)

theorem wave_periodic : Periodic wave (2*Real.pi) := by
  intro x
  simp only [wave,phase_two_pi x]

theorem ideal_periodic : Periodic ideal (2*Real.pi) := by
  intro x
  simp only [ideal,wave_periodic x]

theorem ideal_norm_le (x : ℝ) : ‖ideal x‖ ≤ 1 := by
  by_cases h : ‖wave x‖ = 0
  · simp [ideal,h]
  · simp only [ideal,norm_div,Complex.norm_conj,norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    simp [h]

theorem measurable_ideal : Measurable ideal := by
  unfold ideal wave phase
  fun_prop

theorem ideal_interval_integrable (f : ℝ → ℂ) (hm : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact Eventually.of_forall hb

theorem wave_factor (x : ℝ) :
    wave x = (2 * (Real.cos (x/2) : ℂ)) * phase (x/2) := by
  have hsum : phase (x/2) + phase (-(x/2)) = 2 * (Real.cos (x/2) : ℂ) := by
    rw [phase,phase,ofReal_neg,exp_mul_I,exp_mul_I,cos_neg,sin_neg,← ofReal_cos]
    ring
  rw [← hsum, add_mul, ← phase_add, ← phase_add]
  have hzero : phase 0 = 1 := by simp [phase]
  rw [show x/2+x/2=x by ring, neg_add_cancel,hzero,wave,add_comm]

theorem norm_wave_on_cell {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    ‖wave x‖ = 2 * Real.cos (x/2) := by
  have hc : 0 ≤ Real.cos (x/2) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [wave_factor,norm_mul,phase_norm,mul_one,← ofReal_ofNat,← ofReal_mul, norm_real,
    Real.norm_eq_abs,abs_of_nonneg (by positivity)]

theorem ideal_on_cell {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) :
    ideal x = phase (-(x/2)) := by
  have hc : 0 < Real.cos (x/2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hn : ((2 : ℂ) * (Real.cos (x/2) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hc.ne')
  unfold ideal
  rw [norm_wave_on_cell (Ioo_subset_Icc_self hx),wave_factor]
  simp only [map_mul,map_ofNat,conj_ofReal,phase_conj,ofReal_mul,ofReal_ofNat]
  rw [mul_comm (2 * (Real.cos (x/2) : ℂ)), mul_div_cancel_right₀ _ hn]

theorem integral_period_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hp : Periodic f (2*Real.pi))
    (hi : ∀ a b, IntervalIntegrable f volume a b) (d : ℤ) (hd : 0 < d) :
    (∫ θ in 0..2*Real.pi, f ((d:ℝ)*θ)) = ∫ θ in 0..2*Real.pi, f θ := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [intervalIntegral.integral_comp_mul_left f hd',mul_zero]
  have h := hp.intervalIntegral_add_zsmul_eq d 0 hi
  simp only [zero_add,zsmul_eq_mul] at h
  rw [h,← Int.cast_smul_eq_zsmul ℝ,smul_smul,inv_mul_cancel₀ hd',one_smul]

def meanCoeff (g : ℝ → ℂ) (k : ℤ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ θ in 0..2*Real.pi, g θ * phase (-(k:ℝ)*θ)

private theorem phase_int_periodic (k : ℤ) : Periodic (fun θ => phase (-(k:ℝ)*θ)) (2*Real.pi) := by
  intro θ
  dsimp only
  rw [mul_add,phase_add,show -(k:ℝ)*(2*Real.pi) = ((-k:ℤ):ℝ)*(2*Real.pi) by simp,
    integer_period_phase,mul_one]

theorem ideal_base_coeff_norm (q : ℤ) :
    ‖meanCoeff ideal q‖ = 2 / Real.pi / |((2*q+1:ℤ):ℝ)| := by
  let f := fun θ : ℝ => ideal θ * phase (-(q:ℝ)*θ)
  have hper : Periodic f (2*Real.pi) := ideal_periodic.mul (phase_int_periodic q)
  have hsym : (∫ θ in 0..2*Real.pi, f θ) = ∫ θ in (-Real.pi)..Real.pi, f θ := by
    simpa only [zero_add, show -Real.pi+2*Real.pi=Real.pi by ring] using hper.intervalIntegral_add_eq 0 (-Real.pi)
  have hcell : (∫ θ in (-Real.pi)..Real.pi, f θ) =
      ∫ θ in (-Real.pi)..Real.pi, phase ((-(q:ℝ)-1/2)*θ) := by
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    filter_upwards [volume.ae_ne Real.pi] with θ hn hθ
    have hθ' : θ ∈ Ioo (-Real.pi) Real.pi :=
      ⟨hθ.1, lt_of_le_of_ne hθ.2 (fun he => hn he)⟩
    unfold f
    rw [ideal_on_cell hθ', ← phase_add]
    congr 1
    ring
  let c : ℝ := -(q:ℝ)-1/2
  have hc : c ≠ 0 := by
    intro he
    have hq : 2*q+1=0 := by exact_mod_cast (show 2*(q:ℝ)+1=0 by dsimp [c] at he; linarith)
    omega
  have hI : (∫ θ in (-Real.pi)..Real.pi, phase (c*θ)) = (2*Real.sin (c*Real.pi) / c : ℝ) := by
    have hcd := intervalIntegral.integral_comp_mul_left (fun t : ℝ => phase t) hc
      (a := -Real.pi) (b := Real.pi)
    rw [hcd, mul_neg, show (∫ θ in -(c*Real.pi)..c*Real.pi, phase θ) = (2*Real.sin (c*Real.pi) : ℂ) from
      integral_exp_mul_I_eq_sin _, Complex.real_smul]
    push_cast
    ring
  have hsin : |Real.sin (c*Real.pi)| = 1 := by
    have hx : c*Real.pi = ((-q:ℤ):ℝ)*Real.pi-Real.pi/2 := by
      simp [c]
      ring
    rw [hx, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one,
      zero_sub, abs_neg,Real.abs_cos_int_mul_pi]
  have hden : |((2*q+1:ℤ):ℝ)| = 2*|c| := by
    push_cast
    rw [show 2*(q:ℝ)+1 = -(2*c) by dsimp [c]; ring, abs_neg,abs_mul,show |(2:ℝ)|=2 by norm_num]
  unfold meanCoeff
  rw [show (fun θ : ℝ => ideal θ * phase (-(q:ℝ)*θ)) = f from rfl,hsym,hcell,
    show -(q:ℝ)-1/2=c from rfl,hI,norm_mul,norm_inv,norm_real,norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2*Real.pi),
    abs_div,abs_mul,show |(2:ℝ)|=2 by norm_num,hsin,mul_one,hden]
  ring

theorem ideal_dilate_coeff_norm (d k : ℤ) (hd : 0 < d) :
    ‖meanCoeff (fun θ => ideal ((d:ℝ)*θ)) k‖ =
      if d ∣ k then 2 / Real.pi / |((2*(k/d)+1:ℤ):ℝ)| else 0 := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  let P := 2*Real.pi
  let f := fun θ : ℝ => ideal ((d:ℝ)*θ) * phase (-(k:ℝ)*θ)
  by_cases hdiv : d ∣ k
  · obtain ⟨q,rfl⟩ := hdiv
    have he : d*q/d = q := by
      apply Int.eq_of_mul_eq_mul_left hd.ne'
      rw [Int.mul_comm d,Int.ediv_mul_cancel (dvd_mul_right _ _)]
    let g := fun θ : ℝ => ideal θ * phase (-(q:ℝ)*θ)
    have hp : Periodic g (2*Real.pi) := ideal_periodic.mul (phase_int_periodic q)
    have hi (a b : ℝ) : IntervalIntegrable g volume a b := by
      apply ideal_interval_integrable
      · unfold g phase
        have := measurable_ideal
        fun_prop
      · intro θ
        simp only [g,norm_mul,phase_norm,mul_one]
        exact ideal_norm_le θ
    have hfg (θ : ℝ) : f θ = g ((d:ℝ)*θ) := by
      dsimp only [f,g]
      congr 2
      push_cast
      ring
    have hmean : meanCoeff (fun θ => ideal ((d:ℝ)*θ)) (d*q) = meanCoeff ideal q := by
      unfold meanCoeff
      congr 1
      change (∫ θ in 0..P, f θ) = ∫ θ in 0..P, g θ
      simp_rw [hfg]
      exact integral_period_dilate g hp hi d hd
    rw [hmean,ideal_base_coeff_norm,if_pos (dvd_mul_right _ _),he]
  · have hP : Periodic f P := by
      intro θ
      have hiP : ideal ((d:ℝ)*(θ+P)) = ideal ((d:ℝ)*θ) := by
        rw [mul_add]
        simpa only [zsmul_eq_mul] using (ideal_periodic.zsmul d) ((d:ℝ)*θ)
      change ideal ((d:ℝ)*(θ+P)) * phase (-(k:ℝ)*(θ+P)) =
        ideal ((d:ℝ)*θ) * phase (-(k:ℝ)*θ)
      have hq := phase_int_periodic k θ
      change phase (-(k:ℝ)*(θ+P)) = phase (-(k:ℝ)*θ) at hq
      rw [hiP,hq]
    let a := P/(d:ℝ)
    have hda : (d:ℝ)*a=P := by unfold a; field_simp
    have hshift (θ : ℝ) : f (θ+a) = phase (-(k:ℝ)*a) * f θ := by
      dsimp only [f]
      rw [mul_add (d:ℝ), hda, ideal_periodic, mul_add, phase_add]
      ring
    have hInt' : (∫ θ in 0..P, f (θ+a)) = ∫ θ in 0..P, f θ := by
      rw [intervalIntegral.integral_comp_add_right,zero_add,add_comm P a]
      simpa only [zero_add] using hP.intervalIntegral_add_eq a 0
    have hInt := hInt'
    simp_rw [hshift,intervalIntegral.integral_const_mul] at hInt
    have hnot : phase (-(k:ℝ)*a) ≠ 1 := by
      intro h
      obtain ⟨j,hj⟩ := Complex.exp_eq_one_iff.mp h
      have hj' : ((-(k:ℝ)*a:ℝ):ℂ) * I = (((j:ℝ)*(2*Real.pi):ℝ):ℂ) * I := by
        simpa only [ofReal_mul,ofReal_intCast,ofReal_ofNat,mul_assoc] using hj
      have hr := Complex.ofReal_injective (mul_right_cancel₀ I_ne_zero hj')
      have ha : a = P/(d:ℝ) := rfl
      rw [ha] at hr
      have hP0 : 0 < P := by dsimp [P]; positivity
      have hquot : -(k:ℝ) / (d:ℝ) = (j:ℝ) := by
        apply (mul_right_cancel₀ hP0.ne')
        have hr' : -(k:ℝ)*(P/(d:ℝ)) = (j:ℝ)*P := hr
        convert hr' using 1; ring
      have hk := (div_eq_iff hdR.ne').1 hquot
      apply hdiv
      refine ⟨-j,?_⟩
      exact_mod_cast (show (k:ℝ) = (d:ℝ)*(((-j:ℤ):ℝ)) by push_cast; linarith)
    have hz : (∫ θ in 0..P, f θ) = 0 := by
      have hz' : (phase (-(k:ℝ)*a)-1) * (∫ θ in 0..P, f θ) = 0 := by
        rw [sub_mul,one_mul,hInt,sub_self]
      exact (mul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr hnot)
    rw [if_neg hdiv]
    change ‖((P:ℝ):ℂ)⁻¹ * (∫ θ in 0..P, f θ)‖ = 0
    rw [hz,mul_zero,norm_zero]

private theorem continuous_wave : Continuous wave := by
  unfold wave phase
  fun_prop

private theorem wave_norm_integral (d : ℤ) (hd : 0 < d) :
    (∫ θ in 0..2*Real.pi, ‖wave ((d:ℝ)*θ)‖) = 8 := by
  have hp : Periodic (fun t => ‖wave t‖) (2*Real.pi) := fun t => congrArg norm (wave_periodic t)
  rw [integral_period_dilate _ hp (fun a b => continuous_wave.norm.intervalIntegrable a b) d hd]
  have hsym : (∫ θ in 0..2*Real.pi, ‖wave θ‖) = ∫ θ in (-Real.pi)..Real.pi, ‖wave θ‖ := by
    simpa only [zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] using hp.intervalIntegral_add_eq 0 (-Real.pi)
  rw [hsym]
  have hcell : (∫ t in (-Real.pi)..Real.pi, ‖wave t‖) =
      ∫ t in (-Real.pi)..Real.pi, 2 * Real.cos (t/2) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact fun _ ht => norm_wave_on_cell ht
  rw [hcell,intervalIntegral.integral_const_mul]
  have hscale := intervalIntegral.integral_comp_mul_left Real.cos
    (show (1/2:ℝ) ≠ 0 by norm_num) (a := -Real.pi) (b := Real.pi)
  simp only [smul_eq_mul] at hscale
  simp only [show (fun t : ℝ => Real.cos (t/2)) = (fun t => Real.cos ((1/2)*t)) by
    funext t; congr 1; ring]
  rw [hscale,integral_cos]
  rw [show (1/2:ℝ)*Real.pi=Real.pi/2 by ring,show (1/2:ℝ)*(-Real.pi)=-(Real.pi/2) by ring]
  simp [Real.sin_pi_div_two]
  norm_num

private def cutoff (s x : ℝ) : ℝ := max 0 (1 - ‖wave x‖ / s)

private theorem cutoff_continuous (s : ℝ) : Continuous (cutoff s) := by
  unfold cutoff
  exact continuous_const.max (continuous_const.sub (continuous_wave.norm.div_const s))

private theorem cutoff_le_one (s : ℝ) (hs : 0 < s) (x : ℝ) : cutoff s x ≤ 1 := by
  apply max_le zero_le_one
  linarith [div_nonneg (norm_nonneg (wave x)) hs.le]

private theorem wave_norm_lower {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    2/Real.pi*(Real.pi-|x|) ≤ ‖wave x‖ := by
  have hab : |x| ≤ Real.pi := abs_le.2 hx
  have h := Real.mul_le_sin (x := (Real.pi-|x|)/2) (by linarith) (by linarith [abs_nonneg x])
  have he : Real.sin ((Real.pi-|x|)/2) = Real.cos (x/2) := by
    rw [show (Real.pi-|x|)/2=Real.pi/2-|x/2| by
      rw [abs_div,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]; ring,
      Real.sin_pi_div_two_sub,Real.cos_abs]
  rw [he] at h
  rw [norm_wave_on_cell hx]
  calc
    _ = 2*(2/Real.pi*((Real.pi-|x|)/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

private theorem cutoff_mean_bound (d : ℤ) (hd : 0 < d) (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1/2) :
    (∫ θ in 0..2*Real.pi, cutoff s ((d:ℝ)*θ)) ≤ (2*Real.pi)*s := by
  have hp : Periodic (cutoff s) (2*Real.pi) := by
    intro x
    simp only [cutoff,wave_periodic x]
  have hi (a b : ℝ) : IntervalIntegrable (cutoff s) volume a b :=
    (cutoff_continuous s).intervalIntegrable a b
  rw [integral_period_dilate _ hp hi d hd]
  have hsym : (∫ θ in 0..2*Real.pi, cutoff s θ) = ∫ θ in (-Real.pi)..Real.pi, cutoff s θ := by
    simpa only [zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] using hp.intervalIntegral_add_eq 0 (-Real.pi)
  rw [hsym]
  let w := Real.pi*s
  let a := -Real.pi+w
  let b := Real.pi-w
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw' : 2*w ≤ Real.pi := by dsimp [w]; nlinarith [Real.pi_pos]
  have ha : -Real.pi ≤ a := by dsimp [a]; linarith
  have hb : b ≤ Real.pi := by dsimp [b]; linarith
  have hab : a ≤ b := by dsimp [a,b]; linarith [Real.pi_pos]
  have hzero (x : ℝ) (hx : x ∈ Icc a b) : cutoff s x = 0 := by
    have hxc : x ∈ Icc (-Real.pi) Real.pi := ⟨ha.trans hx.1,hx.2.trans hb⟩
    have hxx : |x| ≤ Real.pi-w := abs_le.2 ⟨by dsimp [a] at hx; linarith only [hx.1],hx.2⟩
    have hn := (mul_le_mul_of_nonneg_left (sub_le_sub_left hxx Real.pi)
      (by positivity : 0 ≤ 2/Real.pi)).trans (wave_norm_lower hxc)
    have hden : 2/Real.pi*(Real.pi-(Real.pi-w)) = 2*s := by
      dsimp [w]
      field_simp [Real.pi_ne_zero]
      ring
    rw [hden] at hn
    unfold cutoff
    exact max_eq_left (by
      have hq := (le_div_iff₀ hs).2 (by linarith : 1*s ≤ ‖wave x‖)
      linarith)
  have hmid : (∫ x in a..b, cutoff s x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    exact hzero
  have h₁ : (∫ x in (-Real.pi)..a, cutoff s x) ≤ w := by
    have h := intervalIntegral.integral_mono_on ha (hi _ _) intervalIntegrable_const
      (fun x _ => cutoff_le_one s hs x)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one,show a-(-Real.pi)=w by dsimp [a]; ring] using h
  have h₂ : (∫ x in b..Real.pi, cutoff s x) ≤ w := by
    have h := intervalIntegral.integral_mono_on hb (hi _ _) intervalIntegrable_const
      (fun x _ => cutoff_le_one s hs x)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one,show Real.pi-b=w by dsimp [b]; ring] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-Real.pi) b) (hi b Real.pi),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-Real.pi) a) (hi a b),hmid,add_zero]
  calc
    _ ≤ w+w := add_le_add h₁ h₂
    _ = _ := by dsimp [w]; ring

private theorem deficit_weighted (x : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖wave x‖ * ‖z-ideal x‖^2 ≤ 2*(‖wave x‖ - (wave x*z).re) := by
  by_cases h : wave x = 0
  · simp [h]
  have hwp : 0 < ‖wave x‖ := norm_pos_iff.mpr h
  have hni : ‖ideal x‖ = 1 := by
    unfold ideal
    simp [hwp.ne']
  have he : (z * conj (ideal x)).re = (wave x*z).re / ‖wave x‖ := by
    unfold ideal
    simp only [map_div₀,starRingEnd_self_apply,conj_ofReal]
    rw [mul_comm z,div_mul_eq_mul_div₀,Complex.div_ofReal_re]
  have hsq : ‖z-ideal x‖^2 = ‖z‖^2+1-2*((wave x*z).re / ‖wave x‖) := by
    rw [← normSq_eq_norm_sq,normSq_sub,normSq_eq_norm_sq,normSq_eq_norm_sq,hni,one_pow,he]
  have hz' : ‖z‖^2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz) (add_nonneg (norm_nonneg z) zero_le_one)]
  rw [hsq]
  calc
    _ ≤ ‖wave x‖ * (1+1-2*((wave x*z).re / ‖wave x‖)) := by
      apply mul_le_mul_of_nonneg_left _ hwp.le
      linarith
    _ = _ := by field_simp [hwp.ne']; ring

private theorem cutoff_pointwise (x : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z-ideal x‖ ≤ 1/400 + 200000000 * (‖wave x‖-(wave x*z).re) +
      400*cutoff (1/1000000) x := by
  let s : ℝ := 1/1000000
  let a := ‖z-ideal x‖
  let W := ‖wave x‖
  let D := W-(wave x*z).re
  have ha : 0 ≤ a := norm_nonneg _
  have ha' : a ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [ideal_norm_le x])
  have hW : 0 ≤ W := norm_nonneg _
  have hs : 0 < s := by dsimp [s]; norm_num
  have hD : W*a^2 ≤ 2*D := deficit_weighted x z hz
  have hasq : a^2 ≤ 4 := by nlinarith only [mul_nonneg (sub_nonneg.mpr ha') (by linarith : 0 ≤ a+2)]
  have hcut : 1-min 1 (W/s) = cutoff s x := by
    unfold cutoff W
    rcases le_total 1 (‖wave x‖/s) with hh | hh
    · rw [min_eq_left hh,max_eq_left (by linarith)]
      norm_num
    · rw [min_eq_right hh,max_eq_right (by linarith)]
  have hin : a^2 ≤ 2*D/s+4*cutoff s x := by
    calc
      a^2 = min 1 (W/s)*a^2 + (1-min 1 (W/s))*a^2 := by ring
      _ ≤ (W/s)*a^2 + (1-min 1 (W/s))*4 :=
        add_le_add (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hasq (sub_nonneg.mpr (min_le_left _ _)))
      _ ≤ _ := by
        rw [hcut]
        have h := div_le_div_of_nonneg_right hD hs.le
        calc
          _ = (W*a^2)/s + cutoff s x*4 := by ring
          _ ≤ (2*D)/s + cutoff s x*4 := add_le_add h (le_refl _)
          _ = _ := by ring
  change a ≤ _
  change a ≤ 1/400 + 200000000*D + 400*cutoff s x
  dsimp [s] at hin
  nlinarith only [hin, sq_nonneg (a-1/200)]

private theorem integral_wave_g (g : ℝ → ℂ) (hg : Continuous g) (d : ℤ) (q : ℝ)
    (h0 : meanCoeff g 0 = (q:ℂ)) (h1 : meanCoeff g (-d) = (q:ℂ)) :
    (∫ θ in 0..2*Real.pi, wave ((d:ℝ)*θ)*g θ) = ((2*Real.pi)*(2*q):ℝ) := by
  let T := 2*Real.pi
  have hT : (T:ℂ) ≠ 0 := ofReal_ne_zero.mpr (by dsimp [T]; positivity)
  have scale (k : ℤ) (h : meanCoeff g k = (q:ℂ)) :
      (∫ θ in 0..T, g θ * phase (-(k:ℝ)*θ)) = (T:ℂ)*(q:ℂ) := by
    change (T:ℂ)⁻¹ * (∫ θ in 0..T, g θ*phase (-(k:ℝ)*θ)) = (q:ℂ) at h
    rw [← h, ← mul_assoc,mul_inv_cancel₀ hT,one_mul]
  have hA := scale 0 h0
  have hB := scale (-d) h1
  have hA' : (∫ θ in 0..T, g θ) = (T:ℂ)*(q:ℂ) := by
    simpa [phase] using hA
  have hB' : (∫ θ in 0..T, phase ((d:ℝ)*θ)*g θ) = (T:ℂ)*(q:ℂ) := by
    simpa only [Int.cast_neg,neg_neg,mul_comm] using hB
  have hC : Continuous fun θ => phase ((d:ℝ)*θ)*g θ := by
    unfold phase
    fun_prop
  change (∫ θ in 0..T, wave ((d:ℝ)*θ)*g θ) = ((T*(2*q):ℝ):ℂ)
  simp only [wave,add_mul,one_mul]
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hC.intervalIntegrable _ _),hA', hB']
  push_cast
  ring

private theorem relative_profile_bounds (d k : ℤ) : 0 ≤ profile 0 d k ∧ profile 0 d k ≤ 1 := by
  unfold profile
  split
  · simp only [sub_zero]
    have hpos : (0:ℤ) < |2*(k/d)+1| := abs_pos.2 (by omega)
    have hge : (1:ℝ) ≤ ((|2*(k/d)+1| : ℤ):ℝ) := by
      exact_mod_cast (show 1 ≤ |2*(k/d)+1| by omega)
    exact ⟨by positivity, (div_le_iff₀ (by positivity)).2 (by simpa only [one_mul] using hge)⟩
  · norm_num

private theorem ideal_profile (d k : ℤ) (hd : 0 < d) :
    ‖meanCoeff (fun θ => ideal ((d:ℝ)*θ)) k‖ = (2/Real.pi)*profile 0 d k := by
  rw [ideal_dilate_coeff_norm d k hd]
  by_cases h : d ∣ k <;> simp only [profile,sub_zero,h,if_true,if_false,Int.cast_abs,div_eq_mul_inv,
    one_mul,mul_zero]

set_option maxHeartbeats 1600000 in
/-- Near equality in the two tied coefficient bound forces the full ideal coefficient profile. -/
theorem profile_stability (g : ℝ → ℂ) (d : ℤ) (q : ℝ)
    (hg : Continuous g) (_hper : Periodic g (2*Real.pi)) (hgNorm : ∀ θ, ‖g θ‖ ≤ 1)
    (h0 : meanCoeff g 0 = (q:ℂ)) (h1 : meanCoeff g (-d) = (q:ℂ))
    (hd : 0 < d) (hq : 2/Real.pi - 1/1000000000000 < q) :
    ∀ k, |‖meanCoeff g k‖ / q - profile 0 d k| ≤ 1/100 := by
  let T := 2*Real.pi
  have hTp : 0 < T := by dsimp [T]; positivity
  let g' := fun θ : ℝ => ideal ((d:ℝ)*θ)
  let A := fun θ : ℝ => ‖g θ - g' θ‖
  let W := fun θ : ℝ => wave ((d:ℝ)*θ)
  let D := fun θ : ℝ => ‖W θ‖-(W θ*g θ).re
  let C := fun θ : ℝ => cutoff (1/1000000) ((d:ℝ)*θ)
  have hWM : Continuous W := continuous_wave.comp (continuous_const.mul continuous_id)
  have hWMG : Continuous (fun θ => W θ*g θ) := hWM.mul hg
  have hD : Continuous D := hWM.norm.sub (Complex.continuous_re.comp hWMG)
  have hC : Continuous C := (cutoff_continuous _).comp (continuous_const.mul continuous_id)
  have hg'N (θ : ℝ) : ‖g' θ‖ ≤ 1 := ideal_norm_le _
  have hg'M : Measurable g' := measurable_ideal.comp (measurable_const.mul measurable_id)
  have hAN (θ : ℝ) : A θ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hgNorm θ,hg'N θ])
  have hAI : IntervalIntegrable A volume 0 T := by
    apply (intervalIntegrable_const (c := (2:ℝ))).mono_fun'
      ((hg.measurable.sub hg'M).norm.aestronglyMeasurable)
    filter_upwards with θ
    change ‖A θ‖ ≤ 2
    rw [Real.norm_of_nonneg (norm_nonneg (g θ-g' θ))]
    exact hAN θ
  have hdInt : (∫ θ in 0..T, D θ) = 8 - T*(2*q) := by
    unfold D
    have hWI : IntervalIntegrable (fun θ => ‖W θ‖) volume 0 T :=
      hWM.norm.intervalIntegrable _ _
    have hRI : IntervalIntegrable (fun θ => (W θ*g θ).re) volume 0 T :=
      (Complex.continuous_re.comp hWMG).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hWI hRI]
    have hm := Complex.reCLM.intervalIntegral_comp_comm (hWMG.intervalIntegrable (μ := volume) 0 T)
    change (∫ θ in 0..T, (W θ*g θ).re) = (∫ θ in 0..T, W θ*g θ).re at hm
    rw [hm, integral_wave_g g hg d q h0 h1, ofReal_re]
    rw [wave_norm_integral d hd]
  have hD0 : 0 ≤ ∫ θ in 0..T, D θ := by
    apply intervalIntegral.integral_nonneg hTp.le
    intro θ _
    have hle : (W θ*g θ).re ≤ ‖W θ‖ := calc
      _ ≤ ‖W θ*g θ‖ := Complex.re_le_norm _
      _ = ‖W θ‖*‖g θ‖ := norm_mul _ _
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hgNorm θ) (norm_nonneg (W θ))
    exact sub_nonneg.mpr hle
  have h8 : T * (2*(2/Real.pi)) = 8 := by dsimp [T]; field_simp [Real.pi_ne_zero]; ring
  have hqu : q ≤ 2/Real.pi := by
    rw [hdInt, ← h8, sub_nonneg] at hD0
    nlinarith [le_of_mul_le_mul_left hD0 hTp]
  have hDupper : (∫ θ in 0..T, D θ) ≤ T*(2/1000000000000) := by
    rw [hdInt,← h8]
    have hq' := mul_lt_mul_of_pos_left hq hTp
    linarith
  have hCupper : (∫ θ in 0..T, C θ) ≤ T*(1/1000000) :=
    cutoff_mean_bound d hd _ (by norm_num) (by norm_num)
  have hAupper : (∫ θ in 0..T, A θ) ≤ T*(33/10000) := by
    have hS : Continuous (fun θ => (1/400:ℝ)+200000000*D θ+400*C θ) :=
      (continuous_const.add (continuous_const.mul hD)).add (continuous_const.mul hC)
    have hi := intervalIntegral.integral_mono_on hTp.le hAI (hS.intervalIntegrable 0 T)
      (fun θ _ => cutoff_pointwise ((d:ℝ)*θ) (g θ) (hgNorm θ))
    have hDI : IntervalIntegrable (fun θ => (200000000:ℝ)*D θ) volume 0 T :=
      (continuous_const.mul hD).intervalIntegrable _ _
    have hCI : IntervalIntegrable (fun θ => (400:ℝ)*C θ) volume 0 T :=
      (continuous_const.mul hC).intervalIntegrable _ _
    have hSD : IntervalIntegrable (fun θ => (1/400:ℝ)+200000000*D θ) volume 0 T :=
      intervalIntegrable_const.add hDI
    rw [intervalIntegral.integral_add hSD hCI,
      intervalIntegral.integral_add intervalIntegrable_const hDI,
      intervalIntegral.integral_const,sub_zero,smul_eq_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hi
    linarith
  have hhalf : (1/2 : ℝ) ≤ 2/Real.pi :=
    (le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_four])
  have hqpos : 0 < q := by linarith
  intro k
  have hPhase : Continuous fun θ => phase (-(k:ℝ)*θ) := by unfold phase; fun_prop
  have hF : IntervalIntegrable (fun θ => g θ*phase (-(k:ℝ)*θ)) volume 0 T :=
    (hg.mul hPhase).intervalIntegrable _ _
  have hF' : IntervalIntegrable (fun θ => g' θ*phase (-(k:ℝ)*θ)) volume 0 T := by
    apply ideal_interval_integrable _ (hg'M.mul hPhase.measurable)
    intro θ
    change ‖g' θ * phase (-(k:ℝ)*θ)‖ ≤ 1
    simp only [norm_mul,phase_norm,mul_one]
    exact hg'N θ
  have hdist : ‖meanCoeff g k - meanCoeff g' k‖ ≤ 33/10000 := by
    unfold meanCoeff
    change ‖(T:ℂ)⁻¹ * (∫ θ in 0..T, g θ*phase (-(k:ℝ)*θ)) -
      (T:ℂ)⁻¹ * (∫ θ in 0..T, g' θ*phase (-(k:ℝ)*θ))‖ ≤ _
    rw [← mul_sub,← intervalIntegral.integral_sub hF hF',norm_mul,norm_inv,norm_real,
      Real.norm_eq_abs,abs_of_pos hTp]
    have hi := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun θ =>
      g θ * phase (-(k:ℝ)*θ) - g' θ * phase (-(k:ℝ)*θ)) hTp.le
    simp only [← sub_mul,norm_mul,phase_norm,mul_one] at hi
    simp only [← sub_mul]
    calc
      _ ≤ T⁻¹ * (∫ θ in 0..T, A θ) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hTp.le)
      _ ≤ T⁻¹ * (T*(33/10000)) := mul_le_mul_of_nonneg_left hAupper (inv_nonneg.mpr hTp.le)
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hTp.ne',one_mul]
  have hnorm := (abs_norm_sub_norm_le (meanCoeff g k) (meanCoeff g' k)).trans hdist
  rw [show ‖meanCoeff g' k‖ = (2/Real.pi)*profile 0 d k from ideal_profile d k hd] at hnorm
  let y := profile 0 d k
  have hy := relative_profile_bounds d k
  have hy₁ : q*y ≤ (2/Real.pi)*y := mul_le_mul_of_nonneg_right hqu hy.1
  have hy₂ : (2/Real.pi)*y ≤ q*y+1/1000000000000 := by
    have hA : (2/Real.pi-q)*y ≤ (1/1000000000000)*y :=
      mul_le_mul_of_nonneg_right (by linarith : 2/Real.pi-q ≤ 1/1000000000000) hy.1
    have hB : (1/1000000000000:ℝ)*y ≤ 1/1000000000000 :=
      mul_le_of_le_one_right (by norm_num) hy.2
    linarith
  obtain ⟨hl,hr⟩ := abs_le.mp hnorm
  apply abs_le.mpr
  change -(1/100 : ℝ) ≤ ‖meanCoeff g k‖/q-y ∧ ‖meanCoeff g k‖/q-y ≤ 1/100
  constructor
  · rw [le_sub_iff_add_le,le_div_iff₀ hqpos]
    nlinarith only [hl,hy₁,hhalf,hq]
  · rw [sub_le_iff_le_add,div_le_iff₀ hqpos]
    nlinarith only [hr,hy₂,hhalf,hq]

end

end MaximumTerm
end

section
/- Maximal terms of a sequence of monomials and consecutive tie radii. -/

open Filter Set Finset
open scoped Topology Classical

namespace MaxTerm513

noncomputable section

def term (a : ℕ → ℝ) (r : ℝ) (n : ℕ) : ℝ := a n * r^n

def HasMaximum (a : ℕ → ℝ) (r : ℝ) (n : ℕ) : Prop :=
  ∀ k, term a r k ≤ term a r n

def Decays (a : ℕ → ℝ) : Prop :=
  ∀ r > 0, Tendsto (fun n => term a r n) atTop (𝓝 0)

def UnboundedSupport (a : ℕ → ℝ) : Prop :=
  ∀ n, ∃ k > n, 0 < a k

theorem term_continuous (a : ℕ → ℝ) (n : ℕ) : Continuous fun r => term a r n := by
  unfold term
  fun_prop

theorem maximum_positive {a : ℕ → ℝ} (hs : UnboundedSupport a) {r : ℝ} (hr : 0 < r)
    {n : ℕ} (h : HasMaximum a r n) : 0 < term a r n := by
  obtain ⟨k,_,hk⟩ := hs n
  exact (show 0 < term a r k from mul_pos hk (pow_pos hr _)).trans_le (h k)

theorem maximum_coeff_positive {a : ℕ → ℝ} (hs : UnboundedSupport a) {r : ℝ} (hr : 0 < r)
    {n : ℕ} (h : HasMaximum a r n) : 0 < a n :=
  pos_of_mul_pos_left (maximum_positive hs hr h) (pow_nonneg hr.le _)

theorem exists_largest {a : ℕ → ℝ} (ht : Decays a) (hs : UnboundedSupport a)
    {r : ℝ} (hr : 0 < r) :
    ∃ n, HasMaximum a r n ∧ ∀ k, HasMaximum a r k → k ≤ n := by
  obtain ⟨k,_,hk⟩ := hs 0
  have hp : 0 < term a r k := mul_pos hk (pow_pos hr _)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht r hr (Iio_mem_nhds hp))
  have hkN : k < N := by
    by_contra! hn
    exact (lt_irrefl (term a r k)) (hN k hn)
  obtain ⟨u,hu,humax⟩ := Finset.exists_max_image (range N) (term a r) ⟨k,mem_range.mpr hkN⟩
  have hmax : HasMaximum a r u := by
    intro j
    by_cases hj : j < N
    · exact humax j (mem_range.mpr hj)
    · exact ((hN _ (le_of_not_gt hj)).trans_le (humax _ (mem_range.mpr hkN))).le
  let S := (range N).filter (HasMaximum a r)
  have hS : S.Nonempty := ⟨u,mem_filter.mpr ⟨hu,hmax⟩⟩
  refine ⟨S.max' hS,(mem_filter.mp (S.max'_mem hS)).2,?_⟩
  intro j hj
  have hjN : j < N := by
    by_contra! hn
    exact (not_lt_of_ge (hj k)) (hN j hn)
  exact S.le_max' j (mem_filter.mpr ⟨mem_range.mpr hjN,hj⟩)

private theorem split_power {a : ℕ → ℝ} {r : ℝ} (hr : 0 < r) {i j : ℕ} (hij : i ≤ j) :
    term a r i ≤ term a r j ↔ a i ≤ a j * r^(j-i) := by
  unfold term
  rw [show r^j = r^(j-i)*r^i from by rw [← pow_add,Nat.sub_add_cancel hij],← mul_assoc]
  exact mul_le_mul_iff_of_pos_right (pow_pos hr _)

private theorem split_power_strict {a : ℕ → ℝ} {r : ℝ} (hr : 0 < r) {i j : ℕ} (hij : i ≤ j) :
    term a r i < term a r j ↔ a i < a j * r^(j-i) := by
  unfold term
  rw [show r^j = r^(j-i)*r^i from by rw [← pow_add,Nat.sub_add_cancel hij],← mul_assoc]
  exact mul_lt_mul_iff_of_pos_right (pow_pos hr _)

private theorem grows_past {a : ℕ → ℝ} (hs : UnboundedSupport a) (n : ℕ) (R : ℝ) :
    ∃ S > R, ∀ r ≥ S, ¬HasMaximum a r n := by
  obtain ⟨k,hkn,hk⟩ := hs n
  let S := max (R+1) (max 1 (a n/a k+1))
  refine ⟨S,lt_of_lt_of_le (by linarith) (le_max_left _ _),?_⟩
  intro r hr h
  have h1 : 1 ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have h2 : a n/a k+1 ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have hp : 0 < r := by linarith
  have hpow : r ≤ r^(k-n) := le_self_pow₀ h1 (by omega)
  have hh : a n < a k * r^(k-n) := by
    have hr' : a n/a k < r := by linarith
    have hh := (div_lt_iff₀ hk).mp hr'
    rw [mul_comm r (a k)] at hh
    exact hh.trans_le (mul_le_mul_of_nonneg_left hpow hk.le)
  exact (not_lt_of_ge (h k)) ((split_power_strict hp hkn.le).mpr hh)

private theorem exists_maximum_right {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (ht : Decays a)
    (hs : UnboundedSupport a) {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hn : HasMaximum a r n) (hl : ∀ j, HasMaximum a r j → j ≤ n) :
    ∃ s > r, HasMaximum a s n := by
  have hpos := maximum_positive hs hr hn
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht (r+1) (by linarith) (Iio_mem_nhds hpos))
  let J := (range N).filter (fun k => n < k)
  have he : ∀ᶠ s in 𝓝 r, ∀ k ∈ J, term a s k < term a s n := by
    rw [Filter.eventually_all_finset]
    intro k hk
    have hk' := (mem_filter.mp hk).2
    have hlt : term a r k < term a r n := by
      apply lt_of_le_of_ne (hn k)
      intro h
      have hm : HasMaximum a r k := fun j => h.symm ▸ hn j
      exact (not_le_of_gt hk') (hl k hm)
    exact (isOpen_lt (term_continuous a k) (term_continuous a n)).mem_nhds hlt
  obtain ⟨ε,he0,hε⟩ := Metric.mem_nhds_iff.mp he
  let s := r + min (ε/2) (1/2)
  have hslt : r < s := by have : 0 < min (ε/2) (1/2:ℝ) := lt_min (by linarith) (by norm_num); dsimp [s]; linarith
  have hsr : s ≤ r+1 := by have := min_le_right (ε/2) (1/2:ℝ); dsimp [s]; linarith
  have hse : s ∈ Metric.ball r ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hslt.le)]
    have := min_le_left (ε/2) (1/2:ℝ)
    dsimp [s]
    linarith
  have hs0 : 0 < s := hr.trans hslt
  refine ⟨s,hslt,?_⟩
  intro k
  by_cases hkn : k ≤ n
  · apply (split_power hs0 hkn).mpr
    exact ((split_power hr hkn).mp (hn k)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hslt.le _) (ha n))
  · by_cases hk : k < N
    · exact (hε hse k (mem_filter.mpr ⟨mem_range.mpr hk,lt_of_not_ge hkn⟩)).le
    · exact (calc
        term a s k ≤ term a (r+1) k := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hs0.le hsr _) (ha k)
        _ < term a r n := hN _ (le_of_not_gt hk)
        _ ≤ term a s n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hslt.le _) (ha n)).le

private theorem edge_tie {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (ht : Decays a)
    (hs : UnboundedSupport a) {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : HasMaximum a R n) (hL : ∀ k, HasMaximum a R k → k ≤ n) :
    ∃ r > R, ∃ m > n, HasMaximum a r n ∧ HasMaximum a r m ∧
      ∀ k, HasMaximum a r k → k ≤ m := by
  let A := Set.Ici R ∩ {r : ℝ | HasMaximum a r n}
  have hA : IsClosed A := by
    apply isClosed_Ici.inter
    rw [show {r : ℝ | HasMaximum a r n} = ⋂ k : ℕ, {r | term a r k ≤ term a r n} from by
      ext r; simp [HasMaximum]]
    exact isClosed_iInter fun k => isClosed_le (term_continuous a k) (term_continuous a n)
  have hAN : A.Nonempty := ⟨R,Set.mem_Ici.mpr le_rfl,hn⟩
  obtain ⟨S,_,hS⟩ := grows_past hs n R
  have hb : BddAbove A := ⟨S,fun r hr => le_of_not_ge (fun hr' => hS _ hr' hr.2)⟩
  let r := sSup A
  have hr : r ∈ A := hA.csSup_mem hAN hb
  obtain ⟨T,hT,hTm⟩ := exists_maximum_right ha ht hs hR hn hL
  have hRr : R < r := hT.trans_le (le_csSup hb ⟨hT.le,hTm⟩)
  obtain ⟨m,hm,hmL⟩ := exists_largest ht hs (hR.trans hRr)
  refine ⟨r,hRr,m,?_ ,hr.2,hm,hmL⟩
  have hnm : n ≤ m := hmL _ hr.2
  by_contra! hmn
  have he : m=n := le_antisymm hmn hnm
  subst m
  obtain ⟨u,hu,hum⟩ := exists_maximum_right ha ht hs (hR.trans hRr) hm hmL
  exact (not_lt_of_ge (le_csSup hb ⟨(hRr.trans hu).le,hum⟩)) hu

theorem two_ties {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (ht : Decays a) (hs : UnboundedSupport a)
    {R : ℝ} (hR : 0 < R) :
    ∃ (r s : ℝ) (n m p : ℕ), R < r ∧ r < s ∧ n < m ∧ m < p ∧
      HasMaximum a r n ∧ HasMaximum a r m ∧ HasMaximum a s m ∧ HasMaximum a s p := by
  obtain ⟨n,hn,hnL⟩ := exists_largest ht hs hR
  obtain ⟨r,hRr,m,hnm,hnr,hmr,hmL⟩ := edge_tie ha ht hs hR hn hnL
  obtain ⟨s,hrs,p,hmp,hms,hps,_⟩ := edge_tie ha ht hs (hR.trans hRr) hmr hmL
  exact ⟨r,s,n,m,p,hRr,hrs,hnm,hmp,hnr,hmr,hms,hps⟩

end

end MaxTerm513

namespace MaxTerm513

open Polynomial
open scoped Nat

noncomputable section

def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 * (n ! : ℂ)⁻¹

def maxMod (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

theorem taylor_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n => coeff f n * z^n) (f z) := by
  simpa only [coeff,sub_zero,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using
    (Complex.hasSum_taylorSeries_of_entire hf 0 z)

theorem coeff_decays {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Decays (fun n => ‖coeff f n‖) := by
  intro r hr
  have h := (taylor_hasSum hf (r:ℂ)).summable.tendsto_atTop_zero.norm
  simpa only [norm_zero,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le,term] using h

theorem coeff_unbounded {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htr : Transcendental ℂ[X] f) : UnboundedSupport (fun n => ‖coeff f n‖) := by
  intro n
  by_contra! hz
  have hzero (k : ℕ) (hk : n < k) : coeff f k = 0 :=
    norm_eq_zero.mp (le_antisymm (hz k hk) (norm_nonneg _))
  let p : ℂ[X] := ∑ k ∈ range (n+1), C (coeff f k)*X^k
  have hpoly : f = algebraMap ℂ[X] (ℂ→ℂ) p := by
    funext z
    rw [Polynomial.algebraMap_algebraPi,show p = ∑ k ∈ range (n+1), C (coeff f k)*X^k from rfl,
      map_sum]
    simp only [map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,
      Algebra.algebraMap_self_apply]
    rw [← (taylor_hasSum hf z).tsum_eq]
    exact tsum_eq_sum (fun k hk => by
      rw [hzero k (by simpa only [Finset.mem_range,not_lt,Nat.succ_le_iff] using hk),zero_mul])
  apply htr
  rw [hpoly]
  exact isAlgebraic_algebraMap p

theorem entire_two_ties {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (htr : Transcendental ℂ[X] f) {R : ℝ} (hR : 0 < R) :
    ∃ (r s : ℝ) (n m p : ℕ), R < r ∧ r < s ∧ n < m ∧ m < p ∧
      HasMaximum (fun j => ‖coeff f j‖) r n ∧ HasMaximum (fun j => ‖coeff f j‖) r m ∧
      HasMaximum (fun j => ‖coeff f j‖) s m ∧ HasMaximum (fun j => ‖coeff f j‖) s p :=
  two_ties (fun _ => norm_nonneg _) (coeff_decays hf) (coeff_unbounded hf htr) hR

theorem maximum_eq_iSup {a : ℕ→ℝ} {r : ℝ} {n : ℕ} (h : HasMaximum a r n) :
    (⨆ k, term a r k) = term a r n :=
  le_antisymm (ciSup_le h) (le_ciSup ⟨term a r n,fun _ ⟨k,hk⟩ => hk ▸ h k⟩ n)

theorem maximum_ratio {f : ℂ→ℂ} {r : ℝ} (hr : 0 ≤ r) {n : ℕ}
    (h : HasMaximum (fun j => ‖coeff f j‖) r n) :
    Erdos513.ratio r f = term (fun j => ‖coeff f j‖) r n / maxMod f r := by
  unfold Erdos513.ratio maxMod
  have he (k : ℕ) : ‖iteratedDeriv k f 0 * (k ! : ℝ)⁻¹ * r^k‖ =
      term (fun j => ‖coeff f j‖) r k := by
    push_cast
    change ‖coeff f k * (r:ℂ)^k‖ = _
    simp only [term,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr]
  simp_rw [he]
  rw [maximum_eq_iSup h]

theorem maxMod_bdd {f : ℂ→ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    BddAbove (Set.range fun z : {z : ℂ // ‖z‖=r} => ‖f z‖) := by
  have hc : IsCompact {z : ℂ | ‖z‖ = r} := by
    convert isCompact_sphere (0:ℂ) r using 1
    ext z
    simp
  obtain ⟨C,hC⟩ := (hc.image hf.continuous.norm).bddAbove
  refine ⟨C,?_⟩
  rintro _ ⟨z,rfl⟩
  exact hC ⟨z.val,z.property,rfl⟩

theorem norm_le_maxMod {f : ℂ→ℂ} (hf : Differentiable ℂ f) {r : ℝ} {z : ℂ}
    (hz : ‖z‖=r) : ‖f z‖ ≤ maxMod f r :=
  le_ciSup (maxMod_bdd hf r) ⟨z,hz⟩

theorem coeff_le_maxMod {f : ℂ→ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0<r) (n : ℕ) :
    term (fun j => ‖coeff f j‖) r n ≤ maxMod f r := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (c := 0) (C := maxMod f r) hf.diffContOnCl
    (fun z hz => norm_le_maxMod hf (by simpa only [Metric.mem_sphere,dist_zero_right] using hz))
  have hF : 0 < (n ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have h' := (le_div_iff₀ (pow_pos hr n)).mp h
  simp only [term,coeff,norm_mul,norm_inv,Complex.norm_natCast]
  rw [← div_eq_mul_inv,div_mul_eq_mul_div]
  exact (div_le_iff₀ hF).mpr (by simpa only [mul_comm] using h')

theorem summable_terms {f : ℂ→ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) :
    Summable (fun n => term (fun j => ‖coeff f j‖) r n) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _)) ?_
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).mul_left (maxMod f (2*r)))
  intro n
  rw [div_pow,one_pow,mul_one_div]
  apply (le_div_iff₀ (pow_pos (by norm_num) _)).mpr
  simpa only [term,mul_pow,mul_assoc,mul_comm,mul_left_comm] using coeff_le_maxMod hf (by linarith : 0 < 2*r) n

theorem ratio_bounds {f : ℂ→ℂ} (hf : Differentiable ℂ f)
    (htr : Transcendental ℂ[X] f) {r : ℝ} (hr : 0 < r) :
    0 ≤ Erdos513.ratio r f ∧ Erdos513.ratio r f ≤ 1 := by
  have ht := coeff_unbounded hf htr
  obtain ⟨n,hn,_⟩ := exists_largest (coeff_decays hf) ht hr
  rw [maximum_ratio hr.le hn]
  have hp := maximum_positive ht hr hn
  have hm := coeff_le_maxMod hf hr n
  have hM := hp.trans_le hm
  exact ⟨div_nonneg hp.le hM.le,(div_le_one₀ hM).mpr hm⟩

theorem maxTermConstant_le_of_frequently {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (f : ℂ→ℂ), Transcendental ℂ[X] f → Differentiable ℂ f →
      ∃ᶠ r in atTop, Erdos513.ratio r f ≤ C) : Erdos513.maxTermConstant ≤ C := by
  let T := {f : ℂ→ℂ // Transcendental ℂ[X] f ∧ Differentiable ℂ f}
  by_cases hT : Nonempty T
  · let : Nonempty T := hT
    change (⨆ f : T, liminf (fun r : ℝ => Erdos513.ratio r f) atTop) ≤ C
    apply ciSup_le
    intro f
    refine liminf_le_of_frequently_le (h f f.property.1 f.property.2) ?_
    exact isBoundedUnder_of_eventually_ge ((eventually_gt_atTop (0:ℝ)).mono fun r hr =>
      (ratio_bounds f.property.2 f.property.1 hr).1)
  · let : IsEmpty T := not_nonempty_iff.mp hT
    change (⨆ f : T, liminf (fun r : ℝ => Erdos513.ratio r f) atTop) ≤ C
    simpa using hC


theorem maxTermConstant_le_of_ties {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (f : ℂ→ℂ), Transcendental ℂ[X] f → Differentiable ℂ f →
      ∀ (r s : ℝ) (n m p : ℕ), 0 < r → r < s → n < m → m < p →
        HasMaximum (fun j => ‖coeff f j‖) r n → HasMaximum (fun j => ‖coeff f j‖) r m →
        HasMaximum (fun j => ‖coeff f j‖) s m → HasMaximum (fun j => ‖coeff f j‖) s p →
        Erdos513.ratio r f ≤ C ∨ Erdos513.ratio s f ≤ C) : Erdos513.maxTermConstant ≤ C := by
  apply maxTermConstant_le_of_frequently hC
  intro f htr hf
  rw [Filter.frequently_atTop]
  intro R
  let R' := max R 1
  have hR : (0:ℝ) < R' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨r,s,n,m,p,hRr,hrs,hnm,hmp,hnr,hmr,hms,hps⟩ := entire_two_ties hf htr hR
  have hr := hR.trans hRr
  have hRr' := (le_max_left R 1).trans hRr.le
  rcases h f htr hf r s n m p hr hrs hnm hmp hnr hmr hms hps with h₁ | h₂
  · exact ⟨r,hRr',h₁⟩
  · exact ⟨s,hRr'.trans hrs.le,h₂⟩

end

end MaxTerm513
end

section
namespace MaximumTerm

open Complex MeasureTheory
open scoped Interval Topology

noncomputable section

private theorem transport_phase_pow (x : ℝ) (n : ℕ) :
    phase x ^ n = phase ((n:ℝ)*x) := by
  unfold phase
  rw [← Complex.exp_nat_mul,Complex.ofReal_mul,Complex.ofReal_natCast,mul_assoc]

private theorem transport_continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

private theorem transport_integral_phase (j : ℤ) :
    (∫ θ in (0:ℝ)..2*Real.pi, phase ((j:ℝ)*θ)) =
      if j=0 then ((2*Real.pi : ℝ):ℂ) else 0 := by
  by_cases hj : j=0
  · subst j
    simp [phase,intervalIntegral.integral_const,Complex.real_smul]
  · rw [if_neg hj]
    have h0 : (j:ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
    have he (x : ℝ) : phase ((j:ℝ)*x) = Complex.exp (((j:ℂ)*Complex.I)*(x:ℂ)) := by
      unfold phase
      push_cast
      congr 1
      ring
    simp_rw [he]
    rw [integral_exp_mul_complex h0]
    have hh : Complex.exp (((j:ℂ) * Complex.I) * ((2*Real.pi:ℝ):ℂ)) = 1 := by
      simpa only [← he] using integer_period_phase j
    rw [hh,Complex.ofReal_zero,mul_zero,Complex.exp_zero,sub_self,zero_div]

/-- Rotation, modulation and scaling of an entire function transport its actual Taylor coefficients. -/
theorem meanCoeff_entire {f : ℂ→ℂ} (hf : Differentiable ℂ f) (c w : ℂ)
    (hw : 0 < ‖w‖) (m k : ℤ) :
    meanCoeff (fun θ => c * phase (-(m:ℝ)*θ) * f (w*phase θ)) k =
      if 0 ≤ m+k then c * MaxTerm513.coeff f (m+k).toNat * w^(m+k).toNat else 0 := by
  let b (n : ℕ) := c * MaxTerm513.coeff f n * w^n
  let F (n : ℕ) (θ : ℝ) := b n * phase ((((n:ℤ)-m-k : ℤ):ℝ) * θ)
  have hF (θ : ℝ) :
      c * phase (-(m:ℝ)*θ) * f (w*phase θ) * phase (-(k:ℝ)*θ) = ∑' n, F n θ := by
    let p := c * phase (-(m:ℝ)*θ) * phase (-(k:ℝ)*θ)
    have hf₀ := (MaxTerm513.taylor_hasSum hf (w*phase θ)).mul_left p
    have he (n : ℕ) : p * (MaxTerm513.coeff f n * (w*phase θ)^n) = F n θ := by
      dsimp [p,F,b]
      rw [mul_pow,transport_phase_pow]
      push_cast
      have hu : ((n:ℝ)-(m:ℝ)-(k:ℝ))*θ =
          -(m:ℝ)*θ + -(k:ℝ)*θ + (n:ℝ)*θ := by ring
      rw [hu]
      simp only [phase_add]
      ring
    have hs : HasSum (fun n => F n θ) (p*f (w*phase θ)) := by simpa only [he] using hf₀
    exact (by dsimp [p]; ring : _ = p*f (w*phase θ)) |>.trans hs.tsum_eq.symm
  let μ := volume.restrict (Set.Ioc 0 (2*Real.pi))
  have hI (n : ℕ) : Integrable (F n) μ := by
    have hcont : Continuous fun θ => F n θ :=
      continuous_const.mul (transport_continuous_phase.comp (continuous_const.mul continuous_id))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp
      (hcont.intervalIntegrable _ _)
  have hnorm (n : ℕ) (θ : ℝ) :
      ‖F n θ‖ = ‖c‖ * MaxTerm513.term (fun j => ‖MaxTerm513.coeff f j‖) ‖w‖ n := by
    simp only [F,b,norm_mul,phase_norm,mul_one,norm_pow,MaxTerm513.term,mul_assoc]
  have hInts : Summable fun n => ∫ θ, ‖F n θ‖ ∂μ := by
    simp_rw [hnorm,MeasureTheory.integral_const,smul_eq_mul]
    exact ((MaxTerm513.summable_terms hf hw).mul_left ‖c‖).mul_left (μ.real Set.univ)
  have hswap : (∫ θ in (0:ℝ)..2*Real.pi, ∑' n, F n θ) =
      ∑' n, ∫ θ in (0:ℝ)..2*Real.pi, F n θ := by
    simp only [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact (integral_tsum_of_summable_integral_norm hI hInts).symm
  have hfI (n : ℕ) : (∫ θ in (0:ℝ)..2*Real.pi, F n θ) =
      if (n:ℤ)=m+k then ((2*Real.pi:ℝ):ℂ) * b n else 0 := by
    have he : ((n:ℤ)-m-k=0) ↔ (n:ℤ)=m+k := by omega
    simp only [F,intervalIntegral.integral_const_mul,transport_integral_phase,he]
    split_ifs <;> simp [mul_comm]
  have hp : ((2*Real.pi:ℝ):ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  unfold meanCoeff
  simp_rw [hF,hswap,hfI]
  by_cases hz : 0 ≤ m+k
  · let i := (m+k).toNat
    have hi : (i:ℤ) = m+k := Int.toNat_of_nonneg hz
    rw [if_pos hz,tsum_eq_single i]
    · rw [if_pos hi]
      change ((2*Real.pi:ℝ):ℂ)⁻¹ * (((2*Real.pi:ℝ):ℂ) * b i) = b i
      rw [← mul_assoc,inv_mul_cancel₀ hp,one_mul]
    · intro n hn
      rw [if_neg (fun he => hn (Int.ofNat.inj (he.trans hi.symm)))]
  · rw [if_neg hz]
    have hzero (n : ℕ) : (n:ℤ) ≠ m+k := by omega
    simp [hzero]

/-- Center at either index of a maximal tie and choose phases making both tied coefficients positive. -/
theorem normalized_tie {f : ℂ→ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0<r)
    {m n : ℕ} (hne : n ≠ m)
    (hm : MaxTerm513.HasMaximum (fun j => ‖MaxTerm513.coeff f j‖) r m)
    (hn : MaxTerm513.HasMaximum (fun j => ‖MaxTerm513.coeff f j‖) r n)
    (hpos : 0 < MaxTerm513.term (fun j => ‖MaxTerm513.coeff f j‖) r m) :
    ∃ g : ℝ→ℂ, Continuous g ∧ Function.Periodic g (2*Real.pi) ∧
      (∀ θ, ‖g θ‖ ≤ 1) ∧
      meanCoeff g 0 = (Erdos513.ratio r f : ℂ) ∧
      meanCoeff g ((n:ℤ)-(m:ℤ)) = (Erdos513.ratio r f : ℂ) ∧
      ∀ k : ℤ, ‖meanCoeff g k‖ =
        if 0 ≤ (m:ℤ)+k then MaxTerm513.term (fun j => ‖MaxTerm513.coeff f j‖) r
          ((m:ℤ)+k).toNat / MaxTerm513.maxMod f r else 0 := by
  let M := MaxTerm513.maxMod f r
  have hM : 0 < M := hpos.trans_le (MaxTerm513.coeff_le_maxMod hf hr m)
  let Z (j : ℕ) := MaxTerm513.coeff f j * (r:ℂ)^j
  let α := (Z m).arg
  let β := (Z n).arg
  let t := (β-α)/((m:ℝ)-(n:ℝ))
  let w := (r:ℂ) * phase t
  let c := (M:ℂ)⁻¹ * phase (-(α+(m:ℝ)*t))
  let g (θ : ℝ) := c * phase (-(m:ℝ)*θ) * f (w*phase θ)
  have hw : ‖w‖ = r := by simp only [w,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg hr.le]
  have hc : ‖c‖ = M⁻¹ := by simp only [c,norm_mul,norm_inv,phase_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg hM.le]
  have hcont : Continuous g :=
    (continuous_const.mul (transport_continuous_phase.comp (continuous_const.mul continuous_id))).mul
      (hf.continuous.comp (continuous_const.mul transport_continuous_phase))
  have hperiod : Function.Periodic g (2*Real.pi) := by
    intro θ
    have h1 : phase (2*Real.pi)=1 := by
      simpa only [Int.cast_one,one_mul] using integer_period_phase 1
    have hm1 : phase (-(m:ℝ)*(2*Real.pi))=1 := by
      simpa only [Int.cast_neg,Int.cast_natCast] using integer_period_phase (-(m:ℤ))
    have hθ : phase (θ+2*Real.pi) = phase θ := by
      rw [phase_add,h1,mul_one]
    have hmθ : phase (-(m:ℝ)*(θ+2*Real.pi)) = phase (-(m:ℝ)*θ) := by
      rw [mul_add,phase_add,hm1,mul_one]
    simp only [g,hθ,hmθ]
  have hbound (θ : ℝ) : ‖g θ‖ ≤ 1 := by
    have hnorm : ‖w*phase θ‖=r := by rw [norm_mul,phase_norm,mul_one,hw]
    have h := MaxTerm513.norm_le_maxMod hf hnorm
    calc
      _ = ‖f (w*phase θ)‖/M := by simp only [g,norm_mul,hc,phase_norm,mul_one,div_eq_mul_inv,mul_comm]
      _ ≤ 1 := (div_le_one₀ hM).mpr h
  have hcoeff (k : ℤ) :
      meanCoeff g k = if 0 ≤ (m:ℤ)+k then c * MaxTerm513.coeff f ((m:ℤ)+k).toNat * w^((m:ℤ)+k).toNat else 0 :=
    meanCoeff_entire hf c w (by simpa only [hw] using hr) m k
  have hZn (j : ℕ) : ‖Z j‖ = MaxTerm513.term (fun j => ‖MaxTerm513.coeff f j‖) r j := by
    simp only [Z,MaxTerm513.term,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le]
  have hPolar (j : ℕ) : Z j = (‖Z j‖:ℂ) * phase (Z j).arg :=
    (Complex.norm_mul_exp_arg_mul_I (Z j)).symm
  have hprod (j : ℕ) :
      c * MaxTerm513.coeff f j * w^j =
      ((‖Z j‖/M:ℝ):ℂ) * phase (-(α+(m:ℝ)*t)+(Z j).arg+(j:ℝ)*t) := calc
    _ = (M:ℂ)⁻¹ * phase (-(α+(m:ℝ)*t)) * Z j * phase ((j:ℝ)*t) := by
      unfold c w Z
      rw [mul_pow,transport_phase_pow]
      ring
    _ = _ := by
      conv_lhs => rw [hPolar j]
      simp only [phase_add,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]
      ring
  have ht : ((m:ℝ)-(n:ℝ))*t=β-α := by
    have hδ : (m:ℝ)-(n:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
    dsimp [t]
    field_simp
  have hangle_m : -(α+(m:ℝ)*t)+(Z m).arg+(m:ℝ)*t = 0 := by
    change -(α+(m:ℝ)*t)+α+(m:ℝ)*t = 0
    ring
  have hangle_n : -(α+(m:ℝ)*t)+(Z n).arg+(n:ℝ)*t = 0 := by
    change -(α+(m:ℝ)*t)+β+(n:ℝ)*t = 0
    linarith only [ht]
  have hzero : phase 0=1 := by simp [phase]
  have hsame := le_antisymm (hm n) (hn m)
  refine ⟨g,hcont,hperiod,hbound,?_,?_,?_⟩
  · rw [MaxTerm513.maximum_ratio hr.le hm,hcoeff]
    simp only [Int.add_zero,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    rw [hprod,hangle_m,hzero,mul_one,hZn]
  · rw [MaxTerm513.maximum_ratio hr.le hm,hcoeff,
      show (m:ℤ)+((n:ℤ)-(m:ℤ))=(n:ℤ) by omega]
    simp only [Int.natCast_nonneg,if_true,Int.toNat_natCast]
    rw [hprod,hangle_n,hzero,mul_one,hZn,hsame]
  · intro k
    by_cases hk : 0 ≤ (m:ℤ)+k
    · simp only [hcoeff,if_pos hk,norm_mul,norm_pow,hw,hc,MaxTerm513.term,div_eq_mul_inv]
      ring
    · simp [hcoeff,hk]

end

end MaximumTerm
end

section
namespace MaxTerm513

noncomputable section

/-- Unit-normalized magnitude at any integral index, with zero values below index zero. -/
def relativeTerm (a : ℕ→ℝ) (r : ℝ) (m : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then term a r j.toNat / term a r m else 0

theorem relativeTerm_bounds {a : ℕ→ℝ} (ha : ∀ k, 0 ≤ a k) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hm : HasMaximum a r m) (hpos : 0 < term a r m) (j : ℤ) :
    0 ≤ relativeTerm a r m j ∧ relativeTerm a r m j ≤ 1 := by
  by_cases hj : 0 ≤ j
  · simp only [relativeTerm,if_pos hj]
    exact ⟨div_nonneg (mul_nonneg (ha _) (pow_nonneg hr.le _)) hpos.le,(div_le_one₀ hpos).mpr (hm _)⟩
  · simp [relativeTerm,hj]

theorem relativeTerm_at_tie {a : ℕ→ℝ} {r : ℝ} {m n : ℕ} (hm : HasMaximum a r m)
    (hn : HasMaximum a r n) (hpos : 0 < term a r m) :
    relativeTerm a r m n = 1 := by
  simp [relativeTerm,le_antisymm (hm n) (hn m),hpos.ne']

theorem relativeTerm_change_center {a : ℕ→ℝ} {r : ℝ} {m n : ℕ} (hm : HasMaximum a r m)
    (hn : HasMaximum a r n) (j : ℤ) :
    relativeTerm a r m j = relativeTerm a r n j := by
  unfold relativeTerm
  rw [le_antisymm (hm n) (hn m)]

theorem relativeTerm_scale {a : ℕ→ℝ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {m : ℕ} (hm : 0 < a m)
    (j : ℤ) : relativeTerm a s m j = relativeTerm a r m j * (s/r)^(j-(m:ℤ)) := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    simp only [relativeTerm,Int.natCast_nonneg,if_true,Int.toNat_natCast]
    rw [zpow_sub₀ (div_ne_zero hs.ne' hr.ne'),zpow_natCast,zpow_natCast,div_pow,div_pow]
    unfold term
    field_simp [hr.ne',hs.ne',hm.ne']
  · simp [relativeTerm,hj]

theorem ratio_positive {f : ℂ→ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hm : HasMaximum (fun j => ‖coeff f j‖) r m)
    (hpos : 0 < term (fun j => ‖coeff f j‖) r m) : 0 < Erdos513.ratio r f := by
  rw [maximum_ratio hr.le hm]
  exact div_pos hpos (hpos.trans_le (coeff_le_maxMod hf hr m))

end

end MaxTerm513

namespace MaximumTerm

open MaxTerm513

theorem normalized_tie_relative {f : ℂ→ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    {m n : ℕ} (hne : n ≠ m)
    (hm : HasMaximum (fun j => ‖coeff f j‖) r m)
    (hn : HasMaximum (fun j => ‖coeff f j‖) r n)
    (hpos : 0 < term (fun j => ‖coeff f j‖) r m) :
    ∃ g : ℝ→ℂ, Continuous g ∧ Function.Periodic g (2*Real.pi) ∧
      (∀ θ, ‖g θ‖ ≤ 1) ∧
      meanCoeff g 0 = (Erdos513.ratio r f : ℂ) ∧
      meanCoeff g ((n:ℤ)-(m:ℤ)) = (Erdos513.ratio r f : ℂ) ∧
      ∀ k : ℤ, ‖meanCoeff g k‖ / Erdos513.ratio r f =
        relativeTerm (fun j => ‖coeff f j‖) r m ((m:ℤ)+k) := by
  obtain ⟨g,hcont,hper,hbd,h0,hnm,hCoeff⟩ := normalized_tie hf hr hne hm hn hpos
  refine ⟨g,hcont,hper,hbd,h0,hnm,?_⟩
  intro k
  rw [hCoeff,maximum_ratio hr.le hm,relativeTerm]
  split_ifs
  · have hM : 0 < maxMod f r := hpos.trans_le (coeff_le_maxMod hf hr m)
    field_simp [hM.ne',hpos.ne']
  · simp

end MaximumTerm
end

section
namespace MaximumTerm

open MaxTerm513
open scoped Interval

/-- From uniform stability of the ideal Fourier profile to a bound for the pinned constant. -/
theorem maxTermConstant_le_of_profile_stability {C : ℝ} (hC : 0 ≤ C)
    (hStable : ∀ (g : ℝ → ℂ) (d : ℤ) (b : ℝ), Continuous g →
      Function.Periodic g (2*Real.pi) → (∀ θ, ‖g θ‖ ≤ 1) →
      meanCoeff g 0 = (b:ℂ) → meanCoeff g (-d) = (b:ℂ) →
      0 < d → C < b → ∀ k : ℤ, |‖meanCoeff g k‖/b - profile 0 d k| ≤ 1/100) :
    Erdos513.maxTermConstant ≤ C := by
  apply MaxTerm513.maxTermConstant_le_of_ties hC
  intro f htr hf r s n m p hr hrs hnm hmp hnr hmr hms hps
  by_contra hbad
  have hrC : C < Erdos513.ratio r f := lt_of_not_ge fun hh => hbad (Or.inl hh)
  have hsC : C < Erdos513.ratio s f := lt_of_not_ge fun hh => hbad (Or.inr hh)
  have hs : 0 < s := hr.trans hrs
  have hSupport := MaxTerm513.coeff_unbounded hf htr
  have hR := MaxTerm513.maximum_positive hSupport hr hmr
  have hS := MaxTerm513.maximum_positive hSupport hs hms
  have hP := MaxTerm513.maximum_positive hSupport hs hps
  obtain ⟨g,hg,hgp,hgb,hg0,hgn,hgf⟩ := normalized_tie_relative hf hr hnm.ne hmr hnr hR
  obtain ⟨G,hG,hGp,hGb,hG0,hGn,hGf⟩ := normalized_tie_relative hf hs hmp.ne hps hms hP
  have hnmZ : (n:ℤ) < m := by exact_mod_cast hnm
  have hmpZ : (m:ℤ) < p := by exact_mod_cast hmp
  have hd : 0 < (m:ℤ)-(n:ℤ) := sub_pos.mpr hnmZ
  have he : 0 < (p:ℤ)-(m:ℤ) := sub_pos.mpr hmpZ
  have hg' : meanCoeff g (-((m:ℤ)-(n:ℤ))) = (Erdos513.ratio r f : ℂ) := by
    rwa [show -((m:ℤ)-(n:ℤ)) = (n:ℤ)-(m:ℤ) by omega]
  have hG' : meanCoeff G (-((p:ℤ)-(m:ℤ))) = (Erdos513.ratio s f : ℂ) := by
    rwa [show -((p:ℤ)-(m:ℤ)) = (m:ℤ)-(p:ℤ) by omega]
  let a (j : ℕ) := ‖coeff f j‖
  let u := relativeTerm a r m
  let v := relativeTerm a s m
  have h1 (j : ℤ) : |u j - profile m ((m:ℤ)-(n:ℤ)) j| ≤ 1/100 := by
    have h := hStable g _ _ hg hgp hgb hg0 hg' hd hrC (j-(m:ℤ))
    rw [hgf,show (m:ℤ)+(j-(m:ℤ))=j by omega] at h
    simpa only [profile,sub_zero,u,a] using h
  have h2 (j : ℤ) : |v j - profile p ((p:ℤ)-(m:ℤ)) j| ≤ 1/100 := by
    have h := hStable G _ _ hG hGp hGb hG0 hG' he hsC (j-(p:ℤ))
    rw [hGf,show (p:ℤ)+(j-(p:ℤ))=j by omega, ← relativeTerm_change_center hms hps] at h
    simpa only [profile,sub_zero,v,a] using h
  exact consecutive_ties_obstruction u v n m p (s/r) hnmZ hmpZ (div_pos hs hr)
    (relativeTerm_bounds (fun _ => norm_nonneg _) hr hmr hR)
    (fun j => (relativeTerm_bounds (fun _ => norm_nonneg _) hs hms hS j).2)
    (relativeTerm_at_tie hms hps hS)
    (relativeTerm_scale hr hs (maximum_coeff_positive hSupport hr hmr))
    h1 h2

end MaximumTerm
end

theorem OMA.solution : type_of% @Erdos513.erdos_513.variants.upper_bound := by
  refine ⟨1/1000000000000, by norm_num, ?_⟩
  have hhalf : (1/2 : ℝ) ≤ 2/Real.pi :=
    (le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_four])
  exact MaximumTerm.maxTermConstant_le_of_profile_stability (by linarith) MaximumTerm.profile_stability