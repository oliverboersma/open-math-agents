import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1

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
