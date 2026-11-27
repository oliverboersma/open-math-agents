import OMAReductions.R_Erdos983_erdos_983_variants_erdos_straus_R1
import Mathlib

noncomputable section
open Real Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1

-- The logarithmic integral in logarithmic coordinates. Clamping below one
-- makes the integrand everywhere continuous and only shifts the usual Li by a constant.
private lemma shape :
    let slope := fun x : ℝ => exp (max 1 x) / max 1 x
    let model := fun x : ℝ => ∫ t in (1:ℝ)..x, slope t
    Monotone model ∧ ConvexOn ℝ univ model := by
  intro slope model
  have hc : Continuous slope := by
    unfold slope
    exact ((continuous_const.max continuous_id).rexp).div (continuous_const.max continuous_id)
      (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  have hd (x : ℝ) : HasDerivAt model (slope x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 1 x) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hsrc : MonotoneOn (fun t : ℝ => exp t / t) (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (f' := fun t => (exp t*t-exp t)/t^2)
    · exact continuous_exp.continuousOn.div continuous_id.continuousOn (fun t ht => by
        change 1 ≤ t at ht; linarith)
    · intro x hx
      have hx1 : 1 ≤ x := interior_subset hx
      simpa [id_def,Pi.div_def] using ((Real.hasDerivAt_exp x).div (hasDerivAt_id x) (by change x ≠ 0; linarith)).hasDerivWithinAt (s := interior (Ici 1))
    · intro x hx
      have hx1 : 1 ≤ x := interior_subset hx
      apply div_nonneg _ (sq_nonneg _)
      nlinarith [mul_nonneg (exp_pos x).le (sub_nonneg.mpr hx1)]
  have hs : Monotone slope := fun x y h => hsrc (show (1:ℝ) ≤ max 1 x from le_max_left ..) (show (1:ℝ) ≤ max 1 y from le_max_left ..) (max_le_max_left _ h)
  constructor
  · exact monotone_of_hasDerivAt_nonneg hd fun x => div_nonneg (exp_pos _).le (le_trans zero_le_one (le_max_left _ _))
  · apply Monotone.convexOn_univ_of_deriv (fun x => (hd x).differentiableAt)
    intro x y h
    rw [(hd x).deriv,(hd y).deriv]
    exact hs h

private lemma compareProducts {a b z : ℕ} (hA : 0 < a) (hB : 0 < b) (hZ : 0 < z)
    (hprod : z*z ≤ a*b) :
    let model := fun x : ℝ => ∫ t in (1:ℝ)..x, exp (max 1 t) / max 1 t
    2*model (log z) ≤ model (log a)+model (log b) := by
  intro model
  have ha : (0:ℝ)<a := by exact_mod_cast hA
  have hb : (0:ℝ)<b := by exact_mod_cast hB
  have hz : (0:ℝ)<z := by exact_mod_cast hZ
  have hl := log_le_log (mul_pos hz hz) (show (z:ℝ)*z ≤ a*b by exact_mod_cast hprod)
  rw [log_mul hz.ne' hz.ne',log_mul ha.ne' hb.ne'] at hl
  have hmid := shape.1 (show log z ≤ (1/2:ℝ)*log a+(1/2:ℝ)*log b by linarith)
  have hc := shape.2.2 (mem_univ (log a)) (mem_univ (log b))
    (show 0≤(1/2:ℝ) by norm_num) (show 0≤(1/2:ℝ) by norm_num) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hc
  linarith

-- The lower estimate is from @zarnab222-dev's #1312 (also used in the Romanoff proof).

private theorem prime_count_lower (x : ℝ) (hx : 64 ≤ x) :
    x / (4 * log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx' : 1 < x := by linarith
  have h₂ := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at h₂
  have h₈ := Real.log_le_sub_one_of_pos (x := 8) (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (x := (x+2)/8) (by linarith)
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  have h := Chebyshev.pi_ge' hx'
  apply le_trans _ h
  have he : x/(4*log x) = (x/4)/log x := by ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx').le
  nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (sub_nonneg.mpr h₂)]

private lemma enoughPrimes : ∀ᶠ N : ℕ in atTop, 2*N.primeCounting ≤ (128*N).primeCounting := by
  have hu := tendsto_natCast_atTop_atTop.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  filter_upwards [hu,eventually_ge_atTop 128] with N hu hN
  have hn : (128:ℝ)≤N := by exact_mod_cast hN
  have hpos : 0 < log N := log_pos (by linarith)
  have hlog : log (128*(N:ℝ)) ≤ 2*log N := by
    rw [log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<128) hn]
  have hl := prime_count_lower (128*N) (by linarith)
  rw [show (128*(N:ℝ)) = ((128*N:ℕ):ℝ) by push_cast; rfl, Nat.floor_natCast] at hl
  push_cast at hl
  simp only [Nat.floor_natCast] at hu
  have hlog4 : log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have ht := (le_div_iff₀ hpos).mp hu
  have hl' := (div_le_iff₀ (show 0 < 4*log (128*(N:ℝ)) by
    have := log_pos (show (1:ℝ)<128*N by linarith); linarith)).mp hl
  have ht' : (N.primeCounting : ℝ)*log N ≤ 4*N := ht.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
  have hl'' := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) (128*N).primeCounting)
  have result : 2*(N.primeCounting : ℝ) ≤ ((128*N).primeCounting : ℝ) := by
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [ht',hl',hl'',hn]
  exact_mod_cast result

-- The prime number theorem with arbitrary logarithmic savings.
def H1 : Prop := ∀ A : ℝ, 0 < A →
    (fun k : ℕ => (k.primeCounting : ℝ) - (∫ t in (1:ℝ)..log k, exp (max 1 t) / max 1 t)) =o[atTop]
      (fun k : ℕ => (k:ℝ) / log k ^ A)

-- Taking the running maximum up to a constant multiple of the square root
-- preserves the savings. The integer envelope also absorbs all rounding.
def H2 : Prop := ∀ g : ℕ → ℝ,
    (∀ A : ℝ, 0<A → g =o[atTop] (fun k : ℕ => (k:ℝ) / log k ^ A)) →
    ∃ E : ℕ → ℕ, (∀ A : ℝ, 0<A → (fun n : ℕ => (E n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt n / log n ^ A)) ∧
      ∀ᶠ n : ℕ in atTop, 1 ≤ E n ∧ ∀ k ≤ 128*n.sqrt, |g k| ≤ E n

theorem main : H1 → H2 → OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1.H2 := by
  let model := fun x : ℝ => ∫ t in (1:ℝ)..x, exp (max 1 t) / max 1 t
  intro pnt envelope
  obtain ⟨E,error,all⟩ := envelope _ pnt
  refine ⟨fun n => 6*E n,?_,?_⟩
  · intro A hA
    simpa using (error A hA).const_mul_left (6:ℝ)
  have hs : Tendsto Nat.sqrt atTop atTop := tendsto_atTop.2 fun k =>
    (eventually_ge_atTop (k*k)).mono fun n hn => Nat.le_sqrt.mpr hn
  filter_upwards [all,hs.eventually enoughPrimes,eventually_ge_atTop 16] with n hn ranks h16
  obtain ⟨hE,herr⟩ := hn
  let N := n.sqrt
  let r := N.primeCounting
  change 2*r ≤ (128*N).primeCounting at ranks
  let t := 2*r - 6*E n
  refine ⟨by omega,?_⟩
  by_cases ok : 2 ≤ t
  · refine ⟨t,ok,by dsimp [t,r,N]; omega,?_⟩
    intro i hi
    let j := t-1-i
    have hij : i+j+1=t := by dsimp [j]; omega
    let p (k:ℕ) := Nat.nth Nat.Prime k
    have hbd (k : ℕ) (hk : k<t) : p k ≤ 128*N := by
      have hc : k < Nat.count Nat.Prime (128*N+1) := by
        change k < (128*N).primeCounting
        have : t ≤ 2*r := Nat.sub_le ..; omega
      exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hc)
    have hp (k : ℕ) : (p k).primeCounting = k+1 := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k
    change p i * p j ≤ n
    by_contra! hbad
    have hnpos : 0<N := Nat.sqrt_pos.mpr (by omega)
    have comp := compareProducts (Nat.prime_nth_prime i).pos (Nat.prime_nth_prime j).pos hnpos
      ((Nat.sqrt_le n).trans hbad.le)
    have hi' := (abs_le.mp (herr _ (hbd i hi))).1
    have hj' := (abs_le.mp (herr _ (hbd j (by omega)))).1
    have hN' := (abs_le.mp (herr N (by dsimp [N]; omega))).2
    change -(E n:ℝ) ≤ ((p i).primeCounting:ℝ)-model (log (p i)) at hi'
    change -(E n:ℝ) ≤ ((p j).primeCounting:ℝ)-model (log (p j)) at hj'
    change (N.primeCounting:ℝ)-model (log N) ≤ E n at hN'
    change 2*model (log N) ≤ model (log (p i))+model (log (p j)) at comp
    rw [hp] at hi' hj'
    push_cast at hi' hj'
    have bad : 2*r ≤ i+j+2+4*E n := by
      exact_mod_cast (show 2*(N.primeCounting : ℝ) ≤ i+j+2+4*(E n:ℝ) by linarith)
    dsimp [t] at hij ok
    omega
  · refine ⟨2,le_rfl,by dsimp [t,r,N] at ok ⊢; omega,?_⟩
    intro i hi
    interval_cases i <;> norm_num [Nat.nth_prime_zero_eq_two,Nat.nth_prime_one_eq_three] <;> omega

end OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1
