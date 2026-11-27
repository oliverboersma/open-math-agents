import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1
import Mathlib
/-! A thinned product measure concentrates in a strictly smaller reciprocal-sum window. Its cost is bounded exponentially in the thinning parameter. The nonintegrability argument is adapted from @marcusbuffett, Erdős 297 R1.H1. -/
open Filter Real Finset Erdos297 MeasureTheory intervalIntegral
open scoped Topology

namespace E297P2

noncomputable def g (l y : ℝ) : ℝ := 1 / (y * (1 + Real.exp (l / y)))

theorem mass_eq (l : ℝ) : massIntegral l = ∫ y in (0:ℝ)..1, g l y := rfl

theorem g_nonneg (l : ℝ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ g l y :=
  div_nonneg zero_le_one (mul_nonneg hy (by positivity))

theorem nonpos (l : ℝ) (hl : l ≤ 0) : massIntegral l = 0 := by
  rw [mass_eq]
  apply intervalIntegral.integral_undef
  intro hint
  have h2 : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 1 := by
    have : IntervalIntegrable (fun y => 2 * g l y) volume 0 1 := hint.const_mul 2
    refine this.mono_fun (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc (fun y hy => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hy
    have hy0 := hy.1
    show ‖y⁻¹‖ ≤ ‖2 * g l y‖
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hy0.le),
      Real.norm_of_nonneg (mul_nonneg zero_le_two (g_nonneg l hy0.le))]
    unfold g
    have he : Real.exp (l / y) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg hl hy0.le)
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    rw [inv_mul_eq_div, div_le_iff₀ hy0]
    nlinarith [Real.exp_pos (l / y)]
  rw [intervalIntegrable_inv_iff] at h2
  rcases h2 with h | h
  · norm_num at h
  · exact h (by simp)

end E297P2
open Finset Real Filter MeasureTheory intervalIntegral Erdos297
open scoped Topology
namespace Thick297
noncomputable section

lemma endpoints (f : ℝ → ℝ) (hc : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n∈Icc 1 N, f (n/(N:ℝ)))/N) atTop
      (𝓝 (∫ y in (0:ℝ)..1,f y)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨δ,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) (ε/2) (by positivity)
  filter_upwards [tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const hd,eventually_gt_atTop 0] with N hδ hN
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  let a (i : ℕ) : ℝ := i/(N:ℝ)
  have a0 : a 0=0 := by simp [a]
  have aN : a N=1 := by simp [a,hn.ne']
  have diff (i : ℕ) : a (i+1)-a i=1/N := by simp [a,add_div]
  have geo (i : ℕ) (hi : i<N) : 0≤a i ∧ a i ≤ a (i+1) ∧ a (i+1) ≤ 1 := by
    refine ⟨by dsimp [a]; positivity,by linarith [diff i,one_div_pos.mpr hn],?_⟩
    change (↑(i+1):ℝ)/N ≤ 1
    apply (div_le_one hn).mpr
    exact_mod_cast (show i+1≤N by omega)
  have intg (i : ℕ) (hi : i<N) : IntervalIntegrable f volume (a i) (a (i+1)) :=
    ContinuousOn.intervalIntegrable_of_Icc (geo i hi).2.1 (hc.mono (Set.Icc_subset_Icc (geo i hi).1 (geo i hi).2.2))
  have err (i : ℕ) (hi : i<N) :
      |f (a (i+1))/N - ∫ y in a i..a (i+1), f y| ≤ (ε/2)/N := by
    obtain ⟨lo,inc,up⟩ := geo i hi
    have bound := intervalIntegral.norm_integral_le_of_norm_le_const (a := a i) (b := a (i+1))
      (f := fun y => f (a (i+1))-f y) (C := ε/2) (fun y hy => by
        rw [Set.uIoc_of_le inc] at hy
        have hdxy : dist (a (i+1)) y < δ := by
          rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hy.2)]
          linarith [diff i,hy.1]
        exact (hclose _ ⟨lo.trans inc,up⟩ _ ⟨lo.trans hy.1.le,hy.2.trans up⟩ hdxy).le)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (intg i hi),intervalIntegral.integral_const,smul_eq_mul,
      diff,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hn)] at bound
    simpa [div_eq_mul_inv,mul_comm] using bound
  have eq := sum_integral_adjacent_intervals intg
  rw [a0,aN] at eq
  rw [Real.dist_eq,←eq,show Icc 1 N = Ico 1 (N+1) by ext; simp, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Nat.add_comm 1]
  change |(∑ i ∈ range N, f (a (i+1)))/N - _| < ε
  rw [Finset.sum_div,←sum_sub_distrib]
  apply lt_of_le_of_lt ((abs_sum_le_sum_abs ..).trans (sum_le_sum fun i h => err i (mem_range.mp h)))
  simp [hn.ne',div_eq_mul_inv,mul_left_comm,mul_comm,mul_assoc]
  linarith

def profile (l y : ℝ) : ℝ := 1/(y*(1+exp (l/y)))

lemma exp_quadratic (z : ℝ) (hz : 0≤z) : z^2 ≤ 2*exp z := by
  have h := Real.pow_div_factorial_le_exp z hz 2
  norm_num at h
  linarith

lemma profile_le {l y : ℝ} (hl : 0<l) (hy : 0≤y) : profile l y ≤ 2*y/l^2 := by
  rcases hy.eq_or_lt with h|h
  · subst y; simp [profile]
  · rw [profile,div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := exp_quadratic (l/y) (by positivity)
    rw [div_pow,div_le_iff₀ (by positivity)] at hh
    nlinarith [sq_nonneg y]

lemma profile_cont (l : ℝ) (hl : 0<l) : ContinuousOn (profile l) (Set.Icc 0 1) := by
  intro y hy
  rcases hy.1.eq_or_lt with h|h
  · subst y
    rw [ContinuousWithinAt,show profile l 0=0 by simp [profile]]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => 0) (h := fun y : ℝ => 2*y/l^2) tendsto_const_nhds
    · have hh : Continuous (fun y : ℝ => 2*y/l^2) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Icc 0 1))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact div_nonneg zero_le_one (mul_nonneg hy.1 (by positivity))
    · filter_upwards [self_mem_nhdsWithin] with y hy using profile_le hl hy.1
  · apply ContinuousAt.continuousWithinAt
    unfold profile
    fun_prop (disch := first | positivity | exact h.ne')

lemma mean_limit (l : ℝ) (hl : 0<l) :
    Tendsto (fun N : ℕ => ∑ n∈Icc 1 N,(1/(n:ℝ))*(exp (-l*N/n)/(1+exp (-l*N/n))))
      atTop (𝓝 (massIntegral l)) := by
  refine (endpoints (profile l) (profile_cont l hl)).congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  have hp : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  unfold profile
  rw [show l/(n/(N:ℝ))=l*N/n by field_simp,show -l*N/n= -(l*N/n) by ring,exp_neg]
  field_simp <;> ring

end
end Thick297
open Finset Real Filter MeasureTheory intervalIntegral
open scoped Topology

namespace Thick297
noncomputable section

def part (P : Finset ℕ) (v : ℕ → ℝ) := ∏ n∈P, (1+v n)
def mean (P : Finset ℕ) (v b : ℕ → ℝ) := ∑ n∈P, b n*(v n/(1+v n))
def variance (P : Finset ℕ) (v b : ℕ → ℝ) := ∑ n∈P, (b n)^2*(v n/(1+v n)^2)
def wt (v : ℕ → ℝ) (A : Finset ℕ) := ∏ n∈A,v n
def mass (b : ℕ → ℝ) (A : Finset ℕ) := ∑ n∈A,b n

lemma second (P : Finset ℕ) (v b : ℕ → ℝ) (hv : ∀ n,0≤v n) (z : ℝ) :
    (∑ A∈P.powerset, wt v A * (mass b A-z)^2) =
      part P v * ((mean P v b-z)^2 + variance P v b) := by
  classical
  induction P using Finset.induction_on generalizing z with
  | empty => simp [wt,mass,part,mean,variance]
  | @insert n P hn ih =>
    rw [sum_powerset_insert hn,ih z]
    have eq : (∑ A∈P.powerset, wt v (insert n A)*(mass b (insert n A)-z)^2)
        = v n*∑ A∈P.powerset, wt v A*(mass b A-(z-b n))^2 := by
      rw [mul_sum]; apply sum_congr rfl
      intro A h
      have h' : n∉A := fun hm => hn ((mem_powerset.mp h) hm)
      simp only [wt,mass,prod_insert h',sum_insert h']
      ring
    rw [eq,ih (z-b n)]
    simp only [part,mean,variance,prod_insert hn,sum_insert hn]
    have hn' : 1+v n ≠ 0 := by linarith [hv n]
    field_simp
    <;> ring

lemma central (P : Finset ℕ) (v b : ℕ → ℝ) (hv : ∀ n, 0≤v n) (d : ℝ) (hd : 0<d)
    (small : variance P v b ≤ d^2/2) :
    part P v/2 ≤ ∑ A∈P.powerset.filter (fun A => |mass b A-mean P v b|≤d), wt v A := by
  classical
  let μ := mean P v b
  let good (A : Finset ℕ) := |mass b A-μ|≤d
  have zz : 0≤part P v := prod_nonneg fun n _ => by linarith [hv n]
  have ww (A : Finset ℕ) : 0 ≤ wt v A := prod_nonneg fun n _ => hv n
  have all : (∑ A∈P.powerset,wt v A) = part P v := (prod_one_add (f := v) P).symm
  have est := calc
    (∑ A∈P.powerset.filter (fun A => ¬good A), wt v A)*d^2
        = ∑ A∈P.powerset.filter (fun A => ¬good A), wt v A*d^2 := sum_mul ..
    _ ≤ ∑ A∈P.powerset.filter (fun A => ¬good A), wt v A*(mass b A-μ)^2 := by
      apply sum_le_sum
      intro A hA
      have h : d < |mass b A-μ| := lt_of_not_ge (mem_filter.mp hA).2
      exact mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using (sq_le_sq₀ hd.le (abs_nonneg _) |>.mpr h.le)) (ww A)
    _ ≤ ∑ A∈P.powerset, wt v A*(mass b A-μ)^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun A _ _ => mul_nonneg (ww A) (sq_nonneg _))
    _ = part P v*variance P v b := by rw [second P v b hv]; simp [μ]
    _ ≤ part P v*(d^2/2) := mul_le_mul_of_nonneg_left small zz
  have hsum := sum_filter_add_sum_filter_not P.powerset good (wt v)
  rw [all] at hsum
  change part P v/2 ≤ ∑ A∈P.powerset.filter good,wt v A
  have hbad : (∑ A∈P.powerset.filter (fun A => ¬good A),wt v A) ≤ part P v/2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
    nlinarith only [est]
  linarith
end
end Thick297
namespace Thick297
open Real Finset Filter Erdos297
open scoped Topology
noncomputable section

def odds (l : ℝ) (N n : ℕ) := exp (-l*N/n)
def thin (a w : ℝ) := a*w/(1+(1-a)*w)
lemma thin_id {a w : ℝ} (ha : 0≤a) (ha' : a≤1) (hw : 0≤w) :
    1+thin a w = (1+w)/(1+(1-a)*w) ∧
    thin a w/(1+thin a w) = a*(w/(1+w)) := by
  have h : 0 < 1+(1-a)*w := by nlinarith [mul_nonneg (sub_nonneg.mpr ha') hw]
  have id : 1+thin a w = (1+w)/(1+(1-a)*w) := by
    apply (eq_div_iff h.ne').mpr
    rw [add_mul,thin,div_mul_cancel₀ _ h.ne',one_mul]
    ring
  refine ⟨id,?_⟩
  rw [id,thin,div_div_div_cancel_right₀ h.ne',mul_div_assoc]

lemma thin_range {a w : ℝ} (ha : 0≤a) (ha' : a≤1) (hw : 0≤w) : 0≤thin a w ∧ thin a w≤w := by
  have z := mul_nonneg (sub_nonneg.mpr ha') hw
  have q : 0 < 1+(1-a)*w := by linarith
  refine ⟨div_nonneg (mul_nonneg ha hw) q.le,(div_le_iff₀ q).mpr ?_⟩
  nlinarith [mul_nonneg hw z]

lemma window_cost (l a : ℝ) (hl : 0<l) (ha : 0<a) (ha' : a<1) (N : ℕ) :
    exp (-(1-a)*N) * part (Icc 1 N) (odds l N) ≤
      part (Icc 1 N) (fun n => thin a (odds l N n)) := by
  have card : (Icc 1 N).card=N := by simp
  have rewrite_exp : exp (-(1-a)*N) = ∏ _n∈Icc 1 N, exp (-(1-a)) := by
    rw [prod_const,card,←Real.exp_nat_mul]; congr 1; ring
  rw [rewrite_exp,part,part,←prod_mul_distrib]
  apply prod_le_prod (fun n _ => by dsimp [odds]; positivity)
  intro n hn
  let w := odds l N n
  have hw : 0<w := exp_pos _
  have hw' : w≤1 := exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  rw [(thin_id ha.le ha'.le hw.le).1,exp_neg]
  have hh : 1+(1-a)*w ≤ exp (1-a) := by
    linarith [mul_le_mul_of_nonneg_left hw' (sub_nonneg.mpr ha'.le),Real.add_one_le_exp (1-a)]
  change (exp (1-a))⁻¹*(1+w) ≤ (1+w)/(1+(1-a)*w)
  rw [mul_comm,←div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by linarith) (by positivity) hh

lemma thin_var (l a : ℝ) (hl : 0<l) (ha : 0≤a) (ha' : a≤1) (N : ℕ) (hN : 0<N) :
    variance (Icc 1 N) (fun n => thin a (odds l N n)) (fun n => 1/(n:ℝ)) ≤ (2/l^2)/N := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ ∑ _n∈Icc 1 N, 2/(l^2*(N:ℝ)^2) := by
      apply sum_le_sum
      intro n hn
      have hn' : (0:ℝ)<n := by exact_mod_cast (mem_Icc.mp hn).1
      let w := odds l N n
      let v := thin a w
      have hw : 0<w := exp_pos _
      obtain ⟨hv,hvw⟩ := thin_range ha ha' hw.le
      have hd : 1 ≤ (1+v)^2 := by change 1 ≤ (1+thin a w)^2; nlinarith [sq_nonneg (thin a w)]
      have bb : v/(1+v)^2 ≤ w := (div_le_self hv hd).trans hvw
      refine (mul_le_mul_of_nonneg_left bb (sq_nonneg _)).trans ?_
      change (1/(n:ℝ))^2*exp (-l*N/n) ≤ _
      rw [show -l*N/n= -(l*N/n) by ring,exp_neg]
      have z := exp_quadratic (l*N/n) (by positivity)
      rw [div_pow,div_le_iff₀ (by positivity)] at z
      field_simp
      nlinarith only [z]
    _ = _ := by simp; field_simp

lemma main (x : ℚ) (l : ℝ) (hx : 0<x) (hm : massIntegral l=x) (hl : 0<l) (ε : ℝ) (he : 0<ε) :
    ∃ d : ℚ, 0<d ∧ ∀ᶠ N : ℕ in atTop, exp (-ε*N) * (∏ n∈Icc 1 N, (1+exp (-l*N/n))) ≤
      (((Icc 1 N).powerset.filter (fun A : Finset ℕ => (∑ n∈A,(1:ℚ)/n) ≤ x-d)).card:ℝ) * exp (-l*N*(x:ℝ)) := by
  classical
  have x0 : (0:ℝ)<x := by exact_mod_cast hx
  let c : ℝ := 2/(x:ℝ)+3*l
  have cp : 0<c := by dsimp [c]; positivity
  obtain ⟨d,d0,hd⟩ := exists_rat_btwn (show (0:ℝ) < min ((x:ℝ)/4) (ε/(2*c)) from lt_min (by positivity) (by positivity))
  have hd₁ := lt_of_lt_of_le hd (min_le_left ..)
  have hd₂ := lt_of_lt_of_le hd (min_le_right ..)
  have cheap : (d:ℝ)*c < ε/2 := by rw [lt_div_iff₀ (by positivity)] at hd₂; linarith
  let a : ℝ := 1-2*(d:ℝ)/x
  have ax : a*(x:ℝ)=(x:ℝ)-2*d := by dsimp [a]; field_simp
  have ap : 0<a := by dsimp [a]; rw [sub_pos,div_lt_one x0]; linarith
  have au : a<1 := by dsimp [a]; linarith [div_pos (by positivity : 0<2*(d:ℝ)) x0]
  have loss : 1-a+3*l*d<ε/2 := by dsimp [c] at cheap; dsimp [a]; convert cheap using 1 <;> ring
  let b (n : ℕ) : ℝ := 1/n
  let v (N n : ℕ) := thin a (odds l N n)
  let P (N : ℕ) := Icc 1 N
  have mlim : Tendsto (fun N => mean (P N) (v N) b) atTop (𝓝 (a*(x:ℝ))) := by
    rw [←hm]
    apply ((mean_limit l hl).const_mul a).congr'
    filter_upwards with N
    rw [mean,mul_sum]
    apply sum_congr rfl
    intro n _
    dsimp only [v,b,odds]
    rw [(thin_id ap.le au.le (exp_pos _).le).2]
    ring
  have vlim : Tendsto (fun N : ℕ => (2/l^2)/(N:ℝ)) atTop (𝓝 0) := by
    have u : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    let K : ℝ := 2/l^2
    change Tendsto (fun n : ℕ => K/(n:ℝ)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv,one_mul,mul_zero] using (show Tendsto (fun n : ℕ => K*(1/(n:ℝ))) atTop (𝓝 (K*0)) from u.const_mul K)
  have decay : Tendsto (fun N : ℕ => exp (-(ε/2)*(N:ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith)
  refine ⟨d,by exact_mod_cast d0,?_⟩
  filter_upwards [Metric.tendsto_nhds.mp mlim ((d:ℝ)/2) (by positivity),
    vlim.eventually_lt_const (show 0<((d:ℝ)/2)^2/2 by positivity),
    decay.eventually_lt_const (show (0:ℝ)<1/2 by norm_num),eventually_gt_atTop (0:ℕ)] with N hμ hvar hdec hN
  let μ := mean (P N) (v N) b
  let good := (P N).powerset.filter (fun A => |mass b A-μ|≤(d:ℝ)/2)
  let sub := (P N).powerset.filter (fun A : Finset ℕ => (∑ n∈A,(1:ℚ)/n) ≤ x-d)
  have center := central (P N) (v N) b (fun n => (thin_range ap.le au.le (exp_pos _).le).1)
    ((d:ℝ)/2) (by positivity) ((thin_var l a hl ap.le au.le N hN).trans hvar.le)
  have band {A : Finset ℕ} (h : A∈good) : (x:ℝ)-3*d ≤ mass b A ∧ mass b A ≤ x-d := by
    obtain ⟨low,up⟩ := abs_le.mp (mem_filter.mp h).2
    rw [Real.dist_eq,ax,abs_lt] at hμ
    change -((d:ℝ)/2) ≤ mass b A-μ at low
    change mass b A-μ ≤ (d:ℝ)/2 at up
    change _ < μ-((x:ℝ)-2*d) ∧ μ-((x:ℝ)-2*d) < _ at hμ
    constructor <;> linarith
  have incl : good ⊆ sub := by
    intro A h
    refine mem_filter.mpr ⟨(mem_filter.mp h).1,?_⟩
    have hh := (band h).2
    dsimp [mass,b] at hh
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Rat.cast_sub] using hh
  have wbound {A : Finset ℕ} (h : A∈good) : wt (v N) A ≤ exp (-l*N*((x:ℝ)-3*d)) := by
    calc
      _ ≤ ∏ n∈A,odds l N n := prod_le_prod
        (fun n _ => (thin_range ap.le au.le (exp_pos _).le).1)
        (fun n _ => (thin_range ap.le au.le (exp_pos _).le).2)
      _ = exp (-l*N*mass b A) := by
        unfold odds
        rw [←Real.exp_sum,mass,mul_sum]
        congr 1; apply sum_congr rfl; intro n _; dsimp [b]; ring
      _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonpos_left (band h).1 (by nlinarith [Nat.cast_nonneg (α := ℝ) N]))
  have H : exp (-(1-a)*N)*part (P N) (odds l N)/2 ≤ (sub.card:ℝ)*exp (-l*N*((x:ℝ)-3*d)) := calc
    _ ≤ part (P N) (v N)/2 := by linarith [window_cost l a hl ap au N]
    _ ≤ ∑ A∈good,wt (v N) A := center
    _ ≤ ∑ _A∈good,exp (-l*N*((x:ℝ)-3*d)) := sum_le_sum fun _ h => wbound h
    _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]; gcongr
  have hleft : exp (-ε*N) ≤ exp (-(1-a)*N)/2 * exp (-(3*l*d)*N) := by
    rw [div_mul_eq_mul_div,← Real.exp_add]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have e := mul_le_mul_of_nonneg_left hdec.le (exp_pos (-ε/2*N)).le
    rw [← Real.exp_add] at e
    have E : -ε/2*N + -(ε/2)*N = -ε*N := by ring
    rw [E] at e
    have q : -ε/2*N ≤ -(1-a)*N + -(3*l*d)*N := by
      nlinarith [mul_le_mul_of_nonneg_right loss.le (Nat.cast_nonneg (α := ℝ) N)]
    nlinarith [exp_le_exp.mpr q]
  have pair := mul_le_mul_of_nonneg_right H (exp_pos (-(3*l*d)*N)).le
  have fix : exp (-l*N*((x:ℝ)-3*d))*exp (-(3*l*d)*N) = exp (-l*N*x) := by rw [←exp_add]; congr 1; ring
  rw [mul_assoc (sub.card:ℝ),fix] at pair
  change exp (-ε*N)*part (P N) (odds l N) ≤ (sub.card:ℝ)*exp (-l*N*x)
  refine le_trans ?_ pair
  have hh := mul_le_mul_of_nonneg_right hleft (show 0≤part (P N) (odds l N) from prod_nonneg fun n _ => by dsimp [odds]; positivity)
  linarith
end
end Thick297
theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1.H1 := by
  intro x l hx hm
  have xl : (0:ℝ)<(x:ℝ) := by exact_mod_cast hx
  exact Thick297.main x l hx hm (lt_of_not_ge (fun h => (ne_of_gt xl) (hm.symm.trans (E297P2.nonpos l h))))
