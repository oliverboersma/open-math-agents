import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1

/-! A finite-difference route to polynomial-frequency dispersion of prime
logarithms. Chebyshev supplies sufficiently many primes in (k/16,k].
A small total cosine loss would put almost all of them close to the phase
lattice. A dense subset of integers contains a cube of well-chosen scale;
the mixed difference of log on this cube lies strictly between two
consecutive multiples of 2 pi. -/
namespace OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1_H1_R1
open Finset Filter Real Chebyshev
open scoped Topology Classical

private lemma phase (w:ℝ) : ∃ z:ℤ, |w-2*π*z|^2 ≤ 2*π^2*(1-|cos (w/2)|) := by
  let x := w/(2*π)
  let z := round x
  let a := w/2-(z:ℝ)*π
  have ha : |a|≤π/2 := by
    have h := mul_le_mul_of_nonneg_right (abs_sub_round x) pi_pos.le
    have eq : a=(x-z)*π := by dsimp [a,x]; field_simp
    rw [eq,abs_mul,abs_of_pos pi_pos]
    linarith
  have ca : 0≤cos a := cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp ha).1],(abs_le.mp ha).2⟩
  have eq : w/2=a+(z:ℝ)*π := by dsimp [a]; ring
  have c : |cos (w/2)|=cos a := by
    rw [eq,cos_add_int_mul_pi,abs_mul,abs_zpow,abs_neg,abs_one,one_zpow,one_mul,abs_of_nonneg ca]
  have h := cos_le_one_sub_mul_cos_sq (ha.trans (by linarith [pi_pos]))
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg π)
  have e : π^2*((2/π^2)*a^2)=2*a^2 := by field_simp
  refine ⟨z,?_⟩
  rw [c,show w-2*π*(z:ℝ)=2*a by dsimp [a]; ring,sq_abs]
  nlinarith only [h',e]

private lemma prime_mass : ∀ᶠ k:ℕ in atTop,
    (k:ℝ)/4 ≤ (((Ioc (k/16) k).filter Nat.Prime).card:ℝ)*(1+log k) := by
  have tn : Tendsto (fun k:ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have slow := (isLittleO_log_rpow_atTop (show 0<(1/2:ℝ) by norm_num)).bound (show (0:ℝ)<1/32 by norm_num)
  filter_upwards [tn.eventually slow,eventually_ge_atTop 128] with k less large
  have x1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have xp : 0<(k:ℝ) := zero_lt_one.trans_le x1
  change ‖log (k:ℝ)‖≤1/32*‖(k:ℝ)^(1/2:ℝ)‖ at less
  rw [←sqrt_eq_rpow,Real.norm_of_nonneg (log_nonneg x1),Real.norm_of_nonneg (sqrt_nonneg _)] at less
  have low := theta_ge k
  have high := theta_le_log4_mul_x (x:=((k/16:ℕ):ℝ)) (Nat.cast_nonneg _)
  have rootlog := mul_le_mul_of_nonneg_left less (sqrt_nonneg (k:ℝ))
  have sq := sq_sqrt xp.le
  have q : ((k/16:ℕ):ℝ)≤(k:ℝ)/16 := by simpa using (Nat.cast_div_le (α:=ℝ) (m:=k) (n:=16))
  have l4 : log 4≤2 := by rw [show (4:ℝ)=2*2 by norm_num,log_mul (by norm_num) (by norm_num)]; linarith [log_two_lt_d9]
  have h4 := mul_le_mul l4 q (Nat.cast_nonneg _) (by norm_num)
  have lp1 : log ((k:ℝ)+1)≤log (k:ℝ)+1 := by
    have h := log_le_log (by linarith) (show (k:ℝ)+1≤(k:ℝ)*2 by linarith)
    rw [log_mul xp.ne' (by norm_num)] at h
    linarith [log_two_lt_d9]
  have rootk := sqrt_le_self_iff.mpr (Or.inr x1)
  let P := (Ioc (k/16) k).filter Nat.Prime
  have hsub : (k/16).primesLE ⊆ k.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans (Nat.div_le_self ..),Nat.prime_of_mem_primesLE hp⟩
  have eq : k.primesLE \ (k/16).primesLE=P := by
    apply Finset.ext
    intro p
    constructor
    · intro hh
      obtain ⟨hk,hn⟩ := Finset.mem_sdiff.mp hh
      obtain ⟨pk,pp⟩ := Nat.mem_primesLE.mp hk
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge (fun hs => hn (Nat.mem_primesLE.mpr ⟨hs,pp⟩)),pk⟩,pp⟩
    · intro hh
      obtain ⟨hi,pp⟩ := mem_filter.mp hh
      obtain ⟨lp,pk⟩ := mem_Ioc.mp hi
      exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨pk,pp⟩,fun hs => lp.not_ge (Nat.mem_primesLE.mp hs).1⟩
  have diff : theta k-theta ((k/16:ℕ):ℝ)=∑ p∈P,log p := by
    rw [theta_eq_sum_primesLE_log,theta_eq_sum_primesLE_log,←eq]
    have h := sum_sdiff hsub (f:=fun p:ℕ => log (p:ℝ))
    try simp only [Nat.floor_natCast]
    linarith
  have ub := sum_le_sum (s:=P) (fun p hp => show log (p:ℝ)≤1+log k by
    have h := mem_filter.mp hp
    have e := log_le_log (show (0:ℝ)<p by exact_mod_cast h.2.pos) (show (p:ℝ)≤k by exact_mod_cast (mem_Ioc.mp h.1).2)
    linarith)
  rw [sum_const,nsmul_eq_mul] at ub
  have kl : (128:ℝ)≤k := by exact_mod_cast large
  have log2 := mul_le_mul_of_nonneg_left (show 1/2≤log 2 by linarith [log_two_gt_d9]) xp.le
  nlinarith only [low,high,h4,lp1,rootlog,sq,ub,diff,less,rootk,log2,kl]

private lemma logs_small (A:ℕ) (C:ℝ) : ∀ᶠ k:ℕ in atTop, C*(1+log (k:ℝ))^A ≤ (k:ℝ) := by
  let B := max C 1*2^A
  have bp : 0<B := mul_pos (lt_of_lt_of_le one_pos (le_max_right ..)) (by positivity)
  have tN : Tendsto (fun k:ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have raw := (isLittleO_log_rpow_rpow_atTop (A:ℝ) (show (0:ℝ)<1 by norm_num)).bound (inv_pos.mpr bp)
  filter_upwards [tL.eventually_ge_atTop 1,tN.eventually raw] with k lg h
  change 1≤log (k:ℝ) at lg
  simp only [rpow_natCast,rpow_one,Real.norm_of_nonneg (pow_nonneg (by linarith : 0≤log (k:ℝ)) _), Real.norm_of_nonneg (Nat.cast_nonneg k (α:=ℝ))] at h
  have hh := mul_le_mul_of_nonneg_left h bp.le
  have bb : B*B⁻¹=1 := mul_inv_cancel₀ bp.ne'
  have e : (1+log (k:ℝ))^A ≤ 2^A*(log (k:ℝ))^A := by rw [←mul_pow]; gcongr; linarith
  calc
    _ ≤ (max C 1)*(2^A*(log (k:ℝ))^A) := mul_le_mul (le_max_left ..) e (by positivity) (le_trans zero_le_one (le_max_right ..))
    _ = B*(log (k:ℝ))^A := by dsimp [B]; ring
    _ ≤ _ := by rw [←mul_assoc,bb,one_mul] at hh; exact hh

-- A dense subset of a fixed macroscopic interval contains a cube of
-- scale k/(1+|s|)^(1/d). The product of its step lengths gives the
-- derivative bounds below with a power of the logarithm to spare.
def H1 : Prop := ∀ M:ℕ, ∃ d A:ℕ, 0<d ∧ ∀ᶠ k:ℕ in atTop, ∀ s:ℝ,
  1/(1+log k)^2≤|s| → |s|≤(k:ℝ)^M → ∀ B ⊆ Ioc (k/16) k,
  (k:ℝ)/(100*(1+log k))≤B.card →
  ∃ (x:ℕ) (h:List ℕ), h.length=d ∧ 0<x ∧ (∀ a∈h,0<a) ∧
  (∀ t:List ℕ,t.Sublist h → x+t.sum∈B) ∧
  1/(1+log k)^A ≤ |s| *((d-1).factorial:ℝ)*(h.prod:ℝ)/((x+h.sum:ℕ):ℝ)^d ∧
  |s| *((d-1).factorial:ℝ)*(h.prod:ℝ)/(x:ℝ)^d≤1

-- Mixed forward differences of the logarithm, evaluated on one cube,
-- exclude simultaneous resonance at its vertices.
def H2 : Prop := ∀ (x:ℕ) (h:List ℕ) (s η:ℝ), 0<x → h≠[] → (∀ a∈h,0<a) → 0≤η →
  (2:ℝ)^h.length*η < |s| *((h.length-1).factorial:ℝ)*(h.prod:ℝ)/((x+h.sum:ℕ):ℝ)^h.length →
  |s| *((h.length-1).factorial:ℝ)*(h.prod:ℝ)/(x:ℝ)^h.length≤1 →
  ∃ t:List ℕ,t.Sublist h ∧ ∀ z:ℤ, η < |s*log ((x+t.sum:ℕ):ℝ)-2*π*z|

theorem main : H1 → H2 → OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1.H1 := by
  classical
  intro cube oscill M
  obtain ⟨d,A,hd,box⟩ := cube M
  let D := (2:ℝ)^(d+1)
  let C := 100*(2*π^2)*((M:ℝ)+1)*D^2
  have dp : 0<D := by dsimp [D]; positivity
  filter_upwards [box,prime_mass,logs_small (2*A+2) C,eventually_ge_atTop 1024] with k box mass slim big
  intro s sl su
  let R := 1+log (k:ℝ)
  have r1 : 1≤R := by dsimp [R]; linarith [log_natCast_nonneg k]
  have rp : 0<R := zero_lt_one.trans_le r1
  let η := 1/(D*R^A)
  have ep : 0<η := by dsimp [η]; positivity
  let P := (Ioc (k/16) k).filter Nat.Prime
  let B := P.filter (fun p:ℕ => ∃ z:ℤ, |s*log (p:ℝ)-2*π*z|≤η)
  let V := P \ B
  let S := (Ioc k.sqrt k).filter Nat.Prime
  let loss (p:ℕ) := 1-|cos (s*log (p:ℝ)/2)|
  have l0 (p:ℕ) : 0≤loss p := sub_nonneg.mpr (abs_cos_le_one _)
  have sp : P⊆S := by
    apply filter_subset_filter
    apply Ioc_subset_Ioc _ le_rfl
    apply (Nat.le_div_iff_mul_le (by decide : 0<16)).mpr
    have h := Nat.sqrt_le k
    have v : 16≤k.sqrt := Nat.le_sqrt.mpr (by omega)
    nlinarith only [h,Nat.mul_le_mul_left k.sqrt v]
  change (M:ℝ)*log k≤ ∑ p∈S,loss p
  by_contra! small
  have ub : (V.card:ℝ)*η^2≤(2*π^2)*((M:ℝ)*log k) := by
    calc _ = ∑ _p∈V,η^2 := by simp
         _ ≤ ∑ p∈V,(2*π^2)*loss p := by
           apply sum_le_sum
           intro p hp
           obtain ⟨pv,pb⟩ := mem_sdiff.mp hp
           obtain ⟨z,hz⟩ := phase (s*log (p:ℝ))
           have h : η < |s*log (p:ℝ)-2*π*z| := lt_of_not_ge (fun h => pb (mem_filter.mpr ⟨pv,z,h⟩))
           exact (pow_le_pow_left₀ ep.le h.le 2).trans hz
         _ ≤ _ := by
           rw [←mul_sum]
           exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans sp) (fun i _ _ => l0 i)).trans small.le) (by positivity)
  have cost : (V.card:ℝ)≤(2*π^2)*((M:ℝ)*log k)*(D^2*R^(2*A)) := by
    have he : η^2*(D^2*R^(2*A))=1 := by dsimp [η]; rw [Nat.mul_comm 2 A,pow_mul]; field_simp
    have hh := mul_le_mul_of_nonneg_right ub (show 0≤D^2*R^(2*A) by positivity)
    rwa [mul_assoc (V.card:ℝ),he,mul_one] at hh
  have rhs : 100*((V.card:ℝ)*R)≤(k:ℝ) := by
    change C*R^(2*A+2)≤(k:ℝ) at slim
    apply le_trans _ slim
    have e := mul_le_mul_of_nonneg_right cost rp.le
    have u : (M:ℝ)*log k≤((M:ℝ)+1)*R := by dsimp [R]; nlinarith [log_natCast_nonneg k,Nat.cast_nonneg M (α:=ℝ)]
    have h := mul_le_mul_of_nonneg_right u (show 0≤(2*π^2)*D^2*R^(2*A)*R by positivity)
    dsimp only [C]
    rw [pow_add,pow_two]
    have h1 := mul_le_mul_of_nonneg_right r1 (show 0≤(2*π^2)*((M:ℝ)+1)*D^2*R^(2*A)*R by positivity)
    nlinarith only [e,h,h1]
  have tot : (V.card:ℝ)+(B.card:ℝ)=P.card := by exact_mod_cast (card_sdiff_add_card_eq_card (show B⊆P from filter_subset ..) : V.card+B.card=P.card)
  have bmass : (k:ℝ)/(100*R)≤B.card := by
    apply (div_le_iff₀ (by positivity)).mpr
    change (k:ℝ)/4≤(P.card:ℝ)*R at mass
    rw [←tot,add_mul] at mass
    linarith only [mass,rhs,Nat.cast_nonneg k (α:=ℝ)]
  obtain ⟨x,h,hlen,xp,steps,vertices,lo,hi⟩ := box s sl su B ((filter_subset ..).trans (filter_subset ..)) bmass
  have nz : h≠[] := by intro e; simp [e] at hlen; omega
  have tol : (2:ℝ)^h.length*η < 1/R^A := by
    rw [hlen]
    dsimp [η,D]
    rw [pow_succ]
    field_simp
    norm_num
  rw [←hlen] at lo hi
  obtain ⟨t,ht,far⟩ := oscill x h s η xp nz steps ep.le (tol.trans_le lo) hi
  obtain ⟨z,hz⟩ := (mem_filter.mp (vertices t ht)).2
  exact (far z).not_ge hz

end OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1_H1_R1
