import FormalConjectures.OEIS.«248123»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Factorization

/-! Following Zedan Soorya's construction for A248123, take m to be the
product of two primes u and r with 3u/2 ≤ r < 2u. We find r by combining
Chebyshev's factorial estimates with a count of forbidden digit patterns. -/

namespace OMA.Catalan248
open Finset Filter Real
open ArithmeticFunction hiding log id
open scoped Topology ArithmeticFunction Chebyshev
noncomputable section

def lf (n : ℕ) := Real.log (n.factorial : ℝ)

lemma lf_sum {n N : ℕ} (hn : n ≤ N) :
    lf n = ∑ d ∈ Ioc 0 N, (n/d : ℕ)*vonMangoldt d := by
  have expand (i : ℕ) (hi : i ∈ range n) :
      Real.log (i+1 : ℕ) = ∑ d ∈ Ioc 0 N, if d ∣ i+1 then vonMangoldt d else 0 := by
    rw [← vonMangoldt_sum, ← sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans
        ((Nat.succ_le_of_lt (mem_range.mp hi)).trans hn)⟩,hd⟩
    · exact fun h => ⟨h.2,by omega⟩
  calc
    lf n = ∑ i ∈ range n, Real.log (i+1 : ℕ) := by
      rw [lf,Nat.factorial_eq_prod_range_add_one,Nat.cast_prod,Real.log_prod]
      intro i hi
      positivity
    _ = ∑ i ∈ range n, ∑ d ∈ Ioc 0 N, if d ∣ i+1 then vonMangoldt d else 0 :=
      sum_congr rfl expand
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul]

def coefficient (j : ℕ) : ℤ := j - (j/2 : ℕ) - (j/3 : ℕ) - (j/5 : ℕ) + (j/30 : ℕ)

lemma coefficient_bounds (j : ℕ) : 0 ≤ coefficient j ∧ coefficient j ≤ 1 := by
  have hj : j = 30*(j/30)+j%30 := (Nat.div_add_mod j 30).symm
  have hr := Nat.mod_lt j (by decide : 0<30)
  unfold coefficient
  omega

lemma coefficient_one {j : ℕ} (hj : 0<j) (h : j<6) : coefficient j = 1 := by
  interval_cases j <;> decide

def F (k : ℕ) := lf (30*k)-lf (15*k)-lf (10*k)-lf (6*k)+lf k

lemma F_sum (k : ℕ) :
    F k = ∑ d ∈ Ioc 0 (30*k), (coefficient (30*k/d) : ℝ)*vonMangoldt d := by
  unfold F
  rw [lf_sum (N := 30*k) (by omega : 30*k ≤ 30*k),
    lf_sum (N := 30*k) (by omega : 15*k ≤ 30*k),
    lf_sum (N := 30*k) (by omega : 10*k ≤ 30*k),
    lf_sum (N := 30*k) (by omega : 6*k ≤ 30*k),
    lf_sum (N := 30*k) (by omega : k ≤ 30*k)]
  rw [← sum_sub_distrib,← sum_sub_distrib,← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have div (a b : ℕ) (ha : 0<a) (hab : a*b=30) :
      30*k/d/a = b*k/d := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm d a, ← Nat.div_div_eq_div_mul,
      ← hab, Nat.mul_assoc, Nat.mul_div_cancel_left _ ha]
  simp only [coefficient,Int.cast_add,Int.cast_sub,Int.cast_natCast,one_mul,div 2 15 (by decide) (by decide),div 3 10 (by decide) (by decide),
    div 5 6 (by decide) (by decide),div 30 1 (by decide) (by decide)]
  ring

lemma F_le (k : ℕ) : F k ≤ Chebyshev.psi (30*k : ℕ) := by
  rw [F_sum,Chebyshev.psi,Nat.floor_natCast]
  apply sum_le_sum
  intro d hd
  exact mul_le_of_le_one_left (vonMangoldt_nonneg) (by exact_mod_cast (coefficient_bounds _).2)

lemma psi_le_F (k : ℕ) : Chebyshev.psi (30*k : ℕ) ≤ F k + Chebyshev.psi (5*k : ℕ) := by
  rw [F_sum,Chebyshev.psi,Chebyshev.psi,Nat.floor_natCast,Nat.floor_natCast]
  have hsub : Ioc 0 (5*k) ⊆ Ioc 0 (30*k) := Ioc_subset_Ioc_right (by omega)
  rw [← sum_sdiff hsub]
  apply add_le_add_left
  apply (sum_le_sum_of_subset_of_nonneg (sdiff_subset (s := Ioc 0 (30*k)) (t := Ioc 0 (5*k)))
    (fun d _ _ => mul_nonneg (by exact_mod_cast (coefficient_bounds _).1) vonMangoldt_nonneg)).trans_eq' ?_
  apply sum_congr rfl
  intro d hd
  obtain ⟨hm,hnot⟩ := mem_sdiff.mp hd
  simp only [mem_Ioc] at hm hnot
  have hpos : 0 < 30*k/d := Nat.div_pos hm.2 hm.1
  have hsmall : 30*k/d < 6 := (Nat.div_lt_iff_lt_mul hm.1).mpr (by omega)
  rw [coefficient_one hpos hsmall]
  simp

lemma lf_limit (c : ℕ) (hc : 0<c) :
    Tendsto (fun k : ℕ => (lf (c*k) - (c:ℝ)*k*(log k-1))/k) atTop (𝓝 ((c:ℝ)*log c)) := by
  have hc' : (0:ℝ)<c := by exact_mod_cast hc
  have hck : Tendsto (fun k : ℕ => c*k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left _ hc) tendsto_id
  have herr := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hck).log
    (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
  have he : Tendsto (fun k : ℕ => log (Stirling.stirlingSeq (c*k))/k) atTop (𝓝 0) :=
    herr.div_atTop tendsto_natCast_atTop_atTop
  have hklog : Tendsto (fun k : ℕ => log (k:ℝ)/k) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (log (2*(c:ℝ)))
  have h := (he.add ((hconst.add hklog).const_mul (1/2:ℝ))).add
    (tendsto_const_nhds (x := (c:ℝ)*log c) (f := (atTop : Filter ℕ)))
  simp only [zero_add,mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have heq := Stirling.log_stirlingSeq_formula (c*k)
  change _ = lf (c*k)-_ -_ at heq
  push_cast at heq
  rw [Real.log_div (by positivity) (by positivity),Real.log_exp,
    ← mul_assoc,Real.log_mul (by positivity : (2*(c:ℝ))≠0) hk'.ne',
    Real.log_mul hc'.ne' hk'.ne'] at heq
  field_simp [hk'.ne']
  linear_combination 2 * heq

def A : ℝ := 30*log 30 - 15*log 15 - 10*log 10 - 6*log 6

lemma F_limit : Tendsto (fun k : ℕ => F k/k) atTop (𝓝 A) := by
  have h := (((((lf_limit 30 (by decide)).sub (lf_limit 15 (by decide))).sub
    (lf_limit 10 (by decide))).sub (lf_limit 6 (by decide))).add (lf_limit 1 (by decide)))
  norm_num [A] at h ⊢
  apply h.congr
  intro k
  unfold F
  ring

lemma A_pos_gap : 15*log 4 < A := by
  have l2 := log_pos (by norm_num : (1:ℝ)<2)
  have l3 := log_lt_log (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)<3)
  have l5 := log_lt_log (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)<5)
  have four : log 4 = 2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  rw [four] at l5 ⊢
  unfold A
  rw [show (30:ℝ)=2*15 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    show (15:ℝ)=3*5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    show (10:ℝ)=2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    show (6:ℝ)=2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith

lemma affine_ratio (d o : ℕ) : Tendsto (fun t : ℕ => ((d*(t+o):ℕ):ℝ)/t) atTop (𝓝 (d:ℝ)) := by
  have h := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).add
    (tendsto_const_div_atTop_nhds_zero_nat (o:ℝ))
  have hh := h.const_mul (d:ℝ)
  simp only [add_zero,mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  push_cast
  field_simp

lemma scaled_limit {f : ℕ → ℝ} {a : ℝ} (h : Tendsto (fun t : ℕ => f t/t) atTop (𝓝 a))
    (d o : ℕ) (hd : 0<d) : Tendsto (fun t : ℕ => f (d*(t+o))/t) atTop (𝓝 (a*d)) := by
  have htop : Tendsto (fun t : ℕ => d*(t+o)) atTop atTop :=
    tendsto_atTop_mono (fun t => (Nat.le_add_right t o).trans (Nat.le_mul_of_pos_left _ hd)) tendsto_id
  apply ((h.comp htop).mul (affine_ratio d o)).congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hp : (0:ℝ)<(d*(t+o):ℕ) := by exact_mod_cast Nat.mul_pos hd (by omega : 0<t+o)
  dsimp only [Function.comp_apply]
  field_simp

lemma sqrt_ratio : Tendsto (fun k : ℕ => Real.sqrt k/k) atTop (𝓝 0) := by
  simpa only [Real.sqrt_div_self,Function.comp_def] using tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma theta_interval : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ t : ℕ in atTop,
    ε*t ≤ Chebyshev.theta (120*t : ℕ) - Chebyshev.theta (90*(t+1) : ℕ) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let ε := (A-15*log 4)/2
  have he : 0<ε := by dsimp [ε]; linarith [A_pos_gap]
  refine ⟨ε,he,?_⟩
  have f4 := scaled_limit F_limit 4 0 (by decide)
  have f3 := scaled_limit F_limit 3 1 (by decide)
  have l15 := (affine_ratio 15 1).const_mul (log 4)
  have errors := ((scaled_limit sqrt_ratio 120 0 (by decide)).add
    (scaled_limit sqrt_ratio 15 1 (by decide))).const_mul C
  have all := (((f4.sub f3).sub l15).sub errors)
  simp only [add_zero,zero_mul,mul_zero,sub_zero] at all
  have hev := all.eventually_const_lt (show ε < A*4-A*3-log 4*15 by dsimp [ε]; linarith [A_pos_gap])
  filter_upwards [hev,eventually_gt_atTop 0] with t ht hpos
  have l := F_le (4*t)
  have u := psi_le_F (3*(t+1))
  have em := hC (120*t : ℕ)
  have es := hC (15*(t+1) : ℕ)
  have th := Chebyshev.theta_le_log4_mul_x (x := (15*(t+1):ℕ)) (by positivity)
  have su := Chebyshev.theta_le_psi (90*(t+1) : ℕ)
  rw [← Nat.mul_assoc] at l
  rw [← Nat.mul_assoc,← Nat.mul_assoc] at u
  norm_num1 at l u
  have ht' : (0:ℝ)<t := by exact_mod_cast hpos
  change ε < F (4*t)/t-F (3*(t+1))/t - log 4*(_/t) -
    C*(Real.sqrt (120*t:ℕ)/t + Real.sqrt (15*(t+1):ℕ)/t) at ht
  field_simp [ht'.ne'] at ht
  linarith

def primeInterval (u : ℕ) := (Ioc (3*u/2) (2*u)).filter Nat.Prime

lemma supply : ∃ η : ℝ, 0<η ∧ ∀ᶠ u : ℕ in atTop,
    η*u ≤ ((primeInterval u).card : ℝ)*log (2*u : ℕ) := by
  obtain ⟨ε,hε,h⟩ := theta_interval
  refine ⟨ε/120,by positivity,?_⟩
  have hd : Tendsto (fun u : ℕ => u/60) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [eventually_ge_atTop (60*a)] with u hu
    omega
  filter_upwards [hd.eventually h,eventually_ge_atTop 120] with u hu hul
  let t := u/60
  have hlo : 3*u/2 ≤ 90*(t+1) := by dsimp [t]; omega
  have hhi : 120*t ≤ 2*u := by dsimp [t]; omega
  have hlu : u ≤ 120*t := by dsimp [t]; omega
  have hhlo := Chebyshev.theta_mono (Nat.cast_le (α := ℝ).mpr hlo)
  have hhhi := Chebyshev.theta_mono (Nat.cast_le (α := ℝ).mpr hhi)
  have hgap : ε*t ≤ Chebyshev.theta (2*u : ℕ)-Chebyshev.theta (3*u/2 : ℕ) := by linarith
  have hl : ε/120*u ≤ ε*t := by
    have hr : (u:ℝ) ≤ 120*t := by exact_mod_cast hlu
    nlinarith [mul_le_mul_of_nonneg_left hr hε.le]
  refine hl.trans (hgap.trans ?_)
  rw [Chebyshev.theta,Chebyshev.theta,Nat.floor_natCast,Nat.floor_natCast]
  have hcut : 3*u/2 ≤ 2*u := by omega
  have hset : ((Ioc 0 (2*u)).filter Nat.Prime) =
      ((Ioc 0 (3*u/2)).filter Nat.Prime) ∪ primeInterval u := by
    ext x
    by_cases hx : x.Prime <;> simp [primeInterval,mem_Ioc,hx]
    omega
  have hdis : Disjoint ((Ioc 0 (3*u/2)).filter Nat.Prime) (primeInterval u) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (mem_Ioc.mp (mem_filter.mp hx').1).1.not_ge (mem_Ioc.mp (mem_filter.mp hx).1).2
  rw [hset,sum_union hdis,add_sub_cancel_left]
  calc
    _ ≤ ∑ _ ∈ primeInterval u, log (2*u : ℕ) := by
      apply sum_le_sum
      intro q hq
      exact log_le_log (by exact_mod_cast (mem_filter.mp hq).2.pos)
        (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hq).1).2)
    _ = _ := by simp

def digit (B a i : ℕ) := a/B^i%B

def Good (B v a : ℕ) : Prop := ∃ i, digit B a i = v

def box (B v t : ℕ) : Finset ℕ := (range (B^t)).filter fun a => ∀ i < t, digit B a i ≠ v

lemma digit_mod {B a t i : ℕ} (hi : i<t) : digit B (a%B^t) i = digit B a i := by
  unfold digit
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self a]
  rw [← pow_succ,Nat.mod_mod_of_dvd a (pow_dvd_pow B hi)]

lemma residue_mem {B v a : ℕ} (hB : 0<B) (h : ¬Good B v a) (t : ℕ) : a%B^t ∈ box B v t := by
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (pow_pos hB _)),?_⟩
  intro i hi
  rw [digit_mod hi]
  exact fun he => h ⟨i,he⟩

lemma box_card {B v : ℕ} (hB : 0<B) (hv : v<B) (t : ℕ) : (box B v t).card ≤ (B-1)^t := by
  induction t with
  | zero => simp [box]
  | succ t ih =>
    let s := (range B).erase v
    have hh : (box B v (t+1)).card ≤ (s ×ˢ box B v t).card := by
      apply card_le_card_of_injOn (fun a => (a%B,a/B))
      · intro a ha
        obtain ⟨hl,hn⟩ := mem_filter.mp ha
        apply mem_product.mpr
        constructor
        · have h0 := hn 0 (by omega)
          exact mem_erase.mpr ⟨by simpa [digit] using h0,mem_range.mpr (Nat.mod_lt _ hB)⟩
        · apply mem_filter.mpr
          constructor
          · apply mem_range.mpr
            rw [Nat.div_lt_iff_lt_mul hB]
            simpa [pow_succ] using mem_range.mp hl
          · intro i hi
            simpa [digit,Nat.div_div_eq_div_mul,pow_succ',Nat.mul_comm] using hn (i+1) (by omega)
      · intro a _ b _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        have ha := Nat.mod_add_div a B
        have hb := Nat.mod_add_div b B
        change a%B=b%B at h1
        change a/B=b/B at h2
        rw [h1,h2] at ha
        omega
    rw [card_product,show s.card=B-1 by simp [s,card_erase_of_mem,mem_range.mpr hv],pow_succ'] at *
    exact hh.trans (Nat.mul_le_mul_left _ ih)

def bad (B v n u : ℕ) : Finset ℕ := by
  classical
  exact (range (2*u+1)).filter (fun r => ¬Good B v (n+u*r))

lemma bad_card {B v : ℕ} (hB : 1<B) (hv : v<B) (n u : ℕ) (hc : u.Coprime B) :
    (bad B v n u).card ≤ B*(B-1)^(Nat.log B (2*u+1)) := by
  classical
  let t := Nat.log B (2*u+1)
  let M := B^t
  have hM : 0<M := pow_pos (by omega : 0<B) _
  have hupper : 2*u+1 < B*M := by
    simpa [M,t,pow_succ'] using Nat.lt_pow_succ_log_self hB (2*u+1)
  have hh : (bad B v n u).card ≤ (range B ×ˢ box B v t).card := by
    apply card_le_card_of_injOn (fun r => (r/M,(n+u*r)%M))
    · intro r hr
      obtain ⟨hr,hn⟩ := mem_filter.mp hr
      have hlt := mem_range.mp hr
      exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hM).mpr (by omega)),
        residue_mem (by omega) hn t⟩
    · intro r _ s _ he
      have h1 : r/M = s/M := congrArg Prod.fst he
      have h2 : n+u*r ≡ n+u*s [MOD M] := congrArg Prod.snd he
      have h3 : r ≡ s [MOD M] :=
        Nat.ModEq.cancel_left_of_coprime (hc.pow_right t).symm (Nat.ModEq.add_left_cancel' n h2)
      have h4 := Nat.mod_add_div r M
      rw [h3,h1,Nat.mod_add_div] at h4
      exact h4.symm
  rw [card_product,card_range] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (box_card (by omega) hv t))

def cap (B u : ℕ) := B*(B-1)^(Nat.log B (2*u+1))

lemma cap_limit {B : ℕ} (hB : 1<B) :
    Tendsto (fun u : ℕ => (cap B u : ℝ)*log (2*u : ℕ)/u) atTop (𝓝 0) := by
  let t (u : ℕ) := Nat.log B (2*u+1)
  let r : ℝ := ((B-1:ℕ):ℝ)/B
  have hB' : (0:ℝ)<B := by positivity
  have hr : 0≤r := by dsimp [r]; positivity
  have hr' : r<1 := by
    apply (div_lt_one hB').mpr
    exact_mod_cast (by omega : B-1<B)
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop (B^x)] with u hu
    exact Nat.le_log_of_pow_le hB (by omega)
  have hseq := ((tendsto_self_mul_const_pow_of_lt_one hr hr').add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr')).comp ht
  have major := hseq.const_mul (3*(B:ℝ)*log B)
  simp only [zero_add,mul_zero] at major
  apply squeeze_zero' _ _ major
  · filter_upwards [eventually_gt_atTop 0] with u hu
    have hl : 0 ≤ log (2*u:ℕ) := log_nonneg (by exact_mod_cast (by omega : 1≤2*u))
    positivity
  · filter_upwards [eventually_gt_atTop 0] with u hu
    have hu' : (0:ℝ)<u := by exact_mod_cast hu
    have hpow : (B:ℝ)^(t u) ≤ 3*u := by
      exact_mod_cast (Nat.pow_log_le_self B (by omega : 2*u+1 ≠ 0)).trans (by omega : 2*u+1 ≤ 3*u)
    have hlog : log (2*u:ℕ) ≤ (t u+1 : ℕ)*log B := by
      rw [← Real.log_pow]
      apply log_le_log (by positivity)
      exact_mod_cast (Nat.le_succ _).trans (Nat.lt_pow_succ_log_self hB (2*u+1)).le
    have hbnd : ((B-1:ℕ):ℝ)^t u ≤ 3*u * r^(t u) := by
      calc
        _ = (B:ℝ)^t u*r^(t u) := by rw [← mul_pow]; congr 1; dsimp [r]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (pow_nonneg hr _)
    have hl : 0 ≤ log (2*u:ℕ) := log_nonneg (by exact_mod_cast (by omega : 1≤2*u))
    change _ ≤ 3*(B:ℝ)*log B * ((t u:ℝ)*r^(t u) + r^(t u))
    rw [cap,Nat.cast_mul,Nat.cast_pow,div_le_iff₀ hu']
    calc
      _ ≤ (B:ℝ)*(3*u*r^(t u))*((t u+1:ℕ)*log B) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hbnd hB'.le) hlog hl (by positivity)
      _ = _ := by push_cast; ring

def base (n p : ℕ) := p^(n.factorization p+1)
def remDigit (n p : ℕ) := base n p - p

lemma good_primes {n : ℕ} (hn : 0<n) : ∃ u r : ℕ, u.Prime ∧ 2*n<u ∧
    r ∈ primeInterval u ∧ ∀ p ∈ n.primeFactors, Good (base n p) (remDigit n p) (n+u*r) := by
  classical
  obtain ⟨η,hη,hs⟩ := supply
  have hbase (p : ℕ) (hp : p ∈ n.primeFactors) : 1 < base n p :=
    one_lt_pow₀ (Nat.prime_of_mem_primeFactors hp).one_lt (by omega)
  have hlim := tendsto_finsetSum n.primeFactors (fun p hp => cap_limit (hbase p hp))
  simp only [sum_const_zero] at hlim
  have hev := hlim.eventually_lt_const hη
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hs.and hev)
  obtain ⟨u,hu,up⟩ := Nat.exists_infinite_primes (max K (2*n+1))
  have hub : 2*n<u := by omega
  obtain ⟨hsup,hsum⟩ := hK u (by omega)
  suffices hh : ∃ r ∈ primeInterval u, ∀ p ∈ n.primeFactors,
      Good (base n p) (remDigit n p) (n+u*r) by
    obtain ⟨r,hr,hp⟩ := hh
    exact ⟨u,r,up,hub,hr,hp⟩
  by_contra! hh
  have sub : primeInterval u ⊆ n.primeFactors.biUnion (fun p => bad (base n p) (remDigit n p) n u) := by
    intro r hr
    obtain ⟨p,hp,hbad⟩ := hh r hr
    apply mem_biUnion.mpr
    exact ⟨p,hp,mem_filter.mpr ⟨mem_range.mpr (by
      have := (mem_Ioc.mp (mem_filter.mp hr).1).2; omega),hbad⟩⟩
  have hsize := (card_le_card sub).trans card_biUnion_le
  have ub (p : ℕ) (hp : p ∈ n.primeFactors) : (bad (base n p) (remDigit n p) n u).card ≤ cap (base n p) u := by
    obtain ⟨pr,pd,_⟩ := Nat.mem_primeFactors.mp hp
    have pn := Nat.le_of_dvd hn pd
    have hc := (Nat.coprime_primes up pr).mpr (by omega)
    exact bad_card (hbase p hp) (by unfold remDigit; have := hbase p hp; have := pr.pos; omega)
      n u (hc.pow_right _)
  have hsizes := hsize.trans (sum_le_sum ub)
  have hsizes' : ((primeInterval u).card : ℝ) ≤ ∑ p ∈ n.primeFactors, (cap (base n p) u:ℝ) := by
    exact_mod_cast hsizes
  have hl : 0≤log (2*u:ℕ) := log_nonneg (by exact_mod_cast (by omega : 1≤2*u))
  have hpos : (0:ℝ)<u := by exact_mod_cast up.pos
  change (∑ p ∈ n.primeFactors, (cap (base n p) u:ℝ)*log (2*u:ℕ)/u) < η at hsum
  rw [←sum_div,←sum_mul,div_lt_iff₀ hpos] at hsum
  exact hsum.not_ge (hsup.trans (mul_le_mul_of_nonneg_right hsizes' hl))

def Carry (p N i : ℕ) := p^i ≤ N%p^i + N%p^i

def Extra (p N i : ℕ) := Carry p N i ∧ ¬p^i ∣ N+1

lemma catalan_ne_zero (N : ℕ) : catalan N ≠ 0 := by
  intro hh
  have h := succ_mul_catalan_eq_centralBinom N
  rw [hh,mul_zero] at h
  exact (Nat.centralBinom_pos N).ne' h.symm

lemma residue_top {N a : ℕ} (ha : 0<a) (hd : a ∣ N+1) : N%a+1=a := by
  have hh := Nat.mod_eq_zero_of_dvd hd
  rw [← Nat.mod_add_mod] at hh
  have hr := Nat.mod_lt N ha
  by_contra hne
  rw [Nat.mod_eq_of_lt (by omega)] at hh
  omega

/-- Carries at places other than the trailing digits p−1 survive division by N+1. -/
lemma count_extra {p N : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (hs : ∀ i ∈ s, 0 < i ∧ Extra p N i) : s.card ≤ (catalan N).factorization p := by
  classical
  let b := max (Nat.log p (N+N)+Nat.log p (N+1)+1) (s.sup id + 1)
  let R := Ico 1 b
  let D := R.filter fun i => p^i ∣ N+1
  let C := R.filter fun i => p^i ≤ N%p^i + N%p^i
  have hnb : Nat.log p (N+N)<b := by dsimp [b]; omega
  have hnb' : N+1 < p^b := Nat.lt_pow_of_log_lt hp.one_lt (by dsimp [b]; omega)
  have dcard : (N+1).factorization p = D.card :=
    Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) hnb'
  have ccard : N.centralBinom.factorization p = C.card := by
    simpa only [Nat.centralBinom,two_mul,C,R] using (Nat.factorization_choose' (n := N) (k := N) hp hnb)
  have hdis : Disjoint D s := by
    apply Finset.disjoint_left.mpr
    exact fun i hi hi' => (hs i hi').2.2 (mem_filter.mp hi).2
  have hmem : D ∪ s ⊆ C := by
    intro i hi
    rcases mem_union.mp hi with hi|hi
    · obtain ⟨hr,hd⟩ := mem_filter.mp hi
      have hi' := (mem_Ico.mp hr).1
      have ht := residue_top (N := N) (pow_pos hp.pos i) hd
      have hpow := one_lt_pow₀ hp.one_lt (by omega : i≠0)
      exact mem_filter.mpr ⟨hr,by omega⟩
    · have hh := hs i hi
      have hle : i ≤ s.sup id := le_sup (f := id) hi
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hh.1,by dsimp [b]; omega⟩,hh.2.1⟩
  have hcard := card_le_card hmem
  rw [card_union_of_disjoint hdis,←dcard,←ccard,←succ_mul_catalan_eq_centralBinom,
    Nat.factorization_mul (by omega) (catalan_ne_zero _),Finsupp.add_apply] at hcard
  omega

lemma sub_mod_divisor {B z p : ℕ} (hd : z ∣ B) (hz : p≤z) (hp : 0<p) (hB : z≤B) :
    (B-p)%z = z-p := by
  have hh : B-p+p ≡ z-p+p [MOD z] := by
    rw [Nat.sub_add_cancel (by omega),Nat.sub_add_cancel hz]
    exact hd.modEq_zero_nat.trans Nat.modulus_modEq_zero.symm
  have he := Nat.ModEq.add_right_cancel' p hh
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt (by omega : z-p<z)] using he

lemma block_extra {p e N i : ℕ} (hp : p.Prime)
    (hg : digit (p^(e+1)) N i = p^(e+1)-p) {j : ℕ} (hj : 1≤j) (hje : j≤e) :
    Extra p N ((e+1)*i+(j+1)) := by
  let B := p^(e+1)
  let S := p^((e+1)*i)
  let z := p^(j+1)
  have hs : 0<S := pow_pos hp.pos _
  have hdiv : z ∣ B := pow_dvd_pow p (by omega)
  have hb : z≤B := Nat.pow_le_pow_right hp.pos (by omega)
  have hbig : 2*p≤z := by
    calc
      _ ≤ p*p := Nat.mul_le_mul_right p hp.two_le
      _ = p^2 := (sq p).symm
      _ ≤ _ := Nat.pow_le_pow_right hp.pos (by omega)
  have hl : (N/S)%B = B-p := by simpa only [digit,B,S,←pow_mul] using hg
  have hres : (N/S)%z=z-p := by
    rw [←Nat.mod_mod_of_dvd (N/S) hdiv,hl]
    exact sub_mod_divisor hdiv (by omega) hp.pos hb
  have low := Nat.mod_lt N hs
  have hd : p≤z := by omega
  have hp2 := hp.two_le
  have hm : N%(S*z) = N%S + S*(z-p) := by rw [Nat.mod_mul,hres]
  have hpay : S*z ≤ N%(S*z)+N%(S*z) := by
    rw [hm]
    have hh := Nat.mul_le_mul_left S (by omega : z ≤ (z-p)+(z-p))
    rw [Nat.mul_add] at hh
    omega
  have htop : N%(S*z)+1<S*z := by
    rw [hm]
    have hh := Nat.mul_le_mul_left S (by omega : (z-p)+2 ≤ z)
    rw [Nat.mul_add] at hh
    omega
  unfold Extra Carry
  rw [pow_add]
  exact ⟨hpay,fun h => htop.ne (residue_top (by positivity) h)⟩

lemma good_dvd {p e N : ℕ} (hp : p.Prime) (hg : Good (p^(e+1)) (p^(e+1)-p) N) :
    p^e ∣ catalan N := by
  obtain ⟨i,hh⟩ := hg
  have h := count_extra (N := N) hp (Ioc ((e+1)*i+1) ((e+1)*i+1+e)) (by
    intro k hk
    obtain ⟨hl,hr⟩ := mem_Ioc.mp hk
    let j := k-((e+1)*i+1)
    have hj : 1≤j := by dsimp [j]; omega
    have hje : j≤e := by dsimp [j]; omega
    have heq : (e+1)*i+(j+1)=k := by dsimp [j]; omega
    exact ⟨by omega,heq ▸ block_extra hp hh hj hje⟩)
  rw [Nat.card_Ioc] at h
  exact (hp.pow_dvd_iff_le_factorization (catalan_ne_zero N)).mpr (by omega)

lemma large_dvd {p q n : ℕ} (hp : p.Prime) (hn : n+1<p) (hq : p ≤ 2*(q%p)) :
    p ∣ catalan (n+p*q) := by
  let N := n+p*q
  have hn' : n<p := by omega
  have hr : N%(p*p) = n + p*(q%p) := by
    rw [Nat.mod_mul]
    simp only [N,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hn',Nat.add_mul_div_left _ _ hp.pos,
      Nat.div_eq_of_lt hn',zero_add]
  have hc : Carry p N 2 := by
    unfold Carry
    rw [sq,hr]
    nlinarith [Nat.mul_le_mul_left p hq]
  have hd : ¬p^2 ∣ N+1 := by
    intro h
    have h1 := (dvd_pow_self p (by decide : 2≠0)).trans h
    have he : N+1 = (n+1)+p*q := by dsimp [N]; omega
    have h2 := Nat.mod_eq_zero_of_dvd h1
    rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hn] at h2
    omega
  have hs := count_extra (N := N) hp {2} (by
    intro i hi
    obtain rfl := Finset.mem_singleton.mp hi
    exact ⟨by decide,hc,hd⟩)
  exact (hp.dvd_iff_one_le_factorization (catalan_ne_zero _)).mpr (by simpa using hs)

lemma exists_multiplier {n : ℕ} (hn : 0<n) :
    ∃ m : ℕ, 0 < m ∧ m.gcd n=1 ∧ m*n ∣ catalan (m+n) := by
  obtain ⟨u,r,up,hu,hr,hgood⟩ := good_primes hn
  obtain ⟨hrr,rp⟩ := mem_filter.mp hr
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hrr
  have hru : u<r := by omega
  have hr2 : r<2*u := by
    by_contra! he
    have eq : r=2*u := by omega
    have hd : 2 ∣ r := ⟨u,eq⟩
    have := (Nat.dvd_prime_two_le rp (by decide : 2≤2)).mp hd
    omega
  let N := n+u*r
  have hnd : n ∣ catalan N := by
    apply (Nat.factorization_le_iff_dvd hn.ne' (catalan_ne_zero _)).mp
    intro p
    by_cases hp : p ∈ n.primeFactors
    · have pr := Nat.prime_of_mem_primeFactors hp
      exact (pr.pow_dvd_iff_le_factorization (catalan_ne_zero _)).mp (good_dvd pr (hgood p hp))
    · have he : n.factorization p = 0 := by
        simpa only [←Finsupp.notMem_support_iff,Nat.support_factorization] using hp
      simp [he]
  have ud : u ∣ catalan N := by
    have hmod : r%u = r-u := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    exact large_dvd up (by omega) (by rw [hmod]; omega)
  have rd : r ∣ catalan N := by
    dsimp [N]
    rw [Nat.mul_comm u r]
    exact large_dvd rp (by omega) (by rw [Nat.mod_eq_of_lt hru]; omega)
  have hcop : u.Coprime r := (Nat.coprime_primes up rp).mpr hru.ne
  have hn1 : u.Coprime n := up.coprime_iff_not_dvd.mpr (fun hd => by have := Nat.le_of_dvd hn hd; omega)
  have hn2 : r.Coprime n := rp.coprime_iff_not_dvd.mpr (fun hd => by have := Nat.le_of_dvd hn hd; omega)
  have c := Nat.coprime_mul_iff_left.mpr ⟨hn1,hn2⟩
  refine ⟨u*r,Nat.mul_pos up.pos rp.pos,c,?_⟩
  simpa only [N,Nat.add_comm n] using
    c.mul_dvd_of_dvd_of_dvd (hcop.mul_dvd_of_dvd_of_dvd ud rd) hnd

end
end OMA.Catalan248

theorem OMA.solution : type_of% @OeisA248123.conjecture := by
  intro n hn
  obtain ⟨m,hm⟩ := OMA.Catalan248.exists_multiplier hn
  exact (Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ k.gcd n=1 ∧ k*n ∣ catalan (k+n)}) ⟨m,hm⟩).1
