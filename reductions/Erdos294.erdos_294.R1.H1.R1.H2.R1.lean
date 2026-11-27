import OMAReductions.R_Erdos294_erdos_294_R1_H1_R1
import Mathlib

/-!
Use the full pool of admissible divisors. A Bernoulli factor with parameter
between 1/9 and 2/3 has norm at most exp(-(8/27) times the squared
distance of its phase to the nearest integer). This removes the target t
from the estimate. Between N^(3/5) and N/16 there is no modular wrap,
and the reciprocal mass gives a Gaussian bound. Only the more distant
frequencies enter the arithmetic hypothesis.
-/

open Finset Filter
namespace OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1

/-- The full smooth pool on the interval has sufficient reciprocal mass. -/
def H1 : Prop := ∀ c : ℝ, 0<c → ∀ᶠ N : ℕ in atTop,
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  let A := (Icc 1 N).filter fun n => N ≤ 16*n ∧ n ∣ Q
  3*Q ≤ 2*(∑ n ∈ A,Q/n) ∧ (∑ n ∈ A,Q/n) ≤ 3*Q

/-- Far frequencies, expressed solely by distances to integer multiples of 4n. -/
def H2 : Prop := ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  letI : NeZero Q := ⟨Nat.lcmUpto_ne_zero _⟩
  let A := (Icc 1 N).filter fun n => N ≤ 16*n ∧ n ∣ Q
  let far := univ.filter fun h : ZMod (4*Q) => N < 16*h.valMinAbs.natAbs
  (∑ h ∈ far, Real.exp (-(8/27:ℝ)*∑ n ∈ A,
    let x := (h.valMinAbs:ℝ)/(4*n)
    (x - round x)^2)) < 1/2

lemma cos_loss (x : ℝ) : 8*(x-round x)^2 ≤ 1-Real.cos (2*Real.pi*x) := by
  let r := x-(round x:ℝ)
  have hr : |r| ≤ 1/2 := abs_sub_round x
  have hsin' := Real.mul_le_sin (x:=Real.pi*|r|) (by positivity)
    (by nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hr Real.pi_pos.le])
  have he : 2/Real.pi*(Real.pi*|r|)=2*|r| := by field_simp
  rw [he] at hsin'
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2*|r|) hsin' 2
  rw [mul_pow,sq_abs] at hs
  have hp : Real.cos (2*Real.pi*x)=Real.cos (2*(Real.pi*|r|)) := by
    have hper : Real.cos (2*Real.pi*r)=Real.cos (2*Real.pi*x) := by
      dsimp [r]
      rw [show 2*Real.pi*(x-(round x:ℝ))=2*Real.pi*x-(round x:ℝ)*(2*Real.pi) by ring,
        Real.cos_sub_int_mul_two_pi]
    rw [← hper]
    rcases le_or_gt 0 r with h|h
    · rw [abs_of_nonneg h]; congr 1; ring
    · rw [abs_of_neg h,show 2*(Real.pi*(-r))= -(2*Real.pi*r) by ring,Real.cos_neg]
  rw [hp, Real.cos_two_mul]
  change 8*r^2 ≤ _
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi*|r|)]

lemma factor_decay (p x : ℝ) (hp : 1/9 ≤ p) (hq : p ≤ 2/3) :
    ‖1-(p:ℂ)+(p:ℂ)*Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)‖ ≤
      Real.exp (-(8/27:ℝ)*(x-round x)^2) := by
  let z := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  have hz : ‖z‖=1 := by simp [z,Complex.norm_exp]
  have hre : z.re=Real.cos (2*Real.pi*x) := by simp [z,Complex.exp_re]
  have hcircle : z.re*z.re+z.im*z.im=1 := by rw [← Complex.normSq_apply,← Complex.sq_norm,hz]; norm_num
  have heq : ‖1-(p:ℂ)+(p:ℂ)*z‖^2=1-2*p*(1-p)*(1-z.re) := by
    simp [Complex.sq_norm, Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
    nlinarith only [congrArg (fun y:ℝ => p^2*y) hcircle]
  have hcoeff : 1/27 ≤ p*(1-p) := calc
    (1/27:ℝ) = (1/9)*(1/3) := by norm_num
    _ ≤ _ := mul_le_mul hp (by linarith) (by norm_num) (by linarith)
  have hcos := cos_loss x
  rw [← hre] at hcos
  have hpos : 0 ≤ 1-z.re := by nlinarith [sq_nonneg (x-(round x:ℝ))]
  have hmult := mul_le_mul_of_nonneg_right hcoeff hpos
  change ‖1-(p:ℂ)+(p:ℂ)*z‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [heq,pow_two,← Real.exp_add]
  have h := Real.add_one_le_exp ((-(8/27:ℝ)*(x-round x)^2)+(-(8/27:ℝ)*(x-round x)^2))
  nlinarith only [h,hcos,hmult]

lemma char_fraction (Q n : ℕ) [NeZero Q] (hn : 0<n) (hd : n ∣ Q) (h : ZMod (4*Q)) :
    ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h) =
      Complex.exp (((2*Real.pi*((h.valMinAbs:ℝ)/(4*n)):ℝ):ℂ)*Complex.I) := by
  let j := h.valMinAbs
  have hh : (j:ZMod (4*Q))=h := h.coe_valMinAbs
  have hchar (r : ℤ) : ZMod.stdAddChar ((r:ZMod (4*Q))*(j:ZMod (4*Q))) =
      Complex.exp (((2*Real.pi*(j:ℝ)/((4*Q:ℕ):ℝ)*(r:ℝ):ℝ):ℂ)*Complex.I) := by
    rw [←Int.cast_mul,ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have hc := hchar (Q/n:ℕ)
  rw [hh] at hc
  simp only [Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] at hc
  rw [hc]
  have eqn : ((Q/n:ℕ):ℝ)*n=Q := by exact_mod_cast Nat.div_mul_cancel hd
  have hn' : (n:ℝ)≠0 := by positivity
  have hQ : (Q:ℝ)≠0 := by exact_mod_cast NeZero.ne Q
  have hw : ((Q/n:ℕ):ℝ)≠0 := by intro h0; rw [h0,zero_mul] at eqn; exact hQ eqn.symm
  have angle : 2*Real.pi*(j:ℝ)/(4*Q)*((Q/n:ℕ):ℝ)=2*Real.pi*((j:ℝ)/(4*n)) := by
    rw [← eqn]
    field_simp
  rw [angle]

lemma mass_card (N Q : ℕ) [NeZero Q] (A : Finset ℕ)
    (ha : ∀ n ∈ A, N≤16*n ∧ n∣Q) (hm : 3*Q≤2*∑ n∈A,Q/n) : 3*N≤32*A.card := by
  have hb : N*(∑ n ∈ A,Q/n) ≤ A.card*(16*Q) := calc
    _ = ∑ n ∈ A,N*(Q/n) := mul_sum _ _ _
    _ ≤ ∑ _n ∈ A,16*Q := by
      apply sum_le_sum
      intro n hn
      calc
        _ ≤ (16*n)*(Q/n) := Nat.mul_le_mul_right _ (ha n hn).1
        _ = 16*Q := by rw [mul_assoc,Nat.mul_div_cancel' (ha n hn).2]
    _ = _ := by simp
  apply (mul_le_mul_iff_of_pos_right (NeZero.pos Q)).mp
  nlinarith only [Nat.mul_le_mul_left N hm,hb]

lemma medium_weight (N : ℕ) (hN : 0<N) (A : Finset ℕ)
    (ha : ∀ n ∈ A, 0<n ∧ N≤16*n ∧ n≤N) (hc : 3*N ≤ 32*A.card)
    (j : ℤ) (hj : 16*j.natAbs ≤ N) :
    Real.exp (-(8/27:ℝ)*∑ n ∈ A, ((j:ℝ)/(4*n)-round ((j:ℝ)/(4*n)))^2) ≤
      Real.exp (-((j.natAbs:ℝ)^2/(1024*N))) := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have habs : |(j:ℝ)|=(j.natAbs:ℝ) := by rw [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast]
  have hj' : (16:ℝ)*j.natAbs ≤ N := by exact_mod_cast hj
  have hc' : (3:ℝ)*N ≤ 32*A.card := by exact_mod_cast hc
  have term (n) (hn : n∈A) :
      ((j.natAbs:ℝ)/(4*N))^2 ≤ ((j:ℝ)/(4*n)-round ((j:ℝ)/(4*n)))^2 := by
    obtain ⟨hn0,hnl,hnu⟩ := ha n hn
    have hn' : (0:ℝ)<n := by exact_mod_cast hn0
    have hnl' : (N:ℝ)≤16*n := by exact_mod_cast hnl
    have hnu' : (n:ℝ)≤N := by exact_mod_cast hnu
    have hdist : |(j:ℝ)/(4*n)| ≤ 1/4 := by
      rw [abs_div,abs_of_pos (by positivity : 0<(4:ℝ)*n),habs,div_le_iff₀ (by positivity)]
      linarith
    have hr : round ((j:ℝ)/(4*n))=0 := by
      apply round_eq_zero_iff.mpr
      obtain ⟨h1,h2⟩ := abs_le.mp hdist
      exact ⟨by linarith,by linarith⟩
    rw [hr,Int.cast_zero,sub_zero]
    calc
      _ ≤ (|(j:ℝ)/(4*n)|)^2 := by
        rw [abs_div,abs_of_pos (by positivity : 0<(4:ℝ)*n),habs]
        exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by positivity)
          (by positivity) (by linarith)) 2
      _ = _ := sq_abs _
  have hb := sum_le_sum term
  simp only [sum_const,nsmul_eq_mul] at hb
  apply Real.exp_le_exp.mpr
  suffices hbound : (j.natAbs:ℝ)^2/(1024*N) ≤ (8/27)*((A.card:ℝ)*((j.natAbs:ℝ)/(4*N))^2) by linarith
  field_simp [hN'.ne']
  nlinarith only [mul_nonneg (sq_nonneg (j.natAbs:ℝ)) (sub_nonneg.mpr hc'),
    mul_nonneg (sq_nonneg (j.natAbs:ℝ)) hN'.le]

lemma medium_exp (N k : ℕ) (hN : 0<N) (hk : N^3<k^5) :
    Real.exp (-((k:ℝ)^2/(1024*N))) ≤ ((1024^10*Nat.factorial 10:ℕ):ℝ)/N^2 := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hh : (N:ℝ)^3 ≤ (k:ℝ)^5 := by exact_mod_cast hk.le
  have hpow : (N:ℝ)^12 ≤ (k:ℝ)^20 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : (0:ℝ)≤(N:ℝ)^3) hh 4
  let u := (k:ℝ)^2/(1024*N)
  have he := Real.pow_div_factorial_le_exp u (by dsimp [u]; positivity : 0≤u) 10
  change Real.exp (-u) ≤ _
  rw [Real.exp_neg,← one_div,div_le_div_iff₀ (Real.exp_pos _) (by positivity),one_mul]
  calc
    (N:ℝ)^2 ≤ (k:ℝ)^20/N^10 := by rw [le_div_iff₀ (by positivity),← pow_add]; exact hpow
    _ = ((1024^10*Nat.factorial 10:ℕ):ℝ)*(u^10/(Nat.factorial 10:ℝ)) := by
      dsimp [u]; push_cast; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

lemma middle_card (Q N : ℕ) [NeZero Q] (T : Finset (ZMod (4*Q)))
    (h : ∀ j∈T,16*j.valMinAbs.natAbs ≤ N) : T.card ≤ 2*N+1 := by
  have hle : T.card ≤ (Icc (-(N:ℤ)) (N:ℤ)).card := by
    apply card_le_card_of_injOn ZMod.valMinAbs
    · intro j hj
      have hn := h j hj
      have ha := Int.abs_eq_natAbs j.valMinAbs
      apply mem_Icc.mpr
      omega
    · intro a _ b _ h; exact ZMod.valMinAbs_inj.mp h
  rw [Int.card_Icc] at hle
  omega

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos294_erdos_294_R1_H1_R1.H2 := by
  classical
  rintro mass ⟨c,hc,far_estimate⟩
  refine ⟨c,hc,?_⟩
  let K : ℕ := 1024^10 * Nat.factorial 10
  filter_upwards [mass c hc,far_estimate,eventually_ge_atTop (8*K+1)] with N hm hf hlarge
  let Q := Nat.lcmUpto ⌊c*(N:ℝ)/((Real.log N)^3*(Real.log (Real.log N))^4)⌋₊
  have hQ : 0<Q := Nat.lcmUpto_pos _
  letI : NeZero Q := ⟨hQ.ne'⟩
  let A := (Icc 1 N).filter fun n => N≤16*n ∧ n ∣ Q
  let V := ∑ n ∈ A,Q/n
  have ha (n) (hn:n∈A) : 0<n ∧ N≤16*n ∧ n≤N ∧ n∣Q := by
    obtain ⟨hi,hl,hd⟩ := mem_filter.mp hn
    obtain ⟨hp,hu⟩ := mem_Icc.mp hi
    exact ⟨hp,hl,hu,hd⟩
  change 3*Q ≤ 2*V ∧ V ≤ 3*Q at hm
  refine ⟨A,ha,hm.1,hm.2,?_⟩
  intro t hmin hmax
  have hN : 0<N := by omega
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hV : 0<V := by omega
  have hV' : (0:ℝ)<V := by exact_mod_cast hV
  let p : ℝ := (t:ℝ)/V
  have hp : 1/9 ≤ p := by
    apply (le_div_iff₀ hV').mpr
    have h : (V:ℝ)≤9*t := by exact_mod_cast (show V≤9*t by omega)
    linarith
  have hp' : p ≤ 2/3 := by
    apply (div_le_iff₀ hV').mpr
    have h : (3:ℝ)*t ≤ 2*V := by exact_mod_cast (show 3*t≤2*V by omega)
    linarith
  let low := univ.filter fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5≤N^3
  let far := univ.filter fun h : ZMod (4*Q) => N<16*h.valMinAbs.natAbs
  let mid := lowᶜ.filter fun h => 16*h.valMinAbs.natAbs≤N
  let W (h : ZMod (4*Q)) := Real.exp (-(8/27:ℝ)*∑ n∈A,
    ((h.valMinAbs:ℝ)/(4*n)-round ((h.valMinAbs:ℝ)/(4*n)))^2)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
    ∏ n∈A,(1-(p:ℂ)+(p:ℂ)*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))
  change (∑ h∈far,W h) < 1/2 at hf
  have hF (h) : ‖F h‖≤W h := by
    dsimp only [F,W]
    rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul,norm_prod]
    rw [mul_sum,Real.exp_sum]
    apply prod_le_prod (fun _ _ => norm_nonneg _)
    intro n hn
    rw [char_fraction Q n (ha _ hn).1 (ha _ hn).2.2.2]
    exact factor_decay p _ hp hp'
  have hcard := mass_card N Q A (fun n hn => ⟨(ha _ hn).2.1,(ha _ hn).2.2.2⟩) hm.1
  have hmid (h) (hh : h∈mid) : W h ≤ (K:ℝ)/N^2 := by
    obtain ⟨hl,hm'⟩ := mem_filter.mp hh
    have hhi : N^3 < h.valMinAbs.natAbs^5 := by
      simpa [low,ZMod.valMinAbs_natAbs_eq_min] using hl
    exact (medium_weight N hN A (fun n hn => ⟨(ha _ hn).1,(ha _ hn).2.1,(ha _ hn).2.2.1⟩)
      hcard h.valMinAbs hm').trans (medium_exp N _ hN hhi)
  have hcount := middle_card Q N mid (fun _ h => (mem_filter.mp h).2)
  have hmid_total : (∑ h∈mid,W h) < 1/2 := calc
    _ ≤ ∑ _h∈mid,(K:ℝ)/N^2 := sum_le_sum hmid
    _ = (mid.card:ℝ)*((K:ℝ)/N^2) := by simp
    _ ≤ (2*(N:ℝ)+1)*((K:ℝ)/N^2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ < 1/2 := by
      have hNK : (8:ℝ)*K+1 ≤ N := by exact_mod_cast hlarge
      have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
      rw [← mul_div_assoc,div_lt_iff₀ (by positivity)]
      have h1 := mul_le_mul_of_nonneg_right (show 2*(N:ℝ)+1≤3*N by linarith) (show (0:ℝ)≤K by positivity)
      have h2 := mul_lt_mul_of_pos_left (show 6*(K:ℝ)<N by linarith [show (0:ℝ)≤K by positivity]) hN'
      calc
        _ ≤ 3*(N:ℝ)*K := h1
        _ = (1/2:ℝ)*(N*(6*(K:ℝ))) := by ring
        _ < (1/2:ℝ)*(N*N) := mul_lt_mul_of_pos_left h2 (by norm_num)
        _ = _ := by ring
  have hrest : lowᶜ.filter (fun h => ¬ 16*h.valMinAbs.natAbs≤N) ⊆ far := by
    intro h hh
    exact mem_filter.mpr ⟨mem_univ _,lt_of_not_ge (mem_filter.mp hh).2⟩
  have he := sum_filter_add_sum_filter_not lowᶜ (fun h => 16*h.valMinAbs.natAbs≤N) W
  have hfar := sum_le_sum_of_subset_of_nonneg (f:=W) hrest (fun h _ _ => (Real.exp_pos _).le)
  change (∑ h∈mid,W h) + _ = _ at he
  have bound : (∑ h∈lowᶜ,W h)<1 := by linarith
  have complete := lt_of_le_of_lt ((norm_sum_le lowᶜ F).trans (sum_le_sum (fun h _ => hF h))) bound
  have hpC : (p:ℂ) = (t:ℂ)/(V:ℂ) := by simp only [p,Complex.ofReal_div, Complex.ofReal_natCast]
  dsimp only [F] at complete
  rw [hpC] at complete
  exact complete

end OMA.R_Erdos294_erdos_294_R1_H1_R1_H2_R1
