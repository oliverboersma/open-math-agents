import OMAReductions.R_Erdos294_erdos_294_R1_H1_R1
import Mathlib

open Finset Complex
namespace OMA.EgyptianFourier

private lemma cubic (u : ℝ) (hu : |u| ≤ 1) :
    ‖Complex.exp ((u:ℂ)*I) - (1+(u:ℂ)*I-(u:ℂ)^2/2)‖ ≤ 3*|u|^3 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((u:ℂ)*I) 3
  have hn : ‖(u:ℂ)*I‖ = |u| := by simp
  rw [hn] at h
  have hpoly : (∑ m ∈ range 3, ((u:ℂ)*I)^m / m.factorial) =
      1+(u:ℂ)*I-(u:ℂ)^2/2 := by
    norm_num [sum_range_succ,mul_pow,Complex.I_sq]
    <;> ring
  rw [hpoly] at h
  have he : Real.exp |u| ≤ 3 := (Real.exp_le_exp.mpr hu).trans
    (by linarith [Real.exp_one_lt_d9])
  nlinarith only [h,mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg u) 3)]

private lemma centered (p x : ℝ) (hp : 0≤p) (hp' : p≤1) (hx : |x|≤1) :
    ‖(1-(p:ℂ))*Complex.exp (((-p*x:ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*x:ℝ):ℂ)*I) -
      ((1-p*(1-p)*x^2/2:ℝ):ℂ)‖ ≤ 3*|x|^3 := by
  let q (s:ℝ) : ℂ := 1+(s:ℂ)*I-(s:ℂ)^2/2
  let E (s:ℝ) : ℂ := Complex.exp ((s:ℂ)*I)-q s
  have hl : |(-p)*x| ≤ |x| := by
    rw [abs_mul,abs_neg,abs_of_nonneg hp]
    exact mul_le_of_le_one_left (abs_nonneg _) hp'
  have hr : |(1-p)*x| ≤ |x| := by
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤1-p)]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  have hE (s:ℝ) (h : |s|≤|x|) : ‖E s‖ ≤ 3*|x|^3 :=
    (cubic _ (h.trans hx)).trans (by gcongr)
  calc
    _ = ‖(1-(p:ℂ))*E (-p*x)+(p:ℂ)*E ((1-p)*x)‖ := by
      congr 1
      dsimp only [E,q]
      push_cast
      ring
    _ ≤ ‖(1-(p:ℂ))*E (-p*x)‖ + ‖(p:ℂ)*E ((1-p)*x)‖ := norm_add_le _ _
    _ = (1-p)*‖E (-p*x)‖ + p*‖E ((1-p)*x)‖ := by
      rw [norm_mul,norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp,
        abs_of_nonneg (by linarith : 0≤1-p)]
    _ ≤ (1-p)*(3*|x|^3)+p*(3*|x|^3) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hE _ hl) (by linarith))
        (mul_le_mul_of_nonneg_left (hE _ hr) hp)
    _ = _ := by ring

/-- A product of centered Bernoulli factors has nonnegative real part if
each increment is small and their absolute cubes have small total. -/
theorem positive_product (A : Finset ℕ) (p : ℝ) (x : ℕ → ℝ)
    (hp : 0≤p) (hp' : p≤1) (hx : ∀ n ∈ A, |x n|≤1)
    (hsmall : 6*(∑ n ∈ A, |x n|^3) ≤ 1/4) :
    0 ≤ (∏ n ∈ A, ((1-(p:ℂ))*Complex.exp (((-p*x n:ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*x n:ℝ):ℂ)*I))).re := by
  let d (n:ℕ) : ℝ := 1-p*(1-p)*(x n)^2/2
  let z (n:ℕ) : ℂ := (1-(p:ℂ))*Complex.exp (((-p*x n:ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*x n:ℝ):ℂ)*I)
  let e (n:ℕ) : ℂ := (z n-(d n:ℂ))/(d n:ℂ)
  have hd (n) (hn:n∈A) : 1/2 ≤ d n := by
    have hb := abs_le.mp (hx n hn)
    have h1 : (x n)^2 ≤ 1 := by nlinarith [mul_nonneg (show 0≤1-x n by linarith) (show 0≤1+x n by linarith)]
    have h2 : p*(1-p) ≤ 1 := by nlinarith [sq_nonneg p]
    dsimp only [d]
    nlinarith only [mul_le_mul h2 h1 (sq_nonneg _) (by norm_num : (0:ℝ)≤1)]
  have he (n) (hn:n∈A) : ‖e n‖ ≤ 6*|x n|^3 := by
    have hdpos : 0<d n := by linarith [hd n hn]
    dsimp only [e]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hdpos.le,div_le_iff₀ hdpos]
    have h := centered p (x n) hp hp' (hx n hn)
    change ‖z n-(d n:ℂ)‖ ≤ _ at h
    nlinarith only [h,mul_le_mul_of_nonneg_left (hd n hn) (show 0≤6*|x n|^3 by positivity)]
  have herr : (∑ n ∈ A, ‖e n‖) ≤ 1/4 := calc
    _ ≤ ∑ n ∈ A, 6*|x n|^3 := sum_le_sum he
    _ ≤ _ := by rwa [←mul_sum]
  have hn := A.norm_prod_one_add_sub_one_le e
  have hequarter : Real.exp (1/4) < 2 := (Real.exp_lt_two_add_div_two_sub (by norm_num) (by norm_num)).trans (by norm_num)
  have hab := Complex.abs_re_le_norm ((∏ n ∈ A, (1+e n))-1)
  rw [Complex.sub_re,Complex.one_re] at hab
  have hpos : 0 ≤ (∏ n ∈ A, (1+e n)).re := by
    linarith [(abs_le.mp (hab.trans hn)).1, Real.exp_le_exp.mpr herr]
  change 0 ≤ (∏ n ∈ A, z n).re
  have hz (n) (hn:n∈A) : z n = (d n:ℂ)*(1+e n) := by
    have hdpos : 0<d n := by linarith [hd n hn]
    dsimp only [e]
    field_simp [show (d n:ℂ) ≠ 0 by exact_mod_cast hdpos.ne']
    <;> ring
  rw [prod_congr rfl hz,prod_mul_distrib,←Complex.ofReal_prod]
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (prod_nonneg fun n hn => (show 0≤d n by linarith [hd n hn])) hpos



private lemma frequencies (N k : ℕ) (hN : 1000000^5 ≤ N) (hk : k^5 ≤ N^3) :
    32*k ≤ N ∧ 786432*k^3 ≤ N^2 := by
  have hge : 1≤N := by omega
  constructor
  · apply (Nat.pow_le_pow_iff_left (by decide : (5:ℕ)≠0)).mp
    calc
      (32*k)^5 = 32^5*k^5 := mul_pow _ _ _
      _ ≤ N*N^3 := Nat.mul_le_mul (by omega) hk
      _ = N^4 := by ring
      _ ≤ N^5 := Nat.pow_le_pow_right hge (by decide)
  · apply (Nat.pow_le_pow_iff_left (by decide : (5:ℕ)≠0)).mp
    calc
      (786432*k^3)^5 = 786432^5*(k^5)^3 := by ring
      _ ≤ N*(N^3)^3 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hk 3)
      _ = (N^2)^5 := by ring

private lemma char_int (M : ℕ) [NeZero M] (r j : ℤ) :
    ZMod.stdAddChar ((r:ZMod M)*(j:ZMod M)) =
      Complex.exp (((2*Real.pi*(j:ℝ)/(M:ℝ)*(r:ℝ):ℝ):ℂ)*I) := by
  rw [←Int.cast_mul,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private lemma centers (A : Finset ℕ) (w : ℕ → ℕ) (t : ℕ) (u : ℝ) (p : ℝ)
    (hp : p*(∑ n ∈ A,(w n:ℝ))=t) :
    Complex.exp (((u*(-(t:ℝ)):ℝ):ℂ)*I) *
      (∏ n ∈ A, (1-(p:ℂ)+(p:ℂ)*Complex.exp (((u*w n:ℝ):ℂ)*I))) =
    ∏ n ∈ A, ((1-(p:ℂ))*Complex.exp (((-p*(u*w n):ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*(u*w n):ℝ):ℂ)*I)) := by
  have he (n:ℕ) : ((1-(p:ℂ))*Complex.exp (((-p*(u*w n):ℝ):ℂ)*I) +
      (p:ℂ)*Complex.exp ((((1-p)*(u*w n):ℝ):ℂ)*I)) =
      Complex.exp (((-p*(u*w n):ℝ):ℂ)*I) *
        (1-(p:ℂ)+(p:ℂ)*Complex.exp (((u*w n:ℝ):ℂ)*I)) := by
    push_cast
    rw [show (1-(p:ℂ))*((u:ℂ)*w n)*I = (-p:ℂ)*((u:ℂ)*w n)*I + (u:ℂ)*w n*I by ring,
      Complex.exp_add]
    ring
  simp_rw [he]
  rw [prod_mul_distrib,←Complex.exp_sum]
  congr 2
  have hx : u*(-(t:ℝ)) = ∑ n ∈ A, -p*(u*w n) := by
    simp_rw [show ∀ n : ℕ, -p*(u*w n)=(-u*p)*(w n) from fun n => by ring,←mul_sum]
    rw [←hp];ring
  rw [hx,Complex.ofReal_sum,Finset.sum_mul]


theorem low (N Q : ℕ) [NeZero Q] (hN : 1000000^5 ≤ N)
    (A : Finset ℕ) (ha : ∀ n ∈ A, 0<n ∧ N≤16*n ∧ n≤N ∧ n∣Q)
    (hmass : 3*Q ≤ 2*(∑ n ∈ A,Q/n)) (t : ℕ) (ht : t≤Q) :
    let V := ∑ n ∈ A,Q/n
    let P : ℂ := (t:ℂ)/(V:ℂ)
    let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
    let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
      ∏ n ∈ A, (1-P+P*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))
    1 ≤ (∑ h ∈ S,F h).re := by
  classical
  let V := ∑ n ∈ A,Q/n
  let p : ℝ := (t:ℝ)/V
  have hQ : 0<Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hV : 0<V := by change 3*Q ≤ 2*V at hmass; omega
  have hV' : (0:ℝ)<V := by exact_mod_cast hV
  have hp : 0≤p := by dsimp [p];positivity
  have hp' : p≤1 := by
    apply (div_le_iff₀ hV').mpr
    rw [one_mul]
    change 3*Q ≤ 2*V at hmass
    exact_mod_cast (show t≤V by omega)
  have hpV : p*(∑ n ∈ A,((Q/n:ℕ):ℝ))=t := by
    rw [←Nat.cast_sum]; exact div_mul_cancel₀ _ hV'.ne'
  let S := Finset.univ.filter (fun h : ZMod (4*Q) => (min h.val (4*Q-h.val))^5 ≤ N^3)
  let F (h : ZMod (4*Q)) := ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
      ∏ n ∈ A, (1-(p:ℂ)+(p:ℂ)*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))
  have hP : (t:ℂ)/(V:ℂ)=(p:ℂ) := by simp [p]
  change 1 ≤ (∑ h ∈ S, ZMod.stdAddChar ((-(t:ZMod (4*Q)))*h) *
    ∏ n ∈ A, (1-(t:ℂ)/(V:ℂ)+(t:ℂ)/(V:ℂ)*ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h))).re
  rw [hP]
  change 1 ≤ (∑ h ∈ S,F h).re
  have hz : (0:ZMod (4*Q))∈S := by simp [S]
  have hzero : F 0=1 := by simp [F]
  have nonneg (h) (hh:h∈S) : 0≤(F h).re := by
    let j := ZMod.valMinAbs h
    let k := j.natAbs
    let u : ℝ := 2*Real.pi*j/((4*Q:ℕ):ℝ)
    let x (n:ℕ) : ℝ := u*(Q/n:ℕ)
    have hk : k^5≤N^3 := by
      have hh' := (Finset.mem_filter.mp hh).2
      simpa only [k,j,ZMod.valMinAbs_natAbs_eq_min] using hh'
    obtain ⟨hlin,hcub⟩ := frequencies N k hN hk
    have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hQp : (0:ℝ)<Q := by exact_mod_cast hQ
    have hjabs : |(j:ℝ)|=(k:ℝ) := by
      dsimp only [k]; rw [←Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hx (n : ℕ) (hn:n∈A) : |x n| ≤ 32*(k:ℝ)/N := by
      obtain ⟨hn₀,hn₁,_,hd⟩ := ha n hn
      have hnpos : (0:ℝ)<n := by exact_mod_cast hn₀
      have hdiv : ((Q/n:ℕ):ℝ) = Q/n := by
        apply (eq_div_iff hnpos.ne').mpr
        exact_mod_cast Nat.div_mul_cancel hd
      have heq : x n = Real.pi*j/(2*n) := by
        dsimp only [x,u]; rw [hdiv];push_cast
        field_simp;ring
      rw [heq,abs_div,abs_mul,abs_of_pos Real.pi_pos,hjabs,
        abs_of_pos (by positivity : (0:ℝ)<2*n)]
      apply (div_le_div_iff₀ (by positivity) hNp).mpr
      calc
        _ ≤ (4*(k:ℝ))*(16*n) := mul_le_mul
          (mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)) (by exact_mod_cast hn₁)
          (by positivity) (by positivity)
        _ = _ := by ring
    have hx₁ (n) (hn:n∈A) : |x n|≤1 := (hx n hn).trans
      ((div_le_one hNp).mpr (by exact_mod_cast hlin))
    have hcard : A.card ≤ N := by
      have hs : A ⊆ Finset.Icc 1 N := fun n hn => Finset.mem_Icc.mpr
        ⟨(ha n hn).1,(ha n hn).2.2.1⟩
      simpa using Finset.card_le_card hs
    have hsum : (∑ n ∈ A, |x n|^3) ≤ (N:ℝ)*(32*k/N)^3 := calc
      _ ≤ ∑ _n ∈ A,(32*(k:ℝ)/N)^3 := sum_le_sum fun n hn => by gcongr;exact hx n hn
      _ = (A.card:ℝ)*(32*k/N)^3 := by simp
      _ ≤ _ := by gcongr
    have hsmall : 6*(∑ n ∈ A,|x n|^3) ≤ 1/4 := by
      apply le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
      apply (mul_le_mul_iff_of_pos_right (pow_pos hNp 2)).mp
      calc
        _ = 196608*(k:ℝ)^3 := by field_simp;ring
        _ ≤ _ := by
          have hc : 786432*(k:ℝ)^3 ≤ (N:ℝ)^2 := by exact_mod_cast hcub
          linarith
    have hchar (r:ℤ) : ZMod.stdAddChar ((r:ZMod (4*Q))*h) =
        Complex.exp (((u*(r:ℝ):ℝ):ℂ)*I) := by
      have H := char_int (4*Q) r j
      rw [show (j:ZMod (4*Q)) = h from h.coe_valMinAbs] at H
      exact H
    have hneg := hchar (-(t:ℤ))
    push_cast at hneg
    have hpos (n:ℕ) : ZMod.stdAddChar (((Q/n:ℕ):ZMod (4*Q))*h) =
        Complex.exp (((u*(Q/n:ℕ):ℝ):ℂ)*I) := by simpa only [Int.cast_natCast] using hchar ((Q/n:ℕ):ℤ)
    dsimp only [F]
    simp_rw [hneg,hpos]
    have hcen := centers A (fun n=>Q/n) t u p hpV
    push_cast at hcen ⊢
    rw [hcen]
    have H := positive_product A p x hp hp' hx₁ hsmall
    dsimp only [x] at H
    push_cast at H
    exact H
  have h := Finset.single_le_sum nonneg hz
  rw [hzero,Complex.one_re] at h
  simpa only [Complex.re_sum] using h

end OMA.EgyptianFourier

open Filter

theorem OMA.solution : OMA.R_Erdos294_erdos_294_R1_H1_R1.H1 := by
  filter_upwards [eventually_ge_atTop (1000000^5 : ℕ)] with N hN
  intro Q _ A ha hmass _ t _ ht
  exact OMA.EgyptianFourier.low N Q hN A ha hmass t ht
