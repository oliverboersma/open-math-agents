import OMAReductions.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1

open Finset Filter Real

private lemma centered_expansion {ι : Type*} (S : Finset ι) (a : ι → ℝ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ t : ℝ, ∏ i ∈ S, (1+a i*t) =
      1+(∑ i ∈ S,a i)*t+t^2*g t := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,continuous_const,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨g,hg,he⟩ := ih
    refine ⟨fun t => (1+a i*t)*g t + a i*(∑ j ∈ S,a j),by fun_prop,?_⟩
    intro t
    rw [prod_insert hi,sum_insert hi,he]
    ring

private lemma centered_root {ι : Type*} (S : Finset ι) (a : ι → ℝ) (hS : 1 ≤ S.card)
    (ha : ∑ i ∈ S, a i = 0) : ∃ K : ℝ, 0 < K ∧
    ∀ (x : ℕ) (Y : ℝ), 0 < Y → Y^S.card = ∏ i ∈ S, ((x:ℝ)+a i) →
      |Y-(x:ℝ)| ≤ K/Y := by
  obtain ⟨g,hg,he⟩ := centered_expansion S a
  obtain ⟨L,hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Set.Icc (0:ℝ) 1) hg.continuousOn
  let C := max L 1
  let P := |∏ i ∈ S,a i|+1
  have cp : 0 < C := lt_of_lt_of_le one_pos (le_max_right ..)
  have pp : 0 < P := by dsimp [P]; positivity
  refine ⟨C*(1+C)+P^2+1,by positivity,?_⟩
  intro x Y hy eqn
  rw [le_div_iff₀ hy]
  by_cases hx : x = 0
  · subst x
    simp only [Nat.cast_zero,zero_add] at eqn
    simp only [Nat.cast_zero,sub_zero,abs_of_pos hy]
    have yl : Y ≤ P := by
      by_cases y1 : Y ≤ 1
      · exact y1.trans (by dsimp [P]; linarith [abs_nonneg (∏ i ∈ S,a i)])
      · calc Y = Y^1 := (pow_one _).symm
             _ ≤ Y^S.card := pow_le_pow_right₀ (by linarith) hS
             _ ≤ P := by dsimp [P]; rw [← eqn,abs_of_pos (pow_pos hy _)]; linarith
    nlinarith [mul_self_le_mul_self hy.le yl,mul_nonneg cp.le (by linarith : 0 ≤ 1+C)]
  · have x1 : (1:ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
    have xp : (0:ℝ) < x := by linarith
    have hx0 := xp.ne'
    have hp : (Y/(x:ℝ))^S.card = ∏ i ∈ S, (1+a i*(x:ℝ)⁻¹) := by
      rw [div_pow,eqn,← Finset.prod_const (b:=(x:ℝ)) (s:=S),←prod_div_distrib]
      apply prod_congr rfl
      intro i hi
      field_simp
    have gt := hL (x:ℝ)⁻¹ (show (x:ℝ)⁻¹ ∈ Set.Icc 0 1 from
      ⟨inv_nonneg.mpr xp.le,inv_le_one_of_one_le₀ x1⟩)
    rw [Real.norm_eq_abs] at gt
    rw [he,ha,zero_mul,add_zero] at hp
    let z := Y/(x:ℝ)
    have zp : 0 < z := div_pos hy xp
    have d1 : |z-1| ≤ |z^S.card-1| := by
      rcases le_or_gt 1 z with hj|hj
      · have hl : z ≤ z^S.card := by simpa using pow_le_pow_right₀ hj hS
        rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
        linarith
      · have hl : z^S.card ≤ z := by simpa using pow_le_pow_of_le_one zp.le hj.le hS
        rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
        linarith
    have d2 : |z^S.card-1| ≤ (x:ℝ)⁻¹^2*C := by
      change |(Y/(x:ℝ))^S.card-1| ≤ _
      rw [hp,add_sub_cancel_left,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (gt.trans (le_max_left ..)) (sq_nonneg _)
    have heq : Y-(x:ℝ) = (z-1)*(x:ℝ) := by dsimp [z]; field_simp
    have diff : |Y-(x:ℝ)| *(x:ℝ) ≤ C := by
      rw [heq,abs_mul,abs_of_pos xp]
      have hh := mul_le_mul_of_nonneg_right (d1.trans d2) (sq_nonneg (x:ℝ))
      calc _ = |z-1| *(x:ℝ)^2 := by ring
           _ ≤ ((x:ℝ)⁻¹^2*C)*(x:ℝ)^2 := hh
           _ = C := by field_simp
    have dx : |Y-(x:ℝ)| ≤ C := by
      calc _ ≤ |Y-(x:ℝ)| *(x:ℝ) := le_mul_of_one_le_right (abs_nonneg _) x1
           _ ≤ C := diff
    have yb : Y ≤ (x:ℝ)*(1+C) := by
      have := (abs_le.mp dx).2
      nlinarith [mul_nonneg (sub_nonneg.mpr x1) cp.le]
    calc |Y-(x:ℝ)| *Y ≤ |Y-(x:ℝ)| *((x:ℝ)*(1+C)) :=
           mul_le_mul_of_nonneg_left yb (abs_nonneg _)
         _ = (|Y-(x:ℝ)| *(x:ℝ))*(1+C) := by ring
         _ ≤ C*(1+C) := mul_le_mul_of_nonneg_right diff (by linarith)
         _ ≤ _ := by linarith [sq_nonneg P]

private lemma scale_id {n b r : ℕ} (hb : 0 < b) (hbn : b ≤ n) (hr : 0 < r) (hdiv : r ∣ b) :
    let Y := fun m : ℕ => (r:ℝ)*(m.factorial:ℝ)^(1/(r:ℝ))
    let w := ∏ j ∈ Ico 1 b, (1-(j:ℝ)/n)^(-(1:ℝ)/r)
    w*Y n = (n^(b/r):ℕ)*Y (n-b) ∧ 1 ≤ w ∧ Y (n-b) ≤ Y n := by
  intro Y w
  have nr : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have rr : 0 < (r:ℝ) := by exact_mod_cast hr
  have yn (m:ℕ) : 0 < Y m := by dsimp [Y]; positivity
  have hY (m:ℕ) : (Y m)^r=(r:ℝ)^r*(m.factorial:ℝ) := by
    dsimp [Y]
    rw [mul_pow,← Real.rpow_mul_natCast (by positivity),one_div_mul_cancel (by positivity),Real.rpow_one]
  have hrange : range b = insert 0 (Ico 1 b) := by
    ext j
    simp only [mem_range,mem_insert,mem_Ico]
    omega
  let f (j:ℕ) := (1-(j:ℝ)/n)^(-(1:ℝ)/r)
  have hleft (j:ℕ) (hj:j ∈ range b) : 0 < 1-(j:ℝ)/n := by
    have hjn : (j:ℝ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le (mem_range.mp hj) hbn)
    exact sub_pos.mpr ((div_lt_one nr).2 hjn)
  have prodEq : w = ∏ j ∈ range b, f j := by
    rw [hrange,prod_insert (by simp)]
    simp [f,w]
  have wone : 1 ≤ w := by
    rw [prodEq]
    apply Finset.one_le_prod
    intro j hj
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hleft j hj)
    · linarith [div_nonneg (Nat.cast_nonneg j (α:=ℝ)) nr.le]
    · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) rr.le
  have pw : w^r = (n:ℝ)^b/(n.descFactorial b:ℝ) := by
    rw [prodEq,← prod_pow]
    calc _ = ∏ j ∈ range b, (n:ℝ)/((n-j:ℕ):ℝ) := by
           apply prod_congr rfl
           intro j hj
           dsimp [f]
           rw [← Real.rpow_mul_natCast (hleft j hj).le,
             show (-(1:ℝ)/r)*r = -1 by field_simp,Real.rpow_neg_one,
             Nat.cast_sub ((mem_range.mp hj).le.trans hbn)]
           field_simp [nr.ne',(hleft j hj).ne']
         _ = _ := by simp only [prod_div_distrib,prod_const,card_range,
                      Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have eqn : ((n-b).factorial:ℝ)*(n.descFactorial b:ℝ)=(n.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hbn
  have dp : 0 < (n.descFactorial b:ℝ) := by
    by_contra! hh
    have z := Nat.cast_nonneg (n.descFactorial b) (α:=ℝ)
    have d0 : (n.descFactorial b:ℝ)=0 := by linarith
    rw [d0,mul_zero] at eqn
    have : 0 < (n.factorial:ℝ) := by positivity
    linarith
  refine ⟨?_,wone,?_⟩
  · apply (pow_left_inj₀ (mul_nonneg (by linarith) (yn n).le) (by positivity) hr.ne').mp
    rw [mul_pow,pw,hY,mul_pow,hY,Nat.cast_pow,← pow_mul,Nat.div_mul_cancel hdiv,←eqn]
    field_simp
  · apply mul_le_mul_of_nonneg_left _ rr.le
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.sub_le n b)) (by positivity)

private lemma factorial_scale_growth (r : ℕ) (hr : 0 < r) (K η : ℝ)
    (hK : 0 < K) (hη : 0 < η) : ∀ᶠ n : ℕ in atTop, ∀ b : ℕ,
    (b:ℝ) ≤ (n:ℝ)^(1/34:ℝ) →
    K*((n:ℝ)^b)^2 ≤ ((r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ)))^η := by
  have rr : 0 < (r:ℝ) := by exact_mod_cast hr
  have r1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  let c := η/(r:ℝ)*log 2
  have cp : 0 < c := mul_pos (div_pos hη rr) (log_pos (by norm_num))
  have ts := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ts.eventually_ge_atTop ((|log K|+9)/c+1),eventually_ge_atTop 2] with n hbig hn
  intro b hb
  change (|log K|+9)/c+1 ≤ sqrt (n:ℝ) at hbig
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have np : 0 < (n:ℝ) := by linarith
  have sn : 1 ≤ sqrt (n:ℝ) := by simpa using Real.sqrt_le_sqrt n1
  have st : c*(n:ℝ) ≥ log K+8*sqrt n+c := by
    have hc : |log K|+9 ≤ (sqrt n-1)*c := (div_le_iff₀ cp).mp (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (n:ℝ))
    have hl := mul_le_mul_of_nonneg_left sn (abs_nonneg (log K))
    have hcs := mul_le_mul_of_nonneg_left sn cp.le
    have sq := congrArg (fun z : ℝ => c*z) (Real.sq_sqrt np.le)
    nlinarith only [hmul,hl,hcs,le_abs_self (log K),sq,sn] 
  have hpow : 2^(n-1) ≤ n.factorial := by
    have h := @Nat.factorial_mul_pow_le_factorial 1 (n-1)
    simpa [show 1+(n-1)=n by omega] using h
  have hf : (n:ℝ)*log 2-log 2 ≤ log (n.factorial:ℝ) := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<2^(n-1)) (by exact_mod_cast hpow : (2:ℝ)^(n-1) ≤ n.factorial)
    rw [Real.log_pow,Nat.cast_sub (by omega),Nat.cast_one] at h
    linarith
  have hp := mul_le_mul_of_nonneg_left hf (div_pos hη rr).le
  have hl := Real.log_le_rpow_div np.le (by norm_num : 0 < (1/4:ℝ))
  have hb' := hb.trans (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (1/34:ℝ) ≤ 1/4))
  have hm := mul_le_mul hb' hl (Real.log_nonneg n1) (Real.rpow_nonneg np.le _)
  have hsq : (n:ℝ)^(1/4:ℝ)*(n:ℝ)^(1/4:ℝ) = sqrt n := by
    rw [← Real.rpow_add np,Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hs : (b:ℝ)*log n ≤ 4*sqrt n := by nlinarith only [hm,hsq]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul hK.ne' (by positivity),Real.log_pow,Real.log_pow,
    Real.log_rpow (by positivity),Real.log_mul rr.ne' (by positivity),
    Real.log_rpow (by positivity)]
  have zr := mul_nonneg hη.le (Real.log_nonneg r1)
  dsimp [c] at st
  simp only [div_eq_mul_inv,one_mul,Nat.cast_ofNat] at st hp ⊢
  nlinarith only [st,hp,hs,zr]

private lemma shifted_approx {x z : ℕ} {Y Z w C m : ℝ} (ypos : 0 < Y)
    (zpos : 0 < Z) (cp : 0 < C) (mw : 1 ≤ w) (zy : Z ≤ Y)
    (eq : w*Y=m*Z) (ex : |Y-(x:ℝ)| ≤ C/Y) (ez : |Z-(z:ℝ)| ≤ C/Z) :
    |(x:ℝ)*w-m*z| ≤ 2*C*m^2/Y := by
  have mp : 0 < m := by
    by_contra! h
    have := mul_nonpos_of_nonpos_of_nonneg h zpos.le
    nlinarith [mul_pos (show 0 < w by linarith) ypos]
  have wm : w ≤ m := by
    apply le_of_mul_le_mul_right (a:=Y) _ ypos
    rw [eq]
    exact mul_le_mul_of_nonneg_left zy mp.le
  have yM : Y ≤ m*Z := by
    rw [←eq]
    exact le_mul_of_one_le_left ypos.le mw
  have he : (x:ℝ)*w-m*z = -((Y-(x:ℝ))*w)+m*(Z-(z:ℝ)) := by linarith
  rw [he]
  refine (abs_add_le ..).trans ?_
  rw [abs_neg,abs_mul,abs_mul,abs_of_pos (lt_of_lt_of_le one_pos mw),abs_of_pos mp]
  have p1 := mul_le_mul ex wm (by linarith : 0 ≤ w) (div_nonneg cp.le ypos.le)
  have p2 := mul_le_mul_of_nonneg_left ez mp.le
  have hfrac : C/Z ≤ C*m/Y := by
    rw [div_le_div_iff₀ zpos ypos]
    nlinarith only [mul_le_mul_of_nonneg_left yM cp.le]
  have m1 : 1 ≤ m := mw.trans wm
  have hh := mul_le_mul_of_nonneg_right m1 (mul_nonneg cp.le mp.le)
  have h3 := p2.trans (mul_le_mul_of_nonneg_left hfrac mp.le)
  calc _ ≤ C/Y*m + m*(C*m/Y) := add_le_add p1 h3
       _ ≤ _ := by
           field_simp
           nlinarith only [hh,m1]

theorem OMA.solution : OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1.H1 := by
  intro T hr η hη r Y w sol
  let a := fun i : ℕ => (r:ℝ)*i-(∑ j∈T,(j:ℝ))
  have rr : 0 < (r:ℝ) := by exact_mod_cast (show 0 < r by change 2 ≤ r at hr; omega)
  have rpos : 0 < r := by exact_mod_cast rr
  have yp (n:ℕ) : 0 < Y n := by dsimp [Y]; positivity
  have zero : ∑ i∈T, a i=0 := by
    simp only [a,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    change (r:ℝ)*_-(r:ℝ)*_=0
    ring
  obtain ⟨C,hC,hroot⟩ := centered_root T a (by omega) zero
  have aprox {n x:ℕ} (h : sol n x) : |Y n-(x:ℝ)| ≤ C/Y n := by
    apply hroot x (Y n) (yp n)
    change ((r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ)))^r=_
    rw [mul_pow,←Real.rpow_mul_natCast (by positivity),one_div_mul_cancel rr.ne',Real.rpow_one]
    change (r:ℤ)^r*(n.factorial:ℤ)=_ at h
    have h' := congrArg (fun z : ℤ => (z:ℝ)) h
    push_cast at h'
    calc _ = ∏ i∈T, ((x:ℝ)+(r:ℝ)*i-∑j∈T,(j:ℝ)) := h'
         _ = _ := by apply prod_congr rfl; intro i hi; dsimp [a]; ring
  obtain ⟨B,hB⟩ := eventually_atTop.mp ((factorial_scale_growth r rpos (2*C) η
    (by positivity) hη).and (factorial_scale_growth r rpos (C+3) 1 (by positivity) one_pos))
  filter_upwards [eventually_ge_atTop (max B 2)] with N hN
  intro n hin x hx
  obtain ⟨hl,hu⟩ := mem_Ico.mp hin
  obtain ⟨big,one⟩ := hB n (by omega)
  have np : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have yy : C+3 ≤ Y n := by simpa [Y] using one 0 (by simpa using Real.rpow_nonneg (Nat.cast_nonneg n) (1/34:ℝ))
  have hh := aprox hx
  have d1 : C/Y n ≤ 1 := (div_le_one (yp n)).mpr (by linarith)
  obtain ⟨dh,dl⟩ := abs_le.mp (hh.trans d1)
  have x1 : 0 < x := by
    by_contra! h
    have : x=0 := by omega
    rw [this,Nat.cast_zero] at dl
    linarith
  refine ⟨x1,by linarith,?_⟩
  rintro b hb hbn hbm hdiv ⟨z,hz⟩
  let m := n^(b/r)
  have he := scale_id hb hbn rpos hdiv
  change w b n*Y n=(m:ℝ)*Y (n-b) ∧ 1 ≤ w b n ∧ Y (n-b) ≤ Y n at he
  have h := shifted_approx (yp n) (yp (n-b)) hC he.2.1 he.2.2 he.1 hh (aprox hz)
  have msmall : (m:ℝ) ≤ (n:ℝ)^b := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega) (Nat.div_le_self b r) : m ≤ n^b)
  have hb' : (b:ℝ) ≤ (n:ℝ)^(1/34:ℝ) := by
    calc _ ≤ (⌊(N:ℝ)^(1/34:ℝ)⌋₊:ℝ) := by exact_mod_cast hbm
         _ ≤ (N:ℝ)^(1/34:ℝ) := Nat.floor_le (by positivity)
         _ ≤ _ := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hl) (by norm_num)
  have hh' : 2*C*(m:ℝ)^2 ≤ (Y n)^η := by
    refine le_trans ?_ (big b hb')
    gcongr
  refine ⟨(m:ℤ)*z,?_⟩
  push_cast
  refine h.trans ((div_le_div_of_nonneg_right hh' (yp n).le).trans_eq ?_)
  rw [Real.rpow_sub (yp n),Real.rpow_one]
  field_simp
