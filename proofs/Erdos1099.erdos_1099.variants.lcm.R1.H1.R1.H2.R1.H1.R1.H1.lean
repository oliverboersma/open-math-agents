import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1_H1_R1

/-! A dense finite interval contains additive cubes at a prescribed scale. Repeated pigeonholing supplies large shifts with many surviving pairs. -/
open Finset Filter Real
open scoped Classical
namespace DenseLogCube

private lemma heavy {α β:Type*} [DecidableEq β] (S:Finset α) (T:Finset β) (f:α→β)
    (ht:T.Nonempty) (maps:∀ x∈S,f x∈T) :
    ∃ b∈T,S.card≤(S.filter (fun x => f x=b)).card*T.card := by
  classical
  obtain ⟨b,hb,hm⟩ := T.exists_max_image (fun b => (S.filter (fun x => f x=b)).card) ht
  exact ⟨b,hb,card_le_mul_card_image_of_maps_to maps _ hm⟩

private def gap (v:ℕ×ℕ) := max v.1 v.2-min v.1 v.2

private lemma gap_fiber (C:Finset ℕ) (W:Finset (ℕ×ℕ)) (sub:W⊆C×ˢC) (b:ℕ) :
    (W.filter (fun v => gap v=b)).card ≤ 2*(C.filter (fun x => x+b∈C)).card := by
  classical
  let U := C.filter (fun x => x+b∈C)
  let f (v:ℕ×ℕ) : Bool×ℕ := (decide (v.1≤ v.2),min v.1 v.2)
  have h : (W.filter (fun v => gap v=b)).card≤((univ:Finset Bool)×ˢU).card := by
    apply card_le_card_of_injOn f
    · rintro ⟨i,j⟩ h
      obtain ⟨w,e⟩ := mem_filter.mp h
      obtain ⟨ic,jc⟩ := mem_product.mp (sub w)
      apply mem_product.mpr
      refine ⟨mem_univ _,mem_filter.mpr ?_⟩
      dsimp [f,gap] at *
      by_cases hy:i≤ j
      · rw [min_eq_left hy,max_eq_right hy] at *
        exact ⟨ic,by rwa [show i+b=j by omega]⟩
      · have hy' : j≤ i := by omega
        rw [min_eq_right hy',max_eq_left hy'] at *
        exact ⟨jc,by rwa [show j+b=i by omega]⟩
    · rintro ⟨i,j⟩ hi ⟨m,n⟩ hm eq
      have ei := (mem_filter.mp hi).2
      have em := (mem_filter.mp hm).2
      have tag := congrArg Prod.fst eq
      have bot := congrArg Prod.snd eq
      dsimp [f,gap] at tag bot ei em
      have ht : (i≤ j) ↔ (m≤ n) := by simpa using tag
      apply Prod.ext <;> dsimp <;> omega
  simpa [U] using h

private lemma shift (C:Finset ℕ) (L H:ℕ) (sub:C⊆Icc L (L+H)) (big:16≤ C.card) (hp:0< H) :
    ∃ b:ℕ, C.card≤8*b ∧ b≤ H ∧
      C.card^2 ≤ 8*H*(C.filter (fun x => x+b∈C)).card := by
  classical
  let W := C×ˢC
  let m := C.card
  let T := m/8
  let N := W.filter (fun v => gap v≤ T)
  let F := W \ N
  have wn : N⊆W := filter_subset ..
  have near : N.card≤2*m*(T+1) := by
    have hm : ∀ v∈N,gap v∈range (T+1) := fun v hv => mem_range.mpr (by have h := (mem_filter.mp hv).2; omega)
    have hc := card_le_mul_card_image_of_maps_to hm (2*m) (fun b _ =>
      (gap_fiber C N wn b).trans (Nat.mul_le_mul_left 2 (card_filter_le ..)))
    simpa using hc
  have tot : F.card+N.card=m^2 := by
    simpa [F,W,m,pow_two] using card_sdiff_add_card_eq_card wn
  have mt : 2*(T+1)≤ m/2 := by dsimp [T,m]; omega
  have fbig : m^2≤2*F.card := by
    have e := Nat.mul_le_mul_left m mt
    have e' := Nat.mul_le_mul_left m (show 2*(m/2)≤ m by omega)
    nlinarith only [tot,e,e',near]
  let B := Icc (T+1) H
  have mapg (v:ℕ×ℕ) (hv:v∈F) : gap v∈B := by
    obtain ⟨hw,hn⟩ := mem_sdiff.mp hv
    obtain ⟨h1,h2⟩ := mem_product.mp hw
    obtain ⟨l1,u1⟩ := mem_Icc.mp (sub h1)
    obtain ⟨l2,u2⟩ := mem_Icc.mp (sub h2)
    have far : T< gap v := lt_of_not_ge (fun e => hn (mem_filter.mpr ⟨hw,e⟩))
    exact mem_Icc.mpr ⟨far,by dsimp [gap]; omega⟩
  have fe : F.Nonempty := card_pos.mp (by dsimp [m] at fbig; nlinarith only [fbig,big])
  obtain ⟨v,hv⟩ := fe
  obtain ⟨b,hb,cap⟩ := heavy F B gap ⟨gap v,mapg v hv⟩ mapg
  obtain ⟨lb,ub⟩ := mem_Icc.mp hb
  have sz : B.card≤2*H := by simp [B,Nat.card_Icc]; omega
  have bound := Nat.mul_le_mul (gap_fiber C F sdiff_subset b) sz
  refine ⟨b,by dsimp [T,m] at lb; omega,ub,?_⟩
  change m^2≤_
  nlinarith only [cap,bound,fbig]

private lemma cubes (d:ℕ) : ∃ e:ℕ, 2≤ e ∧ ∀ (P H L:ℕ) (C:Finset ℕ),
    16≤ P → P^e≤ H → C⊆Icc L (L+H) → H≤ P*C.card →
    ∃ (x:ℕ) (h:List ℕ), h.length=d ∧
      (∀ a∈h,H≤ P^e*a ∧ a≤ H) ∧ ∀ t:List ℕ,t.Sublist h → x+t.sum∈C := by
  classical
  induction d with
  | zero =>
    refine ⟨2,le_rfl,?_⟩
    intro P H L C p16 pl sub dens
    have ch : 0< C.card := by
      by_contra! hc
      have cz : C.card=0 := by omega
      rw [cz,mul_zero] at dens
      nlinarith only [pl,dens,p16]
    obtain ⟨x,hx⟩ := card_pos.mp ch
    refine ⟨x,[],rfl,by simp,?_⟩
    intro t ht
    have eq := List.sublist_nil.mp ht
    simpa [eq] using hx
  | succ d ih =>
    obtain ⟨e,et,ih⟩ := ih
    refine ⟨3*e+3,by omega,?_⟩
    intro P H L C p16 pl sub dens
    have pp : 0< P := by omega
    have p1 : 1≤ P := by omega
    have p2 : P^2≤ P^(3*e+3) := Nat.pow_le_pow_right p1 (by omega)
    have Hpos : 0< H := (pow_pos pp _).trans_le (p2.trans pl)
    have cb : P≤ C.card := by
      apply Nat.le_of_mul_le_mul_left (c:=P) _ pp
      simpa [pow_two] using p2.trans (pl.trans dens)
    obtain ⟨b,be,bH,energy⟩ := shift C L H sub (p16.trans cb) Hpos
    let U := C.filter (fun x => x+b∈C)
    have Usub : U⊆C := filter_subset ..
    have cap : H≤(P^3)*U.card := by
      have a := Nat.mul_le_mul dens dens
      have bnd := Nat.mul_le_mul_left (P^2) energy
      have b8 : 8*P^2≤ P^3 := by
        calc 8*P^2 ≤ P*P^2 := Nat.mul_le_mul_right _ (by omega)
             _ = _ := by ring
      have scaled := Nat.mul_le_mul_right (H*U.card) b8
      apply Nat.le_of_mul_le_mul_left (c:=H) _ Hpos
      change C.card^2≤8*H*U.card at energy
      nlinarith only [a,bnd,scaled]
    have hpow : (P^3)^e≤ H := by
      rw [←pow_mul]
      exact (Nat.pow_le_pow_right p1 (by omega)).trans pl
    obtain ⟨x,t,nt,steps,vertices⟩ := ih (P^3) H L U (by nlinarith only [p16,show P≤ P^3 from by simpa using (Nat.pow_le_pow_right p1 (show 1≤3 by decide))]) hpow (Usub.trans sub) cap
    refine ⟨x,b::t,by simp [nt],?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with eq | ht
      · subst a
        have eb := Nat.mul_le_mul_left P be
        have p8 : P*8≤ P^(3*e+3) := by
          calc P*8 ≤ P*P := Nat.mul_le_mul_left P (by omega)
               _ = P^2 := by ring
               _ ≤ _ := p2
        exact ⟨by nlinarith only [dens,eb,Nat.mul_le_mul_right b p8],bH⟩
      · obtain ⟨lo,hi⟩ := steps a ht
        exact ⟨lo.trans (Nat.mul_le_mul_right a (by rw [←pow_mul]; apply Nat.pow_le_pow_right p1; omega)),hi⟩
    · intro w hw
      cases hw with
      | cons z ht => exact Usub (vertices _ ht)
      | cons_cons z ht =>
        have e := (mem_filter.mp (vertices _ ht)).2
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using e

private lemma local_chunk {k H:ℕ} (hp:0< H) (hk:H≤ k) (R:ℝ) (rp:0< R)
    (P:ℕ) (pR:200*R≤ P) (B:Finset ℕ) (sub:B⊆Ioc (k/16) k) (dens:(k:ℝ)/(100*R)≤ B.card) :
    ∃ (L:ℕ) (C:Finset ℕ), C⊆B ∧ C⊆Icc L (L+H) ∧ H≤ P*C.card := by
  classical
  let bins := range (k/H+1)
  let f (x:ℕ) := x/H
  have maps (x:ℕ) (hx:x∈B) : f x∈bins := by
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ((mem_Ioc.mp (sub hx)).2)))
  obtain ⟨b,hb,hmax⟩ := heavy B bins f (by simp [bins]) maps
  let C := B.filter (fun x => f x=b)
  refine ⟨b*H,C,filter_subset ..,?_,?_⟩
  · intro x hc
    have e := (mem_filter.mp hc).2
    change x/H=b at e
    have a := Nat.div_mul_le_self x H
    have z := Nat.lt_mul_div_succ x hp
    rw [e] at a z
    exact mem_Icc.mpr ⟨a,by nlinarith only [z]⟩
  · have bnd : bins.card*H≤2*k := by
      simp only [bins,card_range,add_mul,one_mul]
      linarith [Nat.div_mul_le_self k H]
    change B.card≤ C.card*bins.card at hmax
    have a := Nat.mul_le_mul_right H hmax
    have b := Nat.mul_le_mul_left C.card bnd
    have e : B.card*H≤2*k*C.card := by nlinarith only [a,b]
    have er : (B.card:ℝ)*H≤2*(k:ℝ)*C.card := by exact_mod_cast e
    have dd := (div_le_iff₀ (by positivity)).mp dens
    have ee := mul_le_mul_of_nonneg_right dd (Nat.cast_nonneg H (α:=ℝ))
    have ef := mul_le_mul_of_nonneg_left er (show 0≤100*R by positivity)
    have kp : 0<(k:ℝ) := by exact_mod_cast hp.trans_le hk
    have cs := mul_le_mul_of_nonneg_right pR (Nat.cast_nonneg C.card (α:=ℝ))
    have goal : (H:ℝ)≤(P:ℝ)*C.card := by
      apply le_trans _ cs
      apply le_of_mul_le_mul_left (a:=(k:ℝ)) _ kp
      nlinarith only [ee,ef]
    exact_mod_cast goal

private lemma choose_scale (k J d:ℕ) (w C:ℝ) (wd:0≤ w) (cd:1≤ C) (hd:0< d)
    (jx:J≤ k) (feas:(1+w)*(C*J)^d≤(k:ℝ)^d) :
    ∃ H:ℕ, J≤ H ∧ H≤ k ∧ (1+w)*(C*H)^d≤(k:ℝ)^d ∧
      (k:ℝ)^d<(1+w)*(C*((H:ℝ)+1))^d := by
  classical
  let S := (range (k+1)).filter (fun h:ℕ => (1+w)*(C*h)^d≤(k:ℝ)^d)
  have jm : J∈S := mem_filter.mpr ⟨mem_range.mpr (by omega),feas⟩
  have ne : S.Nonempty := ⟨J,jm⟩
  let H := S.max' ne
  have hm := S.max'_mem ne
  have memH := mem_filter.mp hm
  have hk : H≤ k := Nat.le_of_lt_succ (mem_range.mp memH.1)
  refine ⟨H,S.le_max' _ jm,hk,memH.2,?_⟩
  by_cases he:H=k
  · rw [he]
    have lt : (k:ℝ)< C*((k:ℝ)+1) := by
      have b := mul_le_mul_of_nonneg_right cd (by positivity : 0≤(k:ℝ)+1)
      linarith
    have powlt := pow_lt_pow_left₀ lt (Nat.cast_nonneg _ (α:=ℝ)) hd.ne'
    have b := mul_le_mul_of_nonneg_right (show 1≤1+w by linarith) (show 0≤(C*((k:ℝ)+1))^d by positivity)
    linarith
  · by_contra! bad
    have nxt : H+1∈S := mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa using bad⟩
    have h : H+1≤ H := S.le_max' _ nxt
    omega

private lemma prod_bounds (h:List ℕ) (H Q:ℕ) (steps:∀ a∈h,H≤ Q*a ∧ a≤ H) :
    H^h.length ≤ Q^h.length*h.prod ∧ h.prod≤ H^h.length := by
  induction h with
  | nil => simp
  | cons a t ih =>
    obtain ⟨lo,hi⟩ := ih (fun b hb => steps b (by simp [hb]))
    obtain ⟨la,ua⟩ := steps a (by simp)
    simp only [List.length_cons,List.prod_cons,pow_succ]
    constructor
    · have e := Nat.mul_le_mul lo la
      nlinarith only [e]
    · exact (Nat.mul_le_mul ua hi).trans_eq (Nat.mul_comm ..)

private lemma logs_small (A:ℕ) (C:ℝ) : ∀ᶠ k:ℕ in atTop, C*(1+log (k:ℝ))^A ≤ (k:ℝ) := by
  let B := max C 1*2^A
  have bp : 0< B := mul_pos (lt_of_lt_of_le one_pos (le_max_right ..)) (by positivity)
  have tN : Tendsto (fun k:ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have raw := (isLittleO_log_rpow_rpow_atTop (A:ℝ) (show (0:ℝ)<1 by norm_num)).bound (inv_pos.mpr bp)
  filter_upwards [tL.eventually_ge_atTop 1,tN.eventually raw] with k lg h
  change 1≤ log (k:ℝ) at lg
  simp only [rpow_natCast,rpow_one,Real.norm_of_nonneg (pow_nonneg (by linarith : 0≤ log (k:ℝ)) _), Real.norm_of_nonneg (Nat.cast_nonneg k (α:=ℝ))] at h
  have hh := mul_le_mul_of_nonneg_left h bp.le
  have bb : B*B⁻¹=1 := mul_inv_cancel₀ bp.ne'
  have e : (1+log (k:ℝ))^A ≤ 2^A*(log (k:ℝ))^A := by rw [←mul_pow]; gcongr; linarith
  calc
    _ ≤ (max C 1)*(2^A*(log (k:ℝ))^A) := mul_le_mul (le_max_left ..) e (by positivity) (le_trans zero_le_one (le_max_right ..))
    _ = B*(log (k:ℝ))^A := by dsimp [B]; ring
    _ ≤ _ := by rw [←mul_assoc,bb,one_mul] at hh; exact hh

private lemma scales (M d e:ℕ) (hd:d=M+1) (_ee:2≤ e) (C:ℝ) (c1:1≤ C) :
    ∀ᶠ k:ℕ in atTop, ∀ s:ℝ, |s|≤(k:ℝ)^M →
    let R := 1+log (k:ℝ)
    let P := ⌈400*R⌉₊
    ∃ H:ℕ, P^e≤ H ∧ H≤ k ∧ (1+|s|)*(C*H)^d≤(k:ℝ)^d ∧
      (k:ℝ)^d<(1+|s|)*(2*C*H)^d := by
  let D := 2*C^d*401^(e*d)
  filter_upwards [logs_small (e*d) D,eventually_ge_atTop 1] with k small k1
  intro s su R P
  have r1 : 1≤ R := by dsimp [R]; linarith [log_natCast_nonneg k]
  have kr : (1:ℝ)≤ k := by exact_mod_cast k1
  have p1 : 1≤ P := by
    have a : 400*R≤(P:ℝ) := Nat.le_ceil _
    exact_mod_cast (show (1:ℝ)≤ P by linarith)
  have Pbound : (P:ℝ)≤401*R := by
    have a := Nat.ceil_lt_add_one (by linarith : 0≤400*R)
    change (P:ℝ)<400*R+1 at a
    linarith
  let J := P^e
  have j1 : 1≤ J := Nat.one_le_pow _ _ p1
  have jr : (1:ℝ)≤ J := by exact_mod_cast j1
  have up : 2*(C*(J:ℝ))^d≤(k:ℝ) := by
    apply le_trans _ small
    calc _ = (2*C^d)*(P:ℝ)^(e*d) := by dsimp [J]; rw [Nat.cast_pow,mul_pow,pow_mul];ring
         _ ≤ (2*C^d)*(401*R)^(e*d) := by gcongr
         _ = D*R^(e*d) := by dsimp [D]; rw [mul_pow];ring
  have d1 : 1≤ d := by omega
  have CJ : (J:ℝ)≤ C*J := by simpa using mul_le_mul_of_nonneg_right c1 (Nat.cast_nonneg J (α:=ℝ))
  have CJp : C*J≤(C*J)^d := by simpa using pow_le_pow_right₀ (jr.trans CJ) d1
  have jk : J≤ k := by exact_mod_cast (show (J:ℝ)≤ k by linarith)
  have kw := one_le_pow₀ kr (n:=M)
  have prep := mul_le_mul_of_nonneg_left up (show 0≤(k:ℝ)^M by positivity)
  have fact := mul_le_mul_of_nonneg_right (show 1+|s|≤2*(k:ℝ)^M by linarith) (show 0≤(C*J)^d by positivity)
  have feasible : (1+|s|)*(C*J)^d≤(k:ℝ)^d := by rw [show (k:ℝ)^d=(k:ℝ)^M*k by rw [hd,pow_succ]]; nlinarith only [prep,fact]
  obtain ⟨H,jh,hk,hlo,hhi⟩ := choose_scale k J d |s| C (abs_nonneg _) c1 (by omega) jk feasible
  have Hr : (1:ℝ)≤ H := by exact_mod_cast j1.trans jh
  refine ⟨H,jh,hk,hlo,hhi.trans_le ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_left Hr (show 0 ≤ C by linarith)]

end DenseLogCube

open DenseLogCube in
theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro M
  let d := M+1
  have dp : 0< d := by dsimp [d];omega
  obtain ⟨e,ep,cube⟩ := cubes d
  let F := ((d-1).factorial:ℝ)
  let C := 16*F
  have F1 : 1≤ F := by dsimp [F]; exact_mod_cast (Nat.factorial_pos (d-1) : 1 ≤ (d-1).factorial)
  have C1 : 1≤ C := by dsimp [C];linarith
  let A := e*d+3
  refine ⟨d,A,dp,?_⟩
  have tn : Tendsto (fun k:ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have lg := tendsto_log_atTop.comp tn
  let D := 2*(2*C)^d*401^(e*d)
  filter_upwards [scales M d e rfl ep C C1,lg.eventually_ge_atTop D,eventually_ge_atTop 16] with k sc kl k16
  intro s sl su B sub dens
  let R := 1+log (k:ℝ)
  have r1 : 1≤ R := by dsimp [R];linarith [log_natCast_nonneg k]
  have rp : 0< R := zero_lt_one.trans_le r1
  let P := ⌈400*R⌉₊
  have pR : 400*R≤(P:ℝ) := Nat.le_ceil _
  have p16 : 16≤ P := by exact_mod_cast (show (16:ℝ)≤ P by linarith)
  have pB : (P:ℝ)≤401*R := by
    have a := Nat.ceil_lt_add_one (by positivity : 0≤400*R)
    change (P:ℝ)<400*R+1 at a
    linarith
  obtain ⟨H,jh,hk,lower,upper⟩ := sc s su
  change P^e≤ H at jh
  have hp : 0< H := (pow_pos (show 0< P by omega) e).trans_le jh
  obtain ⟨L,U,ub,box,mass⟩ := local_chunk hp hk R rp P (by linarith) B sub dens
  obtain ⟨x,h,hlen,steps,verts⟩ := cube P H L U p16 jh box mass
  have vert (t:List ℕ) (ht:t.Sublist h) := ub (verts t ht)
  have left := (mem_Ioc.mp (sub (vert [] (List.nil_sublist h)))).1
  simp only [List.sum_nil,Nat.add_zero] at left
  have right := (mem_Ioc.mp (sub (vert h (.refl _)))).2
  have xpos : 0< x := by omega
  have xl : k<16*x := by omega
  have xR : 0<(x:ℝ) := by exact_mod_cast xpos
  have kR : 0<(k:ℝ) := by exact_mod_cast (show 0< k by omega)
  have kr : (k:ℝ)≤16*x := by exact_mod_cast xl.le
  have top : ((x+h.sum:ℕ):ℝ)≤ k := by exact_mod_cast right
  refine ⟨x,h,hlen,xpos,?_,vert,?_,?_⟩
  · intro a ha; obtain ⟨u,_⟩ := steps a ha; by_contra! bad
    have az : a=0 := by omega
    simp [az] at u
    omega
  · obtain ⟨lo,_⟩ := prod_bounds h H (P^e) steps
    rw [hlen] at lo
    have hpow : (H:ℝ)^d≤(P:ℝ)^(e*d)*h.prod := by rw [pow_mul];exact_mod_cast lo
    have PP := pow_le_pow_left₀ (Nat.cast_nonneg P (α:=ℝ)) pB (e*d)
    rw [mul_pow] at PP
    have lprod := hpow.trans (mul_le_mul_of_nonneg_right PP (Nat.cast_nonneg h.prod (α:=ℝ)))
    have lgD : D≤ R := by change D≤ log (k:ℝ) at kl;dsimp [R];linarith
    have s1 : 1≤|s| *R^2 := by
      change 1/R^2≤|s| at sl
      exact (div_le_iff₀ (by positivity)).mp sl
    have s2 : 1+|s|≤2*(|s| *R^2) := by
      have w := mul_le_mul_of_nonneg_left (one_le_pow₀ r1 (n:=2)) (abs_nonneg s)
      linarith
    have mul := mul_le_mul s2 lprod (by positivity) (by positivity)
    have joined := mul_le_mul_of_nonneg_right mul (show 0≤(2*C)^d by positivity)
    rw [mul_pow (2*C) (H:ℝ) d] at upper
    have gain : (k:ℝ)^d≤|s| *(h.prod:ℝ)*D*R^(e*d+2) := by
      dsimp only [D];rw [pow_add R (e*d) 2];nlinarith only [upper,joined]
    have end1 := mul_le_mul_of_nonneg_right lgD (show 0≤|s| *(h.prod:ℝ)*R^(e*d+2) by positivity)
    have fact := mul_le_mul_of_nonneg_right F1 (show 0≤|s| *(h.prod:ℝ)*R^A by positivity)
    have den : 0<((x+h.sum:ℕ):ℝ)^d := by positivity
    change 1/R^A≤|s| *F*(h.prod:ℝ)/_
    apply (div_le_div_iff₀ (by positivity) den).mpr
    have tpow := pow_le_pow_left₀ (Nat.cast_nonneg (x+h.sum) (α:=ℝ)) top d
    rw [show R^A=R^(e*d+2)*R from pow_succ R (e*d+2)] at fact ⊢
    nlinarith only [gain,end1,fact,tpow]
  · obtain ⟨_,hi⟩ := prod_bounds h H (P^e) steps
    rw [hlen] at hi
    have hpow : (h.prod:ℝ)≤(H:ℝ)^d := by exact_mod_cast hi
    have fD : F≤ F^d := by simpa using pow_le_pow_right₀ F1 dp
    have left := mul_le_mul (show |s|≤1+|s| by linarith) hpow (by positivity) (by positivity)
    have l2 := mul_le_mul left fD (by positivity) (by positivity)
    have l3 := mul_le_mul_of_nonneg_right l2 (show 0≤(16:ℝ)^d by positivity)
    have r3 := pow_le_pow_left₀ kR.le kr d
    simp only [C,mul_pow] at lower r3
    change |s| *F*(h.prod:ℝ)/(x:ℝ)^d≤1
    apply (div_le_iff₀ (by positivity)).mpr
    apply le_of_mul_le_mul_right (a:=(16:ℝ)^d) _ (by positivity)
    nlinarith only [l3,lower,r3]



