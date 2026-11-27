import OMAReductions.R_Erdos375_erdos_375_variants_log_R1_H1_R1

/-! Ramachandra, Shorey and Tijdeman's large-obstruction extraction.
The factorial product bound leaves many rows with a small cofactor.
Two rows have the same prime exponent and the logarithms of their
cofactors occupy the same short interval. Subtracting their logarithmic
factorizations gives the required nonzero linear form. -/
open Finset Real Filter
open scoped Topology

private lemma height_div {a b:ℕ} (ha:0<a) (hb:0<b) :
    (((a:ℚ)/b).num.natAbs+((a:ℚ)/b).den) ≤ a+b := by
  have bd : ((b:ℤ))≠0 := by exact_mod_cast hb.ne'
  have n := Rat.num_dvd (a:ℤ) bd
  have d := Rat.den_dvd (a:ℤ) (b:ℤ)
  rw [Rat.divInt_eq_div] at n d
  push_cast at n d
  have hn := Int.natAbs_dvd_natAbs.mpr n
  have hd := Int.natAbs_dvd_natAbs.mpr d
  simp only [Int.natAbs_natCast] at hn hd
  exact Nat.add_le_add (Nat.le_of_dvd ha hn) (Nat.le_of_dvd hb hd)

private lemma log_near {x y N K:ℝ} (np:0<N) (kx:0≤K) (hx:N≤x) (hy:N≤y)
    (xa:x≤N+K) (ya:y≤N+K) : |log x-log y| ≤ K/N := by
  have xp := np.trans_le hx
  have yp := np.trans_le hy
  have one (v w:ℝ) (vp:0<v) (wp:0<w) (h:N≤w) (up:v≤N+K) : log v-log w≤K/N := by
    rw [←log_div vp.ne' wp.ne']
    have b := log_le_sub_one_of_pos (div_pos vp wp)
    have h' : v/w ≤ (N+K)/N :=
      div_le_div₀ (by linarith) up np h
    have e : (N+K)/N = 1+K/N := by field_simp
    linarith only [b,h',e]
  exact abs_sub_le_iff.mpr ⟨one x y xp yp hy xa,one y x yp xp hx ya⟩

private lemma logpower (a R:ℝ) (ha:0<a) (hR:0<R) :
    ∀ᶠ x:ℝ in atTop, (log x)^8 ≤ a*x^R := by
  have h := (isLittleO_log_rpow_rpow_atTop 8 hR).bound ha
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with x hx h1
  simpa only [Real.rpow_natCast,Real.rpow_ofNat, Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (log_nonneg h1) _),
    abs_of_nonneg (rpow_nonneg (zero_le_one.trans h1) _)] using hx

private lemma find_pair {α:Type} [DecidableEq α] (B:Finset α) (u e:α→ℕ) (E:ℕ) (L l T δ:ℝ)
    (hL:1≤L) (hl:1≤l) (hT:0<T) (tL:T≤L) (dl:0<δ)
    (width:l^4≤L) (large:100 < δ*l^2) (cap:(E:ℝ)+1 ≤ 6*L)
    (size:δ*(L/l)^2 ≤ B.card)
    (sum:∑ i∈B, log (u i:ℝ) ≤ (δ*(L/l)^2)*T/4)
    (exp:∀ i∈B, e i≤E) :
    ∃ i∈B, ∃ j∈B, i≠j ∧ e i=e j ∧ log (u i:ℝ)≤T ∧ log (u j:ℝ)≤T ∧
      |log (u i:ℝ)-log (u j:ℝ)|≤l^4 := by
  classical
  let G := B.filter (fun i => log (u i:ℝ)≤T)
  let Z := B \ G
  have cost : (Z.card:ℝ)*T≤∑ i∈B, log (u i:ℝ) := by
    calc _ = ∑ _i∈Z,T := by simp
         _ ≤ ∑ i∈Z,log (u i:ℝ) := by
           apply sum_le_sum
           intro i hi
           obtain ⟨bi,ng⟩ := mem_sdiff.mp hi
           exact le_of_lt (lt_of_not_ge (fun h => ng (mem_filter.mpr ⟨bi,h⟩)))
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i _ _ => log_natCast_nonneg _)
  have zb : (Z.card:ℝ)≤δ*(L/l)^2/4 := by apply le_of_mul_le_mul_right _ hT; linarith only [cost,sum]
  have ecard : (Z.card:ℝ)+(G.card:ℝ)=B.card := by exact_mod_cast (card_sdiff_add_card_eq_card (show G⊆B from filter_subset ..) : Z.card+G.card=B.card)
  let bins := range (E+1) ×ˢ range (⌊L/l^4⌋₊+1)
  let key (i:α) := (e i,⌊log (u i:ℝ)/l^4⌋₊)
  have lp : 0<l := by linarith
  have wP : 0<l^4 := pow_pos lp _
  have maps (i:α) (hi:i∈G) : key i∈bins := by
    obtain ⟨bi,lt⟩ := mem_filter.mp hi
    exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (exp i bi)),
      mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (lt.trans tL) wP.le)))⟩
  have less : bins.card<G.card := by
    have fl := Nat.floor_le (show 0≤L/l^4 by positivity)
    have denom : 1 ≤ L/l^4 := (le_div_iff₀ wP).mpr (by simpa using width)
    have binsB : (bins.card:ℝ) ≤ 12*L^2/l^4 := by
      dsimp [bins]
      simp only [card_product,card_range,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      have h := mul_le_mul cap (show (⌊L/l^4⌋₊:ℝ)+1 ≤ 2*(L/l^4) by linarith) (by positivity) (by positivity)
      exact h.trans_eq (by ring)
    have ratio : 12*L^2/l^4 < δ*(L/l)^2/2 := by
      rw [show δ*(L/l)^2/2=(δ*l^2/2)*(L^2/l^4) by field_simp,mul_div_assoc]
      exact mul_lt_mul_of_pos_right (by linarith) (div_pos (by positivity) wP)
    have pos : 0≤δ*(L/l)^2 := mul_nonneg dl.le (sq_nonneg _)
    have right : δ*(L/l)^2/2 ≤ (G.card:ℝ) := by linarith only [size,ecard,zb,pos]
    exact_mod_cast (binsB.trans_lt ratio).trans_le right
  obtain ⟨i,hi,j,hj,ne,kij⟩ := exists_ne_map_eq_of_card_lt_of_maps_to less maps
  have ei : e i=e j := congrArg Prod.fst kij
  have eq : ⌊log (u i:ℝ)/l^4⌋₊=⌊log (u j:ℝ)/l^4⌋₊ := congrArg Prod.snd kij
  have li := Nat.floor_le (div_nonneg (log_natCast_nonneg (u i)) wP.le)
  have lj := Nat.floor_le (div_nonneg (log_natCast_nonneg (u j)) wP.le)
  have ui := Nat.lt_floor_add_one (log (u i:ℝ)/l^4)
  have uj := Nat.lt_floor_add_one (log (u j:ℝ)/l^4)
  rw [eq] at li ui
  have diff : |log (u i:ℝ)/l^4-log (u j:ℝ)/l^4|≤1 := abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
  rw [←sub_div,abs_div,abs_of_pos wP, div_le_iff₀ wP, one_mul] at diff
  exact ⟨i,(mem_filter.mp hi).1,j,(mem_filter.mp hj).1,ne,ei,(mem_filter.mp hi).2,(mem_filter.mp hj).2,diff⟩

private lemma forms {n k X Y a b p q e:ℕ} {S:ℝ} (nels:X≠Y)
    (xp:0<X) (yp:0<Y) (pa:0<a) (pb:0<b) (pp:0<p) (pq:0<q)
    (splX:X=a*p^e) (splY:Y=b*q^e) (np:0<n)
    (nx:n≤X) (ny:n≤Y) (xk:X≤n+k) (yk:Y≤n+k)
    (small:(k:ℝ)/n<(n:ℝ)^(-(1/2:ℝ))) (sp:0<S)
    (prime:(p:ℝ)+(q:ℝ)≤(log S)^16)
    (lo:2*log S/log (log S)≤(e:ℝ)) (hi:(e:ℝ)≤(log S)^16)
    (la:log (a:ℝ)≤log S-log 2) (lb:log (b:ℝ)≤log S-log 2)
    (delta:|log (a:ℝ)-log (b:ℝ)|≤(log S)^(3/4:ℝ)) :
    ∃ (u v:ℚ) (m:ℤ), 0<u ∧ 0<v ∧ ((u.num.natAbs+u.den:ℕ):ℝ)≤(log S)^16 ∧
    ((v.num.natAbs+v.den:ℕ):ℝ)≤S ∧ 2*log S/log (log S)≤|(m:ℝ)| ∧ |(m:ℝ)|≤(log S)^16 ∧
    |log (v:ℝ)|≤(log S)^(3/4:ℝ) ∧ 0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧
    |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ)) := by
  let u : ℚ := (p:ℚ)/q
  let v : ℚ := (b:ℚ)/a
  have h₁ := Nat.cast_le (α:=ℝ).mpr (height_div pp pq)
  have h₂ := Nat.cast_le (α:=ℝ).mpr (height_div pb pa)
  push_cast at h₁ h₂
  have ca : (a:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pa) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have cb : (b:ℝ)≤S/2 := (log_le_log_iff (by exact_mod_cast pb) (by positivity)).mp (by rwa [log_div sp.ne' (by norm_num)])
  have lu : log (u:ℝ)=log (p:ℝ)-log (q:ℝ) := by simp [u,log_div,pp.ne',pq.ne']
  have lv : log (v:ℝ)=log (b:ℝ)-log (a:ℝ) := by simp [v,log_div,pa.ne',pb.ne']
  have xl (z c d:ℕ) (hc:0<c) (hd:0<d) (eq:z=c*d^e) :
      log (z:ℝ)=log (c:ℝ)+(e:ℝ)*log (d:ℝ) := by rw [eq,Nat.cast_mul,Nat.cast_pow,log_mul (by positivity) (by positivity),log_pow]
  have hX := xl _ _ _ pa pp splX
  have hY := xl _ _ _ pb pq splY
  have eq : (e:ℝ)*log (u:ℝ)-log (v:ℝ)=log (X:ℝ)-log (Y:ℝ) := by rw [lu,lv,hX,hY]; ring
  have logne : log (X:ℝ)≠log (Y:ℝ) := fun h => nels (by exact_mod_cast (Real.log_injOn_pos (show (0:ℝ)<X by exact_mod_cast xp) (show (0:ℝ)<Y by exact_mod_cast yp) h))
  have close := log_near (x:=(X:ℝ)) (y:=(Y:ℝ)) (by exact_mod_cast np : (0:ℝ)<n) (Nat.cast_nonneg k) (by exact_mod_cast nx) (by exact_mod_cast ny)
    (by exact_mod_cast xk) (by exact_mod_cast yk)
  refine ⟨u,v,e,by dsimp [u]; positivity,by dsimp [v]; positivity,?_,?_,?_,?_,?_,?_,?_⟩
  · push_cast
    exact h₁.trans prime
  · push_cast
    exact h₂.trans (by linarith)
  · simpa using lo
  · simpa using hi
  · rwa [lv,abs_sub_comm]
  · rw [Int.cast_natCast,eq]; exact abs_pos.mpr (sub_ne_zero.mpr logne)
  · rw [Int.cast_natCast,eq]; exact close.trans_lt small

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1.H3 := by
  classical
  intro b hb S₀ δ hδ
  let d := min b (1/100:ℝ)
  have dp : 0<d := lt_min hb (by norm_num)
  have db : d≤b := min_le_left .. 
  have dc : d≤1/100 := min_le_right ..
  let c := min 1 (δ*d/100)
  have cp : 0<c := lt_min one_pos (by positivity)
  have c1 : c≤1 := min_le_left ..
  have cd : c≤δ*d/100 := min_le_right ..
  refine ⟨c,cp,?_⟩
  have tN : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tL := tendsto_log_atTop.comp tN
  have tl := tendsto_log_atTop.comp tL
  have tD := (tendsto_const_mul_atTop_of_pos dp).mpr tL
  have tS := tendsto_exp_atTop.comp tD
  have tl2 := (tendsto_pow_atTop (by decide : 2≠0)).comp tl
  filter_upwards [eventually_ge_atTop 2,tL.eventually_ge_atTop 8,tl.eventually_ge_atTop 1,
    tl.eventually_ge_atTop (-2*log d),tL.eventually_ge_atTop (2/d^2),
    tD.eventually_ge_atTop 8,tS.eventually_ge_atTop S₀,tl2.eventually_gt_atTop (100/δ),
    tL.eventually (logpower d 1 dp one_pos),tN.eventually (logpower 1 (1/2) one_pos (by norm_num))]
    with n hn hL hl hdlog hdL hD hS hδl hpow hNpow
  let L := log (n:ℝ)
  let l := log L
  let S := exp (d*L)
  let T := d*L/4
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change 8≤L at hL
  change 1≤l at hl
  change -2*log d ≤ l at hdlog
  change 2/d^2≤L at hdL
  change 8≤d*L at hD
  change S₀≤S at hS
  change 100/δ<l^2 at hδl
  change l^8 ≤ d*L^(1:ℝ) at hpow
  rw [rpow_one] at hpow
  change L^8≤1*(n:ℝ)^(1/2:ℝ) at hNpow
  rw [one_mul,←sqrt_eq_rpow] at hNpow
  have Lp : 0<L := by linarith
  have lp : 0<l := by linarith
  have sp : 0<S := exp_pos _
  have ls : log S=d*L := log_exp _
  have llS : l/2≤log (log S) := by rw [ls,log_mul dp.ne' Lp.ne']; change _≤log d+l; linarith
  have Spow : S≤(n:ℝ)^b := by rw [rpow_def_of_pos np]; apply exp_le_exp.mpr; dsimp [L]; nlinarith only [mul_le_mul_of_nonneg_right db Lp.le]
  have sp2 : L≤(d*L)^2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos dp)).mp hdL
    nlinarith only [mul_le_mul_of_nonneg_left h Lp.le,Lp.le]
  have cap16 : 4*L^3 ≤ (d*L)^16 := calc
    _ ≤ L^4 := by nlinarith only [mul_nonneg (show 0≤L-4 by linarith) (pow_nonneg Lp.le 3)]
    _ ≤ ((d*L)^2)^4 := pow_le_pow_left₀ Lp.le sp2 _
    _ = (d*L)^8 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  have width : l^4 ≤ (log S)^(3/4:ℝ) := by
    rw [ls]
    calc l^4 ≤ l^6 := pow_le_pow_right₀ hl (by decide)
         _ = (l^8)^(3/4:ℝ) := by rw [←rpow_natCast_mul lp.le]; norm_num
         _ ≤ _ := rpow_le_rpow (by positivity) hpow (by norm_num)
  have wL : l^4≤L := by
    have h := pow_le_pow_right₀ hl (by decide : 4≤8)
    nlinarith only [h,hpow,mul_le_mul_of_nonneg_right dc Lp.le]
  intro k hk B p e u size fac _inj row
  let Q := L/l
  change (k:ℝ)<c*Q^3 at hk
  change δ*Q^2 ≤ (B.card:ℝ) at size
  have qp : 0<Q := div_pos Lp lp
  have qL : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hl)])
  have kl : (k:ℝ)≤L^3 := calc
    _ ≤ c*Q^3 := hk.le
    _ ≤ 1*L^3 := mul_le_mul c1 (pow_le_pow_left₀ qp.le qL _) (by positivity) (by norm_num)
    _ = _ := one_mul _
  have root : (k:ℝ)<sqrt n := by
    have h : L^3<L^8 := pow_lt_pow_right₀ (by linarith) (by decide)
    exact kl.trans_lt (h.trans_le hNpow)
  have kn : k≤n := by
    have h := Real.sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)))
    exact_mod_cast root.le.trans h
  have ks : (k:ℝ)/n < (n:ℝ)^(-(1/2:ℝ)) := by
    rw [←show sqrt (n:ℝ)/n=(n:ℝ)^(-(1/2:ℝ)) by rw [sqrt_eq_rpow,show (n:ℝ)^(-(1/2:ℝ))=(n:ℝ)^((1/2:ℝ)-1) by norm_num,rpow_sub np,rpow_one]]
    exact div_lt_div_of_pos_right root np
  have bp : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hδ (sq_pos_of_pos qp)).trans_le size)
  obtain ⟨ib,hib⟩ := bp
  have kp : 0<k := (row ib hib).1.pos.trans (row ib hib).2.1
  have logk : log (k:ℝ)≤3*l := by
    have h := log_le_log (by exact_mod_cast kp) kl
    rwa [log_pow] at h
  have prod : ∑ i∈B,log (u i:ℝ) ≤ (k:ℝ)*log k := by
    have h : (∏ i∈B,(u i:ℝ))≤(k:ℝ)^k := by exact_mod_cast fac.trans k.factorial_le_pow
    have pos : 0<∏ i∈B,(u i:ℝ) := prod_pos fun i hi => by exact_mod_cast (row i hi).2.2.1
    have hlog := log_le_log pos h
    rwa [log_prod (fun i hi => by exact_mod_cast (row i hi).2.2.1.ne'),log_pow] at hlog
  have cost : ∑ i∈B,log (u i:ℝ) ≤ δ*Q^2*T/4 := by
    apply prod.trans
    calc _ ≤ (c*Q^3)*(3*l) := mul_le_mul hk.le logk (log_natCast_nonneg _) (by positivity)
         _ = 3*c*Q^2*L := by dsimp [Q]; field_simp <;> ring
         _ ≤ _ := by dsimp [T]; nlinarith only [mul_le_mul_of_nonneg_right cd (mul_nonneg (sq_nonneg Q) Lp.le),mul_nonneg (mul_nonneg hδ.le dp.le) (mul_nonneg (sq_nonneg Q) Lp.le)]
  let X (i:Fin k) := n+i.val+1
  have bounds (i:Fin k) : n≤X i ∧ X i≤n+k := by dsimp [X]; have := i.isLt; omega
  have xl (i:Fin k) (bi:i∈B) : log (X i:ℝ)=log (u i:ℝ)+(e i:ℝ)*log (p i:ℝ) := by
    have hi := row i bi
    dsimp only [X]
    rw [hi.2.2.2,Nat.cast_mul,Nat.cast_pow,log_mul (by exact_mod_cast hi.2.2.1.ne') (by positivity [hi.1.pos]),log_pow]
  have Llo (i:Fin k) : L≤log (X i:ℝ) := log_le_log np (by exact_mod_cast (bounds i).1)
  have Lup (i:Fin k) : log (X i:ℝ)≤2*L := by
    have h : (X i:ℝ)≤(n:ℝ)^2 := by exact_mod_cast ((bounds i).2.trans (by nlinarith : n+k≤n^2))
    have h' := log_le_log (by dsimp [X]; positivity) h
    rwa [log_pow] at h'
  have expbd (i:Fin k) (bi:i∈B) : (e i:ℝ)≤4*L := by
    have pp := (row i bi).1
    have lg := log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast pp.two_le : (2:ℝ)≤p i)
    have h := mul_le_mul_of_nonneg_left (show 1/2≤log (p i:ℝ) by linarith [log_two_gt_d9]) (Nat.cast_nonneg (e i))
    linarith only [h,xl i bi, Lup i,log_natCast_nonneg (u i)]
  let E := ⌊4*L⌋₊
  have eNat (i:Fin k) (bi:i∈B) : e i≤E := (Nat.le_floor_iff (by positivity)).mpr (expbd i bi)
  have ecap : (E:ℝ)+1≤6*L := by have h := Nat.floor_le (show 0≤4*L by positivity); change (E:ℝ)≤4*L at h; linarith
  have tlb : 0<T := by dsimp [T]; positivity
  have thresholdL : T≤L := by dsimp [T]; nlinarith only [mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  obtain ⟨i,bi,j,bj,ij,ee,ai,aj,close⟩ := find_pair B u e E L l T δ (by linarith) hl tlb thresholdL hδ wL
    (by have h := (div_lt_iff₀ hδ).mp hδl; linarith) ecap size cost eNat
  have emin : 2*log S/log (log S)≤(e i:ℝ) := by
    have plog := (log_le_log (show (0:ℝ)<p i by exact_mod_cast (row i bi).1.pos) (by exact_mod_cast (row i bi).2.1.le)).trans logk
    have h := mul_le_mul_of_nonneg_left plog (Nat.cast_nonneg (e i) (α:=ℝ))
    have main : L ≤ T+(e i:ℝ)*(3*l) := by linarith only [xl i bi,Llo i,ai,h]
    apply (div_le_iff₀ (by linarith : 0<log (log S))).mpr
    rw [ls]
    have mult := mul_le_mul_of_nonneg_left llS (Nat.cast_nonneg (e i) (α:=ℝ))
    dsimp [T] at main
    rw [ls] at mult
    linarith only [main,mult,mul_le_mul_of_nonneg_right dc Lp.le,Lp.le]
  have same : X j=u j*(p j)^(e i) := by rw [ee]; exact (row j bj).2.2.2
  have ne : X i≠X j := by intro h; apply ij; apply Fin.ext; dsimp [X] at h; omega
  have heights : (p i:ℝ)+(p j:ℝ)≤(log S)^16 := by
    rw [ls]
    have pi : (p i:ℝ) ≤ k := by exact_mod_cast (row i bi).2.1.le
    have pj : (p j:ℝ) ≤ k := by exact_mod_cast (row j bj).2.1.le
    linarith only [pi,pj,kl,cap16,pow_nonneg Lp.le 3]
  have endE : (e i:ℝ)≤(log S)^16 := by
    rw [ls]
    have h := pow_le_pow_right₀ (by linarith : 1≤L) (by decide : 1≤3)
    rw [pow_one] at h
    linarith only [expbd i bi,h,cap16]
  have room : T≤log S-log 2 := by rw [ls]; dsimp [T]; linarith [log_two_lt_d9]
  obtain ⟨x,y,m,xx,yy,hx,hy,low,high,lv,nonzero,near⟩ := forms ne (by dsimp [X]; omega) (by dsimp [X]; omega)
    (row i bi).2.2.1 (row j bj).2.2.1 (row i bi).1.pos (row j bj).1.pos (row i bi).2.2.2 same
    (by omega : 0<n) (bounds i).1 (bounds j).1 (bounds i).2 (bounds j).2 ks sp heights emin endE (ai.trans room) (aj.trans room) (close.trans width)
  exact ⟨S,x,y,m,hS,Spow,xx,yy,hx,hy,low,high,lv,nonzero,near⟩
