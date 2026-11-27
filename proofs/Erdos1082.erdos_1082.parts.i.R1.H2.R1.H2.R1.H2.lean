import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1
import Mathlib

/-! Dyadic valuations and field-degree obstructions to a diameter pentagon. -/

section
/- A closed equilateral polygon of unit side in the 2-adic plane has even length. -/
open Classical
noncomputable section
namespace Erdos1082Padic

private lemma dominant_integral (x y : ℚ_[2]) (h : x^2+y^2=1) (hd : ‖y‖≤‖x‖) : ‖x‖≤1 := by
  by_contra! hx
  have hx0 : x≠0 := by rintro rfl; norm_num at hx
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx0
  let t : ℤ_[2] := ⟨y/x,by rw [norm_div]; exact (div_le_one hn).mpr hd⟩
  have hv : ‖(1:ℚ_[2])/x‖<1 := by rw [norm_div,norm_one]; exact (div_lt_one hn).mpr hx
  let s : ℤ_[2] := ⟨1/x,hv.le⟩
  have id : 1+t^2=s^2 := by
    apply PadicInt.ext
    change 1+(y/x)^2=(1/x)^2
    field_simp [hx0]
    linear_combination h
  obtain ⟨b,hb⟩ := (PadicInt.norm_lt_one_iff_dvd s).mp hv
  rw [hb] at id
  have eq := congrArg (PadicInt.toZModPow (p:=2) 2) id
  simp only [map_add,map_one,map_mul,map_pow,map_natCast] at eq
  let r := PadicInt.toZModPow (p:=2) 2
  change 1+(r t)^2=(2*r b)^2 at eq
  exact (by decide : ∀ a b : ZMod 4, 1+a^2≠(2*b)^2) (r t) (r b) eq

lemma unit_circle_integral (x y : ℚ_[2]) (h : x^2+y^2=1) : ‖x‖≤1 ∧ ‖y‖≤1 := by
  rcases le_total ‖x‖ ‖y‖ with hr|hr
  · have u := dominant_integral y x (by rwa [add_comm]) hr
    exact ⟨hr.trans u,u⟩
  · have u := dominant_integral x y h hr
    exact ⟨u,hr.trans u⟩

theorem no_odd_unit_polygon {I : Type*} [Fintype I] (x y : I→ℚ_[2])
    (unit : ∀i,(x i)^2+(y i)^2=1) (closeX : ∑i,x i=0) (closeY : ∑i,y i=0) :
    (Fintype.card I : ZMod 2)=0 := by
  let a (i:I) : ℤ_[2] := ⟨x i,(unit_circle_integral _ _ (unit i)).1⟩
  let b (i:I) : ℤ_[2] := ⟨y i,(unit_circle_integral _ _ (unit i)).2⟩
  let j : ℤ_[2] →+* ℚ_[2] := PadicInt.Coe.ringHom
  have xy (i:I) : (a i)^2+(b i)^2=1 := by
    apply PadicInt.ext
    change j ((a i)^2+(b i)^2) = j 1
    rw [map_add,map_pow,map_pow,map_one]
    exact unit i
  let r := PadicInt.toZMod (p:=2)
  have parity (i:I) : r (a i)+r (b i)=1 := by
    have t := congrArg r (xy i)
    simp only [map_add,map_pow,map_one] at t
    exact (by decide : ∀u v:ZMod 2,u^2+v^2=1→u+v=1) _ _ t
  have ax : ∑i,a i=0 := by
    apply PadicInt.ext
    change j (∑i,a i) = j 0
    rw [map_sum,map_zero]
    exact closeX
  have byy : ∑i,b i=0 := by
    apply PadicInt.ext
    change j (∑i,b i) = j 0
    rw [map_sum,map_zero]
    exact closeY
  calc
    (Fintype.card I : ZMod 2) = ∑_i:I,1 := by simp
    _ = ∑i,(r (a i)+r (b i)) := Finset.sum_congr rfl (fun i _ => (parity i).symm)
    _ = 0 := by rw [Finset.sum_add_distrib,←map_sum,←map_sum,ax,byy,map_zero,zero_add]
end Erdos1082Padic
end
end

section
namespace Erdos1082Gaussian
lemma dist_sq (z w : ℂ) : dist z w^2=(z.re-w.re)^2+(z.im-w.im)^2 := by
  rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring
lemma real_coord (z : ℂ) : z.re=(dist z 0^2-dist z 1^2+1)/2 := by rw [dist_sq,dist_sq]; simp; ring

end Erdos1082Gaussian
end

section
open Classical EuclideanGeometry
noncomputable section
namespace Erdos1082Padic
open Erdos1082Gaussian
lemma coordinate_recovery (K:Subfield ℝ) (A : Finset ℂ) (h0 : 0∈A) (h1 : 1∈A)
    (hq : ∀x∈A,∀y∈A,dist x y∈K) {p q:ℂ} (hp:p∈A) (hqq:q∈A) (hne:p≠q)
    (h₁ : dist p 0=dist p 1) (h₂ : dist q 0=dist q 1) : ∀z∈A,z.re∈K ∧ z.im∈K := by
  have ds (x:ℂ) (hx:x∈A) (y:ℂ) (hy:y∈A) : dist x y^2∈K := by
    rw [pow_two]; exact K.mul_mem (hq x hx y hy) (hq x hx y hy)
  have re : p.re=q.re := by rw [real_coord p,real_coord q,h₁,h₂]; ring
  have ni : q.im-p.im≠0 := fun e => hne (Complex.ext re (sub_eq_zero.mp e).symm)
  have diff : (q.im-p.im)^2=dist q p^2 := by rw [dist_sq,←re,sub_self,zero_pow (by decide),zero_add]
  have eqabs : |q.im-p.im|=dist q p := by
    nlinarith [sq_abs (q.im-p.im),abs_nonneg (q.im-p.im),(dist_nonneg : 0≤dist q p)]
  have ir : q.im-p.im∈K := by
    have hv := hq q hqq p hp
    rcases le_or_gt 0 (q.im-p.im) with hh|hh
    · rw [abs_of_nonneg hh] at eqabs; exact eqabs ▸ hv
    · rw [abs_of_neg hh] at eqabs
      exact K.neg_mem_iff.mp (eqabs ▸ hv)
  intro z hz
  constructor
  · rw [real_coord]
    exact K.div_mem (K.add_mem (K.sub_mem (ds _ hz _ h0) (ds _ hz _ h1)) K.one_mem) (by norm_num)
  have im : z.im=((dist z p^2-dist z q^2)-(dist 0 p^2-dist 0 q^2))/(2*(q.im-p.im)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) ni)).mpr
    rw [dist_sq,dist_sq,dist_sq,dist_sq,←re,Complex.zero_re,Complex.zero_im]
    ring
  rw [im]
  exact K.div_mem (K.sub_mem (K.sub_mem (ds _ hz _ hp) (ds _ hz _ hqq))
    (K.sub_mem (ds _ h0 _ hp) (ds _ h0 _ hqq))) (K.mul_mem (by norm_num) ir)

theorem normalized_field (K:Subfield ℝ) (A : Finset ℝ²) (s:ℝ) (hs:0<s) (hq : ∀x∈A,∀y∈A,dist x y/s∈K)
    (u v p q:ℝ²) (hu:u∈A) (hv:v∈A) (hp:p∈A) (hqq:q∈A) (huv:u≠v) (hpq:p≠q)
    (pe:dist p u=dist p v) (qe:dist q u=dist q v) :
    ∃f:ℝ²→ℂ,∃t:ℝ,0<t ∧ (∀x y,dist (f x) (f y)=t*dist x y) ∧ (∀x∈A,(f x).re∈K ∧ (f x).im∈K) ∧ ∀x∈A,∀y∈A,dist (f x) (f y)∈K := by
  classical
  let E := Complex.orthonormalBasisOneI.repr.symm
  let a := E (v-u)
  have ha : a≠0 := fun e => huv ((sub_eq_zero.mp (E.injective (e.trans (map_zero E).symm))).symm)
  let f (x:ℝ²) := E (x-u)/a
  have hnorm : ‖a‖=dist u v := by dsimp [a]; rw [E.norm_map,←dist_eq_norm,dist_comm]
  have du : 0<dist u v := dist_pos.mpr huv
  have hd (x y : ℝ²) : dist (f x) (f y)=dist x y/dist u v := by
    rw [dist_eq_norm]; dsimp only [f]; rw [←sub_div,←map_sub,norm_div,E.norm_map,
      show (x-u)-(y-u)=x-y by abel,←dist_eq_norm,hnorm]
  have hfu : f u=0 := by simp [f]
  have hfv : f v=1 := by exact div_self ha
  have hinj : Function.Injective f := by
    intro x y e; have hh:=hd x y; rw [e,dist_self] at hh
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp hh.symm).resolve_right du.ne')
  let B := A.image f
  have m (x) (hx:x∈A) : f x∈B := Finset.mem_image_of_mem f hx
  have fieldmem (x:ℂ) (hx:x∈B) (y:ℂ) (hy:y∈B) : dist x y∈K := by
    obtain ⟨x,hxA,rfl⟩ := Finset.mem_image.mp hx; obtain ⟨y,hyA,rfl⟩ := Finset.mem_image.mp hy
    have e := K.div_mem (hq x hxA y hyA) (hq u hu v hv)
    rwa [div_div_div_cancel_right₀ hs.ne',←hd] at e
  have pE : dist (f p) 0=dist (f p) 1 := by rw [←hfu,←hfv,hd,hd,pe]
  have qE : dist (f q) 0=dist (f q) 1 := by rw [←hfu,←hfv,hd,hd,qe]
  have coords := coordinate_recovery K B (hfu ▸ m u hu) (hfv ▸ m v hv) fieldmem (m p hp) (m q hqq) (hinj.ne hpq) pE qE
  refine ⟨f,(dist u v)⁻¹,inv_pos.mpr du,fun x y => (hd x y).trans (div_eq_inv_mul _ _),?_⟩
  exact ⟨fun x hx => coords _ (m x hx), fun x hx y hy => fieldmem _ (m x hx) _ (m y hy)⟩
end Erdos1082Padic
end
end

section
/- The normalized distance field of a critical equilateral five-cycle has no dyadic embedding. -/
open Classical EuclideanGeometry
noncomputable section
namespace Erdos1082Padic
open OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1
theorem critical_field_model (K:Subfield ℝ) (A : Finset ℝ²) (hN : NonTrilinear (A:Set ℝ²))
    (hA : A.card=2*distinctDistances A+2) (s:ℝ) (hs:0<s) (hq : ∀x∈A,∀y∈A,dist x y/s∈K) :
    ∃f:ℝ²→ℂ,∃t:ℝ,0<t ∧ (∀x y,dist (f x) (f y)=t*dist x y) ∧ (∀x∈A,(f x).re∈K ∧ (f x).im∈K) ∧ ∀x∈A,∀y∈A,dist (f x) (f y)∈K := by
  classical
  let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
  have h := critical_bisectors A hN hA
  change 3*A.card+(A.offDiag.filter fun b => k b=0).card≤(A.offDiag.filter fun b => k b=2).card at h
  obtain ⟨⟨u,v⟩,huv⟩ := Finset.card_pos.mp (show 0<(A.offDiag.filter fun b => k b=2).card by omega)
  obtain ⟨hpair,eq⟩ := Finset.mem_filter.mp huv
  obtain ⟨hu,hv,hne⟩ := Finset.mem_offDiag.mp hpair
  change (A.filter fun p => dist p u=dist p v).card=2 at eq
  obtain ⟨p,hp,q,hq',hpq⟩ := Finset.one_lt_card.mp (show 1<(A.filter fun p => dist p u=dist p v).card by omega)
  obtain ⟨hp,ep⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq',eq'⟩ := Finset.mem_filter.mp hq'
  exact normalized_field K A s hs hq u v p q hu hv hp hq' hne hpq ep eq'


theorem critical_pentagon_no_dyadic_model (A : Finset ℝ²) (hN : NonTrilinear (A:Set ℝ²))
    (hA : A.card=2*distinctDistances A+2) (M:ℝ) (hM:0<M) (cyc : ∃a b c d e:A,
      [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (K:Subfield ℝ) (s:ℝ) (hs:0<s) (hK:∀x∈A,∀y∈A,dist x y/s∈K) : IsEmpty (K→+*ℚ_[2]) := by
  constructor
  intro φ
  obtain ⟨f,t,ht,hd,coord,distmem⟩ := critical_field_model K A hN hA s hs hK
  obtain ⟨a,b,c,d,e,_,e₀,e₁,e₂,e₃,e₄⟩ := cyc
  let p : Fin 5→A := ![a,b,c,d,e]
  have edges (i : Fin 5) : dist (p i).1 (p (i+1)).1=M := by fin_cases i <;> assumption
  have side (i:Fin 5) : dist (f (p i).1) (f (p (i+1)).1)=t*M := by rw [hd,edges]
  let l : K := ⟨t*M,by simpa only [hd,e₀] using distmem _ a.2 _ b.2⟩
  have hl : (l:ℝ)≠0 := (mul_pos ht hM).ne'
  let U (i:Fin 5) : K := ⟨(f (p i).1).re,(coord _ (p i).2).1⟩
  let V (i:Fin 5) : K := ⟨(f (p i).1).im,(coord _ (p i).2).2⟩
  let X (i:Fin 5) := φ (U i/l-U (i+1)/l)
  let Y (i:Fin 5) := φ (V i/l-V (i+1)/l)
  have equation (i:Fin 5) : (U i/l-U (i+1)/l)^2+(V i/l-V (i+1)/l)^2=1 := by
    apply Subtype.ext
    push_cast
    have h := congrArg (fun w:ℝ => w^2) (side i)
    change dist (f (p i).1) (f (p (i+1)).1)^2=(l:ℝ)^2 at h
    rw [Erdos1082Gaussian.dist_sq] at h
    dsimp only [U,V]
    field_simp [hl]
    linear_combination h
  have unit (i:Fin 5) : (X i)^2+(Y i)^2=1 := by
    simpa only [X,Y,map_add,map_pow,map_one] using congrArg φ (equation i)
  have tel (w:Fin 5→ℚ_[2]) : ∑ i,(w i-w (i+1))=0 := by
    simp only [Fin.sum_univ_succ]
    change (w 0-w 1)+((w 1-w 2)+((w 2-w 3)+((w 3-w 4)+((w 4-w 0)+0))))=0
    ring
  have bad := no_odd_unit_polygon X Y unit
    (by simpa only [X,map_sub] using tel (fun i => φ (U i/l)))
    (by simpa only [Y,map_sub] using tel (fun i => φ (V i/l)))
  norm_num at bad
  exact (by decide : (5:ZMod 2)≠0) bad
end Erdos1082Padic
end
end

section
/- Unit vectors over a dyadic field of odd ramification reduce to the affine line x+y=1. -/
noncomputable section
open Classical WithZero
namespace Erdos1082ValParity
variable {K:Type*} [Field K] (v : Valuation K ℤᵐ⁰) (small : v 2<1) (nonsq : ∀a : ℤᵐ⁰,a^2≠v 2)

include nonsq in
lemma coord_integral (x y:K) (e : x^2+y^2=1) : v x≤1 := by
  by_contra! hx
  have hx2 : 1<(v x)^2 := one_lt_pow₀ hx (by decide)
  have ey : y^2=1-x^2 := by linear_combination e
  have hxy : (v y)^2=(v x)^2 := by
    rw [← map_pow,ey,v.map_sub_eq_of_lt_right (by simpa using hx2),map_pow]
  have eq : v y=v x := (pow_left_inj₀ zero_le zero_le (by decide : 2≠0)).mp hxy
  have hid : (x+y-1)^2=2*(x-1)*(y-1) := by linear_combination e
  have q := congrArg v hid
  rw [map_pow,map_mul,map_mul,v.map_sub_eq_of_lt_left (x:=x) (y:=1) (by simpa using hx),
    v.map_sub_eq_of_lt_left (x:=y) (y:=1) (by simpa [eq] using hx),eq] at q
  apply nonsq (v (x+y-1)/v x)
  rw [div_pow,q,div_eq_iff (pow_ne_zero 2 (zero_lt_one.trans hx).ne')]
  rw [pow_two,mul_assoc]

include nonsq small in
lemma unit_reduction (x y:K) (e:x^2+y^2=1) : v (x+y-1)<1 := by
  have hx := coord_integral v nonsq x y e
  have hy := coord_integral v nonsq y x (by rwa [add_comm])
  have h1 : v (x-1)≤1 := v.map_sub_le hx (by simp)
  have h2 : v (y-1)≤1 := v.map_sub_le hy (by simp)
  have hid : (x+y-1)^2=2*(x-1)*(y-1) := by linear_combination e
  have vv : v (x+y-1)^2<1 := by
    rw [←map_pow,hid,map_mul,map_mul]
    calc
      _ ≤ v 2*1*1 := by gcongr
      _ < 1 := by simpa using small
  by_contra! h
  exact vv.not_ge (one_le_pow₀ h)

include nonsq small in
theorem no_five (x y:Fin 5→K) (e:∀i,(x i)^2+(y i)^2=1) (hx:∑i,x i=0) (hy:∑i,y i=0) : False := by
  have all := v.map_sum_lt (s:=Finset.univ) (f:=fun i : Fin 5 => x i+y i-1) one_ne_zero
    (fun i _ => unit_reduction v small nonsq _ _ (e i))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,hx,hy,zero_add,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_one,zero_sub,v.map_neg] at all
  have four : v (4:K)<1 := by
    rw [show (4:K)=2*2 by ring,map_mul]
    exact (mul_le_mul_right (a:=v (2:K)) small.le).trans_lt (by simpa using small)
  have five : v (5:K)=1 := by rw [show (5:K)=4+1 by ring,v.map_add_eq_of_lt_right (by simpa using four),map_one]
  exact all.ne five

end Erdos1082ValParity
end
end

section
/- Every number field of odd degree has a dyadic valuation of odd ramification. -/
open Classical WithZero IsDedekindDomain NumberField
noncomputable section
namespace Erdos1082ValParity

theorem odd_dyadic_valuation (K:Type*) [Field K] [NumberField K] (hodd : Odd (Module.finrank ℚ K)) :
    ∃ v:Valuation K ℤᵐ⁰, v 2<1 ∧ ∀a:ℤᵐ⁰, a^2≠v 2 := by
  classical
  let p : Ideal ℤ := Ideal.span {(2:ℤ)}
  have pn : p≠⊥ := by simp [p]
  have prime : p.IsPrime := (Ideal.span_singleton_prime (by norm_num : (2:ℤ)≠0)).mpr (by norm_num)
  letI : p.IsMaximal := prime.isMaximal_of_ne_bot pn
  have sum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K pn
  have pick : ∃P∈IsDedekindDomain.primesOverFinset p (𝓞 K), ¬2∣p.ramificationIdx' P := by
    by_contra! h
    have hd : 2∣Module.finrank ℚ K := by
      rw [←sum]
      exact Finset.dvd_sum (fun P hP => dvd_mul_of_dvd_left (h P hP) _)
    obtain ⟨j,hj⟩ := hodd
    omega
  obtain ⟨P,hP,hoddP⟩ := pick
  obtain ⟨primeP,overP⟩ := (IsDedekindDomain.mem_primesOverFinset_iff pn _).mp hP
  letI : P.LiesOver p := overP
  let v : HeightOneSpectrum ℤ := ⟨p,prime,pn⟩
  let w : HeightOneSpectrum (𝓞 K) := ⟨P,primeP,Ideal.ne_bot_of_liesOver_of_ne_bot pn P⟩
  letI : w.asIdeal.LiesOver v.asIdeal := overP
  have hv : v.intValuation (2:ℤ)=exp (-1:ℤ) := v.intValuation_singleton (by norm_num) rfl
  have w2 : w.valuation K (2:K)=exp (-1:ℤ)^(p.ramificationIdx' P) := by
    have t := v.valuation_liesOver (K:=ℚ) K w (2:ℚ)
    have pv : v.valuation ℚ (2:ℚ)=exp (-1:ℤ) := by
      have c := v.valuation_of_algebraMap (K:=ℚ) (2:ℤ)
      exact c.trans hv
    rw [pv,map_ofNat] at t
    exact t.symm
  refine ⟨w.valuation K,?_,?_⟩
  · rw [w2,←exp_nsmul,←exp_zero,exp_lt_exp]
    simp
    omega
  · intro a e
    rw [w2] at e
    have logs := congrArg (fun x:ℤᵐ⁰ => log x) e
    simp only [log_pow,log_exp,Int.nsmul_eq_mul] at logs
    omega
end Erdos1082ValParity
end
end

section
/- The normalized field of lengths of a critical pentagon cannot have odd degree. -/
open Classical EuclideanGeometry
noncomputable section
namespace Erdos1082Padic
theorem critical_pentagon_even_degree (A : Finset ℝ²) (hN : NonTrilinear (A:Set ℝ²))
    (hA : A.card=2*distinctDistances A+2) (M:ℝ) (hM:0<M) (cyc : ∃a b c d e:A,
      [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (K:Subfield ℝ) (s:ℝ) (hs:0<s) (hK:∀x∈A,∀y∈A,dist x y/s∈K) : Even (Module.finrank ℚ K) := by
  by_contra hn
  have odd := Nat.not_even_iff_odd.mp hn
  letI : Module.Finite ℚ K := Module.finite_of_finrank_pos (by obtain ⟨k,hk⟩ := odd; omega)
  letI : NumberField K := ⟨⟩
  obtain ⟨val,small,nonsq⟩ := Erdos1082ValParity.odd_dyadic_valuation K odd
  obtain ⟨f,t,ht,hd,coord,distmem⟩ := critical_field_model K A hN hA s hs hK
  obtain ⟨a,b,c,d,e,_,e₀,e₁,e₂,e₃,e₄⟩ := cyc
  let p : Fin 5→A := ![a,b,c,d,e]
  have edges (i : Fin 5) : dist (p i).1 (p (i+1)).1=M := by fin_cases i <;> assumption
  have side (i:Fin 5) : dist (f (p i).1) (f (p (i+1)).1)=t*M := by rw [hd,edges]
  let l : K := ⟨t*M,by simpa only [hd,e₀] using distmem _ a.2 _ b.2⟩
  have hl : (l:ℝ)≠0 := (mul_pos ht hM).ne'
  let U (i:Fin 5) : K := ⟨(f (p i).1).re,(coord _ (p i).2).1⟩
  let V (i:Fin 5) : K := ⟨(f (p i).1).im,(coord _ (p i).2).2⟩
  have equation (i:Fin 5) : (U i/l-U (i+1)/l)^2+(V i/l-V (i+1)/l)^2=1 := by
    apply Subtype.ext
    push_cast
    have h := congrArg (fun w:ℝ => w^2) (side i)
    change dist (f (p i).1) (f (p (i+1)).1)^2=(l:ℝ)^2 at h
    rw [Erdos1082Gaussian.dist_sq] at h
    dsimp only [U,V]
    field_simp [hl]
    linear_combination h
  have tel (w:Fin 5→K) : ∑ i,(w i-w (i+1))=0 := by
    simp only [Fin.sum_univ_succ]
    change (w 0-w 1)+((w 1-w 2)+((w 2-w 3)+((w 3-w 4)+((w 4-w 0)+0))))=0
    ring
  exact Erdos1082ValParity.no_five val small nonsq _ _ equation
    (tel (fun i => U i/l)) (tel (fun i => V i/l))
end Erdos1082Padic
end
end

section
open EuclideanGeometry OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter
namespace Erdos1082SecondAux
set_option maxHeartbeats 800000 in
lemma separated_edges_card {V : Type*} [DecidableEq V] (T : Finset V) (E : Finset (V×V))
    (hT : T.Nonempty) (hE : ∀ e∈E, e.1∈T ∧ e.2∈T)
    (hcut : ∀ e∈E, ∃ f : V→Bool, f e.1≠f e.2 ∧ ∀ t∈E,t≠e → f t.1=f t.2) :
    E.card<T.card := by
  classical
  suffices hall : ∀ n : ℕ, ∀ (T : Finset V) (E : Finset (V×V)), T.card=n → T.Nonempty →
      (∀ e∈E, e.1∈T ∧ e.2∈T) → (∀ e∈E, ∃ f : V→Bool, f e.1≠f e.2 ∧ ∀ t∈E, t≠e → f t.1=f t.2) →
      E.card<n from hall _ T E rfl hT hE hcut
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T E hsize hT hinc hcut
    by_cases hne : E.Nonempty
    · obtain ⟨e,he⟩ := hne
      obtain ⟨f,hd,hs⟩ := hcut e he
      let B (b : Bool) := T.filter fun x => f x=b
      let F (b : Bool) := E.filter fun t => f t.1=b ∧ f t.2=b
      have hn (b : Bool) : (B b).Nonempty := by
        by_cases h : f e.1=b
        · exact ⟨e.1,Finset.mem_filter.mpr ⟨(hinc e he).1,h⟩⟩
        · refine ⟨e.2,Finset.mem_filter.mpr ⟨(hinc e he).2,?_⟩⟩
          have aux (p q w : Bool) (h₁ : p≠q) (h₂ : p≠w) : q=w := by
            cases p <;> cases q <;> cases w <;> simp_all
          exact aux _ _ _ hd h
      have hsum : (B false).card+(B true).card=T.card := by
        have hh := Finset.card_filter_add_card_filter_not (s:=T) (fun x => f x=false)
        simpa [B] using hh
      have hb (b : Bool) : (F b).card<(B b).card := by
        apply ih (B b).card (by have h0 := Finset.card_pos.mpr (hn false); have h1 := Finset.card_pos.mpr (hn true); cases b <;> omega)
          (B b) (F b) rfl (hn b)
        · intro t ht
          obtain ⟨ht,h₁,h₂⟩ := Finset.mem_filter.mp ht
          exact ⟨Finset.mem_filter.mpr ⟨(hinc t ht).1,h₁⟩,Finset.mem_filter.mpr ⟨(hinc t ht).2,h₂⟩⟩
        · intro t ht
          obtain ⟨g,hg,hgt⟩ := hcut t (Finset.mem_filter.mp ht).1
          exact ⟨g,hg,fun w hw hh => hgt w (Finset.mem_filter.mp hw).1 hh⟩
      have hsub : E.erase e ⊆ F false ∪ F true := by
        intro t ht
        obtain ⟨ht,hte⟩ := Finset.mem_erase.mp ht
        have hh := hs t hte ht
        cases h : f t.1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hte,h,hh.symm.trans h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hte,h,hh.symm.trans h⟩)
      have hbound := (Finset.card_le_card hsub).trans (Finset.card_union_le ..)
      have hecard := Finset.card_erase_add_one he
      have := hb true; have := hb false; omega
    · have := Finset.card_pos.mpr hT
      rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
      omega


lemma diameter_bipartite_cut (A : Finset ℝ²) (M : ℝ) (hM : 0<M)
    (hm : ∀ x y : A, dist x.1 y.1≤M) (χ : A→Bool) (a b : A) (ha : χ a=false) (hb : χ b=true)
    (hab : dist a.1 b.1=M) :
    ∃ f : A→Bool, f a≠f b ∧ ∀ i j : A, χ i=false → χ j=true → dist i.1 j.1=M → (i,j)≠(a,b) → f i=f j := by
  classical
  have ab : a≠b := by intro h; simp [h,hb] at ha
  by_cases hax : ∃ x : A, χ x=true ∧ x≠b ∧ dist a.1 x.1=M
  · by_cases hby : ∃ y : A, χ y=false ∧ y≠a ∧ dist b.1 y.1=M
    · obtain ⟨x,hx,hxb,hax⟩ := hax
      obtain ⟨y,hy,hya,hby⟩ := hby
      have hxa : x≠a := by intro h; simp [h,ha] at hx
      have hyb : y≠b := by intro h; simp [h,hb] at hy
      obtain ⟨s,hs⟩ := diameter_sides A M hM hm a b hab
      have hxy := (hs x y hxa hxb hya hyb).2 hax hby
      let f (v : A) := if v=a then !(s x) else if v=b then s x else xor (s v) (χ v)
      refine ⟨f,by simp [f,ab,ab.symm],?_⟩
      intro i j hi hj hdist hne
      have hib : i≠b := by intro h; simp [h,hb] at hi
      have hja : j≠a := by intro h; simp [h,ha] at hj
      by_cases hia : i=a
      · subst i
        have hjb : j≠b := by rintro rfl; exact hne rfl
        have hs' := (hs j y hja hjb hya hyb).2 hdist hby
        simp [f,hja,hjb,hj,hs',hxy]
      by_cases hjb : j=b
      · subst j
        have hs' := (hs x i hxa hxb hia hib).2 hax ((dist_comm b.1 i.1).trans hdist)
        simp [f,hia,hib,hi,ab.symm,hs']
      have hs' := (hs i j hia hib hja hjb).1 hdist
      simp only [f,if_neg hia,if_neg hib,if_neg hja,if_neg hjb,hi,hj]
      cases h₁ : s i <;> cases h₂ : s j <;> simp_all
    · let f (v : A) := decide (v=b)
      refine ⟨f,by simp [f,ab],?_⟩
      intro i j hi hj hdist hne
      have hib : i≠b := by intro h; simp [h,hb] at hi
      have hjb : j≠b := by
        rintro rfl
        exact hby ⟨i,hi,by rintro rfl; exact hne rfl,(dist_comm _ _).trans hdist⟩
      simp [f,hib,hjb]
  · let f (v : A) := decide (v=a)
    refine ⟨f,by simp [f,ab.symm],?_⟩
    intro i j hi hj hdist hne
    have hja : j≠a := by intro h; simp [h,ha] at hj
    have hia : i≠a := by
      rintro rfl
      exact hax ⟨j,hj,by rintro rfl; exact hne rfl,hdist⟩
    simp [f,hia,hja]

lemma bipartite_diameter_sparse (A : Finset ℝ²) (M : ℝ) (hM : 0<M) (hA : A.Nonempty)
    (hm : ∀ x y : A, dist x.1 y.1≤M) (χ : A→Bool) :
    ((A.attach ×ˢ A.attach).filter fun e : A×A => χ e.1=false ∧ χ e.2=true ∧ dist e.1.1 e.2.1=M).card<A.card := by
  classical
  rw [←Finset.card_attach (s:=A)]
  apply separated_edges_card A.attach _ (Finset.attach_nonempty_iff.mpr hA)
  · intro e he
    exact Finset.mem_product.mp (Finset.mem_filter.mp he).1
  · rintro ⟨a,b⟩ he
    obtain ⟨ha,hb,hab⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨f,hf,hother⟩ := diameter_bipartite_cut A M hM hm χ a b ha hb hab
    refine ⟨f,hf,?_⟩
    rintro ⟨i,j⟩ ht hne
    obtain ⟨hi,hj,hd⟩ := (Finset.mem_filter.mp ht).2
    exact hother i j hi hj hd hne


end Erdos1082SecondAux
end

section
/- Two colors separate all diameter edges except a specified nonpendant edge. -/
open EuclideanGeometry
open OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter
noncomputable section
namespace Erdos1082Second

lemma diameter_coloring (A : Finset ℝ²) (M : ℝ) (hM:0<M) (bound:∀x y:A,dist x.1 y.1≤M)
    (a b x y:A) (hab:dist a.1 b.1=M) (xa:x≠a) (xb:x≠b) (ya:y≠a) (yb:y≠b)
    (ax:dist a.1 x.1=M) (byy:dist b.1 y.1=M) :
    ∃f:A→Bool, ∀i j:A,dist i.1 j.1=M → ¬(i=a ∧ j=b) → ¬(i=b ∧ j=a) → f i≠f j := by
  obtain ⟨s,hs⟩ := diameter_sides A M hM bound a b hab
  have ab : a≠b := by rintro rfl; simp at hab; linarith
  let f (i:A) := if i=a ∨ i=b then !(s x) else s i
  have xy := (hs x y xa xb ya yb).2 ax byy
  have froma (j:A) (ja:j≠a) (jb:j≠b) (de:dist a.1 j.1=M) : f a≠f j := by
    have eq := (hs j y ja jb ya yb).2 de byy
    simp [f,ja,jb,eq,xy]
  have fromb (j:A) (ja:j≠a) (jb:j≠b) (de:dist b.1 j.1=M) : f b≠f j := by
    have eq := (hs x j xa xb ja jb).2 ax de
    simp [f,ja,jb,←eq]
  refine ⟨f,?_⟩
  intro i j de neq1 neq2
  have ij:i≠j := by rintro rfl; simp at de; linarith
  by_cases ia:i=a
  · subst i; exact froma j ij.symm (fun h => neq1 ⟨rfl,h⟩) de
  by_cases ib:i=b
  · subst i; exact fromb j (fun h => neq2 ⟨rfl,h⟩) ij.symm de
  by_cases ja:j=a
  · subst j; exact (froma i ia ib ((dist_comm _ _).trans de)).symm
  by_cases jb:j=b
  · subst j; exact (fromb i ia ib ((dist_comm _ _).trans de)).symm
  simpa [f,ia,ib,ja,jb] using (hs i j ia ib ja jb).1 de

lemma two_cut_bound (A:Finset ℝ²) (M:ℝ) (hM:0<M) (nonempty:A.Nonempty) (bound:∀x y:A,dist x.1 y.1≤M)
    (a b:A) (f:A→Bool) (sides:∀i j:A,dist i.1 j.1=M → ¬(i=a ∧ j=b) → ¬(i=b ∧ j=a) → f i≠f j) :
    (A.offDiag.filter fun e => dist e.1 e.2=M).card≤2*A.card := by
  classical
  let F := (A.attach ×ˢ A.attach).filter fun e : A×A => f e.1=false ∧ f e.2=true ∧ dist e.1.1 e.2.1=M
  let g (p:A×A) : ℝ²×ℝ² := (p.1.1,p.2.1)
  have nF:F.card<A.card := Erdos1082SecondAux.bipartite_diameter_sparse A M hM nonempty bound f
  let E := F.image g ∪ F.image (fun p => (g p).swap) ∪ {(a.1,b.1),(b.1,a.1)}
  have sub : (A.offDiag.filter fun e => dist e.1 e.2=M)⊆E := by
    rintro ⟨i,j⟩ hp
    obtain ⟨h,hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi,hj,hn⟩ := Finset.mem_offDiag.mp h
    let I:A := ⟨i,hi⟩; let J:A := ⟨j,hj⟩
    by_cases h1 : I=a ∧ J=b
    · apply Finset.mem_union_right; simp [←h1.1,←h1.2,I,J]
    by_cases h2 : I=b ∧ J=a
    · apply Finset.mem_union_right; simp [←h2.1,←h2.2,I,J]
    apply Finset.mem_union_left
    have hf := sides I J hd h1 h2
    cases fi : f I <;> cases fj : f J <;> simp only [fi,fj,ne_eq] at hf
    · contradiction
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(I,J),Finset.mem_filter.mpr ⟨by simp,fi,fj,hd⟩,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(J,I),Finset.mem_filter.mpr ⟨by simp,fj,fi,(dist_comm _ _).trans hd⟩,rfl⟩)
    · contradiction
  have ne : E.card≤F.card+F.card+2 := by
    apply (Finset.card_union_le _ _).trans
    gcongr
    · exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    · exact Finset.card_le_two
  exact (Finset.card_le_card sub).trans (by omega)
end Erdos1082Second
end
end

section
/- Diameter pairs are at most as numerous as the points. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

theorem diameter_count (M:ℝ) (hM:0<M) (A:Finset ℝ²) :
    (∀x∈A,∀y∈A,dist x y≤M) → (A.offDiag.filter fun e => dist e.1 e.2=M).card≤2*A.card := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro bound
    by_cases low : ∃a∈A,∃b:ℝ²,∀y∈A,dist a y=M → y=b
    · obtain ⟨a,ha,b,leaf⟩ := low
      let B := A.erase a
      have hB := ih B (Finset.erase_ssubset ha) (fun x hx y hy => bound x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
      let F := B.offDiag.filter fun e => dist e.1 e.2=M
      have sub : (A.offDiag.filter fun e => dist e.1 e.2=M)⊆F∪{(a,b),(b,a)} := by
        rintro ⟨x,y⟩ hp
        obtain ⟨h,hd⟩ := Finset.mem_filter.mp hp
        obtain ⟨hx,hy,hn⟩ := Finset.mem_offDiag.mp h
        by_cases hxa:x=a
        · subst x; obtain rfl := leaf y hy hd; simp
        by_cases hya:y=a
        · subst y; obtain rfl := leaf x hx ((dist_comm _ _).trans hd); simp
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_erase.mpr ⟨hxa,hx⟩,
          Finset.mem_erase.mpr ⟨hya,hy⟩,hn⟩,hd⟩)
      have cnt := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
      have pair : ({(a,b),(b,a)}:Finset (ℝ²×ℝ²)).card≤2 := Finset.card_le_two
      have dec := Finset.card_erase_add_one ha
      change F.card≤2*B.card at hB
      change B.card+1=A.card at dec
      omega
    · by_cases nonempty:A.Nonempty
      · have fresh (a:A) (u:A) : ∃x:A,dist a.1 x.1=M ∧ x≠u := by
          by_contra! hn
          apply low
          exact ⟨a.1,a.2,u.1,fun y hy de => congrArg Subtype.val (hn ⟨y,hy⟩ de)⟩
        obtain ⟨c,hc⟩ := nonempty
        let a:A := ⟨c,hc⟩
        obtain ⟨b,ab,_⟩ := fresh a a
        obtain ⟨x,ax,xb⟩ := fresh a b
        obtain ⟨y,byy,ya⟩ := fresh b a
        have xa:x≠a := by rintro rfl; simp at ax; linarith
        have yb:y≠b := by rintro rfl; simp at byy; linarith
        have bd (i j:A) := bound i.1 i.2 j.1 j.2
        obtain ⟨f,hf⟩ := diameter_coloring A M hM bd a b x y ab xa xb ya yb ax byy
        exact two_cut_bound A M hM ⟨c,hc⟩ bd a b f hf
      · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]

theorem diameter_multiplicity (A:Finset ℝ²) (M:ℝ) (hM:0<M) (bound:∀x∈A,∀y∈A,dist x y≤M) :
    distanceMultiplicity A M≤A.card := by
  have c := diameter_count M hM A bound
  unfold distanceMultiplicity
  omega
end Erdos1082Second
end
end

section
/- Interior diameter-neighbors on an arc cannot have any further diameter-neighbor. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

def arcParameter (x:ℂ) : ℝ := x.im/(1+x.re)

lemma arc_coordinates (x:ℂ) (hx:‖x‖=1) (cx:0≤x.re) :
    x.re*(1+(arcParameter x)^2)=1-(arcParameter x)^2 ∧
      x.im*(1+(arcParameter x)^2)=2*arcParameter x := by
  have eq : x.re*x.re+x.im*x.im=1 := by
    have h := Complex.sq_norm x
    rw [hx,Complex.normSq_apply] at h
    nlinarith only [h]
  have rn : 1+x.re≠0 := by linarith
  unfold arcParameter
  constructor <;> field_simp [rn] <;> first | linear_combination (x.re+1)*eq | linear_combination x.im*eq

lemma arc_parameter_inj {x y:ℂ} (hx:‖x‖=1) (hy:‖y‖=1) (cx:0≤x.re) (cy:0≤y.re) (he:arcParameter x=arcParameter y) : x=y := by
  obtain ⟨x1,x2⟩ := arc_coordinates x hx cx
  obtain ⟨y1,y2⟩ := arc_coordinates y hy cy
  rw [he] at x1 x2
  have np : 1+(arcParameter y)^2≠0 := by positivity
  exact Complex.ext (mul_right_cancel₀ np (x1.trans y1.symm)) (mul_right_cancel₀ np (x2.trans y2.symm))

def arcQuad (w:ℂ) (t:ℝ) := (‖w‖^2+2*w.re)*t^2-4*w.im*t+(‖w‖^2-2*w.re)

lemma arc_evaluation (x w:ℂ) (hx:‖x‖=1) (cx:0≤x.re) :
    arcQuad w (arcParameter x)=(‖w-x‖^2-1)*(1+(arcParameter x)^2) := by
  obtain ⟨ex,ey⟩ := arc_coordinates x hx cx
  have e : x.re*x.re+x.im*x.im=1 := by
    have h := Complex.sq_norm x
    rw [hx,Complex.normSq_apply] at h
    nlinarith only [h]
  unfold arcQuad
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  linear_combination 2*w.re*ex+2*w.im*ey-(1+(arcParameter x)^2)*e

lemma arc_strict {u t v a b c:ℝ} (hu:u<t) (hv:t<v) (ha:0<a)
    (eu:a*u^2+b*u+c≤0) (ev:a*v^2+b*v+c≤0) : a*t^2+b*t+c<0 := by
  by_contra! h
  have p : 0≤(t-u)*(a*(t+u)+b) := by nlinarith only [h,eu]
  have q : (v-t)*(a*(v+t)+b)≤0 := by nlinarith only [h,ev]
  have pp := nonneg_of_mul_nonneg_right p (sub_pos.mpr hu)
  have qq := nonpos_of_mul_nonpos_right q (sub_pos.mpr hv)
  nlinarith [mul_pos ha (sub_pos.mpr (hu.trans hv))]

lemma arc_middle (u x v w:ℂ) (hu:‖u‖=1) (hx:‖x‖=1) (hv:‖v‖=1)
    (uc:0≤u.re) (xc:0≤x.re) (vc:0≤v.re) (wc:0≤w.re) (wn:w≠0)
    (hux:arcParameter u<arcParameter x) (hxv:arcParameter x<arcParameter v)
    (wu:‖w-u‖≤1) (wv:‖w-v‖≤1) : ‖w-x‖<1 := by
  have pos : 0<‖w‖^2+2*w.re := by positivity
  have ch (a:ℂ) (h:‖a‖=1) (ha:0≤a.re) (hw:‖w-a‖≤1) : arcQuad w (arcParameter a)≤0 := by
    rw [arc_evaluation a w h ha]
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (w-a)]) (by positivity)
  have strict := arc_strict (a:=‖w‖^2+2*w.re) (b:=-4*w.im) (c:=‖w‖^2-2*w.re) hux hxv pos
    (by simpa [arcQuad,sub_eq_add_neg] using ch u hu uc wu) (by simpa [arcQuad,sub_eq_add_neg] using ch v hv vc wv)
  have neg : arcQuad w (arcParameter x)<0 := by simpa [arcQuad,sub_eq_add_neg] using strict
  rw [arc_evaluation x w hx xc] at neg
  have hsq := neg_of_mul_neg_left neg (show 0≤1+(arcParameter x)^2 by positivity)
  nlinarith
end Erdos1082Second
end
end

section
/- Each vertex of a diameter graph has at most two neighbors that are not leaves. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

theorem exposed_neighbors (A V:Finset ℝ²) (av:A⊆V) (M:ℝ) (hM:0<M) (bound:∀x∈V,∀y∈A,dist x y≤M) (a:ℝ²) :
    (A.filter fun x => dist a x=M ∧ ∃w∈V,w≠a ∧ dist w x=M).card≤2 := by
  classical
  let S := A.filter fun x => dist a x=M ∧ ∃w∈V,w≠a ∧ dist w x=M
  change S.card≤2
  rcases S.eq_empty_or_nonempty with hS|hS
  · simp [hS]
  obtain ⟨b,hb⟩ := hS
  have prop (x) (h:x∈S) : x∈A ∧ dist a x=M ∧ ∃w∈V,w≠a ∧ dist w x=M := Finset.mem_filter.mp h
  obtain ⟨hbA,ab,_⟩ := prop b hb
  let E := Complex.orthonormalBasisOneI.repr.symm
  let dir := E (b-a)
  have normd : ‖dir‖=M := by dsimp [dir]; rw [E.norm_map,←dist_eq_norm,dist_comm,ab]
  have nz : dir≠0 := by intro h; rw [h,norm_zero] at normd; linarith
  let F (x:ℝ²) := E (x-a)/dir
  have hd (x y:ℝ²) : dist (F x) (F y)=dist x y/M := by
    rw [dist_eq_norm]; dsimp only [F]; rw [←sub_div,←map_sub,norm_div,E.norm_map,
      show (x-a)-(y-a)=x-y by abel,←dist_eq_norm,normd]
  have inj : Function.Injective F := by
    intro x y e; have h := hd x y; rw [e,dist_self] at h
    exact dist_eq_zero.mp ((div_eq_zero_iff.mp h.symm).resolve_right hM.ne')
  have fa : F a=0 := by simp [F]
  have fb : F b=1 := div_self nz
  have distle (x) (hx:x∈V) (y) (hy:y∈A) : ‖F x-F y‖≤1 := by
    rw [←dist_eq_norm,hd]; exact (div_le_one hM).mpr (bound _ hx _ hy)
  have re (x) (hx:x∈V) : 0≤(F x).re := by
    have h := distle x hx b hbA
    rw [fb] at h
    have hh := Complex.sq_norm (F x-1)
    rw [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero] at hh
    nlinarith [norm_nonneg (F x-1),sq_nonneg (F x).re,sq_nonneg (F x).im]
  have unit (x) (hx:x∈S) : ‖F x‖=1 := by
    have d := hd x a
    rw [fa,dist_zero_right,dist_comm x a,(prop x hx).2.1,div_self hM.ne'] at d
    exact d
  let T (x:ℝ²) := arcParameter (F x)
  have ti {x y:ℝ²} (hx:x∈S) (hy:y∈S) (e:T x=T y) : x=y :=
    inj (arc_parameter_inj (unit x hx) (unit y hy) (re _ (av (prop _ hx).1)) (re _ (av (prop _ hy).1)) e)
  obtain ⟨l,hl,minl⟩ := Finset.exists_min_image S T ⟨b,hb⟩
  obtain ⟨r,hr,maxr⟩ := Finset.exists_max_image S T ⟨b,hb⟩
  have subset : S ⊆ {l,r} := by
    intro x hx
    by_contra! hn
    have xl : x≠l := fun e => hn (by simp [e])
    have xr : x≠r := fun e => hn (by simp [e])
    obtain ⟨xA,_,w,hw,wa,wx⟩ := prop x hx
    have strict := arc_middle (F l) (F x) (F r) (F w) (unit _ hl) (unit _ hx) (unit _ hr)
      (re _ (av (prop _ hl).1)) (re _ (av xA)) (re _ (av (prop _ hr).1)) (re _ hw) (fun e => wa (inj (e.trans fa.symm)))
      (lt_of_le_of_ne (minl _ hx) (fun e => xl (ti hx hl e.symm)))
      (lt_of_le_of_ne (maxr _ hx) (fun e => xr (ti hx hr e)))
      (distle _ hw _ (prop _ hl).1) (distle _ hw _ (prop _ hr).1)
    rw [←dist_eq_norm,hd,wx,div_self hM.ne'] at strict
    exact strict.false
  exact (Finset.card_le_card subset).trans Finset.card_le_two
end Erdos1082Second
end
end

section
/- Counting incidences of finite families with limited pairwise overlaps. -/
open Classical
noncomputable section
namespace Erdos1082Second

lemma family_overlap {α β:Type*} [DecidableEq α] [DecidableEq β] (F:β→Finset α) (P:Finset β) (C:ℕ)
    (hOverlap:∀i∈P,∀j∈P,i≠j → ((F i)∩(F j)).card≤C) :
    (∑ i∈P,(F i).card) ≤ (P.biUnion F).card+P.card.choose 2*C := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    have sub : P⊆insert a P := Finset.subset_insert ..
    have hi:=ih (fun i hi j hj => hOverlap i (sub hi) j (sub hj))
    have ovsub : F a ∩ P.biUnion F ⊆ P.biUnion (fun b => F a ∩ F b) := by
      intro x hx
      obtain ⟨hxa,hu⟩ := Finset.mem_inter.mp hx
      obtain ⟨i,hi,h⟩ := Finset.mem_biUnion.mp hu
      exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_inter.mpr ⟨hxa,h⟩⟩
    have inter : (F a ∩ P.biUnion F).card≤P.card*C := by
      calc
        _ ≤ _ := Finset.card_le_card ovsub
        _ ≤ ∑i∈P,(F a ∩ F i).card := Finset.card_biUnion_le
        _ ≤ ∑_i∈P,C := Finset.sum_le_sum fun i hi => hOverlap a (Finset.mem_insert_self ..) i (sub hi) (fun e => ha (e ▸ hi))
        _ = _ := by simp
    have inc := Finset.card_union_add_card_inter (F a) (P.biUnion F)
    rw [Finset.sum_insert ha,Finset.biUnion_insert,Finset.card_insert_of_notMem ha,Nat.choose_succ_succ,Nat.choose_one_right,add_mul]
    change _ ≤ (F a ∪ P.biUnion F).card + (P.card*C + P.card.choose 2*C)
    omega

lemma family_bound {α β:Type*} [DecidableEq α] [DecidableEq β] (F:β→Finset α)
    (P:Finset β) (B:Finset α) (C:ℕ) (sub:∀i∈P,F i⊆B)
    (hOverlap:∀i∈P,∀j∈P,i≠j → ((F i)∩(F j)).card≤C) :
    (∑i∈P,(F i).card)≤B.card+P.card.choose 2*C := by
  apply (family_overlap F P C hOverlap).trans
  exact Nat.add_le_add_right (Finset.card_le_card (Finset.biUnion_subset.mpr sub)) _
end Erdos1082Second
end
end

section
/- At most two edges per exceptional center can end at a point with another neighbor. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second
theorem exposed_count (A P S:Finset ℝ²) (pa:P⊆A) (sa:S⊆A) (d:ℝ) (hd:0<d) (dis:Disjoint P S)
    (bound:∀x∈A,∀y∈S,dist x y≤d) :
    (S.offDiag.filter fun e => dist e.1 e.2=d).card+
      2*((P×ˢS).filter fun e => dist e.1 e.2=d).card ≤ 2*(S.card+2*P.card) := by
  classical
  let U:=S.filter fun x => ∃y∈S,dist y x=d
  let D:=S\U
  have us:U⊆S := Finset.filter_subset _ _
  have du:D.card+U.card=S.card := Finset.card_sdiff_add_card_eq_card us
  let E:=(S.offDiag.filter fun e => dist e.1 e.2=d)
  have en:E.card≤2*U.card := by
    have eq : E⊆U.offDiag.filter fun e => dist e.1 e.2=d := by
      rintro ⟨x,y⟩ he
      obtain ⟨h,k⟩:=Finset.mem_filter.mp he
      obtain ⟨xs,ys,hn⟩:=Finset.mem_offDiag.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_filter.mpr ⟨xs,y,ys,(dist_comm _ _).trans k⟩,Finset.mem_filter.mpr ⟨ys,x,xs,k⟩,hn⟩,k⟩
    exact (Finset.card_le_card eq).trans (diameter_count d hd U (fun x hx y hy => bound x (sa (us hx)) y (us hy)))
  let W (a x:ℝ²) := ∃w∈A,w≠a ∧ dist w x=d
  let F (a:ℝ²) := S.filter fun x => dist a x=d ∧ ¬W a x
  let G (a:ℝ²) := S.filter fun x => dist a x=d ∧ W a x
  have only (a) (ha:a∈P) : F a⊆D := by
    intro x hx
    obtain ⟨xs,_,no⟩:=Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨xs,?_⟩
    intro h
    obtain ⟨_,w,ws,wx⟩:=Finset.mem_filter.mp h
    exact no ⟨w,sa ws,fun e => Finset.disjoint_left.mp dis ha (e ▸ ws),wx⟩
  have none (a) (ha:a∈P) (b) (hb:b∈P) (ab:a≠b) : (F a∩F b).card≤0 := by
    rw [Nat.le_zero,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x h
    obtain ⟨h1,h2⟩:=Finset.mem_inter.mp h
    exact (Finset.mem_filter.mp h1).2.2 ⟨b,pa hb,ab.symm,(Finset.mem_filter.mp h2).2.1⟩
  have two (a) (_:a∈P) : (G a).card≤2 := exposed_neighbors S A sa d hd bound a
  have fsum:=family_bound F P D 0 only none
  have gsum : (∑i∈P,(G i).card)≤P.card*2 := (Finset.sum_le_sum fun i hi => two i hi).trans_eq (by simp)
  let T:=(P×ˢS).filter fun e => dist e.1 e.2=d
  have tc : T.card = ∑i∈P,((F i).card+(G i).card) := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=P) (fun e he => (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)]
    apply Finset.sum_congr rfl
    intro i hi
    have fbij : (T.filter fun e => e.1=i).card=(S.filter fun x => dist i x=d).card := by
      apply Finset.card_bij (fun e _ => e.2)
      · rintro ⟨u,v⟩ he
        obtain ⟨ee,rfl⟩:=Finset.mem_filter.mp he
        obtain ⟨uv,dd⟩:=Finset.mem_filter.mp ee
        exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp uv).2,dd⟩
      · rintro ⟨u,v⟩ he ⟨x,y⟩ hf h
        exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) h
      · intro y hy
        obtain ⟨ys,iy⟩:=Finset.mem_filter.mp hy
        exact ⟨(i,y),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi,ys⟩,iy⟩,rfl⟩,rfl⟩
    rw [fbij]
    have disj:Disjoint (F i) (G i) := by
      apply Finset.disjoint_left.mpr; intro x xf xg
      exact (Finset.mem_filter.mp xf).2.2 (Finset.mem_filter.mp xg).2.2
    rw [←Finset.card_union_of_disjoint disj]
    congr 1
    ext x
    by_cases w:W i x <;> simp [F,G,w]
  rw [Finset.sum_add_distrib] at tc
  change E.card+2*T.card≤_
  simp only [mul_zero,add_zero] at fsum
  omega
end Erdos1082Second
end
end

section
/- The sharp energy inequality for alternating steps around a closed five-cycle. -/
open scoped BigOperators
noncomputable section
namespace Erdos1082Second

def nextPair (v:Fin 5→ℝ) (i:Fin 5) := v i+v (i+1)
def signless (v:Fin 5→ℝ) (i:Fin 5) := 2*v i+v (i-1)+v (i+1)
def squareSum (v:Fin 5→ℝ) := ∑ i,v i^2

lemma dot_signless (v:Fin 5→ℝ) : ∑i,v i*signless v i=squareSum (nextPair v) := by
  simp only [squareSum,signless,nextPair,Fin.sum_univ_succ]
  change v 0*(2*v 0+v 4+v 1)+(v 1*(2*v 1+v 0+v 2)+(v 2*(2*v 2+v 1+v 3)+
    (v 3*(2*v 3+v 2+v 4)+(v 4*(2*v 4+v 3+v 0)+0)))) =
    (v 0+v 1)^2+((v 1+v 2)^2+((v 2+v 3)^2+((v 3+v 4)^2+((v 4+v 0)^2+0))))
  ring

lemma square_signless (v:Fin 5→ℝ) (closed:∑i,v i=0) :
    squareSum (signless v)=3*squareSum (nextPair v)-squareSum v := by
  simp only [squareSum,signless,nextPair,Fin.sum_univ_succ] at closed ⊢
  change v 0+(v 1+(v 2+(v 3+(v 4+0))))=0 at closed
  change (2*v 0+v 4+v 1)^2+((2*v 1+v 0+v 2)^2+((2*v 2+v 1+v 3)^2+
    ((2*v 3+v 2+v 4)^2+((2*v 4+v 3+v 0)^2+0)))) =
    3*((v 0+v 1)^2+((v 1+v 2)^2+((v 2+v 3)^2+((v 3+v 4)^2+((v 4+v 0)^2+0)))))-
    ((v 0)^2+((v 1)^2+((v 2)^2+((v 3)^2+((v 4)^2+0)))))
  linear_combination (v 0+v 1+v 2+v 3+v 4)*closed

lemma gram (v:Fin 5→ℝ) (s t:ℝ) :
    0 ≤ s^2*squareSum (signless v)-2*s*t*squareSum (nextPair v)+t^2*squareSum v := by
  rw [←dot_signless]
  have h : 0 ≤ ∑i,(s*signless v i-t*v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  convert h using 1
  unfold squareSum
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pentagon_energy (X Y:Fin 5→ℝ) (hx:∑i,X i=0) (hy:∑i,Y i=0) :
    (3-Real.sqrt 5)*(squareSum X+squareSum Y)≤2*(squareSum (nextPair X)+squareSum (nextPair Y)) := by
  let A:=squareSum X+squareSum Y
  let E:=squareSum (nextPair X)+squareSum (nextPair Y)
  change (3-Real.sqrt 5)*A≤2*E
  have An : 0≤A := add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (X i)) (Finset.sum_nonneg fun i _ => sq_nonneg (Y i))
  have En : 0≤E := add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rcases An.eq_or_lt with h|h
  · rw [←h,mul_zero]; linarith
  have gx := gram X A E
  have gy := gram Y A E
  rw [square_signless X hx] at gx
  rw [square_signless Y hy] at gy
  have q: 0≤A*(3*A*E-A^2-E^2) := by
    dsimp only [A,E] at *
    nlinarith only [gx,gy]
  have q' := nonneg_of_mul_nonneg_right q h
  have r : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  by_contra! bad
  have upper : 0<(3+Real.sqrt 5)*A-2*E := by nlinarith [mul_pos h (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<5))]
  have neg := mul_neg_of_pos_of_neg upper (sub_neg.mpr bad)
  nlinarith only [neg,q',show (Real.sqrt 5)^2*A^2=5*A^2 by rw [r]]
end Erdos1082Second
end
end

section
/- The next distance after a five-cycle diameter is at least the diameter divided by the golden ratio. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

theorem short_chord (p:Fin 5→ℂ) (M d:ℝ) (side:∀i,dist (p i) (p (i+1))=M)
    (short:∀i,dist (p i) (p (i+1+1))≤d) : (3-Real.sqrt 5)*M^2≤2*d^2 := by
  let X (i:Fin 5) := (p i).re-(p (i+1)).re
  let Y (i:Fin 5) := (p i).im-(p (i+1)).im
  have tel (w:Fin 5→ℝ) : ∑ i,(w i-w (i+1))=0 := by
    simp only [Fin.sum_univ_succ]
    change (w 0-w 1)+((w 1-w 2)+((w 2-w 3)+((w 3-w 4)+((w 4-w 0)+0))))=0
    ring
  have spec := pentagon_energy X Y (tel _) (tel _)
  have length (z w:ℂ) : (z.re-w.re)^2+(z.im-w.im)^2=dist z w^2 := by
    rw [dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]; ring
  have edge (i:Fin 5) : (X i)^2+(Y i)^2=M^2 := (length _ _).trans (by rw [side])
  have skip (i:Fin 5) : (nextPair X i)^2+(nextPair Y i)^2≤d^2 := by
    dsimp only [nextPair,X,Y]
    rw [sub_add_sub_cancel,sub_add_sub_cancel,length]
    exact pow_le_pow_left₀ dist_nonneg (short i) _
  have su: squareSum X+squareSum Y=5*M^2 := by
    unfold squareSum; rw [←Finset.sum_add_distrib]; simp [edge]
  have ku: squareSum (nextPair X)+squareSum (nextPair Y)≤5*d^2 := by
    unfold squareSum; rw [←Finset.sum_add_distrib]
    exact (Finset.sum_le_sum fun i _ => skip i).trans_eq (by simp)
  rw [su] at spec
  nlinarith only [spec,ku]

set_option maxHeartbeats 800000 in
theorem diameter_second_golden (A:Finset ℝ²) (M d:ℝ) (hM:0<M) (bound:∀x y:A,dist x.1 y.1≤M)
    (cyc:∃a b c d e:A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧
      dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (hd:∀u∈(distanceSet A).erase M,u≤d) : (3-Real.sqrt 5)*M^2≤2*d^2 := by
  classical
  obtain ⟨a,b,c,q,e,nd,ab,bc,cq,qe,ea⟩ := cyc
  let z : Fin 5→A := ![a,b,c,q,e]
  let F := Complex.orthonormalBasisOneI.repr.symm
  have iso (x y:ℝ²) : dist (F x) (F y)=dist x y := by rw [dist_eq_norm,←map_sub,F.norm_map,dist_eq_norm]
  have ed (i:Fin 5) : dist (z i).1 (z (i+1)).1=M := by fin_cases i <;> assumption
  have ex := (OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter.diameter_exclusions A M hM bound).1
  have ne (w x y u v : A) (hn : [w,x,y,u,v].Nodup) (wx:dist w.1 x.1=M)
      (xy:dist x.1 y.1=M) (uv:dist u.1 v.1=M) : dist w.1 y.1≤d := by
    have notmax : dist w.1 y.1≠M := fun h => ex ⟨w,x,y,u,v,hn,wx,xy,h,uv⟩
    have wny : w≠y := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at hn
      exact hn.1.2.1
    exact hd _ (Finset.mem_erase.mpr ⟨notmax,Finset.mem_image.mpr ⟨(w.1,y.1),Finset.mem_offDiag.mpr
      ⟨w.2,y.2,Subtype.coe_injective.ne wny⟩,rfl⟩⟩)
  apply short_chord (fun i => F (z i).1) M d (fun i => (iso _ _).trans (ed i))
  intro i
  rw [iso]
  apply ne (z i) (z (i+1)) (z (i+1+1)) (z (i+1+1+1)) (z (i+1+1+1+1)) _ (ed i) (ed (i+1)) (ed (i+1+1+1))
  fin_cases i
  · change [a,b,c,q,e].Nodup
    exact nd
  · change [b,c,q,e,a].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
  · change [c,q,e,a,b].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
  · change [q,e,a,b,c].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
  · change [e,a,b,c,q].Nodup
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd ⊢; grind
end Erdos1082Second
end
end

section
/- The five diameter edges account for all diameter pairs when the multiplicity is five. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

set_option maxHeartbeats 1800000 in
theorem pentagon_support (A:Finset ℝ²) (M:ℝ)
    (cyc:∃a b c d e:A,[a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧
      dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (few:distanceMultiplicity A M≤5) :
    ∃P⊆A,P.card=5 ∧ (∀x∈A,∀y∈A,x≠y → dist x y=M → x∈P ∧ y∈P) ∧
      ∀d:ℝ,d≠M → (P.offDiag.filter fun e => dist e.1 e.2=d).card≤10 := by
  classical
  obtain ⟨a,b,c,q,e,nd,ab,bc,cq,qe,ea⟩ := cyc
  let z : Fin 5→A := [a,b,c,q,e].get
  let v (i:Fin 5) : ℝ² := (z i).1
  have inj : Function.Injective v := Subtype.coe_injective.comp nd.injective_get
  have ed (i:Fin 5) : dist (v i) (v (i+1))=M := by fin_cases i <;> assumption
  let P:=Finset.univ.image v
  let T:=(Finset.univ : Finset (Fin 5×Fin 5)).filter fun p => p.2=p.1+1 ∨ p.1=p.2+1
  let mapE (p:Fin 5×Fin 5) := (v p.1,v p.2)
  let F:=T.image mapE
  let E:=A.offDiag.filter fun p => dist p.1 p.2=M
  have pn:P.card=5 := by rw [Finset.card_image_of_injective _ inj]; decide
  have pa:P⊆A := by intro x h; obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h; exact (z i).2
  have tc:T.card=10 := by decide
  have es : F⊆E := by
    intro p h
    obtain ⟨⟨i,j⟩,hij,rfl⟩:=Finset.mem_image.mp h
    have h: j=i+1 ∨ i=j+1 := (Finset.mem_filter.mp hij).2
    have ij:i≠j := by intro heq; subst j; exact (by decide : ∀k : Fin 5, ¬(k=k+1 ∨ k=k+1)) i h
    refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨(z i).2,(z j).2,inj.ne ij⟩,?_⟩
    rcases h with rfl|rfl
    · exact ed i
    · exact (dist_comm _ _).trans (ed j)
  have fn:F.card=10 := by
    rw [Finset.card_image_of_injective (f:=mapE) _ (fun i j h => Prod.ext (inj (congrArg Prod.fst h)) (inj (congrArg Prod.snd h)))]
    exact tc
  have eq:F=E := by
    apply Finset.eq_of_subset_of_card_le es
    have even:=even_card_offDiag_filter_dist_eq A M
    change Even E.card at even
    obtain ⟨k,hk⟩:=even
    change E.card/2≤5 at few
    omega
  have ep : E⊆P.offDiag := by
    intro p hp
    obtain ⟨⟨i,j⟩,_,hi⟩:=Finset.mem_image.mp (eq ▸ hp)
    obtain rfl:=hi
    exact Finset.mem_offDiag.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i),Finset.mem_image_of_mem _ (Finset.mem_univ j),
      (Finset.mem_offDiag.mp (Finset.mem_filter.mp hp).1).2.2⟩
  refine ⟨P,pa,pn,?_,?_⟩
  · intro x hx y hy xy h
    have hpair : (x,y)∈E := Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx,hy,xy⟩,h⟩
    have t:=Finset.mem_offDiag.mp (ep hpair)
    exact ⟨t.1,t.2.1⟩
  · intro d dm
    let H:=P.offDiag.filter fun e => dist e.1 e.2=d
    have dis:Disjoint E H := by
      apply Finset.disjoint_left.mpr; intro p h1 h2
      exact dm ((Finset.mem_filter.mp h2).2.symm.trans (Finset.mem_filter.mp h1).2)
    have count := Finset.card_le_card (Finset.union_subset ep (Finset.filter_subset (fun e : ℝ²×ℝ² => dist e.1 e.2=d) P.offDiag))
    rw [Finset.card_union_of_disjoint dis,Finset.offDiag_card,pn,←eq,fn] at count
    change H.card≤10
    omega
end Erdos1082Second
end
end

section
/- The multiplicity of the second-largest distance in a five-edge diameter pentagon. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma count_partition (A P S:Finset ℝ²) (cover:∀x∈A,x∈P ∨ x∈S) (d:ℝ) :
    (A.offDiag.filter fun e => dist e.1 e.2=d).card ≤
    (P.offDiag.filter fun e => dist e.1 e.2=d).card +
    (S.offDiag.filter fun e => dist e.1 e.2=d).card +2*((P×ˢS).filter fun e => dist e.1 e.2=d).card := by
  classical
  let X:=P.offDiag.filter fun e => dist e.1 e.2=d
  let Y:=S.offDiag.filter fun e => dist e.1 e.2=d
  let F:=(P×ˢS).filter fun e => dist e.1 e.2=d
  have sub : (A.offDiag.filter fun e => dist e.1 e.2=d)⊆(X∪Y) ∪ (F∪F.image Prod.swap) := by
    rintro ⟨x,y⟩ h
    obtain ⟨hxy,dd⟩:=Finset.mem_filter.mp h
    obtain ⟨ha,hb,ne⟩:=Finset.mem_offDiag.mp hxy
    rcases cover x ha with xp|xs <;> rcases cover y hb with yp|ys
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨xp,yp,ne⟩,dd⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨xp,ys⟩,dd⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(y,x),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨yp,xs⟩,(dist_comm _ _).trans dd⟩,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨xs,ys,ne⟩,dd⟩))
  have hh:=(Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have h1:=Finset.card_union_le X Y
  have h2:=Finset.card_union_le F (F.image Prod.swap)
  have h3:(F.image Prod.swap).card≤F.card:=Finset.card_image_le
  change _≤X.card+Y.card+2*F.card
  omega

theorem pentagon_second_bounds (A:Finset ℝ²) (M d:ℝ) (hM:0<M) (hD:d∈(distanceSet A).erase M)
    (bound:∀x y:A,dist x.1 y.1≤M)
    (cyc:∃a b c d e:A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧
      dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (few:distanceMultiplicity A M≤5) (second:∀u∈(distanceSet A).erase M,u≤d) :
    (3-Real.sqrt 5)*M^2≤2*d^2 ∧ distanceMultiplicity A d≤A.card+10 := by
  classical
  have golden:=diameter_second_golden A M d hM bound cyc second
  refine ⟨golden,?_⟩
  obtain ⟨P,pa,pn,endpoint,inside⟩ := pentagon_support A M cyc few
  let S:=A\P
  have sp:S⊆A := Finset.sdiff_subset
  have ds:Disjoint P S := Finset.disjoint_left.mpr fun x xp xs => (Finset.mem_sdiff.mp xs).2 xp
  have total:S.card+P.card=A.card:=Finset.card_sdiff_add_card_eq_card pa
  have pd:0<d := by
    obtain ⟨⟨x,y⟩,h,e⟩:=Finset.mem_image.mp (Finset.mem_erase.mp hD).2
    exact e ▸ dist_pos.mpr (Finset.mem_offDiag.mp h).2.2
  have lower (x) (hx:x∈A) (y) (hy:y∈S) : dist x y≤d := by
    by_cases eq:x=y
    · simpa [eq] using pd.le
    have ne : dist x y≠M := fun ee => (Finset.mem_sdiff.mp hy).2 (endpoint x hx y (sp hy) eq ee).2
    exact second _ (Finset.mem_erase.mpr ⟨ne,Finset.mem_image.mpr ⟨(x,y),Finset.mem_offDiag.mpr ⟨hx,sp hy,eq⟩,rfl⟩⟩)
  have whole:=count_partition A P S (fun x hx => by by_cases xp:x∈P; exact Or.inl xp; exact Or.inr (Finset.mem_sdiff.mpr ⟨hx,xp⟩)) d
  have mix:=exposed_count A P S pa sp d pd ds lower
  have int:=inside d (Finset.mem_erase.mp hD).1
  rw [pn] at mix total
  norm_num [Nat.choose] at mix
  unfold distanceMultiplicity
  omega
end Erdos1082Second
end
end

section
/- Exact Gram determinant identities for three equal short chords of an equidiagonal pentagon. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

def chordTable (w:Fin 5→ℝ) (i j:Fin 5) := if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j
def dotEntry (w:Fin 5→ℝ) (i j:Fin 5) := chordTable w 0 i+chordTable w 0 j-chordTable w i j
def detThree (p q r s t u v w z:ℝ) := p*(t*z-u*w)-q*(s*z-u*v)+r*(s*w-t*v)
def minorZero (w:Fin 5→ℝ) := ∀i j k l m n:Fin 5,detThree
  (dotEntry w i l) (dotEntry w i m) (dotEntry w i n)
  (dotEntry w j l) (dotEntry w j m) (dotEntry w j n)
  (dotEntry w k l) (dotEntry w k m) (dotEntry w k n)=0

lemma plane_minors (p:Fin 5→ℝ²) (s:ℝ) (w:Fin 5→ℝ)
    (table:∀i j,chordTable w i j=s*dist (p i) (p j)^2) : minorZero w := by
  let coord (a b:ℝ²) := (a 0-b 0)^2+(a 1-b 1)^2
  have ds (a b:ℝ²) : dist a b^2=coord a b := by
    rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]; simp [coord,Real.dist_eq]
  let x (i:Fin 5) := p i 0-p 0 0
  let y (i:Fin 5) := p i 1-p 0 1
  have entry (i j:Fin 5) : dotEntry w i j=2*s*(x i*x j+y i*y j) := by
    simp only [dotEntry,table,ds,coord,x,y]; ring
  intro i j k l m n
  simp only [detThree,entry]; ring

set_option maxHeartbeats 500000 in
lemma three_chords_0 (a b c:ℝ) (h:minorZero ![a,a,a,b,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (b+1-a) (b+a-1) (b+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (b+1-a) (b+b-0) (b+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (1+1-c) (1+b-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (1+a-a) (1+b-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (b+1-a) (b+b-0) (b+1-1) (1+1-c) (1+b-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-9*a^3/8-a^2*b/4+143*a^2/32+19*a*b/8+57*a/128-19*b^2*c/8+5*b*c/32-271*b/64-19*c^3/8+195*c^2/32-281*c/128-4841/128)*g1+(9*a^3/4+a^2*b/2-143*a^2/16-19*a*b/4-57*a/64+19*b^2*c/4-5*b*c/16+271*b/32+19*c^3/4-309*c^2/16+1907*c/64+1741/128)*g2+(-9*a^3/8-a^2*b/4+143*a^2/32+19*a*b/8+57*a/128-19*b^2*c/8+5*b*c/32-271*b/64-19*c^3/8+271*c^2/32-1365*c/128-1097/64)*g3+(17*a^3/8+a^2*b/2+a^2*c/4-335*a^2/32-99*a*b/16-23*a*c/16+1671*a/128+19*b^2*c/8-5*b*c/32+63*b/4+19*c/16-603/128)*g4+(-17*a^3/4-a^2*b-a^2*c/2+263*a^2/16+57*a*b/8+19*a*c/8-527*a/64-19*b^2*c/4-19*b^2/4+5*b*c/16-233*b/16+19*c^2/8-195*c/32+777/128)*g5+(33*a^3/8+a^2*b+3*a^2*c/4-503*a^2/32-95*a*b/16-57*a*c/16+1695*a/128+19*b^2*c/8+19*b^2/8-5*b*c/32+107*b/8-19*c^3/4+347*c^2/16-3417*c/64+3889/128)*g6+(17*a^3/8+a^2*b/2+a^2*c/4-207*a^2/32-19*a*b/16-19*a*c/16-329*a/128+19*b^2*c/8+19*b^2/8-5*b*c/32+19*b/16+19*c^2/8-247*c/16+4233/128)*g7+(-25*a^3/8-3*a^2*b/4-a^2*c/2+383*a^2/32+19*a*b/4+19*a*c/8-1111*a/128-19*b^2*c/8+5*b*c/32-661*b/64+19*c^3/8-347*c^2/32+4233*c/128-2501/128)*g8+(a^3+a^2*b/4+a^2*c/4-15*a^2/4-19*a*b/16-19*a*c/16+73*a/16+195*b/64-19*c^3/8+347*c^2/32-3341*c/128+1477/128)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_1 (a b c:ℝ) (h:minorZero ![a,a,b,a,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-a) (a+1-1) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (a+1-a) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (1+1-c) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (1+a-b) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-b) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  linear_combination (-4*a^2*c+6*a^2-11*a*c+33*a/2-45*c+135/2)*g0+(8*a^2*c-12*a^2+22*a*c-33*a+90*c-225)*g1+(-4*a^3-8*a^2*c-3*a^2-22*a*c-23*a-90*c+180)*g2+(-90)*g3+(90)*g4+(8*a^3+30*a^2+112*a-90)*g5+(180)*g6+(-8*a^3-22*a^2-82*a+112)*g7+(-90)*g8

set_option maxHeartbeats 500000 in
lemma three_chords_2 (a b c:ℝ) (h:minorZero ![a,a,b,c,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+c-a) (a+1-1) (a+a-0) (a+c-1) (c+1-a) (c+a-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (c+1-a) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (1+1-a) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g7 g8 g9
  linear_combination (a^3+a^2*b/4+a^2*c/4-15*a^2/4-21*a*b/16-21*a*c/16+79*a/16+255*b/64+17*c^2/8-191*c/64+1441/128)*g0+(-7*a^3/8-a^2*b/4-a^2*c/4+95*a^2/32+a*b/4+21*a*c/16-1109*a/128+17*b^2*c/8+15*b*c/32-187*b/64-17*c^2/4-311*c/64-55/8)*g1+(-17*a^3/8-a^2*b/2-a^2*c/2+265*a^2/32+59*a*b/16+21*a*c/8-787*a/128-17*b^2*c/8-17*b^2/8-15*b*c/32-289*b/32+17*c^2/8-189*c/32+247/16)*g2+(9*a^3/8+a^2*b/4+a^2*c/4-145*a^2/32-19*a*b/8-21*a*c/16+155*a/128+17*b^2*c/8+15*b*c/32+323*b/64-693*c/64+1001/64)*g3+(-a^3/8+25*a^2/32+17*a*b/16+477*a/128-17*b^2*c/8-15*b*c/32-17*b/16+17*c^2/8+251*c/32-561/128)*g4+(17*a^3/8+a^2*b/2+a^2*c/2-265*a^2/32-59*a*b/16-21*a*c/8+787*a/128+17*b^2*c/8+17*b^2/8+15*b*c/32+289*b/32-17*c^2/8+189*c/32-247/16)*g5+(-a^3-a^2*b/4-a^2*c/4+3*a^2/2-21*a*b/16+13*a*c/16+33*a/8-17*b^2/8+291*b/64-19*c/64-21/8)*g7+(a^3+a^2*b/4+a^2*c/4-15*a^2/4-21*a*b/16-21*a*c/16+79*a/16-17*b^2/8+255*b/64+17*c^2/8-561*c/64+459/64)*g8+(7*a^2/4+17*a*b/8-97*a/16+17*b^2/8-155*b/32-17*c^2/8+223*c/32-2585/128)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_3 (a b c:ℝ) (h:minorZero ![a,b,a,a,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (1+a-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-b) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-35*b*c+105*b/2+495*c/4-1485/8)*g1+(32*b*c-105*b-219*c+669)*g2+(-16*b*c+105*b/2+219*c/2-669/2)*g3+(-8*a^3-10*a^2+22*a*b*c+24*a*b+219*a*c/2-2451*a/4+24*b^2-11*b*c-453*b/2-105*c/4+5311/8)*g4+(8*a^3+14*a^2-22*a*b*c-24*a*b-219*a*c/2+2479*a/4-32*b^2+267*b-949/2)*g5+(-4*a^3-7*a^2+11*a*b*c+12*a*b+219*a*c/4-2479*a/8+16*b^2-437*b/2-146*c+1595/2)*g6+(-57*b/2-57*c/2+351/2)*g7+(297*b/2+349*c/2-1719/2)*g8+(-60*b-73*c+342)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_4 (a b c:ℝ) (h:minorZero ![a,b,a,c,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (c+1-b) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (c+1-b) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (1+1-a) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (1+a-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (c+1-b) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (90)*g1+(-180)*g2+(90)*g3+(-4*a^2*c+6*a^2-11*a*c+33*a/2-45*c-45/2)*g4+(8*a^2*c-12*a^2+22*a*c-33*a+90*c+45)*g5+(-4*a^3-8*a^2*c-3*a^2-22*a*c-23*a-90*c)*g6+(-90)*g7+(8*a^3+30*a^2+112*a+180)*g8+(-8*a^3-22*a^2-82*a+22)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_5 (a b c:ℝ) (h:minorZero ![a,b,c,a,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-b) (a+1-1) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (1+1-a) (1+a-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (1+a-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-b) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-245/32)*g0+(-9*a^3/8-a^2*b/4-5*a^2*c/8+39*a^2/16+5*a*b/8+25*a*c/16-113*a/32-35*b/16+35*c/16+245/16)*g1+(-245/16)*g2+(-a^3-a^2*b/4-a^2*c/4+15*a^2/4+5*a*b/8+5*a*c/8-23*a/8-35*b/16-35*c/16+175/8)*g3+(17*a^3/8+a^2*b/2+7*a^2*c/8-71*a^2/16-5*a*b/4-35*a*c/16+181*a/32+35*b/8-105/16)*g4+(-2*a^3-a^2*b/2-a^2*c/2+4*a^2+5*a*b/4+5*a*c/4-17*a/4-35*b/8-35*c/8+105/8)*g5+(-245/16)*g6+(-a^3/8-3*a^2*c/8+7*a^2/16+15*a*c/16-45*a/32+35*c/8-105/16)*g7+(9*a^3/8+a^2*b/4+5*a^2*c/8-39*a^2/16-5*a*b/8-25*a*c/16+113*a/32+35*b/16-35*c/16+245/16)*g8+(-9*a^2/4-7*a*b/8-7*a*c/8+39*a/8+35*b/16+35*c/16-471/32)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_6 (a b c:ℝ) (h:minorZero ![b,a,a,a,c]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (1+1-c) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  linear_combination (a^3+a^2*b/4+a^2*c/4-2*a^2+3*a*b/4+a*c-9*a/8-3*b/32+63*c/64-13/64)*g0+(-25*a^3/8-3*a^2*b/4-a^2*c/2+41*a^2/8-9*a*b/4-2*a*c+255*a/64+9*b/32-63*c/64-121/64)*g1+(33*a^3/8+a^2*b+3*a^2*c/4-57*a^2/8+3*a*b+3*a*c-327*a/64-5*b/2+63*c/32+57/64)*g2+(-9*a^3/8-a^2*b/4+9*a^2/8-3*a*b/4+111*a/64+3*b/32+63*c/64+19/32)*g3+(17*a^3/8+a^2*b/2+a^2*c/4-25*a^2/8+3*a*b/2+a*c-183*a/64-3*b/16-51/64)*g4+(-17*a^3/4-a^2*b-a^2*c/2+11*a^2/4-17*a*b/4-2*a*c+231*a/32+3*b/8-63/64)*g5+(9*a^3/4+a^2*b/2-9*a^2/4+3*a*b/2-111*a/32-3*b/16-63*c/32+109/64)*g6+(17*a^3/8+a^2*b/2+a^2*c/4-29*a^2/8+3*a*b+3*a*c/4-167*a/64+5*b^2/8-73*b/16-c+263/64)*g7+(-9*a^3/8-a^2*b/4+9*a^2/8-3*a*b/4+111*a/64+3*b/32+63*c/64+223/64)*g8

set_option maxHeartbeats 500000 in
lemma three_chords_7 (a b c:ℝ) (h:minorZero ![b,a,a,c,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+c-a) (b+1-1) (b+b-0) (b+c-1) (c+1-a) (c+b-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (c+1-a) (c+b-1) (c+1-1)=0 at g1
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (b+1-1) (b+c-1) (b+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (1+b-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-4*a^2*c/3+2*a^2+7*a*c/9-7*a/6+5*c/27-10/27)*g0+(4*a^3/3+8*a^2*c/3-31*a^2/9-14*a*c/9+23*a/18-10*c/27+10/27)*g1+(4*a^3/3+5*a^2/9-19*a/18-5/27)*g3+(-4*a^3/3-4*a^2*c/3+13*a^2/9+7*a*c/9-a/9+5*c/27)*g4+(-5/54)*g5+(-5/27)*g6+(-4*a^3/3+4*a^2*c/3-11*a^2/9-7*a*c/9+25*a/9-5*c/27-16/27)*g7+(4*a^3/3-8*a^2*c/3+41*a^2/9+14*a*c/9-61*a/18+10*c/27-5/9)*g8+(4*a^2*c/3-2*a^2-7*a*c/9+7*a/6-5*c/27+5/27)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_8 (a b c:ℝ) (h:minorZero ![b,a,c,a,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (1+1-a) (1+b-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (1+b-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (a+1-a) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-8*a^3-48*a^2*b^2+2*a^2-1132*a*b^2+842*a*b*c+597*a*b+249*a*c+719*a/2+696*b^2-106*b*c-1185*b-57*c-881/2)*g0+(8*a^3+48*a^2*b^2-2*a^2+1180*a*b^2-842*a*b*c-597*a*b-249*a*c-719*a/2+476*b^2-429*b*c+351*b/2-225*c/2-65/4)*g1+(-4*a^3-24*a^2*b^2+a^2-590*a*b^2+421*a*b*c+597*a*b/2+249*a*c/2+719*a/4-190*b^2+213*b*c-2033*b/2+153*c/2-1415/4)*g2+(291*b*c-873*b/2+207*c/2-621/4)*g3+(-24*a*b^2-590*b^2+122*b*c+675*b+33*c+297)*g4+(32*a*b^2+772*b^2-388*b*c+301*b-138*c+87/2)*g5+(-16*a*b^2-460*b^2+244*b*c+342*b+66*c+198)*g6+(-8*a*b^2-206*b^2+194*b*c-257*b+69*c-69)*g7+(8*a*b^2+222*b^2-122*b*c-558*b-33*c-441/2)*g8+(8*b^2+96*b+18)*g9

set_option maxHeartbeats 500000 in
lemma three_chords_9 (a b c:ℝ) (h:minorZero ![b,c,a,a,a]) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-c) (b+1-1) (b+b-0) (b+a-1) (a+1-c) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (a+1-c) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (a+1-c) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (a+1-c) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  linear_combination (-a^2/2+21*a*b/8+21*a*c/8-219*a/8+21*b^2/8+21*b*c/4-125*b/8-63*c^2/8+41*c/8+1223/16)*g0+(a^3+a^2*b/4+a^2*c/4+3*a^2/4+a*b/4+a*c/4+109*a/4-63*b/8-21*c^2/2+315*c/8-559/8)*g1+(-9*a^2/2-75*a/2-21*c/2+104)*g2+(-9*a^3/8-a^2*b/4+a^2*c/4+45*a^2/8-a*b/4+a*c/4+913*a/16-21*b^2*c/8-63*b*c^2/8+125*b*c/8+63*b/8+65*c/8-112)*g3+(-a^3-a^2*b/4-a^2*c/4+3*a^2/2-a*b/4-a*c/4-17*a/2+63*b/8+21*c^2/2-231*c/8+10)*g4+(-a^3/8+a^2*c/2+15*a^2/8+a*c/2+749*a/16-21*b^2*c/8-63*b*c^2/8+125*b*c/8-21*c^2/2+53*c/2-497/8)*g5+(a^3/8-a^2*c/2-15*a^2/8-a*c/2-749*a/16+21*b^2*c/8+63*b*c^2/8-125*b*c/8+21*c^2/2-53*c/2+497/8)*g6+(17*a^3/8+a^2*b/2-57*a^2/8+a*b/2-777*a/16+21*b^2*c/8+63*b*c^2/8-125*b*c/8-63*b/4+857/16)*g7+(-25*a^3/8-3*a^2*b/4-a^2*c/4+105*a^2/8-3*a*b/4-a*c/4+1241*a/16-21*b^2*c/8-63*b*c^2/8+125*b*c/8+189*b/8+19*c/8-793/8)*g8+(a^3+a^2*b/4+a^2*c/4-6*a^2+a*b/4+a*c/4-29*a-63*b/8-19*c/8+729/16)*g9

end Erdos1082Second
end
end

section
/- If three pentagon short chords reach the second distance, then their ratio is forced. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma three_equal_value (w:Fin 5→ℝ) (h:minorZero w) (a:ℝ)
    (count:3≤(Finset.univ.filter fun i => w i=a).card) : (a-1)*(a+1)*(4*a-1)*(a^2-3*a+1)=0 := by
  classical
  obtain ⟨B,sub,n⟩:=Finset.exists_subset_card_eq count
  have e (i:Fin 5) (hi:i∈B) : w i=a := (Finset.mem_filter.mp (sub hi)).2
  have cases : ∀S:Finset (Fin 5), S.card=3 → (0∈S ∧ 1∈S ∧ 2∈S) ∨ (0∈S ∧ 1∈S ∧ 3∈S) ∨ (0∈S ∧ 1∈S ∧ 4∈S) ∨ (0∈S ∧ 2∈S ∧ 3∈S) ∨ (0∈S ∧ 2∈S ∧ 4∈S) ∨ (0∈S ∧ 3∈S ∧ 4∈S) ∨ (1∈S ∧ 2∈S ∧ 3∈S) ∨ (1∈S ∧ 2∈S ∧ 4∈S) ∨ (1∈S ∧ 3∈S ∧ 4∈S) ∨ (2∈S ∧ 3∈S ∧ 4∈S) := by decide
  rcases cases B n with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,a,w 3,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_0 a (w 3) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_1 a (w 2) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_2 a (w 2) (w 3) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_3 a (w 1) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_4 a (w 1) (w 3) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_5 a (w 1) (w 2) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_6 a (w 0) (w 4) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_7 a (w 0) (w 3) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_8 a (w 0) (w 2) (eq ▸ h)
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,w 1,a,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    exact three_chords_9 a (w 0) (w 1) (eq ▸ h)

lemma normalized_minor (p:Fin 5→ℝ²) (M:ℝ) (hM:0<M) (unit:∀i,dist (p i) (p (i+1))=M) :
    minorZero (fun i => (M^2)⁻¹*dist (p i) (p (i+2))^2) := by
  apply plane_minors p ((M^2)⁻¹)
  intro i j
  by_cases ij:i=j
  · simp [chordTable,ij]
  by_cases e:j=i+1 ∨ i=j+1
  · have de:dist (p i) (p j)=M := by
      rcases e with rfl|rfl
      · exact unit i
      · exact (dist_comm _ _).trans (unit j)
    simp [chordTable,ij,e,de,hM.ne']
  by_cases e2:j=i+2
  · rw [chordTable,if_neg ij,if_neg e,if_pos e2,e2]
  have e3 : i=j+2 := (by decide : ∀i j:Fin 5,i≠j → ¬(j=i+1 ∨ i=j+1) → j≠i+2 → i=j+2) i j ij e e2
  simp [chordTable,ij,e,e2,←e3,dist_comm (p i) (p j)]

lemma equal_or_below_two (p:Fin 5→ℝ²) (M d:ℝ) (hM:0<M) (hd:0≤d) (dm:d<M)
    (unit:∀i,dist (p i) (p (i+1))=M)
    (strict:(3-Real.sqrt 5)*M^2<2*d^2) :
    (Finset.univ.filter fun i => dist (p i) (p (i+2))=d).card≤2 := by
  classical
  let w (i:Fin 5):=(M^2)⁻¹*dist (p i) (p (i+2))^2
  let a:=(M^2)⁻¹*d^2
  have eq:a*M^2=d^2 := by dsimp [a]; field_simp
  have ap:0≤a := by dsimp [a]; positivity
  have al:a<1 := by
    by_contra! h
    have hh:=mul_le_mul_of_nonneg_right h (sq_nonneg M)
    rw [eq,one_mul] at hh
    nlinarith only [hh,mul_pos (sub_pos.mpr dm) (add_pos_of_pos_of_nonneg hM hd)]
  have lo:3-Real.sqrt 5<2*a := by
    by_contra! h
    have hh:=mul_le_mul_of_nonneg_right h (sq_nonneg M)
    rw [mul_assoc,eq] at hh
    exact strict.not_ge hh
  have rt : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have rootpos:0<Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have p1:a-1≠0 := sub_ne_zero.mpr al.ne
  have p2:a+1≠0 := by linarith
  have p3:4*a-1≠0 := by intro q; nlinarith
  have p4:a^2-3*a+1≠0 := by
    intro q
    have h:=mul_pos (sub_pos.mpr lo) (show 0<(3+Real.sqrt 5)-2*a by linarith)
    nlinarith only [h,q,rt]
  by_contra! bad
  have sub:(Finset.univ.filter fun i => dist (p i) (p (i+2))=d)⊆Finset.univ.filter (fun i => w i=a) := by
    intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [w,a,(Finset.mem_filter.mp hi).2]⟩
  have vv:=three_equal_value w (normalized_minor p M hM unit) a (by have := Finset.card_le_card sub; omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero p1 p2) p3) p4 vv
end Erdos1082Second
end
end

section
/- Away from the regular pentagon ratio at most two of its chords attain the second distance. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma pent_inside_four (A P:Finset ℝ²) (M d:ℝ) (hM:0<M) (hd:0≤d) (dm:d<M) (pn:P.card=5)
    (cyc:∃a b c d e:A,[a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧
      dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (support:∀x∈A,∀y∈A,x≠y → dist x y=M → x∈P ∧ y∈P) (strict:(3-Real.sqrt 5)*M^2<2*d^2) :
    (P.offDiag.filter fun e => dist e.1 e.2=d).card≤4 := by
  classical
  obtain ⟨a,b,c,q,e,nd,ab,bc,cq,qe,ea⟩:=cyc
  let z:Fin 5→A := [a,b,c,q,e].get
  let v (i:Fin 5):ℝ² := (z i).1
  have inj:Function.Injective v := Subtype.coe_injective.comp nd.injective_get
  have Ed (i:Fin 5) : dist (v i) (v (i+1))=M := by fin_cases i <;> assumption
  have sub:Finset.univ.image v ⊆ P := by
    intro x hx; obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    have ne:i≠i+1 := (by decide : ∀k:Fin 5,k≠k+1) i
    exact (support _ (z i).2 _ (z (i+1)).2 (inj.ne ne) (Ed i)).1
  have seteq : Finset.univ.image v=P := Finset.eq_of_subset_of_card_le sub (by rw [Finset.card_image_of_injective _ inj,pn]; decide)
  let T:=Finset.univ.filter fun i:Fin 5 => dist (v i) (v (i+2))=d
  have tc:T.card≤2 := equal_or_below_two v M d hM hd dm Ed strict
  let edge (i:Fin 5) := (v i,v (i+2))
  let F:=T.image edge
  have es : (P.offDiag.filter fun e => dist e.1 e.2=d)⊆F∪F.image Prod.swap := by
    rintro ⟨x,y⟩ he
    obtain ⟨ho,de⟩:=Finset.mem_filter.mp he
    obtain ⟨xp,yp,xy⟩:=Finset.mem_offDiag.mp ho
    rw [←seteq] at xp yp
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp xp
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp yp
    have ne:i≠j := fun e => xy (congrArg v e)
    have dia:¬(j=i+1 ∨ i=j+1) := by
      rintro (rfl|rfl)
      · exact dm.ne (de.symm.trans (Ed i))
      · exact dm.ne (de.symm.trans ((dist_comm _ _).trans (Ed j)))
    rcases (by decide : ∀i j:Fin 5,i≠j → ¬(j=i+1 ∨ i=j+1) → j=i+2 ∨ i=j+2) i j ne dia with rfl|rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,de⟩,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨edge j,Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(dist_comm _ _).trans de⟩,rfl⟩,rfl⟩)
  have cnt:=(Finset.card_le_card es).trans (Finset.card_union_le _ _)
  have f1:F.card≤T.card := Finset.card_image_le
  have f2:(F.image Prod.swap).card≤F.card:=Finset.card_image_le
  omega
end Erdos1082Second
end
end

section
/- Improved multiplicity bound away from the sharp five-cycle ratio. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second
theorem pentagon_strict_second (A:Finset ℝ²) (M d:ℝ) (hM:0<M) (hD:d∈(distanceSet A).erase M)
    (bound:∀x y:A,dist x.1 y.1≤M)
    (cyc:∃a b c d e:A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧
      dist c.1 d.1=M ∧ dist d.1 e.1=M ∧ dist e.1 a.1=M)
    (few:distanceMultiplicity A M≤5) (second:∀u∈(distanceSet A).erase M,u≤d) (strict:(3-Real.sqrt 5)*M^2<2*d^2) :
    distanceMultiplicity A d≤A.card+7 := by
  classical
  obtain ⟨P,pa,pn,endpoint,inside⟩ := pentagon_support A M cyc few
  let S:=A\P
  have sp:S⊆A := Finset.sdiff_subset
  have ds:Disjoint P S := Finset.disjoint_left.mpr fun x xp xs => (Finset.mem_sdiff.mp xs).2 xp
  have total:S.card+P.card=A.card:=Finset.card_sdiff_add_card_eq_card pa
  have pd:0<d := by
    obtain ⟨⟨x,y⟩,h,e⟩:=Finset.mem_image.mp (Finset.mem_erase.mp hD).2
    exact e ▸ dist_pos.mpr (Finset.mem_offDiag.mp h).2.2
  have lower (x) (hx:x∈A) (y) (hy:y∈S) : dist x y≤d := by
    by_cases eq:x=y
    · simpa [eq] using pd.le
    have ne : dist x y≠M := fun ee => (Finset.mem_sdiff.mp hy).2 (endpoint x hx y (sp hy) eq ee).2
    exact second _ (Finset.mem_erase.mpr ⟨ne,Finset.mem_image.mpr ⟨(x,y),Finset.mem_offDiag.mpr ⟨hx,sp hy,eq⟩,rfl⟩⟩)
  have whole:=count_partition A P S (fun x hx => by by_cases xp:x∈P; exact Or.inl xp; exact Or.inr (Finset.mem_sdiff.mpr ⟨hx,xp⟩)) d
  have mix:=exposed_count A P S pa sp d pd ds lower
  have dm:d<M := by
    apply lt_of_le_of_ne _ (Finset.mem_erase.mp hD).1
    obtain ⟨⟨x,y⟩,hp,eq⟩:=Finset.mem_image.mp (Finset.mem_erase.mp hD).2
    exact eq ▸ bound ⟨x,(Finset.mem_offDiag.mp hp).1⟩ ⟨y,(Finset.mem_offDiag.mp hp).2.1⟩
  have int:=pent_inside_four A P M d hM pd.le dm pn cyc endpoint strict
  rw [pn] at mix total
  norm_num [Nat.choose] at mix
  unfold distanceMultiplicity
  omega
end Erdos1082Second
end
end

section
/- A diameter five-cycle is metrically regular as soon as three short chords agree. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

set_option maxHeartbeats 1200000 in
lemma rigid_0 (a b c:ℝ) (h:minorZero ![a,a,a,b,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (b+1-a) (b+a-1) (b+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (b+1-a) (b+b-0) (b+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (a+1-1) (a+b-1) (a+1-a) (1+1-c) (1+b-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (a+a-0) (a+b-1) (a+1-a) (1+a-a) (1+b-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+b-a) (1+1-c) (b+1-a) (b+b-0) (b+1-1) (1+1-c) (1+b-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+b-a) (1+1-c) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+b-1) (a+1-a) (b+a-1) (b+b-0) (b+1-1) (1+a-a) (1+b-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-a^3/4-a^2*b/2+57*a^2/32+33*a*b/16-33*a/32-b^2*c+25*b*c/32-7*b/4-c^3+105*c^2/32-21*c/64-941/64)*g1+(a^3/2+a^2*b-57*a^2/16-33*a*b/8+33*a/16+2*b^2*c-25*b*c/16+7*b/2+2*c^3-153*c^2/16+27*c/2+361/64)*g2+(-a^3/4-a^2*b/2+57*a^2/32+33*a*b/16-33*a/32-b^2*c+25*b*c/32-7*b/4-c^3+137*c^2/32-295*c/64-217/32)*g3+(a^3/4+a^2*b-89*a^2/32-39*a*b/8-3*a*c/16+201*a/32+b^2*c-25*b*c/32+245*b/32+3*c/16-15/4)*g4+(-a^3/2-2*a^2*b+81*a^2/16+29*a*b/4+3*a*c/8-117*a/16-2*b^2*c-2*b^2+25*b*c/16-6*b+c^2-105*c/32+217/64)*g5+(a^3/4+2*a^2*b-129*a^2/32-27*a*b/4-9*a*c/16+285*a/32+b^2*c+b^2-25*b*c/32+11*b/2-2*c^3+169*c^2/16-727*c/32+709/64)*g6+(a^3/4+a^2*b-73*a^2/32-21*a*b/8-3*a*c/16+45*a/32+b^2*c+b^2-25*b*c/32-9*b/32+c^2-13*c/2+903/64)*g7+(-a^3/4-3*a^2*b/2+105*a^2/32+83*a*b/16+3*a*c/8-201*a/32-b^2*c+25*b*c/32-17*b/4+c^3-169*c^2/32+853*c/64-491/64)*g8+(a^2*b/2-3*a^2/4-25*a*b/16-3*a*c/16+21*a/8+5*b/4-c^3+169*c^2/32-711*c/64+141/32)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-7*a^3/8+a^2*b/4-91*a^2/32-17*a*b/8-373*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-119*c^2/32-43*c/128+4485/128)*g1+(7*a^3/4-a^2*b/2+91*a^2/16+17*a*b/4+373*a/64-19*b^2*c/4-71*b*c/16-195*b/32-19*c^3/4+233*c^2/16-1127*c/64-2457/128)*g2+(-7*a^3/8+a^2*b/4-91*a^2/32-17*a*b/8-373*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-195*c^2/32+737*c/128+1157/64)*g3+(-a^3/8-a^2*b/2-a^2*c/4+187*a^2/32+91*a*b/16+19*a*c/16-523*a/128-19*b^2*c/8-71*b*c/32-43*b/4-15*c/16-209/128)*g4+(a^3/4+a^2*b+a^2*c/2-179*a^2/16-49*a*b/8-15*a*c/8-269*a/64+19*b^2*c/4+19*b^2/4+71*b*c/16+157*b/16-19*c^2/8+119*c/32+155/128)*g5+(-17*a^3/8-a^2*b-3*a^2*c/4+355*a^2/32+79*a*b/16+45*a*c/16+61*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-69*b/8+19*c^3/4-271*c^2/16+2789*c/64-4333/128)*g6+(-a^3/8-a^2*b/2-a^2*c/4+123*a^2/32+11*a*b/16+15*a*c/16+901*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-19*b/16-19*c^2/8+247*c/16-3909/128)*g7+(9*a^3/8+3*a^2*b/4+a^2*c/2-267*a^2/32-4*a*b-15*a*c/8-165*a/128+19*b^2*c/8+71*b*c/32+433*b/64-19*c^3/8+271*c^2/32-3909*c/128+3313/128)*g8+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+15*a*b/16+15*a*c/16-13*a/16-119*b/64+19*c^3/8-271*c^2/32+2713*c/128-1585/128)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (9*a^3/8+a^2*b/4-107*a^2/32-17*a*b/8-629*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-119*c^2/32-43*c/128+4549/128)*g1+(-9*a^3/4-a^2*b/2+107*a^2/16+17*a*b/4+629*a/64-19*b^2*c/4-71*b*c/16-195*b/32-19*c^3/4+233*c^2/16-1127*c/64-2585/128)*g2+(9*a^3/8+a^2*b/4-107*a^2/32-17*a*b/8-629*a/128+19*b^2*c/8+71*b*c/32+195*b/64+19*c^3/8-195*c^2/32+737*c/128+1189/64)*g3+(-17*a^3/8-a^2*b/2-a^2*c/4+203*a^2/32+91*a*b/16+19*a*c/16-267*a/128-19*b^2*c/8-71*b*c/32-43*b/4-15*c/16-273/128)*g4+(17*a^3/4+a^2*b+a^2*c/2-195*a^2/16-49*a*b/8-15*a*c/8-525*a/64+19*b^2*c/4+19*b^2/4+71*b*c/16+157*b/16-19*c^2/8+119*c/32+283/128)*g5+(-33*a^3/8-a^2*b-3*a^2*c/4+371*a^2/32+79*a*b/16+45*a*c/16+317*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-69*b/8+19*c^3/4-271*c^2/16+2789*c/64-4397/128)*g6+(-17*a^3/8-a^2*b/2-a^2*c/4+139*a^2/32+11*a*b/16+15*a*c/16+1157*a/128-19*b^2*c/8-19*b^2/8-71*b*c/32-19*b/16-19*c^2/8+247*c/16-3973/128)*g7+(25*a^3/8+3*a^2*b/4+a^2*c/2-283*a^2/32-4*a*b-15*a*c/8-421*a/128+19*b^2*c/8+71*b*c/32+433*b/64-19*c^3/8+271*c^2/32-3909*c/128+3377/128)*g8+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+15*a*b/16+15*a*c/16-13*a/16-119*b/64+19*c^3/8-271*c^2/32+2713*c/128-1585/128)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_1 (a b c:ℝ) (h:minorZero ![a,a,b,a,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-a) (a+1-1) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (a+1-a) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-b) (1+1-c) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-1) (a+a-1) (a+1-b) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-0) (a+a-1) (a+1-b) (1+a-b) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-a) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-b) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^3-2*a^2+3*a/2-1/2)*g0+(-2*a^3+4*a^2-3*a+1)*g1+(2*a^3-2*a^2*c-a^2-8*a*c+15*a-16)*g2+(4*a^2*c-6*a^2+16*a*c-24*a)*g5+(-4*a^2*c+6*a^2+2*a*b-14*a*c+18*a+8*b+8*c-24)*g7
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (2*a^2*b+6*a^2*c-12*a^2-5*a*b/2+25*a*c/2-15*a+b/2+113*c/2-171/2)*g0+(-4*a^2*b-12*a^2*c+24*a^2+5*a*b-25*a*c+30*a-b-113*c+567/2)*g1+(4*a^3+4*a^2*b+12*a^2*c-5*a^2-5*a*b+25*a*c+41*a+b+113*c-455/2)*g2+(225/2)*g3+(-225/2)*g4+(-8*a^3-38*a^2-142*a+113)*g5+(-225)*g6+(8*a^3+28*a^2+209*a/2-281/2)*g7+(225/2)*g8
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (4*a^2*c-6*a^2+15*a*c-45*a/2+56*c-84)*g0+(-8*a^2*c+12*a^2-30*a*c+45*a-112*c+561/2)*g1+(4*a^3+8*a^2*c+7*a^2+30*a*c+26*a+112*c-449/2)*g2+(225/2)*g3+(-225/2)*g4+(-8*a^3-38*a^2-142*a+113)*g5+(-225)*g6+(8*a^3+28*a^2+209*a/2-281/2)*g7+(225/2)*g8
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_2 (a b c:ℝ) (h:minorZero ![a,a,b,c,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+c-a) (a+1-1) (a+a-0) (a+c-1) (c+1-a) (c+a-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (c+1-a) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-b) (1+1-a) (1+a-b) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (a+1-1) (a+c-1) (a+1-b) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-a) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-b) (c+a-1) (c+c-0) (c+1-1) (1+a-b) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^2*b/2-3*a^2/4-25*a*b/16-3*a*c/16+21*a/8+43*b/32+c^2-93*c/32+291/64)*g0+(a^3/4-a^2*b/2-9*a^2/32+17*a*b/16+3*a*c/16-267*a/64+b^2*c-19*b*c/32-27*b/32-2*c^2+71*c/32-71/32)*g1+(-a^3/4-a^2*b+81*a^2/32+29*a*b/8+3*a*c/8-237*a/64-b^2*c-b^2+19*b*c/32-51*b/16+c^2-115*c/32+187/32)*g2+(a^3/4+a^2*b/2-57*a^2/32-33*a*b/16-3*a*c/16+69*a/64+b^2*c-19*b*c/32+59*b/32-115*c/32+55/8)*g3+(-a^3/4+33*a^2/32+a*b/2+99*a/64-b^2*c+19*b*c/32-b/2+c^2+11*c/16-149/64)*g4+(a^3/4+a^2*b-81*a^2/32-29*a*b/8-3*a*c/8+237*a/64+b^2*c+b^2-19*b*c/32+51*b/16-c^2+115*c/32-187/32)*g5+(-a^2*b/2+a^2/2+5*a*b/16+3*a*c/16-b^2+53*b/16-5*c/16-5/2)*g7+(a^2*b/2-3*a^2/4-25*a*b/16-3*a*c/16+21*a/8-b^2+43*b/32+c^2-77*c/16+41/8)*g8+(a^2/4+a*b-9*a/4+b^2-99*b/32-c^2+131*c/32-365/64)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16-171*b/64-17*c^2/8+139*c/64-1525/128)*g0+(23*a^3/8+a^2*b/4+a^2*c/4-83*a^2/32-17*a*c/16+473*a/128-17*b^2*c/8-83*b*c/32+103*b/64+17*c^2/4+467*c/64+59/8)*g1+(a^3/8+a^2*b/2+a^2*c/2-181*a^2/32-51*a*b/16-17*a*c/8-17*a/128+17*b^2*c/8+17*b^2/8+83*b*c/32+205*b/32-17*c^2/8+121*c/32-155/16)*g2+(7*a^3/8-a^2*b/4-a^2*c/4+93*a^2/32+17*a*b/8+17*a*c/16+169*a/128-17*b^2*c/8-83*b*c/32-239*b/64+745*c/64-1053/64)*g3+(-15*a^3/8-5*a^2/32-17*a*b/16-321*a/128+17*b^2*c/8+83*b*c/32+17*b/16-17*c^2/8-303*c/32+581/128)*g4+(-a^3/8-a^2*b/2-a^2*c/2+181*a^2/32+51*a*b/16+17*a*c/8+17*a/128-17*b^2*c/8-17*b^2/8-83*b*c/32-205*b/32+17*c^2/8-121*c/32+155/16)*g5+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+25*a*b/16-9*a*c/16-41*a/8+17*b^2/8-207*b/64-33*c/64+21/8)*g7+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16+17*b^2/8-171*b/64-17*c^2/8+645*c/64-775/64)*g8+(-7*a^2/4-17*a*b/8+69*a/16-17*b^2/8+87*b/32+17*c^2/8-155*c/32+2541/128)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16-171*b/64-17*c^2/8+139*c/64-1525/128)*g0+(7*a^3/8+a^2*b/4+a^2*c/4-67*a^2/32-17*a*c/16+729*a/128-17*b^2*c/8-83*b*c/32+103*b/64+17*c^2/4+467*c/64+55/8)*g1+(17*a^3/8+a^2*b/2+a^2*c/2-197*a^2/32-51*a*b/16-17*a*c/8-273*a/128+17*b^2*c/8+17*b^2/8+83*b*c/32+205*b/32-17*c^2/8+121*c/32-147/16)*g2+(-9*a^3/8-a^2*b/4-a^2*c/4+109*a^2/32+17*a*b/8+17*a*c/16+425*a/128-17*b^2*c/8-83*b*c/32-239*b/64+745*c/64-1085/64)*g3+(a^3/8-21*a^2/32-17*a*b/16-577*a/128+17*b^2*c/8+83*b*c/32+17*b/16-17*c^2/8-303*c/32+645/128)*g4+(-17*a^3/8-a^2*b/2-a^2*c/2+197*a^2/32+51*a*b/16+17*a*c/8+273*a/128-17*b^2*c/8-17*b^2/8-83*b*c/32-205*b/32+17*c^2/8-121*c/32+147/16)*g5+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+25*a*b/16-9*a*c/16-41*a/8+17*b^2/8-207*b/64-33*c/64+21/8)*g7+(-a^3-a^2*b/4-a^2*c/4+11*a^2/4+17*a*b/16+17*a*c/16-19*a/16+17*b^2/8-171*b/64-17*c^2/8+645*c/64-775/64)*g8+(-7*a^2/4-17*a*b/8+69*a/16-17*b^2/8+87*b/32+17*c^2/8-155*c/32+2541/128)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_3 (a b c:ℝ) (h:minorZero ![a,b,a,a,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-c) (a+1-1) (a+a-0) (a+1-a) (1+1-c) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-1) (a+a-1) (a+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-0) (a+a-1) (a+1-a) (1+a-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-c) (a+1-b) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-2*b*c^2+3*b*c-33*c^2/2+291*c/4-72)*g1+(8*b*c^2-6*b*c+30*c^2-162*c+327)*g2+(-4*b*c^2+3*b*c-15*c^2+81*c-327/2)*g3+(-4*a^2*b-24*a^2-12*a*b*c^2+24*a*b*c-24*a*b-9*a*c^2+165*a*c/2-321*a+8*b^2*c-12*b^2+6*b*c^2-3*b*c-30*b-9*c^2/2-153*c/4+324)*g4+(4*a^2*b+24*a^2+12*a*b*c^2-24*a*b*c+26*a*b+9*a*c^2-165*a*c/2+348*a-8*b^2*c+12*b^2-18*b*c+62*b+45*c-225)*g5+(-2*a^2*b-12*a^2-6*a*b*c^2+12*a*b*c-13*a*b-9*a*c^2/2+165*a*c/4-174*a+4*b^2*c-6*b^2-17*b*c-31*b-132*c+783/2)*g6+(-15*a+9*b*c-9*b+9*c^2-48*c+105)*g7+(15*a+19*b*c+9*b-9*c^2+174*c-432)*g8+(-14*b*c-63*c+327/2)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (38*b*c-57*b+38*c^2-171*c+171)*g1+(-24*a*b-76*b*c+114*b-76*c^2+318*c-532)*g2+(12*a*b+38*b*c-57*b+38*c^2-159*c+266)*g3+(8*a^3+8*a^2*b*c+24*a^2*b-7*a^2-8*a*b^2+30*a*b*c-69*a*b+38*a*c^2-111*a*c+438*a-34*b^2-76*b*c+192*b+90*c-504)*g4+(-8*a^3-8*a^2*b*c-24*a^2*b+3*a^2+8*a*b^2-38*a*b*c+69*a*b-38*a*c^2+111*a*c-428*a+38*b^2+76*b*c-204*b-114*c+380)*g5+(4*a^3+4*a^2*b*c+12*a^2*b-3*a^2/2-4*a*b^2+19*a*b*c-69*a*b/2+19*a*c^2-111*a*c/2+214*a-7*b^2-38*b*c+216*b+283*c-682)*g6+(4*a*b*c-12*a*b-17*a/2-19*b*c+69*b/2-19*c^2+159*c/2-128)*g7+(-4*a*b*c+12*a*b+17*a/2-12*b^2+19*b*c-373*b/2+19*c^2-687*c/2+734)*g8+(6*b^2+76*b+132*c-303)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (39*b*c-117*b/2-579*c/4+1737/8)*g1+(-32*b*c+117*b+255*c-806)*g2+(16*b*c-117*b/2-255*c/2+403)*g3+(8*a^3+16*a^2-30*a*b*c-24*a*b-255*a*c/2+3013*a/4-24*b^2+15*b*c+513*b/2+117*c/4-6443/8)*g4+(-8*a^3-22*a^2+30*a*b*c+24*a*b+255*a*c/2-3055*a/4+32*b^2-303*b+1135/2)*g5+(4*a^3+11*a^2-15*a*b*c-12*a*b-255*a*c/4+3055*a/8-16*b^2+497*b/2+184*c-964)*g6+(69*b/2+69*c/2-216)*g7+(-341*b/2-437*c/2+1041)*g8+(68*b+92*c-825/2)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_4 (a b c:ℝ) (h:minorZero ![a,b,a,c,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (c+1-b) (c+a-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (c+1-b) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-a) (1+1-a) (1+a-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (a+1-1) (a+c-1) (a+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (a+a-0) (a+c-1) (a+1-a) (1+a-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-b) (1+1-a) (c+1-b) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+c-b) (1+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+c-1) (a+1-a) (c+a-1) (c+c-0) (c+1-1) (1+a-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^3-2*a^2+3*a/2-1/2)*g4+(-2*a^3+4*a^2-3*a+1)*g5+(2*a^3-2*a^2*c-a^2-8*a*c+15*a-16)*g6+(4*a^2*c-6*a^2+16*a*c-24*a)*g8+(-4*a^2*c+6*a^2+2*a*b-14*a*c+18*a+8*b+8*c-24)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-225/2)*g1+(225)*g2+(-225/2)*g3+(2*a^2*b+6*a^2*c-12*a^2-5*a*b/2+25*a*c/2-15*a+b/2+113*c/2+27)*g4+(-4*a^2*b-12*a^2*c+24*a^2+5*a*b-25*a*c+30*a-b-113*c-54)*g5+(4*a^3+4*a^2*b+12*a^2*c-5*a^2-5*a*b+25*a*c+41*a+b+113*c-5/2)*g6+(225/2)*g7+(-8*a^3-38*a^2-142*a-449/2)*g8+(8*a^3+28*a^2+209*a/2-28)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-225/2)*g1+(225)*g2+(-225/2)*g3+(4*a^2*c-6*a^2+15*a*c-45*a/2+56*c+57/2)*g4+(-8*a^2*c+12*a^2-30*a*c+45*a-112*c-57)*g5+(4*a^3+8*a^2*c+7*a^2+30*a*c+26*a+112*c+1/2)*g6+(225/2)*g7+(-8*a^3-38*a^2-142*a-449/2)*g8+(8*a^3+28*a^2+209*a/2-28)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_5 (a b c:ℝ) (h:minorZero ![a,b,c,a,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+a-1) (1+a-b) (a+1-1) (a+a-0) (a+a-1) (a+1-b) (a+a-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (a+1-b) (a+a-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (a+1-b) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+a-1) (1+1-a) (a+1-1) (a+a-0) (a+1-c) (1+1-a) (1+a-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-1) (a+a-1) (a+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-0) (a+a-1) (a+1-c) (1+a-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-b) (1+1-a) (a+1-b) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+a-1) (1+a-b) (1+1-a) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (a+a-0) (a+a-1) (a+1-c) (a+a-1) (a+a-0) (a+1-1) (1+a-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-1535/128)*g0+(-a^3/4-a^2*b/2-3*a^2*c/4+53*a^2/32+29*a*b/16+101*a*c/32-805*a/128-225*b/64+215*c/64+385/16)*g1+(-1535/64)*g2+(-a^2*b/2+3*a^2/4+29*a*b/16+7*a*c/16-27*a/8-225*b/64-215*c/64+275/8)*g3+(a^3/4+a^2*b+3*a^2*c/4-69*a^2/32-29*a*b/8-115*a*c/32+1269*a/128+225*b/32-665/64)*g4+(-a^2*b+a^2+29*a*b/8+7*a*c/8-29*a/4-225*b/32-215*c/32+165/8)*g5+(-1545/64)*g6+(-a^3/4-3*a^2*c/4+37*a^2/32+87*a*c/32-341*a/128+215*c/32-655/64)*g7+(a^3/4+a^2*b/2+3*a^2*c/4-53*a^2/32-29*a*b/16-101*a*c/32+805*a/128+225*b/64-215*c/64+385/16)*g8+(-a^2/4-a*b-3*a*c/4+19*a/8+137*b/32+115*c/32-3057/128)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (175/32)*g0+(-7*a^3/8+a^2*b/4+5*a^2*c/8-13*a^2/16-3*a*b/8-15*a*c/16+99*a/32+25*b/16-25*c/16-179/16)*g1+(175/16)*g2+(a^3+a^2*b/4+a^2*c/4-11*a^2/4-3*a*b/8-3*a*c/8-7*a/8+25*b/16+25*c/16-117/8)*g3+(-a^3/8-a^2*b/2-7*a^2*c/8+29*a^2/16+3*a*b/4+21*a*c/16-103*a/32-25*b/8+75/16)*g4+(2*a^3+a^2*b/2+a^2*c/2-2*a^2-3*a*b/4-3*a*c/4+a/4+25*b/8+25*c/8-71/8)*g5+(175/16)*g6+(-15*a^3/8+3*a^2*c/8+3*a^2/16-9*a*c/16+95*a/32-25*c/8+67/16)*g7+(7*a^3/8-a^2*b/4-5*a^2*c/8+13*a^2/16+3*a*b/8+15*a*c/16-99*a/32-25*b/16+25*c/16-171/16)*g8+(a^2/4+7*a*b/8+7*a*c/8-17*a/8-21*b/16-21*c/16+309/32)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (175/32)*g0+(9*a^3/8+a^2*b/4+5*a^2*c/8-21*a^2/16-3*a*b/8-15*a*c/16+35*a/32+25*b/16-25*c/16-171/16)*g1+(175/16)*g2+(a^3+a^2*b/4+a^2*c/4-11*a^2/4-3*a*b/8-3*a*c/8-7*a/8+25*b/16+25*c/16-117/8)*g3+(-17*a^3/8-a^2*b/2-7*a^2*c/8+37*a^2/16+3*a*b/4+21*a*c/16-39*a/32-25*b/8+67/16)*g4+(2*a^3+a^2*b/2+a^2*c/2-2*a^2-3*a*b/4-3*a*c/4+a/4+25*b/8+25*c/8-71/8)*g5+(175/16)*g6+(a^3/8+3*a^2*c/8-5*a^2/16-9*a*c/16+31*a/32-25*c/8+75/16)*g7+(-9*a^3/8-a^2*b/4-5*a^2*c/8+21*a^2/16+3*a*b/8+15*a*c/16-35*a/32-25*b/16+25*c/16-179/16)*g8+(a^2/4+7*a*b/8+7*a*c/8-17*a/8-21*b/16-21*c/16+309/32)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_6 (a b c:ℝ) (h:minorZero ![b,a,a,a,c]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-c) (b+1-1) (b+b-0) (b+1-a) (1+1-c) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (b+1-1) (b+a-1) (b+1-a) (1+1-c) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-c) (a+1-a) (a+a-0) (a+1-1) (1+1-c) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^2*b/2-a^2/2-5*a*b/8+a*c/8+5*a/2-5*b/8+19*c/32-13/32)*g0+(-a^3/4-3*a^2*b/2+21*a^2/16+15*a*b/8-a*c/4-179*a/32+15*b/8-19*c/32-3/32)*g1+(a^3/4+2*a^2*b-29*a^2/16-5*a*b/2+3*a*c/8+259*a/32-27*b/16+19*c/16-89/32)*g2+(-a^3/4-a^2*b/2+5*a^2/16+5*a*b/8-19*a/32+5*b/8+19*c/32-17/16)*g3+(a^3/4+a^2*b-13*a^2/16-5*a*b/4+a*c/8+99*a/32-5*b/4+21/32)*g4+(-a^3/2-2*a^2*b+9*a^2/8+a*b-a*c/4-107*a/16+5*b/2-19/32)*g5+(a^3/2+a^2*b-5*a^2/8-5*a*b/4+19*a/16-5*b/4-19*c/16+63/32)*g6+(a^3/4+a^2*b-13*a^2/16-5*a*b/4+a*c/8+123*a/32+3*b^2/4-11*b/16-c/8-105/32)*g7+(-a^3/4-a^2*b/2+5*a^2/16+5*a*b/8-19*a/32+5*b/8+19*c/32-39/32)*g8
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+a^2-a*b-5*a*c/4+25*a/8-21*b/32+93*c/64-55/64)*g0+(9*a^3/8+3*a^2*b/4+a^2*c/2-3*a^2/2+3*a*b+5*a*c/2-475*a/64+63*b/32-93*c/64+29/64)*g1+(-17*a^3/8-a^2*b-3*a^2*c/4+5*a^2/2-4*a*b-15*a*c/4+675*a/64+b/8+93*c/32-333/64)*g2+(-7*a^3/8+a^2*b/4+a^2/2+a*b-75*a/64+21*b/32+93*c/64-23/32)*g3+(-a^3/8-a^2*b/2-a^2*c/4+a^2/2-2*a*b-5*a*c/4+275*a/64-21*b/16-9/64)*g4+(a^3/4+a^2*b+a^2*c/2+5*a^2/2+21*a*b/4+5*a*c/2-211*a/32+21*b/8-93/64)*g5+(7*a^3/4-a^2*b/2-a^2-2*a*b+75*a/32-21*b/16-93*c/32+127/64)*g6+(-a^3/8-a^2*b/2-a^2*c/4-a^2-7*a*b/2-a*c+323*a/64-5*b^2/8+35*b/16+5*c/4-251/64)*g7+(-7*a^3/8+a^2*b/4+a^2/2+a*b-75*a/64+21*b/32+93*c/64-11/64)*g8
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-a^3-a^2*b/4-a^2*c/4+a^2-a*b-5*a*c/4+25*a/8-21*b/32+93*c/64-55/64)*g0+(25*a^3/8+3*a^2*b/4+a^2*c/2-2*a^2+3*a*b+5*a*c/2-603*a/64+63*b/32-93*c/64+61/64)*g1+(-33*a^3/8-a^2*b-3*a^2*c/4+3*a^2-4*a*b-15*a*c/4+803*a/64+b/8+93*c/32-365/64)*g2+(9*a^3/8+a^2*b/4+a*b-203*a/64+21*b/32+93*c/64-7/32)*g3+(-17*a^3/8-a^2*b/2-a^2*c/4+a^2-2*a*b-5*a*c/4+403*a/64-21*b/16-41/64)*g4+(17*a^3/4+a^2*b+a^2*c/2+3*a^2/2+21*a*b/4+5*a*c/2-339*a/32+21*b/8-29/64)*g5+(-9*a^3/4-a^2*b/2-2*a*b+203*a/32-21*b/16-93*c/32+63/64)*g6+(-17*a^3/8-a^2*b/2-a^2*c/4-a^2/2-7*a*b/2-a*c+451*a/64-5*b^2/8+35*b/16+5*c/4-283/64)*g7+(9*a^3/8+a^2*b/4+a*b-203*a/64+21*b/32+93*c/64+21/64)*g8
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_7 (a b c:ℝ) (h:minorZero ![b,a,a,c,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+c-a) (b+1-1) (b+b-0) (b+c-1) (c+1-a) (c+b-1) (c+c-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (c+1-a) (c+b-1) (c+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (b+1-1) (b+c-1) (b+1-a) (c+1-a) (c+c-0) (c+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (b+1-1) (b+c-1) (b+1-a) (1+1-a) (1+c-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (b+b-0) (b+c-1) (b+1-a) (1+b-a) (1+c-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+c-a) (1+1-a) (c+1-a) (c+c-0) (c+1-1) (1+1-a) (1+c-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+c-a) (1+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+c-1) (b+1-a) (c+b-1) (c+c-0) (c+1-1) (1+b-a) (1+c-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a^3-10*a^2/3+17*a/18-5*c/18-5/12)*g0+(-2*a^3+2*a^2*c/3+17*a^2/3+a*c/6-77*a/36-5*b/9+5*c/9+5/6)*g1+(5/6-5*c/9)*g2+(2*a^2*c/3-a^2+a*c/6-a/4-5*b/9+5/6)*g3+(a^3-2*a^2*c/3-7*a^2/3-a*c/6+43*a/36+5*b/9-5*c/18-5/12)*g4+(-5*c/18-5/12)*g5+(5/6)*g6+(-a^3-2*a^2*c/3+13*a^2/3+2*a*b/3-a*c/6-61*a/36+b+5*c/18-13/12)*g7+(2*a^3+2*a^2*c/3-23*a^2/3+a*c/6+59*a/36-5*b/9-5/6)*g8+(-a^3+10*a^2/3-17*a/18-5*c/18+5/4)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (2*a^2*b+10*a^2*c/3-8*a^2-5*a*b/2-35*a*c/18+20*a/3+b/2-25*c/54+19/108)*g0+(-4*a^3/3-4*a^2*b-20*a^2*c/3+127*a^2/9+5*a*b+35*a*c/9-457*a/36-b+25*c/27+29/27)*g1+(-4*a^3/3-17*a^2/9+23*a/36+26/27)*g3+(4*a^3/3+2*a^2*b+10*a^2*c/3-55*a^2/9-5*a*b/2-35*a*c/18+217*a/36+b/2-25*c/54-5/4)*g4+(25/108)*g5+(25/54)*g6+(4*a^3/3-2*a^2*b-10*a^2*c/3+59*a^2/9+5*a*b/2+35*a*c/18-313*a/36-b/2+25*c/54+187/108)*g7+(-4*a^3/3+4*a^2*b+20*a^2*c/3-161*a^2/9-5*a*b-35*a*c/9+503*a/36+b-25*c/27+7/18)*g8+(-2*a^2*b-10*a^2*c/3+8*a^2+5*a*b/2+35*a*c/18-20*a/3-b/2+25*c/54+31/108)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (4*a^2*c/3-2*a^2+5*a*c/9-5*a/6-26*c/27+181/108)*g0+(-4*a^3/3-8*a^2*c/3+19*a^2/9-10*a*c/9+83*a/36+52*c/27-52/27)*g1+(-4*a^3/3-17*a^2/9+23*a/36+26/27)*g3+(4*a^3/3+4*a^2*c/3-a^2/9+5*a*c/9-53*a/36-26*c/27+1/4)*g4+(25/108)*g5+(25/54)*g6+(4*a^3/3-4*a^2*c/3+5*a^2/9-5*a*c/9-43*a/36+26*c/27+25/108)*g7+(-4*a^3/3+8*a^2*c/3-53*a^2/9+10*a*c/9-37*a/36-52*c/27+61/18)*g8+(-4*a^2*c/3+2*a^2-5*a*c/9+5*a/6+26*c/27-131/108)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_8 (a b c:ℝ) (h:minorZero ![b,a,c,a,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-a) (b+1-1) (b+b-0) (b+a-1) (a+1-a) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (a+1-a) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (a+1-a) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-c) (1+1-a) (1+b-c) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (b+1-1) (b+a-1) (b+1-c) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (b+b-0) (b+a-1) (b+1-c) (1+b-c) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-a) (1+1-a) (a+1-a) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-a) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-c) (a+b-1) (a+a-0) (a+1-1) (1+b-c) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (-4*a^2*b+6*a^2-24*a*b^3+20*a*b^2*c-102*a*b^2+66*a*b*c+351*a*b-135*a*c^2+261*a*c-999*a/4+16*b^3-4*b^2*c+42*b^2-6*b*c-283*b+81*c^2-225*c+753/4)*g0+(4*a^2*b-6*a^2+24*a*b^3-20*a*b^2*c+102*a*b^2-66*a*b*c-351*a*b+135*a*c^2-261*a*c+999*a/4+8*b^3-10*b^2*c+51*b^2-60*b*c-56*b+27*c^2/2+72*c-219/8)*g1+(-2*a^2*b+3*a^2-12*a*b^3+10*a*b^2*c-51*a*b^2+33*a*b*c+351*a*b/2-135*a*c^2/2+261*a*c/2-999*a/8-4*b^3+2*b^2*c-27*b^2+54*b*c-44*b+27*c^2/2-9*c/2-93/8)*g2+(6*b^2*c-9*b^2-81*c^2/2+108*c-567/8)*g3+(-12*b^3+4*b^2*c-42*b^2+33*b*c+327*b/2-27*c^2+45*c/2-36)*g4+(16*b^3-8*b^2*c+72*b^2-63*b*c-351*b/2+54*c^2-171*c+297/2)*g5+(-8*b^3+8*b^2*c-48*b^2+12*b*c+168*b-54*c^2+126*c-207/2)*g6+(-4*b^3+4*b^2*c-24*b^2+18*b*c+48*b-27*c^2+171*c/2-117/2)*g7+(4*b^3-4*b^2*c+18*b^2-6*b*c-96*b+27*c^2-45*c/2+45/2)*g8+(12*b-18)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (8*a^3+52*a^2*b^2-2*a^2+1487*a*b^2-2223*a*b*c/2-3225*a*b/4-270*a*c-897*a/2-913*b^2+305*b*c/2+6255*b/4+48*c+531)*g0+(-8*a^3-52*a^2*b^2+2*a^2-1539*a*b^2+2223*a*b*c/2+3225*a*b/4+270*a*c+897*a/2-620*b^2+2227*b*c/4-1617*b/8+267*c/2+63/4)*g1+(4*a^3+26*a^2*b^2-a^2+1539*a*b^2/2-2223*a*b*c/4-3225*a*b/8-135*a*c-897*a/4+238*b^2-1109*b*c/4+10681*b/8-183*c/2+1653/4)*g2+(-1545*b*c/4+4635*b/8-225*c/2+675/4)*g3+(26*a*b^2+1543*b^2/2-323*b*c/2-1821*b/2-69*c/2-693/2)*g4+(-34*a*b^2-1999*b^2/2+515*b*c-383*b+150*c-75/2)*g5+(16*a*b^2+600*b^2-323*b*c-921*b/2-69*c-243)*g6+(8*a*b^2+264*b^2-515*b*c/2+677*b/2-75*c+75)*g7+(-8*a*b^2-290*b^2+323*b*c/2+1473*b/2+69*c/2+513/2)*g8+(-10*b^2-120*b-45/2)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (8*a^3+48*a^2*b^2-2*a^2+1156*a*b^2-1157*a*b*c-1417*a*b/2-48*a*c^3+4189*a*c^2/2-5242*a*c+331*a/8-716*b^2+295*b*c+2695*b/2+48*c^3-2527*c^2/2+2924*c+12575/8)*g0+(-8*a^3-48*a^2*b^2+2*a^2-1204*a*b^2+1157*a*b*c+1417*a*b/2+48*a*c^3-4189*a*c^2/2+5242*a*c-331*a/8+12*b^2*c-494*b^2+846*b*c-697*b-12*c^3-833*c^2/4+299*c/4+6375/16)*g1+(4*a^3+24*a^2*b^2-a^2+602*a*b^2-1157*a*b*c/2-1417*a*b/4-24*a*c^3+4189*a*c^2/4-2621*a*c+331*a/16-12*b^2*c+172*b^2-567*b*c+1245*b/2+20*c^3-661*c^2/4-873*c+49361/16)*g2+(12*b^2*c-18*b^2-12*c^3+2507*c^2/4-9205*c/4+33315/16)*g3+(24*a*b^2-12*b^2*c+616*b^2-1141*b*c/2-1041*b/4-12*c^3+841*c^2/2-1415*c/4-2015)*g4+(-32*a*b^2+12*b^2*c-766*b^2+1799*b*c/2+715*b/4+16*c^3-881*c^2+3354*c-2120)*g5+(16*a*b^2+468*b^2-370*b*c-385*b-24*c^3+833*c^2-2028*c-1523/4)*g6+(8*a*b^2+198*b^2-257*b*c-111*b/2-8*c^3+865*c^2/2-6811*c/4+5113/4)*g7+(-8*a*b^2-242*b^2+185*b*c+645*b/2+12*c^3-817*c^2/2+1581*c/4+1601)*g8+(-4*b^2-130*b+4*c^2+10*c-45/2)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

set_option maxHeartbeats 1200000 in
lemma rigid_9 (a b c:ℝ) (h:minorZero ![b,c,a,a,a]) (ap:0≤a) (al:a<1) (bl:b≤1) (cl:c≤1) : b=a ∧ c=a ∧ a^2-3*a+1=0 := by
  have g0 := h 1 2 3 1 2 3
  change detThree (1+1-0) (1+b-1) (1+a-c) (b+1-1) (b+b-0) (b+a-1) (a+1-c) (a+b-1) (a+a-0)=0 at g0
  have g1 := h 1 2 3 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (a+1-c) (a+b-1) (a+1-1)=0 at g1
  have g2 := h 1 2 3 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (a+1-c) (a+a-0) (a+1-1)=0 at g2
  have g3 := h 1 2 3 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1)=0 at g3
  have g4 := h 1 2 4 1 2 4
  change detThree (1+1-0) (1+b-1) (1+1-a) (b+1-1) (b+b-0) (b+1-a) (1+1-a) (1+b-a) (1+1-0)=0 at g4
  have g5 := h 1 2 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (b+1-1) (b+a-1) (b+1-a) (1+1-a) (1+a-1) (1+1-0)=0 at g5
  have g6 := h 1 2 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (b+b-0) (b+a-1) (b+1-a) (1+b-a) (1+a-1) (1+1-0)=0 at g6
  have g7 := h 1 3 4 1 3 4
  change detThree (1+1-0) (1+a-c) (1+1-a) (a+1-c) (a+a-0) (a+1-1) (1+1-a) (1+a-1) (1+1-0)=0 at g7
  have g8 := h 1 3 4 2 3 4
  change detThree (1+b-1) (1+a-c) (1+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g8
  have g9 := h 2 3 4 2 3 4
  change detThree (b+b-0) (b+a-1) (b+1-a) (a+b-1) (a+a-0) (a+1-1) (1+b-a) (1+a-1) (1+1-0)=0 at g9
  simp only [detThree] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
  have h0 : (2*b-3)*(a-1)*(a+1)*(a^2-3*a+1)=0 := by
    linear_combination (a*b+5*a*c/4-99*a/8+b^2+9*b*c/4-213*b/32-13*c^2/4+69*c/32+4787/128)*g0+(a^2*b/2-a^2/4-15*a*b/16+7*a*c/16+59*a/4-243*b/64-9*c^2/2+1043*c/64-1843/64)*g1+(-a^2/2-37*a/2-9*c/2+45)*g2+(-a^3/4-a^2*b/2+31*a^2/32+15*a*b/16+7*a*c/16+3287*a/128-b^2*c-13*b*c^2/4+213*b*c/32+243*b/64+99*c/64-3043/64)*g3+(-a^2*b/2+a^2/2+15*a*b/16-7*a*c/16-11*a/2+243*b/64+9*c^2/2-755*c/64+3)*g4+(-a^3/4+7*a^2/32+7*a*c/8+2807*a/128-b^2*c-13*b*c^2/4+213*b*c/32-9*c^2/2+283*c/32-99/4)*g5+(a^3/4-7*a^2/32-7*a*c/8-2807*a/128+b^2*c+13*b*c^2/4-213*b*c/32+9*c^2/2-283*c/32+99/4)*g6+(a^3/4+a^2*b-47*a^2/32-15*a*b/8-2583*a/128+b^2*c+13*b*c^2/4-213*b*c/32-243*b/32+2739/128)*g7+(-a^3/4-3*a^2*b/2+79*a^2/32+45*a*b/16-7*a*c/16+4247*a/128-b^2*c-13*b*c^2/4+213*b*c/32+729*b/64+189*c/64-161/4)*g8+(a^2*b/2-a^2-15*a*b/16+7*a*c/16-13*a-243*b/64-189*c/64+2413/128)*g9
  have h1 : (b-a)*(b+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-3*a^2/2-21*a*b/8-21*a*c/8+227*a/8-21*b^2/8-21*b*c/4+13*b+63*c^2/8-5*c/2-1045/16)*g0+(-a^3-a^2*b/4-a^2*c/4+9*a^2/4-a*b/2-a*c/2-29*a+61*b/8+21*c^2/2-317*c/8+561/8)*g1+(a^2/2+43*a+21*c/2-209/2)*g2+(-7*a^3/8+a^2*b/4-a^2*c/4+a*b/2-a*c/2-1029*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-61*b/8-109*c/8+919/8)*g3+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+a*b/2+a*c/2+15*a/2-61*b/8-21*c^2/2+233*c/8-10)*g4+(-15*a^3/8-a^2*c/2+11*a^2/4-a*c-805*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c+21*c^2/2-129*c/4+259/4)*g5+(15*a^3/8+a^2*c/2-11*a^2/4+a*c+805*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c-21*c^2/2+129*c/4-259/4)*g6+(-a^3/8-a^2*b/2+5*a^2/2-a*b+909*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c+61*b/4-947/16)*g7+(9*a^3/8+3*a^2*b/4+a^2*c/4-11*a^2/2+3*a*b/2+a*c/2-1477*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-183*b/8+25*c/8+108)*g8+(-a^3-a^2*b/4-a^2*c/4+3*a^2-a*b/2-a*c/2+71*a/2+61*b/8-25*c/8-781/16)*g9
  have h2 : (c-a)*(c+a-3)*(4*a-1)*(a-1)*(a+1)=0 := by
    linear_combination (-3*a^2/2-21*a*b/8-21*a*c/8+227*a/8-21*b^2/8-21*b*c/4+13*b+63*c^2/8-5*c/2-1045/16)*g0+(-a^3-a^2*b/4-a^2*c/4+9*a^2/4-a*b/2-a*c/2-29*a+61*b/8+21*c^2/2-317*c/8+561/8)*g1+(a^2/2+43*a+21*c/2-209/2)*g2+(9*a^3/8+a^2*b/4-a^2*c/4-a^2/2+a*b/2-a*c/2-1061*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-61*b/8-109*c/8+923/8)*g3+(a^3+a^2*b/4+a^2*c/4-5*a^2/2+a*b/2+a*c/2+15*a/2-61*b/8-21*c^2/2+233*c/8-10)*g4+(a^3/8-a^2*c/2+9*a^2/4-a*c-837*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c+21*c^2/2-129*c/4+261/4)*g5+(-a^3/8+a^2*c/2-9*a^2/4+a*c+837*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c-21*c^2/2+129*c/4-261/4)*g6+(-17*a^3/8-a^2*b/2+3*a^2-a*b+941*a/16-21*b^2*c/8-63*b*c^2/8+13*b*c+61*b/4-955/16)*g7+(25*a^3/8+3*a^2*b/4+a^2*c/4-6*a^2+3*a*b/2+a*c/2-1509*a/16+21*b^2*c/8+63*b*c^2/8-13*b*c-183*b/8+25*c/8+217/2)*g8+(-a^3-a^2*b/4-a^2*c/4+3*a^2-a*b/2-a*c/2+71*a/2+61*b/8-25*c/8-781/16)*g9
  have nz1 : a-1≠0 := by linarith
  have nz2 : a+1≠0 := by linarith
  have nz3 : 2*b-3≠0 := by linarith
  have root := (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (mul_ne_zero nz3 nz1) nz2)
  have nz4 : 4*a-1≠0 := by rintro e; nlinarith only [root,show a*(4*a-1)=0 by rw [e,mul_zero],e]
  have bod : b+a-3≠0 := by linarith
  have cod : c+a-3≠0 := by linarith
  simp only [mul_eq_zero,nz1,nz2,nz4,bod,cod,or_false] at h1 h2
  exact ⟨sub_eq_zero.mp h1,sub_eq_zero.mp h2,root⟩

end Erdos1082Second
end
end

section
/- Three equal short chords force all five short chords of a diameter cycle to coincide. -/
open EuclideanGeometry
noncomputable section
namespace Erdos1082Second

lemma rigid_value (w:Fin 5→ℝ) (h:minorZero w) (wp:∀i,0≤w i) (wl:∀i,w i<1) (a:ℝ)
    (count:3≤(Finset.univ.filter fun i => w i=a).card) : (∀i,w i=a) ∧ a^2-3*a+1=0 := by
  classical
  obtain ⟨B,sub,n⟩:=Finset.exists_subset_card_eq count
  have e (i:Fin 5) (hi:i∈B) : w i=a := (Finset.mem_filter.mp (sub hi)).2
  have cases : ∀S:Finset (Fin 5), S.card=3 → (0∈S ∧ 1∈S ∧ 2∈S) ∨ (0∈S ∧ 1∈S ∧ 3∈S) ∨ (0∈S ∧ 1∈S ∧ 4∈S) ∨ (0∈S ∧ 2∈S ∧ 3∈S) ∨ (0∈S ∧ 2∈S ∧ 4∈S) ∨ (0∈S ∧ 3∈S ∧ 4∈S) ∨ (1∈S ∧ 2∈S ∧ 3∈S) ∨ (1∈S ∧ 2∈S ∧ 4∈S) ∨ (1∈S ∧ 3∈S ∧ 4∈S) ∨ (2∈S ∧ 3∈S ∧ 4∈S) := by decide
  rcases cases B n with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,a,w 3,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_0 a (w 3) (w 4) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 3).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_1 a (w 2) (w 4) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 2).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,a,w 2,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_2 a (w 2) (w 3) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 2).le (wl 3).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_3 a (w 1) (w 4) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 1).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_4 a (w 1) (w 3) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 1).le (wl 3).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![a,w 1,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_5 a (w 1) (w 2) (eq ▸ h) (e _ h1 ▸ wp 0) (e _ h1 ▸ wl 0) (wl 1).le (wl 2).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,a,w 4] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_6 a (w 0) (w 4) (eq ▸ h) (e _ h1 ▸ wp 1) (e _ h1 ▸ wl 1) (wl 0).le (wl 4).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,a,w 3,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_7 a (w 0) (w 3) (eq ▸ h) (e _ h1 ▸ wp 1) (e _ h1 ▸ wl 1) (wl 0).le (wl 3).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,a,w 2,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_8 a (w 0) (w 2) (eq ▸ h) (e _ h1 ▸ wp 1) (e _ h1 ▸ wl 1) (wl 0).le (wl 2).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl
  · obtain ⟨h1,h2,h3⟩ := hc
    have eq : w=![w 0,w 1,a,a,a] := by
      funext i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | rfl
    obtain ⟨hk,hl,root⟩:=rigid_9 a (w 0) (w 1) (eq ▸ h) (e _ h1 ▸ wp 2) (e _ h1 ▸ wl 2) (wl 0).le (wl 1).le
    refine ⟨?_,root⟩
    intro i; fin_cases i <;> first | exact e _ h1 | exact e _ h2 | exact e _ h3 | exact hk | exact hl

theorem diameter_pentagon_rigid (A:Finset ℝ²) (M:ℝ) (hM:0<M) (bound:∀x y:A,dist x.1 y.1≤M)
    (z:Fin 5→A) (inj:Function.Injective z) (edges:∀i,dist (z i).1 (z (i+1)).1=M)
    (r:ℝ) (count:3≤(Finset.univ.filter fun i => dist (z i).1 (z (i+2)).1=r).card) :
    ∀i,dist (z i).1 (z (i+2)).1=r := by
  classical
  let p (i:Fin 5):=(z i).1
  let w (i:Fin 5):=(M^2)⁻¹*dist (p i) (p (i+2))^2
  have hm : (M^2)⁻¹>0 := inv_pos.mpr (sq_pos_of_pos hM)
  have pos (i) : 0≤w i := mul_nonneg hm.le (sq_nonneg _)
  have ex:=(OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.Erdos1082Diameter.diameter_exclusions A M hM bound).1
  have lt (i) : w i<1 := by
    have neq : dist (p i) (p (i+2))≠M := by
      intro de
      have hn : [i,i+1,i+2,i+3,i+4].Nodup := (by decide : ∀j:Fin 5,[j,j+1,j+2,j+3,j+4].Nodup) i
      have no : [z i,z (i+1),z (i+2),z (i+3),z (i+4)].Nodup := hn.map inj
      apply ex ⟨z i,z (i+1),z (i+2),z (i+3),z (i+4),no,edges i,?_,de,?_⟩
      · simpa [add_assoc] using edges (i+1)
      · simpa [add_assoc] using edges (i+3)
    have ds : dist (p i) (p (i+2))<M := lt_of_le_of_ne (bound _ _) neq
    have sq : dist (p i) (p (i+2))^2<M^2 := by nlinarith [dist_nonneg (x:=p i) (y:=p (i+2)),mul_pos (sub_pos.mpr ds) (add_pos_of_pos_of_nonneg hM (dist_nonneg (x:=p i) (y:=p (i+2))))]
    change (M^2)⁻¹*_ < 1
    rw [←inv_mul_cancel₀ (sq_pos_of_pos hM).ne']
    exact mul_lt_mul_of_pos_left sq hm
  let a:=(M^2)⁻¹*r^2
  have inc : (Finset.univ.filter fun i => dist (z i).1 (z (i+2)).1=r)⊆Finset.univ.filter (fun i => w i=a) := by
    intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [w,a,p,(Finset.mem_filter.mp hi).2]⟩
  have rigid:=rigid_value w (normalized_minor p M hM edges) pos lt a (by have :=Finset.card_le_card inc; omega)
  obtain ⟨j,hj⟩:=Finset.card_pos.mp (show 0<(Finset.univ.filter fun i => dist (z i).1 (z (i+2)).1=r).card by omega)
  have rn:0≤r := (Finset.mem_filter.mp hj).2 ▸ dist_nonneg
  intro i
  have val:=rigid.1 i
  change (M^2)⁻¹*dist (p i) (p (i+2))^2=(M^2)⁻¹*r^2 at val
  exact (pow_left_inj₀ dist_nonneg rn (by decide : 2≠0)).mp (mul_left_cancel₀ hm.ne' val)
end Erdos1082Second
end
end

section
/- An isolated five-cycle diameter forces extra doubly occupied perpendicular bisectors. -/
open EuclideanGeometry OMA.R_Erdos1082_erdos_1082_parts_i_R1 OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1
noncomputable section
namespace Erdos1082Second
lemma apex_missing (A : Finset ℝ²) (hcard : A.card=2*distinctDistances A+2) (p : ℝ²) (hp : p∈A) (M:ℝ) (mem:M∈distanceSet A) (missing:∀x∈A.erase p,dist p x≠M) :
    A.card+8 ≤ (A.offDiag.filter fun b => dist p b.1=dist p b.2).card := by
  classical
  let B := A.erase p
  let D:=(distanceSet A).erase M
  let F (r : ℝ) := B.filter fun x => dist p x=r
  let P := A.offDiag.filter fun b => dist p b.1=dist p b.2
  have hBx (x : ℝ²) (hx : x∈B) : dist p x∈D := by
    have notM:=missing x hx
    obtain ⟨hne,hx⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr ⟨notM,dist_mem hp hx hne.symm⟩
  have hmap (b : ℝ²×ℝ²) (hb : b∈P) : b.1∈B ∧ b.2∈B := by
    obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
    obtain ⟨hx,hy,hn⟩ := Finset.mem_offDiag.mp hb
    have hx' : b.1≠p := by intro h; rw [h,dist_self] at he; exact hn (h.trans (dist_eq_zero.mp he.symm))
    have hy' : b.2≠p := by intro h; rw [h,dist_self] at he; exact hn ((dist_eq_zero.mp he).symm.trans h.symm)
    exact ⟨Finset.mem_erase.mpr ⟨hx',hx⟩,Finset.mem_erase.mpr ⟨hy',hy⟩⟩
  have hsum : B.card=∑ r∈D, (F r).card := Finset.card_eq_sum_card_fiberwise hBx
  have hpair : P.card=∑ r∈D, (F r).offDiag.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=fun b : ℝ²×ℝ² => dist p b.1)
      (t:=D) (fun b hb => hBx _ (hmap b hb).1)]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ext b
    constructor
    · intro h
      obtain ⟨hb,hr⟩ := Finset.mem_filter.mp h
      obtain ⟨hx,hy⟩ := hmap b hb
      obtain ⟨ho,he⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_filter.mpr ⟨hx,hr⟩,
        Finset.mem_filter.mpr ⟨hy,he.symm.trans hr⟩,(Finset.mem_offDiag.mp ho).2.2⟩
    · intro h
      obtain ⟨hx,hy,hn⟩ := Finset.mem_offDiag.mp h
      obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy,ht⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
        ⟨Finset.mem_of_mem_erase hx,Finset.mem_of_mem_erase hy,hn⟩,hr.trans ht.symm⟩,hr⟩
  have term (r : ℝ) : 4*(F r).card≤(F r).offDiag.card+6 := by
    rw [Finset.offDiag_card]
    generalize (F r).card=k
    match k with
    | 0 | 1 | 2 => decide
    | k+3 =>
      have he : (k+3)*(k+3)=(k+3)+(k*k+5*k+6) := by ring
      rw [he,Nat.add_sub_cancel_left]; nlinarith
  have hsum' := Finset.sum_le_sum (s:=D) (fun r _ => term r)
  rw [←Finset.mul_sum,←hsum,Finset.sum_add_distrib,←hpair,Finset.sum_const,nsmul_eq_mul] at hsum'
  have hb : B.card+1=A.card := Finset.card_erase_add_one hp
  change 4*B.card≤P.card+D.card*6 at hsum'
  have dec:D.card+1=distinctDistances A := Finset.card_erase_add_one mem
  change A.card+8≤P.card
  omega

lemma pent_bisectors (A : Finset ℝ²) (hA : NonTrilinear (A:Set ℝ²)) (hcard : A.card=2*distinctDistances A+2) (M:ℝ) (hM:M∈distanceSet A)
    (P:Finset ℝ²) (pa:P⊆A) (pn:P.card=5) (support:∀x∈A,∀y∈A,x≠y → dist x y=M → x∈P ∧ y∈P) :
    let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    (9*A.card-30)+(A.offDiag.filter fun b => k b=0).card≤(A.offDiag.filter fun b => k b=2).card := by
  classical
  dsimp only
  let R (p : ℝ²) (b : ℝ²×ℝ²) := dist p b.1=dist p b.2
  let k (b : ℝ²×ℝ²) := (A.filter fun p => R p b).card
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=A) (t:=A.offDiag) R
  change (∑ p∈A,(A.offDiag.filter (R p)).card)=∑ b∈A.offDiag,k b at hdouble
  have term (p) (hp:p∈A) : A.card+2+(if p∈P then 0 else 6)≤(A.offDiag.filter (R p)).card := by
    by_cases h:p∈P
    · simpa [h] using apex_count A hcard p hp
    · have miss (x) (hx:x∈A.erase p) : dist p x≠M := fun he => h (support p hp x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx).symm he).1
      simpa [h,Nat.add_assoc] using apex_missing A hcard p hp M hM miss
  have hs:=Finset.sum_le_sum (s:=A) (fun p hp => term p hp)
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hdouble] at hs
  have zeros : (∑x∈A,if x∈P then 0 else 6)= (A\P).card*6 := by
    calc
      _ = ∑_x∈A.filter (fun x => x∉P), (6:ℕ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx; by_cases h:x∈P <;> simp [h]
      _ = _ := by simp [Finset.sdiff_eq_filter]
  rw [zeros] at hs
  have dec: (A\P).card+5=A.card := pn ▸ Finset.card_sdiff_add_card_eq_card pa
  have hk (b : ℝ²×ℝ²) (hb : b∈A.offDiag) : k b ≤ 2 :=
    bisector_limit A hA _ _ (Finset.mem_offDiag.mp hb).2.2
  have hsum := Finset.sum_congr (s₁:=A.offDiag) rfl (fun b hb => show
    k b+(if k b=0 then 1 else 0) = 1 + (if k b=2 then 1 else 0) by
      have := hk b hb
      split_ifs <;> omega)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hsum
  simp only [Finset.sum_boole] at hsum
  rw [Finset.offDiag_card] at hsum
  change (9*A.card-30)+(A.offDiag.filter fun b => k b=0).card≤(A.offDiag.filter fun b => k b=2).card
  have hn : 1≤A.card := by omega
  have hmul := Nat.mul_le_mul_left A.card hn
  simp only [Nat.mul_one] at hmul
  have big:30≤9*A.card := by omega
  nlinarith [Nat.sub_add_cancel hmul,Nat.sub_add_cancel big]


end Erdos1082Second
end
end

open EuclideanGeometry

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1.H2 := by
  intro A hn hcard M hM hmax hcyc few
  have bound (x y:A) : dist x.1 y.1≤M := by
    by_cases eq : x=y
    · simpa [eq] using hM.le
    · exact hmax _ (Finset.mem_image.mpr ⟨(x.1,y.1),Finset.mem_offDiag.mpr ⟨x.2,y.2,Subtype.coe_injective.ne eq⟩,rfl⟩)
  have mem : M∈distanceSet A := by
    obtain ⟨a,b,c,d,e,_,edge,_⟩:=hcyc
    have ne:a.1≠b.1 := by intro h; rw [h,dist_self] at edge; linarith
    exact Finset.mem_image.mpr ⟨(a.1,b.1),Finset.mem_offDiag.mpr ⟨a.2,b.2,ne⟩,edge⟩
  obtain ⟨P,pa,pn,endpoint,_⟩:=Erdos1082Second.pentagon_support A M hcyc few
  refine ⟨?_,?_,Erdos1082Second.diameter_pentagon_rigid A M hM bound,
    Erdos1082Second.pent_bisectors A hn hcard M mem P pa pn endpoint⟩
  swap
  · intro d hd hs
    have g:=Erdos1082Second.pentagon_second_bounds A M d hM hd bound hcyc few hs
    exact ⟨g.1,g.2,Erdos1082Second.pentagon_strict_second A M d hM hd bound hcyc few hs⟩
  intro K hK
  have memall (x : ℝ²) (hx:x∈A) (y : ℝ²) (hy:y∈A) : dist x y/M∈K := by
    by_cases hxy : x=y
    · simp [hxy]
    · exact hK _ (Finset.mem_image.mpr ⟨(x,y),Finset.mem_offDiag.mpr ⟨hx,hy,hxy⟩,rfl⟩)
  exact ⟨Erdos1082Padic.critical_pentagon_no_dyadic_model A hn hcard M hM hcyc K M hM memall,
    Erdos1082Padic.critical_pentagon_even_degree A hn hcard M hM hcyc K M hM memall⟩
