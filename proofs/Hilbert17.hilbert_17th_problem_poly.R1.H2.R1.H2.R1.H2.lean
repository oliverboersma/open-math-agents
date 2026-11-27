import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1_H2_R1

-- Quadratic cancellation for a nonnegative binary quadratic multiplier.
-- The identity and the coordinate frame follow a draft by astra-3; the closing tactics are filled in here.

namespace OMA.QuadraticCancellation
open Finset

lemma squareSum {R : Type*} [CommSemiring R] (x : R) : IsSumSq (x^2) := by
  simpa only [sq] using IsSumSq.mul_self x

lemma sumRepresentation {R : Type*} [CommSemiring R] {p : R} (hp : IsSumSq p) :
    ∃ n : ℕ, ∃ f : Fin n → R, p=∑ i,(f i)^2 := by
  induction hp with
  | zero => exact ⟨0,Fin.elim0,by simp⟩
  | sq_add a _ ih =>
    obtain ⟨n,f,rfl⟩ := ih
    exact ⟨n+1,Fin.cons a f,by simp [Fin.sum_univ_succ,sq]⟩

lemma realSumSq {R : Type*} [CommSemiring R] [Algebra ℝ R] (a : ℝ) (ha : 0 ≤ a) :
    IsSumSq (algebraMap ℝ R a) := by
  simpa only [← map_pow,Real.sq_sqrt ha] using squareSum (algebraMap ℝ R (Real.sqrt a))

lemma clearPositive {R : Type*} [CommSemiring R] [Algebra ℝ R] (a : ℝ) (ha : 0 < a) {p : R}
    (h : IsSumSq (algebraMap ℝ R a * p)) : IsSumSq p := by
  have hh := (realSumSq (R:=R) a⁻¹ (inv_nonneg.mpr ha.le)).mul h
  rwa [←mul_assoc,←map_mul,inv_mul_cancel₀ ha.ne',map_one,one_mul] at hh

set_option maxHeartbeats 2000000 in
/-- The two vectors of residues at a complex zero are orthogonal and have
the same squared length. Projecting onto them gives a sum of squares after
cancelling the quadratic factor. -/
lemma cancelNorm {R : Type*} [CommRing R] [IsDomain R] [Algebra ℝ R]
    (x y F : R) (hq : x^2+y^2≠0) (H : Fin 3 → R) (A B : Fin 3 → ℝ)
    (norms : ∑ i,(B i)^2=∑ i,(A i)^2) (orth : ∑ i,A i*B i=0)
    (eqn : 4*(x^2+y^2)*F =
      ∑ i,((x^2+y^2)*H i + y^2*(algebraMap ℝ R (A i)*y+algebraMap ℝ R (B i)*x))^2) :
    IsSumSq F := by
  let D := ∑ i,(A i)^2
  let a : Fin 3 → R := fun i => algebraMap ℝ R (A i)
  let b : Fin 3 → R := fun i => algebraMap ℝ R (B i)
  let d : R := algebraMap ℝ R D
  let s := ∑ i,a i*H i
  let t := ∑ i,b i*H i
  let T := ∑ i,(H i)^2
  let q := x^2+y^2
  have aa : ∑ i,(a i)^2=d := by simp [a,d,D]
  have bb : ∑ i,(b i)^2=d := by simpa [b,d,D] using congrArg (algebraMap ℝ R) norms
  have ab : ∑ i,a i*b i=0 := by simpa [a,b] using congrArg (algebraMap ℝ R) orth
  have eqr : 4*F = q*T+2*y^2*(y*s+x*t)+d*y^4 := by
    apply mul_left_cancel₀ hq
    change 4*q*F = ∑ i,(q*H i + y^2*(a i*y+b i*x))^2 at eqn
    dsimp only [q,s,t,T] at eqn ⊢
    simp only [Fin.sum_univ_three] at aa bb ab eqn ⊢
    linear_combination eqn+y^6*aa+(x^2*y^4)*bb+(2*x*y^5)*ab
  have qsq : IsSumSq q := (squareSum x).add (squareSum y)
  have Tsum : IsSumSq T := IsSumSq.sum_sq univ H
  have Dpos : 0 ≤ D := sum_nonneg (fun i _ => sq_nonneg (A i))
  rcases Dpos.eq_or_lt with zero | pos
  · have az (i : Fin 3) : A i=0 := by
      have h := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 3))) => sq_nonneg (A j)) (mem_univ i)
      change _ ≤ D at h
      nlinarith
    have bz (i : Fin 3) : B i=0 := by
      have h := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 3))) => sq_nonneg (B j)) (mem_univ i)
      rw [norms] at h; change _ ≤ D at h
      nlinarith
    apply clearPositive 4 (by norm_num)
    have ee : 4*F=q*T := by simpa [s,t,a,b,d,az,bz,←zero] using eqr
    rw [map_ofNat,ee]; exact qsq.mul Tsum
  · let W (i : Fin 3) := d*H i-a i*s-b i*t
    have er : ∑ i,(W i)^2 = d^2*T-d*(s^2+t^2) := by
      dsimp only [W,s,t,T]
      simp only [Fin.sum_univ_three] at aa bb ab ⊢
      linear_combination (a 0*H 0+a 1*H 1+a 2*H 2)^2*aa+
        (b 0*H 0+b 1*H 1+b 2*H 2)^2*bb+
        2*(a 0*H 0+a 1*H 1+a 2*H 2)*(b 0*H 0+b 1*H 1+b 2*H 2)*ab
    have scaled : 4*d^2*F=d*((y*s+x*t+d*y^2)^2+(x*s-y*t)^2)+q*∑ i,(W i)^2 := by
      rw [er]; dsimp only [q] at eqr ⊢
      linear_combination d^2*eqr
    apply clearPositive (4*D^2) (by positivity)
    rw [map_mul,map_ofNat,map_pow]
    change IsSumSq (4*d^2*F)
    rw [scaled]
    exact ((realSumSq D pos.le).mul ((squareSum _).add (squareSum _))).add
      (qsq.mul (IsSumSq.sum_sq univ W))

end OMA.QuadraticCancellation
namespace OMA.QuadraticCancellation
open Finset MvPolynomial
abbrev BForm := MvPolynomial (Fin 2) ℝ
abbrev TForm := Polynomial BForm

lemma expansion {p : BForm} {n : ℕ} (hp : p.IsHomogeneous n) :
    ∃ c : ℕ → ℝ, p=∑ i ∈ range (n+1), C (c i)*X 0^i*X 1^(n-i) := by
  classical
  let f : Polynomial ℝ := aeval ![Polynomial.X,1] p
  refine ⟨f.coeff,?_⟩
  conv_lhs => rw [←Polynomial.homogenize_eq_of_isHomogeneous hp (rfl : aeval ![Polynomial.X,1] p=f)]
  rw [Polynomial.homogenize,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro i hi
  simp [f,monomial_eq,Finsupp.prod_fintype,Fin.prod_univ_two,mul_assoc]

lemma quadShape (p : BForm) (hp : p.IsHomogeneous 2) :
    ∃ a b c : ℝ, p=C a*X 0^2+C b*X 0*X 1+C c*X 1^2 := by
  obtain ⟨c,h⟩ := expansion hp
  refine ⟨c 2,c 1,c 0,?_⟩
  simp [sum_range_succ] at h
  rw [h]; ring

lemma cubicShape (p : BForm) (hp : p.IsHomogeneous 3) :
    ∃ a b c d : ℝ, p=C a*X 0^3+C b*X 0^2*X 1+C c*X 0*X 1^2+C d*X 1^3 := by
  obtain ⟨c,h⟩ := expansion hp
  refine ⟨c 3,c 2,c 1,c 0,?_⟩
  simp [sum_range_succ] at h
  rw [h]; ring

lemma normResidue (p : BForm) (hp : p.IsHomogeneous 3) :
    ∃ h : BForm, ∃ a b : ℝ, p=(X 0^2+X 1^2)*h+X 1^2*(C a*X 1+C b*X 0) := by
  obtain ⟨a,b,c,d,eq⟩ := cubicShape p hp
  refine ⟨C a*X 0+C b*X 1,d-b,c-a,?_⟩
  rw [eq,map_sub,map_sub]; ring

lemma lineResidue (p : BForm) (hp : p.IsHomogeneous 3) :
    ∃ h : BForm, ∃ a : ℝ, p=X 0*h+C a*X 1^3 := by
  obtain ⟨a,b,c,d,eq⟩ := cubicShape p hp
  exact ⟨C a*X 0^2+C b*X 0*X 1+C c*X 1^2,d,by rw [eq]; ring⟩

lemma cancellationAtI (x y F : TForm) (hq : x^2+y^2≠0)
    (ev : TForm →ₐ[ℝ] ℂ) (hx : ev x=Complex.I) (hy : ev y=1)
    (H : Fin 3 → TForm) (A B : Fin 3 → ℝ)
    (eqn : 4*(x^2+y^2)*F =
      ∑ i,((x^2+y^2)*H i+y^2*(algebraMap ℝ TForm (A i)*y+algebraMap ℝ TForm (B i)*x))^2) :
    IsSumSq F := by
  have z := congrArg ev eqn
  simp only [map_mul,map_pow,map_add,map_sum,map_ofNat,AlgHom.commutes,hx,hy,one_pow,
    Complex.I_sq,neg_add_cancel,zero_mul,zero_add,mul_zero,one_mul,mul_one] at z
  have zr := congrArg Complex.re z
  have zi := congrArg Complex.im z
  simp [Fin.sum_univ_three,sq,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.coe_algebraMap,Complex.ofReal_re,Complex.ofReal_im] at zr zi
  apply cancelNorm x y F hq H A B _ _ eqn
  · simp only [Fin.sum_univ_three]; linarith
  · simp only [Fin.sum_univ_three]; linarith

lemma normalizedNorm (p : Fin 3 → BForm) (hp : ∀ i,(p i).IsHomogeneous 3)
    (J : Fin 3 → TForm) (F : TForm)
    (eqn : 4*Polynomial.C ((X 0:BForm)^2+X 1^2)*F =
       ∑ i,(Polynomial.C ((X 0:BForm)^2+X 1^2)*J i+Polynomial.C (p i))^2) : IsSumSq F := by
  classical
  choose h a b shape using fun i => normResidue (p i) (hp i)
  let x : TForm := Polynomial.C (X 0)
  let y : TForm := Polynomial.C (X 1)
  let e : BForm →ₐ[ℝ] ℂ := aeval ![Complex.I,1]
  let ev : TForm →ₐ[ℝ] ℂ := Polynomial.aevalTower e 0
  have qne : x^2+y^2≠0 := by
    intro eq
    have h := congrArg (fun t : TForm => MvPolynomial.eval ![1,0] (t.eval 0)) eq
    norm_num [x,y] at h
  apply cancellationAtI x y F qne ev (by simp [ev,e,x]) (by simp [ev,e,y])
    (fun i => J i+Polynomial.C (h i)) a b
  have mapped : 4*(x^2+y^2)*F=∑ i,((x^2+y^2)*J i+Polynomial.C (p i))^2 := by
    simpa only [map_add,map_pow,x,y] using eqn
  rw [mapped]
  apply sum_congr rfl; intro i _
  rw [shape i]
  simp only [map_add,map_mul,map_pow,x,y,mul_add,add_assoc]
  rfl

lemma normalizedLine (p : Fin 3 → BForm) (hp : ∀ i,(p i).IsHomogeneous 3)
    (J : Fin 3 → TForm) (F : TForm)
    (eqn : 4*Polynomial.C ((X 0:BForm)^2)*F =
      ∑ i,(Polynomial.C ((X 0:BForm)^2)*J i+Polynomial.C (p i))^2) : IsSumSq F := by
  classical
  choose h a shape using fun i => lineResidue (p i) (hp i)
  let x : TForm := Polynomial.C (X 0)
  let E (t : TForm) : ℝ := MvPolynomial.eval ![0,1] (t.eval 0)
  have ev := congrArg E eqn
  simp [E,shape,Fin.sum_univ_three] at ev
  have hsum : a 0^2+a 1^2+a 2^2=0 := ev.symm
  have az (i : Fin 3) : a i=0 := by
    have htot : ∑ j : Fin 3, a j^2=0 := by simpa [Fin.sum_univ_three] using hsum
    have hle := single_le_sum (fun j (_ : j ∈ univ) => sq_nonneg (a j)) (mem_univ i)
    have : a i^2 ≤ 0 := by simpa [htot] using hle
    exact (sq_eq_zero_iff).mp (le_antisymm this (sq_nonneg _))
  have xn : x≠0 := by simp [x,MvPolynomial.X_ne_zero]
  let k (i : Fin 3) := x*J i+Polynomial.C (h i)
  have cancel : 4*F= ∑ i,(k i)^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 xn)
    calc x^2*(4*F) = 4*Polynomial.C ((X 0:BForm)^2)*F := by simp [x]; ring
         _ = _ := eqn
         _ = x^2*(∑ i,(k i)^2) := by
           rw [mul_sum]; apply sum_congr rfl; intro i _
           rw [shape i,az i]; simp [k,x]; ring
  apply clearPositive 4 (by norm_num)
  rw [map_ofNat,cancel]; exact IsSumSq.sum_sq univ k
end OMA.QuadraticCancellation
namespace OMA.QuadraticCancellation
open MvPolynomial Finset

def Frame (a : BForm) : Prop := ∃ L D : Fin 2 → BForm,
  (∀ i,(L i).IsHomogeneous 1) ∧ (∀ i,aeval D (L i)=X i) ∧
  (aeval L a=X 0^2 ∨ aeval L a=X 0^2+X 1^2)

lemma triangularFrame (a : BForm) (s t w : ℝ) (hs : s≠0)
    (shape : a=(C s*X 0+C t*X 1)^2+(C w*X 1)^2) : Frame a := by
  classical
  let k := if w=0 then 1 else w
  have hk : k≠0 := by dsimp [k]; split_ifs <;> simp_all
  let Y : BForm := C k⁻¹*X 1
  let L : Fin 2 → BForm := ![C s⁻¹*(X 0-C t*Y), Y]
  let D : Fin 2 → BForm := ![C s*X 0+C t*X 1,C k*X 1]
  have ly : Y.IsHomogeneous 1 := isHomogeneous_C_mul_X _ _
  have lin : ∀ i,(L i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact ((isHomogeneous_X _ _).sub (ly.C_mul t)).C_mul _
    · exact ly
  have back (i : Fin 2) : aeval D (L i)=X i := by
    apply MvPolynomial.funext
    intro v
    fin_cases i
    · simp [L,D,Y]; field_simp; ring
    · simp [L,D,Y]; field_simp
  have first : aeval L (C s*X 0+C t*X 1)=X 0 := by
    apply MvPolynomial.funext; intro v; simp [L,Y]; field_simp; ring
  refine ⟨L,D,lin,back,?_⟩
  rw [shape,map_add,map_pow,first,map_pow]
  by_cases hw : w=0
  · left; simp [hw]
  · right
    have last : aeval L (C w*X 1)=X 1 := by
      apply MvPolynomial.funext; intro v; simp [L,Y,k,hw]
    rw [last]

lemma frame (a : BForm) (ha : a.IsHomogeneous 2) (nonneg : ∀ v,0≤eval v a) (hn : a≠0) :
    Frame a := by
  classical
  obtain ⟨r,b,c,shape⟩ := quadShape a ha
  have rp : 0≤r := by simpa [shape] using nonneg ![1,0]
  have cp : 0≤c := by simpa [shape] using nonneg ![0,1]
  have discr := discrim_le_zero (a:=r) (b:=b) (c:=c) (fun t : ℝ => by
    simpa [shape,sq,mul_assoc] using nonneg ![t,1])
  simp only [discrim] at discr
  rcases rp.eq_or_lt with zero | pos
  · rw [←zero] at discr
    have bz : b=0 := by nlinarith only [discr,sq_nonneg b]
    have cpos : 0<c := by
      refine lt_of_le_of_ne cp ?_; intro h; apply hn; simp [shape,←zero,←h,bz]
    let s := Real.sqrt c
    have ss : s^2=c := Real.sq_sqrt cp
    have sn : s≠0 := (Real.sqrt_pos.mpr cpos).ne'
    let L : Fin 2 → BForm := ![X 1,C s⁻¹*X 0]
    let D : Fin 2 → BForm := ![C s*X 1,X 0]
    refine ⟨L,D,?_,?_,Or.inl ?_⟩
    · intro i; fin_cases i
      · exact isHomogeneous_X _ _
      · exact isHomogeneous_C_mul_X _ _
    · intro i; apply MvPolynomial.funext; intro v
      fin_cases i
      · simp [L,D]
      · simp [L,D]; field_simp
    · apply MvPolynomial.funext; intro v
      simp [L,shape,←zero,bz,←ss]; field_simp
  · let s := Real.sqrt r
    let t := b/(2*s)
    have ss : s^2=r := Real.sq_sqrt rp
    have sp : 0<s := Real.sqrt_pos.mpr pos
    have st : 2*s*t=b := by dsimp [t]; field_simp
    have rempos : 0≤c-t^2 := by
      apply nonneg_of_mul_nonneg_right (a:=4*s^2) ?_ (by positivity)
      rw [←ss,←st] at discr
      nlinarith only [discr]
    apply triangularFrame a s t (Real.sqrt (c-t^2)) sp.ne'
    apply MvPolynomial.funext; intro v
    simp only [shape,map_add,map_mul,map_pow,eval_C,eval_X]
    rw [mul_pow,Real.sq_sqrt rempos,←st,←ss]
    ring

lemma transported {a b u v : BForm} (ha : a.IsHomogeneous 2)
    (an : ∀ x,0≤eval x a) (az : a≠0)
    (hb : b.IsHomogeneous 3) (hu : u.IsHomogeneous 3) (hv : v.IsHomogeneous 3)
    (F : TForm) (eqn : 4*Polynomial.C a*F=
      (2*Polynomial.C a*Polynomial.X+Polynomial.C b)^2+(Polynomial.C u)^2+(Polynomial.C v)^2) :
    ∃ m : ℕ, ∃ g : Fin m → TForm, F=∑ i,(g i)^2 := by
  classical
  obtain ⟨L,D,lin,back,form⟩ := frame a ha an az
  let eL : BForm →ₐ[ℝ] BForm := aeval L
  let eD : BForm →ₐ[ℝ] BForm := aeval D
  let φ := Polynomial.mapRingHom eL.toRingHom
  let ψ := Polynomial.mapRingHom eD.toRingHom
  have ret (f : BForm) : eD (eL f)=f := by
    rw [comp_aeval_apply,show (fun i => eD (L i))=X from funext back,aeval_X_left_apply]
  have idhg : eD.toRingHom.comp eL.toRingHom=RingHom.id BForm := RingHom.ext ret
  have recovered : ψ (φ F)=F := by
    change (F.map _).map _=F
    rw [Polynomial.map_map,idhg,Polynomial.map_id]
  let ps : Fin 3 → BForm := ![eL b,eL u,eL v]
  have cubic (i : Fin 3) : (ps i).IsHomogeneous 3 := by
    fin_cases i
    · simpa [ps,eL] using hb.aeval L lin
    · simpa [ps,eL] using hu.aeval L lin
    · simpa [ps,eL] using hv.aeval L lin
  let J : Fin 3 → TForm := ![2*Polynomial.X,0,0]
  have he := congrArg φ eqn
  have normalized : 4*Polynomial.C (eL a)*φ F =
      ∑ i,(Polynomial.C (eL a)*J i+Polynomial.C (ps i))^2 := by
    simp [J,ps,Fin.sum_univ_three,φ,Polynomial.coe_mapRingHom,Polynomial.map_C,Polynomial.map_X,
      map_add,map_mul,map_pow,map_ofNat] at he ⊢
    linear_combination he
  have form' : eL a=X 0^2 ∨ eL a=X 0^2+X 1^2 := by simpa [eL] using form
  have sos : IsSumSq (φ F) := by
    rcases form' with h | h
    · rw [h] at normalized; exact normalizedLine ps cubic J _ normalized
    · rw [h] at normalized; exact normalizedNorm ps cubic J _ normalized
  obtain ⟨m,g,eq⟩ := sumRepresentation sos
  refine ⟨m,fun i => ψ (g i),?_⟩
  simpa only [recovered,map_sum,map_pow] using congrArg ψ eq
end OMA.QuadraticCancellation

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1_H2_R1.H2 := by
  intro a b u v ha han haz hb hu hv F eqn
  exact OMA.QuadraticCancellation.transported ha han haz hb hu hv F eqn
