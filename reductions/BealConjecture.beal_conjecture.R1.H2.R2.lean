import OMAReductions.R_BealConjecture_beal_conjecture_R1
import Mathlib

-- Credit: @ubuwaits

/-!
# The quartic branch of Beal's conjecture

The signatures (4,4,3), (4,3,4), (3,4,4) and (4,4,4) are discharged
unconditionally in this reduction. The one-quartic branch becomes a single
signed equation, with ordered odd prime exponents. For two quartics and a prime
p ≥ 5, a sum gives H2. A difference gives H3 for opposite parities and H4 for
two odd quartic bases.

For Lucas's sum-of-fourths argument, see Bennett, Chen, Dahmen and Yazdani,
*Generalized Fermat equations: a miscellany*, section 5. The proof of Euler's
three-cubes theorem used in the difference case is adapted from Aaron Belinski's
formalization in open-math-agents PR 1271.

H2 is a specialization of Bennett, Ellenberg and Ng on A⁴+B²=Cⁿ. H3 is
a specialization of the Darmon–Merel theorem on three powers in arithmetic
progression. H4 follows in the literature from Ribet, *On the equation
aᵖ+2ᵅbᵖ+cᵖ=0*, Theorem 3. The remaining hypotheses are stated explicitly.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R1_H2_R2

/-- One fourth power and two odd prime powers. Signed bases cover each
placement of the fourth power and the prime exponents are in order. -/
def H1 : Prop :=
  ∀ {p q : ℕ} {x y : ℤ} {w : ℕ}, p.Prime → q.Prime → 2<p → p≤q →
    x≠0 → y≠0 → 0<w → IsCoprime x y → x^p+y^q ≠ (w:ℤ)^4

/-- Two fourth powers adding to an odd prime power of exponent at least five. -/
def H2 : Prop :=
  ∀ {p a b c : ℕ}, p.Prime → 5≤p → 0<a → 0<b → 0<c → a.Coprime b →
    a^4+b^4 ≠ c^p

/-- A progression of p-th powers with positive, distinct square endpoints. -/
def H3 : Prop :=
  ∀ {p u v w : ℕ}, p.Prime → 5≤p → 0<v → v<u → 0<w → u.Coprime v →
    (u^2)^p+(v^2)^p ≠ 2*w^p

/-- The weighted Fermat equation from two odd quartic bases. -/
def H4 : Prop :=
  ∀ {p u v w : ℕ}, p.Prime → 5≤p → 0<u → 0<v → 0<w → u.Coprime v →
    (u^2)^p+(2^(p-3))^2*(v^2)^p ≠ w^p

namespace BealQuartic

private theorem apart {a b p : ℕ} (h : a.Coprime b) (hp : p.Prime) (ha : p ∣ a) :
    ¬p ∣ b := by
  intro hb
  exact hp.not_dvd_one (h.gcd_eq_one ▸ Nat.dvd_gcd ha hb)

theorem split_factors {u v a b t n : ℕ} (hc : u.Coprime v)
    (ha : 0<a) (hb : 0<b) (hau : a ∣ u) (hbv : b ∣ v)
    (h : u*v=a*b*t^n) : ∃ x y : ℕ, u=a*x^n ∧ v=b*y^n := by
  obtain ⟨g,hg⟩ := hau
  obtain ⟨k,hk⟩ := hbv
  have cop : g.Coprime k :=
    Nat.Coprime.coprime_dvd_right (hk ▸ dvd_mul_left _ _)
      (Nat.Coprime.coprime_dvd_left (hg ▸ dvd_mul_left _ _) hc)
  have product : g*k=t^n := by
    apply Nat.mul_left_cancel (Nat.mul_pos ha hb)
    rw [hg,hk] at h
    linear_combination h
  have get {a b : ℕ} (c : a.Coprime b) (prod : a*b=t^n) : ∃ w : ℕ, a=w^n :=
    exists_eq_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp c)) prod
  obtain ⟨x,hx⟩ := get cop product
  obtain ⟨y,hy⟩ := get cop.symm ((Nat.mul_comm _ _).trans product)
  exact ⟨x,y,by rw [hg,hx],by rw [hk,hy]⟩

/-- Half the sum and half the difference of two coprime odd numbers are coprime. -/
theorem halves {u v : ℕ} (hu : u%2=1) (hv : v%2=1)
    (hlt : v<u) (cop : u.Coprime v) :
    ∃ A B : ℕ, 0<B ∧ u=A+B ∧ A=B+v ∧ A.Coprime B := by
  let A := (u+v)/2
  let B := (u-v)/2
  have ea : A=B+v := by dsimp [A,B]; omega
  have eu : u=A+B := by dsimp [A,B]; omega
  refine ⟨A,B,by dsimp [B]; omega,eu,ea,?_⟩
  apply Nat.coprime_of_dvd
  intro p pp pa pb
  apply apart cop pp (eu ▸ dvd_add pa pb)
  apply (Nat.dvd_add_iff_right pb).mpr
  rwa [←ea]

private theorem lucas_local {a b w : ℕ} (cop : a.Coprime b) (eqn : a^4=3*b^4+w^2) :
    a%2=1 ∧ b%2=0 ∧ w%2=1 ∧ ¬3 ∣ a := by
  have h16 := congrArg (fun k : ℕ => (k:ZMod 16)) eqn
  have h9 := congrArg (fun k : ℕ => (k:ZMod 9)) eqn
  push_cast at h16 h9
  have parity : ∀ x y z : ZMod 16, x^4=3*y^4+z^2 →
      (x.val%2=0 ∧ y.val%2=0) ∨ (x.val%2=1 ∧ y.val%2=0 ∧ z.val%2=1) := by decide +kernel
  have tern : ∀ x y z : ZMod 9, x^4=3*y^4+z^2 → x.val%3=0 → y.val%3=0 := by decide +kernel
  have par := parity _ _ _ h16
  have dx := tern _ _ _ h9
  simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] at par
  simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] at dx
  have na : ¬3 ∣ a := fun ha => apart cop Nat.prime_three ha (Nat.dvd_of_mod_eq_zero (dx (Nat.mod_eq_zero_of_dvd ha)))
  rcases par with bad|h
  · exact (apart cop Nat.prime_two (Nat.dvd_of_mod_eq_zero bad.1) (Nat.dvd_of_mod_eq_zero bad.2)).elim
  · exact ⟨h.1,h.2.1,h.2.2,na⟩

/-- A factorization of a fourth power times 12, with coprime factors whose sum
is an odd square, puts all of 12 in the same factor. -/
private theorem twelve_split {U V t s : ℕ} (cop : U.Coprime V) (hV : V%2=1)
    (hprod : U*V=12*t^4) (hs : s^2=U+V) :
    ∃ a b : ℕ, U=12*a^4 ∧ V=b^4 := by
  have htwo : (2:ℕ).Coprime V := (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hV)).symm
  have hfour : 4 ∣ U := (htwo.pow_left 2).dvd_of_dvd_mul_right (hprod ▸
    (show 4 ∣ 12*t^4 from dvd_mul_of_dvd_left (by decide) _))
  have hthree : 3 ∣ U*V := hprod ▸ (show 3 ∣ 12*t^4 from dvd_mul_of_dvd_left (by decide) _)
  rcases Nat.prime_three.dvd_mul.mp hthree with hu|hv
  · have h12 : 12 ∣ U := (show Nat.Coprime 4 3 by decide).mul_dvd_of_dvd_of_dvd hfour hu
    obtain ⟨a,b,ha,hb⟩ := split_factors cop (by decide : 0<12) (by decide : 0<1) h12
      (one_dvd _) (by simpa using hprod : U*V=12*1*t^4)
    exact ⟨a,b,ha,by simpa using hb⟩
  · obtain ⟨a,b,ha,hb⟩ := split_factors cop (by decide : 0<4) (by decide : 0<3) hfour hv hprod
    have impossible : ∀ q x y : ZMod 4, q^2=4*x^4+3*y^4 → y.val%2=0 := by decide +kernel
    rw [ha,hb] at hs
    have mod4 := congrArg (fun k : ℕ => (k:ZMod 4)) hs
    push_cast at mod4
    have eb := impossible _ _ _ mod4
    simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at eb
    rw [hb,Nat.mul_mod,Nat.pow_mod,eb] at hV
    contradiction

/-- One descent cycle takes a solution of a⁴=3b⁴+w² to one with a smaller first
coordinate, through the intermediate equation m⁴+12ℓ⁴=a². -/
private theorem lucas_step {a b w : ℕ} (_ha : 0<a) (hb : 0<b)
    (cop : a.Coprime b) (h : a^4=3*b^4+w^2) :
    ∃ x y z : ℕ, x<a ∧ 0<x ∧ 0<y ∧ x.Coprime y ∧ x^4=3*y^4+z^2 := by
  obtain ⟨ao,be,wo,a3⟩ := lucas_local cop h
  have acw : (a^2).Coprime w := by
    apply Nat.coprime_of_dvd
    intro p pp hp hw
    have pa := pp.dvd_of_dvd_pow hp
    have pa4 := pa.trans (dvd_pow_self a (by decide : 4≠0))
    have pw2 := hw.trans (dvd_pow_self w (by decide : 2≠0))
    have pb4 : p ∣ 3*b^4 := (Nat.dvd_add_iff_left pw2).mpr (h ▸ pa4)
    rcases pp.dvd_mul.mp pb4 with h3|pb
    · exact a3 ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_three).mp h3 ▸ pa)
    · exact apart cop pp pa (pp.dvd_of_dvd_pow pb)
  have a2o : a^2%2=1 := by rw [Nat.pow_mod,ao]
  have lt₁ : w<a^2 := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have := Nat.pow_pos (n:=4) hb
    rw [←pow_mul]; norm_num; omega
  obtain ⟨A,B,hB,hSum,hDiff,hAB⟩ := halves a2o wo lt₁ acw
  let t := b/2
  have bt : b=2*t := by dsimp [t]; omega
  have abprod : A*B=12*t^4 := by
    have hsq : (a^2)^2=3*b^4+w^2 := by rw [←pow_mul]; exact h
    rw [hSum,hDiff,bt] at hsq
    rw [hDiff]; nlinarith only [hsq]
  have choose (U V : ℕ) (hc : U.Coprime V) (hp : U*V=12*t^4)
      (sum : a^2=U+V) (vo : V%2=1) (u0 : 0<U) (v0 : 0<V) :
      ∃ l m : ℕ, 0<l ∧ 0 < m ∧ a^2=m^4+12*l^4 ∧ (m^2).Coprime a := by
    obtain ⟨l,m,hu,hv⟩ := twelve_split hc vo hp sum
    have lm : 0<l := by by_contra! hz; simp_all
    have mm : 0 < m := by by_contra! hz; simp_all
    have mc : V.Coprime (a^2) := by rw [sum]; exact Nat.coprime_add_self_right.mpr hc.symm
    have rootcop := Nat.Coprime.coprime_dvd_left (show m^2 ∣ V by rw [hv]; exact pow_dvd_pow m (by decide : 2≤4)) mc
    refine ⟨l,m,lm,mm,?_,Nat.Coprime.coprime_dvd_right (dvd_pow_self a (by decide : 2≠0)) rootcop⟩
    rw [sum,hu,hv,Nat.add_comm]
  have pairs : ∃ l m : ℕ, 0<l ∧ 0 < m ∧ a^2=m^4+12*l^4 ∧ (m^2).Coprime a := by
    by_cases ae : A%2=0
    · exact choose A B hAB abprod hSum (by omega) (by omega) hB
    · exact choose B A hAB.symm ((Nat.mul_comm _ _).trans abprod) (hSum.trans (Nat.add_comm _ _))
        (by omega) hB (by omega)
  obtain ⟨l,m,lp,mp,hm,ma⟩ := pairs
  have m2o : m^2%2=1 := by
    have mo := congrArg (fun n : ℕ => n%2) hm
    simp only [Nat.add_mod,Nat.mul_mod 12,Nat.pow_mod m,show 12%2=0 by decide,zero_mul,
      Nat.zero_mod,add_zero,Nat.mod_mod] at mo
    have m1 : m%2=1 := by
      by_contra hn
      have me : m%2=0 := by omega
      rw [me] at mo
      norm_num at mo
      omega
    rw [Nat.pow_mod,m1]
  have lt₂ : m^2<a := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have := Nat.pow_pos (n:=4) lp
    rw [←pow_mul]; norm_num; omega
  obtain ⟨C,D,dpos,hs,hd,hcd⟩ := halves ao m2o lt₂ ma.symm
  have cdprod : C*D=3*l^4 := by
    have hm' : a^2=(m^2)^2+12*l^4 := by rw [←pow_mul]; exact hm
    rw [hs,hd] at hm'
    rw [hd]; nlinarith only [hm']
  have d3 : 3 ∣ D := by
    by_contra nd
    have c3 := (Nat.prime_three.dvd_mul.mp (show 3 ∣ C*D from cdprod ▸ dvd_mul_right _ _)).resolve_right nd
    obtain ⟨x,y,cx,dy⟩ := split_factors hcd (by decide : 0<3) (by decide : 0<1) c3
      (one_dvd _) (by simpa using cdprod : C*D=3*1*l^4)
    rw [cx,dy,one_mul] at hd
    have eq3 := congrArg (fun k : ℕ => (k:ZMod 3)) hd
    push_cast at eq3
    have tab : ∀ x y m : ZMod 3, 3*x^4=y^4+m^2 → y=0 := by decide +kernel
    have yz := tab _ _ _ eq3
    have yy := (ZMod.natCast_eq_zero_iff ..).mp yz
    exact nd (dy ▸ dvd_mul_of_dvd_right (yy.trans (dvd_pow_self y (by decide : 4≠0))) _)
  obtain ⟨x,y,cx,dy⟩ := split_factors hcd (by decide : 0<1) (by decide : 0<3) (one_dvd _) d3
    (by simpa using cdprod : C*D=1*3*l^4)
  rw [one_mul] at cx
  have xp : 0<x := by
    by_contra! hz
    have e : x=0 := by omega
    rw [e] at cx
    norm_num at cx
    omega
  have yp : 0<y := by
    by_contra! hz
    have e : y=0 := by omega
    rw [e] at dy
    norm_num at dy
    omega
  have xa : x<a := by
    have le := Nat.le_pow (by decide : 0<4) (a:=x)
    omega
  have xy := Nat.Coprime.coprime_dvd_right
    (show y ∣ D from dy ▸ (dvd_pow_self y (by decide : 4≠0)).trans (dvd_mul_left _ _))
    (Nat.Coprime.coprime_dvd_left (cx ▸ dvd_pow_self x (by decide : 4≠0)) hcd)
  exact ⟨x,y,m,xa,xp,yp,xy,by rwa [cx,dy] at hd⟩

/-- Lucas's quartic descent. No coprime positive a,b satisfy a⁴−3b⁴=w². -/
theorem no_lucas_quartic (a b w : ℕ) (ha : 0<a) (hb : 0<b) (cop : a.Coprime b) :
    a^4 ≠ 3*b^4+w^2 := by
  induction a using Nat.strong_induction_on generalizing b w with
  | h a ih =>
    intro eqn
    obtain ⟨x,y,z,lt,xp,yp,xy,he⟩ := lucas_step ha hb cop eqn
    exact ih x lt y z xp yp xy he

end BealQuartic

namespace BealQuartic

open Zsqrtd

private theorem unit_fourth {v : GaussianInt} (hu : IsUnit v) : v^4=1 := by
  obtain ⟨a,b⟩ := v
  have h := (norm_eq_one_iff' (by decide) (⟨a,b⟩:GaussianInt)).mpr hu
  change a*a-(-1)*b*b=1 at h
  have a₀ : -1≤a := by nlinarith [sq_nonneg b]
  have a₁ : a≤1 := by nlinarith [sq_nonneg b]
  have b₀ : -1≤b := by nlinarith [sq_nonneg a]
  have b₁ : b≤1 := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b <;> norm_num at h <;> decide

/-- The two quartic summands give simultaneous square coordinates in the
Gaussian parametrization of a primitive sum of squares equal to a cube. -/
theorem gaussian_parameters {a b c : ℕ} (cop : a.Coprime b) (h : a^4+b^4=c^3) :
    ∃ s t : ℤ, IsCoprime s t ∧
      (a:ℤ)^2=s*(s^2-3*t^2) ∧ (b:ℤ)^2=t*(t^2-3*s^2) := by
  let _ := IsBezout.toGCDDomain GaussianInt
  let z : GaussianInt := ⟨(a:ℤ)^2,(b:ℤ)^2⟩
  have cp : IsCoprime ((a:ℤ)^2) ((b:ℤ)^2) := (cop.isCoprime.pow_left).pow_right
  have co : c%2=1 := by
    have mod4 := congrArg (fun k : ℕ => (k:ZMod 4)) h
    push_cast at mod4
    have tab : ∀ x y z : ZMod 4, x^4+y^4=z^3 →
        z.val%2=1 ∨ (x.val%2=0 ∧ y.val%2=0) := by decide +kernel
    have ret := tab _ _ _ mod4
    simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at ret
    rcases ret with p|⟨e,f⟩
    · exact p
    · exact (Nat.prime_two.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd
        (Nat.dvd_of_mod_eq_zero e) (Nat.dvd_of_mod_eq_zero f))).elim
  have co2 : IsCoprime ((c:GaussianInt)^3) (2:GaussianInt) := by
    have hc := (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr co)).isCoprime
    simpa using (hc.pow_left (m:=3)).map (Int.castRingHom GaussianInt)
  have norm : z.norm=(c:ℤ)^3 := by
    have eqn : (a:ℤ)^4+(b:ℤ)^4=(c:ℤ)^3 := by exact_mod_cast h
    simp only [norm_def,z]
    linear_combination eqn
  have factor : z*star z=(c:GaussianInt)^3 := by rw [←norm_eq_mul_conj,norm,Int.cast_pow]; rfl
  have sum : z+star z=2*(a:GaussianInt)^2 := by
    apply Zsqrtd.ext <;> simp [z,re_mul,im_mul,pow_two]
    ring
  have diff : (z-star z)*(⟨0,-1⟩:GaussianInt)=2*(b:GaussianInt)^2 := by
    apply Zsqrtd.ext <;> simp [z,re_mul,im_mul,pow_two]
    ring
  have rel : IsRelPrime z (star z) := by
    intro d dz db
    apply co2.isRelPrime
    · rw [←factor]; exact dz.trans (dvd_mul_right _ _)
    · have da : d ∣ 2*(a:GaussianInt)^2 := sum ▸ dvd_add dz db
      have dv : d ∣ 2*(b:GaussianInt)^2 := diff ▸ (dvd_sub dz db).trans (dvd_mul_right _ _)
      have cpG : IsCoprime ((a:GaussianInt)^2) ((b:GaussianInt)^2) := by
        simpa using cp.map (Int.castRingHom GaussianInt)
      obtain ⟨u,v,eqn⟩ := cpG
      have two : (2:GaussianInt)=u*(2*(a:GaussianInt)^2)+v*(2*(b:GaussianInt)^2) := by
        linear_combination -2*eqn
      rw [two]
      exact dvd_add (dvd_mul_of_dvd_right da _) (dvd_mul_of_dvd_right dv _)
  obtain ⟨w,eps,hw⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr rel) factor
  let v := w*(eps:GaussianInt)^3
  have power : v^3=z := by
    have eu : ((eps:GaussianInt)^3)^3=(eps:GaussianInt) := by
      rw [←pow_mul,show 3*3=4*2+1 by decide,pow_succ,pow_mul,unit_fourth eps.isUnit,one_pow,one_mul]
    simpa only [v,mul_pow,eu] using hw
  let s := v.re
  let t := -v.im
  have re := congrArg Zsqrtd.re power
  have im := congrArg Zsqrtd.im power
  have eq₁ : (a:ℤ)^2=s*(s^2-3*t^2) := by
    simp only [show 3=2+1 by decide,pow_succ,pow_zero,one_mul,re_mul,im_mul,z] at re
    dsimp [s,t]; linear_combination -re
  have eq₂ : (b:ℤ)^2=t*(t^2-3*s^2) := by
    simp only [show 3=2+1 by decide,pow_succ,pow_zero,one_mul,re_mul,im_mul,z] at im
    dsimp [s,t]; linear_combination -im
  refine ⟨s,t,?_,eq₁,eq₂⟩
  obtain ⟨u,v,e⟩ := cp
  rw [eq₁,eq₂] at e
  exact ⟨u*(s^2-3*t^2),v*(t^2-3*s^2),by linear_combination e⟩

end BealQuartic

namespace BealQuartic

private theorem split_square {m n x : ℤ} (cop : IsCoprime m n) (eqn : m*n=x^2) (xn : x≠0) :
    ∃ e a b : ℤ, (e=1 ∨ e= -1) ∧ m=e*a^2 ∧ n=e*b^2 := by
  have get {u v : ℤ} (c : IsCoprime u v) (h : u*v=x^2) :
      ∃ a : ℤ, u=a^2 ∨ u= -a^2 := by
    obtain ⟨a,eps,he⟩ := exists_associated_pow_of_mul_eq_pow
      (gcd_isUnit_iff_isRelPrime.mpr c.isRelPrime) h
    rcases Int.isUnit_iff.mp eps.isUnit with pos|neg
    · exact ⟨a,Or.inl (by simpa [pos] using he.symm)⟩
    · exact ⟨a,Or.inr (by simpa [neg] using he.symm)⟩
  obtain ⟨a,aa⟩ := get cop eqn
  obtain ⟨b,bb⟩ := get cop.symm ((mul_comm _ _).trans eqn)
  rcases aa with h₁|h₁ <;> rcases bb with h₂|h₂
  · exact ⟨1,a,b,Or.inl rfl,by simpa using h₁,by simpa using h₂⟩
  · rw [h₁,h₂] at eqn
    nlinarith only [eqn,sq_pos_of_ne_zero xn,sq_nonneg (a*b)]
  · rw [h₁,h₂] at eqn
    nlinarith only [eqn,sq_pos_of_ne_zero xn,sq_nonneg (a*b)]
  · exact ⟨-1,a,b,Or.inr rfl,by simpa using h₁,by simpa using h₂⟩

private theorem cube_factor_coprime {s t : ℤ} (cop : IsCoprime s t) (h3 : ¬3 ∣ s) :
    IsCoprime s (s^2-3*t^2) := by
  have p3 : Prime (3:ℤ) := by norm_num
  have cs := (p3.irreducible.coprime_iff_not_dvd.mpr h3).symm
  obtain ⟨u,v,he⟩ := cs.mul_right (cop.pow_right (n:=2))
  exact ⟨u+v*s,-v,by linear_combination he⟩

/-- If neither coordinate carries the prime three, both would be signed squares
with signed-square cofactors. This is impossible at two. -/
private theorem two_unit_factors {s t e f A B C D : ℤ} (cop : IsCoprime s t)
    (he : e=1 ∨ e= -1) (hf : f=1 ∨ f= -1)
    (hs : s=e*A^2) (hs' : s^2-3*t^2=e*B^2)
    (ht : t=f*C^2) (ht' : t^2-3*s^2=f*D^2) : False := by
  let signSquare (q : ZMod 8) : Bool := q==0 || q==1 || q==4 || q==7
  have tab₁ : ∀ e x : ZMod 8, (e=1 ∨ e= -1) → signSquare (e*x^2) := by
    dsimp [signSquare]; decide +kernel
  have good {m e x : ℤ} (me : m=e*x^2) (sign : e=1 ∨ e= -1) : signSquare (m:ZMod 8) := by
    rw [me]; push_cast
    apply tab₁
    rcases sign with rfl|rfl <;> norm_num
  have gs := good hs he
  have gt := good ht hf
  have gs' := good hs' he
  have gt' := good ht' hf
  push_cast at gs' gt'
  have tab₂ : ∀ s t : ZMod 8, (signSquare s && signSquare t && signSquare (s^2-3*t^2) &&
      signSquare (t^2-3*s^2))=true → s.val%2=0 ∧ t.val%2=0 := by
    dsimp only [signSquare]; decide +kernel
  have ev := tab₂ (s:ZMod 8) (t:ZMod 8) (by simp only [gs,gt,gs',gt',Bool.and_self])
  have tab₃ : ∀ s t u v : ZMod 8, s.val%2=0 → t.val%2=0 → u*s+v*t≠1 := by decide +kernel
  obtain ⟨u,v,bez⟩ := cop.map (Int.castRingHom (ZMod 8))
  exact tab₃ _ _ u v ev.1 ev.2 bez

private theorem primitive_parameters_impossible {s t a b : ℤ} (cop : IsCoprime s t)
    (s3 : ¬3 ∣ s) (an : a≠0) (bn : b≠0)
    (ha : a^2=s*(s^2-3*t^2)) (hb : b^2=t*(t^2-3*s^2)) : False := by
  obtain ⟨e,A,B,he,hs,hs'⟩ := split_square (cube_factor_coprime cop s3) ha.symm an
  by_cases td : (3:ℤ) ∣ t
  · obtain ⟨T,hT⟩ := td
    have p3 : Prime (3:ℤ) := by norm_num
    have bd := p3.dvd_of_dvd_pow (show 3 ∣ b^2 from hb ▸ ⟨T*(t^2-3*s^2),by rw [hT]; ring⟩)
    obtain ⟨b',hb'⟩ := bd
    have bn' : b'≠0 := by rintro rfl; simp_all
    have eqn : T*(3*T^2-s^2)=b'^2 := by
      rw [hT,hb'] at hb
      nlinarith only [hb]
    obtain ⟨u,v,bez⟩ := cop
    have tc : IsCoprime T s := ⟨3*v,u,by rw [hT] at bez; linear_combination bez⟩
    obtain ⟨M,N,comb⟩ := tc.pow_right (n:=2)
    have small : IsCoprime T (3*T^2-s^2) := ⟨M+3*N*T,-N,by linear_combination comb⟩
    obtain ⟨f,P,Q,hf,hP,hQ⟩ := split_square small eqn bn'
    have neg : f= -1 := by
      rcases hf with pos|neg
      · rw [pos,one_mul] at hQ
        have v3 := congrArg (fun k : ℤ => (k:ZMod 3)) hQ
        push_cast at v3
        have table : ∀ T s Q : ZMod 3, 3*T^2-s^2=Q^2 → s=0 := by decide +kernel
        exact (s3 ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (table _ _ _ v3))).elim
      · exact neg
    rw [neg,neg_one_mul] at hP hQ
    have eq₄ : A^4=3*P^4+Q^2 := by
      rw [hs,hP] at hQ
      rcases he with rfl|rfl <;> linear_combination -hQ
    have primitive : IsCoprime A P := by
      rw [hs,hT,hP] at bez
      exact ⟨u*e*A,-3*v*P,by linear_combination bez⟩
    have apos : A≠0 := by rintro rfl; simp_all
    have ppos : P≠0 := by rintro rfl; simp_all
    have nat₄ : A.natAbs^4=3*P.natAbs^4+Q.natAbs^2 := by
      zify
      simpa only [show (4:ℕ)=2*2 by decide,pow_mul,sq_abs] using eq₄
    exact no_lucas_quartic _ _ _ (Int.natAbs_pos.mpr apos) (Int.natAbs_pos.mpr ppos)
      (Int.isCoprime_iff_nat_coprime.mp primitive) nat₄
  · obtain ⟨f,C,D,hf,ht,ht'⟩ := split_square (cube_factor_coprime cop.symm td) hb.symm bn
    exact two_unit_factors cop he hf hs hs' ht ht'

/-- Two coprime nonzero fourth powers never sum to a cube. -/
theorem fourth_powers_not_cube {a b c : ℕ} (ha : 0<a) (hb : 0<b) (cop : a.Coprime b) :
    a^4+b^4 ≠ c^3 := by
  intro eqn
  obtain ⟨s,t,h,ea,eb⟩ := gaussian_parameters cop eqn
  have an : (a:ℤ)≠0 := by exact_mod_cast ha.ne'
  have bn : (b:ℤ)≠0 := by exact_mod_cast hb.ne'
  by_cases h₃ : (3:ℤ) ∣ s
  · have nt : ¬(3:ℤ) ∣ t := by
      intro d
      have e := h.isRelPrime h₃ d
      rcases Int.isUnit_iff.mp e with e|e <;> norm_num at e
    exact primitive_parameters_impossible h.symm nt bn an eb ea
  · exact primitive_parameters_impossible h h₃ an bn ea eb

end BealQuartic

namespace BealQuartic

private theorem coprime_sum_gap {a b d : ℕ} (h : a=b+d) (cop : a.Coprime b)
    (odd : (a+b)%2=1) : (a+b).Coprime d := by
  apply Nat.coprime_of_dvd
  intro p pp ps pd
  have pb2 : p ∣ 2*b := (Nat.dvd_add_iff_left pd).mpr
    (show p ∣ 2*b+d from (show a+b=2*b+d by omega) ▸ ps)
  rcases pp.dvd_mul.mp pb2 with htwo|pb
  · have ptwo := (Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp htwo
    have := Nat.mod_eq_zero_of_dvd (ptwo ▸ ps : 2 ∣ a+b)
    omega
  · exact pp.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd (h ▸ dvd_add pb pd) pb)

private theorem coprime_powers {a b t n : ℕ} (cop : a.Coprime b) (h : a*b=t^n) :
    ∃ x y : ℕ, a=x^n ∧ b=y^n := by
  obtain ⟨x,y,hx,hy⟩ := split_factors cop (by decide : 0<1) (by decide : 0<1)
    (one_dvd _) (one_dvd _) (by simpa using h : a*b=1*1*t^n)
  exact ⟨x,y,by simpa using hx,by simpa using hy⟩

private theorem odd_sum_squares {a b : ℕ} (odd : (a+b)%2=1) : (a^2+b^2)%2=1 := by
  have residue : ∀ x y : ZMod 2, x+y=1 → x^2+y^2=1 := by decide +kernel
  have mod1 : ((a+b:ℕ):ZMod 2)=1 := (ZMod.val_injective 2) odd
  push_cast at mod1
  have hsq : ((a^2+b^2:ℕ):ZMod 2)=1 := by push_cast; exact residue _ _ mod1
  exact congrArg ZMod.val hsq

private theorem odd_difference_factors {a b c n : ℕ} (hb : 0<b) (hlt : b<a)
    (cop : a.Coprime b) (odd : (a+b)%2=1) (hn : 0<n) (eqn : a^4=b^4+c^n) :
    ∃ u v w : ℕ, 0<v ∧ v<u ∧ 0<w ∧ u.Coprime v ∧ (u^2)^n+(v^2)^n=2*w^n := by
  let d := a-b
  have ad : a=b+d := by dsimp [d]; omega
  have asq : a^2=b^2+(a+b)*d := by nth_rw 1 [ad]; rw [ad]; ring
  have cop_sq := coprime_sum_gap asq ((cop.pow_left 2).pow_right 2) (odd_sum_squares odd)
  have prod : (a^2+b^2)*((a+b)*d)=c^n := by
    have eq4 : (a^2)^2=(b^2)^2+c^n := by simpa only [←pow_mul] using eqn
    rw [asq] at eq4 ⊢
    nlinarith only [eq4]
  obtain ⟨w,t,hw,ht⟩ := coprime_powers cop_sq prod
  have csum := coprime_sum_gap ad cop odd
  obtain ⟨u,v,hu,hv⟩ := coprime_powers csum ht
  have vp : 0<v := by
    by_contra! vz
    have vz' : v=0 := by omega
    rw [vz',zero_pow hn.ne'] at hv
    omega
  have vu : v<u := (Nat.pow_lt_pow_iff_left hn.ne').mp (by omega)
  have wp : 0<w := by
    by_contra! wz
    have : w=0 := by omega
    rw [this,zero_pow hn.ne'] at hw
    have := Nat.pow_pos (n:=2) hb
    omega
  have cuv : u.Coprime v := Nat.Coprime.coprime_dvd_right (hv ▸ dvd_pow_self v hn.ne')
    (Nat.Coprime.coprime_dvd_left (hu ▸ dvd_pow_self u hn.ne') csum)
  refine ⟨u,v,w,vp,vu,wp,cuv,?_⟩
  rw [←pow_mul,←pow_mul,Nat.mul_comm 2 n,pow_mul,pow_mul,←hu,←hv,←hw,ad]
  ring

private theorem coprime_with_squares {u v : ℕ} (cop : u.Coprime v) :
    u.Coprime (u^2+v^2) := by
  apply Nat.coprime_of_dvd
  intro p pp pu ps
  have dv := pp.dvd_of_dvd_pow ((Nat.dvd_add_iff_right (dvd_pow pu (by decide : 2≠0))).mpr ps)
  exact pp.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd pu dv)

/-- When the base of the right-hand power is even, the odd and even halves of the two bases'
sum and difference, and the sum of their squares, are pairwise coprime. -/
private theorem even_difference_factors {a b c k : ℕ} (hlt : b<a) (cop : a.Coprime b)
    (ao : a%2=1) (bo : b%2=1) (eqn : a^4=b^4+c^(k+3)) :
    ∃ u v w : ℕ, 0<u ∧ 0<v ∧ 0<w ∧ u.Coprime v ∧
      (u^2)^(k+3)+(2^k)^2*(v^2)^(k+3)=w^(k+3) := by
  obtain ⟨U,V,vpos,ha,hu,uv⟩ := halves ao bo hlt cop
  have prod : 8*(U*V*(U^2+V^2))=c^(k+3) := by
    rw [ha,hu] at eqn
    rw [hu]; nlinarith only [eqn]
  have ce : 2∣c := Nat.prime_two.dvd_of_dvd_pow (prod ▸ dvd_mul_of_dvd_left (by decide : 2∣8) _)
  obtain ⟨t,ct⟩ := ce
  have product : U*V*(U^2+V^2)=2^k*t^(k+3) := by
    rw [ct,mul_pow,pow_add (2:ℕ)] at prod
    norm_num at prod
    nlinarith only [prod]
  have choose (E O : ℕ) (co : E.Coprime O) (ep : 0<E) (op : 0<O)
      (oo : O%2=1) (wo : (E^2+O^2)%2=1)
      (h : E*O*(E^2+O^2)=2^k*t^(k+3)) :
      ∃ u v w : ℕ, 0<u ∧ 0<v ∧ 0<w ∧ u.Coprime v ∧
        (u^2)^(k+3)+(2^k)^2*(v^2)^(k+3)=w^(k+3) := by
    let W := E^2+O^2
    have ew : E.Coprime W := coprime_with_squares co
    have ow : O.Coprime W := by simpa only [W,Nat.add_comm] using (coprime_with_squares co.symm)
    have eoW := co.mul_right ew
    have owodd : (O*W)%2=1 := by rw [Nat.mul_mod,oo,show W%2=1 from wo]
    have moved : E*(O*W)=2^k*t^(k+3) := by simpa only [W,mul_assoc] using h
    have d : 2^k∣E := ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr owodd)).symm.pow_left k).dvd_of_dvd_mul_right
      (moved ▸ dvd_mul_right _ _)
    obtain ⟨v,s,ev,os⟩ := split_factors eoW (by positivity : 0<2^k) (by decide : 0<1)
      d (one_dvd _) (by simpa using moved : E*(O*W)=2^k*1*t^(k+3))
    rw [one_mul] at os
    obtain ⟨u,w,ou,ww⟩ := coprime_powers ow os
    have hn : k+3≠0 := by omega
    have up : 0<u := by
      by_contra! uz
      have uz' : u=0 := by omega
      rw [uz',zero_pow hn] at ou
      omega
    have vp : 0<v := by
      by_contra! vz
      have vz' : v=0 := by omega
      rw [vz',zero_pow hn,mul_zero] at ev
      omega
    have wp : 0<w := by
      by_contra! wz
      have : w=0 := by omega
      rw [this,zero_pow hn] at ww
      dsimp [W] at ww
      have := Nat.pow_pos (n:=2) ep
      omega
    have vdvd : v∣E := ev ▸ (dvd_pow_self v hn).trans (dvd_mul_left _ _)
    have cuv := Nat.Coprime.coprime_dvd_right vdvd
      (Nat.Coprime.coprime_dvd_left (ou ▸ dvd_pow_self u hn) co.symm)
    refine ⟨u,v,w,up,vp,wp,cuv,?_⟩
    rw [←ww]
    dsimp [W]
    have swap (j : ℕ) : (j^2)^(k+3)=(j^(k+3))^2 := by rw [←pow_mul,←pow_mul,Nat.mul_comm 2]
    rw [ev,ou,mul_pow,swap u,swap v,Nat.add_comm]
  have sumOdd : (U+V)%2=1 := ha ▸ ao
  have wOdd := odd_sum_squares sumOdd
  by_cases vodd : V%2=1
  · exact choose U V uv (by omega) vpos vodd wOdd product
  · exact choose V U uv.symm vpos (by omega) (by omega)
      (by simpa only [Nat.add_comm (V^2) (U^2)] using wOdd)
      (by simpa only [Nat.mul_comm V U,Nat.add_comm (V^2) (U^2)] using product)

/-- A primitive positive difference of fourth powers equal to an n-th power,
n ≥ 3, gives either a progression of n-th powers or a sum with coefficient
4^(n−3). Both auxiliary bases in the sum are squares. -/
theorem fourth_power_difference_shapes {a b c n : ℕ} (hb : 0<b) (hc : 0<c)
    (hn : 3≤n) (cop : a.Coprime b) (eqn : a^4=b^4+c^n) :
    (∃ u v w : ℕ, 0<v ∧ v<u ∧ 0<w ∧ u.Coprime v ∧ (u^2)^n+(v^2)^n=2*w^n) ∨
    (∃ u v w : ℕ, 0<u ∧ 0<v ∧ 0<w ∧ u.Coprime v ∧
      (u^2)^n+(2^(n-3))^2*(v^2)^n=w^n) := by
  have hlt : b<a := (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp (by
    have := Nat.pow_pos (n:=n) hc
    omega)
  by_cases odd : (a+b)%2=1
  · exact Or.inl (odd_difference_factors hb hlt cop odd (by omega) eqn)
  have ao : a%2=1 := by
    by_contra bad
    apply Nat.prime_two.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd (by omega) (by omega))
  have bo : b%2=1 := by omega
  have e : n=n-3+3 := by omega
  have r := even_difference_factors hlt cop ao bo (k:=n-3) (by rwa [←e])
  exact Or.inr (by simpa only [←e] using r)

theorem difference_of_fourth_powers {a b c : ℕ}
    (euler : ∀ x y z : ℤ, x^3+y^3=2*z^3 → x=y ∨ z=0)
    (hb : 0<b) (hc : 0<c) (cop : a.Coprime b) : a^4≠b^4+c^3 := by
  intro eqn
  rcases fourth_power_difference_shapes hb hc (by decide : 3≤3) cop eqn with
    ⟨u,v,w,vp,vu,wp,_,he⟩|⟨u,v,w,up,vp,wp,_,he⟩
  · have hz : ((u^2:ℕ):ℤ)^3+((v^2:ℕ):ℤ)^3=2*(w:ℤ)^3 := by exact_mod_cast he
    rcases euler _ _ _ hz with equal|zero
    · have squares : u^2=v^2 := by exact_mod_cast equal
      exact vu.ne ((Nat.pow_left_inj (by decide : 2≠0)).mp squares).symm
    · have wz : w=0 := by exact_mod_cast zero
      omega
  · apply fermatLastTheoremThree (u^2) (v^2) w (by positivity) (by positivity) wp.ne'
    simpa using he

end BealQuartic

namespace EulerCubes

open NumberField IsCyclotomicExtension.Rat.Three

/- Euler’s three-cubes theorem. The descent is due to Aaron Belinski in
open-math-agents PR 1271 (commit fee54a870fa1d00b89a13c9edfe740c32f10f50b).
The field and its instances are local to the lemma which uses them. -/

/-- A primitive cube norm in the Eisenstein integers gives these two
integer cube coordinates. -/
theorem lemma_L {s t b : ℤ} (hc : IsCoprime s (3 * t)) (hpar : Odd (s + t))
    (hb : s ^ 2 + 3 * t ^ 2 = b ^ 3) :
    ∃ u v : ℤ, s = u ^ 3 - 9 * u * v ^ 2 ∧ t = 3 * u ^ 2 * v - 3 * v ^ 3 := by
  let K3 := CyclotomicField 3 ℚ

  let : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

  let : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

  let : IsPrincipalIdealRing (𝓞 K3) := IsCyclotomicExtension.Rat.three_pid K3

  have hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K3) 3 :=
    IsCyclotomicExtension.zeta_spec 3 ℚ K3

  let ω : 𝓞 K3 := hζ3.toInteger

  have ω_sq : ω ^ 2 = -ω - 1 := eta_sq hζ3

  have ω_cube : ω ^ 3 = 1 := hζ3.toInteger_cube_eq_one

  have coord_zero {a b : ℤ} (h : (a : 𝓞 K3) + b * ω = 0) : a = 0 ∧ b = 0 := by
    have hn : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K3) = 0 := by
      have : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K3) = ((a : 𝓞 K3) + b * ω) * (a + b * ω ^ 2) := by
        push_cast
        linear_combination (-(b : 𝓞 K3) ^ 2 * ω - (a : 𝓞 K3) * b + (b : 𝓞 K3) ^ 2) * ω_sq
      rw [this, h, zero_mul]
    have hz : a ^ 2 - a * b + b ^ 2 = 0 := by exact_mod_cast hn
    constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

  have coord_eq {a b c d : ℤ} (h : (a : 𝓞 K3) + b * ω = c + d * ω) : a = c ∧ b = d := by
    have := coord_zero (a := a - c) (b := b - d) (by push_cast; linear_combination h)
    omega

  have exists_coord (x : 𝓞 K3) : ∃ a b : ℤ, x = a + b * ω := by
    obtain ⟨f, rfl⟩ := hζ3.integralPowerBasis.exists_eq_aeval' x
    rw [IsPrimitiveRoot.integralPowerBasis_gen]
    induction f using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, b, ha⟩ := hp
      obtain ⟨c, d, hc⟩ := hq
      exact ⟨a + c, b + d, by rw [map_add, ha, hc]; push_cast; ring⟩
    | monomial n c =>
      rw [Polynomial.aeval_monomial]
      induction n with
      | zero => exact ⟨c, 0, by simp⟩
      | succ n ih =>
        obtain ⟨a, b, hab⟩ := ih
        refine ⟨-b, a - b, ?_⟩
        rw [pow_succ, ← mul_assoc, hab]
        push_cast
        linear_combination (b : 𝓞 K3) * ω_sq

  let r3 : 𝓞 K3 := 1 + 2 * ω

  have r3_sq : r3 ^ 2 = -3 := by
    linear_combination 4 * ω_sq

  set ρ : 𝓞 K3 := s + t * r3 with hρ
  set ρ' : 𝓞 K3 := s - t * r3 with hρ'
  have hprod : ρ * ρ' = (b : 𝓞 K3) ^ 3 := by
    have : ((s ^ 2 + 3 * t ^ 2 : ℤ) : 𝓞 K3) = ((b ^ 3 : ℤ) : 𝓞 K3) := by rw [hb]
    push_cast at this
    rw [← this, hρ, hρ']
    linear_combination (-(t : 𝓞 K3) ^ 2) * r3_sq
  -- coprimality of ρ and ρ'
  have hcop : IsCoprime ρ ρ' := by
    have h3 : IsCoprime s 3 := hc.of_mul_right_left
    have ht : IsCoprime s t := hc.of_mul_right_right
    have hA : IsCoprime (s ^ 2 + 3 * t ^ 2) s := by
      have : IsCoprime (3 * t ^ 2) s := (h3.mul_right ht.pow_right).symm
      have e : s ^ 2 + 3 * t ^ 2 = 3 * t ^ 2 + s * s := by ring
      rw [e]; exact this.add_mul_left_left s
    have hB : IsCoprime (s ^ 2 + 3 * t ^ 2) 2 := by
      obtain ⟨k, hk⟩ := hpar
      refine ⟨1, -(2 * k ^ 2 + 2 * k - 2 * k * t - t + 2 * t ^ 2), ?_⟩
      have : s = 2 * k + 1 - t := by omega
      rw [this]; ring
    obtain ⟨A, B, hAB⟩ := hA.mul_right hB
    refine ⟨A * ρ' + B, B, ?_⟩
    have : ((A * (s ^ 2 + 3 * t ^ 2) + B * (s * 2) : ℤ) : 𝓞 K3) = 1 := by rw [hAB]; simp
    push_cast at this
    rw [← this, hρ, hρ']
    linear_combination (-(A : 𝓞 K3) * (t : 𝓞 K3) ^ 2) * r3_sq
  obtain ⟨γ0, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  -- ρ = ± ω ^ k * γ0 ^ 3
  have hunit : ∃ k ∈ ({0, 1, 2} : Finset ℕ), ∃ γ1 : 𝓞 K3, ρ = ω ^ k * γ1 ^ 3 := by
    have hm := Units.mem hζ3 u0
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> subst h
    · exact ⟨0, by simp, γ0, by rw [← hu0]; simp⟩
    · exact ⟨0, by simp, -γ0, by rw [← hu0]; simp; ring⟩
    · exact ⟨1, by simp, γ0, by rw [← hu0]; simp; ring⟩
    · exact ⟨1, by simp, -γ0, by rw [← hu0]; simp; ring⟩
    · exact ⟨2, by simp, γ0, by rw [← hu0]; simp; ring⟩
    · exact ⟨2, by simp, -γ0, by rw [← hu0]; simp; ring⟩
  obtain ⟨k, hk, γ1, hγ1⟩ := hunit
  -- normalise γ1 to have even ω-coordinate
  obtain ⟨c, d, hcd⟩ := exists_coord γ1
  have hnorm : ∃ u v : ℤ, γ1 ^ 3 = (u + v * r3) ^ 3 := by
    rcases Int.even_or_odd d with ⟨v, hv⟩ | hd
    · exact ⟨c - v, v, by rw [hcd, hv]; push_cast; ring⟩
    · rcases Int.even_or_odd c with ⟨w, hw⟩ | hco
      · -- ω^2 γ1 = (d - c) + (-c) ω, and -c is even
        refine ⟨d - c + w, -w, ?_⟩
        have : γ1 ^ 3 = (ω ^ 2 * γ1) ^ 3 := by
          rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ω_cube]; ring
        rw [this, hcd, hw]
        push_cast
        have e2 : ω ^ 2 * ((c : 𝓞 K3) + d * ω) = (d - c) + (-c) * ω := by
          linear_combination (c : 𝓞 K3) * ω_sq + (d : 𝓞 K3) * ω_cube
        rw [hw] at e2; push_cast at e2
        rw [e2]; ring
      · -- ω γ1 = -d + (c - d) ω, and c - d is even
        obtain ⟨w, hw⟩ : Even (c - d) := by
          rcases hco with ⟨i, hi⟩; rcases hd with ⟨j, hj⟩; exact ⟨i - j, by omega⟩
        refine ⟨-d - w, w, ?_⟩
        have : γ1 ^ 3 = (ω * γ1) ^ 3 := by rw [mul_pow, ω_cube, one_mul]
        rw [this, hcd]
        have e1 : ω * ((c : 𝓞 K3) + d * ω) = -d + ((c - d : ℤ) : 𝓞 K3) * ω := by
          push_cast; linear_combination (d : 𝓞 K3) * ω_sq
        rw [e1, hw]; push_cast; ring
  obtain ⟨u, v, huv⟩ := hnorm
  rw [huv] at hγ1
  set P := u ^ 3 - 9 * u * v ^ 2 with hP
  set Q := 3 * u ^ 2 * v - 3 * v ^ 3 with hQ
  have hcube : ((u : 𝓞 K3) + v * r3) ^ 3 = P + Q * r3 := by
    rw [hP, hQ]; push_cast
    linear_combination (3 * (u : 𝓞 K3) * v ^ 2 + (v : 𝓞 K3) ^ 3 * r3) * r3_sq
  rw [hcube] at hγ1
  -- compare coordinates in each case
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · refine ⟨u, v, ?_⟩
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((P + Q : ℤ) : 𝓞 K3) + ((2 * Q : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1
    have := coord_eq h0
    constructor <;> omega
  · exfalso
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((-2 * Q : ℤ) : 𝓞 K3) + ((P - Q : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1 + 2 * (Q : 𝓞 K3) * ω_sq
    have := coord_eq h0
    obtain ⟨k, hk⟩ := hpar
    omega
  · exfalso
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((Q - P : ℤ) : 𝓞 K3) + ((-(P + Q) : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1 + ((P : 𝓞 K3) + Q) * ω_sq + 2 * (Q : 𝓞 K3) * ω_cube
    have := coord_eq h0
    obtain ⟨k, hk⟩ := hpar
    omega

/-- If `u ^ 3 - 9 u v ^ 2 + 3 u ^ 2 v - 3 v ^ 3` is odd then `u + v` is odd. -/
lemma odd_add_of_odd_PQ {u v : ℤ}
    (h : Odd (u ^ 3 - 9 * u * v ^ 2 + (3 * u ^ 2 * v - 3 * v ^ 3))) : Odd (u + v) := by
  rcases Int.even_or_odd (u + v) with ⟨m, hm⟩ | ho
  · exfalso
    have hu : u = 2 * m - v := by omega
    rw [← Int.not_even_iff_odd] at h
    apply h
    exact ⟨4 * m ^ 3 - 12 * m * v ^ 2 + 4 * v ^ 3, by rw [hu]; ring⟩
  · exact ho

lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

lemma cube_left {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 3) : ∃ d, a = d ^ 3 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

lemma natAbs_le_of_mul {a b : ℤ} (hb : b ≠ 0) : a.natAbs ≤ (a * b).natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hb)

theorem euler_aux (n : ℕ) : ∀ x y z : ℤ, z.natAbs = n → x ^ 3 + y ^ 3 = 2 * z ^ 3 → x ≠ y →
    z ≠ 0 → False := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn h hxy hz
  have ih' : ∀ a b c : ℤ, a ^ 3 + b ^ 3 = 2 * c ^ 3 → a ≠ b → c ≠ 0 →
      c.natAbs < z.natAbs → False :=
    fun a b c h1 h2 h3 h4 => ih _ (hn ▸ h4) a b c rfl h1 h2 h3
  clear ih hn
  -- Step A: x and y coprime
  have hcop : IsCoprime x y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpz : (p : ℤ) ∣ z := by
      have h3 : (p : ℤ) ^ 3 ∣ 2 * z ^ 3 := ⟨x1 ^ 3 + y1 ^ 3, by rw [← h]; ring⟩
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpp.dvd_or_dvd (dvd_trans (dvd_pow_self _ (by norm_num)) h3) with h2 | h2
      · -- p ∣ 2, so p = 2
        have hp2 : p = 2 := by
          have : p ∣ 2 := by exact_mod_cast h2
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
        subst hp2
        obtain ⟨k, hk⟩ := h3
        push_cast at hk ⊢
        have : (2 : ℤ) ∣ z ^ 3 := ⟨2 * k, by linarith⟩
        exact Int.prime_two.dvd_of_dvd_pow this
      · exact hpp.dvd_of_dvd_pow h2
    obtain ⟨z1, rfl⟩ := hpz
    have h1 : x1 ^ 3 + y1 ^ 3 = 2 * z1 ^ 3 := by
      have hp3 : (p : ℤ) ^ 3 ≠ 0 := pow_ne_zero _ hp0
      apply mul_left_cancel₀ hp3
      linear_combination h
    apply ih' x1 y1 z1 h1 (fun e => hxy (by rw [e])) (fun e => hz (by rw [e, mul_zero]))
    have hz1 : z1.natAbs ≠ 0 := by
      intro h0; apply hz; simp [Int.natAbs_eq_zero.mp h0]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_left (Nat.pos_of_ne_zero hz1) hp.one_lt
  -- Step B: x, y odd; write x = s + t, y = s - t
  have hxy_even : Even (x + y) := by
    have h2 : Even (x ^ 3 + y ^ 3) := ⟨z ^ 3, by rw [h]; ring⟩
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at h2
    rw [Int.even_add]; exact h2
  obtain ⟨s, hs⟩ := hxy_even
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by
        obtain ⟨r, hr⟩ := hx
        exact ⟨s - r, by omega⟩
      have h2 := Int.isCoprime_iff_gcd_eq_one.mp hcop
      have : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx.two_dvd hy.two_dvd
      rw [h2] at this; norm_num at this
    · exact hx
  set t := x - s with ht
  have hx' : x = s + t := by omega
  have hy' : y = s - t := by omega
  have hpar : Odd (s + t) := by rw [← hx']; exact hxodd
  have ht0 : t ≠ 0 := by intro h0; apply hxy; omega
  have heq : s * (s ^ 2 + 3 * t ^ 2) = z ^ 3 := by
    have : (s + t) ^ 3 + (s - t) ^ 3 = 2 * z ^ 3 := by rw [← hx', ← hy']; exact h
    linarith [this]
  have hs0 : s ≠ 0 := by
    intro h0; apply hz; rw [h0, zero_mul] at heq; exact pow_eq_zero_iff (by norm_num) |>.mp heq.symm
  have hst : IsCoprime s t := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx', hy']; ring⟩
  have hM3 : 3 ≤ (s ^ 2 + 3 * t ^ 2).natAbs := by
    have : 0 < t ^ 2 := by positivity
    have : 3 ≤ s ^ 2 + 3 * t ^ 2 := by nlinarith [sq_nonneg s]
    omega
  by_cases h3s : (3 : ℤ) ∣ s
  · -- Case 2: 3 ∣ s
    obtain ⟨s', rfl⟩ := h3s
    have h3t : IsCoprime t 3 := by
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd Int.prime_three]
      intro h3; exact Int.prime_three.not_isUnit (hst.isUnit_of_dvd' (dvd_mul_right 3 s') h3)
    have hs't : IsCoprime s' t := hst.of_mul_left_right
    have h3z : (3 : ℤ) ∣ z := by
      apply Int.prime_three.dvd_of_dvd_pow (n := 3)
      exact ⟨s' * (9 * s' ^ 2 + 3 * t ^ 2), by rw [← heq]; ring⟩
    obtain ⟨w, rfl⟩ := h3z
    set M := t ^ 2 + 3 * s' ^ 2 with hM
    have hw : s' * M = 3 * w ^ 3 := by
      have : 27 * (s' * M) = 27 * (3 * w ^ 3) := by rw [hM]; linear_combination 3 * heq
      linarith
    have hM3' : ¬ (3 : ℤ) ∣ M := by
      intro h3
      have : (3 : ℤ) ∣ t ^ 2 := by
        have := dvd_sub h3 (dvd_mul_right 3 (s' ^ 2)); rwa [hM, add_sub_cancel_right] at this
      have := Int.prime_three.dvd_of_dvd_pow this
      exact Int.prime_three.not_isUnit (h3t.isUnit_of_dvd' this (dvd_refl 3))
    have h3s' : (3 : ℤ) ∣ s' := by
      rcases Int.prime_three.dvd_or_dvd (⟨w ^ 3, hw⟩ : (3 : ℤ) ∣ s' * M) with h | h
      · exact h
      · exact absurd h hM3'
    obtain ⟨s'', rfl⟩ := h3s'
    have hw' : s'' * M = w ^ 3 := by linarith [hw]
    have hs''M : IsCoprime s'' M := by
      have : IsCoprime s'' t := hs't.of_mul_left_right
      have h1 : IsCoprime s'' (t ^ 2) := this.pow_right
      have e : M = t ^ 2 + s'' * (27 * s'') := by rw [hM]; ring
      rw [e]; exact h1.add_mul_left_right _
    obtain ⟨c, hc⟩ := cube_left hs''M hw'
    obtain ⟨b, hb⟩ := cube_left hs''M.symm (by rw [mul_comm]; exact hw')
    have hL1 : IsCoprime t (3 * (3 * s'')) := h3t.mul_right hs't.symm
    have hL2 : Odd (t + 3 * s'') := by
      have : t + 3 * s'' = 3 * (3 * s'') + t - 2 * (3 * s'') := by ring
      rw [this]
      obtain ⟨k, hk⟩ := hpar
      exact ⟨k - 3 * s'', by omega⟩
    obtain ⟨u, v, hu, hv⟩ := lemma_L hL1 hL2 (by have := hb; rw [hM] at this; exact this)
    have hvc : v * ((u - v) * (u + v)) = c ^ 3 := by
      rw [← hc]
      have : 3 * (v * ((u - v) * (u + v))) = 3 * s'' := by linear_combination -hv
      omega
    have huv : IsCoprime u v := by
      have h1 : IsCoprime t (3 * s'') := hs't.symm
      rw [hu, hv] at h1
      have e1 : u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) := by ring
      have e2 : 3 * u ^ 2 * v - 3 * v ^ 3 = v * (3 * u ^ 2 - 3 * v ^ 2) := by ring
      rw [e1, e2] at h1
      exact h1.of_mul_left_left.of_mul_right_left
    have hodd : Odd (u + v) := by
      have h1 := hL2
      rw [hu, hv] at h1
      exact odd_add_of_odd_PQ h1
    have hvm : IsCoprime v (u - v) := by
      have e : u - v = u + v * (-1) := by ring
      rw [e]; exact huv.symm.add_mul_left_right _
    have hvp : IsCoprime v (u + v) := by
      have e : u + v = u + v * 1 := by ring
      rw [e]; exact huv.symm.add_mul_left_right _
    have hmp : IsCoprime (u - v) (u + v) := by
      have h2 : IsCoprime (u - v) 2 := isCoprime_two_of_odd (by
        obtain ⟨k, hk⟩ := hodd; exact ⟨k - v, by omega⟩)
      have h2v : IsCoprime (u - v) (2 * v) := h2.mul_right hvm.symm
      have e : u + v = 2 * v + (u - v) * 1 := by ring
      rw [e]; exact h2v.add_mul_left_right _
    obtain ⟨γ, hγ⟩ := cube_left (hvm.mul_right hvp) hvc
    obtain ⟨α, hα⟩ := cube_left (hmp.mul_right hvm.symm) (by rw [← hvc]; ring)
    obtain ⟨β, hβ⟩ := cube_left (hmp.symm.mul_right hvp.symm) (by rw [← hvc]; ring)
    have hv0 : v ≠ 0 := by
      intro h0; apply hs0; rw [h0] at hv; linarith [hv]
    have hu0 : u ≠ 0 := by
      intro h0; apply ht0; rw [hu, h0]; ring
    have hγ0 : γ ≠ 0 := by rintro rfl; apply hv0; rw [hγ]; ring
    apply ih' β (-α) γ (by linear_combination -hβ + hα + 2 * hγ) ?_ hγ0 ?_
    · intro e
      apply hu0
      have : β ^ 3 = -(α ^ 3) := by rw [e]; ring
      linarith [hα, hβ, this]
    · -- |γ| ≤ |c| ≤ |w| < 3 |w| = |z|
      have hc0 : c ≠ 0 := by
        rintro rfl; apply hs0; rw [hc]; ring
      have hγc : γ.natAbs ^ 3 ≤ c.natAbs ^ 3 := by
        rw [← Int.natAbs_pow, ← Int.natAbs_pow, ← hγ, ← hvc]
        have hm : (u - v) * (u + v) ≠ 0 := by
          intro h0; apply hc0; have := hvc; rw [h0, mul_zero] at this
          exact pow_eq_zero_iff (by norm_num) |>.mp this.symm
        exact natAbs_le_of_mul hm
      have hγc' : γ.natAbs ≤ c.natAbs :=
        (Nat.pow_le_pow_iff_left (by norm_num)).mp hγc
      have hb0 : b ≠ 0 := by
        rintro rfl; have : M = 0 := by rw [hb]; ring
        rw [hM] at this; nlinarith [sq_pos_of_ne_zero ht0, sq_nonneg s'']
      have hwcb : w ^ 3 = (c * b) ^ 3 := by rw [mul_pow, ← hc, ← hb, hw']
      have hw : w.natAbs = c.natAbs * b.natAbs := by
        rw [← Int.natAbs_mul]
        have := congrArg Int.natAbs hwcb
        rw [Int.natAbs_pow, Int.natAbs_pow] at this
        exact Nat.pow_left_injective (by norm_num) this
      have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb0
      rw [Int.natAbs_mul]
      norm_num
      nlinarith [Int.natAbs_pos.mpr hc0]
  · -- Case 1: 3 ∤ s
    have h3 : IsCoprime s 3 := by
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd Int.prime_three]; exact h3s
    have hL1 : IsCoprime s (3 * t) := h3.mul_right hst
    have hsM : IsCoprime s (s ^ 2 + 3 * t ^ 2) := by
      have : IsCoprime s (3 * t ^ 2) := h3.mul_right hst.pow_right
      have e : s ^ 2 + 3 * t ^ 2 = 3 * t ^ 2 + s * s := by ring
      rw [e]; exact this.add_mul_left_right _
    obtain ⟨a, ha⟩ := cube_left hsM heq
    obtain ⟨b, hb⟩ := cube_left hsM.symm (by rw [mul_comm]; exact heq)
    obtain ⟨u, v, hu, hv⟩ := lemma_L hL1 hpar hb
    have huv : IsCoprime u v := by
      have h1 := hst
      rw [hu, hv] at h1
      have e1 : u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) := by ring
      have e2 : 3 * u ^ 2 * v - 3 * v ^ 3 = v * (3 * u ^ 2 - 3 * v ^ 2) := by ring
      rw [e1, e2] at h1
      exact h1.of_mul_left_left.of_mul_right_left
    have hu3 : IsCoprime u 3 := by
      have h1 := h3
      rw [hu, show u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) by ring] at h1
      exact h1.of_mul_left_left
    have hodd : Odd (u + v) := by
      apply odd_add_of_odd_PQ; rw [← hu, ← hv]; exact hpar
    have hsfac : s = u * ((u - 3 * v) * (u + 3 * v)) := by rw [hu]; ring
    have hu3v : IsCoprime u (3 * v) := hu3.mul_right huv
    have hum : IsCoprime u (u - 3 * v) := by
      have e : u - 3 * v = -(3 * v) + u * 1 := by ring
      rw [e]; exact hu3v.neg_right.add_mul_left_right _
    have hup : IsCoprime u (u + 3 * v) := by
      have e : u + 3 * v = 3 * v + u * 1 := by ring
      rw [e]; exact hu3v.add_mul_left_right _
    have hmp : IsCoprime (u - 3 * v) (u + 3 * v) := by
      have h2 : IsCoprime (u - 3 * v) 2 := isCoprime_two_of_odd (by
        obtain ⟨k, hk⟩ := hodd; exact ⟨k - 2 * v, by omega⟩)
      have h3' : IsCoprime (u - 3 * v) 3 := by
        have e : u - 3 * v = u + 3 * (-v) := by ring
        rw [e]; exact (hu3.symm.add_mul_left_right _).symm
      have hv' : IsCoprime (u - 3 * v) v := by
        have e : u - 3 * v = u + v * (-3) := by ring
        rw [e]; exact (huv.symm.add_mul_left_right _).symm
      have h6 : IsCoprime (u - 3 * v) (6 * v) := by
        have := (h2.mul_right h3').mul_right hv'
        convert this using 2; ring
      have e : u + 3 * v = 6 * v + (u - 3 * v) * 1 := by ring
      rw [e]; exact h6.add_mul_left_right _
    rw [hsfac] at ha
    obtain ⟨α, hα⟩ := cube_left (hum.mul_right hup) ha
    obtain ⟨β, hβ⟩ := cube_left (hmp.mul_right hum.symm) (by rw [← ha]; ring)
    obtain ⟨γ, hγ⟩ := cube_left (hmp.symm.mul_right hup.symm) (by rw [← ha]; ring)
    have hu0 : u ≠ 0 := by intro h0; apply hs0; rw [hsfac, h0, zero_mul]
    have hv0 : v ≠ 0 := by intro h0; apply ht0; rw [hv, h0]; ring
    have hα0 : α ≠ 0 := by rintro rfl; apply hu0; rw [hα]; ring
    apply ih' β γ α (by linear_combination -hβ - hγ + 2 * hα) ?_ hα0 ?_
    · intro e; apply hv0
      have : β ^ 3 = γ ^ 3 := by rw [e]
      linarith [hβ, hγ, this]
    · -- |α|^3 = |u| ≤ |s| < |z|^3
      have hm : (u - 3 * v) * (u + 3 * v) ≠ 0 := by
        intro h0; apply hs0; rw [hsfac, h0, mul_zero]
      have h1 : α.natAbs ^ 3 ≤ s.natAbs := by
        rw [← Int.natAbs_pow, ← hα, hsfac]; exact natAbs_le_of_mul hm
      have h2 : z.natAbs ^ 3 = s.natAbs * (s ^ 2 + 3 * t ^ 2).natAbs := by
        rw [← Int.natAbs_pow, ← heq, Int.natAbs_mul]
      have hs1 : 1 ≤ s.natAbs := Int.natAbs_pos.mpr hs0
      have h3' : α.natAbs ^ 3 < z.natAbs ^ 3 := by rw [h2]; nlinarith
      exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h3'

/-- Euler: `x ^ 3 + y ^ 3 = 2 z ^ 3` forces `x = y` or `z = 0`. -/
theorem euler_cubes (x y z : ℤ) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y ∨ z = 0 := by
  by_contra hc
  push Not at hc
  exact euler_aux _ x y z rfl h hc.1 hc.2

end EulerCubes

namespace BealQuartic

/-- A positive cube is never a difference of coprime positive fourth powers. -/
theorem fourth_powers_difference_not_cube {a b c : ℕ} (hb : 0<b) (hc : 0<c)
    (cop : a.Coprime b) : a^4≠b^4+c^3 :=
  difference_of_fourth_powers EulerCubes.euler_cubes hb hc cop

theorem coprime_pairs {a b c x y z : ℕ} (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (eqn : a^x+b^y=c^z) (none : ¬∃ p : ℕ, p.Prime ∧ p∣a ∧ p∣b ∧ p∣c) :
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c := by
  have ab : a.Coprime b := by
    apply Nat.coprime_of_dvd
    intro p pp pa pb
    exact none ⟨p,pp,pa,pb,pp.dvd_of_dvd_pow (eqn ▸ dvd_add (dvd_pow pa hx.ne') (dvd_pow pb hy.ne'))⟩
  have ac : a.Coprime c := by
    apply Nat.coprime_of_dvd
    intro p pp pa pc
    have d : p ∣ a^x+b^y := eqn ▸ dvd_pow pc hz.ne'
    exact none ⟨p,pp,pa,pp.dvd_of_dvd_pow ((Nat.dvd_add_iff_right (dvd_pow pa hx.ne')).mpr d),pc⟩
  have bc : b.Coprime c := by
    apply Nat.coprime_of_dvd
    intro p pp pb pc
    have d : p ∣ a^x+b^y := eqn ▸ dvd_pow pc hz.ne'
    exact none ⟨p,pp,pp.dvd_of_dvd_pow ((Nat.dvd_add_iff_left (dvd_pow pb hy.ne')).mpr d),pb,pc⟩
  exact ⟨ab,ac,bc⟩

/-- Every solution with two fourth-power terms and one cube has a common
prime divisor of the original bases. The cube can occupy any of the three positions. -/
theorem quartic_cube_common_prime {a b c x y z : ℕ}
    (ha : 0<a) (hb : 0<b) (_hc : 0<c) (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (powers : (4∣x ∧ 4∣y ∧ 3∣z) ∨ (4∣x ∧ 3∣y ∧ 4∣z) ∨ (3∣x ∧ 4∣y ∧ 4∣z))
    (eqn : a^x+b^y=c^z) : ∃ p : ℕ, p.Prime ∧ p∣a ∧ p∣b ∧ p∣c := by
  by_contra none
  obtain ⟨ab,ac,bc⟩ := coprime_pairs hx hy hz eqn none
  have rep {n q : ℕ} (dq : q∣n) : ∃ k : ℕ, n=k*q := by
    obtain ⟨k,e⟩ := dq
    exact ⟨k,e.trans (Nat.mul_comm ..)⟩
  rcases powers with ⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩
  all_goals
    obtain ⟨i,rfl⟩ := rep h₁
    obtain ⟨j,rfl⟩ := rep h₂
    obtain ⟨k,rfl⟩ := rep h₃
    simp only [pow_mul] at eqn
  · exact fourth_powers_not_cube (pow_pos ha i) (pow_pos hb j) (ab.pow i j) eqn
  · exact fourth_powers_difference_not_cube (pow_pos ha i) (pow_pos hb j) (ac.symm.pow k i) eqn.symm
  · exact fourth_powers_difference_not_cube (pow_pos hb j) (pow_pos ha i) (bc.symm.pow k j)
      (eqn.symm.trans (Nat.add_comm ..))

/-- Beal's common-divisor conclusion for this family, in the exact gcd form
used by the formal conjecture. -/
theorem beal_for_quartics_and_cube {a b c x y z : ℕ}
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hx : 2<x) (hy : 2<y) (hz : 2<z)
    (powers : (4∣x ∧ 4∣y ∧ 3∣z) ∨ (4∣x ∧ 3∣y ∧ 4∣z) ∨ (3∣x ∧ 4∣y ∧ 4∣z))
    (eqn : a^x+b^y=c^z) : 1 < Finset.gcd {a,b,c} id := by
  obtain ⟨p,pp,pa,pb,pc⟩ := quartic_cube_common_prime (Nat.pos_of_ne_zero ha)
    (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc) (by omega) (by omega) (by omega) powers eqn
  have divides : p ∣ Finset.gcd {a,b,c} id := by
    apply Finset.dvd_gcd
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl <;> assumption
  have pos : Finset.gcd {a,b,c} id ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨a,Finset.mem_insert_self _ _,ha⟩
  exact pp.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero pos) divides)

end BealQuartic

private theorem five_le {p : ℕ} (hp : p.Prime) (gt : 2<p) (h : p≠3) : 5≤p := by
  have ne : p≠4 := by rintro rfl; norm_num at hp
  omega

private theorem single_quartic (one : H1) {x y : ℤ} {w p q : ℕ}
    (hp : 2<p ∧ p.Prime) (hq : 2<q ∧ q.Prime)
    (hx : x≠0) (hy : y≠0) (hw : 0<w) (cop : IsCoprime x y) :
    x^p+y^q≠(w:ℤ)^4 := by
  intro eqn
  rcases le_total p q with ord|ord
  · exact one hp.2 hq.2 hp.1 ord hx hy hw cop eqn
  · exact one hq.2 hp.2 hq.1 ord hy hx hw cop.symm ((add_comm ..).trans eqn)

private theorem sum_quartics (summed : H2) {p a b c : ℕ} (hp : 2<p ∧ p.Prime)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (cop : a.Coprime b) : a^4+b^4≠c^p := by
  by_cases cube : p=3
  · subst p
    exact BealQuartic.fourth_powers_not_cube ha hb cop
  · exact summed hp.2 (five_le hp.2 hp.1 cube) ha hb hc cop

private theorem diff_quartics (ap : H3) (weighted : H4) {p a b c : ℕ}
    (hp : 2<p ∧ p.Prime) (hb : 0<b) (hc : 0<c) (cop : a.Coprime b) :
    a^4≠b^4+c^p := by
  by_cases cube : p=3
  · subst p
    exact BealQuartic.fourth_powers_difference_not_cube hb hc cop
  · intro eqn
    have large := five_le hp.2 hp.1 cube
    rcases BealQuartic.fourth_power_difference_shapes hb hc hp.1 cop eqn with
      ⟨u,v,w,vp,vu,wp,cp,h⟩|⟨u,v,w,up,vp,wp,cp,h⟩
    · exact ap hp.2 large vp vu wp cp h
    · exact weighted hp.2 large up vp wp cp h

theorem main : H1 → H2 → H3 → H4 → OMA.R_BealConjecture_beal_conjecture_R1.H2 := by
  intro single summed ap weighted a b c x y z ha hb hc hx hy hz four eqn
  by_contra none
  have xpos : 0<x := hx.elim (fun e => by omega) (fun h => by have := h.1; omega)
  have ypos : 0<y := hy.elim (fun e => by omega) (fun h => by have := h.1; omega)
  have zpos : 0<z := hz.elim (fun e => by omega) (fun h => by have := h.1; omega)
  obtain ⟨ab,ac,bc⟩ := BealQuartic.coprime_pairs xpos ypos zpos eqn none
  have an : (a:ℤ)≠0 := by exact_mod_cast ha
  have bn : (b:ℤ)≠0 := by exact_mod_cast hb
  have cn : (c:ℤ)≠0 := by exact_mod_cast hc
  have he : (a:ℤ)^x+(b:ℤ)^y=(c:ℤ)^z := by exact_mod_cast eqn
  rcases hx with rfl|px <;> rcases hy with rfl|py <;> rcases hz with rfl|pz
  · exact fermatLastTheoremFour a b c ha hb hc eqn
  · exact sum_quartics summed pz (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc) ab eqn
  · exact diff_quartics ap weighted py (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) ac.symm eqn.symm
  · apply single_quartic single py pz (neg_ne_zero.mpr bn) cn (Nat.pos_of_ne_zero ha) bc.isCoprime.neg_left
    rw [(py.2.odd_of_ne_two (by omega)).neg_pow]
    linear_combination -he
  · exact diff_quartics ap weighted px (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero ha) bc.symm
      (eqn.symm.trans (Nat.add_comm ..))
  · apply single_quartic single px pz (neg_ne_zero.mpr an) cn (Nat.pos_of_ne_zero hb) ac.isCoprime.neg_left
    rw [(px.2.odd_of_ne_two (by omega)).neg_pow]
    linear_combination -he
  · exact single_quartic single px py an bn (Nat.pos_of_ne_zero hc) ab.isCoprime he
  · rcases four with rfl|rfl|rfl
    · norm_num at px
    · norm_num at py
    · norm_num at pz

end OMA.R_BealConjecture_beal_conjecture_R1_H2_R2
