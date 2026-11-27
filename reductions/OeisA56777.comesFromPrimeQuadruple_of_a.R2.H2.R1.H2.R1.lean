import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Prime-root divisor reduction for A056777

A putative squarefree endpoint supplies three prime roots of the cubic from
its elementary symmetric sums. One prime root lies below the repeated prime.
Its positive quadratic expression divides a fixed polynomial in the repeated
prime and determines the unrepeated prime. Spacing of prime roots yields
stronger upper bounds on the repeated prime for large values of the unrepeated
prime.
-/

namespace OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1

open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem squarefree_triple_shape {n : ℕ}
    (hn : n.primeFactorsList.length=3) (hs : Squarefree n) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ n=a*b*c := by
  obtain ⟨a,b,c,he⟩ : ∃ a b c, n.primeFactorsList = [a,b,c] := by
    generalize hl : n.primeFactorsList = l at hn ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at hn
    rcases l with _ | ⟨b,l⟩
    · simp at hn
    rcases l with _ | ⟨c,l⟩
    · simp at hn
    rcases l with _ | ⟨d,l⟩
    · exact ⟨a,b,c,rfl⟩
    · simp at hn
  have ha := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=c) (by simp [he])
  have hnd := hs.nodup_primeFactorsList
  simp only [he,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hnd
  exact ⟨a,b,c,ha,hb,hc,hnd.1.1,hnd.1.2,hnd.2,
    by simpa [he,mul_assoc] using (Nat.prod_primeFactorsList hs.ne_zero).symm⟩

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
  simpa using sigma_one_apply_prime_pow (i:=1) hp

private theorem triple_formulas {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a*b*c).totient+(a*b+a*c+b*c)+1=a*b*c+(a+b+c) ∧
      σ 1 (a*b*c)+(a*b*c).totient=2*(a*b*c)+2*(a+b+c) := by
  have h₁ := (Nat.coprime_primes ha hb).mpr hab
  have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
  rw [Nat.totient_mul h₂,Nat.totient_mul h₁,Nat.totient_prime ha,Nat.totient_prime hb,
    Nat.totient_prime hc,isMultiplicative_sigma.map_mul_of_coprime h₂,
    isMultiplicative_sigma.map_mul_of_coprime h₁,sigma_prime ha,sigma_prime hb,sigma_prime hc]
  have ha1 := ha.pos
  have hb1 := hb.pos
  have hc1 := hc.pos
  zify [ha1,hb1,hc1]
  constructor <;> ring

private theorem fourth_times_prime_formulas {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    (p^4*q).totient+p^3*(p+q-1)=p^4*q ∧
      σ 1 (p^4*q)+(p^4*q).totient=2*(p^4*q)+(p^2+p+1)*(q+1)+2*p^3 := by
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 4
  have hsig : σ 1 (p^4)=1+p+p^2+p^3+p^4 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [Nat.totient_mul hc,show (p^4).totient=p^3*(p-1) from Nat.totient_prime_pow_succ hp 3,
    Nat.totient_prime hq,isMultiplicative_sigma.map_mul_of_coprime hc,hsig,sigma_prime hq]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1 ≤ p+q := by omega
  zify [hp1,hq1,hpq1]
  constructor <;> ring

private def twiceSum (p q : ℤ) : ℤ := (p^2+p+1)*(q+1)+2*p^3
private def twicePairSum (p q : ℤ) : ℤ := 2*p^3*(p+q-1)+twiceSum p q-2

private theorem cubic_linear_positive (p q : ℤ) (hp : 2*q<p) (hq : 11 ≤ q) :
    2*twiceSum p q*q < twicePairSum p q := by
  let U := p-(2*q+1)
  let V := q-11
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let C := 2*U^4 + 14*U^3*V + 162*U^3 + 34*U^2*V^2 + 789*U^2*V +
    4578*U^2 + 32*U*V^3 + 1118*U*V^2 + 13023*U*V + 50578*U +
    8*V^4 + 376*V^3 + 6628*V^2 + 51937*V + 152650
  have hpos : 0<C := by
    dsimp [C]
    positivity
  have he : twicePairSum p q-2*twiceSum p q*q=C := by
    dsimp [twicePairSum,twiceSum,C,U,V]
    ring
  omega

private theorem cubic_root_gt_q (p q x : ℤ) (hp : 2*q<p) (hq : 11 ≤ q) (hx : 0 ≤ x)
    (hroot : 2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)=0) :
    q<x := by
  by_contra! hxq
  let f (z : ℤ) := 2*z^3-twiceSum p q*z^2+twicePairSum p q*z-2*(p^4*q+12)
  have hL : 0 ≤ twiceSum p q := by
    have hp0 : 0 ≤ p := by omega
    have hq0 : 0 ≤ q := by omega
    dsimp [twiceSum]
    positivity
  have hM := cubic_linear_positive p q hp hq
  have hdiff : f q-f x=(q-x)*(2*(q^2+q*x+x^2)+twicePairSum p q-twiceSum p q*(q+x)) := by
    dsimp [f]
    ring
  have hprod : 0 ≤ twiceSum p q*(q-x) := mul_nonneg hL (by omega)
  have hqx : 0 ≤ q*x := mul_nonneg (by omega) hx
  have hinner : 0 ≤ 2*(q^2+q*x+x^2)+twicePairSum p q-twiceSum p q*(q+x) := by
    nlinarith only [hprod,hqx,hM,sq_nonneg q,sq_nonneg x]
  have hnon := mul_nonneg (show 0 ≤ q-x by omega) hinner
  have hqeval : f q= -(p^2+p-1)*(q^3-q)-24 := by dsimp [f,twicePairSum,twiceSum]; ring
  have hprod' := mul_nonneg (show 0 ≤ p^2+p-1 by nlinarith [sq_nonneg p]) (show 0 ≤ q^3-q by
    nlinarith [sq_nonneg q, mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ q^2-1 by nlinarith)])
  change f x=0 at hroot
  nlinarith only [hroot,hqeval,hdiff,hnon,hprod']

set_option maxHeartbeats 2000000 in
/-- The three integer roots satisfy a product identity independent of the
unrepeated prime parameter q. Each quadratic value consequently divides the
fixed degree-sixteen expression in p. -/
theorem cubic_root_quadratic_product (p q a b c : ℤ)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    let T (x : ℤ) := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
    T a*T b*T c=2*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
      29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72) := by
  let h := p^2+p+1
  let j := -(2*p^3+p^2+p+1)
  let k := 2*p^4
  let E (L M Z : ℤ) :=
    8*h^3*Z^2+4*h^2*j*M*Z+2*h^2*k*M^2+2*h*j*k*L*M+
      2*h*k^2*L^2+4*j*k^2*L+8*k^3+4*L*Z*(-2*h^2*k+h*j^2)+
      4*M*(-2*h*k^2+j^2*k)+8*Z*(-3*h*j*k+j^3)
  let T (x : ℤ) := h*x^2-(2*p^3+p^2+p+1)*x+k
  have he : 8*(T a*T b*T c)=E (2*(a+b+c)) (2*(a*b+a*c+b*c)) (a*b*c) := by
    dsimp [E,T,j]
    ring
  have hL' : 2*(a+b+c)=twiceSum p q := hL
  have hM' : 2*(a*b+a*c+b*c)=twicePairSum p q := by
    dsimp [twicePairSum]
    nlinarith only [hM,hL']
  rw [hL',hM',hZ] at he
  have he' : E (twiceSum p q) (twicePairSum p q) (p^4*q+12) =
      16*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
      29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72) := by
    dsimp [E,h,j,k,twiceSum,twicePairSum]
    ring
  rw [he'] at he
  change T a*T b*T c=_
  linarith only [he]

/-- For a fixed repeated prime and a root, the positive quadratic coefficient
allows reconstruction of the other prime by a single exact division. -/
theorem cubic_root_recovers_unrepeated_prime (p q x : ℤ) (hp : 3 ≤ p)
    (hx : 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
      (2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2)*x
      -2*(p^4*q+12)=0) :
    let T := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
    0<T ∧ q*T=2*x^3-(p^2+p+1+2*p^3)*x^2+(2*p^4+p^2+p-1)*x-24 := by
  let T := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
  let u := p-3
  have hu : 0 ≤ u := by dsimp [u]; omega
  let C := 4*u^6+76*u^5+603*u^4+2550*u^3+6045*u^2+7594*u+3935
  have hc : 0<C := by dsimp [C]; positivity
  have he : 4*(p^2+p+1)*T=(2*(p^2+p+1)*x-(2*p^3+p^2+p+1))^2+C := by
    dsimp [T,C,u]
    ring
  have hprod : 0<4*(p^2+p+1)*T := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hc
  have hp0 : 0 ≤ p := by omega
  refine ⟨pos_of_mul_pos_right hprod (by positivity),?_⟩
  linear_combination -hx

/-- At least one of the roots lies strictly between q and p. Its quadratic
value is a positive divisor of a polynomial in p and determines q exactly. -/
theorem cubic_root_reconstruction_candidate (p q a b c : ℤ)
    (hq : 11 ≤ q) (hp : 2*q<p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    let T (x : ℤ) := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
    ∃ x : ℤ, q<x ∧ x<p ∧ (x=a ∨ x=b ∨ x=c) ∧ 0<T x ∧
      q*T x=2*x^3-(p^2+p+1+2*p^3)*x^2+(2*p^4+p^2+p-1)*x-24 ∧
      T x∣2*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
        29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72) := by
  have hp3 : 3 ≤ p := by omega
  have hq0 : 0 ≤ q := by omega
  have hp0 : 0 ≤ p := by omega
  have hL' : 2*(a+b+c)=twiceSum p q := hL
  have hM' : 2*(a*b+a*c+b*c)=twicePairSum p q := by
    dsimp [twicePairSum]
    nlinarith only [hL',hM]
  have hpos : 0<2*p*twiceSum p q-twicePairSum p q-6*p^2 := by
    have he : 2*p*twiceSum p q-twicePairSum p q-6*p^2 =
        (p^2+p-1)*q+p^2*(2*p^2-5)+2*p^3+p+1 := by
      dsimp [twiceSum,twicePairSum]
      ring
    rw [he]
    have h₁ := mul_nonneg (show 0 ≤ p^2+p-1 by nlinarith [sq_nonneg p]) hq0
    have h₂ := mul_nonneg (sq_nonneg p) (show 0 ≤ 2*p^2-5 by
      nlinarith [mul_nonneg (show 0 ≤ p-3 by omega) (show 0 ≤ p+3 by omega)])
    have h₃ : 0 ≤ p^3 := by positivity
    nlinarith only [h₁,h₂,h₃,hp3]
  have hsmall : a<p ∨ b<p ∨ c<p := by
    by_contra! h
    obtain ⟨hpa,hpb,hpc⟩ := h
    have h₁ := mul_nonneg (show 0 ≤ a-p by omega) (show 0 ≤ b-p by omega)
    have h₂ := mul_nonneg (show 0 ≤ a-p by omega) (show 0 ≤ c-p by omega)
    have h₃ := mul_nonneg (show 0 ≤ b-p by omega) (show 0 ≤ c-p by omega)
    have hsum := congrArg (fun y : ℤ => 2*p*y) hL'
    nlinarith only [hpos,h₁,h₂,h₃,hsum,hM']
  let T (x : ℤ) := (p^2+p+1)*x^2-(2*p^3+p^2+p+1)*x+2*p^4
  let P := 2*(p^16+2*p^15-p^14-2*p^13+p^12-13*p^11-32*p^10-
    29*p^9+2*p^8+29*p^7+72*p^6+234*p^5+438*p^4+492*p^3+432*p^2+216*p+72)
  have hprod : T a*T b*T c=P := cubic_root_quadratic_product p q a b c hL hM hZ
  have root (x : ℤ) (hx : x=a ∨ x=b ∨ x=c) :
      2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)=0 := by
    rw [←hL',←hM',←hZ]
    rcases hx with rfl|rfl|rfl <;> ring
  have exhibit (x : ℤ) (hx : 0 ≤ x) (hxp : x<p) (hr : x=a ∨ x=b ∨ x=c)
      (hd : T x∣P) :
      ∃ y : ℤ, q<y ∧ y<p ∧ (y=a ∨ y=b ∨ y=c) ∧ 0<T y ∧
        q*T y=2*y^3-(p^2+p+1+2*p^3)*y^2+(2*p^4+p^2+p-1)*y-24 ∧ T y∣P := by
    obtain ⟨ht,hqT⟩ := cubic_root_recovers_unrepeated_prime p q x hp3 (root x hr)
    exact ⟨x,cubic_root_gt_q p q x hp hq hx (root x hr),hxp,hr,ht,hqT,hd⟩
  change ∃ x : ℤ, q<x ∧ x<p ∧ (x=a ∨ x=b ∨ x=c) ∧ 0<T x ∧
    q*T x=2*x^3-(p^2+p+1+2*p^3)*x^2+(2*p^4+p^2+p-1)*x-24 ∧ T x∣P
  rcases hsmall with h|h|h
  · exact exhibit a ha h (Or.inl rfl) ⟨T b*T c,by rw [←hprod]; ring⟩
  · exact exhibit b hb h (Or.inr (Or.inl rfl)) ⟨T a*T c,by rw [←hprod]; ring⟩
  · exact exhibit c hc h (Or.inr (Or.inr rfl)) ⟨T a*T b,by rw [←hprod]; ring⟩

namespace A056777CubicRootSpacing

/-- In the surviving odd branch, the product equation alone excludes the first
possible odd root above the unrepeated prime. -/
theorem not_next_odd_prime_root {p q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q)
    (hq8 : q % 8 = 3) (hx : (q + 2).Prime) (hd : q + 2 ∣ p^4*q + 12) : False := by
  let x := q+2
  have hx3 : 3 < x := by dsimp [x]; omega
  let _ : Fact x.Prime := ⟨hx⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have nondiv3 {n : ℕ} (hp : n.Prime) (hn : 3<n) : n%3 ≠ 0 := by
    intro he
    have hh := Nat.dvd_iff_mod_eq_zero.mpr he
    rcases (Nat.dvd_prime hp).mp hh with h|h <;> omega
  have hq3 := nondiv3 hq (by omega)
  have hxmod := nondiv3 hx hx3
  have hmod3 : x%3=1 := by dsimp [x] at *; omega
  have hmod8 : x%8=5 := by dsimp [x]; omega
  have hmod4 : x%4=1 := by omega
  have h2 : legendreSym x 2 = -1 := by
    rw [legendreSym.at_two (by omega)]
    have hcast8 : (x:ZMod 8)=5 := calc
      (x:ZMod 8) = (x%8:ℕ) := by simp
      _ = 5 := by rw [hmod8]; rfl
    rw [ZMod.χ₈,hcast8]
    decide
  have h3 : legendreSym x 3 = 1 := by
    have h := legendreSym.quadratic_reciprocity_one_mod_four (p:=x) (q:=3) hmod4 (by decide)
    push_cast at h
    rw [←h,legendreSym.mod]
    have hm : (x:ℤ)%3=1 := by exact_mod_cast hmod3
    simp [hm]
  have h6 : legendreSym x 6 = -1 := by
    rw [show (6:ℤ)=2*3 by decide,legendreSym.mul,h2,h3]
    norm_num
  have hcast := (ZMod.natCast_eq_zero_iff (p^4*q+12) x).2 hd
  push_cast at hcast
  have hxz : (q:ZMod x)+2=0 := by simpa only [x,Nat.cast_add,Nat.cast_ofNat] using ZMod.natCast_self x
  have he : (p:ZMod x)^4 = 6 := by
    have hx2 : (2:ZMod x) ≠ 0 := by
      exact fun hn => (not_le_of_gt (show 2<x by omega)) (Nat.le_of_dvd (by decide)
        ((ZMod.natCast_eq_zero_iff 2 x).mp hn))
    have hqz : (q:ZMod x)= -2 := eq_neg_of_add_eq_zero_left hxz
    rw [hqz] at hcast
    apply mul_left_cancel₀ hx2
    linear_combination -hcast
  have hp0 : (p:ZMod x) ≠ 0 := by
    intro hh
    have hzero : (6:ZMod x)=0 := by simpa [hh] using he.symm
    have hdiv := (ZMod.natCast_eq_zero_iff 6 x).mp hzero
    have := Nat.le_of_dvd (by decide : 0<6) hdiv
    dsimp [x] at *
    omega
  have hs : legendreSym x ((p:ℤ)^4) = 1 := by
    rw [show (p:ℤ)^4=((p:ℤ)^2)^2 by ring]
    apply legendreSym.sq_one'
    simpa only [Int.cast_pow,Int.cast_natCast] using pow_ne_zero 2 hp0
  have hf : legendreSym x ((p:ℤ)^4) = legendreSym x 6 := by
    unfold legendreSym
    push_cast
    rw [he]
  omega

/-- Evaluating the doubled cubic at the second possible odd root excludes it
when the repeated prime is three modulo five. -/
theorem not_second_odd_root_mod_five {p q : ℕ} (hp : p%5=3) (hq : q%5=2)
    (hroot : 2*((q:ℤ)+4)^3-((p^2+p+1)*(q+1)+2*p^3)*((q:ℤ)+4)^2+
      (2*p^3*((p:ℤ)+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2)*((q:ℤ)+4)
      -2*((p:ℤ)^4*q+12)=0) : False := by
  have hp5 : (p:ZMod 5)=3 := calc
    (p:ZMod 5) = (p%5:ℕ) := by simp
    _ = 3 := by rw [hp]; rfl
  have hq5 : (q:ZMod 5)=2 := calc
    (q:ZMod 5) = (q%5:ℕ) := by simp
    _ = 2 := by rw [hq]; rfl
  have h := congrArg (fun t : ℤ => (t:ZMod 5)) hroot
  push_cast at h
  rw [hp5,hq5] at h
  exact (by decide : ¬ (2*(2+4)^3-((3^2+3+1)*(2+1)+2*3^3)*(2+4)^2+
      (2*3^3*(3+2-1)+((3^2+3+1)*(2+1)+2*3^3)-2)*(2+4)
      -2*(3^4*2+12)= (0:ZMod 5))) h

/-- The first possible odd root is at least q+4. In either of the displayed
residue cases it is at least q+6. -/
theorem prime_root_spacing {p q x : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q)
    (hq8 : q%8=3) (hq5 : q%5=2) (hx : x.Prime) (hqx : q<x)
    (hdiv : x∣p^4*q+12)
    (hroot : 2*(x:ℤ)^3-(((p:ℤ)^2+p+1)*((q:ℤ)+1)+2*(p:ℤ)^3)*(x:ℤ)^2+
      (2*(p:ℤ)^3*((p:ℤ)+q-1)+(((p:ℤ)^2+p+1)*((q:ℤ)+1)+2*(p:ℤ)^3)-2)*x
      -2*((p:ℤ)^4*q+12)=0) :
    q+4 ≤ x ∧ (q%3=2 ∨ p%5=3 → q+6 ≤ x) := by
  have hxodd := hx.eq_two_or_odd.resolve_left (by omega)
  have hfirst : x ≠ q+2 := by
    rintro rfl
    exact not_next_odd_prime_root hq hq11 hq8 hx hdiv
  refine ⟨by omega,?_⟩
  intro h
  have hsecond : x ≠ q+4 := by
    rintro rfl
    rcases h with h|h
    · have hd : 3∣q+4 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
      rcases (Nat.dvd_prime hx).mp hd with h|h <;> omega
    · push_cast at hroot
      exact not_second_odd_root_mod_five h hq5 hroot
  omega

/-- A proven minimum root offset of four or six gives the corresponding
explicit lower bound on q³/p². -/
theorem cubic_bound_of_root_spacing (p q a b c k : ℤ) (hq : 4000 ≤ q) (hp : 0<p)
    (hk : k=4 ∨ k=6) (hka : q+k ≤ a) (hkb : q+k ≤ b) (hkc : q+k ≤ c)
    (hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c))
    (hZ : a*b*c=p^4*q+12) :
    (2*k-1)*p^2<q^3 := by
  by_contra! hpow
  have hk0 : 0 ≤ 2*k-1 := by omega
  have he : 19*q ≤ p := by
    by_contra! hf
    have hg := mul_pos (show 0<19*q-p by omega) (show 0<19*q+p by omega)
    have hi := mul_nonneg (sq_nonneg q) (show 0 ≤ q-3971 by omega)
    have hj := mul_nonneg (sq_nonneg p) (show 0 ≤ 11-(2*k-1) by omega)
    nlinarith only [hg,hi,hj,hpow]
  let L := (p^2+p+1)*(q+1)+2*p^3
  let M := 2*p^3*(p+q-1)+L-2
  have hP : 2*(a*b+a*c+b*c)=M := by dsimp [M,L]; nlinarith only [hM,hL]
  have hN : 2*(a+b+c)=L := hL
  let f (x : ℤ) := 2*x^3-L*x^2+M*x-2*(p^4*q+12)
  have hf : f (q+k) ≤ 0 := by
    have hfactor : f (q+k)=2*(q+k-a)*(q+k-b)*(q+k-c) := by
      dsimp [f]
      rw [←hN,←hP,←hZ]
      ring
    rw [hfactor]
    have hab := mul_nonneg_of_nonpos_of_nonpos (show q+k-a ≤ 0 by omega) (show q+k-b ≤ 0 by omega)
    have habc := mul_nonpos_of_nonneg_of_nonpos hab (show q+k-c ≤ 0 by omega)
    nlinarith only [habc]
  let A := q^3+2*k*q^2+(k^2+k-1)*q+(k^2-k)
  let C := q^3+4*k*q^2+(5*k^2-k-1)*q+(2*k^3-k^2-k-24)
  have hformula : f (q+k)=2*k*p^3*(p-q-k)-(p^2+p)*A+C := by
    dsimp [f,L,M,A,C]
    ring
  have hq0 : 0 ≤ q := by omega
  have hA : 100*A ≤ 101*q^3 := by
    have h1 := mul_nonneg (sq_nonneg q) (show 0 ≤ q-4000 by omega)
    have h2 := mul_nonneg hq0 (show 0 ≤ q-4000 by omega)
    dsimp [A]
    rcases hk with rfl|rfl <;> nlinarith only [h1,h2,hq,sq_nonneg q]
  have hC : 0 ≤ C := by
    dsimp [C]
    rcases hk with rfl|rfl <;> norm_num <;> positivity
  have hfirst := mul_le_mul_of_nonneg_left (show 17*p ≤ 18*(p-q-k) by omega)
    (show 0 ≤ 2*k*p^3 by
      have hk' : 0 ≤ k := by omega
      positivity)
  have hmid := mul_le_mul_of_nonneg_left (hA.trans
    (mul_le_mul_of_nonneg_left hpow (by decide))) (show 0 ≤ p^2+p by positivity)
  have hmid' := mul_le_mul_of_nonneg_right (show 100*(p^2+p) ≤ 101*p^2 by
    nlinarith only [mul_nonneg hp.le (show 0 ≤ p-100 by omega)])
    (show 0 ≤ 101*(2*k-1)*p^2 by positivity)
  have hpp : 0<p^4 := by positivity
  rw [hformula] at hf
  rcases hk with rfl|rfl <;> nlinarith only [hf,hfirst,hmid,hmid',hC,hpp]

end A056777CubicRootSpacing

/-- Exclude prime-root divisors for q below 4000. -/
def H1 : Prop :=
  ∀ p q x : ℕ, p.Prime → q.Prime → x.Prime →
    p % 4 = 3 → q % 8 = 3 → 11 ≤ q → 2*q < p → p % 3 ≠ q % 3 →
    p^2 < q^3 → (p % 5 = 2 ∨ p % 5 = 3) → q % 5 = 2 →
    q < 4000 →
    q+4 ≤ x → (q % 3 = 2 ∨ p % 5 = 3 → q+6 ≤ x) → x < p →
    x ∣ p^4*q+12 →
    let P : ℤ := p
    let X : ℤ := x
    let T := (P^2+P+1)*X^2-(2*P^3+P^2+P+1)*X+2*P^4
    0 < T →
    (q : ℤ)*T = 2*X^3-(P^2+P+1+2*P^3)*X^2+(2*P^4+P^2+P-1)*X-24 →
    T ∣ 2*(P^16+2*P^15-P^14-2*P^13+P^12-13*P^11-32*P^10-
      29*P^9+2*P^8+29*P^7+72*P^6+234*P^5+438*P^4+492*P^3+432*P^2+216*P+72) →
    False


/-- Exclude prime-root divisors for q at least 4000. -/
def H2 : Prop :=
  ∀ p q x : ℕ, p.Prime → q.Prime → x.Prime →
    p % 4 = 3 → q % 8 = 3 → 11 ≤ q → 2*q < p → p % 3 ≠ q % 3 →
    p^2 < q^3 → (p % 5 = 2 ∨ p % 5 = 3) → q % 5 = 2 →
    4000 ≤ q →
    7*p^2 < q^3 → (q % 3 = 2 ∨ p % 5 = 3 → 11*p^2 < q^3) →
    q+4 ≤ x → (q % 3 = 2 ∨ p % 5 = 3 → q+6 ≤ x) → x < p →
    x ∣ p^4*q+12 →
    let P : ℤ := p
    let X : ℤ := x
    let T := (P^2+P+1)*X^2-(2*P^3+P^2+P+1)*X+2*P^4
    0 < T →
    (q : ℤ)*T = 2*X^3-(P^2+P+1+2*P^3)*X^2+(2*P^4+P^2+P-1)*X-24 →
    T ∣ 2*(P^16+2*P^15-P^14-2*P^13+P^12-13*P^11-32*P^10-
      29*P^9+2*P^8+29*P^7+72*P^6+234*P^5+438*P^4+492*P^3+432*P^2+216*P+72) →
    False


theorem main : H1 → H2 → OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1.H2 := by
  intro small large n m hn _ _ hs hgap hphi hsigma hshape
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,hpgt,hpq3,hsize,hp5,hq5,rfl⟩ := hshape
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,rfl⟩ := squarefree_triple_shape hn hs
  obtain ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  obtain ⟨hF',hK'⟩ := triple_formulas ha hb hc hab hac hbc
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hpq1 : 1 ≤ p+q := by omega
  zify [hpq1] at hL hM
  have hZ : (a:ℤ)*b*c=(p:ℤ)^4*q+12 := by exact_mod_cast hgap.symm
  have hq11' : (11:ℤ) ≤ q := by exact_mod_cast hq11
  have hpgt' : 2*(q:ℤ) < p := by exact_mod_cast hpgt
  have hLa : 2*((a:ℤ)+b+c)=twiceSum p q := hL
  have hMa : 2*((a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c)=twicePairSum p q := by
    dsimp [twicePairSum,twiceSum]
    linarith only [hL,hM]
  have root (x : ℕ) (hr : x=a ∨ x=b ∨ x=c) :
      2*(x:ℤ)^3-twiceSum p q*(x:ℤ)^2+twicePairSum p q*x-2*((p:ℤ)^4*q+12)=0 := by
    rw [← hLa,← hMa,← hZ]
    rcases hr with rfl | rfl | rfl <;> ring
  have divides (x : ℕ) (hr : x=a ∨ x=b ∨ x=c) : x ∣ p^4*q+12 := by
    rw [hgap]
    rcases hr with rfl | rfl | rfl
    · exact ⟨b*c, by ring⟩
    · exact ⟨a*c, by ring⟩
    · exact ⟨a*b, by ring⟩
  have spaced (x : ℕ) (hx : x.Prime) (hr : x=a ∨ x=b ∨ x=c) :
      q+4 ≤ x ∧ (q % 3 = 2 ∨ p % 5 = 3 → q+6 ≤ x) := by
    have hroot := root x hr
    have hqx : q < x := by
      exact_mod_cast cubic_root_gt_q p q x hpgt' hq11' (Int.natCast_nonneg x) hroot
    exact A056777CubicRootSpacing.prime_root_spacing hq hq11 hq8 hq5 hx hqx
      (divides x hr) hroot
  obtain ⟨x,hqx,hxp,hxroot,hT,hrec,hres⟩ :=
    cubic_root_reconstruction_candidate p q a b c hq11' hpgt'
      (Int.natCast_nonneg a) (Int.natCast_nonneg b) (Int.natCast_nonneg c) hL hM hZ
  obtain ⟨y,hy,hyroot,he⟩ :
      ∃ y : ℕ, y.Prime ∧ (y=a ∨ y=b ∨ y=c) ∧ x=(y:ℤ) := by
    rcases hxroot with h | h | h
    · exact ⟨a,ha,Or.inl rfl,h⟩
    · exact ⟨b,hb,Or.inr (Or.inl rfl),h⟩
    · exact ⟨c,hc,Or.inr (Or.inr rfl),h⟩
  rw [he] at hxp hT hrec hres
  obtain ⟨hy4,hy6⟩ := spaced y hy hyroot
  have hyp : y < p := by exact_mod_cast hxp
  by_cases hsmall : q < 4000
  · exact small p q y hp hq hy hp4 hq8 hq11 hpgt hpq3 hsize hp5 hq5 hsmall
      hy4 hy6 hyp (divides y hyroot) hT hrec hres
  · have hlarge : 4000 ≤ q := by omega
    obtain ⟨ha4,ha6⟩ := spaced a ha (Or.inl rfl)
    obtain ⟨hb4,hb6⟩ := spaced b hb (Or.inr (Or.inl rfl))
    obtain ⟨hc4,hc6⟩ := spaced c hc (Or.inr (Or.inr rfl))
    have bound (k : ℕ) (hk : k=4 ∨ k=6) (hka : q+k ≤ a)
        (hkb : q+k ≤ b) (hkc : q+k ≤ c) :
        (2*(k:ℤ)-1)*(p:ℤ)^2 < (q:ℤ)^3 :=
      A056777CubicRootSpacing.cubic_bound_of_root_spacing p q a b c k
        (by exact_mod_cast hlarge) (by exact_mod_cast hp.pos)
        (by rcases hk with rfl | rfl <;> norm_num)
        (by exact_mod_cast hka) (by exact_mod_cast hkb) (by exact_mod_cast hkc) hL hM hZ
    have h7 : 7*p^2 < q^3 := by
      have hh := bound 4 (Or.inl rfl) ha4 hb4 hc4
      norm_num at hh
      exact_mod_cast hh
    have h11 (hr : q % 3 = 2 ∨ p % 5 = 3) : 11*p^2 < q^3 := by
      have hh := bound 6 (Or.inr rfl) (ha6 hr) (hb6 hr) (hc6 hr)
      norm_num at hh
      exact_mod_cast hh
    exact large p q y hp hq hy hp4 hq8 hq11 hpgt hpq3 hsize hp5 hq5 hlarge h7 h11
      hy4 hy6 hyp (divides y hyroot) hT hrec hres

end OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1
