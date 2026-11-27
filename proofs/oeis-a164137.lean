import OMAStatements.S_oeis_a164137
import Mathlib

/-!
A weighted three-state automaton enumerates binary words by the excess of occurrences
of `000` over `001`. A rational telescoping identity yields a differential equation
for its Laurent constant term. Extracting the coefficient of degree `n` proves Robert
P. P. McKone's recurrence for every `n ≥ 10`. Ekhad and Zeilberger obtained an earlier
order-eight recurrence for the same words in Proposition 1 of their length-three table,
https://sites.math.rutgers.edu/~zeilberg/tokhniot/oRPS23 .
-/

namespace A164137Automaton
open OMA.S_oeis_a164137
open LaurentPolynomial PowerSeries

abbrev L := LaurentPolynomial ℚ
abbrev S := PowerSeries L

def difference (w : List Bool) : ℤ := (occurrences w false : ℤ) - occurrences w true

private lemma occurrences_cons (b : Bool) (l : List Bool) (v : Bool) :
    occurrences (b::l) v = occurrences l v +
      (if b = false ∧ l[0]? = some false ∧ l[1]? = some v then 1 else 0) := by
  simp only [occurrences, List.length_cons, List.range_succ_eq_map, List.countP_cons,
    List.countP_map, Function.comp_def, List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp [Bool.and_assoc]

private lemma difference_one (w : List Bool) : difference (true::w) = difference w := by
  simp [difference, occurrences_cons]

private lemma difference_zero_one (w : List Bool) : difference (false::true::w) = difference w := by
  simp [difference, occurrences_cons]

private lemma difference_three (v : Bool) (w : List Bool) :
    difference (false::false::v::w) = difference (false::v::w) + (if v then -1 else 1) := by
  cases v <;> simp [difference, occurrences_cons] <;> omega

noncomputable def weighted (seed : List Bool) (n : ℕ) : L :=
  ∑ w : Fin n → Bool, LaurentPolynomial.T (difference (seed ++ List.ofFn w))

noncomputable def words (seed : List Bool) : S := PowerSeries.mk (weighted seed)

private lemma split_words (seed : List Bool) (n : ℕ) : weighted seed (n+1) =
    weighted (seed ++ [false]) n + weighted (seed ++ [true]) n := by
  unfold weighted
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simp [Fintype.sum_prod_type, Fin.consEquiv, add_comm]

theorem constant_word_count (n : ℕ) : ((PowerSeries.coeff n (words [])).coeff 0) = (a n : ℚ) := by
  simp only [words, PowerSeries.coeff_mk, weighted, List.nil_append, a, Finset.natCast_card_filter]
  simp [difference, sub_eq_zero]

private lemma fixed_prefix (l l' : List Bool) (n : ℕ) (k : ℤ)
    (h : ∀ w, difference (l ++ w) = difference (l' ++ w)+k) :
    weighted l n = weighted l' n * LaurentPolynomial.T k := by
  simp only [weighted, h, T_add, Finset.sum_mul]

private lemma base (p : List Bool) (hp : difference p = 0) : weighted p 0 = 1 := by
  simp [weighted, hp]

/-- Three automaton states according to the number of zeroes already read (capped at two). -/
theorem updates (n : ℕ) :
    weighted [] (n+1) = weighted [] n + weighted [false] n ∧
    weighted [false] (n+1) = weighted [] n + weighted [false,false] n ∧
    weighted [false,false] (n+1) = weighted [] n * LaurentPolynomial.T (-1) +
      weighted [false,false] n * LaurentPolynomial.T 1 := by
  have t := fixed_prefix [true] [] n 0 (by simpa using difference_one)
  have ft := fixed_prefix [false,true] [] n 0 (by simpa using difference_zero_one)
  have fft := fixed_prefix [false,false,true] [] n (-1) (by
    intro w; simp [difference_three, difference_zero_one])
  have fff := fixed_prefix [false,false,false] [false,false] n 1 (by
    intro w; simp [difference_three])
  simp only [T_zero, mul_one] at t ft
  constructor
  · rw [split_words]; simp [t, add_comm]
  constructor
  · rw [split_words]; simp [ft, add_comm]
  · rw [split_words]; simp [fft, fff, add_comm]

noncomputable abbrev t : S := PowerSeries.X
noncomputable abbrev z (j : ℤ) : S := PowerSeries.C (LaurentPolynomial.T j)

private theorem equations :
    words [] = 1 + (words [] + words [false]) * t ∧
    words [false] = 1 + (words [] + words [false,false]) * t ∧
    words [false,false] = 1 + (words [] * z (-1) + words [false,false] * z 1) * t := by
  have h0 : weighted [] 0 = 1 := base _ (by decide)
  have h1 : weighted [false] 0 = 1 := base _ (by decide)
  have h2 : weighted [false,false] 0 = 1 := base _ (by decide)
  refine ⟨?_, ?_, ?_⟩ <;> apply PowerSeries.ext <;> intro n <;> cases n with
  | zero => simp only [t, words, map_add, coeff_mk, coeff_zero_one, coeff_zero_mul_X, add_zero, h0, h1, h2]
  | succ n =>
    simp only [t, z, words, map_add, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false,
      zero_add, coeff_succ_mul_X, coeff_mul_C]
    first | exact (updates n).1 | exact (updates n).2.1 | exact (updates n).2.2

/-- Exact rational generating function for the pinned finite binary-word counts,
with the Laurent exponent recording excess occurrences of `000` over `001`. -/
theorem rational_word_series :
    words [] * ((1-t-t^2)*(1-t*z 1)-t^3*z (-1)) = (1+t)*(1-t*z 1)+t^2 := by
  obtain ⟨h0,h1,h2⟩ := equations
  linear_combination (1-t*z 1)*h0 + t*(1-t*z 1)*h1 + t^2*h2


end A164137Automaton

namespace A164137Euler
open A164137Automaton PowerSeries
noncomputable section

def eL : L →+ L where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.coeff.support
    (fun i => (i:ℚ)*p.coeff i) (by intro i hi; apply Finsupp.mem_support_iff.mpr; aesop))
  map_zero' := LaurentPolynomial.ext (by intro i; change (i:ℚ)*0=0; ring)
  map_add' p q := LaurentPolynomial.ext (by intro i; change (i:ℚ)*(p.coeff i+q.coeff i)=_; change _=(i:ℚ)*p.coeff i+(i:ℚ)*q.coeff i; ring)

@[simp] lemma eL_coeff (p : L) (i : ℤ) : (eL p).coeff i = (i:ℚ)*p.coeff i := rfl

private lemma single (i : ℤ) (v : ℚ) : eL (.single i v) = .single i ((i:ℚ)*v) := by
  apply LaurentPolynomial.ext; intro j
  rw [eL_coeff]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split <;> simp_all

private lemma ind (p : L) {P : L → Prop} (hz : P 0) (ha : ∀ p q, P p → P q → P (p+q))
    (hl : ∀ (i:ℤ) (c:ℚ), P (.single i c)) : P p := by
  cases p with
  | ofCoeff f =>
    induction f using Finsupp.induction_linear with
    | zero => exact hz
    | add x y hx hy => exact ha _ _ hx hy
    | single i a => exact hl i a

lemma eL_mul (p q : L) : eL (p*q) = eL p * q + p * eL q := by
  induction p using ind with
  | hz => simp
  | ha p r hp hr => simp only [add_mul, map_add, hp, hr]; ring
  | hl i a =>
    induction q using ind with
    | hz => simp
    | ha p r hp hr => simp only [mul_add, map_add, hp, hr]; ring
    | hl j b =>
      rw [AddMonoidAlgebra.single_mul_single, single, single, single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
        ← AddMonoidAlgebra.single_add]
      congr 1; push_cast; ring

@[simp] lemma eL_one : eL 1 = 0 := by
  have h := eL_mul 1 1; simpa using h

@[simp] lemma eL_natCast (n : ℕ) : eL (n:L) = 0 := by
  induction n <;> simp_all [Nat.cast_succ]

/-- Euler derivative in the Laurent marker, acting coefficientwise in time. -/
def e : S →+ S where
  toFun f := PowerSeries.mk fun n => eL (PowerSeries.coeff n f)
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

/-- Extract the Laurent constant term at every time. -/
def ct (f : S) : PowerSeries ℚ := PowerSeries.mk fun n => (PowerSeries.coeff n f).coeff 0

@[simp] lemma coeff_e (f : S) (n : ℕ) : PowerSeries.coeff n (e f) = eL (PowerSeries.coeff n f) := by
  simp [e]

@[simp] lemma coeff_ct (f : S) (n : ℕ) : PowerSeries.coeff n (ct f) = (PowerSeries.coeff n f).coeff 0 := by simp [ct]

@[simp] lemma ct_e (f : S) : ct (e f) = 0 := by apply PowerSeries.ext; intro n; simp

lemma e_mul (f g : S) : e (f*g) = e f * g + f * e g := by
  apply PowerSeries.ext; intro n
  simp only [coeff_e, map_add, coeff_mul, map_sum, eL_mul, Finset.sum_add_distrib]

abbrev dt := PowerSeries.derivative L
abbrev dq := PowerSeries.derivative ℚ

lemma e_dt (f : S) : e (dt f) = dt (e f) := by
  apply PowerSeries.ext; intro n
  simp [dt, coeff_derivative, eL_mul]

lemma ct_dt (f : S) : ct (dt f) = dq (ct f) := by
  apply PowerSeries.ext; intro n
  simp only [coeff_ct, dt, dq, coeff_derivative]
  have h (p : L) (j : ℕ) : (p * (j:L)).coeff 0 = p.coeff 0 * (j:ℚ) := by
    induction j <;> simp_all [Nat.cast_succ, mul_add]
  simpa only [Nat.cast_succ] using h (PowerSeries.coeff (n+1) f) (n+1)

@[simp] lemma e_one : e 1 = 0 := by have h := e_mul 1 1; simpa using h

lemma logarithmic_constant_term (D I : S) (inv : D*I=1) (hD : PowerSeries.coeff 0 D = 1) :
    ct (e D * I) = 0 := by
  have dz := congrArg e inv
  simp only [e_mul, e_one] at dz
  have dtz := congrArg dt inv
  simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at dtz
  have eqn : dt (e D * I) = e (dt D * I) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, e_mul, e_dt]
    linear_combination (dt I) * D * dz - (e I) * D * dtz - ((e D) * (dt I) - (dt D) * (e I)) * inv
  have zeroDeriv : dq (ct (e D * I)) = 0 := by
    rw [← ct_dt, eqn, ct_e]
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
    have h0 : coeff 0 (e D * I) = coeff 0 (e D) * coeff 0 I := by simp only [coeff_zero_eq_constantCoeff_apply, map_mul]
    simp [h0, hD]
  | succ n =>
    have h := congrArg (PowerSeries.coeff n) zeroDeriv
    simp only [dq, coeff_derivative, map_zero] at h
    simpa using (mul_eq_zero.mp h).resolve_right (by positivity)

@[simp] lemma ct_add (f g : S) : ct (f+g) = ct f + ct g := by ext n; simp
@[simp] lemma ct_neg (f : S) : ct (-f) = -ct f := by ext n; simp
@[simp] lemma ct_sub (f g : S) : ct (f-g) = ct f - ct g := by simp [sub_eq_add_neg]
@[simp] lemma ct_zero : ct 0 = 0 := by ext n; simp
@[simp] lemma ct_one : ct 1 = 1 := by
  apply PowerSeries.ext; intro n
  simp only [coeff_ct, coeff_one]; split <;> simp

abbrev lift : PowerSeries ℚ →+* S := PowerSeries.map LaurentPolynomial.C

lemma ct_lift_mul (f : PowerSeries ℚ) (g : S) : ct (lift f * g) = f * ct g := by
  apply PowerSeries.ext; intro n
  simp only [coeff_ct, coeff_mul, lift, coeff_map, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, LaurentPolynomial.C]
  apply Finset.sum_congr rfl; intro i _
  exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _

lemma ct_lift (f : PowerSeries ℚ) : ct (lift f) = f := by simpa using ct_lift_mul f 1

@[simp] lemma e_lift (f : PowerSeries ℚ) : e (lift f) = 0 := by
  apply PowerSeries.ext; intro n
  simp only [coeff_e, lift, coeff_map, map_zero]
  apply LaurentPolynomial.ext; intro j
  simp only [eL_coeff, LaurentPolynomial.C_apply]; split <;> simp_all

lemma e_inverse (D I : S) (inv : D*I=1) : e I = -I^2 * e D := by
  have h := congrArg e inv
  simp only [e_mul, e_one] at h
  linear_combination I * h - e I * inv

lemma e_C (r : L) : e (PowerSeries.C r) = PowerSeries.C (eL r) := by
  apply PowerSeries.ext; intro n; simp only [coeff_e, coeff_C]; split <;> simp

@[simp] lemma e_t : e t = 0 := by
  apply PowerSeries.ext; intro n; simp only [coeff_e, t, coeff_X, map_zero]; split <;> simp

@[simp] lemma e_zp : e (z 1) = z 1 := by
  rw [z, e_C]; congr 1; rw [LaurentPolynomial.T, single]; norm_num

@[simp] lemma e_zm : e (z (-1)) = -z (-1) := by
  rw [z, e_C, ← map_neg]; congr 1; rw [LaurentPolynomial.T, single]; norm_num

@[simp] lemma z_mul : z 1 * z (-1) = 1 := by
  simp only [z, ← map_mul, ← LaurentPolynomial.T_add]; norm_num

end
end A164137Euler

namespace A164137Coeff
open PowerSeries OMA.S_oeis_a164137

def A {R : Type*} [CommRing R] (x : R) : R :=
  1 - 2 * x - x^2 - x^3 + x^4 + 11 * x^5 + 5 * x^7 - 6 * x^8 - 20 * x^9 - 8 * x^10

def B {R : Type*} [CommRing R] (x : R) : R :=
  -2 * x - 2 * x^2 + 15 * x^3 - 8 * x^4 - x^5 + 16 * x^6 - 11 * x^7 - 22 * x^8 - 20 * x^9 - 8 * x^10

def rhs {R : Type*} [CommRing R] (x : R) : R :=
  -2 * x^2 + 3 * x^3 - 8 * x^5

private noncomputable def shift (c : ℚ) (j : ℕ) (G : PowerSeries ℚ) :=
  C c * (X^j * G)

private theorem coeff_shift (c : ℚ) (j m : ℕ) (G : PowerSeries ℚ) (h : j ≤ m) :
    coeff m (shift c j G) = c * coeff (m-j) G := by
  unfold shift
  rw [coeff_C_mul]
  conv_lhs => rw [show m = (m-j)+j by omega, coeff_X_pow_mul]

private lemma euler_coeff (G : PowerSeries ℚ) (m : ℕ) :
    coeff m (X * derivative ℚ G) = (m : ℚ) * coeff m G := by
  cases m with
  | zero => simp
  | succ k => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

/-- Coefficient extraction in the differential equation, over the full OEIS range. -/
theorem fromODE (G : PowerSeries ℚ) (hg : ∀ n, coeff n G = (a n : ℚ))
    (h : X * A X * derivative ℚ G + B X * G = rhs X) :
    type_of% @OMA.S_oeis_a164137.main := by
  intro n hn
  have expand :
      shift (1) 0 (X * derivative ℚ G)
      + shift (-2) 1 (X * derivative ℚ G)
      + shift (-1) 2 (X * derivative ℚ G)
      + shift (-1) 3 (X * derivative ℚ G)
      + shift (1) 4 (X * derivative ℚ G)
      + shift (11) 5 (X * derivative ℚ G)
      + shift (5) 7 (X * derivative ℚ G)
      + shift (-6) 8 (X * derivative ℚ G)
      + shift (-20) 9 (X * derivative ℚ G)
      + shift (-8) 10 (X * derivative ℚ G)
      + shift (-2) 1 (G)
      + shift (-2) 2 (G)
      + shift (15) 3 (G)
      + shift (-8) 4 (G)
      + shift (-1) 5 (G)
      + shift (16) 6 (G)
      + shift (-11) 7 (G)
      + shift (-22) 8 (G)
      + shift (-20) 9 (G)
      + shift (-8) 10 (G) =
      shift (-2) 2 (1)
      + shift (3) 3 (1)
      + shift (-8) 5 (1) := by
    convert h using 1 <;> norm_num [shift, A, B, rhs, map_ofNat] <;> ring
  have c := congrArg (coeff n) expand
  simp (disch := omega) only [map_add, coeff_shift, euler_coeff, hg, coeff_one, if_neg] at c
  have bound (j : ℕ) (hj : j ≤ 10) : ((n-j : ℕ) : ℚ) = (n : ℚ) - j :=
    Nat.cast_sub (hj.trans hn)
  simp only [Nat.sub_zero] at c
  simp (disch := decide) only [bound, Nat.cast_ofNat] at c
  dsimp
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination c

end A164137Coeff

namespace A164137Polynomial

variable {R : Type*} [CommRing R]

def C (x : R) := 1-x-x^2
def D (x z y : R) := C x * (1-x*z) - x^3*y
def N (x z : R) := (1+x)*(1-x*z)+x^2
def Dt (x z y : R) := (-1-2*x)*(1-x*z) - C x*z - 3*x^2*y
def Nt (x z : R) := 1-x*z-(1+x)*z+2*x
def Dz (x z y : R) := -C x*x*z+x^3*y
def U (x : R) := -x^3*(2*x^2+x+1)*(4*x^6+4*x^5-3*x^4-6*x^3-3*x^2-2*x+3)
def V (x : R) := x^2*(x^2+x-1)*(2*x^2+x+1)*(4*x^5-3*x^3-3*x^2+2*x-1)

/-- Telescoping identity for the binary-word enumerator after clearing the denominator. -/
theorem certificate (x z y : R) (zy : z*y=1) :
    A164137Coeff.A x*x*(Nt x z * D x z y-N x z * Dt x z y)
      + A164137Coeff.B x*N x z*D x z y - A164137Coeff.rhs x*(D x z y)^2 =
    A164137Coeff.rhs x*Dz x z y*D x z y - U x*y*D x z y
      - (U x*y+V x)*Dz x z y := by
  unfold A164137Coeff.A A164137Coeff.B A164137Coeff.rhs Nt Dt Dz D N C U V
  linear_combination (-x^4*(x^2+x-1)^2*(2*x^2+x+1)^2*(2*x^2+3*x-4))*zy

end A164137Polynomial

namespace A164137Direct
open PowerSeries A164137Automaton A164137Euler A164137Coeff A164137Polynomial

private theorem remove_den {R : Type*} [CommRing R]
    (a b s d i n dn dd dz u y v : R) (di : d*i=1)
    (h : a*(dn*d-n*dd)+b*n*d-s*d^2=s*dz*d-u*y*d-(u*y+v)*dz) :
    a*(dn*i+n*(-i^2*dd))+b*(n*i)-s = s*(dz*i)+((-u*y)*i+(u*y+v)*(-i^2*dz)) := by
  linear_combination i^2*h+(-a*dn*i-b*n*i+s*(1+d*i)+s*dz*i-u*y*i)*di

private lemma ode :
    X * A X * derivative ℚ (ct (words [])) + B X * ct (words []) = rhs X := by
  let zp := z 1
  let zm := z (-1)
  let d := D t zp zm
  let n := N t zp
  let f := words []
  have hd : PowerSeries.constantCoeff d = 1 := by simp [d, D, A164137Polynomial.C, t]
  obtain ⟨i,hi⟩ := (PowerSeries.isUnit_iff_constantCoeff.mpr (hd ▸ isUnit_one)).exists_right_inv
  have prod : f*d = n := rational_word_series
  have nf : f = n*i := calc
    f = f*(d*i) := by rw [hi,mul_one]
    _ = n*i := by rw [← mul_assoc, prod]
  have dtD : dt d = Dt t zp zm := by
    simp [d, D, A164137Polynomial.C, Dt, zp, zm, z, t, dt, Derivation.leibniz,
      Derivation.leibniz_pow, smul_eq_mul]; ring
  have dtN : dt n = Nt t zp := by
    simp [n, N, Nt, zp, z, t, dt, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul]; ring
  have eD : e d = Dz t zp zm := by
    simp [d, D, A164137Polynomial.C, Dz, zp, zm, pow_succ, e_mul]; ring
  have ii : dt i = -i^2 * dt d := by
    simpa using dt.leibniz_of_mul_eq_one (show i*d=1 by rw [mul_comm,hi])
  have eii := e_inverse d i hi
  have dtF : dt f = Nt t zp*i+n*(-i^2*Dt t zp zm) := by
    rw [nf, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ii, dtD, dtN]; ring
  have lx : lift (X:PowerSeries ℚ) = t := by simp [lift,t]
  have uv : U t = lift (U (X:PowerSeries ℚ)) := by simp [U,lx,map_ofNat]
  have vv : V t = lift (V (X:PowerSeries ℚ)) := by simp [V,lx,map_ofNat]
  have eU : e (U t) = 0 := by rw [uv,e_lift]
  have eV : e (V t) = 0 := by rw [vv,e_lift]
  have eqQ : e ((U t*zm+V t)*i) = (-U t*zm)*i+(U t*zm+V t)*(-i^2*Dz t zp zm) := by
    simp only [e_mul, map_add, eU, eV, zm, e_zm, zero_mul, zero_add, add_zero, eii, eD]; ring
  have cert := A164137Polynomial.certificate t zp zm z_mul
  have key : (t*A t)*dt f+B t*f-rhs t = rhs t*(e d*i)+e ((U t*zm+V t)*i) := by
    rw [dtF, nf, eqQ, eD, mul_comm t (A t)]
    exact remove_den _ _ _ d i n _ _ _ _ _ _ hi cert
  have aL : t*A t = lift (X*A (X:PowerSeries ℚ)) := by simp [A,lx,map_ofNat]
  have bL : B t = lift (B (X:PowerSeries ℚ)) := by simp [B,lx,map_ofNat]
  have sL : rhs t = lift (rhs (X:PowerSeries ℚ)) := by simp [rhs,lx,map_ofNat]
  have lzero := logarithmic_constant_term d i hi (by rwa [coeff_zero_eq_constantCoeff_apply])
  have result := congrArg ct key
  rw [ct_sub, ct_add, ct_add, aL, bL, sL, ct_lift_mul, ct_lift_mul, ct_lift_mul, ct_lift,
      ct_e, lzero, mul_zero, add_zero, ct_dt, sub_eq_zero] at result
  exact result

end A164137Direct

/-- McKone's recurrence, directly from the weighted enumeration of binary words. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a164137.main :=
  A164137Coeff.fromODE _ (fun n => by simpa only [A164137Euler.coeff_ct] using A164137Automaton.constant_word_count n) A164137Direct.ode
