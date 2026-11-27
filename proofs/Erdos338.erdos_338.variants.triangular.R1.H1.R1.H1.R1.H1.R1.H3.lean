import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1

/-! The quaternion model, eigenline count, and eight representatives per line are adapted from @ysanatomic (Yordan), merged Tunnell even-twist proof 3112a07, via @marcusbuffett in the merged Erdős 338 squares proof. We apply them to conjugation of trace-zero quaternions to count primitive ternary representations. -/

section

/- Integral quaternion norm shells, rotations, and the weight on a coordinate. -/

namespace TunnellQuaternion

open Finset Quaternion


abbrev QInt := Quaternion ℤ

lemma normSq_mk (a b c d : ℤ) : Quaternion.normSq (⟨a,b,c,d⟩:QInt) = a^2+b^2+c^2+d^2 := Quaternion.normSq_def' _

lemma neg_mk (a b c d : ℤ) : -(⟨a,b,c,d⟩:QInt) = ⟨-a,-b,-c,-d⟩ := rfl

abbrev coordsEquiv := Quaternion.equivProd ℤ

noncomputable def quatShell (N : ℕ) : Finset QInt :=
  let I := Icc (-(N:ℤ)) (N:ℤ)
  ((I ×ˢ (I ×ˢ (I ×ˢ I))).map coordsEquiv.symm.toEmbedding).filter (fun q => Quaternion.normSq q=N)

@[simp] lemma mem_quatShell {q : QInt} {N : ℕ} : q ∈ quatShell N ↔ Quaternion.normSq q=N := by
  simp only [quatShell,mem_filter,mem_map_equiv]
  refine ⟨And.right,fun hn => ⟨?_,hn⟩⟩
  rw [Quaternion.normSq_def'] at hn
  obtain ⟨a,b,c,d⟩ := q
  change a^2+b^2+c^2+d^2 = (N:ℤ) at hn
  simp only [mem_product,mem_Icc]
  change (- (N:ℤ) ≤ a ∧ a ≤ N) ∧ (- (N:ℤ) ≤ b ∧ b ≤ N) ∧
    (- (N:ℤ) ≤ c ∧ c ≤ N) ∧ - (N:ℤ) ≤ d ∧ d ≤ N
  have hb (x : ℤ) (h : x^2 ≤ N) : -(N:ℤ) ≤ x ∧ x ≤ N := by
    constructor <;> by_contra! he
    · have := mul_nonneg_of_nonpos_of_nonpos (by omega : x ≤ 0) (by omega : x+1 ≤ 0)
      nlinarith
    · have := mul_nonneg (by omega : 0 ≤ x) (by omega : 0 ≤ x-1)
      nlinarith
  exact ⟨hb _ (by nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg c,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c])⟩

end TunnellQuaternion

end

section

/- Explicit splitting of the Hamilton quaternion algebra at odd primes. -/

namespace TunnellQuaternion

open Matrix Quaternion

variable {K : Type*} [Field K]

def matrixOf (a b : K) (x : Quaternion K) : Matrix (Fin 2) (Fin 2) K :=
  !![x.re + a*x.imJ + b*x.imK, x.imI+b*x.imJ-a*x.imK;
     -x.imI+b*x.imJ-a*x.imK, x.re-a*x.imJ-b*x.imK]

def splitHom (a b : K) (hab : a^2+b^2 = -1) : Quaternion K →+* Matrix (Fin 2) (Fin 2) K where
  toFun := matrixOf a b
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring
  map_mul' x y := by
    have hb : b^2= -1-a^2 := by linear_combination hab
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixOf,Matrix.mul_apply,Fin.sum_univ_two] <;> ring_nf <;> rw [hb] <;> ring

lemma split_det (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).det = normSq x := by
  change (matrixOf a b x).det = _
  simp [Matrix.det_fin_two,matrixOf,normSq_def']
  linear_combination -(x.imJ^2+x.imK^2)*hab

lemma split_trace (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).trace = 2*x.re := by
  change (matrixOf a b x).trace = _
  simp [Matrix.trace_fin_two,matrixOf]
  ring

lemma split_star (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    splitHom a b hab (star x) = (splitHom a b hab x).adjugate := by
  change matrixOf a b (star x) = (matrixOf a b x).adjugate
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring

def quaternionOf (a b : K) (m : Matrix (Fin 2) (Fin 2) K) : Quaternion K :=
  ⟨(m 0 0+m 1 1)/2,(m 0 1-m 1 0)/2,
    -(a*(m 0 0-m 1 1) + b*(m 0 1+m 1 0))/2,
    -(b*(m 0 0-m 1 1) - a*(m 0 1+m 1 0))/2⟩

lemma split_iso (a b : K) (hab : a^2+b^2 = -1) (htwo : (2:K) ≠ 0) :
    Function.Bijective (splitHom a b hab) := by
  have hb : b^2 = -1-a^2 := by linear_combination hab
  have left : Function.LeftInverse (quaternionOf a b) (splitHom a b hab) := by
    intro x
    change quaternionOf a b (matrixOf a b x) = x
    ext <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  have right : Function.RightInverse (quaternionOf a b) (splitHom a b hab) := by
    intro M
    change matrixOf a b (quaternionOf a b M) = M
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  exact ⟨left.injective,right.surjective⟩

lemma exists_splitting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a b : ZMod p, a^2+b^2 = -1 ∧ (2:ZMod p) ≠ 0 := by
  obtain ⟨a,b,ha,hb,h⟩ := Nat.sq_add_sq_zmodEq p (-1)
  refine ⟨a,b,?_,?_⟩
  · exact_mod_cast ((ZMod.intCast_eq_intCast_iff _ _ _).mpr h)
  · intro he
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using he)
    have := (Nat.dvd_prime Nat.prime_two).mp hh
    have := (Fact.out : p.Prime).ne_one
    tauto

end TunnellQuaternion

end

section

/- Projective lines and rank-one quaternion reductions modulo an odd prime. -/

namespace TunnellQuaternion

open Matrix

variable {K : Type*} [Field K]
abbrev M2 (K : Type*) := Matrix (Fin 2) (Fin 2) K
abbrev V2 (K : Type*) := Fin 2 → K

def inLine (l : Option K) (M : M2 K) : Prop :=
  match l with
  | none => ∀ j, M 0 j = 0
  | some r => ∀ j, M 1 j = r*M 0 j

def direction (l : Option K) : V2 K := match l with
  | none => ![0,1]
  | some r => ![1,r]

def rowOf (l : Option K) (M : M2 K) : V2 K := match l with
  | none => M 1
  | some _ => M 0

lemma line_factored {l : Option K} {M : M2 K} (h : inLine l M) :
    vecMulVec (direction l) (rowOf l M) = M := by
  ext i j
  cases l <;> fin_cases i <;> fin_cases j <;> simp_all [inLine,rowOf,direction,vecMulVec]

lemma line_mul {l : Option K} {M : M2 K} (h : inLine l M) (B : M2 K) :
    inLine l (M*B) := by
  cases l with
  | none => change ∀ j, M 0 j = 0 at h; intro j; simp [Matrix.mul_apply,h]
  | some r =>
    intro j
    change ∀ j, M 1 j=r*M 0 j at h
    simp [Matrix.mul_apply,h,mul_assoc,mul_add]

lemma line_smul {l : Option K} {M : M2 K} (h : inLine l M) (t : K) :
    inLine l (t • M) := by
  cases l with
  | none => change ∀ j, M 0 j = 0 at h; intro j; simp [h]
  | some r => intro j; change ∀ j, M 1 j = r*M 0 j at h; simp [h,mul_left_comm]

lemma det_line {l : Option K} {M : M2 K} (h : inLine l M) : M.det=0 := by
  cases l <;> simp_all [inLine, Matrix.det_fin_two] <;> ring

lemma line_unique (M : M2 K) (h : M≠0) (hd : M.det=0) : ∃! l, inLine l M := by
  by_cases h0 : ∀ j, M 0 j=0
  · refine ⟨none,h0,?_⟩
    rintro (_|r) he
    · rfl
    · change ∀ j, M 1 j=r*M 0 j at he; exfalso; apply h; ext i j; fin_cases i <;> simp [h0,he]
  · obtain ⟨j,hj⟩ := not_forall.mp h0
    refine ⟨some (M 1 j/M 0 j),?_,?_⟩
    · intro k
      rw [div_mul_eq_mul_div,eq_div_iff hj]
      rw [Matrix.det_fin_two] at hd
      fin_cases j <;> fin_cases k
      · rfl
      · change M 1 1 * M 0 0 = M 1 0 * M 0 1; linear_combination hd
      · change M 1 0 * M 0 1 = M 1 1 * M 0 0; linear_combination -hd
      · rfl
    · rintro (_|r) he
      · exact False.elim (hj (he j))
      · congr 1
        exact (eq_div_iff hj).mpr (he j).symm

lemma adj_mul_zero_iff {l : Option K} {A : M2 K} (hA : A≠0)
    (hdl : inLine l A) (B : M2 K) : A.adjugate * B = 0 ↔ inLine l B := by
  by_cases hr : rowOf l A = 0
  · have := line_factored hdl
    rw [hr, Matrix.vecMulVec_zero] at this
    exact False.elim (hA this.symm)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
  rw [Matrix.adjugate_fin_two]
  cases l with
  | none =>
    change ∀ j, A 0 j=0 at hdl
    change A 1 i ≠ 0 at hi
    constructor
    · intro h j
      have h₀ := congrArg (fun M:M2 K => M 0 j) h
      have h₁ := congrArg (fun M:M2 K => M 1 j) h
      simp [Matrix.mul_apply,Fin.sum_univ_two,hdl] at h₀ h₁
      fin_cases i <;> grind
    · intro h; change ∀ j, B 0 j=0 at h; ext i j; fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hdl,h]
  | some r =>
    change ∀ j, A 1 j=r*A 0 j at hdl
    change A 0 i ≠ 0 at hi
    constructor
    · intro h j
      have h₀ := congrArg (fun M:M2 K => M 0 j) h
      have h₁ := congrArg (fun M:M2 K => M 1 j) h
      simp [Matrix.mul_apply,Fin.sum_univ_two,hdl] at h₀ h₁
      fin_cases i
      · apply mul_left_cancel₀ hi
        change A 0 0 * B 1 j = A 0 0 * (r*B 0 j)
        linear_combination h₁
      · apply mul_left_cancel₀ hi
        change A 0 1 * B 1 j = A 0 1 * (r*B 0 j)
        linear_combination -h₀
    · intro h; change ∀ j, B 1 j=r*B 0 j at h
      ext i j; fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hdl,h] <;> ring

lemma reversed_product_zero {A B : M2 K} (ha : A.det=0) (hb : B.det=0)
    (hab : A*B≠0) (htr : (A*B).trace=0) : B*A=0 := by
  obtain ⟨l,hl,_⟩ := line_unique A (by rintro rfl; simp at hab) ha
  obtain ⟨m,hm,_⟩ := line_unique B (by rintro rfl; simp at hab) hb
  rw [←line_factored hl,←line_factored hm] at hab htr ⊢
  let u := direction l
  let v := rowOf l A
  let x := direction m
  let y := rowOf m B
  have mul (a b c d : V2 K) : vecMulVec a b * vecMulVec c d = (b ⬝ᵥ c) • vecMulVec a d := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [mul_left_comm]
  rw [mul] at hab htr ⊢
  have hd : (v ⬝ᵥ x) ≠ 0 := by intro h; exact hab (by rw [show rowOf l A ⬝ᵥ direction m = 0 from h,zero_smul])
  rw [Matrix.trace_smul,Matrix.trace_vecMulVec] at htr
  have e := (mul_eq_zero.mp htr).resolve_left hd
  rw [dotProduct_comm, e,zero_smul]

end TunnellQuaternion

end

section

/- Descent of integral Hamilton quaternions inside specified right ideals modulo an odd prime. -/

namespace TunnellQuaternion

open Quaternion


def redFun (p : ℕ) (q : Quaternion ℤ) : Quaternion (ZMod p) := ⟨q.re,q.imI,q.imJ,q.imK⟩

def red (p : ℕ) : Quaternion ℤ →+* Quaternion (ZMod p) where
  toFun := redFun p
  map_add' x y := by apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> simp [redFun]
  map_mul' x y := by
    apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> simp [redFun]
  map_zero' := by ext <;> simp [redFun]
  map_one' := by ext <;> simp [redFun]

lemma red_apply (p : ℕ) (x : Quaternion ℤ) : red p x = redFun p x := rfl

lemma red_star (p : ℕ) (x : Quaternion ℤ) : red p (star x) = star (red p x) := by
  change redFun p (star x) = star (redFun p x)
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [redFun]

lemma red_norm (p : ℕ) (x : Quaternion ℤ) : ((normSq x:ℤ) : ZMod p) = normSq (red p x) := by
  rw [normSq_def',normSq_def']
  simp [red_apply,redFun]

lemma red_smul (p : ℕ) (t : ℤ) (x : Quaternion ℤ) :
    red p (t • x) = (t:ZMod p) • red p x := by
  change redFun p (t • x) = (t:ZMod p) • redFun p x
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul] <;> simp [redFun,smul_eq_mul]

lemma norm_smul (t : ℤ) (x : Quaternion ℤ) : normSq (t • x) = t^2*normSq x := by
  rw [← coe_mul_eq_smul, map_mul, normSq_coe]

lemma div_iff (m : ℕ) (q : Quaternion ℤ) : red m q = 0 ↔ ∃ v : Quaternion ℤ, q = (m:ℤ) • v := by
  constructor
  · intro h
    have hd (a : ℤ) (ha : (a:ZMod m)=0) : a=(m:ℤ)*(a/m) :=
      (Int.mul_ediv_cancel' (ZMod.intCast_zmod_eq_zero_iff_dvd a m |>.mp ha)).symm
    refine ⟨⟨q.re/m,q.imI/m,q.imJ/m,q.imK/m⟩,?_⟩
    cases q with | mk a b c d =>
      exact QuaternionAlgebra.ext (hd a (congrArg (fun q : Quaternion (ZMod m) => q.re) h)) (hd b (congrArg (fun q : Quaternion (ZMod m) => q.imI) h))
        (hd c (congrArg (fun q : Quaternion (ZMod m) => q.imJ) h)) (hd d (congrArg (fun q : Quaternion (ZMod m) => q.imK) h))
  · rintro ⟨v,rfl⟩
    rw [red_smul]; simp

def lift (m : ℕ) (x : Quaternion (ZMod m)) : Quaternion ℤ :=
  ⟨x.re.valMinAbs,x.imI.valMinAbs,x.imJ.valMinAbs,x.imK.valMinAbs⟩

@[simp] lemma red_lift (m : ℕ) (x : Quaternion (ZMod m)) : red m (lift m x)=x := by
  change redFun m (lift m x)=x
  apply QuaternionAlgebra.ext <;> dsimp only [redFun,lift] <;> simp

lemma norm_lift_lt {m : ℕ} [NeZero m] (hm : Odd m) (x : Quaternion (ZMod m)) :
    normSq (lift m x) < (m:ℤ)^2 := by
  have hn : 0<(m:ℤ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have h (a : ZMod m) : 4*a.valMinAbs^2 < (m:ℤ)^2 := by
    obtain ⟨hl,hu⟩ := a.valMinAbs_mem_Ioc
    have hm' := hm
    rcases hm' with ⟨k,hk⟩
    have hu2 : a.valMinAbs*2 < (m:ℤ) := by omega
    nlinarith [mul_pos (sub_pos.mpr hu2) (by linarith [hl] : 0<(m:ℤ)+a.valMinAbs*2)]
  rw [normSq_def']
  dsimp only [lift]
  linarith [h x.re,h x.imI,h x.imJ,h x.imK]

lemma even_descent (x : Quaternion ℤ) (h : Even (normSq x)) :
    ∃ r : Quaternion ℤ, normSq r=2 ∧ red 2 (x*r)=0 := by
  let i : Quaternion ℤ := ⟨1,1,0,0⟩
  let j : Quaternion ℤ := ⟨1,0,1,0⟩
  let k : Quaternion ℤ := ⟨1,0,0,1⟩
  have ee : normSq (red 2 x)=0 := by rw [←red_norm]; exact h.intCast_zmod_two
  letI : DecidableEq (Quaternion (ZMod 2)) := (Quaternion.equivProd _).decidableEq
  have claim : ∀ w : Quaternion (ZMod 2), normSq w=0 →
      w*red 2 i=0 ∨ w*red 2 j=0 ∨ w*red 2 k=0 := by
    intro ⟨a,b,c,d⟩
    revert a b c d
    decide
  rcases claim _ ee with h|h|h
  · exact ⟨i,by decide, by simpa using h⟩
  · exact ⟨j,by decide, by simpa using h⟩
  · exact ⟨k,by decide, by simpa using h⟩

theorem find_generator {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) (S : Set (Quaternion (ZMod p)))
    (hS : ∀ a ∈ S, ∀ b, a*b ∈ S)
    (hSc : ∀ (r : ZMod p) a, a ∈ S → r • a ∈ S)
    (hzero : ∀ a ∈ S, normSq a=0) (hne : ∃ a ∈ S, a≠0) :
    ∃ q : Quaternion ℤ, normSq q = p ∧ red p q ∈ S := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hodd := hp.odd_of_ne_two ho
  have initial : ∃ m : ℕ, 0 < m ∧ m < p ∧ ∃ x : Quaternion ℤ, normSq x = (m:ℤ)*p ∧ red p x ∈ S := by
    obtain ⟨a,ha,ha0⟩ := hne
    let x := lift p a
    have hr : red p x = a := red_lift p a
    have hd : (p:ℤ) ∣ normSq x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by rw [red_norm,hr,hzero _ ha])
    obtain ⟨v,hv⟩ := hd
    have hx : 0 < normSq x := (normSq_nonneg (a:=x)).lt_of_ne' (normSq_ne_zero.mpr
      (fun he => ha0 (by rw [←hr,he,map_zero])))
    have hpos : 0 < v := pos_of_mul_pos_right (hv ▸ hx) (by positivity : (0:ℤ) ≤ p)
    have hlt := norm_lift_lt hodd a
    change normSq x < (p:ℤ)^2 at hlt
    refine ⟨v.toNat,by omega,?_,x,?_,hr ▸ ha⟩
    · rw [hv,sq] at hlt
      have := lt_of_mul_lt_mul_left hlt (by positivity : (0:ℤ) ≤ p)
      omega
    · rw [Int.toNat_of_nonneg hpos.le,hv,mul_comm]
  obtain ⟨m,⟨hm0,hmp,x,hx,hxs⟩,minimal⟩ := Nat.findX initial
  by_cases hm1 : m=1
  · subst m; exact ⟨x,by simpa using hx,hxs⟩
  have hm : 1 < m := by omega
  have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
  have hm0' : (0:ℤ) < m := by exact_mod_cast hm0
  have preserve {d : ℕ} (hd : 0 < d) (hdp : d < p) {r y : Quaternion ℤ}
      (hy : x*r = (d:ℤ) • y) : red p y ∈ S := by
    have hd0 : (d:ZMod p)≠0 := fun hh =>
      have hh' := (ZMod.natCast_eq_zero_iff _ _).mp hh
      (Nat.not_dvd_of_pos_of_lt hd hdp) hh'
    have hs := hS _ hxs (red p r)
    rw [←map_mul,hy,red_smul] at hs
    have := hSc ((d:ZMod p)⁻¹) _ hs
    simpa [smul_smul,hd0] using this
  exfalso
  by_cases he : Even m
  · obtain ⟨u,hu⟩ := he
    have hx2 : Even (normSq x) := by rw [hx]; exact (by exact_mod_cast (show Even m from ⟨u,hu⟩) : Even (m:ℤ)).mul_right _
    obtain ⟨r,hr,hr0⟩ := even_descent x hx2
    obtain ⟨y,hy⟩ := (div_iff 2 _).mp hr0
    have hnorm := congrArg normSq hy
    rw [map_mul,hx,hr,norm_smul] at hnorm
    have hu' : (m:ℤ)=u+u := by exact_mod_cast hu
    refine minimal u (by omega) ⟨by omega,by omega,y,?_,preserve (d:=2) (by decide) (by omega) hy⟩
    norm_num at hnorm
    nlinarith [congrArg (fun k:ℤ => k*p) hu']
  · have hmOdd := Nat.not_even_iff_odd.mp he
    letI : NeZero m := ⟨hm0.ne'⟩
    let r := lift m (red m x)
    have hr : red m r = red m x := red_lift m _
    have hm_norm : ((normSq x:ℤ):ZMod m)=0 := by simp [hx]
    have hd : (m:ℤ) ∣ normSq r := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
      rw [red_norm,hr,←red_norm]; exact hm_norm)
    obtain ⟨u,hu⟩ := hd
    have hr0 : r≠0 := by
      intro hz
      have hz' : red m x=0 := by rw [←hr,hz,map_zero]
      obtain ⟨w,hw⟩ := (div_iff m x).mp hz'
      rw [hw,norm_smul] at hx
      have hdiv : (m:ℤ) ∣ p := ⟨normSq w,by
        apply mul_left_cancel₀ hm0'.ne' (b := (p:ℤ))
        nlinarith [hx]⟩
      have hdvd : m ∣ p := by exact_mod_cast hdiv
      rcases (Nat.dvd_prime hp).mp hdvd with ee|ee <;> omega
    have hupos : 0 < u := pos_of_mul_pos_right (hu ▸ (normSq_nonneg (a:=r)).lt_of_ne' (normSq_ne_zero.mpr hr0)) hm0'.le
    have hless := norm_lift_lt hmOdd (red m x)
    change normSq r < (m:ℤ)^2 at hless
    rw [hu,sq] at hless
    have huLt := lt_of_mul_lt_mul_left hless hm0'.le
    have hz : red m (x*star r)=0 := by
      rw [map_mul,red_star,hr,self_mul_star,←red_norm,hm_norm,coe_zero]
    obtain ⟨y,hy⟩ := (div_iff m _).mp hz
    have hnorm := congrArg normSq hy
    rw [map_mul,normSq_star,norm_smul,hx,hu] at hnorm
    refine minimal u.toNat (by omega) ⟨by omega,by omega,y,?_,preserve hm0 hmp hy⟩
    rw [Int.toNat_of_nonneg hupos.le]
    apply mul_left_cancel₀ (pow_ne_zero 2 hm0'.ne') (b := normSq y)
    linear_combination -hnorm


end TunnellQuaternion

end

section

namespace TunnellEigenlines

open Matrix

abbrev Mat (p : ℕ) := Matrix (Fin 2) (Fin 2) (ZMod p)

def vec {p : ℕ} : Option (ZMod p) → Fin 2 → ZMod p
  | none => ![0, 1]
  | some r => ![1, r]

def invariant {p : ℕ} (W : Mat p) : Option (ZMod p) → Prop
  | none => W 0 1 = 0
  | some r => W 1 0 + W 1 1 * r = r * (W 0 0 + W 0 1 * r)

instance {p : ℕ} [NeZero p] (W : Mat p) (l : Option (ZMod p)) : Decidable (invariant W l) := by
  cases l <;> unfold invariant <;> infer_instance

theorem invariant_iff {p : ℕ} (W : Mat p) (l : Option (ZMod p)) : invariant W l ↔
    ∃ k : ZMod p, W.mulVec (vec l) = k • vec l := by
  cases l with
  | none =>
    constructor
    · intro h
      refine ⟨W 1 1, ?_⟩
      ext i
      fin_cases i <;> simp_all [vec, invariant, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
    · rintro ⟨k, h⟩
      simpa [vec, invariant, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] using congrFun h 0
  | some r =>
    constructor
    · intro h
      refine ⟨W 0 0 + W 0 1 * r, ?_⟩
      ext i
      fin_cases i <;> simp_all [vec, invariant, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, mul_comm]
    · rintro ⟨k, h⟩
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [vec, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at h0 h1
      rw [← h0] at h1
      simpa [invariant, mul_comm] using h1

theorem card_invariant {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (W : Mat p)
    (ht : W.trace = 0) :
    ((Finset.univ.filter (invariant W)).card : ℤ) =
      if W = 0 then (p : ℤ) + 1 else 1 + quadraticChar (ZMod p) (-W.det) := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  by_cases hW : W = 0
  · subst W
    have hall : (Finset.univ.filter (invariant (0 : Mat p))) = Finset.univ := by
      ext l
      cases l <;> simp [invariant]
    simp [hall, ZMod.card]
  rw [if_neg hW]
  have hd : W 1 1 = -W 0 0 := by
    rw [Matrix.trace_fin_two] at ht
    linear_combination ht
  have hdet : -W.det = (W 0 0)^2 + W 0 1 * W 1 0 := by
    rw [Matrix.det_fin_two, hd]
    ring
  by_cases hb : W 0 1 = 0
  · rw [hdet, hb, zero_mul, add_zero]
    by_cases ha : W 0 0 = 0
    · have hc' : W 1 0 ≠ 0 := by
        intro h
        apply hW
        ext i j
        fin_cases i <;> fin_cases j <;> simp_all
      have heq : Finset.univ.filter (invariant W) = {none} := by
        ext l
        cases l <;> simp [invariant, hb, hd, ha, hc']
      simp [heq, ha]
    · have hden := mul_ne_zero h2 ha
      set r : ZMod p := W 1 0 / (2 * W 0 0) with hr
      have hi (s : ZMod p) : invariant W (some s) ↔ s = r := by
        change W 1 0 + W 1 1*s = s*(W 0 0 + W 0 1*s) ↔ _
        rw [hd, hb, zero_mul, add_zero, hr, eq_div_iff hden]
        constructor <;> intro h <;> linear_combination -h
      have heq : Finset.univ.filter (invariant W) = {none, some r} := by
        ext l
        cases l with
        | none => simp [invariant,hb]
        | some s => simpa using hi s
      simp [heq, quadraticChar_sq_one' ha]
  · have hi (r : ZMod p) : invariant W (some r) ↔ (W 0 1*r+W 0 0)^2 = -W.det := by
      change W 1 0 + W 1 1*r = r*(W 0 0 + W 0 1*r) ↔ _
      rw [hd,hdet]
      constructor
      · intro h
        linear_combination -W 0 1*h
      · intro h
        have e : W 0 1*(W 1 0 + -W 0 0*r-r*(W 0 0 + W 0 1*r))=0 := by
          linear_combination -h
        exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hb)
    have hcard : (Finset.univ.filter (invariant W)).card =
        {x : ZMod p | x^2 = -W.det}.toFinset.card := by
      apply Finset.card_nbij' (fun l => W 0 1*l.getD 0 + W 0 0)
        (fun s => some ((s-W 0 0)/W 0 1))
      · intro l hl
        cases l with
        | none => simp [invariant,hb] at hl
        | some r => simpa using (hi r).mp (Finset.mem_filter.mp hl).2
      · intro s hs
        have hs' : s^2 = -W.det := by simpa using hs
        apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hi _).mpr ?_⟩
        have h : W 0 1*((s-W 0 0)/W 0 1)+W 0 0=s := by field_simp; ring
        rw [h, hs']
      · intro l hl
        cases l with
        | none => simp [invariant,hb] at hl
        | some r => simp [hb]
      · intro s _
        change W 0 1*((s-W 0 0)/W 0 1)+W 0 0=s
        field_simp
        ring
    rw [hcard, quadraticChar_card_sqrts hc, add_comm]

end TunnellEigenlines

end

section

/- Norm-prime right divisors parameterized by the projective line at an odd prime. -/

namespace TunnellQuaternion

open Matrix Quaternion

variable {p : ℕ} [Fact p.Prime]

structure Model (p : ℕ) where
  f : Quaternion (ZMod p) ≃+* M2 (ZMod p)
  det (x) : (f x).det=normSq x
  trace (x) : (f x).trace=2*x.re
  bar (x) : f (star x) = (f x).adjugate
  smul (t : ZMod p) (x) : f (t • x)=t • f x

noncomputable def localModel (hp : p≠2) : Model p := Classical.choice <| by
  classical
  obtain ⟨a,b,hab,h2⟩ := exists_splitting p hp
  refine ⟨?_⟩
  exact ⟨RingEquiv.ofBijective (splitHom a b hab) (split_iso a b hab h2),split_det a b hab,
    split_trace a b hab,split_star a b hab,fun t x => by
      change matrixOf a b (t • x) = t • matrixOf a b x
      ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring⟩

variable (M : Model p)

def residue : Quaternion ℤ →+* M2 (ZMod p) := M.f.toRingHom.comp (red p)

lemma residue_zero (x : Quaternion ℤ) : residue M x = 0 ↔ red p x = 0 :=
  M.f.map_eq_zero_iff

lemma residue_star (x : Quaternion ℤ) : residue M (star x) = (residue M x).adjugate := by
  change M.f (red p (star x)) = _
  rw [red_star,M.bar]
  rfl

lemma residue_det (x : Quaternion ℤ) : (residue M x).det = (normSq x : ℤ) :=
  (M.det _).trans (red_norm p x).symm

lemma norm_prime_nonzero {x : Quaternion ℤ} (hx : normSq x = p) : residue M x ≠ 0 := by
  intro h
  obtain ⟨v,hv⟩ := (div_iff p x).mp ((residue_zero M x).mp h)
  have pp := Fact.out (p:=p.Prime)
  have hh := congrArg normSq hv
  rw [hx,norm_smul,pow_two,mul_assoc] at hh
  have eq := mul_left_cancel₀ (by exact_mod_cast pp.ne_zero : (p:ℤ)≠0)
    (show (p:ℤ)*1=p*((p:ℤ)*normSq v) by simpa using hh)
  have hd : (p:ℤ) ∣ 1 := ⟨_,eq⟩
  have hdn : p ∣ 1 := by exact_mod_cast hd
  exact pp.not_dvd_one hdn

lemma exists_at_line (hp : p≠2) (l : Option (ZMod p)) :
    ∃ x : Quaternion ℤ, normSq x = p ∧ inLine l (residue M x) := by
  let S := {a : Quaternion (ZMod p) | inLine l (M.f a)}
  apply find_generator Fact.out hp S
  · intro a ha b; change inLine l (M.f (a*b)); rw [map_mul]; exact line_mul ha _
  · intro r a ha; change inLine l (M.f (r • a)); rw [M.smul]; exact line_smul ha _
  · intro a ha; rw [←M.det]; exact det_line ha
  · let B : M2 (ZMod p) := vecMulVec (direction l) ![1,0]
    refine ⟨M.f.symm B,?_,?_⟩
    · change inLine l (M.f (M.f.symm B))
      rw [M.f.apply_symm_apply]
      cases l <;> intro j <;> fin_cases j <;> simp [B,vecMulVec,direction]
    · intro h
      have := congrArg M.f h
      rw [M.f.apply_symm_apply,map_zero] at this
      cases l with
      | none => simpa [B,vecMulVec,direction] using congrArg (fun m:M2 (ZMod p) => m 1 0) this
      | some r => simpa [B,vecMulVec,direction] using congrArg (fun m:M2 (ZMod p) => m 0 0) this

lemma scalar_cancel (d : ℤ) (hd : d≠0) {x y : Quaternion ℤ} (h : d • x = d • y) : x=y := by
  apply QuaternionAlgebra.ext
  all_goals
    first
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.re) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imI) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imJ) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imK) h)

lemma divide_left {q w : Quaternion ℤ} (hq : normSq q=p) {l : Option (ZMod p)}
    (hl : inLine l (residue M q)) (hw : inLine l (residue M w)) :
    ∃ x, w=q*x := by
  have hz := (adj_mul_zero_iff (norm_prime_nonzero M hq) hl (residue M w)).mpr hw
  rw [←residue_star,←map_mul,residue_zero] at hz
  obtain ⟨x,hx⟩ := (div_iff p _).mp hz
  refine ⟨x,?_⟩
  apply scalar_cancel (p:ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have he := congrArg (q*·) hx
  simpa only [←mul_assoc,self_mul_star,hq,coe_mul_eq_smul,Algebra.mul_smul_comm] using he

lemma same_line_iff {q w : Quaternion ℤ} (hq : normSq q=p) (hw : normSq w=p)
    {l : Option (ZMod p)} (hl : inLine l (residue M q)) :
    inLine l (residue M w) ↔ ∃ u : Quaternion ℤ, normSq u=1 ∧ w=q*u := by
  constructor
  · intro hh
    obtain ⟨u,hu⟩ := divide_left M hq hl hh
    have h := hw
    rw [hu,map_mul,hq] at h
    refine ⟨u,?_,hu⟩
    apply mul_left_cancel₀ (by exact_mod_cast (Fact.out:p.Prime).ne_zero : (p:ℤ)≠0)
    simpa using h
  · rintro ⟨u,_,rfl⟩; rw [map_mul]; exact line_mul hl _

lemma invariant_criterion {l : Option (ZMod p)} {A : M2 (ZMod p)} (hn : A ≠ 0) (hl : inLine l A)
    (W : M2 (ZMod p)) : A.adjugate*W*A=0 ↔ TunnellEigenlines.invariant W l := by
  rw [mul_assoc,adj_mul_zero_iff hn hl]
  obtain ⟨i,hi⟩ : ∃ i, rowOf l A i ≠ 0 := by
    by_contra! hh
    have hr : rowOf l A=0 := funext hh
    have h := line_factored hl
    rw [hr,vecMulVec_zero] at h
    exact hn h.symm
  cases l with
  | none =>
    change ∀ j, A 0 j=0 at hl
    change A 1 i≠0 at hi
    change (∀ j, (W*A) 0 j=0) ↔ W 0 1=0
    simp only [Matrix.mul_apply,Fin.sum_univ_two,hl,mul_zero,zero_add]
    exact ⟨fun h => (mul_eq_zero.mp (h i)).resolve_right hi,by rintro h j; simp [h]⟩
  | some a =>
    change ∀ j, A 1 j=a*A 0 j at hl
    change A 0 i≠0 at hi
    change (∀ j, (W*A) 1 j = a*(W*A) 0 j) ↔ W 1 0+W 1 1*a=a*(W 0 0+W 0 1*a)
    simp only [Matrix.mul_apply,Fin.sum_univ_two,hl,←mul_assoc,←add_mul]
    exact ⟨fun h => mul_right_cancel₀ hi (by simpa [mul_assoc] using h i),
      fun h j => by rw [h,mul_assoc]⟩

end TunnellQuaternion

end

section

/- Eight integral quaternions represent each projective line at an odd prime. -/

namespace TunnellQuaternion

open Finset Quaternion

variable {p : ℕ} [Fact p.Prime] (M : Model p)

lemma unique_class {q : QInt} (hq : normSq q=p) : ∃! l, inLine l (residue M q) := by
  apply line_unique _ (norm_prime_nonzero M hq)
  rw [residue_det,hq]
  simp

noncomputable def classOf (q : QInt) : Option (ZMod p) :=
  if h : normSq q = p then (unique_class M h).exists.choose else none

lemma class_eq_iff {q : QInt} (hq : normSq q=p) (l : Option (ZMod p)) :
    classOf M q=l ↔ inLine l (residue M q) := by
  rw [classOf,dif_pos hq]
  have h := (unique_class M hq).exists.choose_spec
  constructor
  · rintro rfl
    exact h
  · exact fun h' => (unique_class M hq).unique h h'

lemma quatShell_one_card : (quatShell 1).card = 8 := by decide

lemma fiber_class_card (hp : p≠2) (l : Option (ZMod p)) :
    ((quatShell p).filter (fun q => classOf M q = l)).card = 8 := by
  classical
  obtain ⟨q,hq,hl⟩ := exists_at_line M hp l
  rw [←quatShell_one_card]
  symm
  apply card_nbij (fun u => q*u)
  · intro u hu
    have hu' := mem_quatShell.mp hu
    have hqu : normSq (q*u)=p := by rw [map_mul,hq,hu']; simp
    refine mem_filter.mpr ⟨mem_quatShell.mpr hqu,(class_eq_iff M hqu l).mpr ?_⟩
    rw [map_mul]
    exact line_mul hl _
  · intro u hu v hv h
    apply scalar_cancel (p:ℤ) (by exact_mod_cast (Fact.out:p.Prime).ne_zero)
    have he := congrArg (star q * ·) h
    simpa only [←mul_assoc,star_mul_self,hq,coe_mul_eq_smul] using he
  · intro w hw
    obtain ⟨hn,he⟩ := mem_filter.mp hw
    have hn' := mem_quatShell.mp hn
    obtain ⟨u,hu,hw⟩ := (same_line_iff M hq hn' hl).mp ((class_eq_iff M hn' l).mp he)
    exact ⟨u,mem_quatShell.mpr hu,hw.symm⟩

lemma card_class_mem (hp : p≠2) (L : Finset (Option (ZMod p))) :
    ((quatShell p).filter (fun q => classOf M q ∈ L)).card = 8*L.card := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter (quatShell p) L (classOf M) (fun _ => (1:ℕ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  simpa [fiber_class_card M hp,mul_comm] using h.symm

end TunnellQuaternion

end

section

/- The odd-prime recurrence for the number of representations by four squares. -/

namespace TunnellQuaternion

open Finset Quaternion
open scoped Classical

noncomputable section

lemma quat_left_cancel {q u v : QInt} (hq : normSq q≠0) (h : q*u=q*v) : u=v := by
  apply scalar_cancel (normSq q) hq
  have he := congrArg (star q * ·) h
  simpa only [←mul_assoc, star_mul_self,coe_mul_eq_smul] using he


end
end TunnellQuaternion
end

namespace ThreeSquareLift
open Finset Quaternion TunnellQuaternion
open scoped Classical

private noncomputable def pureShell (n : ℕ) := (quatShell n).filter (fun x => x.re=0)
private noncomputable def primitive (p n : ℕ) := (pureShell n).filter (fun x => red p x ≠ 0)

private lemma re_rotate (q x : QInt) (hx : x.re=0) : (star q*x*q).re=0 := by
  have cyc (a b : QInt) : (a*b).re=(b*a).re := by simp only [Quaternion.re_mul]; ring
  rw [cyc,←mul_assoc,self_mul_star,coe_mul_eq_smul,Quaternion.re_smul,hx,smul_zero]

private lemma rotate_inj (q : QInt) (hq : normSq q ≠ 0) : Function.Injective
    (fun x : QInt => star q*x*q) := by
  intro x y he
  have he' := congrArg star he
  simp only [star_mul,star_star] at he'
  have h1 := quat_left_cancel (q:=star q) (by rwa [normSq_star]) he'
  have h2 := congrArg star h1
  simp only [star_mul,star_star] at h2
  exact quat_left_cancel (by rwa [normSq_star]) h2

private lemma data_mem {p n : ℕ} {x : QInt} (hx : x ∈ primitive p n) :
    normSq x=n ∧ x.re=0 ∧ red p x ≠ 0 := by
  obtain ⟨h,hp⟩ := mem_filter.mp hx
  obtain ⟨h,hr⟩ := mem_filter.mp h
  exact ⟨mem_quatShell.mp h,hr,hp⟩

private lemma primitive_lift {p n k : ℕ} [Fact p.Prime] (hp : p ≠ 2) (M : Model p)
    (hk : ∀ x ∈ primitive p n, k ≤
      (univ.filter (fun l => ¬ TunnellEigenlines.invariant (residue M x) l)).card) :
    k * (primitive p n).card ≤ (primitive p (p^2*n)).card := by
  classical
  let D := primitive p n
  let S := primitive p (p^2*n)
  let Q := quatShell p
  let f := fun t : QInt × QInt => star t.2*t.1*t.2
  let G := (D ×ˢ Q).filter (fun t => red p (f t) ≠ 0)
  have hq {q : QInt} (hq : q ∈ Q) := mem_quatShell.mp hq
  have near {x q : QInt} (hh : q ∈ Q) : red p (star q*x*q) ≠ 0 ↔
      ¬TunnellEigenlines.invariant (residue M x) (classOf M q) := by
    apply not_congr
    rw [←residue_zero M,map_mul,map_mul,residue_star]
    exact invariant_criterion (norm_prime_nonzero M (hq hh)) ((class_eq_iff M (hq hh) _).mp rfl) _
  have lower : 8*k*D.card ≤ G.card := by
    have fibers (x : QInt) (hx : x ∈ D) :
        8*k ≤ (Q.filter (fun q => red p (star q*x*q) ≠ 0)).card := by
      let L := univ.filter (fun l => ¬ TunnellEigenlines.invariant (residue M x) l)
      have e : Q.filter (fun q => red p (star q*x*q) ≠ 0) =
          Q.filter (fun q => classOf M q ∈ L) := by
        ext q
        simp only [mem_filter,L,mem_univ,true_and]
        exact and_congr_right (fun hh => near hh)
      rw [e,card_class_mem M hp]
      exact Nat.mul_le_mul_left _ (hk x hx)
    calc 8*k*D.card = ∑ x ∈ D, 8*k := by simp [Nat.mul_comm]
         _ ≤ ∑ x ∈ D,(Q.filter (fun q => red p (star q*x*q) ≠ 0)).card :=
           sum_le_sum fibers
         _ = G.card := by simp only [G,card_filter,sum_product,f]
  have maps : (G:Set _).MapsTo f S := by
    rintro ⟨x,q⟩ h
    obtain ⟨h,hn⟩ := mem_filter.mp h
    obtain ⟨hx,hp⟩ := mem_product.mp h
    obtain ⟨h1,h2,h3⟩ := data_mem hx
    apply mem_filter.mpr ⟨mem_filter.mpr ⟨mem_quatShell.mpr ?_,re_rotate q x h2⟩,hn⟩
    simp only [f,map_mul,normSq_star,hq hp,h1,Nat.cast_mul,Nat.cast_pow]
    ring
  have upper : G.card ≤ 8*S.card := by
    rw [card_eq_sum_card_fiberwise maps]
    calc _ ≤ ∑ y ∈ S,8 := by
           apply sum_le_sum
           intro y hy
           obtain ⟨yn,yr,yp⟩ := data_mem hy
           have nz : residue M y ≠ 0 := fun e => yp ((residue_zero M y).mp e)
           have det : (residue M y).det=0 := by rw [residue_det,yn]; simp
           obtain ⟨l,hl,hu⟩ := line_unique _ nz det
           rw [← fiber_class_card M hp l]
           apply card_le_card_of_injOn (fun t : QInt×QInt => star t.2)
           · rintro ⟨x,q⟩ hh
             obtain ⟨h,he⟩ := mem_filter.mp hh
             obtain ⟨hs,_⟩ := mem_filter.mp h
             have hq' := hq (mem_product.mp hs).2
             have hstar : normSq (star q)=p := by rwa [normSq_star]
             have hc := (class_eq_iff M hstar _).mp rfl
             refine mem_filter.mpr ⟨mem_quatShell.mpr hstar,hu _ ?_⟩
             rw [← he]
             change inLine _ (residue M (star q*x*q))
             rw [map_mul,map_mul]
             exact line_mul (line_mul hc _) _
           · rintro ⟨x,q⟩ hx ⟨z,q'⟩ hz he
             have eq : q=q' := star_injective he
             subst q'
             obtain ⟨h,hf⟩ := mem_filter.mp hx
             obtain ⟨hd,_⟩ := mem_filter.mp h
             have hq' := hq (mem_product.mp hd).2
             have q0 : normSq q ≠ 0 := by
               rw [hq']
               exact_mod_cast (Fact.out : p.Prime).ne_zero
             exact Prod.ext (rotate_inj q q0 (hf.trans (mem_filter.mp hz).2.symm)) rfl
         _ = 8*S.card := by simp [Nat.mul_comm]
  have e := lower.trans upper
  rw [Nat.mul_assoc] at e
  exact Nat.le_of_mul_le_mul_left e (by decide : 0 < 8)

private lemma nilpotent_lift {p n : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ n) :
    p*(primitive p n).card ≤ (primitive p (p^2*n)).card := by
  let M := localModel hp
  apply primitive_lift hp M
  intro x hx
  obtain ⟨hn,hr,hnz⟩ := data_mem hx
  have nz : residue M x ≠ 0 := fun e => hnz ((residue_zero M x).mp e)
  have tr : (residue M x).trace=0 := by
    rw [show residue M x=M.f (red p x) by rfl,M.trace]
    change 2*(x.re:ZMod p)=0
    rw [hr]
    simp
  have hd' : (residue M x).det=0 := by
    rw [residue_det,hn,Int.cast_natCast,ZMod.natCast_eq_zero_iff]
    exact hd
  have h := TunnellEigenlines.card_invariant hp _ tr
  rw [if_neg nz,hd'] at h
  simp at h
  have hs := card_filter_add_card_filter_not (s:=univ) (TunnellEigenlines.invariant (residue M x))
  simp only [card_univ,Fintype.card_option,ZMod.card] at hs
  omega

end ThreeSquareLift


namespace ThreeSquareLift
open Finset Quaternion TunnellQuaternion
open scoped Classical

private def natShell (n : ℕ) :=
  ((range (n+1)) ×ˢ ((range (n+1)) ×ˢ (range (n+1)))).filter
    (fun v : ℕ×ℕ×ℕ => v.1^2+v.2.1^2+v.2.2^2=n)

private lemma mem_nat {n a b c : ℕ} : (a,b,c) ∈ natShell n ↔ a^2+b^2+c^2=n := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨?_,h⟩
    simp only [mem_product,mem_range]
    constructor
    · nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) a]
    constructor <;> nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) b,
      Nat.le_self_pow (by decide : 2 ≠ 0) c]

private lemma all_pos {n a b c : ℕ} (hm : n%4=3) (h : a^2+b^2+c^2=n) :
    0 < a ∧ 0 < b ∧ 0 < c := by
  have sq (j : ℕ) : j^2%4 ≤ 1 := by
    rw [Nat.pow_mod]
    have bound := Nat.mod_lt j (by decide : 0 < 4)
    interval_cases j%4 <;> decide
  have hh := congrArg (·%4) h
  have ha := sq a
  have hb := sq b
  have hc := sq c
  by_contra! bad
  rcases Nat.eq_zero_or_pos a with rfl|pa
  · simp at hh
    omega
  rcases Nat.eq_zero_or_pos b with rfl|pb
  · simp at hh
    omega
  have ez : c=0 := by omega
  subst c
  simp at hh
  omega

private def enc (b : Bool) (a : ℕ) : ℤ := if b then -(a:ℤ) else a

private lemma enc_sq (b : Bool) (a : ℕ) : (enc b a)^2=(a:ℤ)^2 := by
  cases b <;> simp [enc]

private lemma enc_abs (b : Bool) (a : ℕ) : (enc b a).natAbs=a := by
  cases b <;> simp [enc]

private lemma enc_recover (a : ℤ) : enc (decide (a<0)) a.natAbs=a := by
  by_cases h : a < 0
  · simp [enc,h,abs_of_neg h]
  · simp [enc,h,abs_of_nonneg (le_of_not_gt h)]

private lemma enc_sign (b : Bool) {a : ℕ} (h : 0 < a) : decide (enc b a < 0)=b := by
  cases b <;> simp [enc,h]

private lemma count_signs {n : ℕ} (hn : n%4=3) :
    (pureShell n).card=8*(natShell n).card := by
  let S := natShell n ×ˢ (univ : Finset (Bool×Bool×Bool))
  let f (z : (ℕ×ℕ×ℕ)×(Bool×Bool×Bool)) : QInt :=
    ⟨0,enc z.2.1 z.1.1,enc z.2.2.1 z.1.2.1,enc z.2.2.2 z.1.2.2⟩
  let g (q : QInt) := ((q.imI.natAbs,q.imJ.natAbs,q.imK.natAbs),
    (decide (q.imI<0),decide (q.imJ<0),decide (q.imK<0)))
  have eq : S.card=(pureShell n).card := by
    apply card_nbij' f g
    · rintro ⟨⟨a,b,c⟩,i,j,k⟩ h
      have he := mem_nat.mp (mem_product.mp h).1
      refine mem_filter.mpr ⟨mem_quatShell.mpr ?_,rfl⟩
      simp only [f,normSq_mk,zero_pow (by decide : 2 ≠ 0),zero_add,enc_sq]
      exact_mod_cast he
    · intro q h
      obtain ⟨hq,hr⟩ := mem_filter.mp h
      have he := mem_quatShell.mp hq
      rw [Quaternion.normSq_def',hr,zero_pow (by decide : 2 ≠ 0),zero_add] at he
      refine mem_product.mpr ⟨mem_nat.mpr ?_,mem_univ _⟩
      exact_mod_cast (show ((q.imI.natAbs:ℤ)^2+(q.imJ.natAbs:ℤ)^2+(q.imK.natAbs:ℤ)^2)=(n:ℤ) by
        simpa only [Int.natCast_natAbs,sq_abs] using he)
    · rintro ⟨⟨a,b,c⟩,i,j,k⟩ h
      have hh := all_pos hn (mem_nat.mp (mem_product.mp h).1)
      simp only [g,f,enc_abs,enc_sign _ hh.1,enc_sign _ hh.2.1,enc_sign _ hh.2.2]
    · intro q h
      obtain ⟨_,hr⟩ := mem_filter.mp h
      apply QuaternionAlgebra.ext <;> simp [f,g,hr,enc_recover]
  rw [←eq,card_product]
  simp [Nat.mul_comm]

private lemma scaled {p n : ℕ} (hp : 0 < p) :
    (primitive p (p^2*n)).card+(pureShell n).card=(pureShell (p^2*n)).card := by
  classical
  have pp : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have bij : (pureShell n).card=
      ((pureShell (p^2*n)).filter (fun q => red p q=0)).card := by
    apply card_nbij (fun x : QInt => (p:ℤ) • x)
    · intro x hx
      obtain ⟨hq,hr⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_quatShell.mpr (by
        rw [norm_smul,mem_quatShell.mp hq]; push_cast; rfl),by rw [Quaternion.re_smul,hr,smul_zero]⟩,
        (div_iff p _).mpr ⟨x,rfl⟩⟩
    · intro x hx y hy h
      exact scalar_cancel _ pp h
    · intro q h
      obtain ⟨hh,h0⟩ := mem_filter.mp h
      obtain ⟨x,rfl⟩ := (div_iff p _).mp h0
      obtain ⟨hq,hr⟩ := mem_filter.mp hh
      have he := mem_quatShell.mp hq
      rw [norm_smul,Nat.cast_mul,Nat.cast_pow] at he
      have ex := mul_left_cancel₀ (pow_ne_zero 2 pp) he
      change (p:ℤ)*x.re=0 at hr
      exact ⟨x, mem_filter.mpr ⟨mem_quatShell.mpr ex,(mul_eq_zero.mp hr).resolve_left pp⟩,rfl⟩
  rw [bij,Nat.add_comm]
  exact card_filter_add_card_filter_not (s:=pureShell (p^2*n)) (fun q => red p q=0)

end ThreeSquareLift


namespace ThreeSquareLift
open Finset Quaternion TunnellQuaternion
open scoped Classical

private lemma odd_scale {p n : ℕ} (hp : p%2=1) (hn : n%4=3) : (p^2*n)%4=3 := by
  have h : p%4=1 ∨ p%4=3 := by omega
  rw [Nat.mul_mod,Nat.pow_mod]
  rcases h with h|h <;> rw [h,hn] <;> decide


private lemma general_lift {p n : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (p-1)*(primitive p n).card ≤ (primitive p (p^2*n)).card := by
  let M := localModel hp
  apply primitive_lift hp M
  intro x hx
  obtain ⟨hn,hr,hnz⟩ := data_mem hx
  have nz : residue M x ≠ 0 := fun e => hnz ((residue_zero M x).mp e)
  have tr : (residue M x).trace=0 := by
    rw [show residue M x=M.f (red p x) by rfl,M.trace]
    change 2*(x.re:ZMod p)=0
    rw [hr]
    simp
  have h := TunnellEigenlines.card_invariant hp _ tr
  rw [if_neg nz] at h
  let d := -(residue M x).det
  have ch : quadraticChar (ZMod p) d ≤ 1 := by
    by_cases h0 : d=0
    · simp [h0,quadraticChar_zero]
    · rcases quadraticChar_dichotomy h0 with hh|hh <;> omega
  have hs := card_filter_add_card_filter_not (s:=univ) (TunnellEigenlines.invariant (residue M x))
  simp only [card_univ,Fintype.card_option,ZMod.card] at hs
  dsimp [d] at ch
  omega

end ThreeSquareLift

open ThreeSquareLift Finset Quaternion TunnellQuaternion
open scoped Classical

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1.H3 := by
  intro p n hp ho hn hn2
  letI : Fact p.Prime := ⟨hp⟩
  have hn4 : n%4=3 := by omega
  have h2 := odd_scale ho hn4
  have hl := general_lift (p:=p) (n:=n) (by omega)
  have hs := scaled (n:=n) hp.pos
  have all : primitive p n=pureShell n := by
    apply filter_true_of_mem
    intro x hx hz
    obtain ⟨v,hh⟩ := (div_iff p x).mp hz
    have h := mem_quatShell.mp (mem_filter.mp hx).1
    rw [hh,norm_smul] at h
    have : (p:ℤ)^2 ∣ (n:ℤ) := ⟨normSq v,h.symm⟩
    exact hn2 (by exact_mod_cast this)
  rw [all] at hl
  have pe : p=p-1+1 := by have := hp.pos; omega
  have cb : p*(pureShell n).card ≤ (pureShell (p^2*n)).card := by
    calc p*(pureShell n).card=(p-1)*(pureShell n).card+(pureShell n).card := by
           conv_lhs => rw [pe,Nat.add_mul,Nat.one_mul]
         _ ≤ _ := by omega
  rw [count_signs hn4,count_signs h2] at cb
  change p*(natShell n).card ≤ (natShell (p^2*n)).card
  nlinarith only [cb]


