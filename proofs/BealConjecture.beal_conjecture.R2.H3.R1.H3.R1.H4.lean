import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H3_R1
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.ZMod.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Parity

-- Credit: @Hennyrick

namespace BealCubicNorm

abbrev Triple := Int × Int × Int

/-- Multiplication in the integral power basis of a root of X³ − 2. -/
def mul (x y : Triple) : Triple :=
  (x.1*y.1 + 2*(x.2.1*y.2.2+x.2.2*y.2.1),
   x.1*y.2.1+x.2.1*y.1+2*x.2.2*y.2.2,
   x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1)

def norm (x : Triple) : Int :=
  x.1^3 + 2*x.2.1^3 + 4*x.2.2^3 - 6*x.1*x.2.1*x.2.2

theorem norm_mul (x y : Triple) : BealCubicNorm.norm (mul x y) = BealCubicNorm.norm x * BealCubicNorm.norm y := by
  dsimp [BealCubicNorm.norm, mul]
  grind

theorem mul_assoc (x y z : Triple) : mul (mul x y) z = mul x (mul y z) := by
  dsimp [mul]
  grind

theorem mul_comm (x y : Triple) : mul x y = mul y x := by
  dsimp [mul]
  grind

def one : Triple := (1,0,0)

theorem mul_one (x : Triple) : mul x one = x := by simp [one,mul]
theorem one_mul (x : Triple) : mul one x = x := by rw [mul_comm, mul_one]

def pow (x : Triple) : Nat → Triple
  | 0 => one
  | n+1 => mul (pow x n) x

def eps : Triple := (-1,1,0)
def epsInv : Triple := (1,1,1)

theorem eps_mul_inv : mul eps epsInv = one := by decide
theorem inv_mul_eps : mul epsInv eps = one := by decide

theorem eps_norm : BealCubicNorm.norm eps = 1 := by decide
theorem epsInv_norm : BealCubicNorm.norm epsInv = 1 := by decide


end BealCubicNorm

namespace BealCubicInterval

structure BoxInterval where
  lo : Int
  hi : Int
deriving DecidableEq

def product (B C : BoxInterval) : BoxInterval :=
  ⟨min (min (B.lo*C.lo) (B.lo*C.hi)) (min (B.hi*C.lo) (B.hi*C.hi)),
   max (max (B.lo*C.lo) (B.lo*C.hi)) (max (B.hi*C.lo) (B.hi*C.hi))⟩

def scale (d : Int) (B : BoxInterval) : BoxInterval := ⟨d*B.lo,d*B.hi⟩

private theorem between (a b x k l u : Int) (hx : a ≤ x ∧ x ≤ b)
    (ha : l ≤ a*k ∧ a*k ≤ u) (hb : l ≤ b*k ∧ b*k ≤ u) :
    l ≤ x*k ∧ x*k ≤ u := by
  by_cases hk : 0 ≤ k
  · exact ⟨Int.le_trans ha.1 (Int.mul_le_mul_of_nonneg_right hx.1 hk),
           Int.le_trans (Int.mul_le_mul_of_nonneg_right hx.2 hk) hb.2⟩
  · have hk' : k ≤ 0 := by omega
    exact ⟨Int.le_trans hb.1 (Int.mul_le_mul_of_nonpos_right hx.2 hk'),
           Int.le_trans (Int.mul_le_mul_of_nonpos_right hx.1 hk') ha.2⟩

theorem product_bounds (B C : BoxInterval) {d e x y : Int} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hx : d*B.lo ≤ x ∧ x ≤ d*B.hi) (hy : e*C.lo ≤ y ∧ y ≤ e*C.hi) :
    (d*e)*(product B C).lo ≤ x*y ∧ x*y ≤ (d*e)*(product B C).hi := by
  let l := (product B C).lo
  let u := (product B C).hi
  have hde := Int.mul_nonneg hd he
  have corner (i j : Int) (h : l ≤ i*j ∧ i*j ≤ u) :
      d*e*l ≤ (d*i)*(e*j) ∧ (d*i)*(e*j) ≤ d*e*u := by
    have hm : (d*i)*(e*j) = d*e*(i*j) := by grind
    rw [hm]
    exact ⟨Int.mul_le_mul_of_nonneg_left h.1 hde, Int.mul_le_mul_of_nonneg_left h.2 hde⟩
  have left := between _ _ _ _ _ _ hx
    (corner B.lo C.lo (by dsimp [l,u,product]; omega))
    (corner B.hi C.lo (by dsimp [l,u,product]; omega))
  have right := between _ _ _ _ _ _ hx
    (corner B.lo C.hi (by dsimp [l,u,product]; omega))
    (corner B.hi C.hi (by dsimp [l,u,product]; omega))
  rw [Int.mul_comm x y]
  apply between _ _ _ _ _ _ hy
  · simpa only [Int.mul_comm (e*C.lo) x] using left
  · simpa only [Int.mul_comm (e*C.hi) x] using right

private theorem cube_mono {a b : Int} (h : a ≤ b) : a^3 ≤ b^3 := by
  have hf : 0 ≤ 2*(a^2 + a*b + b^2) := by
    have ha := Int.sq_nonneg a
    have hb := Int.sq_nonneg b
    have hab := Int.sq_nonneg (a+b)
    grind
  have hp := Int.mul_nonneg (show 0 ≤ b-a by omega) (show 0 ≤ a^2 + a*b + b^2 by omega)
  grind

theorem cube_bounds (B : BoxInterval) {d x : Int} (hx : d*B.lo ≤ x ∧ x ≤ d*B.hi) :
    d^3*B.lo^3 ≤ x^3 ∧ x^3 ≤ d^3*B.hi^3 := by
  simpa only [Int.mul_pow] using And.intro (cube_mono hx.1) (cube_mono hx.2)

end BealCubicInterval

namespace BealCubicCover

open BealCubicNorm BealCubicInterval

/-- Coordinates are scaled by six. A bit specifies which endpoint of the
original unit cube is chosen as the approximating integral coordinate. -/
def cell (i : Fin 6) (s : Fin 2) : BoxInterval :=
  ⟨(i.val:Int) - 6*s.val, (i.val:Int) + 1 - 6*s.val⟩

def normBounds (B C T : BoxInterval) : BoxInterval :=
  let p := product (product B C) T
  ⟨B.lo^3 + 2*C.lo^3 + 4*T.lo^3 - 6*p.hi,
   B.hi^3 + 2*C.hi^3 + 4*T.hi^3 - 6*p.lo⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem finite_cover : ∀ i j k : Fin 6, ∃ s t u : Fin 2,
    -208 ≤ (normBounds (cell i s) (cell j t) (cell k u)).lo ∧
    (normBounds (cell i s) (cell j t) (cell k u)).hi ≤ 208 := by
  decide +kernel

theorem norm_bounds (B C T : BoxInterval) {d x y z : Int} (hd : 0 ≤ d)
    (hx : d*B.lo ≤ x ∧ x ≤ d*B.hi) (hy : d*C.lo ≤ y ∧ y ≤ d*C.hi)
    (hz : d*T.lo ≤ z ∧ z ≤ d*T.hi) :
    d^3*(normBounds B C T).lo ≤ BealCubicNorm.norm (x,y,z) ∧
      BealCubicNorm.norm (x,y,z) ≤ d^3*(normBounds B C T).hi := by
  have hp := product_bounds B C hd hd hx hy
  have hp' := product_bounds (product B C) T (Int.mul_nonneg hd hd) hd hp hz
  have hc1 := cube_bounds B hx
  have hc2 := cube_bounds C hy
  have hc3 := cube_bounds T hz
  let w := product (product B C) T
  change (d*d*d)*w.lo ≤ x*y*z ∧ x*y*z ≤ (d*d*d)*w.hi at hp'
  change d^3*(B.lo^3 + 2*C.lo^3 + 4*T.lo^3 - 6*w.hi) ≤
    x^3 + 2*y^3 + 4*z^3 - 6*x*y*z ∧
    x^3 + 2*y^3 + 4*z^3 - 6*x*y*z ≤ d^3*(B.hi^3 + 2*C.hi^3 + 4*T.hi^3 - 6*w.lo)
  grind

private theorem locate (x d : Int) (hd : 0 < d) (hx : 0 ≤ x ∧ x < d) :
    ∃ i : Fin 6, ∀ s : Fin 2, d*(cell i s).lo ≤ 6*(x-(s.val:Int)*d) ∧
      6*(x-(s.val:Int)*d) ≤ d*(cell i s).hi := by
  let n := 6*x/d
  have hn0 : 0 ≤ n := Int.ediv_nonneg (by omega) (by omega)
  have hn6 : n < 6 := (Int.ediv_lt_iff_lt_mul hd).mpr (by omega)
  let i : Fin 6 := ⟨n.toNat, by omega⟩
  have hi : (i.val:Int) = n := Int.toNat_of_nonneg hn0
  refine ⟨i, fun s => ?_⟩
  have l : n*d ≤ 6*x := Int.ediv_mul_le _ (by omega)
  have h : 6*x < (n+1)*d := Int.lt_ediv_add_one_mul_self _ hd
  dsimp only [cell]
  rw [hi]
  grind

/-- For any rational coefficient triple with common positive denominator d,
there is an integral triple with the absolute norm of the numerator error
strictly less than d³. -/
theorem approximate (x y z d : Int) (hd : 0 < d) :
    ∃ a b c : Int, (BealCubicNorm.norm (x-a*d, y-b*d, z-c*d)).natAbs < (d^3).natAbs := by
  have inside (t : Int) : 0 ≤ t%d ∧ t%d < d :=
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hd⟩
  obtain ⟨i, hi⟩ := locate _ _ hd (inside x)
  obtain ⟨j, hj⟩ := locate _ _ hd (inside y)
  obtain ⟨k, hk⟩ := locate _ _ hd (inside z)
  obtain ⟨s,t,u,hl,hh⟩ := finite_cover i j k
  let a := x/d + (s.val:Int)
  let b := y/d + (t.val:Int)
  let c := z/d + (u.val:Int)
  refine ⟨a,b,c,?_⟩
  have trans (v w : Int) : v%d - w*d = v - (v/d+w)*d := by
    have := Int.emod_add_ediv_mul v d
    grind
  have h := norm_bounds _ _ _ (d := d) (by omega) (hi s) (hj t) (hk u)
  rw [trans, trans, trans] at h
  let N := BealCubicNorm.norm (x-a*d, y-b*d, z-c*d)
  let bound := normBounds (cell i s) (cell j t) (cell k u)
  have hhom : BealCubicNorm.norm (6*(x-a*d), 6*(y-b*d), 6*(z-c*d)) = 216*N := by
    dsimp only [BealCubicNorm.norm,N]
    grind
  change d^3*bound.lo ≤ BealCubicNorm.norm (6*(x-a*d), 6*(y-b*d), 6*(z-c*d)) ∧
    BealCubicNorm.norm (6*(x-a*d), 6*(y-b*d), 6*(z-c*d)) ≤ d^3*bound.hi at h
  rw [hhom] at h
  have hd3 : 0 < d^3 := Int.pow_pos hd
  have l := Int.mul_le_mul_of_nonneg_left hl (show 0 ≤ d^3 by omega)
  have u := Int.mul_le_mul_of_nonneg_left hh (show 0 ≤ d^3 by omega)
  change d^3*(-208) ≤ d^3*bound.lo at l
  change d^3*bound.hi ≤ d^3*208 at u
  change N.natAbs < (d^3).natAbs
  have habs := Int.natAbs_eq_iff.mp (rfl : N.natAbs = N.natAbs)
  have hpos := Int.natAbs_of_nonneg (show 0 ≤ d^3 by omega)
  omega

end BealCubicCover

namespace BealCubicNorm

private theorem even_of_cube (a t : Int) (h : a^3 = 2*t) : a = 2*(a/2) := by
  let k := a/2
  by_cases he : a = 2*k
  · exact he
  · have ho : a = 2*k+1 := by dsimp [k] at *; omega
    have hc : a^3 = 2*(4*k^3+6*k^2+3*k)+1 := by rw [ho]; grind
    omega

/-- Successive division of the norm equation by 2 and 4 shows that all
three coordinates of a zero of the norm are even. -/
theorem even_coords_of_norm_zero (a b c : Int) (h : BealCubicNorm.norm (a,b,c) = 0) :
    a = 2*(a/2) ∧ b = 2*(b/2) ∧ c = 2*(c/2) := by
  change a^3 + 2*b^3 + 4*c^3 - 6*a*b*c = 0 at h
  have ha := even_of_cube a (3*a*b*c-b^3-2*c^3) (by grind)
  let i := a/2
  have hi : a = 2*i := ha
  rw [hi] at h
  have hb := even_of_cube b (3*i*b*c-2*i^3-c^3) (by grind)
  let j := b/2
  have hj : b = 2*j := hb
  rw [hj] at h
  exact ⟨ha, hb, even_of_cube c (3*i*j*c-i^3-2*j^3) (by grind)⟩

private theorem zero_coords (a b c : Int) (h : BealCubicNorm.norm (a,b,c) = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨ha,hb,hc⟩ := even_coords_of_norm_zero a b c h
  by_cases hz : a = 0 ∧ b = 0 ∧ c = 0
  · exact hz
  · let i := a/2
    let j := b/2
    let k := c/2
    have hi : a = 2*i := ha
    have hj : b = 2*j := hb
    have hk : c = 2*k := hc
    have habs {x y : Int} (hxy : x = 2*y) : x.natAbs = 2*y.natAbs := by
      rw [hxy, Int.natAbs_mul]
      rfl
    have hsmall : i.natAbs+j.natAbs+k.natAbs < a.natAbs+b.natAbs+c.natAbs := by
      have := habs hi
      have := habs hj
      have := habs hk
      have hpos : 0 < a.natAbs ∨ 0 < b.natAbs ∨ 0 < c.natAbs := by
        by_cases ha0 : a = 0
        · by_cases hb0 : b = 0
          · exact Or.inr (Or.inr (Int.natAbs_pos.mpr (by omega)))
          · exact Or.inr (Or.inl (Int.natAbs_pos.mpr hb0))
        · exact Or.inl (Int.natAbs_pos.mpr ha0)
      omega
    have hnorm : BealCubicNorm.norm (i,j,k) = 0 := by
      rw [hi,hj,hk] at h
      dsimp [BealCubicNorm.norm] at h ⊢
      grind
    obtain ⟨r,s,t⟩ := zero_coords i j k hnorm
    omega
termination_by a.natAbs+b.natAbs+c.natAbs

theorem norm_eq_zero_iff (x : Triple) : BealCubicNorm.norm x = 0 ↔ x = (0,0,0) := by
  obtain ⟨a,b,c⟩ := x
  constructor
  · intro h
    obtain ⟨rfl,rfl,rfl⟩ := zero_coords a b c h
    rfl
  · intro h
    rw [h]
    decide

end BealCubicNorm

namespace BealCubicDivision

open BealCubicNorm

def adj (x : Triple) : Triple :=
  (x.1^2 - 2*x.2.1*x.2.2, 2*x.2.2^2-x.1*x.2.1, x.2.1^2-x.1*x.2.2)

def sub (x y : Triple) : Triple :=
  (x.1-y.1,x.2.1-y.2.1,x.2.2-y.2.2)

def scale (k : Int) (x : Triple) : Triple :=
  (x.1*k,x.2.1*k,x.2.2*k)

theorem mul_adj (x : Triple) : mul x (adj x) = (BealCubicNorm.norm x,0,0) := by
  dsimp [mul, adj, BealCubicNorm.norm]
  grind

private theorem mul_scale (a : Int) (x y : Triple) :
    mul (scale a x) y = scale a (mul x y) := by
  dsimp [mul,scale]
  grind

private theorem mul_sub (x y z : Triple) : mul (sub x y) z = sub (mul x z) (mul y z) := by
  dsimp [mul,sub]
  grind

private theorem norm_scale (d : Int) (x : Triple) : BealCubicNorm.norm (scale d x) = d^3 * BealCubicNorm.norm x := by
  dsimp [BealCubicNorm.norm,scale]
  grind

private theorem error_mul (x y m : Triple) :
    mul (sub (mul x (adj y)) (scale (BealCubicNorm.norm y) m)) y = scale (BealCubicNorm.norm y) (sub x (mul m y)) := by
  rw [mul_sub, BealCubicNorm.mul_assoc, BealCubicNorm.mul_comm (adj y), mul_adj, mul_scale]
  dsimp [sub, scale, mul]
  grind

/-- Approximation of every rational triple by an integral triple within unit absolute norm. -/
def Covers : Prop := ∀ x y z d : Int, 0 < d → ∃ a b c : Int,
    (BealCubicNorm.norm (x-a*d, y-b*d, z-c*d)).natAbs < (d^3).natAbs

private theorem approx_signed (h : Covers) (x : Triple) (d : Int) (hd : d ≠ 0) :
    ∃ m : Triple, (BealCubicNorm.norm (sub x (scale d m))).natAbs < (d^3).natAbs := by
  by_cases hp : 0 < d
  · obtain ⟨a,b,c,hs⟩ := h x.1 x.2.1 x.2.2 d hp
    exact ⟨(a,b,c),hs⟩
  obtain ⟨a,b,c,hs⟩ := h x.1 x.2.1 x.2.2 (-d) (by omega)
  refine ⟨(-a,-b,-c), ?_⟩
  dsimp [sub,scale]
  simpa only [Int.neg_mul, Int.mul_neg, Int.natAbs_pow, Int.natAbs_neg] using hs

/-- A strict approximation in the norm yields Euclidean division for any divisor
of nonzero norm. The remainder is given by x minus the quotient times y. -/
theorem euclidean_division (h : Covers) (x y : Triple) (hy : BealCubicNorm.norm y ≠ 0) :
    ∃ m : Triple, (BealCubicNorm.norm (sub x (mul m y))).natAbs < (BealCubicNorm.norm y).natAbs := by
  obtain ⟨m, hm⟩ := approx_signed h (mul x (adj y)) (BealCubicNorm.norm y) hy
  refine ⟨m, ?_⟩
  have he := congrArg BealCubicNorm.norm (error_mul x y m)
  change BealCubicNorm.norm (mul _ y) = BealCubicNorm.norm (scale _ _) at he
  rw [BealCubicNorm.norm_mul, norm_scale] at he
  have ha := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_pow] at ha hm
  have hpos : 0 < (BealCubicNorm.norm y).natAbs := by omega
  have hbound := Nat.mul_lt_mul_of_pos_right hm hpos
  rw [ha] at hbound
  exact Nat.lt_of_mul_lt_mul_left hbound

theorem euclidean_division_nonzero (h : Covers) (x y : Triple) (hy : y ≠ (0,0,0)) :
    ∃ m : Triple, (BealCubicNorm.norm (sub x (mul m y))).natAbs < (BealCubicNorm.norm y).natAbs :=
  euclidean_division h x y (fun hzero => hy ((norm_eq_zero_iff y).mp hzero))

end BealCubicDivision

namespace BealCubicRing

/-- The integral cubic order with power basis 1, α, α² and α³ = 2. -/
structure R where
  coords : BealCubicNorm.Triple
deriving DecidableEq

theorem R.ext {x y : R} (h : x.coords = y.coords) : x = y := by cases x; cases y; cases h; rfl

instance : Zero R := ⟨⟨0,0,0⟩⟩
instance : One R := ⟨⟨BealCubicNorm.one⟩⟩
instance : Add R := ⟨fun x y => ⟨x.coords+y.coords⟩⟩
instance : Neg R := ⟨fun x => ⟨-x.coords⟩⟩
instance : Mul R := ⟨fun x y => ⟨BealCubicNorm.mul x.coords y.coords⟩⟩

theorem coords_zero : (0:R).coords = (0,0,0) := rfl
theorem coords_one : (1:R).coords = (1,0,0) := rfl
theorem coords_add (x y : R) : (x+y).coords = x.coords+y.coords := rfl
theorem coords_neg (x : R) : (-x).coords = -x.coords := rfl
theorem coords_mul (x y : R) : (x*y).coords = BealCubicNorm.mul x.coords y.coords := rfl

instance : CommRing R := CommRing.ofMinimalAxioms
  (fun x y z => R.ext <| add_assoc x.coords y.coords z.coords)
  (fun x => R.ext <| zero_add x.coords)
  (fun x => R.ext <| neg_add_cancel x.coords)
  (fun x y z => R.ext <| BealCubicNorm.mul_assoc x.coords y.coords z.coords)
  (fun x y => R.ext <| BealCubicNorm.mul_comm x.coords y.coords)
  (fun x => R.ext <| BealCubicNorm.one_mul x.coords)
  (fun x y z => by
    apply R.ext
    simp only [coords_add, coords_mul, BealCubicNorm.mul]
    ext <;> dsimp <;> ring)

instance : Nontrivial R := ⟨⟨0,1,by decide⟩⟩

theorem coords_sub (x y : R) : (x-y).coords = BealCubicDivision.sub x.coords y.coords := by
  rw [sub_eq_add_neg, coords_add, coords_neg]
  ext <;> simp [BealCubicDivision.sub,sub_eq_add_neg]

def scalar : Int →+* R where
  toFun z := ⟨(z,0,0)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by apply R.ext; simp [coords_add]
  map_mul' x y := by apply R.ext; simp [coords_mul, BealCubicNorm.mul]

theorem coords_intCast (z : Int) : (z:R).coords = (z,0,0) := by
  rw [← map_intCast scalar z]
  rfl

def alpha : R := ⟨(0,1,0)⟩

theorem alpha_cube : alpha^3 = 2 := by
  apply R.ext
  rw [show (2:R) = ((2:Int):R) by rfl, coords_intCast]
  decide

private noncomputable def normQuotient (x y : R) : R :=
  if h : y = 0 then 0 else
    ⟨Classical.choose (BealCubicDivision.euclidean_division_nonzero
      BealCubicCover.approximate x.coords y.coords (fun h' => h (R.ext h')))⟩

private theorem normQuotient_spec (x y : R) (hy : y ≠ 0) :
    (BealCubicNorm.norm (x-y*normQuotient x y).coords).natAbs <
      (BealCubicNorm.norm y.coords).natAbs := by
  rw [coords_sub, coords_mul, BealCubicNorm.mul_comm y.coords]
  unfold normQuotient
  rw [dif_neg hy]
  exact Classical.choose_spec (BealCubicDivision.euclidean_division_nonzero
    BealCubicCover.approximate x.coords y.coords (fun h => hy (R.ext h)))

noncomputable instance : EuclideanDomain R where
  quotient := normQuotient
  quotient_zero x := by simp [normQuotient]
  remainder x y := x-y*normQuotient x y
  quotient_mul_add_remainder_eq x y := by rw [add_sub_cancel]
  r x y := (BealCubicNorm.norm x.coords).natAbs < (BealCubicNorm.norm y.coords).natAbs
  r_wellFounded := (measure (fun x : R => (BealCubicNorm.norm x.coords).natAbs)).wf
  remainder_lt x _ hy := normQuotient_spec _ _ hy
  mul_left_not_lt x y hy := by
    change ¬ (BealCubicNorm.norm (x*y).coords).natAbs < (BealCubicNorm.norm x.coords).natAbs
    rw [coords_mul, BealCubicNorm.norm_mul, Int.natAbs_mul]
    have hn : BealCubicNorm.norm y.coords ≠ 0 :=
      fun h => hy (R.ext ((BealCubicNorm.norm_eq_zero_iff _).mp h))
    have hp : 0 < (BealCubicNorm.norm y.coords).natAbs := by omega
    have h := Nat.mul_le_mul_left (BealCubicNorm.norm x.coords).natAbs
      (show 1 ≤ (BealCubicNorm.norm y.coords).natAbs by omega)
    omega

section

variable {A : Type*} [CommRing A]

/-- Evaluation in any commutative ring at a root of X³−2. -/
def evalHom (β : A) (hβ : β^3=2) : R →+* A where
  toFun x := (x.coords.1 : A) + β*x.coords.2.1 + β^2*x.coords.2.2
  map_zero' := by simp [coords_zero]
  map_one' := by simp [coords_one]
  map_add' x y := by
    simp only [coords_add, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  map_mul' x y := by
    simp only [coords_mul, BealCubicNorm.mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    have hc : β^4=2*β := by rw [pow_succ, hβ]
    ring_nf
    simp only [hβ,hc]
    ring

@[simp] theorem evalHom_alpha (β : A) (hβ : β^3=2) : evalHom β hβ alpha = β := by
  simp [evalHom, alpha]

end

end BealCubicRing

namespace BealCubicUnits
open BealCubicNorm

/-- An integer approximation to the coordinates of the real embedding,
with weights close to 10000 times 1, ∛2 and ∛4. -/
def height (x : Triple) : Int :=
  max |10000*x.1| (max |12599*x.2.1| |15874*x.2.2|)

private theorem forward_contract (a b c M : Int)
    (ha : |10000*a| ≤ M) (hb : |12599*b| ≤ M) (hc : |15874*c| ≤ M)
    (hab : 2*|10000*a-12599*b| < M) (hbc : 2*|12599*b-15874*c| < M)
    (hca : 2*|15874*c-10000*a| < M) :
    height (mul (a,b,c) eps) < M := by
  rw [abs_le] at ha hb hc
  have h₁ := le_abs_self (10000*a-12599*b)
  have h₂ := neg_le_abs (10000*a-12599*b)
  have h₃ := le_abs_self (12599*b-15874*c)
  have h₄ := neg_le_abs (12599*b-15874*c)
  have h₅ := le_abs_self (15874*c-10000*a)
  have h₆ := neg_le_abs (15874*c-10000*a)
  simp only [height, mul, eps, mul_neg_one, mul_one, mul_zero, zero_mul, add_zero,
    zero_add, max_lt_iff, abs_lt]
  constructor
  · constructor <;> linarith
  · constructor <;> constructor <;> linarith

private theorem inverse_contract (a b c M : Int)
    (ha : |10000*a| ≤ M) (hb : |12599*b| ≤ M) (hc : |15874*c| ≤ M)
    (h : 25*|10000*a+12599*b+15874*c| < M) :
    height (mul (a,b,c) epsInv) < M := by
  rw [abs_le] at ha hb hc
  have h₁ := le_abs_self (10000*a+12599*b+15874*c)
  have h₂ := neg_le_abs (10000*a+12599*b+15874*c)
  simp only [height, mul, epsInv, mul_one, max_lt_iff, abs_lt]
  constructor
  · constructor <;> linarith
  · constructor <;> constructor <;> linarith

/-- The quadratic factor in the identity for a sum of three cubes equals
half the sum of the three squared pairwise differences. -/
private theorem twice_square_bound {u v w M : Int}
    (hu : 0 ≤ M) (h : M ≤ 2*|u-v| ∨ M ≤ 2*|v-w| ∨ M ≤ 2*|w-u|) :
    M^2 ≤ 8*(u^2+v^2+w^2-u*v-v*w-w*u) := by
  obtain h | h | h := h
  · have h' := pow_le_pow_left₀ hu h 2
    rw [mul_pow, sq_abs] at h'
    nlinarith [sq_nonneg (v-w),sq_nonneg (w-u)]
  · have h' := pow_le_pow_left₀ hu h 2
    rw [mul_pow, sq_abs] at h'
    nlinarith [sq_nonneg (u-v),sq_nonneg (w-u)]
  · have h' := pow_le_pow_left₀ hu h 2
    rw [mul_pow, sq_abs] at h'
    nlinarith [sq_nonneg (u-v),sq_nonneg (v-w)]

set_option maxHeartbeats 1000000 in
private theorem error_bound (a b c S : Int) (ha : |a| ≤ S) (hb : |b| ≤ S) (hc : |c| ≤ S) :
    |-(100242201*b^3) - 7952376*c^3 + 104220000*a*b*c| ≤ 212414577*S^3 := by
  have hS := (abs_nonneg a).trans ha
  have hB := pow_le_pow_left₀ (abs_nonneg b) hb 3
  have hC := pow_le_pow_left₀ (abs_nonneg c) hc 3
  have hABC := mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hS) hc (abs_nonneg _) (mul_nonneg hS hS)
  calc
    _ ≤ |-(100242201*b^3) - 7952376*c^3| + |104220000*a*b*c| := abs_add_le _ _
    _ ≤ (|-(100242201*b^3)| + |7952376*c^3|) + |104220000*a*b*c| :=
      add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ _ := by
      simp only [abs_mul,abs_neg,abs_pow] 
      norm_num
      linarith

/-- If neither elementary unit shortens the triple, the linear form L and
the quadratic form Q give lower bounds for its height and squared height.
Their product approximates 10¹² times the integral norm. -/
private theorem minimal_small (a b c : Int) (hn : |BealCubicNorm.norm (a,b,c)| = 1)
    (hf : height (a,b,c) ≤ height (mul (a,b,c) eps))
    (hi : height (a,b,c) ≤ height (mul (a,b,c) epsInv)) :
    max |a| (max |b| |c|) ≤ 5 := by
  let S := max |a| (max |b| |c|)
  let M := height (a,b,c)
  let u := 10000*a
  let v := 12599*b
  let w := 15874*c
  let L := u+v+w
  let Q := u^2+v^2+w^2-u*v-v*w-w*u
  have ha : |a| ≤ S := le_max_left _ _
  have hb : |b| ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hc : |c| ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  have hu : |u| ≤ M := le_max_left _ _
  have hv : |v| ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hw : |w| ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hM : 0 ≤ M := (abs_nonneg _).trans hu
  have hS : 0 ≤ S := (abs_nonneg _).trans ha
  have hSM : 10000*S ≤ M := by
    dsimp [u,v,w] at hu hv hw
    simp only [abs_mul, abs_of_nonneg (by decide : (0:Int) ≤ 10000),
      abs_of_nonneg (by decide : (0:Int) ≤ 12599), abs_of_nonneg (by decide : (0:Int) ≤ 15874)] at hu hv hw
    dsimp [S]
    rcases le_total |a| (max |b| |c|) with ha' | ha'
    · rw [max_eq_right ha']
      rcases le_total |b| |c| with h | h
      · rw [max_eq_right h]
        linarith [abs_nonneg c]
      · rw [max_eq_left h]
        linarith [abs_nonneg b]
    · rwa [max_eq_left ha']
  have hL : M ≤ 25*|L| := by
    by_contra! h
    exact (not_lt_of_ge hi) (inverse_contract a b c M hu hv hw h)
  have hD : M ≤ 2*|u-v| ∨ M ≤ 2*|v-w| ∨ M ≤ 2*|w-u| := by
    by_contra! h
    exact (not_lt_of_ge hf) (forward_contract a b c M hu hv hw h.1 h.2.1 h.2.2)
  have hQ : M^2 ≤ 8*Q := twice_square_bound hM hD
  have hQn : 0 ≤ Q := by linarith [sq_nonneg M]
  have hbig := mul_le_mul hL hQ (sq_nonneg M) (mul_nonneg (by decide : (0:Int) ≤ 25) (abs_nonneg L))
  have hprod : L*Q = 1000000000000*BealCubicNorm.norm (a,b,c) +
      (-(100242201*b^3) - 7952376*c^3 + 104220000*a*b*c) := by
    dsimp [L,Q,u,v,w,BealCubicNorm.norm]
    ring
  have hbound : |L| * Q ≤ 1000000000000+212414577*S^3 := by
    calc
      _ = |L*Q| := by rw [abs_mul, abs_of_nonneg hQn]
      _ ≤ _ := by
        rw [hprod]
        apply (abs_add_le _ _).trans
        apply add_le_add _ (error_bound a b c S ha hb hc)
        rw [abs_mul, hn]
        decide
  have hm3 := pow_le_pow_left₀ (mul_nonneg (by decide : (0:Int) ≤ 10000) hS) hSM 3
  change S ≤ 5
  by_contra! h
  have hs6 : (6:Int) ≤ S := by omega
  have hs3 := pow_le_pow_left₀ (by decide : (0:Int) ≤ 6) hs6 3
  nlinarith only [hm3, hbig, hbound, hs3]

private theorem coordinate_enumeration : ∀ i j k : Fin 11,
    let x : Triple := ((i.val:Int)-5,(j.val:Int)-5,(k.val:Int)-5)
    |BealCubicNorm.norm x| = 1 → height x ≤ height (mul x eps) → height x ≤ height (mul x epsInv) →
    x = one ∨ x = (-1,0,0) := by decide +kernel

theorem minimal_unit {x : Triple} (hn : |BealCubicNorm.norm x| = 1)
    (hf : height x ≤ height (mul x eps)) (hi : height x ≤ height (mul x epsInv)) :
    x = one ∨ x = (-1,0,0) := by
  obtain ⟨a,b,c⟩ := x
  have h := minimal_small a b c hn hf hi
  simp only [max_le_iff, abs_le] at h
  let i : Fin 11 := ⟨(a+5).toNat, by omega⟩
  let j : Fin 11 := ⟨(b+5).toNat, by omega⟩
  let k : Fin 11 := ⟨(c+5).toNat, by omega⟩
  have hA : (i.val:Int)-5=a := by dsimp [i]; omega
  have hB : (j.val:Int)-5=b := by dsimp [j]; omega
  have hC : (k.val:Int)-5=c := by dsimp [k]; omega
  have t := coordinate_enumeration i j k
  dsimp only at t
  rw [hA,hB,hC] at t
  exact t hn hf hi

def negOne : Triple := (-1,0,0)

/-- Integer powers of the unit ε = ∛2−1. -/
def zpowEps : Int → Triple
  | .ofNat n => pow eps n
  | .negSucc n => pow epsInv (n+1)

theorem zpow_succ (j : Int) : zpowEps (j+1) = mul (zpowEps j) eps := by
  cases j with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero => decide
    | succ n =>
      change pow epsInv (n+1) = mul (mul (pow epsInv (n+1)) epsInv) eps
      rw [BealCubicNorm.mul_assoc, inv_mul_eps, BealCubicNorm.mul_one]

theorem zpow_pred (j : Int) : zpowEps (j-1) = mul (zpowEps j) epsInv := by
  have h := zpow_succ (j-1)
  rw [show j-1+1=j by omega] at h
  rw [h, BealCubicNorm.mul_assoc, eps_mul_inv, BealCubicNorm.mul_one]

theorem zpow_add (j k : Int) : zpowEps (j+k) = mul (zpowEps j) (zpowEps k) := by
  cases k with
  | ofNat n =>
    induction n with
    | zero => change zpowEps (j+0) = mul (zpowEps j) one; rw [Int.add_zero, BealCubicNorm.mul_one]
    | succ n ih =>
      change zpowEps (j+((n:Int)+1)) = mul (zpowEps j) (mul (zpowEps (n:Int)) eps)
      change zpowEps (j+(n:Int)) = mul (zpowEps j) (zpowEps (n:Int)) at ih
      rw [← Int.add_assoc, zpow_succ, ih, BealCubicNorm.mul_assoc]
  | negSucc n =>
    induction n with
    | zero => change zpowEps (j-1) = mul (zpowEps j) epsInv; exact zpow_pred j
    | succ n ih =>
      have h : j + Int.negSucc (n+1) = (j + Int.negSucc n)-1 := by omega
      change zpowEps (j+Int.negSucc (n+1)) = mul (zpowEps j) (mul (zpowEps (Int.negSucc n)) epsInv)
      rw [h, zpow_pred, ih, BealCubicNorm.mul_assoc]

theorem zpow_mul_nat (j : Int) (n : Nat) : zpowEps ((n:Int)*j) = pow (zpowEps j) n := by
  induction n with
  | zero => change zpowEps (0*j) = one; rw [Int.zero_mul]; rfl
  | succ n ih =>
    change zpowEps (((n:Int)+1)*j) = mul (pow (zpowEps j) n) (zpowEps j)
    rw [Int.add_mul, Int.one_mul, zpow_add, ih]

theorem pow_product (x y : Triple) (n : Nat) :
    pow (mul x y) n = mul (pow x n) (pow y n) := by
  induction n with
  | zero => exact (BealCubicNorm.mul_one one).symm
  | succ n ih =>
    simp only [pow,ih]
    calc
      mul (mul (pow x n) (pow y n)) (mul x y)
          = mul (pow x n) (mul x (mul (pow y n) y)) := by
              rw [BealCubicNorm.mul_assoc, ← BealCubicNorm.mul_assoc (pow y n) x, BealCubicNorm.mul_comm (pow y n) x, BealCubicNorm.mul_assoc]
      _ = _ := (BealCubicNorm.mul_assoc _ _ _).symm

/-- Every integral triple of norm ±1 is a sign times an integer power of ε. -/
theorem units_generated (x : Triple) (hn : |BealCubicNorm.norm x| = 1) :
    ∃ s : Triple, (s = one ∨ s = negOne) ∧ ∃ j : Int, x = mul s (zpowEps j) := by
  generalize he : (height x).toNat = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have hpos (t : Triple) : 0 ≤ height t := (abs_nonneg _).trans (le_max_left _ _)
    by_cases hf : height (mul x eps) < height x
    · have hn' : |BealCubicNorm.norm (mul x eps)| = 1 := by rw [BealCubicNorm.norm_mul,eps_norm,Int.mul_one]; exact hn
      have hlt : (height (mul x eps)).toNat < n := by have := hpos (mul x eps); omega
      obtain ⟨s,hs,j,hj⟩ := ih _ hlt _ hn' rfl
      refine ⟨s,hs,j-1,?_⟩
      rw [zpow_pred, ← BealCubicNorm.mul_assoc, ← hj, BealCubicNorm.mul_assoc, eps_mul_inv, BealCubicNorm.mul_one]
    · by_cases hi : height (mul x epsInv) < height x
      · have hn' : |BealCubicNorm.norm (mul x epsInv)| = 1 := by rw [BealCubicNorm.norm_mul,epsInv_norm,Int.mul_one]; exact hn
        have hlt : (height (mul x epsInv)).toNat < n := by have := hpos (mul x epsInv); omega
        obtain ⟨s,hs,j,hj⟩ := ih _ hlt _ hn' rfl
        refine ⟨s,hs,j+1,?_⟩
        rw [zpow_succ, ← BealCubicNorm.mul_assoc, ← hj, BealCubicNorm.mul_assoc, inv_mul_eps, BealCubicNorm.mul_one]
      · obtain hp | hp := minimal_unit hn (le_of_not_gt hf) (le_of_not_gt hi)
        · exact ⟨one, Or.inl rfl, 0, hp.trans (BealCubicNorm.mul_one one).symm⟩
        · exact ⟨negOne, Or.inr rfl, 0, hp.trans (BealCubicNorm.mul_one negOne).symm⟩


end BealCubicUnits

namespace BealCubicRing

theorem coords_pow (x : R) (n : Nat) :
    (x^n).coords = BealCubicNorm.pow x.coords n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, coords_mul, ih]; rfl

theorem abs_norm_unit (u : Rˣ) : |BealCubicNorm.norm (u:R).coords| = 1 := by
  have h : BealCubicNorm.norm (u:R).coords * BealCubicNorm.norm (↑u⁻¹:R).coords = 1 := by
    rw [← BealCubicNorm.norm_mul, ← coords_mul, u.mul_inv]
    rfl
  have hh := congrArg Int.natAbs h
  rw [Int.natAbs_mul] at hh
  have hone : (BealCubicNorm.norm (u:R).coords).natAbs = 1 := Nat.eq_one_of_mul_eq_one_right hh
  rw [← Int.natCast_natAbs, hone]
  rfl


end BealCubicRing

namespace BealSeventhBridge43

open BealCubicRing

def allowed43 (i j : Nat) : Bool :=
  match i with
  | 0 => j == 1 || j == 4
  | 1 | 2 | 4 => j == 2 || j == 4
  | 3 | 5 | 6 => j == 5
  | _ => false

/-- A nonzero seventh power in the field of order 43 has sixth power one. -/
private theorem fermat43 (s : ZMod 43) : s = 0 ∨ s ^ 42 = 1 := by
  have h : ∀ t : Fin 43, (t : ZMod 43) = 0 ∨ (t : ZMod 43)^42 = 1 := by decide
  exact h s

private def passes (i q : Nat) (a r : ZMod 43) : Bool :=
  let value := -a + r^2 * 2^q
  value == 0 || value^6 == ((r-1)^i)^6

private theorem eval_at_root {a q : Nat} (i : Fin 7) (x : R)
    (he : (R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val)*x^7).coords = (-(a:Int),0,2^q))
    (r : ZMod 43) (hr : r^3 = 2) : passes i.val q (a:ZMod 43) r = true := by
  let E := evalHom r hr
  have hep : E (R.mk BealCubicNorm.eps) = r - 1 := by
    change ((-1:Int):ZMod 43) + r * ((1:Int):ZMod 43) + r^2 * ((0:Int):ZMod 43) = r-1
    simp
    ring
  have hunit : R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val) = (R.mk BealCubicNorm.eps)^i.val := by
    apply R.ext
    rw [coords_pow]
  have heval := congrArg E (R.ext he)
  rw [map_mul, hunit, map_pow, hep, map_pow] at heval
  dsimp [E, evalHom] at heval
  push_cast at heval
  simp only [mul_zero, add_zero] at heval
  unfold passes
  rcases fermat43 ((x.coords.1 : ZMod 43) + r*x.coords.2.1 + r^2*x.coords.2.2) with hz | hz
  · rw [hz, zero_pow (by decide : 7 ≠ 0), mul_zero] at heval
    simp [← heval]
  · have h6 := congrArg (· ^ 6) heval
    simp only [mul_pow, ← pow_mul, show 7*6 = 42 by decide, hz, mul_one] at h6
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact Or.inr (h6.symm.trans (pow_mul (r-1) i.val 6))

private theorem period43 (q : Nat) : (2:ZMod 43)^q = 2^(q%14) := by
  have h : (2:ZMod 43)^14 = 1 := by decide
  calc
    _ = (2:ZMod 43)^(q%14+14*(q/14)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add, pow_mul, h, one_pow, mul_one]

private theorem passes_period (i q : Nat) (a r : ZMod 43) :
    passes i q a r = passes i (q%14) a r := by
  unfold passes
  rw [period43 q]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 6000 in
private theorem checked : ∀ (i : Fin 7) (t : Fin 14) (a : Fin 43),
    passes i.val t.val a 20 = true → passes i.val t.val a 32 = true →
    passes i.val t.val a 34 = true → allowed43 i.val (t.val % 7) = true := by decide

theorem allowed_of_rep {a q : Nat} (i : Fin 7) (x : R)
    (he : (R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val)*x^7).coords = (-(a:Int),0,2^q)) :
    allowed43 i.val (q%7) = true := by
  let t : Fin 14 := ⟨q%14, by omega⟩
  have h (r : ZMod 43) (hr : r^3 = 2) : passes i.val t.val a r = true := by
    exact (passes_period i.val q a r).symm.trans (eval_at_root i x he r hr)
  have hc := checked i t (a:ZMod 43) (h 20 (by decide)) (h 32 (by decide)) (h 34 (by decide))
  have ht : t.val % 7 = q%7 := by dsimp [t]; omega
  rwa [ht] at hc

end BealSeventhBridge43

namespace BealUniformDescent

open BealCubicRing

/-- A power of two whose exponent is nonzero modulo three cannot coincide
with a cubic residue modulo nine. -/
theorem two_pow_not_cube_mod_nine {k : Nat} (hk : k%3 ≠ 0) (a : Nat) :
    2^k % 9 ≠ a^3 % 9 := by
  have periods (q : Nat) : 2^(3*q) % 9 = 1 ∨ 2^(3*q) % 9 = 8 := by
    induction q with
    | zero => decide
    | succ q ih =>
      rw [show 3*(q+1) = 3*q+3 by omega, Nat.pow_add, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> decide
  have cubes : ∀ i : Fin 9, i.val^3 % 9 = 0 ∨ i.val^3 % 9 = 1 ∨ i.val^3 % 9 = 8 := by decide
  have h := cubes ⟨a%9, Nat.mod_lt _ (by decide)⟩
  change (a%9)^3%9=0 ∨ (a%9)^3%9=1 ∨ (a%9)^3%9=8 at h
  simp only [← Nat.pow_mod] at h
  have hf : 2^k % 9 = (2^(3*(k/3)) % 9 * (2^(k%3) % 9)) % 9 := by
    calc
      _ = 2^(3*(k/3)+k%3) % 9 := by rw [show 3*(k/3)+k%3=k by omega]
      _ = _ := by rw [Nat.pow_add, Nat.mul_mod]
  obtain h1 | h2 := (show k%3=1 ∨ k%3=2 by omega)
  · rw [h1] at hf
    rcases periods (k/3) with hp | hp <;> rw [hp] at hf <;> omega
  · rw [h2] at hf
    rcases periods (k/3) with hp | hp <;> rw [hp] at hf <;> omega

theorem three_not_dvd_base {a b n k : Nat} (hn : 2 ≤ n) (hk : k%3 ≠ 0)
    (he : a^3 + b^n = 2^k) : ¬3 ∣ b := by
  intro hb
  have h9 : 9 ∣ b^2 := by
    obtain ⟨j, hj⟩ := hb
    exact ⟨j^2, by rw [hj, Nat.mul_pow]⟩
  have hf := Nat.mod_eq_zero_of_dvd (h9.trans (Nat.pow_dvd_pow b hn))
  have h := congrArg (· % 9) he
  change (a^3+b^n)%9=2^k%9 at h
  rw [Nat.add_mod,hf,Nat.add_zero,Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))] at h
  exact two_pow_not_cube_mod_nine hk a h.symm

/-- Generic factor extraction in a Bézout domain for every exponent.
The ring element τ may be any chosen cube root of the right-hand side. -/
theorem associated_power_of_cube_root {A : Type*} [CommRing A] [IsDomain A] [IsBezout A]
    {a b n k : Nat} (hc : a.Coprime b) (hb3 : ¬3 ∣ b) (he : a^3+b^n=2^k)
    {τ : A} (hτ : τ^3=(2:A)^k) :
    ∃ w : A, Associated (w^n) (τ-(a:A)) := by
  let f := τ-(a:A)
  let g := 3*(a:A)^2+f*(f+3*a)
  have ht : b.Coprime 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb3).symm
  have hi : b.Coprime (3*a^2) := ht.mul_right (hc.symm.pow_right 2)
  have hmap := hi.isCoprime.map (Int.castRingHom A)
  have hcop : IsCoprime (b:A) (3*(a:A)^2) := by simpa using hmap
  have hcast := congrArg (fun q : Nat => (q:A)) he
  push_cast at hcast
  have hcalc : f*g=(b:A)^n := by
    calc
      f*g = (f+a)^3 - (a:A)^3 := by dsimp [g]; ring
      _ = τ^3 - (a:A)^3 := by rw [show f+(a:A)=τ by dsimp [f]; ring]
      _ = (b:A)^n := by rw [hτ, ← hcast]; ring
  have hcn : IsCoprime ((b:A)^n) (3*(a:A)^2) := hcop.pow_left
  have hd : f ∣ (b:A)^n := ⟨g,hcalc.symm⟩
  have hf : IsCoprime f g := (hcn.of_isCoprime_of_dvd_left hd).add_mul_left_right _
  exact exists_associated_pow_of_mul_eq_pow' hf hcalc

open BealCubicNorm BealCubicUnits

/-- For every odd exponent there are at most n unit classes modulo n-th powers.
The representatives are the first n powers of ε = ∛2−1. -/
theorem units_mod_odd (x : Triple) {n : Nat} (hn : Odd n) (hu : |BealCubicNorm.norm x|=1) :
    ∃ i : Fin n, ∃ y : Triple, x = mul (pow eps i.val) (pow y n) := by
  obtain ⟨s,hs,j,hj⟩ := units_generated x hu
  have hn0 : 0 < n := hn.pos
  have hd : 0 < (n:Int) := by omega
  have hm : 0 ≤ j % (n:Int) := Int.emod_nonneg j (by omega)
  have hm' : j % (n:Int) < (n:Int) := Int.emod_lt_of_pos _ hd
  let i : Fin n := ⟨(j % (n:Int)).toNat, by omega⟩
  have hri : (i.val:Int) = j % (n:Int) := by dsimp [i]; omega
  have hsign : pow s n = s := by
    rcases hs with rfl | rfl
    · exact (coords_pow (1:R) n).symm.trans (congrArg R.coords (one_pow n))
    · exact (coords_pow (-1:R) n).symm.trans (congrArg R.coords hn.neg_one_pow)
  refine ⟨i,mul s (zpowEps (j/(n:Int))), ?_⟩
  change x = mul (zpowEps (i.val:Int)) (pow (mul s (zpowEps (j/(n:Int)))) n)
  rw [pow_product,hsign,hri,← zpow_mul_nat,hj]
  have he : j = j % (n:Int) + (n:Int)*(j/(n:Int)) := (Int.emod_add_mul_ediv _ _).symm
  calc
    mul s (zpowEps j) = mul s (mul (zpowEps (j%(n:Int))) (zpowEps ((n:Int)*(j/(n:Int))))) :=
      congrArg (mul s) ((congrArg zpowEps he).trans (zpow_add _ _))
    _ = _ := by rw [← BealCubicNorm.mul_assoc, BealCubicNorm.mul_comm s, BealCubicNorm.mul_assoc]

/-- Complete integral descent in both nonzero classes of k modulo three, for
every odd n ≥ 3, including composite n. The prime exponent special case used
in the Beal reduction is immediate. -/
theorem odd_power_descent {a b n k : Nat} (hn : Odd n) (hn2 : 2 ≤ n)
    (hk : k%3 ≠ 0) (hc : a.Coprime b) (he : a^3+b^n=2^k) :
    ∃ i : Fin n, ∃ y : R, alpha^k-(a:R) = R.mk (pow eps i.val) * y^n := by
  have hτ : (alpha^k)^3 = (2:R)^k := by
    rw [← pow_mul, Nat.mul_comm k 3, pow_mul, alpha_cube]
  obtain ⟨w,u,hwu⟩ := associated_power_of_cube_root hc (three_not_dvd_base hn2 hk he) he hτ
  obtain ⟨i,y,hy⟩ := units_mod_odd (u:R).coords hn (abs_norm_unit u)
  have hu : (u:R) = R.mk (pow eps i.val) * (R.mk y)^n := by
    apply R.ext
    rw [coords_mul,coords_pow]
    exact hy
  refine ⟨i,w*(R.mk y), ?_⟩
  rw [← hwu, hu, mul_pow]
  ac_rfl

/-- The sparse linear or quadratic coefficient form used by local sieves. -/
theorem residue_class_descent {a b n q r : Nat} (hn : Odd n) (hn2 : 2 ≤ n)
    (hr : r=1 ∨ r=2) (hc : a.Coprime b) (he : a^3+b^n=2^(3*q+r)) :
    ∃ i : Fin n, ∃ y : R, (2:R)^q * alpha^r-(a:R) = R.mk (pow eps i.val) * y^n := by
  obtain ⟨i,y,hy⟩ := odd_power_descent hn hn2 (by omega) hc he
  rw [pow_add, pow_mul, alpha_cube] at hy
  exact ⟨i,y,hy⟩

end BealUniformDescent

namespace BealSeventhBridge

open BealCubicRing

private def residue7 (a : Int) : Fin 7 := ⟨(a%7).toNat, by omega⟩

private theorem residue7_cast (a : Int) : ((residue7 a).val : Int) = a%7 := by
  dsimp [residue7]
  omega

/-- The binomial coefficients make seventh powers modulo 49 constant
on coefficient classes modulo seven, over any commutative ring. -/
theorem seventh_lift {A : Type*} [CommRing A] (r z : A) :
    ∃ h : A, (r+7*z)^7 = r^7 + 49*h := by
  refine ⟨r^6*z + 21*r^5*z^2 + 245*r^4*z^3 + 1715*r^3*z^4 +
    7203*r^2*z^5 + 16807*r*z^6 + 16807*z^7, ?_⟩
  ring

private theorem reduce_coords (x : R) :
    ∃ a b c : Fin 7, ∃ z : R, x = R.mk ((a.val:Int),(b.val:Int),(c.val:Int)) + 7*z := by
  obtain ⟨a,b,c⟩ := x
  refine ⟨residue7 a,residue7 b,residue7 c, R.mk (a/7,b/7,c/7),?_⟩
  apply R.ext
  rw [coords_add,coords_mul,show (7:R) = ((7:Int):R) by rfl,coords_intCast]
  simp only [residue7_cast,BealCubicNorm.mul]
  apply Prod.ext
  · change a = a%7 + (7*(a/7) + 2*(0*(c/7)+0*(b/7)))
    omega
  · apply Prod.ext
    · change b = b%7 + (7*(b/7)+0*(a/7)+2*0*(c/7))
      omega
    · change c = c%7 + (7*(c/7)+0*(b/7)+0*(a/7))
      omega

/-- The linear and quadratic coefficients modulo 49 of a unit times a
seventh power are tested by 343 coefficient representatives. -/
theorem reduce_seventh49 (i : Fin 7) (x : R) :
    ∃ a b c : Fin 7,
      let small : R := R.mk ((a.val:Int),(b.val:Int),(c.val:Int))
      let u := R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val)
      (u*x^7).coords.2.1 % 49 = (u*small^7).coords.2.1 % 49 ∧
      (u*x^7).coords.2.2 % 49 = (u*small^7).coords.2.2 % 49 := by
  obtain ⟨a,b,c,z,hx⟩ := reduce_coords x
  let r := R.mk ((a.val:Int),(b.val:Int),(c.val:Int))
  let u := R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val)
  refine ⟨a,b,c,?_⟩
  change (u*x^7).coords.2.1 % 49 = (u*r^7).coords.2.1 % 49 ∧
      (u*x^7).coords.2.2 % 49 = (u*r^7).coords.2.2 % 49
  change x = r+7*z at hx
  obtain ⟨h,hh⟩ := seventh_lift r z
  have he : u*x^7 = u*r^7 + 49*(u*h) := by rw [hx,hh]; ring
  rw [he,coords_add,coords_mul (49:R),show (49:R) = ((49:Int):R) by rfl,coords_intCast]
  simp [BealCubicNorm.mul, Int.add_mul_emod_self_left]

/-- The exact common unit and integral seventh power, in the coordinate basis
used by both local tests of the k=3q+2 branch. -/
theorem seventh_representation {a b q : Nat} (hc : a.Coprime b)
    (he : a^3+b^7=2^(3*q+2)) :
    ∃ i : Fin 7, ∃ y : R,
      (R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val) * y^7).coords =
        (-(a:Int),0,2^q) := by
  obtain ⟨i,y,hy⟩ := BealUniformDescent.residue_class_descent
    (n:=7) (r:=2) (by decide) (by decide) (Or.inr rfl) hc he
  refine ⟨i,y,?_⟩
  rw [← hy,coords_sub,coords_mul]
  have hq : (2:R)^q = (((2:Int)^q : Int):R) := by push_cast; rfl
  have ha : (a:R) = ((a:Int):R) := by simp
  rw [hq,coords_intCast,ha,coords_intCast,show (alpha^2).coords = (0,0,1) by decide]
  simp [BealCubicDivision.sub,BealCubicNorm.mul]

/-- Necessary finite-ring witness for the *same* i as the integral
representation. The finite-table arithmetic here uses ordinary integer
triples and the multiplication modulo α³=2. -/
theorem fits49_of_rep {i : Fin 7} {x : R} {a b c : Int}
    (he : (R.mk (BealCubicNorm.pow BealCubicNorm.eps i.val)*x^7).coords = (a,b,c)) :
    ∃ u v w : Fin 7,
      let z := BealCubicNorm.mul (BealCubicNorm.pow BealCubicNorm.eps i.val)
        (BealCubicNorm.pow ((u.val:Int),(v.val:Int),(w.val:Int)) 7)
      z.2.1 % 49 = b % 49 ∧ z.2.2 % 49 = c % 49 := by
  obtain ⟨u,v,w,h⟩ := reduce_seventh49 i x
  dsimp only at h
  rw [he] at h
  rw [coords_mul,coords_pow] at h
  exact ⟨u,v,w,h.1.symm,h.2.symm⟩

end BealSeventhBridge

namespace BealSeventhTable49

open BealCubicNorm

def coeff (i a b c : Fin 7) : Triple :=
  mul (pow eps i.val) (pow ((a.val:Int),(b.val:Int),(c.val:Int)) 7)

/-- Required class of q modulo seven for each unit at the prime above seven. -/
def allowed (i j : Nat) : Bool :=
  match i with
  | 0 => j == 4
  | 1 => j == 1 || j == 4
  | 2 => j == 3
  | 3 => j == 6
  | 5 => j == 6
  | _ => false

/-- Discrete logarithm modulo seven on the subgroup generated by 2 modulo 49.
The sentinel 7 denotes residues outside that subgroup. -/
def logClass : Nat → Nat
  | 1 | 30 | 18 => 0
  | 2 | 11 | 36 => 1
  | 4 | 22 | 23 => 2
  | 8 | 44 | 46 => 3
  | 16 | 39 | 43 => 4
  | 32 | 29 | 37 => 5
  | 15 | 9 | 25 => 6
  | _ => 7

private def passes (i a b c : Fin 7) : Bool :=
  let x := coeff i a b c
  let j := logClass (x.2.2 % 49).toNat
  x.2.1 % 49 != 0 || j == 7 || allowed i.val j

set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i a b c : Fin 7, passes i a b c = true := by decide

private theorem two_period (q : Nat) : (2:Int)^q % 49 = (2:Int)^(q%21) % 49 := by
  have hp : (2:Int)^21 % 49 = 1 % 49 := by decide
  have hpow (k : Nat) : ((2:Int)^21)^k % 49 = 1 % 49 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Int.pow_succ, Int.mul_emod, ih, hp, ← Int.mul_emod, Int.mul_one]
  calc
    _ = (2:Int)^(q%21+21*(q/21)) % 49 := by rw [Nat.mod_add_div]
    _ = _ := by
      rw [Int.pow_add, Int.pow_mul, Int.mul_emod, hpow, ← Int.mul_emod, Int.mul_one]

theorem allowed_of_representative (i a b c : Fin 7) (q : Nat)
    (hb : (coeff i a b c).2.1 % 49 = 0)
    (hc : (coeff i a b c).2.2 % 49 = (2:Int)^q % 49) :
    allowed i.val (q%7) = true := by
  let j : Fin 21 := ⟨q%21, by omega⟩
  have decode : ∀ n : Fin 21, logClass ((2:Int)^n.val % 49).toNat = n.val % 7 := by decide
  have hq : logClass ((2:Int)^q % 49).toNat = q%7 := by
    rw [two_period q, decode j]
    dsimp [j]
    omega
  have hp := checked i a b c
  simp [passes,hb,hc,hq,show q%7 ≠ 7 by omega] at hp
  exact hp

end BealSeventhTable49

namespace BealSeventhFamily

private theorem intersection (i j : Fin 7)
    (m49 : BealSeventhTable49.allowed i.val j.val = true)
    (m43 : BealSeventhBridge43.allowed43 i.val j.val = true) : j.val = 4 := by
  have check : ∀ i j : Fin 7, BealSeventhTable49.allowed i.val j.val = true →
      BealSeventhBridge43.allowed43 i.val j.val = true → j.val = 4 := by decide
  exact check i j m49 m43

/-- Every coprime solution in the quadratic coefficient branch obeys this
congruence, for every size of the bases and exponent. -/
theorem seventh_sieve {a b q : Nat} (hc : a.Coprime b) (he : a^3+b^7=2^(3*q+2)) : q%7=4 := by
  obtain ⟨i,x,hr⟩ := BealSeventhBridge.seventh_representation hc he
  obtain ⟨u,v,w,h49b,h49c⟩ := BealSeventhBridge.fits49_of_rep hr
  have h49 := BealSeventhTable49.allowed_of_representative i u v w q h49b h49c
  exact intersection i ⟨q%7,by omega⟩ h49 (BealSeventhBridge43.allowed_of_rep i x hr)


end BealSeventhFamily

theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H3_R1.H4 := by
  exact BealSeventhFamily.seventh_sieve
