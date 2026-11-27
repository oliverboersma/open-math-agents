import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Ring.Parity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card.Arithmetic

/- OrbitUp -/
section

namespace OrbitUp

open scoped BigOperators Matrix

abbrev K := ZMod 2
abbrev V (d : ℕ) := Fin d → K
abbrev Q (d s : ℕ) := QuadraticMap K (V d) (V s)
abbrev L (d : ℕ) := V d ≃ₗ[K] V d

def basis {d : ℕ} (i : Fin d) : V d := Pi.single i 1

private theorem twozero {d : ℕ} (w : V d) : w+w = 0 := by
  funext i
  have h : ∀ z : K, z+z = 0 := by decide
  exact h (w i)

private theorem maps_eq_on_basis {d s : ℕ} {f g : V d → V s} (hz : f 0 = g 0)
    (hadd : ∀ x y, f x = g x → f y = g y → f (x+y) = g (x+y))
    (hb : ∀ i, f (basis i) = g (basis i)) (x : V d) : f x = g x := by
  induction x using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb' => exact hadd a b ha hb'
  | single i x =>
    have h : ∀ b : K, b=0 ∨ b=1 := by decide
    rcases h x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact hb i

abbrev Slots (d : ℕ) := Fin d ⊕ ((i : Fin d) × Fin i.val)

def coefficients {d s : ℕ} (q : Q d s) : Slots d → V s :=
  Sum.elim (fun i => q (basis i))
    (fun z => QuadraticMap.polar q (basis z.1) (basis ⟨z.2.val, z.2.isLt.trans z.1.isLt⟩))

theorem coefficients_injective {d s : ℕ} : Function.Injective (@coefficients d s) := by
  intro q r he
  have hd (i : Fin d) : q (basis i) = r (basis i) := congrFun he (.inl i)
  have lower (i j : Fin d) (h : j < i) : QuadraticMap.polar q (basis i) (basis j) =
      QuadraticMap.polar r (basis i) (basis j) := congrFun he (.inr ⟨i,⟨j.val,h⟩⟩)
  have entries (i j : Fin d) : QuadraticMap.polar q (basis i) (basis j) =
      QuadraticMap.polar r (basis i) (basis j) := by
    rcases lt_trichotomy i j with h | rfl | h
    · rw [QuadraticMap.polar_comm q, QuadraticMap.polar_comm r]
      exact lower j i h
    · simp only [QuadraticMap.polar_self, two_nsmul, twozero]
    · exact lower i j h
  have eq2 (x y : V d) : QuadraticMap.polar q x y = QuadraticMap.polar r x y := by
    apply maps_eq_on_basis _ _ _ x
    · simp
    · intro u v hu hv
      simp only [QuadraticMap.polar_add_left,hu,hv]
    · intro i
      apply maps_eq_on_basis _ _ (entries i) y
      · simp
      · intro u v hu hv
        simp only [QuadraticMap.polar_add_right, hu,hv]
  apply QuadraticMap.ext
  intro x
  apply maps_eq_on_basis _ _ hd x
  · simp
  · intro u v hu hv
    rw [QuadraticMap.map_add q, QuadraticMap.map_add r, hu, hv, eq2]

theorem count_forms (d s : ℕ) :
    Nat.card (Q d s) ≤ 2^(s*(d+d*(d-1)/2)) := by
  have h := Nat.card_le_card_of_injective (@coefficients d s) coefficients_injective
  have slots : Nat.card (Slots d) = d + d*(d-1)/2 := by
    rw [Slots, Nat.card_sum, Nat.card_fin, Nat.card_sigma]
    simp only [Nat.card_fin]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
  simpa only [Nat.card_fun, slots, V, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h

theorem gl_lower (d : ℕ) : 2^(d*(d-1)) ≤ Nat.card (L d) := by
  let e : GL (Fin d) K ≃* L d := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (V d))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field (𝔽 := K) d, ZMod.card]
  cases d with
  | zero => simp
  | succ n =>
    have hfactor (i : Fin (n+1)) : 2^n ≤ 2^(n+1)-2^i.val := by
      have hi : 2^i.val ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ]
      omega
    calc
      2^((n+1)*(n+1-1)) = ∏ _i : Fin (n+1), 2^n := by simp [← pow_mul, Nat.mul_comm]
      _ ≤ _ := Finset.prod_le_prod' (fun i _ => hfactor i)

end OrbitUp

end

/- Rigid -/
section

namespace OrbitUp

abbrev Change (d s : ℕ) := L d × L s

noncomputable def change {d s : ℕ} (g : Change d s) (q : Q d s) : Q d s :=
  g.2.toLinearMap.compQuadraticMap (q.comp g.1.symm.toLinearMap)

noncomputable instance {d s : ℕ} : MulAction (Change d s) (Q d s) where
  smul := change
  one_smul q := by ext x; rfl
  mul_smul g h q := by ext x; rfl

/-- A form has no nonidentity coordinate change preserving it. -/
def Rigid {d s : ℕ} (q : Q d s) : Prop := ∀ g : Change d s, g • q = q → g=1

private theorem orbit_rigid_injective {d s : ℕ} {q : Q d s} (hq : Rigid q) :
    Function.Injective (fun g : Change d s => g • q) := by
  intro a b h
  change a • q = b • q at h
  have hg : (b⁻¹*a) • q = q := by rw [mul_smul,h,inv_smul_smul]
  exact (inv_mul_eq_one.mp (hq _ hg)).symm

private instance forms_finite (d s : ℕ) : Finite (Q d s) :=
  Finite.of_injective (@coefficients d s) coefficients_injective

private instance linear_finite (d : ℕ) : Finite (L d) :=
  Finite.of_injective (fun e : L d => (e : V d → V d)) (by intro f g h; exact LinearEquiv.ext (fun v => congrFun h v))

abbrev Classes (d s : ℕ) := MulAction.orbitRel.Quotient (Change d s) (Q d s)

def RigidClasses (d s : ℕ) :=
  {c : Classes d s // ∃ q : Q d s, Quotient.mk'' q = c ∧ Rigid q}

theorem count_rigid (d s : ℕ) :
    Nat.card (RigidClasses d s) * 2^(d*(d-1)+s*(s-1)) ≤ 2^(s*(d+d*(d-1)/2)) := by
  classical
  let rep (c : RigidClasses d s) : Q d s := c.property.choose
  have hr (c : RigidClasses d s) : Quotient.mk'' (rep c) = c.1 ∧ Rigid (rep c) :=
    c.property.choose_spec
  let encode (x : RigidClasses d s × Change d s) : Q d s := x.2 • rep x.1
  have hinj : Function.Injective encode := by
    rintro ⟨c,g⟩ ⟨e,h⟩ he
    change g • rep c = h • rep e at he
    have same (v : Change d s) (q : Q d s) :
        Quotient.mk'' (v • q) = (Quotient.mk'' q : Classes d s) :=
      Quotient.sound ((MulAction.orbitRel_apply).mpr ⟨v,rfl⟩)
    have hc : c = e := Subtype.ext (by
      rw [← (hr c).1, ← (hr e).1, ← same g (rep c), ← same h (rep e), he])
    subst e
    exact Prod.ext rfl (orbit_rigid_injective (hr c).2 he)
  have group_lower : 2^(d*(d-1)+s*(s-1)) ≤ Nat.card (Change d s) := by
    rw [Nat.pow_add, Nat.card_prod]
    exact Nat.mul_le_mul (gl_lower d) (gl_lower s)
  calc
    _ ≤ Nat.card (RigidClasses d s) * Nat.card (Change d s) :=
      Nat.mul_le_mul_left _ group_lower
    _ = Nat.card (RigidClasses d s × Change d s) := (Nat.card_prod _ _).symm
    _ ≤ Nat.card (Q d s) := Nat.card_le_card_of_injective encode hinj
    _ ≤ _ := count_forms d s

end OrbitUp

end

/- Uniform -/
section

namespace OrbitUp

private theorem rank_polynomial (d s : ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    27*(s*(d*(d+1)/2)-d*(d-1)-s*(s-1)) + 12*(d+s)^2 ≤
      2*(d+s)^3+60*(d+s) := by
  let m := d+s
  let x := d-2*m/3
  have hm : 0 ≤ m := add_nonneg hd hs
  have hdx : 0 ≤ m+x-m/3 := by dsimp [m,x]; linarith
  have cubic := mul_nonneg hdx (sq_nonneg x)
  have square := mul_nonneg hm (sq_nonneg (x+5/2))
  have xx := sq_nonneg x
  dsimp [m,x] at cubic square xx hm
  nlinarith only [cubic, square, xx, hm]

theorem rank_powers (d s : ℕ) :
    27*(s*(d+d*(d-1)/2)) + 12*(d+s)^2 ≤
      2*(d+s)^3+60*(d+s)+27*(d*(d-1)+s*(s-1)) := by
  have tri_even : 2*(d*(d-1)/2) = d*(d-1) := by
    rcases Nat.even_or_odd d with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hv : d*(d-1)=2*(k*(d-1)) := by rw [hk]; ring
      rw [hv, Nat.mul_div_cancel_left _ (by decide)]
    · have hp : d-1=2*k := by omega
      have hv : d*(d-1)=2*(d*k) := by rw [hp]; ring
      rw [hv, Nat.mul_div_cancel_left _ (by decide)]
  have input (j : ℕ) : ((j*(j-1):ℕ):ℝ) = (j:ℝ)*((j:ℝ)-1) := by
    cases j with
    | zero => simp
    | succ n => simp
  have rad := rank_polynomial (d:ℝ) (s:ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have tri : 2*((d*(d-1)/2 : ℕ):ℝ) = (d:ℝ)*((d:ℝ)-1) := by
    rw [← input]
    exact_mod_cast tri_even
  have tris := congrArg (fun r : ℝ => r*(s:ℝ)) tri
  change (2*((d*(d-1)/2:ℕ):ℝ))*(s:ℝ) = ((d:ℝ)*((d:ℝ)-1))*(s:ℝ) at tris
  have goal : 27*((s:ℝ)*((d:ℝ)+((d*(d-1)/2:ℕ):ℝ)))+12*((d:ℝ)+(s:ℝ))^2 ≤
      2*((d:ℝ)+(s:ℝ))^3+60*((d:ℝ)+(s:ℝ))+27*(((d*(d-1):ℕ):ℝ)+((s*(s-1):ℕ):ℝ)) := by
    rw [input d, input s]
    linarith only [rad,tris]
  exact_mod_cast goal

/-- Uniform over every rank split, the number of rigid quadratic-map orbits has
the sharp cubic and quadratic coefficients with an explicit linear remainder. -/
theorem rigid_sharp_uniform (d s : ℕ) :
    Nat.card (RigidClasses d s)^27 * 2^(12*(d+s)^2) ≤ 2^(2*(d+s)^3+60*(d+s)) := by
  have counted := Nat.pow_le_pow_left (count_rigid d s) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at counted
  apply Nat.le_of_mul_le_mul_right
    (c := 2^((d*(d-1)+s*(s-1))*27)) _ (Nat.pow_pos (by decide))
  calc
    _ = (Nat.card (RigidClasses d s)^27 * 2^((d*(d-1)+s*(s-1))*27)) * 2^(12*(d+s)^2) :=
      Nat.mul_right_comm _ _ _
    _ ≤ 2^((s*(d+d*(d-1)/2))*27) * 2^(12*(d+s)^2) := Nat.mul_le_mul_right _ counted
    _ = 2^((s*(d+d*(d-1)/2))*27 + 12*(d+s)^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^((2*(d+s)^3+60*(d+s))+(d*(d-1)+s*(s-1))*27) :=
      Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm 27 _] using rank_powers d s)
    _ = _ := Nat.pow_add _ _ _

/-- In particular, every rigid rank split already obeys the requested negative
quadratic coefficient once d+s reaches 20. -/
theorem rigid_below_target (d s : ℕ) (hm : 20 ≤ d+s) :
    Nat.card (RigidClasses d s)^27 * 2^(9*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  let m := d+s
  have hexp : 9*m^2 + 60*m ≤ 12*m^2 := by
    have h := Nat.mul_le_mul_right m hm
    change 20*m ≤ m*m at h
    nlinarith only [h]
  apply Nat.le_of_mul_le_mul_right (c := 2^(60*m)) _ (Nat.pow_pos (by decide))
  calc
    _ = Nat.card (RigidClasses d s)^27 * (2^(9*m^2)*2^(60*m)) := Nat.mul_assoc _ _ _
    _ = Nat.card (RigidClasses d s)^27 * 2^(9*m^2+60*m) := by rw [Nat.pow_add]
    _ ≤ Nat.card (RigidClasses d s)^27 * 2^(12*m^2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
    _ ≤ _ := (rigid_sharp_uniform d s).trans_eq (Nat.pow_add 2 (2*m^3) (60*m))

end OrbitUp

end

/- Shear -/
section

namespace OrbitUp

private def shearMap {d : ℕ} (i j : Fin d) : V d →ₗ[K] V d where
  toFun v := v + (v i) • basis j
  map_add' x y := by simp [add_smul, add_add_add_comm]
  map_smul' a x := by simp [smul_add, smul_smul]

def shear {d : ℕ} (i j : Fin d) (h : i ≠ j) : L d :=
  let t := shearMap i j
  { t with
    invFun := t
    left_inv := by
      intro v
      funext k
      have zero : basis j i = 0 := by simp [basis,Ne.symm h]
      change (v k + v i * basis j k) + (v i + v i * basis j i)*basis j k = v k
      rw [zero,mul_zero, add_zero]
      have dbl : ∀ z : K, z+z=0 := by decide
      rw [add_assoc,dbl,add_zero]
    right_inv := by
      intro v
      funext k
      have zero : basis j i = 0 := by simp [basis,Ne.symm h]
      change (v k + v i * basis j k) + (v i + v i * basis j i)*basis j k = v k
      rw [zero,mul_zero, add_zero]
      have dbl : ∀ z : K, z+z=0 := by decide
      rw [add_assoc,dbl,add_zero] }

private theorem shear_on {d : ℕ} (i j : Fin d) (h : i ≠ j) :
    shear i j h (basis i) = basis i + basis j := by
  change basis i + (basis i i) • basis j = _
  simp [basis]

private theorem shear_off {d : ℕ} (i j k : Fin d) (h : i ≠ j) (hk : k ≠ i) :
    shear i j h (basis k) = basis k := by
  change basis k + (basis k i) • basis j = _
  simp [basis,hk]

abbrev shearFixed {d : ℕ} (s : ℕ) (i j : Fin d) (h : i ≠ j) :=
  {q : Q d s // ∀ x, q (shear i j h x)=q x}

private theorem polar_invariant {d s : ℕ} {i j : Fin d} {h : i ≠ j}
    (q : shearFixed s i j h) (u v : V d) :
    QuadraticMap.polar q.val (shear i j h u) (shear i j h v) = QuadraticMap.polar q.val u v := by
  simp only [QuadraticMap.polar, ← map_add, q.property]

theorem forced_diag {d s : ℕ} {i j : Fin d} {h : i ≠ j} (q : shearFixed s i j h) :
    q.val (basis j) = QuadraticMap.polar q.val (basis i) (basis j) := by
  have fix := q.property (basis i)
  rw [shear_on, QuadraticMap.map_add q.val] at fix
  have zero : ∀ w : V s, w + w = 0 := by
    intro w
    funext k
    have dbl : ∀ z : K, z+z=0 := by decide
    exact dbl (w k)
  calc
    q.val (basis j) = q.val (basis j) + ((QuadraticMap.polar q.val (basis i) (basis j)) +
      (QuadraticMap.polar q.val (basis i) (basis j))) := by rw [zero,add_zero]
    _ = _ := by
      apply add_left_cancel (a := q.val (basis i))
      calc
        _ = (q.val (basis i)+q.val (basis j)+QuadraticMap.polar q.val (basis i) (basis j))+
            QuadraticMap.polar q.val (basis i) (basis j) := by abel
        _ = _ := by rw [fix]

theorem forced_polar {d s : ℕ} {i j : Fin d} {h : i ≠ j}
    (q : shearFixed s i j h) (k : Fin d) (hk : k ≠ i) :
    QuadraticMap.polar q.val (basis j) (basis k) = 0 := by
  have eqn := polar_invariant q (basis i) (basis k)
  rw [shear_on, shear_off _ _ _ _ hk, QuadraticMap.polar_add_left] at eqn
  exact add_left_cancel (eqn.trans (add_zero _).symm)

end OrbitUp

end

/- ShearCount -/
section

namespace OrbitUp

private abbrev lastPairs (n : ℕ) := (i : Fin n) × Fin i.val
private abbrev compact (n : ℕ) := Fin n ⊕ lastPairs n ⊕ Unit

private def compactCode {n s : ℕ} {i j : Fin (n+1)} {h : i ≠ j} (q : shearFixed s i j h) :
    compact n → V s := Sum.elim (fun k => q.val (basis (j.succAbove k))) <|
      Sum.elim (fun z => QuadraticMap.polar q.val (basis (j.succAbove z.1))
        (basis (j.succAbove ⟨z.2.val,z.2.isLt.trans z.1.isLt⟩)))
        (fun _ => QuadraticMap.polar q.val (basis i) (basis j))

private theorem compactCode_injective {n s : ℕ} (i j : Fin (n+1)) (h : i ≠ j) :
    Function.Injective (@compactCode n s i j h) := by
  intro q r he
  have hij : QuadraticMap.polar q.val (basis i) (basis j) =
      QuadraticMap.polar r.val (basis i) (basis j) := congrFun he (.inr (.inr ()))
  have hd (k : Fin (n+1)) : q.val (basis k) = r.val (basis k) := by
    rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨l,rfl⟩
    · exact (forced_diag q).trans (hij.trans (forced_diag r).symm)
    · exact congrFun he (.inl l)
  have hrow (k : Fin (n+1)) : QuadraticMap.polar q.val (basis j) (basis k) =
      QuadraticMap.polar r.val (basis j) (basis k) := by
    by_cases hk : k=i
    · subst k; rw [QuadraticMap.polar_comm q.val, QuadraticMap.polar_comm r.val]; exact hij
    · rw [forced_polar q k hk, forced_polar r k hk]
  have low (u v : Fin n) (hv : v < u) :
      QuadraticMap.polar q.val (basis (j.succAbove u)) (basis (j.succAbove v)) =
      QuadraticMap.polar r.val (basis (j.succAbove u)) (basis (j.succAbove v)) :=
    congrFun he (.inr (.inl ⟨u,⟨v.val,hv⟩⟩))
  have hp (a b : Fin (n+1)) : QuadraticMap.polar q.val (basis a) (basis b) =
      QuadraticMap.polar r.val (basis a) (basis b) := by
    rcases Fin.eq_self_or_eq_succAbove j a with rfl | ⟨u,rfl⟩
    · exact hrow b
    rcases Fin.eq_self_or_eq_succAbove j b with rfl | ⟨v,rfl⟩
    · rw [QuadraticMap.polar_comm q.val, QuadraticMap.polar_comm r.val]; exact hrow _
    rcases lt_trichotomy u v with huv | rfl | hvu
    · rw [QuadraticMap.polar_comm q.val, QuadraticMap.polar_comm r.val]; exact low v u huv
    · simp only [QuadraticMap.polar_self, hd]
    · exact low u v hvu
  apply Subtype.ext
  apply coefficients_injective
  funext z
  rcases z with k | ⟨a,b⟩
  · exact hd k
  · exact hp a ⟨b.val,b.isLt.trans a.isLt⟩

/-- A single input-coordinate transvection leaves at most this many vector-valued quadratic
maps fixed. Relative to the full coefficient count the lost exponent is s*n for domain rank n+1. -/
theorem transvection_fixed_count (n s : ℕ) (i j : Fin (n+1)) (h : i ≠ j) :
    Nat.card (shearFixed s i j h) ≤ 2^(s*(n+n*(n-1)/2+1)) := by
  have c := Nat.card_le_card_of_injective (@compactCode n s i j h) (compactCode_injective i j h)
  have countPairs : Nat.card (lastPairs n) = n*(n-1)/2 := by
    rw [lastPairs,Nat.card_sigma]
    simp only [Nat.card_fin]
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n).trans (Finset.sum_range_id n)
  have slots : Nat.card (compact n) = n+n*(n-1)/2+1 := by
    change Nat.card (Fin n ⊕ (lastPairs n ⊕ Unit)) = _
    rw [Nat.card_sum,Nat.card_sum,countPairs,Nat.card_fin]
    simp [Nat.add_assoc]
  simpa only [Nat.card_fun, slots, V, Nat.card_fin, Nat.card_zmod, ← pow_mul] using c

end OrbitUp

end

/- Mixed -/
section

namespace OrbitUp

def fixedSubspace {s : ℕ} (b : L s) : Submodule K (V s) :=
  LinearMap.ker (b.toLinearMap - LinearMap.id)

theorem mem_fixedSubspace {s : ℕ} (b : L s) (w : V s) :
    w ∈ fixedSubspace b ↔ b w = w := by
  change b w - w = 0 ↔ b w = w
  exact sub_eq_zero

theorem fixed_finrank_lt {s : ℕ} {b : L s} (hb : b ≠ 1) :
    Module.finrank K (fixedSubspace b) < s := by
  have h : fixedSubspace b ≠ ⊤ := by
    intro ht
    apply hb
    apply LinearEquiv.ext
    intro w
    exact (mem_fixedSubspace b w).mp (by rw [ht]; trivial)
  simpa only [V,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using Submodule.finrank_lt h

abbrev mixedFix {d s : ℕ} (a : L d) (b : L s) := {q : Q d s // ∀ x, b (q x) = q (a x)}

private theorem off {d : ℕ} (i j k : Fin d) (h : i ≠ j) (hk : k ≠ i) :
    shear i j h (basis k) = basis k := by
  change basis k + (basis k i) • basis j = _
  simp [basis,hk]

private theorem coeff_fix {n s : ℕ} {i j : Fin (n+1)} {h : i ≠ j} {b : L s}
    (q : mixedFix (shear i j h) b) (k : Fin n) :
    q.val (basis (i.succAbove k)) ∈ fixedSubspace b := by
  rw [mem_fixedSubspace,q.property,off _ _ _ _ (Fin.succAbove_ne _ _)]

private theorem polar_fix {n s : ℕ} {i j : Fin (n+1)} {h : i ≠ j} {b : L s}
    (q : mixedFix (shear i j h) b) (k l : Fin n) :
    QuadraticMap.polar q.val (basis (i.succAbove k)) (basis (i.succAbove l)) ∈ fixedSubspace b := by
  rw [mem_fixedSubspace]
  simp only [QuadraticMap.polar,map_sub,q.property,map_add,off _ _ _ _ (Fin.succAbove_ne _ _)]

private def mixedCode {n s : ℕ} {i j : Fin (n+1)} {h : i ≠ j} {b : L s}
    (q : mixedFix (shear i j h) b) :
    (Slots n → fixedSubspace b) × V s × (Fin n → V s) :=
  ⟨Sum.elim (fun k => ⟨q.val (basis (i.succAbove k)),coeff_fix q k⟩) (fun z =>
    ⟨QuadraticMap.polar q.val (basis (i.succAbove z.1))
      (basis (i.succAbove ⟨z.2.val,z.2.isLt.trans z.1.isLt⟩)),polar_fix q _ _⟩),
    q.val (basis i), fun l => QuadraticMap.polar q.val (basis i) (basis (i.succAbove l))⟩

private theorem mixedCode_injective {n s : ℕ} (i j : Fin (n+1)) (h : i ≠ j) (b : L s) :
    Function.Injective (@mixedCode n s i j h b) := by
  intro q r he
  have hrestricted (z : Slots n) := congrArg Subtype.val <| congrFun (congrArg Prod.fst he) z
  have hpivot : q.val (basis i) = r.val (basis i) := congrArg (fun f => f.2.1) he
  have hrow (k : Fin n) : QuadraticMap.polar q.val (basis i) (basis (i.succAbove k)) =
      QuadraticMap.polar r.val (basis i) (basis (i.succAbove k)) :=
    congrFun (congrArg (fun f => f.2.2) he) k
  have hd (k : Fin (n+1)) : q.val (basis k) = r.val (basis k) := by
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l,rfl⟩
    · exact hpivot
    · exact hrestricted (.inl l)
  have low (u v : Fin n) (hv : v < u) :
      QuadraticMap.polar q.val (basis (i.succAbove u)) (basis (i.succAbove v)) =
      QuadraticMap.polar r.val (basis (i.succAbove u)) (basis (i.succAbove v)) :=
    hrestricted (.inr ⟨u,⟨v.val,hv⟩⟩)
  have hp (k l : Fin (n+1)) : QuadraticMap.polar q.val (basis k) (basis l) =
      QuadraticMap.polar r.val (basis k) (basis l) := by
    rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨u,hk⟩ <;> subst k <;>
      rcases Fin.eq_self_or_eq_succAbove i l with hl | ⟨v,hl⟩ <;> subst l
    · simp only [QuadraticMap.polar_self,hpivot]
    · exact hrow v
    · rw [QuadraticMap.polar_comm q.val,QuadraticMap.polar_comm r.val]; exact hrow u
    · rcases lt_trichotomy u v with huv | rfl | hvu
      · rw [QuadraticMap.polar_comm q.val,QuadraticMap.polar_comm r.val]; exact low v u huv
      · simp only [QuadraticMap.polar_self,hd]
      · exact low u v hvu
  apply Subtype.ext
  apply coefficients_injective
  funext z
  rcases z with k | ⟨a,c⟩
  · exact hd k
  · exact hp a ⟨c.val,c.isLt.trans a.isLt⟩

theorem mixed_transvection_count {n s : ℕ} (i j : Fin (n+1)) (h : i ≠ j) (b : L s) :
    Nat.card (mixedFix (shear i j h) b) ≤
      2^(Module.finrank K (fixedSubspace b)*(n+n*(n-1)/2) + s*(n+1)) := by
  have c := Nat.card_le_card_of_injective (@mixedCode n s i j h b) (mixedCode_injective i j h b)
  have slots : Nat.card (Slots n) = n + n*(n-1)/2 := by
    rw [Slots, Nat.card_sum, Nat.card_fin, Nat.card_sigma]
    simp only [Nat.card_fin]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n).trans (Finset.sum_range_id n)
  have vec : Nat.card (V s) = 2^s := by simp [V]
  have arr : Nat.card (Fin n → V s) = (2^s)^n := by rw [Nat.card_fun,vec,Nat.card_fin]
  have subarr : Nat.card (Slots n → fixedSubspace b) =
      (2^(Module.finrank K (fixedSubspace b)))^(n + n*(n-1)/2) := by
    rw [Nat.card_fun,slots,Module.natCard_eq_pow_finrank (K := K) (V := fixedSubspace b),
      Nat.card_zmod]
  rw [Nat.card_prod,Nat.card_prod,subarr,arr,vec,← pow_mul,← pow_mul,←pow_add,←pow_add] at c
  convert c using 3 <;> ring

theorem mixed_nontrivial_transvection_count {n s : ℕ} (i j : Fin (n+1)) (h : i ≠ j)
    {b : L s} (hb : b ≠ 1) :
    Nat.card (mixedFix (shear i j h) b) ≤ 2^((s-1)*(n+n*(n-1)/2) + s*(n+1)) := by
  apply (mixed_transvection_count i j h b).trans
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  have := fixed_finrank_lt hb
  omega

end OrbitUp

end

/- Conjugate -/
section

namespace OrbitUp

/-- The conjugacy class of an elementary transvection. -/
abbrev ShearClass {d : ℕ} (i j : Fin d) (h : i ≠ j) :=
  {a : L d // ∃ u : L d, ∀ x, a x = u (shear i j h (u.symm x))}

private noncomputable def conjCode {d : ℕ} {i j : Fin d} {h : i ≠ j}
    (a : ShearClass i j h) : (V d →ₗ[K] K) × V d :=
  let u := a.property.choose
  ⟨(LinearMap.proj i).comp u.symm.toLinearMap, u (basis j)⟩

private theorem conj_recover {d : ℕ} {i j : Fin d} {h : i ≠ j}
    (a : ShearClass i j h) (x : V d) :
    a.val x = x + (conjCode a).1 x • (conjCode a).2 := by
  let u := a.property.choose
  calc
    _ = u (u.symm x + u.symm x i • basis j) := a.property.choose_spec x
    _ = _ := by simp [conjCode,u]

theorem card_shearClass {d : ℕ} (i j : Fin d) (h : i ≠ j) :
    Nat.card (ShearClass i j h) ≤ 2^(2*d) := by
  have inj : Function.Injective (@conjCode d i j h) := by
    intro a c he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [conj_recover a x,conj_recover c x,he]
  have eq : Nat.card (V d →ₗ[K] K) = 2^d := by
    rw [Module.natCard_eq_pow_finrank (K := K),Module.finrank_linearMap_self]
    simp [V,K]
  letI : Finite (V d →ₗ[K] K) := Finite.of_injective (fun f => (f : V d → K)) DFunLike.coe_injective
  have bd := Nat.card_le_card_of_injective _ inj
  simpa only [Nat.card_prod,eq,V,Nat.card_fun,Nat.card_fin,Nat.card_zmod,←pow_add,two_mul] using bd

private noncomputable def pullFixed {d s : ℕ} {i j : Fin d} {h : i ≠ j}
    (a : ShearClass i j h) (b : L s) (q : mixedFix a.val b) : mixedFix (shear i j h) b :=
  let u := a.property.choose
  ⟨q.val.comp u.toLinearMap, fun x => by
    change b (q.val (u x)) = q.val (u (shear i j h x))
    rw [q.property,a.property.choose_spec]
    simp [u]⟩

private theorem card_pullFixed {d s : ℕ} {i j : Fin d} {h : i ≠ j}
    (a : ShearClass i j h) (b : L s) :
    Nat.card (mixedFix a.val b) ≤ Nat.card (mixedFix (shear i j h) b) := by
  apply Nat.card_le_card_of_injective (pullFixed a b)
  intro q r he
  apply Subtype.ext
  apply QuadraticMap.ext
  intro x
  let u := a.property.choose
  have hv := congrArg (fun z : mixedFix (shear i j h) b => z.val (u.symm x)) he
  simpa only [pullFixed,QuadraticMap.comp_apply,LinearEquiv.coe_coe,u,
    LinearEquiv.apply_symm_apply] using hv

theorem gl_upper (d : ℕ) : Nat.card (L d) ≤ 2^(d*d) := by
  have inj : Function.Injective (fun a : L d => a.toLinearMap) := by
    intro a b hb
    exact LinearEquiv.ext (fun x => LinearMap.congr_fun hb x)
  letI : Finite (V d →ₗ[K] V d) := Finite.of_injective (fun f => (f : V d → V d)) DFunLike.coe_injective
  have bd := Nat.card_le_card_of_injective _ inj
  rw [Module.natCard_eq_pow_finrank (K := K) (V := V d →ₗ[K] V d),Module.finrank_linearMap] at bd
  simpa [V,K] using bd

private theorem card_sigma_le {α : Type*} [Finite α] {β : α → Type*} [∀ a, Finite (β a)]
    {c : ℕ} (h : ∀ a, Nat.card (β a) ≤ c) : Nat.card (Σ a, β a) ≤ Nat.card α * c := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _a : α, c := Finset.sum_le_sum (fun a _ => h a)
    _ = _ := by simp [Nat.card_eq_fintype_card]

abbrev Nonidentity (s : ℕ) := {b : L s // b ≠ 1}

abbrev MixedShearIncidence {n s : ℕ} (i j : Fin (n+1)) (h : i ≠ j) :=
  (a : ShearClass i j h) × (b : Nonidentity s) × mixedFix a.val b.val

/-- Total fixed-point incidences over the entire input transvection conjugacy class and
all nonidentity output transformations. -/
theorem mixed_shear_incidence_count {n s : ℕ} (i j : Fin (n+1)) (h : i ≠ j) :
    Nat.card (@MixedShearIncidence n s i j h) ≤
      2^(2*(n+1) + s*s + (s-1)*(n+n*(n-1)/2) + s*(n+1)) := by
  have gb : Nat.card (Nonidentity s) ≤ 2^(s*s) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (gl_upper s)
  have each (a : ShearClass i j h) (b : Nonidentity s) :
      Nat.card (mixedFix a.val b.val) ≤ 2^((s-1)*(n+n*(n-1)/2)+s*(n+1)) :=
    (card_pullFixed a b.val).trans (mixed_nontrivial_transvection_count i j h b.property)
  have row (a : ShearClass i j h) :
      Nat.card ((b : Nonidentity s) × mixedFix a.val b.val) ≤
      2^(s*s) * 2^((s-1)*(n+n*(n-1)/2)+s*(n+1)) :=
    (card_sigma_le (each a)).trans (Nat.mul_le_mul_right _ gb)
  have bd := (card_sigma_le row).trans
    (Nat.mul_le_mul_right _ (card_shearClass i j h))
  simpa only [←pow_add,Nat.add_assoc,MixedShearIncidence] using bd

abbrev PureShearIncidence {n : ℕ} (s : ℕ) (i j : Fin (n+1)) (h : i ≠ j) :=
  (a : ShearClass i j h) × mixedFix a.val (1 : L s)

theorem pure_shear_incidence_count {n : ℕ} (s : ℕ) (i j : Fin (n+1)) (h : i ≠ j) :
    Nat.card (PureShearIncidence s i j h) ≤ 2^(2*(n+1)+s*(n+n*(n-1)/2+1)) := by
  have row (a : ShearClass i j h) :
      Nat.card (mixedFix a.val (1 : L s)) ≤ 2^(s*(n+n*(n-1)/2+1)) := by
    apply (card_pullFixed a (1 : L s)).trans
    have inj : Function.Injective (fun q : mixedFix (shear i j h) (1 : L s) =>
        (⟨q.val,fun x => (q.property x).symm⟩ : shearFixed s i j h)) := by
      intro q r he
      exact Subtype.ext (congrArg (fun z : shearFixed s i j h => z.val) he)
    exact (Nat.card_le_card_of_injective _ inj).trans (transvection_fixed_count n s i j h)
  have bd := (card_sigma_le row).trans
    (Nat.mul_le_mul_right _ (card_shearClass i j h))
  simpa only [←pow_add,PureShearIncidence] using bd

end OrbitUp

end

/- LargeMove -/
section

namespace OrbitUp

private def entry {k s : ℕ} (t : Slots k → V s) (i j : Fin k) : V s :=
  if h : j < i then t (.inr ⟨i,⟨j.val,h⟩⟩)
  else if i=j then t (.inl i) else 0

private def bilin {k s : ℕ} (t : Slots k → V s) : V k →ₗ[K] V k →ₗ[K] V s :=
  LinearMap.mk₂ K (fun a b c => ∑ i, ∑ j, a i * b j * entry t i j c)
    (by intro a b y; funext c; simp [add_mul,Finset.sum_add_distrib])
    (by intro x a b; funext c; simp [Finset.mul_sum,mul_assoc])
    (by intro a b y; funext c; simp [mul_add,add_mul,Finset.sum_add_distrib])
    (by intro x a b; funext c; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring)

private theorem bilin_basis {k s : ℕ} (t : Slots k → V s) (i j : Fin k) :
    bilin t (basis i) (basis j) = entry t i j := by
  funext c
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b c) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

private theorem build_injective {k s : ℕ} :
    Function.Injective (fun t : Slots k → V s => LinearMap.BilinMap.toQuadraticMap (bilin t)) := by
  intro t u he
  funext z
  rcases z with i | ⟨i,j⟩
  · have eq := congrArg (fun f : Q k s => f (basis i)) he
    simpa only [LinearMap.BilinMap.toQuadraticMap_apply,bilin_basis,entry,lt_self_iff_false,
      dite_false,ite_true] using eq
  · let l : Fin k := ⟨j.val,j.isLt.trans i.isLt⟩
    have hl : l < i := j.isLt
    have eq := congrArg (fun f : Q k s => QuadraticMap.polar f (basis i) (basis l)) he
    simpa [LinearMap.BilinMap.polar_toQuadraticMap,bilin_basis,entry,hl,
      not_lt_of_ge (le_of_lt hl),ne_of_lt hl,l] using eq

theorem card_forms_exact (k s : ℕ) : Nat.card (Q k s) = 2^(s*(k+k*(k-1)/2)) := by
  apply Nat.le_antisymm (count_forms k s)
  have bd := Nat.card_le_card_of_injective _ (@build_injective k s)
  have slots : Nat.card (Slots k) = k + k*(k-1)/2 := by
    rw [Slots, Nat.card_sum, Nat.card_fin, Nat.card_sigma]
    simp only [Nat.card_fin]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k).trans (Finset.sum_range_id k)
  simpa only [Nat.card_fun,slots,V,Nat.card_fin,Nat.card_zmod,←pow_mul] using bd

/-- A change of input coordinates moves k independent directions to a second independent
subspace, as witnessed by a linear decoder. -/
def Moves {d : ℕ} (a : L d) (k : ℕ) : Prop :=
  ∃ (u : V k →ₗ[K] V d) (c : V d →ₗ[K] V k), (∀ x, c (u x) = 0) ∧ (∀ x, c (a (u x)) = x)

theorem moved_fixed_card {d s k : ℕ} {a : L d} (b : L s) (ha : Moves a k) :
    Nat.card (mixedFix a b) * 2^(s*(k+k*(k-1)/2)) ≤ 2^(s*(d+d*(d-1)/2)) := by
  obtain ⟨u,c,zero,decode⟩ := ha
  let enc (p : mixedFix a b × Q k s) : Q d s := p.1.val + p.2.comp c
  have inj : Function.Injective enc := by
    rintro ⟨q,t⟩ ⟨r,v⟩ he
    have hv (x : V d) : q.val x + t (c x) = r.val x + v (c x) :=
      congrArg (fun f : Q d s => f x) he
    have hu (x : V k) : q.val (u x) = r.val (u x) := by simpa [zero] using hv (u x)
    have ht : t = v := by
      apply QuadraticMap.ext
      intro x
      have := hv (a (u x))
      rw [decode,←q.property,←r.property,hu] at this
      exact add_left_cancel this
    subst v
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    exact add_right_cancel (hv x)
  have bd := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,card_forms_exact,card_forms_exact] at bd
  exact bd

end OrbitUp

end

/- OrbitCounting -/
section

namespace OrbitUp

abbrev Incidence (d s : ℕ) := (a : L d) × (b : L s) × mixedFix a b

private noncomputable def mixedFixEquiv {d s : ℕ} (a : L d) (b : L s) :
    mixedFix a b ≃ MulAction.fixedBy (Q d s) (a,b) where
  toFun := fun ⟨q,hq⟩ => ⟨q, by
    apply QuadraticMap.ext
    intro x
    change b (q (a.symm x)) = q x
    simpa only [a.apply_symm_apply] using hq (a.symm x)⟩
  invFun := fun ⟨q,hq⟩ => ⟨q, fun x => by
    have h := congrArg (fun z : Q d s => z (a x)) hq
    change b (q (a.symm (a x))) = q (a x) at h
    simpa only [a.symm_apply_apply] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incidence_eq_orbits_mul_group (d s : ℕ) :
    Nat.card (Incidence d s) = Nat.card (Classes d s) * Nat.card (Change d s) := by
  let e : Incidence d s ≃ (Σ g : Change d s, MulAction.fixedBy (Q d s) g) := {
    toFun := fun ⟨a,b,q⟩ => ⟨(a,b),mixedFixEquiv a b q⟩
    invFun := fun ⟨⟨a,b⟩,q⟩ => ⟨a,b,(mixedFixEquiv a b).symm q⟩
    left_inv := by rintro ⟨a,b,q⟩; rfl
    right_inv := by rintro ⟨⟨a,b⟩,q⟩; rfl }
  exact (Nat.card_congr (e.trans (MulAction.sigmaFixedByEquivOrbitsProdGroup (Change d s) (Q d s)))).trans (Nat.card_prod _ _)

/-- A bound on the three ranges of fixed-point incidences becomes a bound on every orbit. -/
theorem count_all_of_incidence {d s R : ℕ}
    (h : Nat.card (Incidence d s) ≤ (2^(2*d*R) + 2)*2^(s*(d+d*(d-1)/2))) :
    Nat.card (Classes d s) * 2^(d*(d-1)+s*(s-1)) ≤
      2^(s*(d+d*(d-1)/2)+(2*d*R+2)) := by
  rw [incidence_eq_orbits_mul_group] at h
  have hg : 2^(d*(d-1)+s*(s-1)) ≤ Nat.card (Change d s) := by
    rw [Nat.pow_add,Nat.card_prod]
    exact Nat.mul_le_mul (gl_lower d) (gl_lower s)
  have hf : 2^(2*d*R)+2 ≤ 2^(2*d*R+2) := by
    rw [Nat.pow_add]
    have hp : 0 < 2^(2*d*R) := Nat.two_pow_pos _
    omega
  calc
    _ ≤ Nat.card (Classes d s) * Nat.card (Change d s) := Nat.mul_le_mul_left _ hg
    _ ≤ _ := h
    _ ≤ 2^(2*d*R+2) * 2^(s*(d+d*(d-1)/2)) := Nat.mul_le_mul_right _ hf
    _ = _ := by rw [Nat.mul_comm, ← Nat.pow_add]

end OrbitUp

end

/- OrbitMargins -/
section

namespace OrbitUp

abbrev slotsN (d : ℕ) := d + d*(d-1)/2

theorem twice_slots (d : ℕ) : 2*slotsN d = d^2+d := by
  cases d with
  | zero => decide
  | succ n =>
    have he : 2*((n+1)*n/2)=(n+1)*n := by
      rcases Nat.even_or_odd n with ⟨k,h⟩ | ⟨k,h⟩
      · have h' : (n+1)*n=2*((n+1)*k) := by rw [h];ring
        rw [h',Nat.mul_div_cancel_left _ (by decide)]
      · have h' : (n+1)*n=2*((k+1)*n) := by rw [h];ring
        rw [h',Nat.mul_div_cancel_left _ (by decide)]
    dsimp only [slotsN]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at *
    nlinarith only [he]

/-- In the balanced range large-rank changes pay for every coordinate change. -/
theorem far_move_pays {d s r k : ℕ} (hm : 10000000 ≤ d+s) (hlo : d≤3*s)
    (hhi : 3*s≤2*d) (hr : d/128<r) (hmoves : r ≤ 2*k+2) :
    d*d+s*s ≤ s*slotsN k := by
  have hd : d≤300*k := by omega
  have hs : 360000 ≤ s := by omega
  have hsd : s ≤ d := by omega
  have h1 := Nat.mul_le_mul hd hd
  have h2 := Nat.mul_le_mul hsd hsd
  have hk := twice_slots k
  have h3 := Nat.mul_le_mul_right (slotsN k) hs
  nlinarith only [h1,h2,hk,h3]

/-- At low input rank, a nonidentity output loses enough slots to absorb the number
of possible low-rank inputs and all output changes. -/
theorem low_move_pays {d s r f : ℕ} (hhi : 3*s≤2*d)
    (hr : r≤d/128) (hf : r+f=d) :
    2*d*(d/128)+s*s ≤ slotsN f := by
  let R := d/128
  have hR : 128*R ≤ d := by dsimp [R];omega
  have hf' : 127*d ≤ 128*f := by omega
  have h1 := Nat.mul_le_mul hhi hhi
  have h2 := Nat.mul_le_mul hf' hf'
  have h3 := Nat.mul_le_mul_left d hR
  have h4 := twice_slots f
  change 2*d*R+s*s ≤ slotsN f
  nlinarith only [h1,h2,h3,h4]

theorem low_input_slack {d s : ℕ} (hm : 10000000 ≤ d+s) :
    27*(2*d*(d/128)+2) + 60*(d+s) ≤ 2*(d+s)^2 := by
  have h1 : 128*(d/128) ≤ d := by omega
  have h2 := Nat.mul_le_mul_left d h1
  have h3 := Nat.mul_le_mul_left (d+s) hm
  nlinarith only [h2,h3,hm,sq_nonneg (d:ℤ)]

/-- Far from the balanced dimension split, even the raw number of parameters is small. -/
theorem far_rank_slots {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s ≤ d ∨ 2*d ≤ 3*s) :
    27*(s*slotsN d)+10*(d+s)^2 ≤ 2*(d+s)^3 := by
  let m := d+s
  have slots := Nat.mul_le_mul_left s (le_of_eq (twice_slots d))
  have hmp := Nat.mul_le_mul_left (m^2) hm
  change 10000000 ≤ m at hm
  have gap : m^3 + 25*(27*s*d^2) ≤ 25*(4*m^3) := by
    rcases hfar with h | h
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le h
      dsimp [m]
      apply Nat.le.intro (k := 261*s^3+702*s^2*u+513*s*u^2+99*u^3)
      ring
    · have h' : 2*s ≥ d := by omega
      obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le h'
      have hh : d+s ≤ 5*u := by omega
      have hg₁ := Nat.mul_le_mul hh hh
      have hg₂ := Nat.mul_le_mul hg₁ (show d+s ≤ 4*d+s by omega)
      dsimp [m]
      nlinarith only [hg₂, congrArg (fun x : ℕ => (4*d+s)*x^2) hu,
          congrArg (fun x : ℕ => (4*d+s)*d*x) hu]
  dsimp [m] at hmp gap
  nlinarith only [slots,hmp,gap]

end OrbitUp

end

/- AllRanks -/
section

namespace OrbitUp

theorem orbit_rank_near {d s : ℕ} (hm : 10000000 ≤ d+s)
    (h : Nat.card (Incidence d s) ≤ (2^(2*d*(d/128))+2)*2^(s*slotsN d)) :
    Nat.card (Classes d s)^27 * 2^(10*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  let m := d+s
  let A := d*(d-1)+s*(s-1)
  let P := s*slotsN d
  let E := 2*d*(d/128)+2
  have hc := Nat.pow_le_pow_left (count_all_of_incidence h) 27
  change (Nat.card (Classes d s)*2^A)^27 ≤ (2^(P+E))^27 at hc
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hc
  have he : (P+E)*27+10*m^2 ≤ 2*m^3 + A*27 := by
    have hpoly := rank_powers d s
    have hslack := low_input_slack hm
    change 27*P + 12*m^2 ≤ 2*m^3+60*m+27*A at hpoly
    change 27*E + 60*m ≤ 2*m^2 at hslack
    omega
  apply Nat.le_of_mul_le_mul_right (c := 2^(A*27)) _ (Nat.two_pow_pos _)
  calc
    _ = (Nat.card (Classes d s)^27 * 2^(A*27)) * 2^(10*m^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^((P+E)*27) * 2^(10*m^2) := Nat.mul_le_mul_right _ hc
    _ = 2^((P+E)*27+10*m^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*m^3+A*27) := Nat.pow_le_pow_right (by decide) he
    _ = _ := Nat.pow_add _ _ _

theorem orbit_rank_far {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s≤d ∨ 2*d≤3*s) :
    Nat.card (Classes d s)^27 * 2^(10*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  letI : Finite (Q d s) := Finite.of_injective _ (@coefficients_injective d s)
  have hc : Nat.card (Classes d s) ≤ Nat.card (Q d s) :=
    Nat.card_le_card_of_surjective Quotient.mk'' Quotient.mk''_surjective
  have h := Nat.pow_le_pow_left (hc.trans (count_forms d s)) 27
  rw [← Nat.pow_mul] at h
  calc
    _ ≤ 2^((s*slotsN d)*27)*2^(10*(d+s)^2) := Nat.mul_le_mul_right _ h
    _ = 2^((s*slotsN d)*27+10*(d+s)^2) := (Nat.pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      rw [Nat.mul_comm (s*slotsN d) 27];exact far_rank_slots hm hfar)

end OrbitUp

end

/- FixedInput -/
section

namespace OrbitUp

/-- The input rank fixed by a gives an unconditional saving for every nonidentity output change. -/
theorem fixed_input_card {d s : ℕ} (a : L d) (b : L s) (hb : b ≠ 1) :
    let f := Module.finrank K (fixedSubspace a)
    Nat.card (mixedFix a b) * 2^(f+f*(f-1)/2) ≤ 2^(s*(d+d*(d-1)/2)) := by
  classical
  let f := Module.finrank K (fixedSubspace a)
  let e : fixedSubspace a ≃ₗ[K] V f := (Module.finBasis K _).equivFun
  let u : V f →ₗ[K] V d := (fixedSubspace a).subtype.comp e.symm.toLinearMap
  have au (x : V f) : a (u x) = u x := (mem_fixedSubspace a _).mp (e.symm x).property
  have injU : Function.Injective u := (fixedSubspace a).subtype_injective.comp e.symm.injective
  obtain ⟨c,cinv⟩ := u.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr injU)
  have cu (x : V f) : c (u x) = x := LinearMap.congr_fun cinv x
  obtain ⟨w,hw⟩ : ∃ w : V s, b w ≠ w := by
    by_contra! h
    exact hb (LinearEquiv.ext h)
  let line : V 1 →ₗ[K] V s := (LinearMap.id.smulRight w).comp (LinearMap.proj 0)
  let enc (p : mixedFix a b × Q f 1) : Q d s := p.1.val +
    line.compQuadraticMap (p.2.comp c)
  have delta (q : mixedFix a b) (t : Q f 1) (x : V f) :
      b (enc (q,t) (u x)) - enc (q,t) (u x) = t x 0 • (b w-w) := by
    change b (q.val (u x) + t (c (u x)) 0 • w) - (q.val (u x) + t (c (u x)) 0 • w) = _
    rw [cu,map_add,map_smul,q.property,au,smul_sub]
    abel
  have inj : Function.Injective enc := by
    rintro ⟨q,t⟩ ⟨r,v⟩ he
    have ht : t = v := by
      apply QuadraticMap.ext
      intro x
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      apply smul_left_injective K (sub_ne_zero.mpr hw)
      change (t x 0) • (b w - w) = (v x 0) • (b w - w)
      rw [←delta q t x,he,delta r v x]
    subst v
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    apply add_right_cancel (b := line (t (c x)))
    exact congrArg (fun z : Q d s => z x) he
  have bd := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,card_forms_exact,card_forms_exact,one_mul] at bd
  exact bd

theorem rank_add_fixed {d : ℕ} (a : L d) :
    Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id)) +
      Module.finrank K (fixedSubspace a) = d := by
  exact (a.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker.trans (by simp [V])

end OrbitUp

end

/- RankCount -/
section

namespace OrbitUp

private theorem low_rank_factor {d r : ℕ} (f : V d →ₗ[K] V d)
    (h : Module.finrank K (LinearMap.range f) ≤ r) :
    ∃ t : (V d →ₗ[K] V r) × (V r →ₗ[K] V d), t.2.comp t.1 = f := by
  have hdim : Module.finrank K (LinearMap.range f) ≤ Module.finrank K (V r) := by
    simpa only [Module.finrank_fin_fun] using h
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.mp hdim
  obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨⟨i.comp f.rangeRestrict, (LinearMap.range f).subtype.comp p⟩, ?_⟩
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (DFunLike.congr_fun hp (f.rangeRestrict x))

private lemma card_rectangular (d r : ℕ) :
    Nat.card (V d →ₗ[K] V r) = 2^(d*r) := by
  rw [Nat.card_congr (LinearMap.toMatrix' : (V d →ₗ[K] V r) ≃ₗ[K] Matrix (Fin r) (Fin d) K).toEquiv]
  change Nat.card (Fin r → Fin d → ZMod 2) = _
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]

theorem count_small_rank_changes (d r : ℕ) :
    Nat.card {a : L d // Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ r}
      ≤ 2^(2*d*r) := by
  classical
  let _ (p q : ℕ) : Finite (V p →ₗ[K] V q) :=
    Finite.of_equiv (Matrix (Fin q) (Fin p) K) LinearMap.toMatrix'.symm.toEquiv
  let A := {a : L d // Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ r}
  let f (a : A) := a.val.toLinearMap - LinearMap.id
  have fac (a : A) := low_rank_factor (r := r) (f a) a.property
  let code (a : A) := (fac a).choose
  have hi : Function.Injective code := by
    intro a b hab
    have he : f a = f b := (fac a).choose_spec.symm.trans
      ((congrArg (fun z : (V d →ₗ[K] V r) × (V r →ₗ[K] V d) => z.2.comp z.1) hab).trans (fac b).choose_spec)
    change a.val.toLinearMap - LinearMap.id = b.val.toLinearMap - LinearMap.id at he
    exact Subtype.ext (LinearEquiv.toLinearMap_injective (sub_left_inj.mp he))
  calc
    _ ≤ Nat.card ((V d →ₗ[K] V r) × (V r →ₗ[K] V d)) := Nat.card_le_card_of_injective code hi
    _ = _ := by
      rw [Nat.card_prod, card_rectangular, card_rectangular, ← pow_add]
      congr 1
      ring

end OrbitUp

end

/- Stratify -/
section

namespace OrbitUp

noncomputable abbrev rankChange {d : ℕ} (a : L d) := Module.finrank K (LinearMap.range (a.toLinearMap - LinearMap.id))

abbrev Incidences (d s : ℕ) := (a : L d) × (b : L s) × mixedFix a b

private theorem sum_bound {A : Type*} [Fintype A] (f : A → ℕ) {c z : ℕ}
    (hA : Nat.card A ≤ c) (h : ∀ a, f a ≤ z) : ∑ a, f a ≤ c * z := by
  calc
    _ ≤ ∑ _a : A, z := Finset.sum_le_sum (fun a _ => h a)
    _ = Nat.card A * z := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := Nat.mul_le_mul_right _ hA

/-- Count all stabilizer incidences in the two ranges of input rank. -/
theorem incidence_stratified (d s R : ℕ)
    (hi : ∀ a : L d, R < rankChange a → ∃ k, Moves a k ∧ d*d+s*s ≤ s*(k+k*(k-1)/2))
    (lo : ∀ a : L d, rankChange a ≤ R →
      let f := Module.finrank K (fixedSubspace a)
      2*d*R+s*s ≤ f+f*(f-1)/2) :
    Nat.card (Incidences d s) ≤ (2^(2*d*R)+2)*2^(s*(d+d*(d-1)/2)) := by
  classical
  let _ := Fintype.ofFinite (L d)
  let _ := Fintype.ofFinite (L s)
  let N := 2^(s*(d+d*(d-1)/2))
  let F (a : L d) (b : L s) := Nat.card (mixedFix a b)
  let P (a : L d) := rankChange a ≤ R
  have small (a : {a // P a}) (b : {b : L s // b ≠ 1}) :
      F a.val b.val ≤ N / (2^(2*d*R+s*s)) := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).2
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (lo a.val a.property))).trans
      (fixed_input_card a.val b.val b.property)
  have large (a : {a // ¬P a}) (b : L s) :
      F a.val b ≤ N / (2^(d*d+s*s)) := by
    obtain ⟨k,hm,hk⟩ := hi a.val (Nat.lt_of_not_ge a.property)
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).2
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)).trans (moved_fixed_card b hm)
  have all_low : Nat.card {a // P a} ≤ 2^(2*d*R) := count_small_rank_changes d R
  have all_high : Nat.card {a // ¬P a} ≤ 2^(d*d) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (gl_upper d)
  have outputs : Nat.card {b : L s // b ≠ 1} ≤ 2^(s*s) :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (gl_upper s)
  have smallrow (a : {a // P a}) :
      ∑ b : L s, F a.val b ≤ N+2^(s*s)*(N / 2^(2*d*R+s*s)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 1]
    apply Nat.add_le_add _ (sum_bound _ outputs (small a))
    exact (Nat.card_le_card_of_injective Subtype.val (@Subtype.val_injective _ _)).trans_eq
      (card_forms_exact d s)
  have biggerow (a : {a // ¬P a}) :
      ∑ b : L s, F a.val b ≤ 2^(s*s)*(N / 2^(d*d+s*s)) :=
    sum_bound _ (gl_upper s) (large a)
  have lowtotal : (∑ a : {a // P a}, ∑ b : L s, F a.val b) ≤ 2^(2*d*R)*N + N := by
    apply (sum_bound _ all_low smallrow).trans
    rw [Nat.mul_add,← Nat.mul_assoc,←pow_add 2 (2*d*R) (s*s)]
    exact Nat.add_le_add_left (Nat.mul_div_le _ _) _
  have hightotal : (∑ a : {a // ¬P a}, ∑ b : L s, F a.val b) ≤ N := by
    apply (sum_bound _ all_high biggerow).trans
    rw [← Nat.mul_assoc,←pow_add]
    exact Nat.mul_div_le _ _
  calc
    _ = ∑ a : L d, ∑ b : L s, F a b := by
      rw [Incidences,Nat.card_sigma]
      exact Finset.sum_congr rfl (fun a _ => Nat.card_sigma)
    _ = _ := (Fintype.sum_subtype_add_sum_subtype P (fun a : L d => ∑ b : L s, F a b)).symm
    _ ≤ (2^(2*d*R)*N+N)+N := Nat.add_le_add lowtotal hightotal
    _ = _ := by dsimp [N]; ring

end OrbitUp

end

/- MoveRank -/
section

namespace OrbitUp

private theorem dimV (d : ℕ) : Module.finrank K (V d) = d := by
  simp [V]

private theorem cardW {d : ℕ} (W : Submodule K (V d)) :
    (W : Set (V d)).ncard = 2^Module.finrank K W := by
  classical
  let _ := Fintype.ofFinite W
  change Nat.card W = _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ZMod.card]

/-- An excluded vector can be found as long as the rank of a-1 leaves three
dimensions outside the current paired coordinate image. -/
private theorem find_extra {d k : ℕ} (a : L d) (W : Submodule K (V d))
    (hW : Module.finrank K W ≤ 2*k)
    (high : 2*k+2 < Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id))) :
    ∃ v : V d, v ∉ W ∧ a v ∉ W ∧ a v-v ∉ W := by
  classical
  let f := a.toLinearMap - LinearMap.id
  let T := W.comap f
  let U := W.comap a.toLinearMap
  have hr : Module.finrank K f.range ≤ d := f.range.finrank_le.trans_eq (dimV _)
  have hT : T ≠ ⊤ := by
    intro he
    have hle : f.range ≤ W := by
      rintro _ ⟨x,rfl⟩
      exact (show x ∈ T by rw [he]; trivial)
    have := Submodule.finrank_mono hle
    change 2*k+2 < Module.finrank K f.range at high
    omega
  have hTd := (Submodule.finrank_lt hT).trans_eq (dimV d)
  have hUd : Module.finrank K U ≤ 2*k := by
    let g : U →ₗ[K] W := (a.toLinearMap.comp U.subtype).codRestrict W (fun x => x.property)
    have hi : Function.Injective g := fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h))
    exact (LinearMap.finrank_le_finrank_of_injective hi).trans hW
  change 2*k+2 < Module.finrank K f.range at high
  let n := d-3
  have hd : d = n+3 := by dsimp [n]; omega
  have hUW : 2*k ≤ n := by omega
  have hTn : Module.finrank K T ≤ n+2 := by omega
  by_contra! hen
  have hall : (Set.univ : Set (V d)) ⊆ (W : Set (V d)) ∪ U ∪ T := by
    intro v _
    by_cases h : v ∈ W
    · exact Or.inl (Or.inl h)
    by_cases h' : a v ∈ W
    · exact Or.inl (Or.inr h')
    exact Or.inr (hen v h h')
  have hu := Set.ncard_le_ncard hall
  have h1 := Set.ncard_union_le (W : Set (V d)) U
  have h2 := Set.ncard_union_le ((W : Set (V d)) ∪ U) T
  simp only [Set.ncard_univ, V,Nat.card_fun,Nat.card_fin,Nat.card_zmod] at hu
  rw [cardW,cardW] at h1
  rw [cardW] at h2
  have p1 := Nat.pow_le_pow_right (n := 2) (by decide) (hW.trans hUW)
  have p2 := Nat.pow_le_pow_right (n := 2) (by decide) (hUd.trans hUW)
  have p3 := Nat.pow_le_pow_right (n := 2) (by decide) hTn
  have hpow : 2^d = 2^n*8 := by rw [hd,Nat.pow_add]
  rw [hpow] at hu
  rw [Nat.pow_add] at p3
  have hp := Nat.two_pow_pos n
  omega

private def pairMap {k d : ℕ} (a : L d) (u : V k →ₗ[K] V d) :=
  u.coprod (a.toLinearMap.comp u)

private def prepend {k d : ℕ} (u : V k →ₗ[K] V d) (b : V d) : V (k+1) →ₗ[K] V d where
  toFun x := x 0 • b + u (Fin.tail x)
  map_add' x y := by
    change (x 0+y 0) • b + u (Fin.tail x + Fin.tail y) = _
    rw [add_smul,map_add]
    abel
  map_smul' z x := by
    change (z * x 0) • b + u (z • Fin.tail x) = z • (x 0 • b + u (Fin.tail x))
    rw [mul_smul,map_smul,smul_add]

private theorem extend_pair {k d : ℕ} (a : L d) (u : V k →ₗ[K] V d)
    (hu : (pairMap a u).ker = ⊥)
    (high : 2*k+2 < Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id))) :
    ∃ u' : V (k+1) →ₗ[K] V d, (pairMap a u').ker = ⊥ := by
  let W := (pairMap a u).range
  have hd : Module.finrank K W ≤ 2*k := by
    simpa only [Module.finrank_prod,dimV,two_mul] using (pairMap a u).finrank_range_le
  obtain ⟨b,hb,ha,hab⟩ := find_extra a W hd high
  refine ⟨prepend u b,LinearMap.ker_eq_bot'.mpr ?_⟩
  rintro ⟨x,y⟩ h
  change (x 0 • b + u (Fin.tail x)) + a (y 0 • b + u (Fin.tail y)) = 0 at h
  rw [map_add,map_smul] at h
  have hout : x 0 • b + y 0 • a b ∈ W := by
    have he : x 0 • b + y 0 • a b = -((pairMap a u) (Fin.tail x, Fin.tail y)) := by
      change _ = -(u (Fin.tail x) + a (u (Fin.tail y)))
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_assoc,add_left_comm,add_comm] using h
    rw [he]
    exact W.neg_mem ⟨_,rfl⟩
  have bits (z : K) : z=0 ∨ z=1 := (show ∀ w : K, w=0 ∨ w=1 by decide) z
  have hx : x 0 = 0 ∧ y 0 = 0 := by
    rcases bits (x 0) with hx|hx <;> rcases bits (y 0) with hy|hy
    · exact ⟨hx,hy⟩
    · exact False.elim (ha (by simpa [hx,hy] using hout))
    · exact False.elim (hb (by simpa [hx,hy] using hout))
    · apply False.elim (hab ?_)
      have hneg : -b=b := by
        funext i
        exact (show ∀ w : K, -w=w by decide) (b i)
      simpa [hx,hy,sub_eq_add_neg,hneg,add_comm] using hout
  simp [hx.1,hx.2] at h
  have ht : (Fin.tail x,Fin.tail y) = (0 : V k × V k) :=
    (LinearMap.ker_eq_bot'.mp hu) _ h
  apply Prod.ext
  · funext i
    exact Fin.cases hx.1 (congrFun (congrArg Prod.fst ht)) i
  · funext i
    exact Fin.cases hx.2 (congrFun (congrArg Prod.snd ht)) i

theorem exists_moves_rank {d : ℕ} (a : L d) : ∃ k,
    Module.finrank K (LinearMap.range (a.toLinearMap-LinearMap.id)) ≤ 2*k+2 ∧ Moves a k := by
  classical
  let P (k : ℕ) := ∃ u : V k →ₗ[K] V d, (pairMap a u).ker = ⊥
  have base : P 0 := ⟨0,LinearMap.ker_eq_bot'.mpr (fun x _ => Subsingleton.elim _ _)⟩
  let k := Nat.findGreatest P d
  obtain ⟨u,hu⟩ := Nat.findGreatest_spec (Nat.zero_le d) base
  refine ⟨k,?_,?_⟩
  · by_contra! h
    have hr := (LinearMap.range (a.toLinearMap-LinearMap.id)).finrank_le.trans_eq (dimV d)
    have hmax := Nat.findGreatest_is_greatest (P := P) (n := d) (k := k+1) (Nat.lt_succ_self _) (by omega)
    exact hmax (extend_pair a u hu h)
  · obtain ⟨g,hg⟩ := (pairMap a u).exists_leftInverse_of_injective hu
    refine ⟨u,(LinearMap.snd K (V k) (V k)).comp g,?_,?_⟩
    · intro x
      have h := congrArg Prod.snd (LinearMap.congr_fun hg (x,0))
      simpa [pairMap] using h
    · intro x
      have h := congrArg Prod.snd (LinearMap.congr_fun hg (0,x))
      simpa [pairMap] using h

end OrbitUp

end

/- AllOrbits -/
section

namespace OrbitUp

/-- Counts every orbit, including quadratic maps with nontrivial stabilizer. -/
theorem all_quadratic_orbits_upper (d s : ℕ) (hm : 10000000 ≤ d+s) :
    Nat.card (Classes d s)^27 * 2^(10*(d+s)^2) ≤ 2^(2*(d+s)^3) := by
  by_cases hnear : d ≤ 3*s ∧ 3*s ≤ 2*d
  · apply orbit_rank_near hm
    apply incidence_stratified d s (d/128)
    · intro a ha
      obtain ⟨k,hk,hmove⟩ := exists_moves_rank a
      exact ⟨k,hmove,far_move_pays hm hnear.1 hnear.2 ha hk⟩
    · intro a ha
      exact low_move_pays hnear.2 ha (rank_add_fixed a)
  · exact orbit_rank_far hm (by omega)

end OrbitUp

end

/- SumRanks -/
section

namespace OrbitUp

/-- The spare quadratic term pays for every dimension split and a factor two
so the resulting class of groups can be combined with its complement. -/
theorem sum_over_ranks (m A : ℕ) (hm : 10000000 ≤ m) (f : ℕ → ℕ)
    (hA : A ≤ ∑ k ∈ Finset.range (m+1), f k)
    (h : ∀ k ≤ m, (f k)^27 * 2^(10*m^2) ≤ 2^(2*m^3)) :
    (2*A)^27 * 2^(9*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image (Finset.range (m+1)) f (by simp)
  have hs : A ≤ (m+1)*f k := hA.trans (calc
    _ ≤ ∑ _i ∈ Finset.range (m+1), f k := Finset.sum_le_sum hmax
    _ = _ := by simp)
  have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfactor : 2*A ≤ 2^(m+1)*f k := calc
    _ ≤ 2*((m+1)*f k) := Nat.mul_le_mul_left _ hs
    _ = (2*(m+1))*f k := (Nat.mul_assoc _ _ _).symm
    _ ≤ (2*2^m)*f k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (show m < 2^m from Nat.lt_two_pow_self))
    _ = _ := by rw [Nat.pow_succ, Nat.mul_comm 2]
  have he : (m+1)*27+9*m^2 ≤ 10*m^2 := by
    have hbig := Nat.mul_le_mul_left m hm
    nlinarith only [hbig,hm]
  calc
    _ ≤ (2^(m+1)*f k)^27 * 2^(9*m^2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hfactor 27)
    _ = (f k)^27 * 2^((m+1)*27+9*m^2) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add, Nat.mul_comm (2^((m+1)*27)),Nat.mul_assoc]
    _ ≤ (f k)^27 * 2^(10*m^2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) he)
    _ ≤ _ := h k hk'

end OrbitUp

end

/- ClassCounts -/
section

open CategoryTheory

namespace Erdos1160

lemma groupClasses_eq_range (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}) =
      Set.range (fun h : Group (Fin n) =>
        let _ := h
        Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of (Fin n))) := by
  ext q
  constructor
  · rintro ⟨G, hG, rfl⟩
    let _ := Fintype.ofFinite G
    have hcard : Fintype.card G = n := (Nat.card_eq_fintype_card (α := G)).symm.trans hG
    let e : Fin n ≃ G := (Fintype.equivFinOfCardEq hcard).symm
    let h := e.group
    refine ⟨h, ?_⟩
    let _ := h
    let K : FiniteGrp := FiniteGrp.of (Fin n)
    let iso : K ≃* G := e.mulEquiv
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := K.toGrp) (Y := G.toGrp) iso)⟩
  · rintro ⟨h, rfl⟩
    let _ := h
    refine ⟨FiniteGrp.of (Fin n), ?_, rfl⟩
    change Nat.card (Fin n) = n
    simp

lemma finiteGroupLaws (n : ℕ) : Finite (Group (Fin n)) :=
  Finite.of_injective (fun h : Group (Fin n) => h.mul) (fun _ _ h => Group.ext h)

theorem groupClasses_finite (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  rw [groupClasses_eq_range]
  let _ := finiteGroupLaws n
  exact Set.finite_range _

theorem group_count_pos (n : ℕ) (hn : 0 < n) : 0 < g n := by
  let _ : NeZero n := ⟨hn.ne'⟩
  rw [g, Set.ncard_pos (groupClasses_finite n)]
  let C := FiniteGrp.of (Multiplicative (ZMod n))
  exact ⟨_, C, Nat.card_zmod n, rfl⟩

theorem group_count_le_multiplication_tables (n : ℕ) : g n ≤ n ^ (n * n) := by
  let _ := finiteGroupLaws n
  rw [g, groupClasses_eq_range, ← Set.image_univ]
  calc
    _ ≤ (Set.univ : Set (Group (Fin n))).ncard := Set.ncard_image_le
    _ = Nat.card (Group (Fin n)) := Set.ncard_univ _
    _ ≤ Nat.card (Fin n → Fin n → Fin n) :=
      Nat.card_le_card_of_injective (fun h : Group (Fin n) => h.mul)
        (fun _ _ h => Group.ext h)
    _ = _ := by simp [pow_mul]

end Erdos1160

end

/- BilinearExtension -/
section

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (hb : x.base = y.base)
    (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  congr

instance : Mul (BilinearExtension B) :=
  ⟨fun x y => ⟨x.base + y.base, x.fiber + y.fiber + B x.base y.base⟩⟩

instance : One (BilinearExtension B) := ⟨⟨0,0⟩⟩

instance : Inv (BilinearExtension B) :=
  ⟨fun x => ⟨-x.base, -x.fiber + B x.base x.base⟩⟩

@[simp] theorem mul_base (x y : BilinearExtension B) :
    (x*y).base = x.base + y.base := rfl
@[simp] theorem mul_fiber (x y : BilinearExtension B) :
    (x*y).fiber = x.fiber + y.fiber + B x.base y.base := rfl
@[simp] theorem inv_base (x : BilinearExtension B) : (x⁻¹).base = -x.base := rfl
@[simp] theorem inv_fiber (x : BilinearExtension B) :
    (x⁻¹).fiber = -x.fiber + B x.base x.base := rfl
@[simp] theorem one_base : (1 : BilinearExtension B).base = 0 := rfl
@[simp] theorem one_fiber : (1 : BilinearExtension B).fiber = 0 := rfl

instance : Group (BilinearExtension B) where
  mul_assoc x y z := by
    apply BilinearExtension.ext <;> simp [map_add] <;> abel
  one_mul x := by
    apply BilinearExtension.ext <;> simp
  mul_one x := by
    apply BilinearExtension.ext <;> simp
  inv_mul_cancel x := by
    apply BilinearExtension.ext <;> simp

def projection (B : V →+ V →+ W) : BilinearExtension B →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.base
  map_mul' _ _ := rfl
  map_one' := rfl

def coordinateEquiv (B : V →+ V →+ W) : BilinearExtension B ≃ V × W where
  toFun x := (x.base, x.fiber)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card (B : V →+ V →+ W) :
    Nat.card (BilinearExtension B) = Nat.card V * Nat.card W := by
  rw [Nat.card_congr (coordinateEquiv B), Nat.card_prod]

open scoped commutatorElement

theorem commutator_formula (x y : BilinearExtension B) :
    ⁅x, y⁆ = ⟨0, B x.base y.base - B y.base x.base⟩ := by
  rw [commutatorElement_def]
  apply BilinearExtension.ext <;> simp [map_add, map_neg]
  abel

theorem commutator_le_kernel (B : V →+ V →+ W) :
    commutator (BilinearExtension B) ≤ (projection B).ker := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  rw [commutator_formula]
  rfl

theorem central_fiber (w : W) :
    (⟨0,w⟩ : BilinearExtension B) ∈ Subgroup.center (BilinearExtension B) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply BilinearExtension.ext <;> simp
  abel

/-- Surjectivity of the alternating commutator on pairs ensures that the fiber is characteristic. -/
def AllFiberCommutators (B : V →+ V →+ W) : Prop :=
  ∀ w : W, ∃ u v : V, B u v - B v u = w

theorem commutator_eq_kernel (h : AllFiberCommutators B) :
    commutator (BilinearExtension B) = (projection B).ker := by
  apply le_antisymm (commutator_le_kernel B)
  intro x hx
  have hx0 : x.base = 0 := hx
  obtain ⟨u, v, huv⟩ := h x.fiber
  let a : BilinearExtension B := ⟨u, 0⟩
  let b : BilinearExtension B := ⟨v, 0⟩
  have heq : ⁅a, b⁆ = x := by
    rw [commutator_formula]
    exact BilinearExtension.ext hx0.symm huv
  rw [← heq]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

variable {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W'] {C : V' →+ V' →+ W'}

theorem map_fiber_base (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (w : W) :
    (f ⟨0, w⟩).base = 0 := by
  obtain ⟨u, v, huv⟩ := h w
  let a : BilinearExtension B := ⟨u, 0⟩
  let b : BilinearExtension B := ⟨v, 0⟩
  have heq : ⁅a, b⁆ = ⟨0, w⟩ := by
    rw [commutator_formula]
    exact BilinearExtension.ext rfl huv
  rw [← heq, map_commutatorElement, commutator_formula]

theorem map_base_lift (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (x : BilinearExtension B) :
    (f x).base = (f ⟨x.base, 0⟩).base := by
  have decomp : x = (⟨x.base, 0⟩ : BilinearExtension B) * ⟨0, x.fiber⟩ := by
    apply BilinearExtension.ext <;> simp
  conv => lhs; rw [decomp, map_mul, mul_base, map_fiber_base h, add_zero]

def inducedBase (h : AllFiberCommutators B) (f : BilinearExtension B →* BilinearExtension C) :
    V →+ V' where
  toFun u := (f ⟨u, 0⟩).base
  map_zero' := by change (f 1).base = 0; rw [map_one, one_base]
  map_add' u v := by
    let x : BilinearExtension B := ⟨u, 0⟩
    let y : BilinearExtension B := ⟨v, 0⟩
    exact (map_base_lift h f (x*y)).symm.trans (by rw [map_mul, mul_base])

def inducedFiber (h : AllFiberCommutators B) (f : BilinearExtension B →* BilinearExtension C) :
    W →+ W' where
  toFun w := (f ⟨0, w⟩).fiber
  map_zero' := by change (f 1).fiber = 0; rw [map_one, one_fiber]
  map_add' w z := by
    let x : BilinearExtension B := ⟨0, w⟩
    let y : BilinearExtension B := ⟨0, z⟩
    have eqn : (⟨0, w+z⟩ : BilinearExtension B) = x*y := by apply BilinearExtension.ext <;> simp [x,y]
    rw [eqn, map_mul, mul_fiber]
    simp [x, y, map_fiber_base h]

theorem inducedBase_apply (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (x : BilinearExtension B) :
    inducedBase h f x.base = (f x).base := (map_base_lift h f x).symm

theorem map_lift_fiber (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (w : W) :
    f ⟨0, w⟩ = ⟨0, inducedFiber h f w⟩ :=
  BilinearExtension.ext (map_fiber_base h f w) rfl

theorem intertwinement (h : AllFiberCommutators B)
    (f : BilinearExtension B →* BilinearExtension C) (u v : V) :
    inducedFiber h f (B u v - B v u) =
    C (inducedBase h f u) (inducedBase h f v) - C (inducedBase h f v) (inducedBase h f u) := by
  let x : BilinearExtension B := ⟨u, 0⟩
  let y : BilinearExtension B := ⟨v, 0⟩
  have hm := map_commutatorElement f x y
  rw [commutator_formula, commutator_formula] at hm
  exact congrArg BilinearExtension.fiber hm

theorem inducedBase_leftInv (hB : AllFiberCommutators B) (hC : AllFiberCommutators C)
    (e : BilinearExtension B ≃* BilinearExtension C) :
    Function.LeftInverse (inducedBase hC e.symm.toMonoidHom) (inducedBase hB e.toMonoidHom) := by
  intro u
  let x : BilinearExtension B := ⟨u, 0⟩
  change inducedBase hC e.symm.toMonoidHom (e x).base = u
  rw [inducedBase_apply]
  change (e.symm (e x)).base = u
  rw [e.symm_apply_apply]

theorem inducedFiber_leftInv (hB : AllFiberCommutators B) (hC : AllFiberCommutators C)
    (e : BilinearExtension B ≃* BilinearExtension C) :
    Function.LeftInverse (inducedFiber hC e.symm.toMonoidHom) (inducedFiber hB e.toMonoidHom) := by
  intro w
  change (e.symm ⟨0, inducedFiber hB e.toMonoidHom w⟩).fiber = w
  rw [← map_lift_fiber hB e.toMonoidHom w]
  change (e.symm (e ⟨0,w⟩)).fiber = w
  rw [e.symm_apply_apply]

/-- Any isomorphism of the constructed groups gives a change of coordinates on the
abelian quotient and the commutator subgroup that preserves the alternating map. -/
theorem isomorphism_preserves_alternating (hB : AllFiberCommutators B) (hC : AllFiberCommutators C)
    (e : BilinearExtension B ≃* BilinearExtension C) :
    ∃ (s : V ≃+ V') (t : W ≃+ W'), ∀ u v,
      t (B u v - B v u) = C (s u) (s v) - C (s v) (s u) := by
  let s : V ≃+ V' :=
    { inducedBase hB e.toMonoidHom with
      invFun := inducedBase hC e.symm.toMonoidHom
      left_inv := inducedBase_leftInv hB hC e
      right_inv := inducedBase_leftInv hC hB e.symm }
  let t : W ≃+ W' :=
    { inducedFiber hB e.toMonoidHom with
      invFun := inducedFiber hC e.symm.toMonoidHom
      left_inv := inducedFiber_leftInv hB hC e
      right_inv := inducedFiber_leftInv hC hB e.symm }
  exact ⟨s, t, intertwinement hB e.toMonoidHom⟩

end BilinearExtension

end Erdos1160Growth

end

/- SharpSlots -/
section

namespace Erdos1160Growth.SharpFamily

theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

end Erdos1160Growth.SharpFamily

end

/- LowerTriangularUpper -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin d
abbrev P (d s : ℕ) := Slot d → V s

variable {d s : ℕ}

def row : Slot d → Fin d := Sum.elim Sigma.fst id
def col : Slot d → Fin d :=
  Sum.elim (fun h => ⟨h.2.val, h.2.isLt.trans h.1.isLt⟩) id

def form (a : P d s) : V d →+ V d →+ V s where
  toFun x :=
    { toFun := fun y => ∑ l, (x (row l) * y (col l)) • a l
      map_zero' := by simp
      map_add' := by
        intro y z
        simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib] }
  map_zero' := by ext y; simp
  map_add' := by
    intro x y
    ext z
    simp [add_mul, add_smul, Finset.sum_add_distrib]

abbrev G (a : P d s) := BilinearExtension (form a)
instance (a : P d s) : Finite (G a) := Finite.of_equiv _ (BilinearExtension.coordinateEquiv _).symm

def bundle (a : P d s) : FiniteGrp := FiniteGrp.of (G a)
def classOf (a : P d s) : Quotient (isIsomorphicSetoid FiniteGrp) := Quotient.mk _ (bundle a)

abbrev Change (s : ℕ) := V s ≃ₗ[ZMod 2] V s

def change (u : Change s) (a : P d s) : P d s := fun l => u (a l)

lemma form_change (u : Change s) (a : P d s) (x y : V d) :
    form (change u a) x y = u (form a x y) := by
  change (∑ l, (x (row l) * y (col l)) • u (a l)) =
    u (∑ l, (x (row l) * y (col l)) • a l)
  simp

def changeIso (u : Change s) (a : P d s) : G a ≃* G (change u a) where
  toFun x := ⟨x.base, u x.fiber⟩
  invFun x := ⟨x.base, u.symm x.fiber⟩
  left_inv x := by apply BilinearExtension.ext; · rfl
                   exact u.symm_apply_apply _
  right_inv x := by apply BilinearExtension.ext; · rfl
                    exact u.apply_symm_apply _
  map_mul' x y := by
    apply BilinearExtension.ext
    · rfl
    · change u (x.fiber + y.fiber + form a x.base y.base) =
        u x.fiber + u y.fiber + form (change u a) x.base y.base
      rw [form_change,map_add,map_add]

theorem classOf_change (u : Change s) (a : P d s) :
    classOf (change u a) = classOf a := by
  symm
  apply Quotient.sound
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := (bundle a).toGrp) (Y := (bundle (change u a)).toGrp)
      (changeIso u a))⟩

def Full (a : P d s) : Prop := Submodule.span (ZMod 2) (Set.range a) = ⊤

def classes (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp)) :=
  classOf '' {a : P d s | Full a}

theorem classes_card_fiber (d s : ℕ) :
    (classes d s).ncard * Nat.card (Change s) ≤
      2 ^ (s * (d*(d-1)/2+d)) := by
  classical
  let C := ↥(classes d s)
  have witness (c : C) : ∃ a : P d s, Full a ∧ classOf a = c.val := c.property
  let rep (c : C) := Classical.choose (witness c)
  have repFull (c : C) : Full (rep c) := (Classical.choose_spec (witness c)).1
  have repClass (c : C) : classOf (rep c) = c.val := (Classical.choose_spec (witness c)).2
  let encode (cu : C × Change s) := change cu.2 (rep cu.1)
  have encInj : Function.Injective encode := by
    rintro ⟨c,u⟩ ⟨e,v⟩ heq
    change change u (rep c) = change v (rep e) at heq
    have hclass := congrArg classOf heq
    rw [classOf_change,classOf_change,repClass,repClass] at hclass
    obtain rfl : c = e := Subtype.ext hclass
    have hu : u.toLinearMap = v.toLinearMap :=
      LinearMap.ext_on_range (repFull c) (congrFun heq)
    exact Prod.ext rfl (LinearEquiv.toLinearMap_injective hu)
  calc
    _ = Nat.card (C × Change s) := by rw [Nat.card_prod]; rfl
    _ ≤ Nat.card (P d s) := Nat.card_le_card_of_injective encode encInj
    _ = _ := by
      simp only [P, V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, Slot,
        Nat.card_sum, SharpFamily.triangular_card]

end Erdos1160Growth.LowerTriangularUpper

end

/- Gaussian -/
section

namespace Erdos1160Growth.LowerTriangularUpper

variable {d s : ℕ}

lemma full_change (u : Change s) {a : P d s} (ha : Full a) : Full (change u a) := by
  change Submodule.span (ZMod 2) (Set.range (u ∘ a)) = ⊤
  rw [Set.range_comp]
  change Submodule.span (ZMod 2) (u.toLinearMap '' (Set.range a)) = ⊤
  rw [← Submodule.map_span u.toLinearMap, ha]
  simpa [Submodule.map_top] using (LinearMap.range_eq_top.mpr u.surjective : u.toLinearMap.range = ⊤)

theorem full_rows (a : P d s) (ha : Full a) :
    LinearIndependent (ZMod 2) (fun i : Fin s => fun l : Slot d => a l i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let f := Fintype.linearCombination (ZMod 2) g
  have hz : f = 0 := by
    apply LinearMap.ext_on_range ha
    intro l
    change (∑ k, a l k * g k) = 0
    simpa [Finset.sum_apply, mul_comm] using congrFun hg l
  have hi := LinearMap.congr_fun hz (Pi.single i 1)
  simpa [f, Fintype.linearCombination_apply, Pi.single_apply, ite_mul, Finset.sum_ite_eq'] using hi

theorem classes_times_GL_le_independent (d s : ℕ) :
    (classes d s).ncard * Nat.card (Change s) ≤
      Nat.card {x : Fin s → Slot d → ZMod 2 // LinearIndependent (ZMod 2) x} := by
  classical
  let C := ↥(classes d s)
  have witness (c : C) : ∃ a : P d s, Full a ∧ classOf a = c.val := c.property
  let rep (c : C) := Classical.choose (witness c)
  have repFull (c : C) : Full (rep c) := (Classical.choose_spec (witness c)).1
  have repClass (c : C) : classOf (rep c) = c.val := (Classical.choose_spec (witness c)).2
  let encode (cu : C × Change s) : {x : Fin s → Slot d → ZMod 2 // LinearIndependent (ZMod 2) x} :=
    ⟨fun i l => (change cu.2 (rep cu.1)) l i, full_rows _ (full_change cu.2 (repFull cu.1))⟩
  have encInj : Function.Injective encode := by
    rintro ⟨c,u⟩ ⟨e,v⟩ h
    have heq : change u (rep c) = change v (rep e) := by
      funext l i
      exact congrFun (congrFun (congrArg Subtype.val h) i) l
    have hclass := congrArg classOf heq
    rw [classOf_change,classOf_change,repClass,repClass] at hclass
    obtain rfl : c = e := Subtype.ext hclass
    have hu : u.toLinearMap = v.toLinearMap := LinearMap.ext_on_range (repFull c) (congrFun heq)
    exact Prod.ext rfl (LinearEquiv.toLinearMap_injective hu)
  calc
    _ = Nat.card (C × Change s) := by rw [Nat.card_prod]; rfl
    _ ≤ _ := Nat.card_le_card_of_injective encode encInj

end Erdos1160Growth.LowerTriangularUpper

end

/- FiberGL -/
section

namespace Erdos1160Growth.LowerTriangularUpper

lemma card_change (s : ℕ) :
    Nat.card (Change s) = ∏ i : Fin s, (2^s-2^i.val) := by
  let e : Matrix.GeneralLinearGroup (Fin s) (ZMod 2) ≃* Change s :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (V s))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp

theorem triangular_class_upper (d s : ℕ) :
    (classes d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      2^(s * (d*(d-1)/2+d)) := by
  rw [← card_change]
  exact classes_card_fiber d s

def D (d : ℕ) : ℕ := d*(d-1)/2+d

lemma finrank_slots (d : ℕ) : Module.finrank (ZMod 2) (Slot d → ZMod 2) = D d := by
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]
  simp only [Slot,D,Nat.card_sum,SharpFamily.triangular_card,Nat.card_fin]

theorem gaussian_upper (d s : ℕ) (hs : s ≤ D d) :
    (classes d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      ∏ i : Fin s, (2^(D d)-2^i.val) := by
  have h := classes_times_GL_le_independent d s
  have hk : s ≤ Module.finrank (ZMod 2) (Slot d → ZMod 2) := by rw [finrank_slots]; exact hs
  rw [card_change,card_linearIndependent hk,finrank_slots, ZMod.card] at h
  exact h

end Erdos1160Growth.LowerTriangularUpper

end

/- Normalize -/
section

namespace Erdos1160Growth.LowerTriangularUpper

variable {d s : ℕ}

lemma form_add (a b : P d s) : form (a+b) = form a + form b := by
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  change (∑ l, (x (row l) * y (col l)) • (a l+b l)) =
    (∑ l, (x (row l) * y (col l)) • a l) + ∑ l, (x (row l) * y (col l)) • b l
  simp only [smul_add,Finset.sum_add_distrib]

lemma two_copies_zero (v : V s) : v+v = 0 := by
  ext i
  exact (show ∀ z : ZMod 2, z+z = 0 by decide) (v i)

def normalizedIso (A B : V d →+ V d →+ V s) :
    BilinearExtension (A + B.flip) ≃* BilinearExtension (A + B) where
  toFun x := ⟨x.base, x.fiber + B x.base x.base⟩
  invFun x := ⟨x.base, x.fiber - B x.base x.base⟩
  left_inv x := by apply BilinearExtension.ext; · rfl
                   exact add_sub_cancel_right _ _
  right_inv x := by apply BilinearExtension.ext; · rfl
                    exact sub_add_cancel _ _
  map_mul' x y := by
    apply BilinearExtension.ext
    · rfl
    · change (x.fiber + y.fiber + (A x.base y.base + B y.base x.base)) +
        B (x.base+y.base) (x.base+y.base) =
        (x.fiber+B x.base x.base) + (y.fiber+B y.base y.base) +
          (A x.base y.base + B x.base y.base)
      simp only [map_add,AddMonoidHom.add_apply]
      nth_rewrite 2 [← add_zero (B x.base y.base)]
      rw [← two_copies_zero (B y.base x.base)]
      abel

noncomputable def normalize_arrays (a b : P d s) :
    BilinearExtension (form a + (form b).flip) ≃* G (a+b) := by
  unfold G
  rw [form_add]
  exact normalizedIso (form a) (form b)

end Erdos1160Growth.LowerTriangularUpper

end

/- TensorFamily -/
section

open scoped BigOperators commutatorElement

namespace Erdos1160Growth.TensorFamily

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev T (d : ℕ) := Fin d → Fin d → V d

variable {d : ℕ}

def basis (i : Fin d) : V d := Pi.single i 1

def form (t : T d) : (V d × V d) →+ (V d × V d) →+ V d where
  toFun a :=
    { toFun := fun b k => ∑ i, ∑ j, a.2 i * b.1 j * t i j k
      map_zero' := by funext k; simp
      map_add' := by
        intro b c
        funext k
        simp [mul_add, add_mul, Finset.sum_add_distrib] }
  map_zero' := by ext b k; simp
  map_add' := by
    intro a b
    ext c k
    simp [add_mul, Finset.sum_add_distrib]

abbrev G (t : T d) := BilinearExtension (form t)

def X (t : T d) (x : V d) : G t := ⟨(x, 0), 0⟩
def Y (t : T d) (y : V d) : G t := ⟨(0, y), 0⟩
def Z (t : T d) (z : V d) : G t := ⟨0, z⟩

lemma cross_form (t : T d) (i j : Fin d) :
    form t (0,basis i) (basis j, 0) = t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

theorem commutator_YX (t : T d) (i j : Fin d) :
    ⁅Y t (basis i), X t (basis j)⁆ = Z t (t i j) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  change form t (0,basis i) (basis j,0) - form t (basis j,0) (0,basis i) = t i j
  rw [cross_form]
  have hz : form t (basis j, 0) (0, basis i) = 0 := by funext k; simp [form]
  rw [hz, sub_zero]

lemma XYZ_normal (t : T d) (x y z : V d) :
    X t x * Y t y * Z t z = ⟨(x,y),z⟩ := by
  apply BilinearExtension.ext
  · simp [X,Y,Z]
  · rw [BilinearExtension.mul_fiber, BilinearExtension.mul_fiber]
    simp [X, Y, Z, form]
    funext k; simp

theorem Z_injective (t : T d) : Function.Injective (Z t) := fun _ _ h => congrArg BilinearExtension.fiber h

lemma Z_add (t : T d) (u v : V d) : Z t (u + v) = Z t u * Z t v := by
  apply BilinearExtension.ext <;> simp [Z]

theorem map_Z_of_basis {s t : T d} (e : G s →* G t)
    (hz : ∀ i, e (Z s (basis i)) = Z t (basis i)) (v : V d) : e (Z s v) = Z t v := by
  induction v using Pi.single_induction with
  | zero => exact e.map_one
  | add a b ha hb => rw [Z_add, map_mul, ha, hb, ← Z_add]
  | single i x =>
    have hbit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hbit x with rfl | rfl
    · rw [Pi.single_zero]; exact e.map_one
    · exact hz i

end Erdos1160Growth.TensorFamily

end

/- AllBilinear -/
section

namespace Erdos1160Growth.LowerTriangularUpper

variable {d s : ℕ}

def bit (i : Fin d) : V d := Pi.single i 1

lemma col_le_row (l : Slot d) : col l ≤ row l := by
  rcases l with ⟨i,j⟩|i
  · exact j.isLt.le
  · exact le_rfl

lemma slot_inj : Function.Injective (fun l : Slot d => (row l,col l)) := by
  rintro (⟨i,j⟩|i) (⟨k,n⟩|k) h
  · obtain rfl : i = k := congrArg Prod.fst h
    have hval : j.val = n.val := congrArg (fun p => (p.2 : Fin d).val) h
    obtain rfl : j = n := Fin.ext hval
    rfl
  · have h1 : i = k := congrArg Prod.fst h
    have h2 : j.val = k.val := congrArg (fun p => (p.2 : Fin d).val) h
    have hj := j.isLt
    subst k
    omega
  · have h1 : i = k := congrArg Prod.fst h
    have h2 : i.val = n.val := congrArg (fun p => (p.2 : Fin d).val) h
    have hn := n.isLt
    subst i
    omega
  · obtain rfl : i = k := congrArg Prod.fst h
    rfl

lemma form_at_slot (a : P d s) (l : Slot d) :
    form a (bit (row l)) (bit (col l)) = a l := by
  change (∑ k, (bit (row l) (row k) * bit (col l) (col k)) • a k) = a l
  rw [Fintype.sum_eq_single l]
  · simp [bit]
  · intro k hk
    by_cases hr : row k = row l
    · have hc : col k ≠ col l := fun hc => hk (slot_inj <| Prod.ext hr hc)
      simp [bit,Pi.single_apply,hc]
    · simp [bit,Pi.single_apply,hr]

lemma form_above (a : P d s) (i j : Fin d) (h : i < j) :
    form a (bit i) (bit j) = 0 := by
  change (∑ l, (bit i (row l) * bit j (col l)) • a l) = 0
  apply Finset.sum_eq_zero
  intro l _
  by_cases hr : row l = i
  · have hc : col l ≠ j := by
      intro hc
      have hrc := col_le_row l
      rw [hr,hc] at hrc
      exact h.not_ge hrc
    simp [bit,Pi.single_apply,hc]
  · simp [bit,Pi.single_apply,hr]

lemma addhom_eq_bits {W : Type*} [AddCommGroup W] (b c : V d →+ W)
    (h : ∀ i, b (bit i) = c (bit i)) : b = c := by
  apply AddMonoidHom.ext
  intro x
  induction x using Pi.single_induction with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single i a =>
    have hbit : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide
    rcases hbit a with rfl|rfl
    · simp
    · exact h i

def lowerArray (B : V d →+ V d →+ V s) : P d s := fun l => B (bit (row l)) (bit (col l))
def upperArray (B : V d →+ V d →+ V s) : P d s := fun l =>
  if row l = col l then 0 else B (bit (col l)) (bit (row l))

lemma split_matrix (B : V d →+ V d →+ V s) :
    B = form (lowerArray B) + (form (upperArray B)).flip := by
  apply addhom_eq_bits
  intro i
  apply addhom_eq_bits
  intro j
  change B (bit i) (bit j) = form (lowerArray B) (bit i) (bit j) +
    form (upperArray B) (bit j) (bit i)
  rcases lt_trichotomy i j with hij | rfl | hji
  · let l : Slot d := .inl ⟨j,⟨i.val,hij⟩⟩
    rw [form_above _ _ _ hij,zero_add]
    change _ = form (upperArray B) (bit (row l)) (bit (col l))
    rw [form_at_slot]
    simp [upperArray,l,row,col,ne_of_gt hij]
  · let l : Slot d := .inr i
    change _ = form (lowerArray B) (bit (row l)) (bit (col l)) +
      form (upperArray B) (bit (row l)) (bit (col l))
    rw [form_at_slot,form_at_slot]
    simp [l,row,col,lowerArray,upperArray]
  · let l : Slot d := .inl ⟨i,⟨j.val,hji⟩⟩
    rw [form_above _ _ _ hji,add_zero]
    change _ = form (lowerArray B) (bit (row l)) (bit (col l))
    rw [form_at_slot]
    rfl

noncomputable def allBilinear_normal (B : V d →+ V d →+ V s) :
    BilinearExtension B ≃* G (lowerArray B + upperArray B) := by
  let castLaw {b c : V d →+ V d →+ V s} (h : b = c) : BilinearExtension b ≃* BilinearExtension c := h ▸ MulEquiv.refl _
  apply (castLaw (split_matrix B)).trans
  exact normalize_arrays _ _

end Erdos1160Growth.LowerTriangularUpper

end

/- SquareSpanUpper -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory

variable {d s : ℕ}

lemma square_span_eq (B : V d →+ V d →+ V s) :
    Submodule.span (ZMod 2) (Set.range (fun x => B x x)) =
      Submodule.span (ZMod 2) (Set.range (lowerArray B + upperArray B)) := by
  let C := lowerArray B + upperArray B
  let K := Submodule.span (ZMod 2) (Set.range (fun x => B x x))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hsplit := congrArg (fun L : V d →+ V d →+ V s => L x x) (split_matrix B)
    change B x x = form (lowerArray B) x x + form (upperArray B) x x at hsplit
    have hsum := congrArg (fun L : V d →+ V d →+ V s => L x x) (form_add (lowerArray B) (upperArray B))
    change form C x x = form (lowerArray B) x x + form (upperArray B) x x at hsum
    change B x x ∈ Submodule.span (ZMod 2) (Set.range C)
    rw [hsplit,←hsum]
    apply Submodule.sum_mem
    intro l _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨l,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    have diagonal (x : V d) : B x x ∈ K := Submodule.subset_span ⟨x,rfl⟩
    rcases l with ⟨i,j⟩ | i
    · let k : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
      have hk : k < i := j.isLt
      change B (bit i) (bit k) + (if i = k then 0 else B (bit k) (bit i)) ∈ K
      rw [if_neg (ne_of_gt hk)]
      have h := K.sub_mem (K.sub_mem (diagonal (bit i + bit k)) (diagonal (bit i))) (diagonal (bit k))
      simp only [map_add,AddMonoidHom.add_apply] at h
      convert h using 1 <;> abel
    · change B (bit i) (bit i) + (if i=i then 0 else _) ∈ K
      simpa using diagonal (bit i)

private def bundleB (B : V d →+ V d →+ V s) : FiniteGrp :=
  have : Finite (BilinearExtension B) := Finite.of_equiv _ (BilinearExtension.coordinateEquiv _).symm
  FiniteGrp.of (BilinearExtension B)

def bilinearClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp)) :=
  (fun B : V d →+ V d →+ V s => Quotient.mk _ (bundleB B)) ''
    {B | Submodule.span (ZMod 2) (Set.range (fun x => B x x)) = ⊤}

lemma classes_finite (d s : ℕ) : (classes d s).Finite :=
  (Set.toFinite {a : P d s | Full a}).image _

lemma bilinearClasses_subset (d s : ℕ) : bilinearClasses d s ⊆ classes d s := by
  rintro _ ⟨B,hB,rfl⟩
  refine ⟨lowerArray B+upperArray B, ?_, ?_⟩
  · change Submodule.span (ZMod 2) (Set.range _) = ⊤
    rw [←square_span_eq]
    exact hB
  · symm
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (bundleB B).toGrp)
        (Y := (bundle (lowerArray B+upperArray B)).toGrp) (allBilinear_normal B))⟩

theorem bilinear_gaussian_upper (d s : ℕ) (hs : s ≤ D d) :
    (bilinearClasses d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      ∏ i : Fin s, (2^(D d)-2^i.val) :=
  (Nat.mul_le_mul_right _ (Set.ncard_le_ncard (bilinearClasses_subset d s)
    (classes_finite d s))).trans (gaussian_upper d s hs)

end Erdos1160Growth.LowerTriangularUpper

end

/- ExtensionBasics -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open scoped commutatorElement

structure CentralData (E : Type*) [Group E] (d s : ℕ) where
  incl : Multiplicative (V s) →* E
  proj : E →* Multiplicative (V d)
  incl_inj : Function.Injective incl
  proj_onto : Function.Surjective proj
  exact_ker : proj.ker = incl.range
  central : ∀ v : Multiplicative (V s), ∀ x : E, Commute (incl v) x

namespace CentralData

variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)

def liftK (w : V s) : E := S.incl (Multiplicative.ofAdd w)
def base (x : E) : V d := (S.proj x).toAdd

@[simp] lemma liftK_zero : S.liftK 0 = 1 := S.incl.map_one
@[simp] lemma liftK_add (a b : V s) : S.liftK (a+b) = S.liftK a * S.liftK b := S.incl.map_mul ..
@[simp] lemma base_one : S.base 1 = 0 := congrArg Multiplicative.toAdd S.proj.map_one
@[simp] lemma base_mul (x y : E) : S.base (x*y) = S.base x + S.base y :=
  congrArg Multiplicative.toAdd (S.proj.map_mul ..)
lemma liftK_comm (v : V s) (x : E) : Commute (S.liftK v) x := S.central _ _
lemma liftK_inj : Function.Injective S.liftK := fun _ _ h => congrArg Multiplicative.toAdd (S.incl_inj h)
lemma liftK_mem (v : V s) : S.base (S.liftK v) = 0 := by
  change S.liftK v ∈ S.proj.ker
  rw [S.exact_ker]
  exact ⟨_,rfl⟩
lemma exists_lift {x : E} (hx : S.base x = 0) : ∃ w : V s, S.liftK w = x := by
  change x ∈ S.proj.ker at hx
  rw [S.exact_ker] at hx
  exact hx
lemma base_onto : Function.Surjective S.base := fun w => S.proj_onto (Multiplicative.ofAdd w)
lemma exists_square (x : E) : ∃ w, S.liftK w = x*x := by
  apply S.exists_lift
  rw [base_mul,two_copies_zero]

end CentralData
end Erdos1160Growth.LowerTriangularUpper

end

/- ElementaryCoords -/
section

namespace Erdos1160Growth.LowerTriangularUpper

lemma exist_elementary_coords {G : Type*} [Group G] [Finite G] {d : ℕ}
    (h : ∀ x : G, x*x=1) (hcard : Nat.card G = 2^d) :
    Nonempty (G ≃* Multiplicative (V d)) := by
  classical
  have hinv (x : G) : x⁻¹=x := inv_eq_of_mul_eq_one_left (h x)
  let _ : CommGroup G := { ‹Group G› with
    mul_comm := fun x y => by
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv] }
  let _ : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact h x.toMul)
  let _ : Fintype (Additive G) := Fintype.ofFinite _
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive G)
  rw [← Nat.card_eq_fintype_card, ZMod.card] at hc
  change Nat.card G = 2^Module.finrank (ZMod 2) (Additive G) at hc
  rw [hcard] at hc
  have hd : Module.finrank (ZMod 2) (Additive G) = d :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hd).equivFun
  exact ⟨e.toAddEquiv.toMultiplicativeRight⟩

noncomputable def dataOfSubgroup {G : Type*} [Group G] (H : Subgroup G) [H.Normal] {d s : ℕ}
    (hc : H ≤ Subgroup.center G) (h : H ≃* Multiplicative (V s))
    (q : G ⧸ H ≃* Multiplicative (V d)) : CentralData G d s where
  incl := H.subtype.comp h.symm.toMonoidHom
  proj := q.toMonoidHom.comp (QuotientGroup.mk' H)
  incl_inj := Subtype.val_injective.comp h.symm.injective
  proj_onto := q.surjective.comp (QuotientGroup.mk'_surjective H)
  exact_ker := by
    ext x
    constructor
    · intro hx
      change q ((QuotientGroup.mk' H) x) = 1 at hx
      have hh : x ∈ H := (QuotientGroup.eq_one_iff x).mp (q.injective (hx.trans q.map_one.symm))
      exact ⟨h ⟨x,hh⟩,by simp⟩
    · rintro ⟨w,rfl⟩
      change q ((QuotientGroup.mk' H) ((h.symm w : H) : G)) = 1
      simp
  central v x := by
    have hcomm := Subgroup.mem_center_iff.mp (hc (h.symm v).property) x
    exact hcomm.symm

end Erdos1160Growth.LowerTriangularUpper

end

/- SectionEquiv -/
section

namespace Erdos1160Growth.LowerTriangularUpper.CentralData

open CategoryTheory

variable {E : Type*} [Group E] {d s : ℕ}
variable (S : CentralData E d s) (σ : V d → E) (B : V d →+ V d →+ V s)
variable (hπ : ∀ x, S.base (σ x) = x)
variable (hmul : ∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y))

include hmul in
theorem section_zero : σ 0 = 1 := by
  have he := hmul 0 0
  simp only [map_zero,S.liftK_zero,one_mul,zero_add] at he
  exact mul_right_cancel (b := σ 0) (he.trans (one_mul _).symm)

include hπ in
theorem section_decomp (z : E) : ∃ w, S.liftK w * σ (S.base z) = z := by
  have hb : S.base (z * (σ (S.base z))⁻¹) = 0 := by
    change (S.proj (z * (σ (S.base z))⁻¹)).toAdd = 0
    rw [map_mul, map_inv]
    change S.base z + -S.base (σ (S.base z)) = 0
    rw [hπ,add_neg_cancel]
  obtain ⟨w,hw⟩ := S.exists_lift hb
  exact ⟨w, by rw [hw, mul_assoc, inv_mul_cancel, mul_one]⟩

def sectionHom : BilinearExtension B →* E where
  toFun z := S.liftK z.fiber * σ z.base
  map_one' := by simp [section_zero S σ B hmul]
  map_mul' x y := by
    change S.liftK (x.fiber+y.fiber+B x.base y.base)*σ (x.base+y.base) = _
    rw [S.liftK_add, S.liftK_add, mul_assoc, mul_assoc, ← hmul]
    rw [mul_assoc, (S.liftK_comm y.fiber (σ x.base)).symm.left_comm]

noncomputable def sectionEquiv : BilinearExtension B ≃* E := by
  apply MulEquiv.ofBijective (sectionHom S σ B hmul)
  constructor
  · rintro ⟨u,w⟩ ⟨v,t⟩ h
    change S.liftK w * σ u = S.liftK t * σ v at h
    have hb := congrArg S.base h
    simp only [S.base_mul, S.liftK_mem, zero_add, hπ] at hb
    subst v
    obtain rfl := S.liftK_inj (mul_right_cancel h)
    rfl
  · intro z
    obtain ⟨w,hw⟩ := S.section_decomp σ hπ z
    exact ⟨⟨S.base z,w⟩,hw⟩

include hπ hmul in
theorem squares_eq_diagonal :
    {w : V s | ∃ z : E, S.liftK w = z*z} = Set.range (fun u => B u u) := by
  ext w
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t,ht⟩ := S.section_decomp σ hπ z
    refine ⟨S.base z, S.liftK_inj ?_⟩
    have h_square : (S.liftK t * σ (S.base z))*(S.liftK t * σ (S.base z)) =
        S.liftK (B (S.base z) (S.base z)) := by
      rw [mul_assoc, (S.liftK_comm t (σ (S.base z))).symm.left_comm, ← mul_assoc]
      rw [← S.liftK_add, two_copies_zero, S.liftK_zero, one_mul,hmul,
        two_copies_zero,section_zero S σ B hmul,mul_one]
    rw [ht] at h_square
    exact h_square.symm.trans hz.symm
  · rintro ⟨u,rfl⟩
    refine ⟨σ u, ?_⟩
    rw [hmul, two_copies_zero,section_zero S σ B hmul,mul_one]

end Erdos1160Growth.LowerTriangularUpper.CentralData

end

/- CommCode -/
section

namespace Erdos1160Growth.LowerTriangularUpper.CentralData

open scoped commutatorElement

/-- Centrality and the abelian quotient turn commutation with g into a character on E. -/
theorem exists_commCode {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s) (g : E) :
    ∃ h : E →* Multiplicative (V s), (∀ x, g * x = S.liftK (h x).toAdd * x * g) ∧
      (∀ w, h (S.liftK w) = 1) := by
  classical
  have hc (x : E) : ⁅g, x⁆ ∈ S.incl.range := by
    rw [← S.exact_ker]
    change S.proj ⁅g, x⁆ = 1
    simpa only [map_commutatorElement] using
      (commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (S.proj g) (S.proj x)))
  choose c he using hc
  have central (x y : E) : Commute ⁅g, x⁆ y := he x ▸ S.central (c x) y
  let h : E →* Multiplicative (V s) := {
    toFun := c
    map_one' := S.incl_inj (by rw [he, commutatorElement_one_right, S.incl.map_one])
    map_mul' := fun x y => S.incl_inj (by
      rw [he, S.incl.map_mul, he, he, commutatorElement_mul_right_eq_mul_conj]
      rw [mul_assoc ⁅g, x⁆ x, (central y x).symm.eq, ← mul_assoc, mul_inv_cancel_right]) }
  refine ⟨h, ?_, ?_⟩
  · intro x
    change g * x = S.incl (c x) * x * g
    rw [he, commutatorElement_def]
    group
  · intro w
    apply S.incl_inj
    change S.incl (c (S.liftK w)) = S.incl 1
    rw [he, S.incl.map_one]
    exact (S.liftK_comm w g).symm.commutator_eq

end Erdos1160Growth.LowerTriangularUpper.CentralData

end

/- Collect -/
section

namespace Erdos1160Growth.LowerTriangularUpper.CentralData

variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)

structure Collected where
  sec : V d → E
  bil : V d →+ V d →+ V s
  sec_zero : sec 0 = 1
  sec_mul : ∀ x y, sec x * sec y = S.liftK (bil x y) * sec (x+y)

private lemma two_bits (b : ZMod 2) : b = 0 ∨ b = 1 :=
  (show ∀ b : ZMod 2, b=0 ∨ b=1 by decide) b

def useBit (g : E) (b : ZMod 2) : E := if b=1 then g else 1

lemma bit_product (g : E) (z : V s) (hz : S.liftK z = g*g) (a b : ZMod 2) :
    useBit g a * useBit g b = S.liftK ((a*b) • z) * useBit g (a+b) := by
  rcases two_bits a with rfl|rfl <;> rcases two_bits b with rfl|rfl <;>
    simp [useBit,show (1+1 : ZMod 2) = 0 by decide,hz]

lemma bit_cross (g y : E) (v : V s) (h : g*y = S.liftK v * y * g) (u : ZMod 2) :
    useBit g u * y = S.liftK (u • v) * y * useBit g u := by
  rcases two_bits u with rfl|rfl <;> simp [useBit,h]

lemma product_collect (x b y b' X B : E) (a c z : V s)
    (hbase : x*y = S.liftK a * X)
    (hcross : b*y = S.liftK c * y * b)
    (hbit : b*b' = S.liftK z * B) :
    (x*b)*(y*b') = S.liftK (a+c+z) * (X*B) := by
  calc
    _ = x*(b*y)*b' := by group
    _ = (x*S.liftK c)*(y*(b*b')) := by rw [hcross]; group
    _ = S.liftK c*((x*y)*(b*b')) := by rw [←(S.liftK_comm c x).eq]; group
    _ = S.liftK c*((S.liftK a*X)*(S.liftK z*B)) := by rw [hbase,hbit]
    _ = S.liftK c*(S.liftK a*(X*S.liftK z)*B) := by group
    _ = S.liftK (c+a+z)*(X*B) := by rw [←(S.liftK_comm z X).eq]; simp [mul_assoc]
    _ = _ := by rw [add_comm c a]

def crossBilinear (i : Fin d) (L : V d →+ V s) (z : V s) : V d →+ V d →+ V s where
  toFun x :=
    { toFun := fun y => x i • L y + (x i * y i) • z
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add,smul_add,mul_add,add_smul]; abel }
  map_zero' := by apply AddMonoidHom.ext; intro x; simp
  map_add' := by
    intro x y
    apply AddMonoidHom.ext
    intro v
    simp [add_mul, add_smul]
    abel

noncomputable def codeLinear (C : Collected S) (h : E →* Multiplicative (V s))
    (hc : ∀ w, h (S.liftK w) = 1) : V d →+ V s where
  toFun x := (h (C.sec x)).toAdd
  map_zero' := by rw [C.sec_zero,map_one]; rfl
  map_add' x y := by
    have hm := congrArg h (C.sec_mul x y)
    rw [map_mul, map_mul, hc, one_mul] at hm
    exact congrArg Multiplicative.toAdd hm.symm

noncomputable def adjoin (C : Collected S) (g : E) (i : Fin d) : Collected S := by
  let z := Classical.choose (S.exists_square g)
  have hz : S.liftK z = g*g := Classical.choose_spec (S.exists_square g)
  let h := Classical.choose (S.exists_commCode g)
  have hh := Classical.choose_spec (S.exists_commCode g)
  let L := S.codeLinear C h hh.2
  exact
    { sec := fun x => C.sec x * useBit g (x i)
      bil := C.bil + crossBilinear i L z
      sec_zero := by simp [C.sec_zero,useBit]
      sec_mul := by
        intro x y
        exact S.product_collect _ _ _ _ _ _ (C.bil x y) (x i • L y) ((x i*y i) • z)
          (C.sec_mul x y) (S.bit_cross g (C.sec y) (L y) (hh.1 _) (x i))
          (S.bit_product g z hz (x i) (y i)) |>.trans (by
            congr 2
            exact add_assoc _ _ _) }

end Erdos1160Growth.LowerTriangularUpper.CentralData

end

/- SectionCoverage -/
section

namespace Erdos1160Growth.LowerTriangularUpper.CentralData

variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)

def emptyCollected : Collected S where
  sec _ := 1
  bil := 0
  sec_zero := rfl
  sec_mul x y := by change 1*1 = S.liftK 0 * 1; simp

lemma base_useBit (g : E) (i : Fin d) (hg : S.base g = bit i) (b : ZMod 2) :
    S.base (useBit g b) = Pi.single i b := by
  rcases (show ∀ z : ZMod 2, z=0 ∨ z=1 by decide) b with rfl|rfl <;>
    simp [useBit,bit,hg]

theorem collected_on (I : Finset (Fin d)) :
    ∃ C : Collected S, ∀ x, S.base (C.sec x) = ∑ i ∈ I, Pi.single i (x i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨S.emptyCollected, fun x => by simp [emptyCollected]⟩
  | insert i I hi ih =>
    obtain ⟨C,hC⟩ := ih
    obtain ⟨g,hg⟩ := S.base_onto (bit i)
    refine ⟨S.adjoin C g i, ?_⟩
    intro x
    change S.base (C.sec x * useBit g (x i)) = _
    rw [S.base_mul, hC, S.base_useBit g i hg, Finset.sum_insert hi, add_comm]

/-- Every central extension of elementary abelian two-groups admits a bilinear
factor set. The section is obtained by multiplying chosen lifts of a basis in order. -/
theorem exists_bilinear_section :
    ∃ (σ : V d → E) (B : V d →+ V d →+ V s),
      (∀ x, S.base (σ x) = x) ∧ (∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y)) := by
  obtain ⟨C,hC⟩ := S.collected_on Finset.univ
  refine ⟨C.sec,C.bil,?_,C.sec_mul⟩
  intro x
  exact (hC x).trans (Finset.univ_sum_single x)

end Erdos1160Growth.LowerTriangularUpper.CentralData

end

/- IntrinsicCounts -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory

namespace CentralData

variable {E : Type*} [Group E] {d s : ℕ} (S : CentralData E d s)

/-- The embedded elementary abelian subgroup is generated by the squares of the group. -/
def SquaresGenerate : Prop :=
  S.incl.range ≤ Subgroup.closure (Set.range (fun z : E => z*z))

theorem square_subgroup_le : Subgroup.closure (Set.range (fun z : E => z*z)) ≤ S.incl.range := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z,rfl⟩
  obtain ⟨w,hw⟩ := S.exists_square z
  exact ⟨Multiplicative.ofAdd w,hw⟩

theorem square_span_top (h : S.SquaresGenerate) :
    Submodule.span (ZMod 2) {w : V s | ∃ z : E, S.liftK w = z*z} = ⊤ := by
  let K := Submodule.span (ZMod 2) {w : V s | ∃ z : E, S.liftK w = z*z}
  let H := (AddSubgroup.toSubgroup K.toAddSubgroup).map S.incl
  have hsq : Subgroup.closure (Set.range (fun z : E => z*z)) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨z,rfl⟩
    obtain ⟨w,hw⟩ := S.exists_square z
    refine ⟨Multiplicative.ofAdd w, ?_,hw⟩
    change w ∈ K
    exact Submodule.subset_span ⟨z,hw⟩
  apply top_unique
  intro w _
  have hw : S.liftK w ∈ H := hsq (h ⟨Multiplicative.ofAdd w,rfl⟩)
  obtain ⟨v,hv,he⟩ := hw
  have he' : v.toAdd = w := congrArg Multiplicative.toAdd (S.incl_inj he)
  exact he' ▸ hv

variable {E : FiniteGrp.{0}}

theorem class_mem_of_section (S : CentralData E d s) (σ : V d → E)
    (B : V d →+ V d →+ V s) (hπ : ∀ x, S.base (σ x) = x)
    (hmul : ∀ x y, σ x * σ y = S.liftK (B x y) * σ (x+y))
    (h : Submodule.span (ZMod 2) {w : V s | ∃ z : E, S.liftK w = z*z} = ⊤) :
    Quotient.mk _ E ∈ bilinearClasses d s := by
  refine ⟨B,?_,?_⟩
  · change Submodule.span (ZMod 2) (Set.range (fun u => B u u)) = ⊤
    rwa [← S.squares_eq_diagonal σ B hπ hmul]
  · apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := GrpCat.of (BilinearExtension B)) (Y := E.toGrp)
        (S.sectionEquiv σ B hπ hmul))⟩

theorem class_mem (S : CentralData E d s) (h : S.SquaresGenerate) :
    Quotient.mk _ E ∈ bilinearClasses d s := by
  obtain ⟨σ,B,hπ,hmul⟩ := S.exists_bilinear_section
  exact S.class_mem_of_section σ B hπ hmul (S.square_span_top h)

end CentralData

/-- Isomorphism classes of central elementary abelian extensions of ranks d and s
whose kernel is generated by the squares in the ambient group. -/
def intrinsicClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | ∃ S : CentralData E d s, S.SquaresGenerate}

theorem intrinsicClasses_subset (d s : ℕ) : intrinsicClasses d s ⊆ bilinearClasses d s := by
  rintro _ ⟨E,⟨S,hS⟩,rfl⟩
  exact S.class_mem hS

theorem intrinsic_gaussian_upper (d s : ℕ) (hs : s ≤ D d) :
    (intrinsicClasses d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      ∏ i : Fin s, (2^(D d)-2^i.val) :=
  (Nat.mul_le_mul_right _ (Set.ncard_le_ncard
    ((intrinsicClasses_subset d s).trans (bilinearClasses_subset d s))
    (classes_finite d s))).trans (gaussian_upper d s hs)

end Erdos1160Growth.LowerTriangularUpper

end

/- SquareCoreCount -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory

def squareCore (E : Type*) [Group E] : Subgroup E :=
  Subgroup.closure (Set.range fun x : E => x*x)

def squareCoreClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | squareCore E ≤ Subgroup.center E ∧
    (∀ x : squareCore E, x*x = 1) ∧ Nat.card (squareCore E) = 2^s ∧
    (squareCore E).index = 2^d}

lemma squareCoreClasses_subset (d s : ℕ) : squareCoreClasses d s ⊆ intrinsicClasses d s := by
  rintro _ ⟨E, ⟨hc,he,hw,hv⟩,rfl⟩
  let K := squareCore E
  let _ : K.Normal :=
    { conj_mem := fun n hn g => by
        have hh := Subgroup.mem_center_iff.mp (hc hn) g
        rwa [hh,mul_inv_cancel_right] }
  have hxq (x : E ⧸ K) : x*x = 1 := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure ⟨a,rfl⟩
  obtain ⟨h⟩ := exist_elementary_coords he hw
  have hv' : Nat.card (E ⧸ K) = 2^d := by rwa [← Subgroup.index_eq_card]
  obtain ⟨q⟩ := exist_elementary_coords hxq hv'
  let S := dataOfSubgroup K hc h q
  refine ⟨E,⟨S,?_⟩,rfl⟩
  rintro x ⟨w,rfl⟩
  exact (h.symm w).property

/-- The subgroup generated by the squares is central and elementary abelian of
order 2^s. The index of that subgroup is 2^d. The count is over abstract
isomorphism classes and makes no choice of a presentation or coordinates. -/
theorem squareCore_gaussian_upper (d s : ℕ) (hs : s ≤ D d) :
    (squareCoreClasses d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      ∏ i : Fin s, (2^(D d)-2^i.val) :=
  (Nat.mul_le_mul_right _ (Set.ncard_le_ncard
    (((squareCoreClasses_subset d s).trans (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s))
    (classes_finite d s))).trans (gaussian_upper d s hs)

end Erdos1160Growth.LowerTriangularUpper

end

/- FrattiniContainment -/
section

namespace Erdos1160Growth.LowerTriangularUpper

private lemma frattini_f2 : frattini (Multiplicative (ZMod 2)) = ⊥ := by
  let _ : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨by
    change (Nat.card (ZMod 2)).Prime
    rw [Nat.card_zmod]
    decide⟩
  apply le_antisymm _ bot_le
  apply frattini_le_coatom
  refine ⟨bot_ne_top, ?_⟩
  intro H h
  exact H.eq_bot_or_eq_top_of_prime_card.resolve_left (ne_of_gt h)

instance squareCore_normal {E : Type*} [Group E] : (squareCore E).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro h _ _ ⟨g,rfl⟩
  apply Subgroup.subset_closure
  exact ⟨h*g*h⁻¹, by group⟩

theorem frattini_le_squareCore {E : Type*} [Group E] [Finite E] : frattini E ≤ squareCore E := by
  let K := squareCore E
  let π := QuotientGroup.mk' K
  have hq (x : E ⧸ K) : x*x=1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨y,rfl⟩)
  have htwo : IsPGroup 2 (E ⧸ K) := fun x => ⟨1, by rw [pow_one,pow_two]; exact hq x⟩
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  obtain ⟨e⟩ := exist_elementary_coords hq hn
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply e.injective
  rw [map_one]
  have heval (i : Fin n) :
      ((e (π x)).toAdd i) = 0 := by
    let f : Multiplicative (V n) →* Multiplicative (ZMod 2) :=
      { toFun := fun v => Multiplicative.ofAdd (v.toAdd i)
        map_mul' := fun _ _ => rfl
        map_one' := rfl }
    have onto_f : Function.Surjective f := fun v => ⟨Multiplicative.ofAdd (fun _ => v.toAdd),rfl⟩
    let ψ := f.comp (e.toMonoidHom.comp π)
    have hφ : Function.Surjective ψ := onto_f.comp (e.surjective.comp (QuotientGroup.mk'_surjective K))
    have hmem := (frattini_le_comap_frattini_of_surjective hφ) hx
    change ψ x ∈ frattini (Multiplicative (ZMod 2)) at hmem
    rw [frattini_f2] at hmem
    exact congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp hmem)
  exact congrArg Multiplicative.ofAdd (funext heval)

end Erdos1160Growth.LowerTriangularUpper

end

/- FrattiniSquare -/
section

namespace Erdos1160Growth.LowerTriangularUpper

theorem coatom_index_prime_pow {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hc : Nat.card G = p^m) (H : Subgroup G) (hH : IsCoatom H) : H.index = p := by
  let hp := (Fact.out : p.Prime)
  have hg : IsPGroup p G := IsPGroup.of_card hc
  obtain ⟨h,hh⟩ := (hg.to_subgroup H).exists_card_eq
  have hlt : h < m := by
    have ht : Nat.card H < Nat.card G := lt_of_le_of_ne (H.card_le_card_group) (fun he => hH.1 (H.eq_top_of_card_eq he))
    rw [hh,hc] at ht
    exact lt_of_not_ge (fun hi => ht.not_ge (Nat.pow_le_pow_right hp.pos hi))
  obtain ⟨J,hJ,hle⟩ := Sylow.exists_subgroup_card_pow_succ (G := G)
    (hc ▸ pow_dvd_pow p (show h+1 ≤ m by omega)) hh
  have hne : H ≠ J := by
    intro he
    rw [← he,hh] at hJ
    exact (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self h)).ne hJ
  have htop := hH.2 J (lt_of_le_of_ne hle hne)
  have heq := H.index_mul_card
  rw [htop,Subgroup.card_top] at hJ
  rw [hJ,hh,pow_succ,Nat.mul_comm (p^h) p] at heq
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp.pos) heq

theorem squares_le_frattini {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G = 2^m) :
    Subgroup.closure (Set.range (fun z : G => z*z)) ≤ frattini G := by
  simp only [frattini,Order.radical,le_iInf_iff]
  intro H hH
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z,rfl⟩
  exact H.mul_self_mem_of_index_two (coatom_index_prime_pow hc H hH) z

end Erdos1160Growth.LowerTriangularUpper

end

/- FrattiniCount -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory

theorem frattini_eq_squareCore {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : Nat.card G = 2^m) : frattini G = squareCore G :=
  le_antisymm frattini_le_squareCore (squares_le_frattini h)

def frattiniClasses (d s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | frattini E ≤ Subgroup.center E ∧
    (∀ x : frattini E, x*x = 1) ∧ Nat.card (frattini E) = 2^s ∧ (frattini E).index = 2^d}

theorem frattiniClasses_subset (d s : ℕ) : frattiniClasses d s ⊆ squareCoreClasses d s := by
  rintro _ ⟨E, h,rfl⟩
  change frattini E ≤ Subgroup.center E ∧ _ at h
  have hcard := (frattini E).index_mul_card
  rw [h.2.2.1, h.2.2.2, ←pow_add] at hcard
  refine ⟨E,?_,rfl⟩
  change squareCore E ≤ Subgroup.center E ∧ _
  rwa [←frattini_eq_squareCore hcard.symm]

/-- Upper bound for the number of isomorphism classes of arbitrary finite groups
whose Frattini subgroup is a central elementary abelian subgroup of order 2^s
and has index 2^d. -/
theorem frattini_gaussian_upper (d s : ℕ) (hs : s ≤ D d) :
    (frattiniClasses d s).ncard * (∏ i : Fin s, (2^s-2^i.val)) ≤
      ∏ i : Fin s, (2^(D d)-2^i.val) := by
  have hfin := (classes_finite d s).subset
    (((squareCoreClasses_subset d s).trans (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s))
  exact (Nat.mul_le_mul_right _ (Set.ncard_le_ncard (frattiniClasses_subset d s) hfin)).trans
    (squareCore_gaussian_upper d s hs)

end Erdos1160Growth.LowerTriangularUpper

end

/- JointOrbit -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory
variable {d s : ℕ}

def diagonalQ (B : V d →+ V d →+ V s) : OrbitUp.Q d s :=
  LinearMap.BilinMap.toQuadraticMap
    (((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom.comp B).toZModLinearMap 2)

def pushB (g : OrbitUp.Change d s) (B : V d →+ V d →+ V s) : V d →+ V d →+ V s where
  toFun x := g.2.toAddMonoidHom.comp ((B (g.1.symm x)).comp g.1.symm.toAddMonoidHom)
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

def pushIso (g : OrbitUp.Change d s) (B : V d →+ V d →+ V s) :
    BilinearExtension B ≃* BilinearExtension (pushB g B) where
  toFun x := ⟨g.1 x.base, g.2 x.fiber⟩
  invFun x := ⟨g.1.symm x.base, g.2.symm x.fiber⟩
  left_inv _ := by apply BilinearExtension.ext <;> simp
  right_inv _ := by apply BilinearExtension.ext <;> simp
  map_mul' x y := by
    apply BilinearExtension.ext
    · exact map_add _ _ _
    · change g.2 (x.fiber+y.fiber+B x.base y.base) =
        g.2 x.fiber + g.2 y.fiber + g.2 (B (g.1.symm (g.1 x.base)) (g.1.symm (g.1 y.base)))
      simp

lemma normalizedArray_eq {B C : V d →+ V d →+ V s} (h : ∀ x, B x x = C x x) :
    lowerArray B + upperArray B = lowerArray C + upperArray C := by
  funext l
  rcases l with ⟨i,j⟩ | i
  · let k : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hk : k < i := j.isLt
    change B (bit i) (bit k) + (if i = k then 0 else B (bit k) (bit i)) =
      C (bit i) (bit k) + (if i = k then 0 else C (bit k) (bit i))
    simp only [if_neg (ne_of_gt hk)]
    have H := h (bit i + bit k)
    simp only [map_add,AddMonoidHom.add_apply] at H
    rw [h (bit i),h (bit k)] at H
    apply add_left_cancel (a := C (bit i) (bit i) + C (bit k) (bit k))
    convert H using 1 <;> abel
  · change B (bit i) (bit i) + (if i=i then 0 else _) =
      C (bit i) (bit i) + (if i=i then 0 else _)
    simpa using h (bit i)

noncomputable def diagonalIso {B C : V d →+ V d →+ V s} (h : ∀ x, B x x = C x x) :
    BilinearExtension B ≃* BilinearExtension C := by
  have he := normalizedArray_eq h
  let e := allBilinear_normal B
  rw [he] at e
  exact e.trans (allBilinear_normal C).symm

lemma classOf_eq_of_orbit {a b : P d s}
    (h : (Quotient.mk'' (diagonalQ (form a)) : OrbitUp.Classes d s) =
      Quotient.mk'' (diagonalQ (form b))) : classOf a = classOf b := by
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  have hdiag (x : V d) : pushB g (form b) x x = form a x x :=
    congrArg (fun q : OrbitUp.Q d s => q x) hg
  let e := (pushIso g (form b)).trans (diagonalIso hdiag)
  symm
  apply Quotient.sound
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := (bundle b).toGrp) (Y := (bundle a).toGrp) e)⟩

theorem classes_le_quadraticOrbits (d s : ℕ) :
    (classes d s).ncard ≤ Nat.card (OrbitUp.Classes d s) := by
  classical
  let rep (c : classes d s) : P d s := c.property.choose
  have hr (c : classes d s) : classOf (rep c) = c.val := c.property.choose_spec.2
  let f (c : classes d s) : OrbitUp.Classes d s := Quotient.mk'' (diagonalQ (form (rep c)))
  have hf : Function.Injective f := by
    intro c e he
    apply Subtype.ext
    rw [←hr c,←hr e]
    exact classOf_eq_of_orbit he
  exact Nat.card_le_card_of_injective f hf

theorem frattini_le_quadraticOrbits (d s : ℕ) :
    (frattiniClasses d s).ncard ≤ Nat.card (OrbitUp.Classes d s) := by
  have h := (((frattiniClasses_subset d s).trans (squareCoreClasses_subset d s)).trans
    (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s)
  exact (Set.ncard_le_ncard h (classes_finite d s)).trans (classes_le_quadraticOrbits d s)

end Erdos1160Growth.LowerTriangularUpper

end

/- FrattiniOrder -/
section

namespace Erdos1160Growth.LowerTriangularUpper

open CategoryTheory

def frattiniOrderClasses (m : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2^m ∧
    frattini G ≤ Subgroup.center G ∧ ∀ x : frattini G, x*x=1}

theorem frattiniClasses_finite (d s : ℕ) : (frattiniClasses d s).Finite :=
  (classes_finite d s).subset ((((frattiniClasses_subset d s).trans (squareCoreClasses_subset d s)).trans
    (intrinsicClasses_subset d s)).trans (bilinearClasses_subset d s))

theorem frattiniOrderClasses_le_sum (m : ℕ) :
    (frattiniOrderClasses m).ncard ≤ ∑ d ∈ Finset.range (m+1), (frattiniClasses d (m-d)).ncard := by
  let F := fun d => frattiniClasses d (m-d)
  let U := ⋃ d ∈ Finset.range (m+1), F d
  have hs : frattiniOrderClasses m ⊆ U := by
    rintro _ ⟨G, ⟨hcard, hc, he⟩, rfl⟩
    have hi := (frattini G).index_mul_card
    rw [hcard] at hi
    obtain ⟨d,hd,hd'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show (frattini G).index ∣ 2^m from ⟨_,hi.symm⟩)
    obtain ⟨s,_,hs'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (frattini G) ∣ 2^m from (dvd_mul_left _ _).trans (dvd_of_eq hi))
    rw [hd',hs',←pow_add] at hi
    have hds : d+s=m := Nat.pow_right_injective (by decide : 1<2) hi
    have hsd : m-d=s := by omega
    apply Set.mem_iUnion_of_mem d
    apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m + 1))
    change Quotient.mk _ G ∈ frattiniClasses d (m-d)
    exact ⟨G, ⟨hc, he, hsd ▸ hs', hd'⟩,rfl⟩
  have hfin : U.Finite := (Finset.range (m+1)).finite_toSet.biUnion (fun i _ => frattiniClasses_finite i _)
  exact (Set.ncard_le_ncard hs hfin).trans ((Finset.range (m+1)).set_ncard_biUnion_le F)

end Erdos1160Growth.LowerTriangularUpper

end

/- CentralFrattiniUpper -/
section

namespace Erdos1160Growth.LowerTriangularUpper

/-- The target's dyadic enumeration bound, including a factor two, holds
unconditionally on all groups with a central elementary abelian Frattini subgroup. -/
theorem central_frattini_upper (m : ℕ) (hm : 10000000 ≤ m) :
    (2*(frattiniOrderClasses m).ncard)^27 * 2^(9*m^2) ≤ 2^(2*m^3) := by
  apply OrbitUp.sum_over_ranks m _ hm _ (frattiniOrderClasses_le_sum m)
  intro d hd
  have he : d+(m-d)=m := by omega
  have h := OrbitUp.all_quadratic_orbits_upper d (m-d) (by omega)
  rw [he] at h
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (frattini_le_quadraticOrbits d (m-d)) 27)).trans h

end Erdos1160Growth.LowerTriangularUpper

end

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1.H1 := by
  apply Filter.eventually_atTop.mpr
  exact ⟨10000000, fun m hm =>
    Erdos1160Growth.LowerTriangularUpper.central_frattini_upper m hm⟩
