import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Abel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
A direct proof of the Higman-type lower bound for the number of groups of
order 2^m, by counting class-two central extensions over the binary field.
The lower bound and its infinite-subsequence corollary use only this count.
-/

/-! Relating the canonical count of group isomorphism classes to finite
multiplication tables modulo simultaneous relabeling of their entries. -/

namespace Erdos1160.Tables

open CategoryTheory

/-- The group isomorphism classes counted by the upstream function. -/
def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}

/-- A labeled multiplication table which is realized by a group law. -/
def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }

instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance

/-- Bundle a labeled table as a finite group. -/
noncomputable abbrev model {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance

/-- Evaluate a product using the multiplication of the specified bundled group. -/
def product (G : FiniteGrp) (a b : G) : G := a * b

theorem model_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    product (model t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b

/-- The isomorphism class of a labeled table. -/
noncomputable def groupClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (model t)

/-- A multiplication-preserving bijection gives an isomorphism in the category
of finite groups. -/
theorem iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (product G a b) = product H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩

/-- Every group of order n can be labeled with the elements of Fin n. -/
theorem range_groupClass (n : ℕ) : Set.range (@groupClass n) = orderClasses n := by
  ext c
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨model t, Nat.card_fin n, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : GroupTable n := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul t a b)).trans (e.apply_symm_apply (e a * e b))

theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _

end Erdos1160.Tables

/-!
Counting abstract groups using marked presentations. A finite family may
contain several isomorphic groups. If an isomorphism preserving all marks
determines the parameter, each class has at most as many parameters as
there are ordered tuples of marks in one representative.
-/

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- Count by the fibers of a map between finite types. -/
theorem card_le_of_fiber_bound {A B : Type*} [Finite A] [Finite B] (f : A → B)
    (M : ℕ) (h : ∀ b : B, Nat.card {a : A // f a = b} ≤ M) :
    Nat.card A ≤ Nat.card B * M := by
  classical
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * M := by simp [Nat.card_eq_fintype_card]

end Erdos1160.PresentationCount

namespace Erdos1160.PresentationCount

open CategoryTheory

/-- If comparisons with one fixed representative have finite codes, and a
code determines the source parameter, the number of isomorphic parameters
in each class is at most the size of the code space. -/
theorem card_le_of_relative_codes {A C : Type*} [Finite A] [Finite C] {n : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (code : ∀ a b : A, (X a ≃* X b) → C)
    (sep : ∀ (a b r : A) (e : X a ≃* X r) (f : X b ≃* X r),
      code a r e = code b r f → a = b) :
    Nat.card A ≤ Erdos1160.g n * Nat.card C := by
  classical
  let classOf (a : A) : Tables.orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (Tables.orderClasses n) := (Tables.orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound classOf (Nat.card C)
  intro c
  let F := {a : A // classOf a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) : C := code a.val r.val (transport a)
    exact Nat.card_le_card_of_injective encode (fun {a b} h =>
      Subtype.ext (sep a.val b.val r.val (transport a) (transport b) h))
  · have empty : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ Nat.card C
    simp

end Erdos1160.PresentationCount

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (hb : x.base = y.base) (hf : x.fiber = y.fiber) : x = y := by
  cases x
  cases y
  simp_all

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

end BilinearExtension

end Erdos1160Growth

namespace Erdos1160Growth.BilinearExtension

open scoped commutatorElement

private theorem double_zero {s : ℕ} (w : Fin s → ZMod 2) : w+w = 0 := by
  funext i
  have h : ∀ z : ZMod 2, z+z = 0 := by decide
  exact h (w i)

theorem lift_square_eq_of_base_eq {V : Type*} [AddCommGroup V] {s : ℕ}
    {B : V →+ V →+ (Fin s → ZMod 2)} {a b : BilinearExtension B} (h : a.base = b.base) :
    a * a = b * b := by
  apply BilinearExtension.ext
  · simp only [mul_base, h]
  · simp only [mul_fiber, double_zero, zero_add, h]

theorem lift_commutator_eq_of_base_eq {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {B : V →+ V →+ W} {a b c d : BilinearExtension B}
    (hac : a.base = c.base) (hbd : b.base = d.base) :
    ⁅a,b⁆ = ⁅c,d⁆ := by
  rw [commutator_formula, commutator_formula, hac, hbd]

end Erdos1160Growth.BilinearExtension

open scoped BigOperators commutatorElement

namespace Erdos1160Growth.SharpFamily

abbrev V (d : ℕ) := Fin d → ZMod 2
abbrev Slot (d s : ℕ) := (Σ i : Fin d, Fin i.val) ⊕ Fin (d-s)
abbrev Param (d s : ℕ) := Slot d s → V s

variable {d s : ℕ}

def basis {k : ℕ} (i : Fin k) : V k := Pi.single i 1

def entry (t : Param d s) (i j : Fin d) : V s :=
  if h : j < i then t (.inl ⟨i, ⟨j.val,h⟩⟩)
  else if i = j then
    if hl : i.val < s then basis ⟨i.val, hl⟩
    else t (.inr ⟨i.val - s, by have := i.isLt; omega⟩)
  else 0

theorem entry_fixed {t : Param d s} (i : Fin s) (hs : s ≤ d) :
    entry t (Fin.castLE hs i) (Fin.castLE hs i) = basis i := by
  simp [entry, i.isLt]

theorem entry_upper {t : Param d s} {i j : Fin d} (h : i < j) : entry t i j = 0 := by
  simp [entry, not_lt_of_ge (le_of_lt h), ne_of_lt h]

theorem entry_injective {t u : Param d s} (h : ∀ i j, entry t i j = entry u i j) : t = u := by
  funext k
  rcases k with ⟨i,j⟩ | k
  · let j' : Fin d := ⟨j.val, j.isLt.trans i.isLt⟩
    have hj : j' < i := j.isLt
    simpa [entry,hj,j'] using h i j'
  · have hk : s + k.val < d := by have := k.isLt; omega
    let i : Fin d := ⟨s + k.val, hk⟩
    have hi : ¬ i.val < s := by simp [i]
    simpa [entry,hi,i] using h i i

def form (t : Param d s) : V d →+ V d →+ V s where
  toFun a :=
    { toFun := fun b k => ∑ i, ∑ j, a i * b j * entry t i j k
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

abbrev G (t : Param d s) := BilinearExtension (form t)

def gen (t : Param d s) (i : Fin d) : G t := ⟨basis i, 0⟩
def Z (t : Param d s) (z : V s) : G t := ⟨0, z⟩

lemma eval_basis (t : Param d s) (i j : Fin d) :
    form t (basis i) (basis j) = entry t i j := by
  funext k
  change (∑ a, ∑ b, basis i a * basis j b * entry t a b k) = _
  simp [basis, Pi.single_apply, ite_mul, mul_ite, Finset.sum_ite_eq']

theorem double_zero {k : ℕ} (v : V k) : v + v = 0 := by
  funext j
  exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)

theorem gen_sq (t : Param d s) (i : Fin d) : gen t i * gen t i = Z t (entry t i i) := by
  apply BilinearExtension.ext
  · exact double_zero (basis i)
  · change 0 + 0 + form t (basis i) (basis i) = entry t i i
    rw [zero_add, zero_add, eval_basis]

theorem gen_comm (t : Param d s) (i j : Fin d) (h : j < i) :
    ⁅gen t i, gen t j⁆ = Z t (entry t i j) := by
  rw [BilinearExtension.commutator_formula]
  apply BilinearExtension.ext
  · rfl
  · change form t (basis i) (basis j) - form t (basis j) (basis i) = _
    rw [eval_basis, eval_basis, entry_upper h, sub_zero]
    rfl

theorem Z_injective (t : Param d s) : Function.Injective (Z t) :=
  fun _ _ h => congrArg BilinearExtension.fiber h

theorem Z_add (t : Param d s) (u v : V s) : Z t (u + v) = Z t u * Z t v := by
  apply BilinearExtension.ext <;> simp [Z]

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

open scoped commutatorElement

variable {d s : ℕ}

/-- Two homomorphisms from different presentations that agree on all coordinate fibers
agree on every element of the common central vector space. -/
theorem map_Z_agree {R : Type*} [Group R] {t u : Param d s}
    (e : G t →* R) (f : G u →* R)
    (h : ∀ i : Fin s, e (Z t (basis i)) = f (Z u (basis i))) (w : V s) :
    e (Z t w) = f (Z u w) := by
  have hz : e (Z t 0) = f (Z u 0) := e.map_one.trans f.map_one.symm
  induction w using Pi.single_induction with
  | zero => exact hz
  | add a b ha hb => rw [Z_add, Z_add, map_mul, map_mul, ha, hb]
  | single i x =>
    have bit : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases bit x with rfl | rfl
    · simpa only [Pi.single_zero] using hz
    · exact h i

/-- Projecting the images of the d generators into the elementary abelian quotient
gives a complete code for presentations mapping isomorphically into one fixed target. -/
theorem recover_of_equal_base (hs : s ≤ d) (t u r : Param d s)
    (e : G t ≃* G r) (f : G u ≃* G r)
    (h : ∀ i : Fin d, (e (gen t i)).base = (f (gen u i)).base) : t = u := by
  have hsquare (i : Fin d) : e (Z t (entry t i i)) = f (Z u (entry u i i)) := by
    rw [← gen_sq, ← gen_sq, map_mul, map_mul]
    exact BilinearExtension.lift_square_eq_of_base_eq (h i)
  have hfix (i : Fin s) : e (Z t (basis i)) = f (Z u (basis i)) := by
    simpa only [entry_fixed i hs] using hsquare (Fin.castLE hs i)
  have recover {v w : V s} (hv : e (Z t v) = f (Z u w)) : v = w := by
    have hsame := map_Z_agree e.toMonoidHom f.toMonoidHom hfix v
    exact Z_injective u (f.injective (hsame.symm.trans hv))
  apply entry_injective
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [entry_upper hij, entry_upper hij]
  · exact recover (hsquare i)
  · apply recover
    rw [← gen_comm t i j hji, ← gen_comm u i j hji, map_commutatorElement, map_commutatorElement]
    exact BilinearExtension.lift_commutator_eq_of_base_eq (h i) (h j)

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

private instance {d s : ℕ} (t : Param d s) : Finite (G t) :=
  Finite.of_equiv _ (BilinearExtension.coordinateEquiv (form t)).symm

private def bundled {d s : ℕ} (t : Param d s) : FiniteGrp.{0} := FiniteGrp.of (G t)

private theorem bundled_order {d s : ℕ} (t : Param d s) : Nat.card (bundled t) = 2 ^ (d+s) := by
  change Nat.card (BilinearExtension (form t)) = _
  rw [BilinearExtension.card]
  simp only [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_add]

theorem parameter_card {d s : ℕ} (hs : s ≤ d) :
    Nat.card (Param d s) = 2 ^ (s * (d * (d - 1) / 2 + d - s)) := by
  change Nat.card (Slot d s → Fin s → ZMod 2) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul]
  unfold Slot
  rw [Nat.card_sum, triangular_card, Nat.card_fin]
  have h : d * (d - 1) / 2 + (d - s) = d * (d - 1) / 2 + d - s := by omega
  rw [h]

/-- Lower bound from the explicit family with s diagonal squares fixed to a
fiber basis. A comparison with a representative needs only d base vectors
of d bits each. -/
theorem sharp_parameter_lower {d s : ℕ} (hs : s ≤ d) :
    2 ^ (s * (d * (d - 1) / 2 + d - s)) ≤
      Erdos1160.g (2 ^ (d+s)) * 2 ^ (d*d) := by
  let code (a r : Param d s) (e : bundled a ≃* bundled r) (i : Fin d) : V d :=
    (e (gen a i) : G r).base
  have sep (a b r : Param d s) (e : bundled a ≃* bundled r) (f : bundled b ≃* bundled r)
      (h : code a r e = code b r f) : a = b :=
    recover_of_equal_base hs a b r e f (congrFun h)
  have h := Erdos1160.PresentationCount.card_le_of_relative_codes bundled bundled_order code sep
  rw [parameter_card hs] at h
  change _ ≤ _ * Nat.card (Fin d → Fin d → ZMod 2) at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] using h

end Erdos1160Growth.SharpFamily

namespace Erdos1160Growth.SharpFamily

private theorem converted_bound (m d s : ℕ) (hs : s ≤ d) (horder : d+s=m)
    (hexp : 2*m^3 + (d*d)*27 ≤ (s*(d*(d-1)/2+d-s))*27 + 12*m^2) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  have count := Nat.pow_le_pow_left (sharp_parameter_lower hs) 27
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, horder] at count
  apply Nat.le_of_mul_le_mul_right (c := 2^((d*d)*27)) _ (Nat.pow_pos (by decide))
  calc
    2^(2*m^3) * 2^((d*d)*27) = 2^(2*m^3+(d*d)*27) := (pow_add _ _ _).symm
    _ ≤ 2^((s*(d*(d-1)/2+d-s))*27+12*m^2) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := pow_add _ _ _
    _ ≤ (Erdos1160.g (2^m)^27 * 2^((d*d)*27)) * 2^(12*m^2) :=
      Nat.mul_le_mul_right _ count
    _ = _ := Nat.mul_right_comm _ _ _

private theorem triangle_even (u : ℕ) :
    (2*u)*(2*u-1)/2 = u*(2*u-1) := by
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]

private theorem triangle_odd (u : ℕ) :
    (2*u+1)*(2*u+1-1)/2 = (2*u+1)*u := by
  have h : 2*u+1-1 = 2*u := by omega
  rw [h, show (2*u+1)*(2*u) = (2*u+1)*u*2 by ring, Nat.mul_div_cancel _ (by decide)]

/-- The sharp cubic and quadratic terms of Higman's lower bound, with all denominators
cleared and a single estimate valid in each of the three residue classes. -/
theorem higman_lower_all (m : ℕ) (hm : 3 ≤ m) :
    2^(2*m^3) ≤ Erdos1160.g (2^m)^27 * 2^(12*m^2) := by
  let k := m/3-1
  have cases_m : m=3*(k+1) ∨ m=3*(k+1)+1 ∨ m=3*(k+1)+2 := by
    dsimp [k]
    omega
  have even_pred : 2*(k+1)-1 = 2*k+1 := by omega
  rcases cases_m with h | h | h
  · apply converted_bound m (2*(k+1)) (k+1) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+1) = (k+1)*(2*k+1)+(k+1) := by omega
    rw [sub_id]
    exact le_of_eq (by ring)
  · apply converted_bound m (2*(k+1)) (k+2) (by omega) (by omega)
    rw [h, triangle_even, even_pred]
    have sub_id : (k+1)*(2*k+1)+2*(k+1)-(k+2) = (k+1)*(2*k+1)+k := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 27*k+10)
    ring
  · apply converted_bound m (2*(k+1)+1) (k+2) (by omega) (by omega)
    rw [h, triangle_odd]
    have sub_id : (2*(k+1)+1)*(k+1)+(2*(k+1)+1)-(k+2) =
        (2*(k+1)+1)*(k+1)+(k+1) := by omega
    rw [sub_id]
    apply Nat.le.intro (k := 18*k+23)
    ring

end Erdos1160Growth.SharpFamily

namespace Erdos1160.Growth

open Filter

/-- A lower bound with the optimal cubic coefficient forces the logarithm
of the adjacent growth factor to attain the predicted quadratic leading
coefficient on an infinite subsequence. -/
theorem frequently_sharp_jump_of_lower (a : ℕ → ℕ)
    (hl : ∀ᶠ m : ℕ in atTop, 2^(2*m^3) ≤ a m^27 * 2^(13*m^2)) :
    ∃ᶠ m : ℕ in atTop, 2^(2*m^2/9-m)*a m < a (m+1) := by
  by_contra hf
  obtain ⟨N₀,hN⟩ := eventually_atTop.mp (Filter.not_frequently.mp hf)
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp hl
  let N := max (max N₀ N₁) 5
  let B := 27*a N+14*N^2
  have hN₀ : N₀ ≤ N := by dsimp [N]; omega
  have hN₁ : N₁ ≤ N := by dsimp [N]; omega
  have h5 : 5 ≤ N := by dsimp [N]; omega
  have hu (t : ℕ) : a (N+t)^27 * 2^(14*(N+t)^2) ≤ 2^(B+2*(N+t)^3) := by
    induction t with
    | zero =>
      simp only [Nat.add_zero]
      calc
        a N^27 * 2^(14*N^2) ≤ (2^(a N))^27 * 2^(14*N^2) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _) le_rfl
        _ = 2^B := by rw [← pow_mul, ← pow_add]; congr 1; dsimp [B]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    | succ t ih =>
      let m := N+t
      let r := 2*m^2/9-m
      have hm : 5 ≤ m := by dsimp [m]; omega
      have hmul := Nat.mul_le_mul_right m hm
      have hdiv : m ≤ 2*m^2/9 :=
        (Nat.le_div_iff_mul_le (by decide)).2 (by nlinarith only [hmul, Nat.zero_le m])
      have hr : 9*(r+m) ≤ 2*m^2 := by dsimp [r]; omega
      have he : r*27+14*(m+1)^2+(B+2*m^3) ≤ B+2*(m+1)^3+14*m^2 := by
        nlinarith only [hr,hm]
      have step : a (m+1) ≤ 2^r*a m := le_of_not_gt (hN m (by dsimp [m]; omega))
      apply Nat.le_of_mul_le_mul_right (c := 2^(14*m^2)) _ (Nat.pow_pos (by decide))
      calc
        a (m+1)^27 * 2^(14*(m+1)^2) * 2^(14*m^2)
            ≤ (2^r * a m)^27 * 2^(14*(m+1)^2) * 2^(14*m^2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left step _))
        _ = (2^(r*27) * 2^(14*(m+1)^2)) * (a m^27 * 2^(14*m^2)) := by
          rw [mul_pow, pow_mul (2:ℕ) r 27]
          ring
        _ ≤ (2^(r*27) * 2^(14*(m+1)^2)) * 2^(B+2*m^3) := Nat.mul_le_mul_left _ ih
        _ = 2^(r*27+14*(m+1)^2+(B+2*m^3)) := by rw [← pow_add, ← pow_add]
        _ ≤ 2^(B+2*(m+1)^3+14*m^2) := Nat.pow_le_pow_right (by decide) he
        _ = 2^(B+2*(m+1)^3) * 2^(14*m^2) := pow_add .. 
  let m := N+(B+1)
  have hlo := h₁ m (by dsimp [m]; omega)
  have hpow : 2^(2*m^3+m^2) ≤ 2^(B+2*m^3) := calc
    _ = 2^(2*m^3)*2^(m^2) := pow_add ..
    _ ≤ (a m^27 * 2^(13*m^2)) * 2^(m^2) := Nat.mul_le_mul_right _ hlo
    _ = a m^27 * 2^(14*m^2) := by rw [Nat.mul_assoc, ← pow_add]; congr 2; omega
    _ ≤ _ := hu (B+1)
  have he := (Nat.pow_le_pow_iff_right (a := 2) (by decide)).1 hpow
  have hmB : B < m := by dsimp [m]; omega
  have hbig := Nat.mul_le_mul_right m (show 1 ≤ m by omega)
  nlinarith only [he,hmB,hbig]

end Erdos1160.Growth

namespace Erdos1160.Growth

open Filter

theorem adjacent_growth_lower : ∀ᶠ m : ℕ in atTop,
    2^(2*m^3) ≤ g (2^m)^27 * 2^(13*m^2) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨3, fun m hm => ?_⟩
  apply (Erdos1160Growth.SharpFamily.higman_lower_all m hm).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- Infinitely often the adjacent growth factor exceeds an explicit
quadratic exponential, with leading coefficient 2/9 in its exponent. -/
theorem frequently_sharp_jump_two_power :
    ∃ᶠ m : ℕ in atTop, 2^(2*m^2/9-m)*g (2^m) < g (2^(m+1)) :=
  frequently_sharp_jump_of_lower (fun m => g (2^m)) adjacent_growth_lower

end Erdos1160.Growth

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1.H1 := by
  exact Erdos1160.Growth.adjacent_growth_lower
