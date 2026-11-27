import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Abel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Set.Card.Arithmetic

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

/-- Equality of the isomorphism classes is exactly simultaneous relabeling
of the two input positions and the output by one permutation. -/
theorem groupClass_eq_iff {n : ℕ} (s t : GroupTable n) :
    groupClass s = groupClass t ↔
      ∃ e : Equiv.Perm (Fin n), ∀ a b, e (s.val a b) = t.val (e a) (e b) := by
  constructor
  · intro h
    obtain ⟨i⟩ := Quotient.exact h
    let e := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    refine ⟨e.toEquiv, fun a b => ?_⟩
    have hmul (a b : model s) :
        e (product (model s) a b) = product (model t) (e a) (e b) := e.map_mul a b
    exact (congrArg (fun z => e z) (model_mul s a b)).symm.trans
      ((hmul a b).trans (model_mul t (e a) (e b)))
  · rintro ⟨e,h⟩
    apply Quotient.sound
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul s a b)).trans
      ((h a b).trans (model_mul t (e a) (e b)).symm)

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

/-- The kernel relation has the explicit relabeling description in
`groupClass_eq_iff`. -/
noncomputable def relabelSetoid (n : ℕ) : Setoid (GroupTable n) :=
  Setoid.ker (@groupClass n)

/-- Group isomorphism classes of order n are in bijection with group
multiplication tables on n labels up to relabeling. -/
noncomputable def tablesEquivClasses (n : ℕ) :
    Quotient (relabelSetoid n) ≃ orderClasses n :=
  (Setoid.quotientKerEquivRange (@groupClass n)).trans (Equiv.setCongr (range_groupClass n))

theorem g_eq_card_tables (n : ℕ) : Erdos1160.g n = Nat.card (Quotient (relabelSetoid n)) :=
  (Nat.card_congr (tablesEquivClasses n)).symm

/-- A coarse upper bound obtained by ignoring the group axioms and counting all
binary operations on the labeled carrier. -/
theorem g_le_table_count (n : ℕ) : Erdos1160.g n ≤ n ^ (n * n) := by
  rw [g_eq_card_tables]
  calc
    Nat.card (Quotient (relabelSetoid n)) ≤ Nat.card (GroupTable n) :=
      Nat.card_le_card_of_surjective _ Quotient.mk_surjective
    _ ≤ Nat.card (Fin n → Fin n → Fin n) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = n ^ (n * n) := by rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, pow_mul]

theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _

theorem g_pos {n : ℕ} (hn : 0 < n) : 0 < Erdos1160.g n := by
  let : NeZero n := ⟨hn.ne'⟩
  let G := @FiniteGrp.of (Multiplicative (Fin n)) inferInstance (inferInstanceAs (Finite (Fin n)))
  change 0 < (orderClasses n).ncard
  exact ((Set.ncard_pos (orderClasses_finite n)).2
    ⟨Quotient.mk _ G, G, Nat.card_fin n, rfl⟩)

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

/-- An isomorphism preserving all the marked elements distinguishes parameter
values. Forgetting the k marks can identify at most n^k parameters per class. -/
theorem card_le_of_marked_family {A : Type*} [Finite A] {n k : ℕ}
    (X : A → FiniteGrp.{0}) (hN : ∀ a, Nat.card (X a) = n)
    (mark : (a : A) → Fin k → X a)
    (sep : ∀ (a b : A) (e : X a ≃* X b),
      (∀ i, e (mark a i) = mark b i) → a = b) :
    Nat.card A ≤ Erdos1160.g n * n ^ k := by
  classical
  let f (a : A) : Tables.orderClasses n := ⟨Quotient.mk _ (X a), X a, hN a, rfl⟩
  let : Finite (Tables.orderClasses n) := (Tables.orderClasses_finite n).to_subtype
  apply card_le_of_fiber_bound f (n ^ k)
  intro c
  let F := {a : A // f a = c}
  by_cases hn : Nonempty F
  · let r := Classical.choice hn
    have sameClass (a : F) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (X a.val)
        = Quotient.mk _ (X r.val) :=
      congrArg Subtype.val (a.property.trans r.property.symm)
    let transport (a : F) : X a.val ≃* X r.val :=
      ((inducedFunctor FiniteGrp.toGrp).mapIso
        (Classical.choice (Quotient.exact (sameClass a)))).groupIsoToMulEquiv
    let encode (a : F) (i : Fin k) : X r.val := transport a (mark a.val i)
    have uniqueCode : Function.Injective encode := by
      intro a b he
      apply Subtype.ext
      apply sep a.val b.val ((transport a).trans (transport b).symm)
      intro i
      apply (transport b).injective
      change transport b ((transport b).symm (transport a (mark a.val i))) =
        transport b (mark b.val i)
      rw [MulEquiv.apply_symm_apply]
      exact congrFun he i
    calc
      Nat.card F ≤ Nat.card (Fin k → X r.val) :=
        Nat.card_le_card_of_injective encode uniqueCode
      _ = n ^ k := by rw [Nat.card_fun, hN, Nat.card_fin]
  · have empty : IsEmpty F := not_nonempty_iff.mp hn
    change Nat.card F ≤ n ^ k
    simp

end Erdos1160.PresentationCount

namespace Erdos1160.Cancellation

abbrev C₂ := Multiplicative (Fin 2)

lemma c2_square (x : C₂) : x*x=1 := by
  have h : ∀ t : C₂, t * t = 1 := by decide
  exact h x

lemma endo_dichotomy (f : C₂ →* C₂) : (∀ x, f x = x) ∨ (∀ x, f x = 1) := by
  let t : C₂ := Multiplicative.ofAdd 1
  have exhaust : ∀ x : C₂, x = 1 ∨ x = t := by decide
  rcases exhaust (f t) with ht | ht
  · right
    intro x
    rcases exhaust x with rfl | rfl
    · exact map_one _
    · exact ht
  · left
    intro x
    rcases exhaust x with rfl | rfl
    · exact map_one _
    · exact ht

lemma mul_middle {K : Type*} [Group K] {x y u v : K} (h : Commute y u) :
    (x*y)*(u*v) = (x*u)*(y*v) := by
  calc
    _ = x * ((y*u)*v) := by simp [mul_assoc]
    _ = x * ((u*y)*v) := by rw [h.eq]
    _ = _ := by simp [mul_assoc]

def pairMul {A K : Type*} [Group A] [Group K] (f g : A →* K)
    (hc : ∀ x y, Commute (g x) (f y)) : A →* K where
  toFun x := f x * g x
  map_one' := by simp
  map_mul' x y := by simpa only [map_mul] using (mul_middle (x := f x) (v := g y) (hc x y)).symm

lemma common_section {K : Type*} [Group K] (p q : K →* C₂) (s t : C₂ →* K)
    (hs : ∀ x, p (s x) = x) (ht : ∀ x, q (t x) = x)
    (sc : ∀ x k, Commute (s x) k) (tc : ∀ x k, Commute (t x) k) :
    ∃ u : C₂ →* K, (∀ x, p (u x) = x) ∧ (∀ x, q (u x) = x) ∧ (∀ x k, Commute (u x) k) := by
  rcases endo_dichotomy (q.comp s) with h | h
  · exact ⟨s,hs,h,sc⟩
  rcases endo_dichotomy (p.comp t) with j | j
  · exact ⟨t,j,ht,tc⟩
  refine ⟨pairMul s t (fun x y => tc x (s y)), ?_, ?_, ?_⟩
  · intro x
    change p (s x * t x) = x
    have htx : p (t x) = 1 := j x
    simp [hs, htx]
  · intro x
    change q (s x * t x) = x
    have hsx : q (s x) = 1 := h x
    simp [ht, hsx]
  · intro x k
    exact (sc x k).mul_left (tc x k)

def project {K : Type*} [Group K] (p : K →* C₂) (s : C₂ →* K)
    (sc : ∀ x k, Commute (s x) k) : K →* K :=
  pairMul (MonoidHom.id K) (s.comp p) (fun x y => sc (p x) y)

lemma project_mem {K : Type*} [Group K] (p : K →* C₂) (s : C₂ →* K)
    (hs : ∀ x, p (s x) = x) (sc : ∀ x k, Commute (s x) k) (x : K) :
    project p s sc x ∈ p.ker := by
  change p (x * s (p x)) = 1
  rw [map_mul, hs, c2_square]

lemma project_roundtrip {K : Type*} [Group K] (p q : K →* C₂) (s : C₂ →* K)
    (hp : ∀ x, p (s x) = x) (sc : ∀ x k, Commute (s x) k) (x : K) (hx : p x = 1) :
    project p s sc (project q s sc x) = x := by
  change (x * s (q x)) * s (p (x * s (q x))) = x
  rw [map_mul, hx, one_mul, hp, mul_assoc, ← map_mul, c2_square, map_one, mul_one]

def kernelEquiv {K : Type*} [Group K] (p q : K →* C₂) (s : C₂ →* K)
    (hp : ∀ x, p (s x) = x) (hq : ∀ x, q (s x) = x) (sc : ∀ x k, Commute (s x) k) :
    p.ker ≃* q.ker where
  toFun x := ⟨project q s sc x, project_mem q s hq sc x⟩
  invFun y := ⟨project p s sc y, project_mem p s hp sc y⟩
  left_inv x := Subtype.ext (project_roundtrip p q s hp sc x x.property)
  right_inv y := Subtype.ext (project_roundtrip q p s hq sc y y.property)
  map_mul' x y := Subtype.ext (map_mul (project q s sc) x.val y.val)

def factorKernel {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) :
    H ≃* ((MonoidHom.snd H C₂).comp e.toMonoidHom).ker where
  toFun h := ⟨e.symm (h,1), by change (e (e.symm (h,1))).2 = 1; simp⟩
  invFun x := (e x.val).1
  left_inv h := by simp
  right_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext rfl x.property.symm
  map_mul' h k := by
    apply Subtype.ext
    exact map_mul e.symm (h,1) (k,1)

def sectionOfEquiv {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) : C₂ →* K :=
  e.symm.toMonoidHom.comp (MonoidHom.inr H C₂)

lemma sectionOfEquiv_right {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) (z : C₂) :
    ((MonoidHom.snd H C₂).comp e.toMonoidHom) (sectionOfEquiv e z) = z := by
  change (e (e.symm (1,z))).2 = z
  simp

lemma sectionOfEquiv_central {K H : Type*} [Group K] [Group H] (e : K ≃* H × C₂) (z : C₂) (k : K) :
    Commute (sectionOfEquiv e z) k := by
  apply e.injective
  change e (e.symm (1,z) * k) = e (k * e.symm (1,z))
  simp only [map_mul, e.apply_symm_apply]
  apply Prod.ext
  · simp
  · simp [mul_comm]

theorem c2_cancel {G H : Type*} [Group G] [Group H] (e : G × C₂ ≃* H × C₂) :
    Nonempty (G ≃* H) := by
  let i := MulEquiv.refl (G × C₂)
  let p := (MonoidHom.snd G C₂).comp i.toMonoidHom
  let q := (MonoidHom.snd H C₂).comp e.toMonoidHom
  obtain ⟨s,hp,hq,hc⟩ := common_section p q (sectionOfEquiv i) (sectionOfEquiv e)
    (sectionOfEquiv_right i) (sectionOfEquiv_right e)
    (sectionOfEquiv_central i) (sectionOfEquiv_central e)
  exact ⟨((factorKernel i).trans (kernelEquiv p q s hp hq hc)).trans (factorKernel e).symm⟩

end Erdos1160.Cancellation

namespace Erdos1160.Cancellation

open CategoryTheory
open Erdos1160.Tables

abbrev GroupClass := Quotient (isIsomorphicSetoid FiniteGrp.{0})

def withC2 (G : FiniteGrp.{0}) : FiniteGrp.{0} := FiniteGrp.of (G × C₂)

def doubleClass : GroupClass → GroupClass :=
  Quotient.map withC2 (by
    rintro G H ⟨i⟩
    let e : G ≃* H := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    let f : withC2 G ≃* withC2 H := e.prodCongr (MulEquiv.refl C₂)
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩)

lemma doubleClass_mk (G : FiniteGrp.{0}) :
    doubleClass (Quotient.mk _ G) = Quotient.mk _ (withC2 G) := rfl

lemma doubleClass_injective : Function.Injective doubleClass := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ G H =>
    intro h
    obtain ⟨i⟩ := Quotient.exact (show Quotient.mk _ (withC2 G) = Quotient.mk _ (withC2 H) from h)
    let f : G × C₂ ≃* H × C₂ := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv
    obtain ⟨e⟩ := c2_cancel f
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩

lemma doubleClass_maps (n : ℕ) : Set.MapsTo doubleClass (orderClasses n) (orderClasses (n * 2)) := by
  rintro _ ⟨G,hG,rfl⟩
  refine ⟨withC2 G, ?_, rfl⟩
  change Nat.card (G × C₂) = n * 2
  rw [Nat.card_prod, show Nat.card G = n from hG]
  exact congrArg (n * ·) (Nat.card_fin 2)

lemma mem_doubleClass_image_iff (n : ℕ) (y : GroupClass) :
    y ∈ doubleClass '' orderClasses n ↔ ∃ G : FiniteGrp.{0}, Nat.card G = n ∧
      Quotient.mk _ (withC2 G) = y := by
  constructor
  · rintro ⟨_, ⟨G,hG,rfl⟩, h⟩
    exact ⟨G,hG,h⟩
  · rintro ⟨G,hG,rfl⟩
    exact ⟨Quotient.mk _ G, ⟨G,hG,rfl⟩, rfl⟩

lemma ncard_doubleClass_image (n : ℕ) : (doubleClass '' orderClasses n).ncard = g n :=
  (Set.injOn_of_injective doubleClass_injective).ncard_image

theorem g_le_g_double (n : ℕ) : g n ≤ g (n * 2) :=
  Set.ncard_le_ncard_of_injOn doubleClass (doubleClass_maps n)
    (Set.injOn_of_injective doubleClass_injective) (orderClasses_finite _)

theorem g_two_pow_mono (m : ℕ) : g (2 ^ m) ≤ g (2 ^ (m + 1)) := by
  simpa only [pow_succ] using g_le_g_double (2 ^ m)

end Erdos1160.Cancellation

namespace Erdos1160Growth

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- The central extension built from an arbitrary biadditive map, with two visible coordinates. -/
structure BilinearExtension (B : V →+ V →+ W) where
  base : V
  fiber : W

namespace BilinearExtension

variable {B : V →+ V →+ W}

theorem ext {x y : BilinearExtension B} (h₁ : x.base = y.base) (h₂ : x.fiber = y.fiber) : x = y := by
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

end BilinearExtension

end Erdos1160Growth

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

namespace Erdos1160Growth.TensorFamily

open scoped commutatorElement

variable {d : ℕ}

private def mark (t : T d) : Fin d ⊕ Fin d ⊕ Fin d → G t :=
  Sum.elim (fun i => X t (basis i)) <|
    Sum.elim (fun i => Y t (basis i)) (fun i => Z t (basis i))

private theorem mark_separates (s t : T d) (e : G s ≃* G t)
    (h : ∀ i, e (mark s i) = mark t i) : s = t := by
  have hx (i : Fin d) : e (X s (basis i)) = X t (basis i) := h (.inl i)
  have hy (i : Fin d) : e (Y s (basis i)) = Y t (basis i) := h (.inr (.inl i))
  have hz (i : Fin d) : e (Z s (basis i)) = Z t (basis i) := h (.inr (.inr i))
  funext i j
  have hcomm := map_commutatorElement e (Y s (basis i)) (X s (basis j))
  rw [commutator_YX, hx, hy, commutator_YX] at hcomm
  rw [← e.coe_toMonoidHom, map_Z_of_basis e.toMonoidHom hz] at hcomm
  exact congrArg BilinearExtension.fiber hcomm

private noncomputable def markIndex (d : ℕ) : (Fin d ⊕ Fin d ⊕ Fin d) ≃ Fin (3*d) :=
  Fintype.equivFinOfCardEq (by simp; omega)

private instance (t : T d) : Finite (G t) :=
  Finite.of_equiv _ (BilinearExtension.coordinateEquiv (form t)).symm

private def groupObject (t : T d) : FiniteGrp.{0} := FiniteGrp.of (G t)

private theorem groupObject_order (t : T d) : Nat.card (groupObject t) = 2^(3*d) := by
  change Nat.card (BilinearExtension (form t)) = _
  rw [BilinearExtension.card, Nat.card_prod]
  simp only [V, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- Independent binary commutator tables give a coarse cubic lower bound for the number
of groups of order 2^(3d), even after discarding the 3d marked elements. -/
theorem cubic_parameter_lower (d : ℕ) :
    2^(d^3) ≤ Erdos1160.g (2^(3*d)) * 2^(9*d^2) := by
  have hc := Erdos1160.PresentationCount.card_le_of_marked_family
    (n := 2^(3*d)) (k := 3*d) (groupObject (d := d)) groupObject_order
    (fun t i => mark t ((markIndex d).symm i)) (by
      intro s t e he
      change G s ≃* G t at e
      change ∀ i, e (mark s ((markIndex d).symm i)) = mark t ((markIndex d).symm i) at he
      apply mark_separates s t e
      intro i
      simpa using he ((markIndex d) i))
  change Nat.card (Fin d → Fin d → Fin d → ZMod 2) ≤ _ at hc
  simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, ← pow_mul] at hc
  convert hc using 2 <;> congr 1 <;> ring

end Erdos1160Growth.TensorFamily

namespace Erdos1160.Abelian

open CategoryTheory

/-- The isomorphism classes of abelian groups of order strictly below the cutoff. -/
def classesBelow (N : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G < N ∧ ∀ a b : G, a * b = b * a}

abbrev Code (m : ℕ) := (k : Fin (m + 1)) × (Fin k.val → Fin (2 ^ m))

abbrev factor (t : ℕ) := Multiplicative (ZMod (t + 1))

noncomputable def decode (m : ℕ) (c : Code m) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (FiniteGrp.of ((i : Fin c.1.val) → factor (c.2 i).val))

/-- Encode the nontrivial cyclic factors of a finite abelian group by a bounded tuple. -/
theorem classesBelow_subset_range (m : ℕ) :
    classesBelow (2 ^ m) ⊆ Set.range (decode m) := by
  classical
  rintro _ ⟨G, ⟨hbound, hcomm⟩, rfl⟩
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  obtain ⟨ι, inst, n, hn, ⟨iso⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have size : Nat.card G = ∏ i, n i := by
    rw [Nat.card_congr iso.toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => Nat.card_zmod (n i)
  have product_lt : ∏ i, n i < 2 ^ m := size ▸ hbound
  have length_lt : Fintype.card ι < m := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    refine lt_of_le_of_lt ?_ product_lt
    calc
      2 ^ Fintype.card ι = ∏ _i : ι, (2 : ℕ) := by simp
      _ ≤ ∏ i, n i := Finset.prod_le_prod (by simp) (fun i _ => hn i)
  have entry_lt (i : ι) : n i < 2 ^ m :=
    (Finset.single_le_prod' (s := Finset.univ) (fun j _ => (hn j).le) (Finset.mem_univ i)).trans_lt product_lt
  let e := Fintype.equivFin ι
  let k : Fin (m + 1) := ⟨Fintype.card ι, by omega⟩
  let f : Fin k.val → Fin (2 ^ m) :=
    fun j => ⟨n (e.symm j) - 1, by have := entry_lt (e.symm j); omega⟩
  refine ⟨⟨k, f⟩, Quotient.sound ?_⟩
  let reindex : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((j : Fin k.val) → Multiplicative (ZMod (n (e.symm j)))) :=
    { Equiv.piCongrLeft' _ e with map_mul' := by intros; rfl }
  have eqf (j : Fin k.val) : n (e.symm j) = (f j).val + 1 := by
    change _ = n _ - 1 + 1
    have := hn (e.symm j)
    omega
  let congr : ((j : Fin k.val) → Multiplicative (ZMod (n (e.symm j)))) ≃*
      ((j : Fin k.val) → factor (f j).val) :=
    MulEquiv.piCongrRight fun j => by
      unfold factor
      rw [eqf j]
  let H := FiniteGrp.of ((j : Fin k.val) → factor (f j).val)
  let equiv : G ≃* H := (iso.trans reindex).trans congr
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := H.toGrp) (Y := G.toGrp) equiv.symm)⟩

theorem classesBelow_finite (m : ℕ) : (classesBelow (2 ^ m)).Finite :=
  (Set.finite_range (decode m)).subset (classesBelow_subset_range m)

/-- Bound the contribution of all abelian groups, uniformly over all smaller orders. -/
theorem classesBelow_ncard_le (m : ℕ) :
    (classesBelow (2 ^ m)).ncard ≤ 2 ^ (m * m + m) := by
  classical
  calc
    (classesBelow (2 ^ m)).ncard ≤ (Set.range (decode m)).ncard :=
      Set.ncard_le_ncard (classesBelow_subset_range m) (Set.finite_range _)
    _ ≤ Nat.card (Code m) := by
      rw [← Set.image_univ, ← Set.ncard_univ]
      exact Set.ncard_image_le
    _ = ∑ k : Fin (m + 1), (2 ^ m) ^ k.val := by
      rw [Nat.card_sigma]
      simp
    _ ≤ (m + 1) * (2 ^ m) ^ m := by
      simpa using Finset.sum_le_card_nsmul Finset.univ
        (fun k : Fin (m + 1) => (2 ^ m) ^ k.val) ((2 ^ m) ^ m)
        (fun k _ => Nat.pow_le_pow_right (by positivity) (by omega))
    _ ≤ 2 ^ m * (2 ^ m) ^ m := Nat.mul_le_mul_right _ Nat.lt_two_pow_self
    _ = 2 ^ (m * m + m) := by rw [← pow_mul, ← pow_add, Nat.add_comm]
/-- The abelian isomorphism classes of exactly one order. -/
def classesAt (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n ∧ ∀ a b : G, a * b = b * a}

private theorem classesAt_subset_below {n N : ℕ} (h : n < N) : classesAt n ⊆ classesBelow N := by
  rintro _ ⟨G, ⟨hcard, hcomm⟩, rfl⟩
  exact ⟨G, ⟨hcard.trans_lt h, hcomm⟩, rfl⟩

private theorem classesAt_disjoint {n k : ℕ} (hnk : n ≠ k) : Disjoint (classesAt n) (classesAt k) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨G, ⟨hG, _⟩, rfl⟩ ⟨H, ⟨hH, _⟩, heq⟩
  obtain ⟨iso⟩ := Quotient.exact heq
  let e := ((inducedFunctor FiniteGrp.toGrp).mapIso iso).groupIsoToMulEquiv
  exact hnk (hG.symm.trans ((Nat.card_congr e.toEquiv).symm.trans hH))

theorem sum_classesAt_eq (m : ℕ) :
    (∑ n ∈ Finset.Ico 1 (2 ^ m), (classesAt n).ncard) = (classesBelow (2 ^ m)).ncard := by
  classical
  let s := Finset.Ico 1 (2 ^ m)
  have hu : (⋃ i ∈ (s : Set ℕ), classesAt i) = classesBelow (2 ^ m) := by
    ext q
    simp only [Set.mem_iUnion, SetLike.mem_coe, s, Finset.mem_Ico, exists_prop]
    constructor
    · rintro ⟨i, ⟨_, hi⟩, hq⟩
      exact classesAt_subset_below hi hq
    · rintro ⟨G, ⟨hG, hcomm⟩, rfl⟩
      exact ⟨Nat.card G, ⟨Nat.card_pos, hG⟩, G, ⟨rfl, hcomm⟩, rfl⟩
  rw [← hu]
  have hfin : ∀ i ∈ (s : Set ℕ), (classesAt i).Finite := by
    intro i hi
    exact (classesBelow_finite m).subset (classesAt_subset_below (Finset.mem_Ico.mp hi).2)
  have hd : (s : Set ℕ).PairwiseDisjoint classesAt :=
    fun _ _ _ _ hne => classesAt_disjoint hne
  rw [s.finite_toSet.ncard_biUnion hfin hd]
  rw [finsum_mem_eq_finite_toFinset_sum _ s.finite_toSet]
  simp [s]

theorem abelian_contribution_le (m : ℕ) :
    (∑ n ∈ Finset.Ico 1 (2 ^ m), (classesAt n).ncard) ≤ 2 ^ (m * m + m) :=
  (sum_classesAt_eq m).trans_le (classesBelow_ncard_le m)

end Erdos1160.Abelian

namespace Erdos1160.Abelian

/-- Doubling the total abelian contribution still stays below the preceding dyadic count. -/
theorem twice_abelian_le_previous (m : ℕ) (hm : 100 ≤ m) :
    2 * (∑ n ∈ Finset.Ico 1 (2 ^ m), (classesAt n).ncard) ≤ g (2 ^ (m - 1)) := by
  let d := (m - 1) / 3
  have hd : 33 ≤ d := by dsimp [d]; omega
  have hmono : 3*d ≤ m - 1 := by dsimp [d]; omega
  have hu : m ≤ 3*d + 3 := by dsimp [d]; omega
  have hh := Nat.mul_le_mul hu hu
  have hh' := Nat.mul_le_mul_right (d*d) hd
  have hh'' := Nat.mul_le_mul_right d hd
  have hs : (m*m+m+1) + 9*d^2 ≤ d^3 := by nlinarith
  have hl := Erdos1160Growth.TensorFamily.cubic_parameter_lower d
  have hp : 2^(m*m+m+1) * 2^(9*d^2) ≤ g (2^(3*d)) * 2^(9*d^2) := by
    rw [← pow_add]
    exact (Nat.pow_le_pow_right (by decide) hs).trans hl
  have hcancel : 2^(m*m+m+1) ≤ g (2^(3*d)) :=
    Nat.le_of_mul_le_mul_right hp (by positivity)
  calc
    _ ≤ 2 * 2 ^ (m*m+m) := Nat.mul_le_mul_left _ (abelian_contribution_le m)
    _ = 2 ^ (m*m+m+1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ g (2 ^ (m-1)) := hcancel.trans
      (monotone_nat_of_le_succ Erdos1160.Cancellation.g_two_pow_mono hmono)

end Erdos1160.Abelian

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1.H1 := by
  apply Filter.eventually_atTop.mpr
  refine ⟨100, fun m hm => ?_⟩
  have hs : m - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  exact (Erdos1160.Abelian.twice_abelian_le_previous m hm).trans
    (Finset.single_le_sum (f := fun k => Erdos1160.g (2 ^ k)) (fun _ _ => Nat.zero_le _) hs)
