import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Abel
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.PGroup
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Positivity
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Ring.Parity
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fintype

/- ClassTwoData -/
section

namespace ClassTwoProfile

open scoped commutatorElement

abbrev Cyc (n : ℕ) := Multiplicative (ZMod (2^n))
abbrev Factors {r : ℕ} (e : Fin r → ℕ) := (i : Fin r) → Cyc (e i)

def gen {r : ℕ} (e : Fin r → ℕ) (i : Fin r) : Factors e :=
  Pi.mulSingle i (Multiplicative.ofAdd 1)

theorem gen_pow {r : ℕ} (e : Fin r → ℕ) (i : Fin r) : gen e i ^ (2^(e i)) = 1 := by
  rw [gen,← Pi.mulSingle_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod (2^(e i)))) ^ (2^(e i)) = 1 := by
    change (2^(e i)) • (1 : ZMod (2^(e i))) = 0
    simp [nsmul_eq_mul]
  rw [h,Pi.mulSingle_one]

theorem gen_closure {r : ℕ} (e : Fin r → ℕ) : Subgroup.closure (Set.range (gen e)) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using Pi.mulSingle_induction with
  | one => exact Subgroup.one_mem _
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy
  | mulSingle i x =>
    let j := x.toAdd.val
    have hx : x = (Multiplicative.ofAdd (1 : ZMod (2^(e i)))) ^ j := by
      change x.toAdd = j • (1 : ZMod (2^(e i)))
      simp [j,nsmul_eq_mul]
    rw [hx,Pi.mulSingle_pow]
    exact Subgroup.pow_mem _ (show gen e i ∈ Subgroup.closure (Set.range (gen e)) from Subgroup.subset_closure ⟨i,rfl⟩) _

theorem card_factors {r : ℕ} (e : Fin r → ℕ) : Nat.card (Factors e) = 2^(∑ i, e i) := by
  rw [Nat.card_pi,←Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => Nat.card_zmod _

/-- A finite central extension expressed in cyclic coordinates for the kernel and quotient. -/
structure Data (E : Type) [Group E] {d s : ℕ} (e : Fin d → ℕ) (b : Fin s → ℕ) where
  incl : Factors b →* E
  inj : Function.Injective incl
  cent : incl.range ≤ Subgroup.center E
  proj : E →* Factors e
  onto : Function.Surjective proj
  ker_eq : proj.ker = incl.range
  x : Fin d → E
  x_spec : ∀ i, proj (x i) = gen e i

namespace Data

variable {E : Type} [Group E] {d s : ℕ} {e : Fin d → ℕ} {b : Fin s → ℕ} (S : Data E e b)

include S in
lemma center_comm (x y : E) : ⁅x,y⁆ ∈ Subgroup.center E := by
  apply S.cent
  rw [←S.ker_eq, MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

lemma central_pow (i : Fin d) : S.x i ^ (2^(e i)) ∈ Subgroup.center E := by
  apply S.cent
  rw [←S.ker_eq,MonoidHom.mem_ker,map_pow,S.x_spec,gen_pow]

include S in
lemma comm_pow_left (x y : E) (n : ℕ) : ⁅x^n,y⁆ = ⁅x,y⁆^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,commutatorElement_mul_left_eq_conj_mul,ih,pow_succ']
    have hc := Subgroup.mem_center_iff.mp (S.center_comm x y) (x^n)
    rw [hc,mul_inv_cancel_right]

include S in
lemma comm_pow_right (x y : E) (n : ℕ) : ⁅x,y^n⁆ = ⁅x,y⁆^n := by
  rw [← commutatorElement_inv (y^n) x, S.comm_pow_left, ←inv_pow, commutatorElement_inv]

abbrev Tor (k : ℕ) (b : Fin s→ℕ) := {w : Factors b // w^(2^k) = 1}

lemma pow_mem (i : Fin d) : S.x i^(2^(e i)) ∈ S.incl.range := by
  rw [← S.ker_eq, MonoidHom.mem_ker,map_pow,S.x_spec,gen_pow]

noncomputable def powCode (i : Fin d) : Factors b := Classical.choose (S.pow_mem i)

lemma powCode_spec (i : Fin d) : S.incl (S.powCode i) = S.x i^(2^(e i)) :=
  Classical.choose_spec (S.pow_mem i)

lemma comm_mem (i j : Fin d) : ⁅S.x i,S.x j⁆ ∈ S.incl.range := by
  rw [← S.ker_eq, MonoidHom.mem_ker,map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

noncomputable def commCode (i j : Fin d) : Tor (min (e i) (e j)) b := by
  have hcomm := S.comm_mem i j
  refine ⟨Classical.choose hcomm, ?_⟩
  apply S.inj
  rw [map_one,map_pow,Classical.choose_spec hcomm]
  rcases le_total (e i) (e j) with h|h
  · rw [min_eq_left h,←S.comm_pow_left]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (S.central_pow i) _).symm
  · rw [min_eq_right h,←S.comm_pow_right]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (S.central_pow j) _)

lemma commCode_spec (i j : Fin d) : S.incl (S.commCode i j).val = ⁅S.x i,S.x j⁆ :=
  Classical.choose_spec (S.comm_mem i j)

end Data
end ClassTwoProfile

end

/- ParameterSizes -/
section

namespace ClassTwoProfile

abbrev Tri (d : ℕ) := (i : Fin d) × Fin i.val
def row {d : ℕ} (l : Tri d) := l.1
def col {d : ℕ} (l : Tri d) : Fin d := ⟨l.2.val, l.2.isLt.trans l.1.isLt⟩

variable {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ)

abbrev Code := (Fin d → Factors b) × ((l : Tri d) → Data.Tor (min (e (row l)) (e (col l))) b)

lemma card_tor (k : ℕ) :
    Nat.card (Data.Tor k b) = 2^(∑ i, min k (b i)) := by
  let f : Data.Tor k b ≃ ∀ i, (powMonoidHom (2^k) : Cyc (b i) →* Cyc (b i)).ker :=
    { toFun := fun w i => ⟨w.1 i,congrFun w.2 i⟩
      invFun := fun w => ⟨fun i => w i, funext (fun i => (w i).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr f,Nat.card_pi,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [IsCyclic.card_powMonoidHom_ker]
  change (Nat.card (ZMod (2^(b i)))).gcd (2^k) = _
  rw [Nat.card_zmod]
  rcases le_total k (b i) with h|h
  · rw [min_eq_left h, Nat.gcd_eq_right (pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (pow_dvd_pow 2 h)]

def cost := d*(∑i,b i) + ∑ l : Tri d, ∑ k, min (min (e (row l)) (e (col l))) (b k)

lemma card_code : Nat.card (Code e b) = 2^(cost e b) := by
  rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,card_factors,Nat.card_pi]
  simp_rw [card_tor]
  rw [←pow_mul,Finset.prod_pow_eq_pow_sum,←pow_add,Nat.mul_comm (∑ i,b i)]
  rfl

end ClassTwoProfile

end

/- CentralBound -/
section

namespace CentralKernelCount

open scoped commutatorElement

def adjoin {G : Type*} [Group G] {d : ℕ} (N : Subgroup G) (x : Fin d → G) : Subgroup G :=
  N ⊔ Subgroup.closure (Set.range x)

theorem central_normal {G : Type*} [Group G] {N : Subgroup G} (hn : N ≤ Subgroup.center G) :
    N.Normal where
  conj_mem n m g := by
    rw [Subgroup.mem_center_iff.mp (hn m) g,mul_inv_cancel_right]
    exact m

/-- Above a normal subgroup, adjoining d generators with involutory, pairwise commuting
images can increase the order by a factor of at most two to the d. -/
theorem card_adjoin_orders {G : Type*} [Group G] [Finite G] {d : ℕ} (N : Subgroup G) [N.Normal]
    (x : Fin d → G) (n : Fin d → ℕ) (hn : ∀ i, 0 < n i) (hsq : ∀ i, x i ^ n i ∈ N) (hcomm : ∀ i j, ⁅x i,x j⁆ ∈ N) :
    Nat.card (adjoin N x) ≤ (∏ i, n i) * Nat.card N := by
  classical
  let π := QuotientGroup.mk' N
  let S := adjoin N x
  let f := π.comp S.subtype
  let H (i : Fin d) := Subgroup.zpowers (π (x i))
  have van {g : G} (h : g ∈ N) : π g = 1 := (QuotientGroup.eq_one_iff _).mpr h
  have commute : Pairwise fun i j => ∀ z w : G ⧸ N, z ∈ H i → w ∈ H j → Commute z w := by
    intro i j _ z w hz hw
    obtain ⟨m,rfl⟩ := hz
    obtain ⟨n,rfl⟩ := hw
    have hc : Commute (π (x i)) (π (x j)) :=
      commutatorElement_eq_one_iff_mul_comm.mp <| (map_commutatorElement π _ _).symm.trans (van (hcomm i j))
    exact hc.zpow_zpow _ _
  let p := Subgroup.noncommPiCoprod commute
  have hSP : S ≤ p.range.comap π := by
    apply sup_le
    · intro z hz
      change π z ∈ p.range
      rw [van hz]
      exact p.range.one_mem
    · rw [Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      change π (x i) ∈ p.range
      rw [show p.range = ⨆ i, H i from Subgroup.noncommPiCoprod_range]
      exact (le_iSup H i) (Subgroup.mem_zpowers _)
  have hrange : f.range ≤ p.range := by
    rintro z ⟨w,rfl⟩
    exact hSP w.property
  have hp : Nat.card p.range ≤ ∏ i, n i := by
    apply (Nat.card_le_card_of_surjective _ p.rangeRestrict_surjective).trans
    rw [Nat.card_pi]
    apply Finset.prod_le_prod'
    intro i _
    change Nat.card (Subgroup.zpowers (π (x i))) ≤ n i
    rw [Nat.card_zpowers]
    apply Nat.le_of_dvd (hn i)
    exact orderOf_dvd_of_pow_eq_one <| (map_pow π _ _).symm.trans (van (hsq i))
  have hk : Nat.card f.ker ≤ Nat.card N := by
    let m (z : f.ker) : N := ⟨z.val.val,(QuotientGroup.eq_one_iff _).mp z.property⟩
    apply Nat.card_le_card_of_injective m
    intro z w hw
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun q : N => q.val) hw)
  change Nat.card S ≤ _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  apply Nat.mul_le_mul _ hk
  exact (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hrange)).trans hp

theorem card_adjoin {G : Type*} [Group G] [Finite G] {d : ℕ} (N : Subgroup G) [N.Normal]
    (x : Fin d → G) (hsq : ∀ i, x i ^ 2 ∈ N) (hcomm : ∀ i j, ⁅x i,x j⁆ ∈ N) :
    Nat.card (adjoin N x) ≤ 2^d * Nat.card N := by
  simpa using card_adjoin_orders N x (fun _ => 2) (fun _ => by decide) hsq hcomm

end CentralKernelCount

end

/- PairedCentral -/
section

namespace CentralKernelCount

open scoped commutatorElement

theorem map_adjoin {G J : Type*} [Group G] [Group J] {d : ℕ}
    (N : Subgroup G) (x : Fin d → G) (f : G →* J) :
    (adjoin N x).map f = adjoin (N.map f) (fun i => f (x i)) := by
  rw [adjoin,adjoin,Subgroup.map_sup,MonoidHom.map_closure,← Set.range_comp]
  rfl

theorem paired_equiv {E F : Type*} [Group E] [Group F] [Finite E] [Finite F] {d : ℕ}
    (N : Subgroup (E × F)) [N.Normal] (x : Fin d → E × F) (n : Fin d → ℕ)
    (hn : ∀ i, 0 < n i) (hpow : ∀ i, x i ^ n i ∈ N) (hcomm : ∀ i j, ⁅x i,x j⁆ ∈ N)
    (genE : adjoin (N.map (MonoidHom.fst E F)) (fun i => (x i).1) = ⊤)
    (genF : adjoin (N.map (MonoidHom.snd E F)) (fun i => (x i).2) = ⊤)
    (cardE : (∏ i,n i)*Nat.card N ≤ Nat.card E)
    (cardF : (∏ i,n i)*Nat.card N ≤ Nat.card F) : Nonempty (E ≃* F) := by
  let S := adjoin N x
  have bound := card_adjoin_orders N x n hn hpow hcomm
  let fE := (MonoidHom.fst E F).comp S.subtype
  let fF := (MonoidHom.snd E F).comp S.subtype
  have se : Function.Surjective fE := by
    intro v
    change v ∈ fE.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact (genE ▸ (show v ∈ (⊤ : Subgroup E) from trivial))
  have sf : Function.Surjective fF := by
    intro v
    change v ∈ fF.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact (genF ▸ (show v ∈ (⊤ : Subgroup F) from trivial))
  exact ⟨(MulEquiv.ofBijective fE (se.bijective_of_nat_card_le (bound.trans cardE))).symm.trans
    (MulEquiv.ofBijective fF (sf.bijective_of_nat_card_le (bound.trans cardF)))⟩

end CentralKernelCount

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

/- ClassTwoCompare -/
section

namespace ClassTwoProfile

open scoped commutatorElement
open CentralKernelCount CategoryTheory

namespace Data
variable {E F : Type} [Group E] [Group F]
variable {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ}
variable (S : Data E e b) (T : Data F e b)

noncomputable def code : Code e b := (S.powCode,fun l => S.commCode (row l) (col l))

lemma adjoin_eq : adjoin S.incl.range S.x = ⊤ := by
  let H := adjoin S.incl.range S.x
  have hin : S.incl.range ≤ H := le_sup_left
  have hx (i : Fin d) : S.x i ∈ H :=
    le_sup_right (a := S.incl.range) (Subgroup.subset_closure ⟨i,rfl⟩)
  have hmap : H.map S.proj = ⊤ := by
    apply top_unique
    rw [←gen_closure e]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨S.x i,hx i,S.x_spec i⟩
  apply top_unique
  intro v _
  obtain ⟨z,hz,hz'⟩ : S.proj v ∈ H.map S.proj := hmap ▸ trivial
  have hres : v*z⁻¹ ∈ S.incl.range := by rw [←S.ker_eq,MonoidHom.mem_ker,map_mul,map_inv,hz',mul_inv_cancel]
  simpa using H.mul_mem (hin hres) hz

include S in
lemma card_group : Nat.card E = (∏ i, 2^(e i))*Nat.card (Factors b) := by
  have H := S.proj.ker.index_mul_card
  have hi : S.proj.ker.index = Nat.card (Factors e) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective S.proj S.onto).toEquiv
  rw [hi,S.ker_eq,←Nat.card_congr (MonoidHom.ofInjective S.inj).toEquiv,card_factors,←Finset.prod_pow_eq_pow_sum] at H
  exact H.symm

theorem equiv_of_code [Finite E] [Finite F] (h : S.code = T.code) : Nonempty (E ≃* F) := by
  let z := S.incl.prod T.incl
  let N := z.range
  let x (i : Fin d) : E×F := (S.x i,T.x i)
  have mem (w : Factors b) : (S.incl w,T.incl w) ∈ N := ⟨w,rfl⟩
  let _ : N.Normal :=
    { conj_mem := by
        rintro _ ⟨w,rfl⟩ g
        have hE := Subgroup.mem_center_iff.mp (S.cent (show S.incl w ∈ S.incl.range from ⟨w,rfl⟩)) g.1
        have hF := Subgroup.mem_center_iff.mp (T.cent (show T.incl w ∈ T.incl.range from ⟨w,rfl⟩)) g.2
        change (g.1*S.incl w*g.1⁻¹,g.2*T.incl w*g.2⁻¹) ∈ N
        rw [hE,hF,mul_inv_cancel_right,mul_inv_cancel_right]
        exact mem w }
  have hp (i : Fin d) : S.powCode i = T.powCode i := congrFun (congrArg Prod.fst h) i
  have hc (i j : Fin d) (hj : j < i) : (S.commCode i j).val = (T.commCode i j).val :=
    congrArg Subtype.val (congrFun (congrArg Prod.snd h) ⟨i,⟨j.val,hj⟩⟩)
  have hpow (i : Fin d) : x i ^ (2^(e i)) ∈ N := by
    change (S.x i ^ (2^(e i)),T.x i ^ (2^(e i))) ∈ N
    rw [←S.powCode_spec i, ←T.powCode_spec i, ←hp]
    exact mem _
  have hcomm1 (i j : Fin d) (hj : j < i) : ⁅x i,x j⁆ ∈ N := by
    change (⁅S.x i,S.x j⁆,⁅T.x i,T.x j⁆) ∈ N
    rw [←S.commCode_spec, ←T.commCode_spec, ←hc i j hj]
    exact mem _
  have hcomm (i j : Fin d) : ⁅x i,x j⁆ ∈ N := by
    rcases lt_trichotomy j i with hij | rfl | hij
    · exact hcomm1 i j hij
    · simp
    · rw [←commutatorElement_inv]
      exact N.inv_mem (hcomm1 j i hij)
  have hinj : Function.Injective z := fun _ _ he => S.inj (congrArg Prod.fst he)
  have hcard : Nat.card N = Nat.card (Factors b) := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine paired_equiv N x (fun i=>2^(e i)) (fun _=>Nat.pow_pos (by decide)) hpow hcomm ?_ ?_ ?_ ?_
  · change adjoin ((S.incl.prod T.incl).range.map _) S.x = ⊤
    rw [←MonoidHom.range_comp,MonoidHom.fst_comp_prod,S.adjoin_eq]
  · change adjoin ((S.incl.prod T.incl).range.map _) T.x = ⊤
    rw [←MonoidHom.range_comp,MonoidHom.snd_comp_prod,T.adjoin_eq]
  · rw [hcard,S.card_group]
  · rw [hcard,T.card_group]

end Data

def profileClasses {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) :
    Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | Nonempty (Data E e b)}

theorem profileClasses_bound {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) :
    (profileClasses e b).ncard ≤ 2^(cost e b) := by
  classical
  let G (c : profileClasses e b) : FiniteGrp := c.property.choose
  let S (c : profileClasses e b) : Data (G c) e b := c.property.choose_spec.1.some
  let f (c : profileClasses e b) := (S c).code
  have hf : Function.Injective f := by
    intro c d he
    have ⟨h⟩ := (S c).equiv_of_code (S d) he
    apply Subtype.ext
    rw [← c.property.choose_spec.2, ← d.property.choose_spec.2]
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (G c).toGrp) (Y := (G d).toGrp) h)⟩
  exact (Nat.card_le_card_of_injective f hf).trans_eq (card_code e b)

end ClassTwoProfile

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

/- NoncentralRanks -/
section

namespace ClassTwoProfile.Data

open scoped commutatorElement
open CentralKernelCount

variable {E : Type} [Group E] {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ} (S : Data E e b)

include S in
def commSquareHom (y : E) : E →* E where
  toFun x := ⁅x,y⁆^2
  map_one' := by simp
  map_mul' x z := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h := Subgroup.mem_center_iff.mp (S.center_comm z y) x
    rw [h,mul_inv_cancel_right]
    have hzx : Commute ⁅z,y⁆ ⁅x,y⁆ :=
      (Subgroup.mem_center_iff.mp (S.center_comm x y) _)
    rw [hzx.eq, hzx.symm.mul_pow]

lemma kill_commSquare (y : E) (h : ∀ i, ⁅S.x i,y⁆^2=1) (v : E) : ⁅v,y⁆^2=1 := by
  let f := S.commSquareHom y
  have hk : f.ker = ⊤ := by
    apply top_unique
    rw [←S.adjoin_eq]
    apply sup_le
    · intro w hw
      change ⁅w,y⁆^2=1
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (S.cent hw) _).symm,one_pow]
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      exact h i
  exact (show v ∈ f.ker from hk ▸ trivial)

lemma swap_commSquare {v w : E} (h : ⁅v,w⁆^2=1) : ⁅w,v⁆^2=1 := by
  rw [←commutatorElement_inv, inv_pow, h,inv_one]

theorem bad_pair [Finite E] (hn : ¬ frattini E ≤ Subgroup.center E) :
    ∃ i j, ⁅S.x i,S.x j⁆^2 ≠ 1 := by
  by_contra! ha
  apply hn
  apply Erdos1160Growth.LowerTriangularUpper.frattini_le_squareCore.trans
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Eq.symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change ⁅x*x,y⁆ = 1
  rw [←sq, S.comm_pow_left]
  apply S.kill_commSquare
  intro i
  exact swap_commSquare (S.kill_commSquare (S.x i) (fun j =>ha j i) y)

lemma height_from_pow {A : Type*} [Group A] {w : A} {k : ℕ}
    (h : w^(2^k)=1) (hbad : w^2≠1) : 2 ≤ k := by
  by_contra! hk
  apply hbad
  apply orderOf_dvd_iff_pow_eq_one.mp
  have h' := orderOf_dvd_iff_pow_eq_one.mpr h
  have hd := pow_dvd_pow 2 (show k ≤ 1 by omega)
  simpa using h'.trans hd

include S in
theorem high_indices [Finite E] (hn : ¬ frattini E ≤ Subgroup.center E) :
    (∃ i j : Fin d, i≠j ∧ 2 ≤ e i ∧ 2 ≤ e j) ∧ (∃ k : Fin s, 2 ≤ b k) := by
  obtain ⟨i,j,hbad⟩ := S.bad_pair hn
  let w := (S.commCode i j).val
  have hw : w^2 ≠ 1 := by
    intro he
    apply hbad
    rw [←S.commCode_spec, ←map_pow,show (S.commCode i j).val ^2 = 1 from he,map_one]
  have hh := height_from_pow (S.commCode i j).2 hw
  refine ⟨⟨i,j,?_,(le_min_iff.mp hh).1,(le_min_iff.mp hh).2⟩,?_⟩
  · intro hij
    subst j
    simp at hbad
  · by_contra! h
    apply hw
    funext k
    have hx := pow_card_eq_one' (x := w k)
    change w k ^ 2 = 1
    rw [show Nat.card (Cyc (b k)) = 2^(b k) from Nat.card_zmod _] at hx
    by_contra! hh
    exact (not_le.mpr (h k)) (height_from_pow hx hh)

lemma excess_of_high {d : ℕ} (v : Fin d→ℕ) (hv : ∀ i,0 < v i) {i : Fin d} (hi : 2 ≤ v i) :
    d+1 ≤ ∑j,v j := by
  calc
    _ = ∑ j : Fin d, (1+(if j=i then 1 else 0)) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by have := hv j; by_cases hj : j=i <;> simp_all <;> exact hv j)

lemma excess_of_two {d : ℕ} (v : Fin d→ℕ) (hv : ∀ i,0 < v i) {i j : Fin d} (hne : i≠j)
    (hi : 2 ≤ v i) (hj : 2 ≤ v j) : d+2 ≤ ∑k,v k := by
  calc
    _ = ∑ k : Fin d, (1+(if k=i then 1 else 0)+(if k=j then 1 else 0)) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun k _ => by
      have := hv k
      by_cases hki : k=i
      · subst k
        simp_all
      · by_cases hkj : k=j <;> simp_all <;> exact hv k)

include S in
theorem ranks_tail [Finite E] (hn : ¬ frattini E ≤ Subgroup.center E)
    (he : ∀ i,0 < e i) (hb : ∀ k,0 < b k) : d+s+3 ≤ (∑i,e i)+(∑k,b k) := by
  obtain ⟨⟨i,j,hij,hi,hj⟩,⟨k,hk⟩⟩ := S.high_indices hn
  have h₁ := excess_of_high b hb hk
  have h₂ := excess_of_two e he hij hi hj
  omega

end ClassTwoProfile.Data

end

/- CyclicCoords -/
section

namespace ClassTwoProfile

lemma exists_cyclic_coords (A : Type) [CommGroup A] [Finite A] {m : ℕ}
    (hc : Nat.card A = 2^m) :
    ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ (∑ i, e i)=m ∧ Nonempty (A ≃* Factors e) := by
  classical
  obtain ⟨ι,_,n,hn,⟨f⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hor : ∏ i, n i = 2^m := by
    rw [←hc, Nat.card_congr f.toEquiv,Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => (Nat.card_zmod _).symm
  have pow (i : ι) : ∃ a ≤ m, n i = 2^a := by
    apply (Nat.dvd_prime_pow Nat.prime_two).mp
    rw [←hor]
    exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  let e' (i : ι) := (pow i).choose
  have hn' (i : ι) : n i = 2^(e' i) := (pow i).choose_spec.2
  let t := Fintype.equivFin ι
  let e := e' ∘ t.symm
  let reindex : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((j : Fin (Fintype.card ι)) → Multiplicative (ZMod (n (t.symm j)))) :=
    { Equiv.piCongrLeft' _ t with map_mul' := by intros; rfl }
  let factorIso : ((j : Fin (Fintype.card ι)) → Multiplicative (ZMod (n (t.symm j)))) ≃* Factors e :=
    MulEquiv.piCongrRight fun j => by change Multiplicative (ZMod (n (t.symm j))) ≃* Multiplicative (ZMod (2^(e' (t.symm j)))); rw [hn']
  let h := (f.trans reindex).trans factorIso
  refine ⟨_,e,?_,?_,⟨h⟩⟩
  · intro i
    have hni := hn (t.symm i)
    rw [hn'] at hni
    change 0 < e' _
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hni
  · apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2^(∑ i,e i) = 2^m
    rw [←hc, Nat.card_congr h.toEquiv,card_factors]

end ClassTwoProfile

end

/- ClassTwoProfiles -/
section

namespace ClassTwoProfile

theorem exists_composition_coords (A : Type) [CommGroup A] [Finite A] {m : ℕ}
    (hc : Nat.card A = 2^m) :
    ∃ c : Composition m, Nonempty (A ≃* Factors c.blocksFun) := by
  classical
  obtain ⟨d,e,hpos,hsum,⟨f⟩⟩ := exists_cyclic_coords A hc
  let c : Composition m :=
    { blocks := List.ofFn e
      blocks_pos := by
        intro a ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
        exact hpos i
      blocks_sum := by simpa only [List.sum_ofFn] using hsum }
  have hlen : c.length = d := List.length_ofFn
  let t := finCongr hlen.symm
  let r : Factors e ≃* ((i : Fin c.length) → Cyc (e (t.symm i))) :=
    { Equiv.piCongrLeft' _ t with map_mul' := by intros; rfl }
  refine ⟨c, ⟨(f.trans r).trans (MulEquiv.piCongrRight fun i => ?_)⟩⟩
  have ei : c.blocksFun i = e (t.symm i) := List.get_ofFn _ _
  change Cyc (e (t.symm i)) ≃* Cyc (c.blocksFun i)
  rw [ei]

noncomputable def Data.ofCentralSubgroup {E : Type} [Group E]
    {d s : ℕ} {e : Fin d → ℕ} {b : Fin s → ℕ}
    (K : Subgroup E) [K.Normal] (hc : K ≤ Subgroup.center E)
    (iK : K ≃* Factors b) (iQ : E ⧸ K ≃* Factors e) : Data E e b := by
  classical
  let incl := K.subtype.comp iK.symm.toMonoidHom
  let proj := iQ.toMonoidHom.comp (QuotientGroup.mk' K)
  have hi : incl.range = K := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact (iK.symm u).property
    · intro hx
      exact ⟨iK ⟨x,hx⟩, congrArg Subtype.val (iK.symm_apply_apply ⟨x,hx⟩)⟩
  have hp : Function.Surjective proj := iQ.surjective.comp (QuotientGroup.mk'_surjective K)
  refine { incl := incl, inj := Subtype.val_injective.comp iK.symm.injective,
           cent := hi ▸ hc, proj := proj, onto := hp, ker_eq := ?_,
           x := fun i => (hp (gen e i)).choose,
           x_spec := fun i => (hp (gen e i)).choose_spec }
  rw [hi, MonoidHom.ker_comp_of_injective _ _ iQ.injective, QuotientGroup.ker_mk']

end ClassTwoProfile

end

/- LayerMargin -/
section

namespace Erdos1160Growth.LayerMargin

private theorem cubic_width (d s : ℕ) :
    27*(s*d.choose 2) ≤ 2*(d+s)^3 := by
  have hcut : 2*d.choose 2 ≤ d*d := by
    rw [Nat.choose_two_right]
    exact (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  have hab : 27*s*d^2 ≤ 4*(d+s)^3 := by
    zify
    nlinarith only [mul_nonneg (sq_nonneg ((d:ℤ)-2*s)) (show 0 ≤ 4*(d:ℤ)+s by positivity)]
  nlinarith only [Nat.mul_le_mul_left s hcut, hab]

private theorem sum_cubes_le {ι : Type*} (I : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ I, (f i)^3) ≤ (∑ i ∈ I, f i)^3 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    nlinarith only [ih, Nat.zero_le (f i^2*(∑ j ∈ I, f j)), Nat.zero_le (f i*(∑ j ∈ I, f j)^2)]

/-- A single layer and its complementary layers each carry at least three dimensions.
The counts of alternating commutators and powers then leave a quadratic margin,
with the estimate valid for all widths including zero. -/
theorem profile_cost {ι : Type*} (I : Finset ι) (d s : ι → ℕ) {j : ι} (hj : j ∈ I)
    (m : ℕ) (hsize : ∑ i ∈ I, (d i+s i) = m)
    (hbase : 3 ≤ d j+s j) (htail : d j+s j+3 ≤ m) :
    108*((∑ i ∈ I, s i*(d i).choose 2)+d j*(∑ i ∈ I, s i))+45*m^2 ≤
      8*m^3+216*m := by
  classical
  let u (i : ι) := d i+s i
  let t := ∑ i ∈ I.erase j, u i
  have hs : u j+t=m := (Finset.add_sum_erase I u hj).trans hsize
  have ht : 3 ≤ t := by change u j + 3 ≤ m at htail; omega
  have hb : 3 ≤ u j := hbase
  have hump : 3*m ≤ u j*t+9 := by
    obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le hb
    obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le ht
    rw [← hs, hx, hy]
    nlinarith only [Nat.zero_le (x*y)]
  have hcube : (∑ i ∈ I, u i^3)+9*m^2 ≤ m^3+27*m := by
    rw [← Finset.add_sum_erase I (fun i => u i^3) hj]
    have he := sum_cubes_le (I.erase j) u
    change _ ≤ t^3 at he
    have hp := Nat.mul_le_mul_left (3*m) hump
    rw [← hs] at hp ⊢
    nlinarith only [hp,he]
  have halts : 27*(∑ i ∈ I, s i*(d i).choose 2) ≤ 2*(∑ i ∈ I, u i^3) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => cubic_width (d i) (s i))
  let A := ∑ i ∈ I, d i
  let B := ∑ i ∈ I, s i
  have htot : A+B=m := by simpa only [Finset.sum_add_distrib] using hsize
  have hdom : d j ≤ A := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  have hcross : 4*(d j*B) ≤ m^2 := by
    have h := Nat.mul_le_mul_right B hdom
    rw [← htot]
    zify at h ⊢
    nlinarith only [h,sq_nonneg ((A:ℤ)-B)]
  change 108*((∑ i ∈ I, s i*(d i).choose 2)+d j*B)+45*m^2 ≤ _
  omega

/-- Applicable directly to the layer widths of two decompositions into cyclic factors.
The six linear dimensions of slack also pay for the choices of both profiles. -/
theorem antitone_profile_with_slack (m : ℕ) (hm : 200 ≤ m) (d s : Fin (m+1) → ℕ)
    (hd : Antitone d) (_hs : Antitone s)
    (hsize : ∑ i, (d i+s i) = m) (htail : d 0+s 0+3 ≤ m) :
    27*((∑ i, s i*(d i*(d i-1)/2))+d 0*(∑ i, s i)+6*m)+10*m^2 ≤ 2*m^3 := by
  classical
  by_cases hbase : 3 ≤ d 0 + s 0
  · have h := profile_cost Finset.univ d s (Finset.mem_univ 0) m hsize hbase htail
    simp only [Nat.choose_two_right] at h
    have hsq := Nat.mul_le_mul_right m hm
    nlinarith only [h,hsq]
  · have hd₂ (i : Fin (m+1)) : d i ≤ 2 := by
      have h := hd (Fin.zero_le i)
      omega
    have cs (i : Fin (m+1)) : d i*(d i-1)/2 ≤ 1 := by
      have h : d i=0 ∨ d i=1 ∨ d i=2 := by have := hd₂ i; omega
      rcases h with h | h | h <;> simp [h]
    have hc : (∑ i, s i*(d i*(d i-1)/2)) ≤ ∑ i, s i := by
      exact Finset.sum_le_sum (fun i _ => (Nat.mul_le_mul_left (s i) (cs i)).trans_eq (Nat.mul_one _))
    have hs' : (∑ i, s i) ≤ m := by
      calc
        _ ≤ ∑ i, (d i+s i) := Finset.sum_le_sum (fun i _ => Nat.le_add_left (s i) (d i))
        _ = _ := hsize
    have hp := Nat.mul_le_mul (hd₂ 0) hs'
    have hpoly : 27*(3*m+6*m)+10*m^2 ≤ 2*m^3 := by
      obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hm
      rw [hv]
      nlinarith only [Nat.zero_le v,Nat.zero_le (v^2),Nat.zero_le (v^3)]
    omega

end Erdos1160Growth.LayerMargin

end

/- CompositionProfiles -/
section

namespace Erdos1160Growth.LayerMargin

abbrev CompositionProfiles (m : ℕ) := (a : Fin (m+1)) × (Composition a.val × Composition (m-a.val))

theorem count_composition_profiles (m : ℕ) : Nat.card (CompositionProfiles m) ≤ 2^(2*m) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  calc
    _ ≤ ∑ _a : Fin (m+1), 2^m := by
      apply Finset.sum_le_sum
      intro a _
      rw [Fintype.card_prod, composition_card, composition_card, ← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by have := a.isLt; omega)
    _ = (m+1)*2^m := by simp
    _ ≤ 2^m * 2^m := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt m.lt_two_pow_self)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem sum_composition_costs (m : ℕ) (S : Finset (CompositionProfiles m))
    (C : CompositionProfiles m → ℕ)
    (hC : ∀ p ∈ S, 27*(C p+6*m)+10*m^2 ≤ 2*m^3) :
    (∑ p ∈ S, 2^(C p))^27 * 2^(10*m^2) ≤ 2^(2*m^3) := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨q, hq, hmax⟩ := S.exists_max_image C hS
    have hcard : S.card ≤ 2^(6*m) := by
      have h₀ : S.card ≤ Fintype.card (CompositionProfiles m) := Finset.card_le_univ _
      rw [← Nat.card_eq_fintype_card] at h₀
      exact (h₀.trans (count_composition_profiles m)).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    have hu : (∑ p ∈ S, 2^(C p)) ≤ 2^(6*m+C q) := calc
      _ ≤ ∑ _p ∈ S, 2^(C q) := Finset.sum_le_sum (fun p hp => Nat.pow_le_pow_right (by decide) (hmax p hp))
      _ = S.card * 2^(C q) := by simp
      _ ≤ 2^(6*m)*2^(C q) := Nat.mul_le_mul_right _ hcard
      _ = _ := (pow_add _ _ _).symm
    have hc := hC q hq
    calc
      _ ≤ (2^(6*m+C q))^27 * 2^(10*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hu _)
      _ = 2^((6*m+C q)*27+10*m^2) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end Erdos1160Growth.LayerMargin

end

/- NoncentralCover -/
section

namespace ClassTwoProfile

open CategoryTheory Erdos1160Growth.LayerMargin

def noncentralClasses (m : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧ commutator G ≤ Subgroup.center G ∧
    ¬ frattini G ≤ Subgroup.center G}

def deepProfiles (m : ℕ) : Finset (CompositionProfiles m) :=
  Finset.univ.filter (fun p => p.2.1.length + p.2.2.length + 3 ≤ m)

abbrev listed {m : ℕ} (p : CompositionProfiles m) := profileClasses p.2.1.blocksFun p.2.2.blocksFun
abbrev price {m : ℕ} (p : CompositionProfiles m) := cost p.2.1.blocksFun p.2.2.blocksFun

lemma profileClasses_finite {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) :
    (profileClasses e b).Finite := by
  apply (Erdos1160.groupClasses_finite ((∏i,2^(e i))*Nat.card (Factors b))).subset
  rintro _ ⟨G,⟨S⟩,rfl⟩
  exact ⟨G,S.card_group,rfl⟩

theorem subgroup_profiles (m : ℕ) (G : FiniteGrp.{0}) (hc : Nat.card G=2^m)
    (K : Subgroup G) [K.Normal] (hK : ∀ x y : K, x*y=y*x) (hQ : ∀ x y : G ⧸ K, x*y=y*x) :
    ∃ p : CompositionProfiles m, Nonempty ((G ⧸ K) ≃* Factors p.2.1.blocksFun) ∧
      Nonempty (K ≃* Factors p.2.2.blocksFun) := by
  let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := hK }
  let _ : CommGroup (G ⧸ K) := { (inferInstance : Group (G ⧸ K)) with mul_comm := hQ }
  have hi := K.index_mul_card
  rw [hc] at hi
  obtain ⟨a,ha,ha'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show K.index ∣ 2^m from ⟨_,hi.symm⟩)
  obtain ⟨j,_,hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card K ∣ 2^m from (dvd_mul_left _ _).trans (dvd_of_eq hi))
  rw [ha',hj',←pow_add] at hi
  have haj : a+j=m := Nat.pow_right_injective (by decide : 1 < 2) hi
  have hr : j=m-a := by omega
  subst j
  obtain ⟨u,⟨fu⟩⟩ := exists_composition_coords (G ⧸ K) (by rwa [← Subgroup.index_eq_card])
  obtain ⟨v,⟨fv⟩⟩ := exists_composition_coords K hj'
  exact ⟨⟨⟨a,by omega⟩,u,v⟩,⟨fu⟩,⟨fv⟩⟩

theorem noncentral_cover (m : ℕ) :
    noncentralClasses m ⊆ ⋃ p ∈ deepProfiles m, listed p := by
  rintro _ ⟨G,⟨hc,hcenter,hnot⟩,rfl⟩
  let K := commutator G
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hcenter y.property) x.val) }
  let _ : CommGroup (G ⧸ K) := Abelianization.commGroup G
  obtain ⟨p,⟨fu⟩,⟨fv⟩⟩ := subgroup_profiles m G hc K (fun _ _=>mul_comm _ _) (fun _ _=>mul_comm _ _)
  let u := p.2.1
  let v := p.2.2
  let S := Data.ofCentralSubgroup K hcenter fv fu
  have hdeep : p ∈ deepProfiles m := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change u.length + v.length + 3 ≤ m
    have h := S.ranks_tail hnot u.one_le_blocksFun v.one_le_blocksFun
    simp only [Composition.sum_blocksFun] at h
    dsimp [u,v] at *
    omega
  exact Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hdeep ⟨G,⟨S⟩,rfl⟩)

def deepClasses (m : ℕ) := ⋃ p ∈ deepProfiles m, listed p

theorem deepClasses_finite (m : ℕ) : (deepClasses m).Finite :=
  (deepProfiles m).finite_toSet.biUnion (fun _p _ => profileClasses_finite _ _)

theorem deepClasses_bound (m : ℕ) : (deepClasses m).ncard ≤ ∑ p ∈ deepProfiles m, 2^(price p) :=
  ((deepProfiles m).set_ncard_biUnion_le listed).trans (Finset.sum_le_sum (fun _p _ => profileClasses_bound _ _))

theorem sum_profile_bound (m : ℕ) : (noncentralClasses m).ncard ≤ ∑ p ∈ deepProfiles m, 2^(price p) :=
  (Set.ncard_le_ncard (noncentral_cover m) (deepClasses_finite m)).trans (deepClasses_bound m)

end ClassTwoProfile

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

/- SquareSizes -/
section

namespace ClassTwoProfile

open Erdos1160Growth.LowerTriangularUpper

lemma squareCore_eq_range (A : Type*) [CommGroup A] : squareCore A = (powMonoidHom 2 : A→*A).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    exact ⟨a,sq a⟩
  · rintro _ ⟨u,rfl⟩
    exact Subgroup.subset_closure ⟨u,(sq u).symm⟩

lemma squareCore_size {A : Type} [CommGroup A] {s : ℕ} {b : Fin s→ℕ}
    (f : A ≃* Factors b) (hb : ∀ i,0 < b i) :
    Nat.card (squareCore A)*2^s = 2^(∑ i,b i) := by
  let g := (powMonoidHom 2 : A→*A)
  let kerE : g.ker ≃ Data.Tor 1 b :=
    { toFun := fun w => ⟨f w.val,by change (f w.val)^2=1; rw [←map_pow,show w.val^2=1 from w.2,map_one]⟩
      invFun := fun w => ⟨f.symm w.val,by change (f.symm w.val)^2=1; rw [←map_pow,show w.val^2=1 from w.2,map_one]⟩
      left_inv := by intro w; exact Subtype.ext (f.symm_apply_apply _)
      right_inv := by intro w; exact Subtype.ext (f.apply_symm_apply _) }
  have hk : Nat.card g.ker = 2^s := by
    rw [Nat.card_congr kerE,card_tor]
    have he (i : Fin s) : min 1 (b i)=1 := min_eq_left (show 1 ≤ b i from hb i)
    simp [he]
  have h := g.ker.index_mul_card
  rw [Subgroup.index_ker,hk, Nat.card_congr f.toEquiv, card_factors] at h
  rw [squareCore_eq_range]
  exact h

end ClassTwoProfile

end

/- BigCover -/
section

namespace ClassTwoProfile

open CategoryTheory Erdos1160Growth.LowerTriangularUpper

def bigFrattiniClasses (m : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧ frattini G ≤ Subgroup.center G ∧
    8 ≤ Nat.card (squareCore (frattini G))}

theorem bigFrattini_subset_deep (m : ℕ) : bigFrattiniClasses m ⊆ deepClasses m := by
  rintro _ ⟨G,⟨hc,hcenter,hbig⟩,rfl⟩
  let K := frattini G
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hcenter y.property) x.val) }
  have hsq (x : G ⧸ K) : x*x=1 := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact squares_le_frattini hc (Subgroup.subset_closure ⟨u,rfl⟩)
  have hinv (x : G ⧸ K) : x⁻¹=x := inv_eq_of_mul_eq_one_left (hsq x)
  let _ : CommGroup (G ⧸ K) := { (inferInstance : Group (G ⧸ K)) with
    mul_comm := fun x y => by
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv] }
  obtain ⟨p,⟨fu⟩,⟨fv⟩⟩ := subgroup_profiles m G hc K (fun _ _=>mul_comm _ _) (fun _ _=>mul_comm _ _)
  let S := Data.ofCentralSubgroup K hcenter fv fu
  have hsh := squareCore_size fv p.2.2.one_le_blocksFun
  rw [Composition.sum_blocksFun] at hsh
  have hbig' : 2^3 ≤ Nat.card (squareCore K) := hbig
  have hl : p.2.2.length + 3 ≤ m-p.1.val := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [Nat.add_comm, Nat.pow_add, ←hsh]
    exact Nat.mul_le_mul_right _ hbig'
  have hdeep : p ∈ deepProfiles m := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have ha := p.1.isLt
    have hlen := p.2.1.length_le
    omega
  exact Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hdeep ⟨G,⟨S⟩,rfl⟩)

end ClassTwoProfile

end

/- WidthCount -/
section

namespace ClassTwoProfile

open Finset

def width {d : ℕ} (e : Fin d → ℕ) (t : ℕ) := (univ.filter (fun i => t < e i)).card

theorem width_zero {d : ℕ} (e : Fin d → ℕ) (h : ∀ i, 0 < e i) : width e 0 = d := by
  simp [width, h]

theorem width_antitone {d : ℕ} (e : Fin d → ℕ) : Antitone (width e) := by
  intro t u h
  apply Finset.card_le_card
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, h.trans_lt (mem_filter.mp hi).2⟩

private theorem count_levels {x m : ℕ} (h : x ≤ m) :
    (∑ t : Fin (m+1), if t.val < x then 1 else 0) = x := by
  classical
  rw [Finset.sum_boole]
  have eqn : (univ.filter (fun t : Fin (m+1) => t.val < x)).card =
      (univ : Finset (Fin x)).card := by
    refine Finset.card_bij (fun a ha => ⟨a.val,(mem_filter.mp ha).2⟩) (fun _ _ => mem_univ _) ?_ ?_
    · intro a ha b hb hab
      exact Fin.ext (congrArg (fun v : Fin x => v.val) hab)
    · intro b _
      refine ⟨⟨b.val,by omega⟩,?_,rfl⟩
      exact mem_filter.mpr ⟨mem_univ _,b.isLt⟩
  simpa using eqn

theorem sum_width {n m : ℕ} (e : Fin n → ℕ) (h : ∀ i, e i ≤ m) :
    (∑ t : Fin (m+1), width e t.val) = ∑ i, e i := by
  simp only [width, Finset.card_filter]
  rw [Finset.sum_comm]
  exact sum_congr rfl (fun i _ => count_levels (h i))

private theorem triangle_count {d : ℕ} (e : Fin d → ℕ) (t : ℕ) :
    (∑ l : Tri d, if t < e (row l) ∧ t < e (col l) then 1 else 0) =
      width e t * (width e t-1) / 2 := by
  classical
  let U := univ.filter (fun i : Fin d => t < e i)
  rw [Finset.sum_boole, ← Nat.choose_two_right]
  change (univ.filter _).card = U.card.choose 2
  rw [← Finset.card_product_filter_lt (s := U)]
  refine Finset.card_bij (fun l _ => (col l,row l)) ?_ ?_ ?_
  · intro l hl
    obtain ⟨hr,hc⟩ := (mem_filter.mp hl).2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hc⟩,
      mem_filter.mpr ⟨mem_univ _,hr⟩⟩,l.2.isLt⟩
  · rintro ⟨i,j⟩ _ ⟨k,r⟩ _ h
    have hik : i=k := congrArg Prod.snd h
    subst k
    have hjr : j.val=r.val := congrArg (fun pair : Fin d × Fin d => pair.1.val) h
    obtain rfl := Fin.ext hjr
    rfl
  · rintro ⟨i,j⟩ h
    rcases mem_filter.mp h with ⟨hm,hlt⟩
    obtain ⟨hi,hj⟩ := mem_product.mp hm
    refine ⟨⟨j,⟨i.val,hlt⟩⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2,(mem_filter.mp hi).2⟩

theorem cost_eq_width {d s m : ℕ} (e : Fin d → ℕ) (b : Fin s → ℕ)
    (he : ∀ i, e i ≤ m) (hb : ∀ j, b j ≤ m) :
    cost e b = (∑ t : Fin (m+1),width b t.val *
      (width e t.val*(width e t.val-1)/2)) + d*(∑ i,b i) := by
  rw [cost,add_comm]
  congr 1
  let v (l : Tri d) (j : Fin s) := min (min (e (row l)) (e (col l))) (b j)
  have hl (l : Tri d) (j : Fin s) : v l j ≤ m := (min_le_right _ _).trans (hb j)
  change (∑ l, ∑ j, v l j) = _
  calc
    _ = ∑ l, ∑ j, ∑ t : Fin (m+1), if t.val < v l j then 1 else 0 := by
      exact sum_congr rfl fun l _ => sum_congr rfl fun j _ => (count_levels (hl l j)).symm
    _ = ∑ t : Fin (m+1), ∑ l, ∑ j, if t.val < v l j then 1 else 0 := by
      simp_rw [Finset.sum_comm (s := (univ : Finset (Fin s))) (t := (univ : Finset (Fin (m+1))))]
      rw [Finset.sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [← triangle_count,Finset.mul_sum]
      apply sum_congr rfl
      intro l _
      change (∑ j, if t.val < min (min (e (row l)) (e (col l))) (b j) then 1 else 0) = _
      by_cases ht : t.val < e (row l) ∧ t.val < e (col l)
      · simpa [lt_min_iff,ht,width] using (Finset.sum_boole (s := (univ : Finset (Fin s)))
          (p := fun j => t.val < b j))
      · simp [lt_min_iff,ht]
        intro _ h₁ h₂
        exact False.elim (ht ⟨h₁,h₂⟩)

end ClassTwoProfile

end

/- NoncentralUpper -/
section

namespace ClassTwoProfile

open Erdos1160Growth.LayerMargin

theorem cheap_deep_profile (m : ℕ) (hm : 200 ≤ m) (p : CompositionProfiles m)
    (hp : p ∈ deepProfiles m) : 27*(price p+6*m)+10*m^2 ≤ 2*m^3 := by
  let e := p.2.1.blocksFun
  let b := p.2.2.blocksFun
  let u (t : Fin (m+1)) := width e t.val
  let v (t : Fin (m+1)) := width b t.val
  have ha : p.1.val ≤ m := Nat.le_of_lt_succ p.1.isLt
  have he (i) : e i ≤ m := (p.2.1.blocksFun_le i).trans ha
  have hb (i) : b i ≤ m := (p.2.2.blocksFun_le i).trans (Nat.sub_le m p.1.val)
  have su : (∑ t, u t) = p.1.val := (sum_width e he).trans p.2.1.sum_blocksFun
  have sv : (∑ t, v t) = m-p.1.val := (sum_width b hb).trans p.2.2.sum_blocksFun
  have hsize : (∑ t, (u t + v t)) = m := by rw [Finset.sum_add_distrib,su,sv]; omega
  have hz : u 0 = p.2.1.length := width_zero e p.2.1.one_le_blocksFun
  have hz' : v 0 = p.2.2.length := width_zero b p.2.2.one_le_blocksFun
  have hlarge : u 0+v 0+3 ≤ m := by
    rw [hz,hz']
    exact (Finset.mem_filter.mp hp).2
  have h := antitone_profile_with_slack m hm u v
    (fun _ _ hij=>width_antitone e hij) (fun _ _ hij=>width_antitone b hij) hsize hlarge
  change 27*(cost e b+6*m)+10*m^2 ≤ 2*m^3
  rw [cost_eq_width e b he hb, ← sum_width b hb]
  rw [hz] at h
  exact h

theorem deepProfileUnion_upper (m : ℕ) (hm : 200 ≤ m) :
    (deepClasses m).ncard^27 * 2^(10*m^2) ≤ 2^(2*m^3) := by
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (deepClasses_bound m) 27)).trans
    (sum_composition_costs m (deepProfiles m) price (cheap_deep_profile m hm))

/-- All groups of order 2^m whose derived subgroup is central and whose
Frattini subgroup is noncentral have a quadratic saving over Higman's cubic exponent. -/
theorem noncentral_class_two_upper (m : ℕ) (hm : 200 ≤ m) :
    (noncentralClasses m).ncard^27 * 2^(10*m^2) ≤ 2^(2*m^3) := by
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (sum_profile_bound m) 27)).trans
    (sum_composition_costs m (deepProfiles m) price (cheap_deep_profile m hm))

end ClassTwoProfile

end

/- Erdos1160Tables -/
section

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

end

/- LiftPresentations -/
section

namespace Erdos1160.CentralLifts

open scoped commutatorElement

variable {I J : Type} {p : ℕ}

abbrev Grp (R : J → FreeGroup I) := PresentedGroup (Set.range R)

def newRel (R : J → FreeGroup I) (c : J → Fin p) : Unit ⊕ (I ⊕ J) → FreeGroup (Option I)
  | .inl _ => FreeGroup.of none ^ p
  | .inr (.inl i) => ⁅FreeGroup.of (none : Option I), FreeGroup.of (some i)⁆
  | .inr (.inr j) => FreeGroup.map some (R j) * (FreeGroup.of none ^ (c j).val)⁻¹

abbrev Lift (R : J → FreeGroup I) (c : J → Fin p) := Grp (newRel R c)

def z (R : J → FreeGroup I) (c : J → Fin p) : Lift R c := PresentedGroup.of none

def old (R : J → FreeGroup I) (c : J → Fin p) (i : I) : Lift R c := PresentedGroup.of (some i)

theorem relation {A B : Type} (S : B → FreeGroup A) (j : B) :
    PresentedGroup.mk (Set.range S) (S j) = 1 :=
  PresentedGroup.one_of_mem ⟨j,rfl⟩

theorem z_pow (R : J → FreeGroup I) (c : J → Fin p) : z R c ^ p = 1 := by
  simpa only [newRel, map_pow, z, PresentedGroup.of] using relation (newRel R c) (.inl ())

theorem z_commutes_old (R : J → FreeGroup I) (c : J → Fin p) (i : I) :
    Commute (z R c) (old R c i) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [newRel, map_commutatorElement, z, old, PresentedGroup.of] using
    relation (newRel R c) (.inr (.inl i))

theorem z_central (R : J → FreeGroup I) (c : J → Fin p) :
    z R c ∈ Subgroup.center (Lift R c) := by
  rw [Subgroup.center_eq_iInf (PresentedGroup.closure_range_of (Set.range (newRel R c)))]
  simp only [Subgroup.mem_iInf, Subgroup.mem_centralizer_singleton_iff]
  rintro _ ⟨_ | i,rfl⟩
  · rfl
  · exact (z_commutes_old R c i).eq

instance z_normal (R : J → FreeGroup I) (c : J → Fin p) :
    (Subgroup.zpowers (z R c)).Normal where
  conj_mem n hn g := by
    have hcenter : n ∈ Subgroup.center (Lift R c) := (Subgroup.zpowers_le.mpr (z_central R c)) hn
    have hc := Subgroup.mem_center_iff.mp hcenter g
    rwa [hc, mul_inv_cancel_right]

def inc (R : J → FreeGroup I) (c : J → Fin p) : FreeGroup I →* Lift R c :=
  (PresentedGroup.mk (Set.range (newRel R c))).comp (FreeGroup.map some)

theorem inc_rel (R : J → FreeGroup I) (c : J → Fin p) (j : J) :
    inc R c (R j) = z R c ^ (c j).val := by
  apply eq_of_mul_inv_eq_one
  simpa only [newRel, map_mul, map_inv, map_pow, inc, MonoidHom.comp_apply, z, PresentedGroup.of]
    using relation (newRel R c) (.inr (.inr j))

def quotientMap (R : J → FreeGroup I) (c : J → Fin p) :
    Grp R →* (Lift R c ⧸ Subgroup.zpowers (z R c)) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (inc R c)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    change (QuotientGroup.mk' _) (inc R c (R j)) = 1
    rw [inc_rel, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)

theorem quotientMap_old (R : J → FreeGroup I) (c : J → Fin p) (i : I) :
    quotientMap R c (PresentedGroup.of i) = (QuotientGroup.mk' _) (old R c i) := by rfl

theorem quotientMap_surjective (R : J → FreeGroup I) (c : J → Fin p) :
    Function.Surjective (quotientMap R c) := by
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers (z R c)) y
  change (QuotientGroup.mk' _) x ∈ (quotientMap R c).range
  have h : (quotientMap R c).range.comap (QuotientGroup.mk' (Subgroup.zpowers (z R c))) = ⊤ := by
    apply top_unique
    rw [← PresentedGroup.closure_range_of (Set.range (newRel R c))]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨_ | i,rfl⟩
    · change (QuotientGroup.mk' (Subgroup.zpowers (z R c))) (z R c) ∈ (quotientMap R c).range
      have hz : (QuotientGroup.mk' (Subgroup.zpowers (z R c))) (z R c) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
      rw [hz]
      exact Subgroup.one_mem _
    · exact ⟨PresentedGroup.of i,quotientMap_old R c i⟩
  exact (show x ∈ (quotientMap R c).range.comap (QuotientGroup.mk' _) by rw [h]; trivial)

theorem card_lift (R : J → FreeGroup I) (c : J → Fin p) [Finite (Grp R)] (hp : 0 < p) :
    Nat.card (Lift R c) ≤ Nat.card (Grp R) * p := by
  let N := Subgroup.zpowers (z R c)
  have hc : Nat.card N ≤ p := by
    rw [show Nat.card N = orderOf (z R c) from Nat.card_zpowers _]
    exact Nat.le_of_dvd hp (orderOf_dvd_iff_pow_eq_one.mpr (z_pow R c))
  rw [Nat.card_congr (Subgroup.groupEquivQuotientProdSubgroup (s := N)), Nat.card_prod]
  exact Nat.mul_le_mul (Nat.card_le_card_of_surjective (quotientMap R c) (quotientMap_surjective R c)) hc

theorem finite_lift (R : J → FreeGroup I) (c : J → Fin p) [Finite (Grp R)] (hp : 0 < p) :
    Finite (Lift R c) := by
  let N := Subgroup.zpowers (z R c)
  have hd := orderOf_dvd_iff_pow_eq_one.mpr (z_pow R c)
  let : Finite N := Nat.finite_of_card_ne_zero (by rw [show Nat.card N = orderOf (z R c) from Nat.card_zpowers _]; exact fun e => by simp [e] at hd; omega)
  let : Finite (Lift R c ⧸ N) := Finite.of_surjective (quotientMap R c) (quotientMap_surjective R c)
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := N)).symm

end Erdos1160.CentralLifts

end

/- RealizeLift -/
section

namespace Erdos1160.CentralLifts

open scoped commutatorElement

variable {I J : Type} {p : ℕ}

theorem lift_surjection {U Q : Type} [Group U] [Group Q] [Finite U]
    (R : J → FreeGroup I) (q : U →* Q) (hq : Function.Surjective q)
    (u : U) (hu : orderOf u = p) (hcenter : u ∈ Subgroup.center U)
    (hker : q.ker = Subgroup.zpowers u) (e : Grp R →* Q) (he : Function.Surjective e) :
    ∃ c : J → Fin p, ∃ f : Lift R c →* U, Function.Surjective f := by
  classical
  choose x hx using (fun i : I => hq (e (PresentedGroup.of i)))
  let X := FreeGroup.lift x
  have hqX : q.comp X = e.comp (PresentedGroup.mk (Set.range R)) :=
    FreeGroup.ext_hom _ _ (fun i => by simpa [X, PresentedGroup.of] using hx i)
  have hrel (j : J) : X (R j) ∈ Subgroup.zpowers u := by
    rw [← hker, MonoidHom.mem_ker]
    change (q.comp X) (R j) = 1
    rw [hqX, MonoidHom.comp_apply, relation, map_one]
  have existsTwist (j : J) : ∃ t : Fin p, X (R j) = u ^ t.val := by
    have h := (isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf.mp (hrel j)
    obtain ⟨k,hk,heq⟩ := Finset.mem_image.mp h
    exact ⟨⟨k,hu ▸ Finset.mem_range.mp hk⟩,heq.symm⟩
  choose c hc using existsTwist
  let y : Option I → U := fun o => o.elim u x
  let Y := FreeGroup.lift y
  have hu1 : Y (FreeGroup.of none) = u := by simp [Y,y]
  have hxi (i : I) : Y (FreeGroup.of (some i)) = x i := by simp [Y,y]
  have hXY : Y.comp (FreeGroup.map some) = X := FreeGroup.ext_hom _ _ (fun i => by simp [Y,X,y])
  have rels : ∀ w ∈ Set.range (newRel R c), Y w = 1 := by
    rintro w ⟨(_ | (i | j)),rfl⟩
    · simpa only [newRel, map_pow, hu1, ← hu] using pow_orderOf_eq_one u
    · rw [newRel, map_commutatorElement, hu1, hxi, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcenter _).symm
    · simp only [newRel,map_mul,map_inv,map_pow,hu1]
      change (Y.comp (FreeGroup.map some)) (R j) * (u ^ (c j).val)⁻¹ = 1
      rw [hXY,hc,mul_inv_cancel]
  let f : Lift R c →* U := PresentedGroup.toGroup rels
  have fgen (i : Option I) : f (PresentedGroup.of i) = y i := PresentedGroup.toGroup.of rels
  have hcomp : (q.comp f).comp (inc R c) = e.comp (PresentedGroup.mk (Set.range R)) := by
    apply FreeGroup.ext_hom
    intro i
    change q (f (PresentedGroup.of (some i))) = e (PresentedGroup.of i)
    rw [fgen]
    exact hx i
  refine ⟨c,f,?_⟩
  have uin : u ∈ f.range := ⟨PresentedGroup.of none, fgen none⟩
  have kernel : q.ker ≤ f.range := hker ▸ (Subgroup.zpowers_le.mpr uin)
  intro a
  obtain ⟨b,hb⟩ := he (q a)
  obtain ⟨w,rfl⟩ := PresentedGroup.mk_surjective (Set.range R) b
  let v := inc R c w
  have qv : q (f v) = q a := (DFunLike.congr_fun hcomp w).trans hb
  have ha : a * (f v)⁻¹ ∈ q.ker := by rw [MonoidHom.mem_ker,map_mul,map_inv,qv,mul_inv_cancel]
  obtain ⟨r,hr⟩ := kernel ha
  exact ⟨r*v,by rw [map_mul,hr,inv_mul_cancel_right]⟩

theorem exists_central_prime {p k : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (h : Nat.card G = p^(k+1)) :
    ∃ u : G, u ∈ Subgroup.center G ∧ orderOf u = p := by
  obtain ⟨j,hj,hz⟩ := IsPGroup.card_center_eq_prime_pow h (by omega)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p
    (hz ▸ (dvd_pow_self _ (Nat.ne_of_gt hj)))
  exact ⟨t.val,t.property,(Subgroup.orderOf_coe t).trans ht⟩

theorem normal_zpowers_of_central {G : Type} [Group G] (u : G) (hz : u ∈ Subgroup.center G) :
    (Subgroup.zpowers u).Normal where
  conj_mem n hn g := by
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz) hn) g
    rwa [hc,mul_inv_cancel_right]

theorem card_quotient_prime {G : Type} [Group G] {u : G}
    [_n : (Subgroup.zpowers u).Normal] {p k : ℕ} (hp : 0 < p)
    (ho : orderOf u = p) (h : Nat.card G = p^(k+1)) :
    Nat.card (G ⧸ Subgroup.zpowers u) = p^k := by
  apply Nat.mul_left_cancel hp
  calc
    p * Nat.card (G ⧸ Subgroup.zpowers u) = Nat.card (Subgroup.zpowers u) * (Subgroup.zpowers u).index := by
      rw [Nat.card_zpowers, ho, Subgroup.index_eq_card]
    _ = Nat.card G := Subgroup.card_mul_index _
    _ = p*p^k := by rw [h, pow_succ, mul_comm]

end Erdos1160.CentralLifts

end

/- LiftCodes -/
section

namespace Erdos1160.CentralLifts

def Gen : ℕ → Type
  | 0 => Empty
  | k + 1 => Option (Gen k)

def Rel : ℕ → Type
  | 0 => Empty
  | k + 1 => Unit ⊕ (Gen k ⊕ Rel k)

def Codes (p : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Codes p k × (Rel k → Fin p)

def relations {p : ℕ} : {k : ℕ} → Codes p k → Rel k → FreeGroup (Gen k)
  | 0, _, r => nomatch r
  | k + 1, c, r => newRel (relations (k := k) c.1) c.2 r

instance genFinite (k : ℕ) : Finite (Gen k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Empty)
  | succ k ih => exact inferInstanceAs (Finite (Option (Gen k)))

instance relFinite (k : ℕ) : Finite (Rel k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Empty)
  | succ k ih => exact inferInstanceAs (Finite (Unit ⊕ (Gen k ⊕ Rel k)))

instance codeFinite (p k : ℕ) : Finite (Codes p k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ k ih => exact inferInstanceAs (Finite (Codes p k × (Rel k → Fin p)))

theorem card_gen (k : ℕ) : Nat.card (Gen k) = k := by
  induction k with
  | zero => simp [Gen]
  | succ k ih =>
    change Nat.card (Option (Gen k)) = k+1
    letI := Fintype.ofFinite (Gen k)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using congrArg (· + 1) ih

theorem twice_card_rel (k : ℕ) : 2 * Nat.card (Rel k) = k*(k+1) := by
  induction k with
  | zero => simp [Rel]
  | succ k ih =>
    change 2 * Nat.card (Unit ⊕ (Gen k ⊕ Rel k)) = (k+1)*(k+1+1)
    simp only [Nat.card_sum, Nat.card_unique, card_gen]
    nlinarith only [ih]

theorem card_codes_succ (p k : ℕ) :
    Nat.card (Codes p (k+1)) = Nat.card (Codes p k) * p ^ Nat.card (Rel k) := by
  change Nat.card (Codes p k × (Rel k → Fin p)) = _
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]

theorem card_codes_pow_six_le (p k : ℕ) (hp : 0 < p) :
    (Nat.card (Codes p k))^6 ≤ p^(k^3) := by
  induction k with
  | zero => simp [Codes]
  | succ k ih =>
    rw [card_codes_succ, mul_pow, ← pow_mul]
    calc
      _ ≤ p^(k^3) * p^(Nat.card (Rel k)*6) := Nat.mul_le_mul_right _ ih
      _ = p^(k^3 + Nat.card (Rel k)*6) := (pow_add _ _ _).symm
      _ ≤ p^((k+1)^3) := Nat.pow_le_pow_right hp (by
        have h := twice_card_rel k
        nlinarith only [h])

end Erdos1160.CentralLifts

end

/- PrimePowerUpper -/
section

namespace Erdos1160.CentralLifts

open CategoryTheory

abbrev Model {p k : ℕ} (c : Codes p k) := Grp (relations c)

theorem trivial_zero {p : ℕ} (c : Codes p 0) : Subsingleton (Model c) := by
  let : IsEmpty (Gen 0) := inferInstanceAs (IsEmpty Empty)
  have h := PresentedGroup.closure_range_of (Set.range (relations c))
  rw [Set.range_eq_empty (PresentedGroup.of : Gen 0 → Model c), Subgroup.closure_empty] at h
  exact (subsingleton_iff_forall_eq (1 : Model c)).2 (fun g =>
    ((Subgroup.eq_bot_iff_forall _).mp h.symm) g trivial)

theorem finite_model {p : ℕ} (hp : 0 < p) (k : ℕ) (c : Codes p k) : Finite (Model c) := by
  induction k with
  | zero => let := trivial_zero c; infer_instance
  | succ k ih =>
    let : Finite (Model c.1) := ih c.1
    exact finite_lift (relations c.1) c.2 hp

theorem card_model {p : ℕ} (hp : 0 < p) (k : ℕ) (c : Codes p k) : Nat.card (Model c) ≤ p^k := by
  induction k with
  | zero =>
    let := trivial_zero c
    rw [Nat.card_unique, pow_zero]
  | succ k ih =>
    let : Finite (Model c.1) := finite_model hp _ _
    exact (card_lift (relations c.1) c.2 hp).trans (by
      rw [pow_succ]; exact Nat.mul_le_mul_right _ (ih c.1))

theorem covered {p : ℕ} (hp : p.Prime) (k : ℕ) (G : Type) [Group G] [Finite G]
    (hG : Nat.card G = p^k) :
    ∃ c : Codes p k, ∃ f : Model c →* G, Function.Surjective f := by
  let : Fact p.Prime := ⟨hp⟩
  induction k generalizing G with
  | zero =>
    have hone : Nat.card G = 1 := hG.trans (pow_zero _)
    let : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hone).1
    exact ⟨(),1,fun g => ⟨1,Subsingleton.elim _ _⟩⟩
  | succ k ih =>
    obtain ⟨u,hz,ho⟩ := exists_central_prime hG
    let N := Subgroup.zpowers u
    let : N.Normal := normal_zpowers_of_central u hz
    have hQ := card_quotient_prime hp.pos ho hG
    obtain ⟨c,f,hf⟩ := ih (G ⧸ N) hQ
    obtain ⟨j,v,hv⟩ := lift_surjection (relations c) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      u ho hz (QuotientGroup.ker_mk' N) f hf
    exact ⟨(c,j),v,hv⟩

noncomputable def classOfModel {p k : ℕ} (hp : 0 < p) (c : Codes p k) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
  let : Finite (Model c) := finite_model hp _ _
  exact Quotient.mk _ (FiniteGrp.of (Model c))

theorem g_le_card_codes {p : ℕ} (hp : p.Prime) (k : ℕ) :
    g (p^k) ≤ Nat.card (Codes p k) := by
  let f := @classOfModel p k hp.pos
  have h : Tables.orderClasses (p^k) ⊆ Set.range f := by
    rintro _ ⟨G,hG,rfl⟩
    obtain ⟨c,v,hv⟩ := covered hp k G hG
    let : Finite (Model c) := finite_model hp.pos _ _
    have hcard : Nat.card (Model c) = Nat.card G :=
      le_antisymm ((card_model hp.pos _ _).trans (le_of_eq (show Nat.card G = p^k from hG).symm))
        (Nat.card_le_card_of_surjective v hv)
    let e := MulEquiv.ofBijective v ((Nat.bijective_iff_surjective_and_card v).2 ⟨hv,hcard⟩)
    exact ⟨c,Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩⟩
  calc
    g (p^k) ≤ (Set.range f).ncard := Set.ncard_le_ncard h (Set.finite_range f)
    _ ≤ Nat.card (Codes p k) := Nat.card_le_card_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective

/-- Uniform elementary upper bound for the number of groups of prime-power order. -/
theorem prime_power_upper {p : ℕ} (hp : p.Prime) (k : ℕ) :
    g (p^k)^6 ≤ p^(k^3) :=
  (Nat.pow_le_pow_left (g_le_card_codes hp k) 6).trans (card_codes_pow_six_le p k hp.pos)

end Erdos1160.CentralLifts

end

/- QuotientFiber -/
section

namespace Erdos1160.CentralLifts

open CategoryTheory

variable {p m : ℕ} {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q]

/-- Every nontrivial normal subgroup of a finite p-group contains a central
element of order p. -/
theorem central_prime_in_normal (hp : p.Prime) (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (hd : p ∣ Nat.card N) :
    ∃ u : G, u ∈ N ∧ u ∈ Subgroup.center G ∧ orderOf u = p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp' := hG.of_equiv ConjAct.toConjAct
  have hone : (1 : N) ∈ MulAction.fixedPoints (ConjAct G) N := fun _ => smul_one _
  obtain ⟨b,hb,hb1⟩ := hp'.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hd hone
  let C := N ⊓ Subgroup.center G
  have hc : (b : G) ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have h := congrArg ((↑) : N → G) (hb (ConjAct.toConjAct g))
    change g * (b:G) * g⁻¹ = b at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hn : Nontrivial C := (Subgroup.nontrivial_iff_exists_ne_one C).mpr
    ⟨b,⟨b.property,hc⟩,fun e => hb1 (Subtype.ext e.symm)⟩
  obtain ⟨k,hk,hC⟩ := (hG.to_subgroup C).nontrivial_iff_card.mp hn
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := C) p (hC ▸ dvd_pow_self _ (Nat.ne_of_gt hk))
  exact ⟨u,u.property.1,u.property.2,(Subgroup.orderOf_coe u).trans hu⟩

omit [Finite G] [Finite Q] in
theorem ker_card_of_epi (hp : p.Prime) {e : ℕ} (hG : Nat.card G = p^(m+e))
    (hQ : Nat.card Q = p^m) (f : G →* Q) (hf : Function.Surjective f) :
    Nat.card f.ker = p^e := by
  apply Nat.mul_left_cancel (n := p^m) (pow_pos hp.pos _)
  calc
    p^m * Nat.card f.ker = f.ker.index * Nat.card f.ker := by
      rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f hf]
      simp [hQ]
    _ = Nat.card G := f.ker.index_mul_card
    _ = p^m * p^e := hG.trans (pow_add _ _ _)

def Tail (p m : ℕ) : ℕ → Type
  | 0 => Unit
  | e+1 => Tail p m e × (Rel (m+e) → Fin p)

def appendCode (c : Codes p m) : {e : ℕ} → Tail p m e → Codes p (m+e)
  | 0, _ => c
  | _+1, t => (appendCode c t.1,t.2)

instance tailFinite (p m e : ℕ) : Finite (Tail p m e) := by
  induction e with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ e ih => exact inferInstanceAs (Finite (Tail p m e × (Rel (m+e) → Fin p)))

def tailCost (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | e+1 => tailCost m e + (m+e)*(m+e+1)/2

theorem card_tail (p m e : ℕ) : Nat.card (Tail p m e) = p^(tailCost m e) := by
  induction e with
  | zero => simp [Tail,tailCost]
  | succ e ih =>
    change Nat.card (Tail p m e × (Rel (m+e) → Fin p)) = _
    rw [Nat.card_prod,ih,Nat.card_fun,Nat.card_fin,tailCost,pow_add]
    have h := twice_card_rel (m+e)
    rw [← h]
    simp

theorem extension_covered (hp : p.Prime) (hQ : Nat.card Q = p^m) (c : Codes p m)
    (g : Model c →* Q) (hg : Function.Surjective g) (e : ℕ) (hG : Nat.card G = p^(m+e))
    (f : G →* Q) (hf : Function.Surjective f) :
    ∃ t : Tail p m e, ∃ l : Model (appendCode c t) →* G, Function.Surjective l := by
  let _ : Fact p.Prime := ⟨hp⟩
  induction e generalizing G with
  | zero =>
    have he := MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).2 ⟨hf,hG.trans hQ.symm⟩)
    exact ⟨(),he.symm.toMonoidHom.comp g,he.symm.surjective.comp hg⟩
  | succ e ih =>
    have hsize := ker_card_of_epi hp hG hQ f hf
    obtain ⟨u,hu,hz,ho⟩ := central_prime_in_normal hp (IsPGroup.of_card hG) f.ker
      (hsize ▸ dvd_pow_self _ (Nat.succ_ne_zero e))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let q := QuotientGroup.mk' N
    let f' := QuotientGroup.lift N f (Subgroup.zpowers_le.mpr hu)
    have hf' : Function.Surjective f' := by
      intro y
      obtain ⟨x,rfl⟩ := hf y
      exact ⟨q x,rfl⟩
    have h' := card_quotient_prime hp.pos ho (k := m+e) hG
    obtain ⟨t,l,hl⟩ := ih h' f' hf'
    obtain ⟨j,v,hv⟩ := lift_surjection (relations (appendCode c t)) q (QuotientGroup.mk'_surjective _)
      u ho hz (QuotientGroup.ker_mk' _) l hl
    exact ⟨(t,j),v,hv⟩

/-- Actual isomorphism classes of p-groups of order p^(m+e) surjecting to one
specified quotient group Q of order p^m. Every degree of the kernel is allowed. -/
def epiClasses (p m e : ℕ) (Q : Type) [Group Q] : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  {x | ∃ (G : FiniteGrp.{0}), Nat.card G = p^(m+e) ∧ (∃ f : G →* Q, Function.Surjective f) ∧ Quotient.mk _ G = x}

theorem epi_classes_bound (hp : p.Prime) (hQ : Nat.card Q = p^m) (e : ℕ) :
    (epiClasses p m e Q).ncard ≤ p^(tailCost m e) := by
  obtain ⟨c,g,hg⟩ := covered hp m Q hQ
  let encode (t : Tail p m e) := classOfModel hp.pos (appendCode c t)
  have h : epiClasses p m e Q ⊆ Set.range encode := by
    rintro _ ⟨G,hG,⟨f,hf⟩,rfl⟩
    obtain ⟨t,l,hl⟩ := extension_covered hp hQ c g hg e hG f hf
    let _ : Finite (Model (appendCode c t)) := finite_model hp.pos _ _
    have hc : Nat.card (Model (appendCode c t)) = Nat.card G :=
      le_antisymm ((card_model hp.pos _ _).trans hG.ge) (Nat.card_le_card_of_surjective l hl)
    let iso := MulEquiv.ofBijective l ((Nat.bijective_iff_surjective_and_card l).2 ⟨hl,hc⟩)
    exact ⟨t,Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) iso.toGrpIso⟩⟩
  calc
    _ ≤ (Set.range encode).ncard := Set.ncard_le_ncard h (Set.finite_range encode)
    _ ≤ Nat.card (Tail p m e) := Nat.card_le_card_of_surjective (Set.rangeFactorization encode) Set.rangeFactorization_surjective
    _ = _ := card_tail p m e

end Erdos1160.CentralLifts

end

/- DeepBudget -/
section

namespace ClassTwoProfile

open Erdos1160.CentralLifts Erdos1160Growth.LayerMargin

theorem tailCost_le_rect (n e : ℕ) : tailCost n e ≤ e*(n+e)^2 := by
  induction e with
  | zero => simp [tailCost]
  | succ e ih =>
    have hs : n+e ≤ n+(e+1) := by omega
    have ha := Nat.mul_le_mul_left e (Nat.pow_le_pow_left hs 2)
    have hb := (Nat.div_le_self ((n+e)*(n+e+1)) 2).trans
      (Nat.mul_le_mul hs (show n+e+1 ≤ n+(e+1) by omega))
    rw [tailCost]
    nlinarith only [ih,ha,hb]

private theorem layer_cubic (a b : ℕ) :
    27*(b*(a*(a-1)/2)) ≤ 2*(a+b)^3 := by
  have hcut : 2*(a*(a-1)/2) ≤ a*a :=
    (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  have H : 27*b*a^2 ≤ 4*(a+b)^3 := by
    zify
    nlinarith only [mul_nonneg (sq_nonneg ((a:ℤ)-2*b)) (show 0 ≤ 4*(a:ℤ)+b by positivity)]
  nlinarith only [Nat.mul_le_mul_left b hcut,H]

/-- A loss of 32 first-layer dimensions per added binary dimension pays for
all extensions through a kernel of arbitrary nilpotency class. -/
theorem wide_defect_budget (n e : ℕ) (hn : 200 ≤ n) (a b : Fin (n+1) → ℕ)
    (ha : Antitone a) (hb : Antitone b)
    (hs : ∑ i, (a i+b i) = n) (hw : a 0+b 0+32*(e+1) ≤ n) :
    27*((∑ i, b i*(a i*(a i-1)/2)) + a 0*(∑ i, b i) + 2*n + tailCost n e)
      +10*(n+e)^2 ≤ 2*(n+e)^3 := by
  let w := a 0 + b 0
  have hpt (i : Fin (n+1)) : 27*(b i*(a i*(a i-1)/2)) ≤ 2*w^2*(a i+b i) := by
    have h₁ := Nat.add_le_add (ha (Fin.zero_le i)) (hb (Fin.zero_le i))
    have h₂ := Nat.mul_le_mul_right (a i+b i) (Nat.pow_le_pow_left h₁ 2)
    have h₃ := layer_cubic (a i) (b i)
    dsimp [w]
    nlinarith only [h₂,h₃]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpt i)
  rw [←Finset.mul_sum, ←Finset.mul_sum, hs] at hsum
  have less : w+32*(e+1) ≤ n := hw
  have wn : w ≤ n := by omega
  have h₁ := Nat.mul_le_mul_left w wn
  have h₂ := Nat.mul_le_mul_right n less
  have hgap : w^2 + 32*(e+1)*n ≤ n^2 := by nlinarith only [h₁,h₂]
  have hgap' := Nat.mul_le_mul_right n hgap
  have en : 32*e ≤ n := by omega
  have hmn : (n+e)^2 ≤ 2*n^2 := by
    nlinarith only [Nat.mul_le_mul en en,Nat.mul_le_mul_left n en]
  have htail := (tailCost_le_rect n e).trans (Nat.mul_le_mul_left e hmn)
  have ha0 : a 0 ≤ n := by dsimp [w] at wn;omega
  have hbt : (∑ i, b i) ≤ n := by
    exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => Nat.le_add_left (b i) (a i))).trans_eq hs
  have hcross := Nat.mul_le_mul ha0 hbt
  have hn' := Nat.mul_le_mul_left n hn
  have hmono := Nat.pow_le_pow_left (Nat.le_add_right n e) 3
  nlinarith only [hsum,hgap',hmn,htail,hcross,hn',hmono]

end ClassTwoProfile

end

/- DescendantFamilies -/
section

namespace ClassTwoProfile

open Erdos1160.CentralLifts Erdos1160Growth.LayerMargin CategoryTheory
abbrev GroupId := Quotient (isIsomorphicSetoid FiniteGrp.{0})

def descendants (n e : ℕ) (S : Set GroupId) : Set GroupId :=
  {x | ∃ Q : FiniteGrp.{0}, Quotient.mk _ Q ∈ S ∧ x ∈ epiClasses 2 n e Q}

private theorem iso_of_equal {G H : FiniteGrp.{0}} (h : (Quotient.mk _ G : GroupId)=Quotient.mk _ H) :
    Nonempty ((G : Type) ≃* (H : Type)) := by
  obtain ⟨i⟩ := Quotient.exact h
  exact ⟨((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv⟩

theorem descendants_bound (n e : ℕ) (S : Set GroupId) (hfin : S.Finite)
    (horder : S ⊆ Erdos1160.Tables.orderClasses (2^n)) :
    (descendants n e S).ncard ≤ S.ncard*2^(tailCost n e) := by
  classical
  let _ : Fintype S := hfin.fintype
  have reps (x : S) : ∃ Q : FiniteGrp.{0}, Nat.card Q=2^n ∧ Quotient.mk _ Q = x.val := horder x.property
  choose H hH eqH using reps
  have hsub : descendants n e S ⊆ ⋃ x : S, epiClasses 2 n e (H x) := by
    rintro k ⟨Q,hq,G,hG,⟨f,hf⟩,rfl⟩
    let x : S := ⟨Quotient.mk _ Q,hq⟩
    obtain ⟨i⟩ := iso_of_equal (eqH x).symm
    exact Set.mem_iUnion_of_mem x ⟨G,hG,⟨i.toMonoidHom.comp f,i.surjective.comp hf⟩,rfl⟩
  have hf (i : S) : (epiClasses 2 n e (H i)).Finite :=
    (Erdos1160.Tables.orderClasses_finite (2^(n+e))).subset (by
      rintro _ ⟨G,h,_,rfl⟩; exact ⟨G,h,rfl⟩)
  calc
    _ ≤ (⋃ x : S, epiClasses 2 n e (H x)).ncard :=
      Set.ncard_le_ncard hsub (Set.finite_iUnion hf)
    _ ≤ ∑ x : S, (epiClasses 2 n e (H x)).ncard := Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _x : S, 2^(tailCost n e) := Finset.sum_le_sum (fun i _ => epi_classes_bound Nat.prime_two (hH i) _)
    _ = _ := by simp [Set.ncard, Nat.card_eq_fintype_card]

theorem profile_order {n : ℕ} (p : CompositionProfiles n) :
    listed p ⊆ Erdos1160.Tables.orderClasses (2^n) := by
  rintro _ ⟨G,⟨S⟩,rfl⟩
  refine ⟨G,?_,rfl⟩
  change Nat.card G = 2^n
  rw [S.card_group,card_factors]
  simp only [Finset.prod_pow_eq_pow_sum]
  rw [← pow_add,
    Composition.sum_blocksFun,Composition.sum_blocksFun]
  have hp := p.1.isLt
  congr 1
  omega

end ClassTwoProfile

end

/- TailProfiles -/
section

namespace ClassTwoProfile

open Erdos1160.CentralLifts Erdos1160Growth.LayerMargin CategoryTheory

def profileRoots {n : ℕ} (S : Finset (CompositionProfiles n)) : Set GroupId :=
  ⋃ p ∈ S, listed p

theorem profile_descendant_bound (n e : ℕ) (S : Finset (CompositionProfiles n))
    (h : ∀ p ∈ S, 27*(price p+2*n+tailCost n e)+10*(n+e)^2 ≤ 2*(n+e)^3) :
    (descendants n e (profileRoots S)).ncard^27 * 2^(10*(n+e)^2) ≤ 2^(2*(n+e)^3) := by
  classical
  have fin : (profileRoots S).Finite := S.finite_toSet.biUnion (fun _ _ => profileClasses_finite _ _)
  have horder : profileRoots S ⊆ Erdos1160.Tables.orderClasses (2^n) := by
    exact Set.iUnion₂_subset (fun p _ => profile_order p)
  have upper := descendants_bound n e (profileRoots S) fin horder
  have hr : (profileRoots S).ncard ≤ ∑ p ∈ S, 2^(price p) :=
    (S.set_ncard_biUnion_le listed).trans (Finset.sum_le_sum (fun _ _ => profileClasses_bound _ _))
  by_cases nonempt : S.Nonempty
  · obtain ⟨q,hq,hmax⟩ := S.exists_max_image price nonempt
    have hc : S.card ≤ 2^(2*n) := by
      have hcard := Finset.card_le_univ S
      rw [←Nat.card_eq_fintype_card] at hcard
      exact hcard.trans (count_composition_profiles n)
    have hp : (profileRoots S).ncard ≤ 2^(price q+2*n) := hr.trans (calc
      _ ≤ ∑ _p ∈ S, 2^(price q) := Finset.sum_le_sum (fun p hp => Nat.pow_le_pow_right (by decide) (hmax p hp))
      _ = S.card*2^(price q) := by simp
      _ ≤ 2^(2*n)*2^(price q) := Nat.mul_le_mul_right _ hc
      _ = _ := by rw [←Nat.pow_add,Nat.add_comm])
    have hd := upper.trans (Nat.mul_le_mul_right _ hp)
    rw [←Nat.pow_add] at hd
    calc
      _ ≤ (2^(price q+2*n+tailCost n e))^27*2^(10*(n+e)^2) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd 27)
      _ = 2^(27*(price q+2*n+tailCost n e)+10*(n+e)^2) := by rw [←Nat.pow_mul,←Nat.pow_add,Nat.mul_comm _ 27]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (h q hq)
  · have hz : (profileRoots S).ncard=0 := Nat.eq_zero_of_le_zero (hr.trans_eq (by simp [Finset.not_nonempty_iff_eq_empty.mp nonempt]))
    simp only [hz,Nat.zero_mul,Nat.le_zero] at upper
    simp [upper]

def wideProfiles (n e : ℕ) : Finset (CompositionProfiles n) := Finset.univ.filter
  (fun p => p.2.1.length+p.2.2.length+32*(e+1) ≤ n)

theorem wide_profiles_budget (n e : ℕ) (hn : 200 ≤ n) (p : CompositionProfiles n)
    (h : p ∈ wideProfiles n e) :
    27*(price p+2*n+tailCost n e)+10*(n+e)^2 ≤ 2*(n+e)^3 := by
  let a := p.2.1.blocksFun
  let b := p.2.2.blocksFun
  let u (i : Fin (n+1)) := width a i.val
  let v (i : Fin (n+1)) := width b i.val
  have hp := Nat.le_of_lt_succ p.1.isLt
  have ha (i) : a i ≤ n := (p.2.1.blocksFun_le i).trans hp
  have hb (i) : b i ≤ n := (p.2.2.blocksFun_le i).trans (Nat.sub_le ..)
  have su : (∑ i, u i) = p.1.val := (sum_width a ha).trans p.2.1.sum_blocksFun
  have sv : (∑ i, v i) = n-p.1.val := (sum_width b hb).trans p.2.2.sum_blocksFun
  have hs : (∑ i, (u i+v i))=n := by rw [Finset.sum_add_distrib,su,sv];omega
  have h0 : u 0 = p.2.1.length := width_zero a p.2.1.one_le_blocksFun
  have h1 : v 0 = p.2.2.length := width_zero b p.2.2.one_le_blocksFun
  have hw : u 0+v 0+32*(e+1) ≤ n := by rw [h0,h1];exact (Finset.mem_filter.mp h).2
  have H := wide_defect_budget n e hn u v (fun _ _ hi => width_antitone a hi)
    (fun _ _ hi => width_antitone b hi) hs hw
  change 27*(cost a b+2*n+tailCost n e)+10*(n+e)^2 ≤ 2*(n+e)^3
  rw [cost_eq_width a b ha hb,←sum_width b hb]
  rw [h0] at H
  exact H

/-- All higher-class groups admitting any quotient of order 2^n with the indicated
abelian presentation profile, allowing a kernel of order 2^e and arbitrary class. -/
theorem deep_descendants_upper (n e : ℕ) (hn : 200 ≤ n) :
    (descendants n e (profileRoots (wideProfiles n e))).ncard^27*2^(10*(n+e)^2) ≤ 2^(2*(n+e)^3) :=
  profile_descendant_bound n e _ (wide_profiles_budget n e hn)

end ClassTwoProfile

end

/- FourBits -/
section

namespace Erdos1160Growth.LayerMargin

private theorem layer_with_pairs (d s : ℕ) :
    54*(s*d.choose 2)+27*(d*s) ≤ 4*(d+s)^3 := by
  have hc : 2*d.choose 2 + d = d*d := by
    rw [Nat.choose_two_right,Nat.mul_comm 2,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self d)]
    cases d <;> simp <;> ring
  have h : 27*s*d^2 ≤ 4*(d+s)^3 := by
    zify
    nlinarith only [mul_nonneg (sq_nonneg ((d:ℤ)-2*s)) (show (0:ℤ) ≤ 4*d+s by positivity)]
  nlinarith only [h,congrArg (s*·) hc]

private theorem cubes_merge {ι : Type*} (I : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ I, f i^3) ≤ (∑ i ∈ I, f i)^3 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    nlinarith only [ih, Nat.zero_le (f i^2*(∑ j ∈ I, f j)), Nat.zero_le (f i*(∑ j ∈ I, f j)^2)]

private theorem base_four {n : ℕ} (hn : 256 ≤ n) (d s : Fin (n+1)→ℕ)
    (hsize : ∑ i, (d i+s i) = n) (hbase : 4 ≤ d 0+s 0) (htail : d 0+s 0+4 ≤ n) :
    216*((∑ i, s i*(d i).choose 2)+d 0*(∑ i, s i))+161*n^2 ≤ 16*n^3+752*n := by
  classical
  let I := (Finset.univ : Finset (Fin (n+1)))
  let u (i : Fin (n+1)) := d i+s i
  let t := ∑ i ∈ I.erase 0, u i
  let v := u 0
  have hi : 0∈I := Finset.mem_univ _
  have htot : v+t=n := (Finset.add_sum_erase I u hi).trans hsize
  have hp : 4*n ≤ v*t+16 := by
    have hv : 4 ≤ v := hbase
    have ht : 4 ≤ t := by change v+4 ≤ n at htail; omega
    obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le hv
    obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le ht
    rw [←htot,hx,hy]
    nlinarith only [Nat.zero_le (x*y)]
  let cubes := ∑ i, u i^3
  let alt := ∑ i,s i*(d i).choose 2
  have hcube : cubes+3*n*(v*t) ≤ n^3 := by
    have he := cubes_merge (I.erase 0) u
    change _ ≤ t^3 at he
    have H : cubes+3*(v+t)*(v*t) ≤ (v+t)^3 := by
      change (∑ i∈I,u i^3)+_ ≤ _
      rw [← Finset.add_sum_erase I (fun i=>u i^3) hi]
      change v^3+_+_≤_
      nlinarith only [he]
    rwa [htot] at H
  have hsum : 54*alt+27*(d 0*s 0) ≤ 4*cubes := by
    have hsingle : d 0*s 0 ≤ ∑ i, d i*s i := Finset.single_le_sum (fun i _=>Nat.zero_le (d i*s i)) (Finset.mem_univ (0 : Fin (n+1)))
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left 27 hsingle) (54*alt)).trans
    change 54*(∑i,s i*(d i).choose 2)+27*(∑i,d i*s i) ≤ 4*∑i,u i^3
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>layer_with_pairs (d i) (s i))
  have htail_s : (∑i∈I.erase 0,s i) ≤ t := Finset.sum_le_sum (fun i _=>Nat.le_add_left _ _)
  have hvd : d 0 ≤ v := Nat.le_add_right _ _
  have hs : (∑ i,s i) ≤ s 0+t := by
    change (∑i∈I,s i) ≤ _
    rw [←Finset.add_sum_erase I s hi]
    omega
  have hpow : d 0*(∑i,s i) ≤ d 0*s 0+v*t := by
    have h := Nat.mul_le_mul_left (d 0) hs
    rw [Nat.mul_add] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right t hvd) _)
  have hcross : 4*(d 0*s 0) ≤ n^2 := by
    apply le_trans (b := v^2)
    · dsimp only [v,u]
      zify
      nlinarith only [sq_nonneg ((d 0:ℤ)-s 0)]
    · exact Nat.pow_le_pow_left (show v ≤ n by omega) 2
  have habs : 216*(v*t) ≤ n*(v*t) := Nat.mul_le_mul_right _ (by omega)
  have hh := Nat.mul_le_mul_left (47*n) hp
  change 216*(alt + d 0*(∑i,s i))+161*n^2 ≤ _
  nlinarith only [hsum,hcube,hcross,hpow,habs,hh]

theorem four_bit_window {n : ℕ} (hn : 256 ≤ n) (d s : Fin (n+1)→ℕ)
    (hd : Antitone d) (hsize : ∑ i,(d i+s i) = n) (htail : d 0+s 0+4 ≤ n) :
    27*((∑ i,s i*(d i).choose 2)+d 0*(∑ i,s i)+2*n+n*(n+1)/2)+10*(n+1)^2 ≤ 2*(n+1)^3 := by
  have hdiv := Nat.mul_div_le (n*(n+1)) 2
  have hquad := Nat.mul_le_mul_left n hn
  by_cases hb : 4 ≤ d 0+s 0
  · have h := base_four hn d s hsize hb htail
    nlinarith only [h,hdiv,hquad,hn]
  · have htop : d 0 ≤ 3 := by omega
    have hs : (∑ i,s i) ≤ n := by
      exact (Finset.sum_le_sum (fun i _ => Nat.le_add_left (s i) (d i))).trans_eq hsize
    have hc (i : Fin (n+1)) : (d i).choose 2 ≤ 3 := by
      have hi : d i ≤ 3 := (hd (Fin.zero_le i)).trans htop
      exact (Nat.choose_le_choose 2 hi).trans (by decide)
    have hsum : (∑i,s i*(d i).choose 2) ≤ 3*n := by
      apply le_trans (b:=∑i,3*s i)
      · exact Finset.sum_le_sum (fun i _ => (Nat.mul_le_mul_left _ (hc i)).trans_eq (mul_comm _ _))
      · rw [←Finset.mul_sum]
        exact Nat.mul_le_mul_left 3 hs
    have hpow := Nat.mul_le_mul htop hs
    have hcub := Nat.mul_le_mul_left (n^2) hn
    nlinarith only [hsum,hpow,hdiv,hquad,hcub,hn]

end Erdos1160Growth.LayerMargin

end

/- OneBitDeep -/
section

namespace ClassTwoProfile

open Erdos1160Growth.LayerMargin Erdos1160.CentralLifts

/-- Four excess cyclic-height bits in a central presentation pay for all twists
of one central extension by C₂ and for both ordered cyclic profiles. -/
theorem one_bit_deep_price (n : ℕ) (hn : 256 ≤ n) (p : CompositionProfiles n)
    (hp : p.2.1.length + p.2.2.length + 4 ≤ n) :
    27*(price p+2*n+tailCost n 1)+10*(n+1)^2 ≤ 2*(n+1)^3 := by
  let e := p.2.1.blocksFun
  let b := p.2.2.blocksFun
  let u (t : Fin (n+1)) := width e t.val
  let v (t : Fin (n+1)) := width b t.val
  have ha : p.1.val ≤ n := Nat.le_of_lt_succ p.1.isLt
  have he (i) : e i ≤ n := (p.2.1.blocksFun_le i).trans ha
  have hb (i) : b i ≤ n := (p.2.2.blocksFun_le i).trans (Nat.sub_le n p.1.val)
  have su : (∑ t, u t) = p.1.val := (sum_width e he).trans p.2.1.sum_blocksFun
  have sv : (∑ t, v t) = n-p.1.val := (sum_width b hb).trans p.2.2.sum_blocksFun
  have hsize : (∑ t, (u t + v t)) = n := by rw [Finset.sum_add_distrib,su,sv]; omega
  have hz : u 0 = p.2.1.length := width_zero e p.2.1.one_le_blocksFun
  have hz' : v 0 = p.2.2.length := width_zero b p.2.2.one_le_blocksFun
  have hlarge : u 0+v 0+4 ≤ n := by rw [hz,hz']; exact hp
  have h := four_bit_window hn u v (fun _ _ hij=>width_antitone e hij) hsize hlarge
  change 27*(cost e b+2*n+tailCost n 1)+10*(n+1)^2 ≤ _
  rw [cost_eq_width e b he hb, ←sum_width b hb]
  rw [hz] at h
  simpa only [tailCost,add_zero,zero_add,Nat.choose_two_right] using h

end ClassTwoProfile

end

/- FourBitDescendants -/
section

namespace ClassTwoProfile
open Erdos1160Growth.LayerMargin

def fourBitProfiles (n : ℕ) : Finset (CompositionProfiles n) := Finset.univ.filter
  (fun p => p.2.1.length+p.2.2.length+4 ≤ n)

/-- All groups admitting an order-two kernel and a quotient described by any
class-two cyclic-factor profile with at least four excess binary dimensions. -/
theorem four_bit_descendants (n : ℕ) (hn : 256 ≤ n) :
    (descendants n 1 (profileRoots (fourBitProfiles n))).ncard^27*2^(10*(n+1)^2) ≤ 2^(2*(n+1)^3) :=
  profile_descendant_bound n 1 _ (fun p hp => one_bit_deep_price n hn p ((Finset.mem_filter.mp hp).2))

end ClassTwoProfile

end

/- FrattiniFactors -/
section

namespace ClassTwoProfile

open CategoryTheory Erdos1160Growth.LayerMargin Erdos1160Growth.LowerTriangularUpper

theorem elementary_factors {A : Type} [Group A] {d : ℕ} {e : Fin d → ℕ}
    (f : A ≃* Factors e) (he : ∀ i,0 < e i) (h : ∀ x : A,x*x=1) :
    ∀ i,e i=1 := by
  intro i
  have huv := congrArg f (h (f.symm (gen e i)))
  rw [map_mul,map_one,f.apply_symm_apply] at huv
  have hi := congrFun huv i
  change (gen e i i) * (gen e i i) = 1 at hi
  simp only [gen,Pi.mulSingle_eq_same] at hi
  change (1:ZMod (2^(e i)))+1=0 at hi
  have htwo : ((2 : ℕ) : ZMod (2^(e i))) = (1:ZMod (2^(e i)))+1 := by norm_num
  have hdvd : 2^(e i) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2^(e i))).mp (htwo.trans hi)
  have hpow : 2^(e i) ≤ 2^1 := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  exact le_antisymm ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow) (he i)

/-- Cyclic coordinates for a group with central Frattini subgroup. The output
records its square-subgroup cardinality and the elementary quotient heights. -/
theorem exists_central_frattini_coords (n : ℕ) (G : FiniteGrp.{0}) (hc : Nat.card G=2^n)
    (hcenter : frattini G ≤ Subgroup.center G) :
    ∃ (p : CompositionProfiles n) (S : Data G p.2.1.blocksFun p.2.2.blocksFun),
      S.incl.range = frattini G ∧ (∀ i,p.2.1.blocksFun i=1) ∧
      p.2.1.length=p.1.val ∧
      Nat.card (squareCore (frattini G)) = 2^(n-p.1.val-p.2.2.length) := by
  let K := frattini G
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hcenter y.property) x.val) }
  have hsq (x : G ⧸ K) : x*x=1 := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (squares_le_frattini hc (Subgroup.subset_closure ⟨u,rfl⟩))
  have hinv (x : G ⧸ K) : x⁻¹=x := inv_eq_of_mul_eq_one_left (hsq x)
  let _ : CommGroup (G ⧸ K) := { (inferInstance : Group (G ⧸ K)) with
    mul_comm := fun x y => by
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv] }
  obtain ⟨p,⟨fu⟩,⟨fv⟩⟩ := subgroup_profiles n G hc K (fun _ _=>mul_comm _ _) (fun _ _=>mul_comm _ _)
  let S := Data.ofCentralSubgroup K hcenter fv fu
  have hi : S.incl.range=K := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact (fv.symm w).property
    · intro hx
      exact ⟨fv ⟨x,hx⟩,congrArg Subtype.val (fv.symm_apply_apply ⟨x,hx⟩)⟩
  have he := elementary_factors fu p.2.1.one_le_blocksFun hsq
  have hlen := p.2.1.sum_blocksFun
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hlen
  refine ⟨p,S,hi,he,hlen,?_⟩
  have h := squareCore_size fv p.2.2.one_le_blocksFun
  rw [Composition.sum_blocksFun] at h
  apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos p.2.2.length)
  rw [h,←Nat.pow_add,Nat.sub_add_cancel p.2.2.length_le]

def fourFrattiniClasses (n : ℕ) : Set GroupId :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^n ∧ frattini G ≤ Subgroup.center G ∧
    16 ≤ Nat.card (squareCore (frattini G))}

theorem four_frattini_subset (n : ℕ) : fourFrattiniClasses n ⊆ profileRoots (fourBitProfiles n) := by
  rintro _ ⟨G,⟨hc,hcent,hbig⟩,rfl⟩
  obtain ⟨p,S,_,_,h₁,h₂⟩ := exists_central_frattini_coords n G hc hcent
  have h₃ : 2^4 ≤ 2^(n-p.1.val-p.2.2.length) := h₂ ▸ hbig
  have h₄ := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h₃
  have hp : p ∈ fourBitProfiles n := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  exact Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hp ⟨G,⟨S⟩,rfl⟩)

theorem four_frattini_descendants (n : ℕ) (hn : 256 ≤ n) :
    (descendants n 1 (fourFrattiniClasses n)).ncard^27*2^(10*(n+1)^2) ≤ 2^(2*(n+1)^3) := by
  have hsub : descendants n 1 (fourFrattiniClasses n) ⊆ descendants n 1 (profileRoots (fourBitProfiles n)) := by
    rintro _ ⟨H,hH,h⟩
    exact ⟨H,four_frattini_subset n hH,h⟩
  have hf : (descendants n 1 (profileRoots (fourBitProfiles n))).Finite :=
    (Erdos1160.Tables.orderClasses_finite (2^(n+1))).subset (by
      rintro _ ⟨H,_,G,hk,_,rfl⟩
      exact ⟨G,hk,rfl⟩)
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Set.ncard_le_ncard hsub hf) 27)).trans
    (four_bit_descendants n hn)

end ClassTwoProfile

end

/- ThreePrice -/
section

namespace ClassTwoProfile

private theorem width_cost {r : ℕ} (b : Fin r → ℕ) (hp : ∀ i,0 < b i) :
    r+width b 1 ≤ ∑ i,b i := by
  have h (i : Fin r) : 1+(if 1 < b i then 1 else 0) ≤ b i := by
    have := hp i
    split <;> omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i)
  simpa [Finset.sum_add_distrib,Finset.sum_boole,width] using hs

private theorem single_high {r : ℕ} (b : Fin r→ℕ) (hp : ∀ i,0 < b i)
    (he : (∑ i,b i)=r+1) (k : Fin r) : b k ≤ 2 := by
  by_contra! h
  have rel (i : Fin r) : 1+(if i=k then 2 else 0) ≤ b i := by
    by_cases hi : i=k
    · subst i
      simp; omega
    · simp [hi]; exact hp i
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => rel i)
  simp [Finset.sum_add_distrib,he] at hs

lemma three_price_le {n : ℕ} (hn : 1 ≤ n) (p : Erdos1160Growth.LayerMargin.CompositionProfiles n)
    (he' : p.1.val = p.2.1.length+2) (hb' : n-p.1.val=p.2.2.length+1) :
    price p ≤ p.2.2.length*(p.2.1.length*(p.2.1.length-1)/2) +
      p.2.1.length*(p.2.2.length+1)+1 := by
  let e := p.2.1.blocksFun
  let b := p.2.2.blocksFun
  let d := p.2.1.length
  let s := p.2.2.length
  have he : (∑i,e i)=d+2 := p.2.1.sum_blocksFun.trans he'
  have hb : (∑i,b i)=s+1 := p.2.2.sum_blocksFun.trans hb'
  have h0e : width e 0 = d := width_zero e p.2.1.one_le_blocksFun
  have h0b : width b 0 = s := width_zero b p.2.2.one_le_blocksFun
  have h1e : width e 1 ≤ 2 := by have hh := width_cost e p.2.1.one_le_blocksFun; rw [he] at hh; change d+_ ≤ d+2 at hh; omega
  have h1b : width b 1 ≤ 1 := by have hh := width_cost b p.2.2.one_le_blocksFun; rw [hb] at hh; change s+_ ≤ s+1 at hh; omega
  have h1 : (width e 1)*(width e 1-1)/2 ≤ 1 := by
    have hh : (width e 1).choose 2 ≤ (2 : ℕ).choose 2 := Nat.choose_le_choose 2 h1e
    simpa [Nat.choose_two_right] using hh
  have hbig (t : ℕ) (ht : 2 ≤ t) : width b t = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro j _
    exact not_lt.mpr ((single_high b p.2.2.one_le_blocksFun hb j).trans ht)
  let g (t : Fin (n+1)) := width b t.val*((width e t.val)*(width e t.val-1)/2)
  let base := s*(d*(d-1)/2)
  let one : Fin (n+1) := ⟨1,by omega⟩
  have bound (t : Fin (n+1)) : g t ≤ (if t=0 then base else 0)+(if t=one then 1 else 0) := by
    rcases eq_or_ne t 0 with rfl|ht
    · simp [g,base,h0b,h0e]
    · rcases eq_or_ne t one with rfl|ht'
      · simp only [if_neg ht,if_pos rfl,zero_add]
        exact (Nat.mul_le_mul h1b h1).trans_eq (by decide)
      · have htwo : 2 ≤ t.val := by
          have h0 : t.val≠0 := fun h=>ht (Fin.ext h)
          have h1 : t.val≠1 := fun h=>ht' (Fin.ext h)
          omega
        simp [g,hbig t.val htwo]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>bound i)
  have hall : (∑ t,g t) ≤ base+1 := by simpa [Finset.sum_add_distrib] using hsum
  have hemax (i) : e i ≤ n := (p.2.1.blocksFun_le i).trans (Nat.le_of_lt_succ p.1.isLt)
  have hbmax (i) : b i ≤ n := (p.2.2.blocksFun_le i).trans (Nat.sub_le n _)
  change cost e b ≤ base+d*(s+1)+1
  rw [cost_eq_width e b hemax hbmax,hb]
  change (∑t,g t)+d*(s+1) ≤ base+d*(s+1)+1
  omega

end ClassTwoProfile

end

/- DerivedRigidity -/
section

namespace ClassTwoProfile.Data

open scoped commutatorElement
open CentralKernelCount

variable {E : Type} [Group E] {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ} (S : Data E e b)

include S in
def commTo (y : E) : E→*E where
  toFun x := ⁅x,y⁆
  map_one' := by simp
  map_mul' x z := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hc := Subgroup.mem_center_iff.mp (S.center_comm z y) x
    rw [hc,mul_inv_cancel_right]
    exact Subgroup.mem_center_iff.mp (S.center_comm x y) _

lemma extend_comm_mem (C : Subgroup E) (y : E) (h : ∀ i,⁅S.x i,y⁆ ∈ C) (x : E) :
    ⁅x,y⁆ ∈ C := by
  let K := C.comap (S.commTo y)
  have hk : K=⊤ := by
    apply top_unique
    rw [←S.adjoin_eq]
    apply sup_le
    · intro w hw
      change ⁅w,y⁆ ∈ C
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (S.cent hw) _).symm]
      exact C.one_mem
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i,rfl⟩
      exact h i
  exact (show x∈K from hk ▸ trivial)

lemma derived_le (C : Subgroup E) (h : ∀ i j, ⁅S.x i,S.x j⁆ ∈ C) : commutator E ≤ C := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  apply S.extend_comm_mem C y _ x
  intro i
  rw [←commutatorElement_inv]
  exact C.inv_mem (S.extend_comm_mem C (S.x i) (fun j=>h j i) y)

noncomputable def vector (l : Tri d) : Factors b := (S.commCode (row l) (col l)).val

/-- If the central kernel is the derived subgroup, its commutator coordinates
generate every element of the kernel, including in mixed-exponent profiles. -/
lemma vector_dense (h : S.incl.range=commutator E) :
    Subgroup.closure (Set.range S.vector) = ⊤ := by
  let K := Subgroup.closure (Set.range S.vector)
  let C := K.map S.incl
  have hlow (i j : Fin d) (hj : j < i) : ⁅S.x i,S.x j⁆ ∈ C := by
    let l : Tri d := ⟨i,⟨j.val,hj⟩⟩
    exact ⟨S.vector l,Subgroup.subset_closure ⟨l,rfl⟩,S.commCode_spec i j⟩
  have hpair (i j : Fin d) : ⁅S.x i,S.x j⁆ ∈ C := by
    rcases lt_trichotomy j i with hji|rfl|hij
    · exact hlow i j hji
    · simp
    · rw [←commutatorElement_inv]
      exact C.inv_mem (hlow j i hij)
  have hall := S.derived_le C hpair
  apply top_unique
  intro w _
  have hin : S.incl w ∈ commutator E := h ▸ (show _ ∈ S.incl.range from ⟨w,rfl⟩)
  obtain ⟨z,hz,hz'⟩ := hall hin
  exact (S.inj hz') ▸ hz

def relabel (u : Factors b ≃* Factors b) : Data E e b where
  incl := S.incl.comp u.symm.toMonoidHom
  inj := S.inj.comp u.symm.injective
  cent := by rintro _ ⟨x,rfl⟩; exact S.cent ⟨u.symm x,rfl⟩
  proj := S.proj
  onto := S.onto
  ker_eq := by
    rw [S.ker_eq]
    ext w
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨u a,by simp⟩
    · rintro ⟨a,rfl⟩
      exact ⟨u.symm a,rfl⟩
  x := S.x
  x_spec := S.x_spec

lemma relabel_vector (u : Factors b ≃* Factors b) (l : Tri d) :
    (S.relabel u).vector l = u (S.vector l) := by
  apply (S.relabel u).inj
  calc
    _ = ⁅S.x (row l),S.x (col l)⁆ := (S.relabel u).commCode_spec _ _
    _ = S.incl (S.vector l) := (S.commCode_spec _ _).symm
    _ = _ := by change _ = S.incl (u.symm (u _)); simp

lemma relabel_code_injective (h : S.incl.range = commutator E) :
    Function.Injective (fun u : Factors b ≃* Factors b => (S.relabel u).code) := by
  intro u v he
  have hv (l : Tri d) : u (S.vector l) = v (S.vector l) := by
    rw [← S.relabel_vector u,←S.relabel_vector v]
    exact congrArg Subtype.val (congrFun (congrArg Prod.snd he) l)
  have hhom : u.toMonoidHom = v.toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense (S.vector_dense h) (fun _ ⟨l,hl⟩ => hl ▸ hv l)
  exact MulEquiv.ext fun x => DFunLike.congr_fun hhom x

end ClassTwoProfile.Data

namespace ClassTwoProfile

open CategoryTheory

def derivedProfiles {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | ∃ S : Data E e b, S.incl.range = commutator E}

theorem derived_profile_upper {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) :
    (derivedProfiles e b).ncard * Nat.card (Factors b ≃* Factors b) ≤ 2^(cost e b) := by
  classical
  let C := derivedProfiles e b
  let G (c : C) : FiniteGrp := c.property.choose
  let S (c : C) : Data (G c) e b := c.property.choose_spec.1.choose
  have hS (c : C) : (S c).incl.range = commutator (G c) := c.property.choose_spec.1.choose_spec
  let f (cu : C × (Factors b ≃* Factors b)) := ((S cu.1).relabel cu.2).code
  have hf : Function.Injective f := by
    rintro ⟨c,u⟩ ⟨k,v⟩ eq
    have ⟨eG⟩ := ((S c).relabel u).equiv_of_code ((S k).relabel v) eq
    have same : c=k := by
      apply Subtype.ext
      rw [← c.property.choose_spec.2, ← k.property.choose_spec.2]
      exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
        (MulEquiv.toGrpIso (X := (G c).toGrp) (Y := (G k).toGrp) eG)⟩
    subst k
    exact Prod.ext rfl ((S c).relabel_code_injective (hS c) eq)
  calc
    _ = Nat.card (C × (Factors b ≃* Factors b)) := by rw [Nat.card_prod]; rfl
    _ ≤ Nat.card (Code e b) := Nat.card_le_card_of_injective f hf
    _ = _ := card_code e b

end ClassTwoProfile

end

/- ThreeCover -/
section

namespace ClassTwoProfile

open CategoryTheory Erdos1160Growth.LayerMargin

def derivedCandidates (n : ℕ) : Finset (CompositionProfiles n) :=
  Finset.univ.filter fun p => p.2.1.length+p.2.2.length+4 ≤ n ∨
    (p.1.val=p.2.1.length+2 ∧ n-p.1.val=p.2.2.length+1)

abbrev derivedListed {n : ℕ} (p : CompositionProfiles n) := derivedProfiles p.2.1.blocksFun p.2.2.blocksFun

theorem derived_subset {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) : derivedProfiles e b ⊆ profileClasses e b := by
  rintro _ ⟨G,⟨S,_⟩,rfl⟩
  exact ⟨G,⟨S⟩,rfl⟩

theorem derived_cover (n : ℕ) : noncentralClasses n ⊆ ⋃ p ∈ derivedCandidates n, derivedListed p := by
  rintro _ ⟨G,⟨hcard,hcenter,hbad⟩,rfl⟩
  let K := commutator G
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hcenter y.property) x.val) }
  let _ : CommGroup (G ⧸ K) := Abelianization.commGroup G
  obtain ⟨p,⟨fu⟩,⟨fv⟩⟩ := subgroup_profiles n G hcard K (fun _ _=>mul_comm _ _) (fun _ _=>mul_comm _ _)
  let S := Data.ofCentralSubgroup K hcenter fv fu
  have hderived : S.incl.range=K := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact (fv.symm w).property
    · intro hx
      exact ⟨fv ⟨x,hx⟩,congrArg Subtype.val (fv.symm_apply_apply ⟨x,hx⟩)⟩
  have hdeep : p∈derivedCandidates n := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    obtain ⟨⟨i,j,hij,hi,hj⟩,⟨k,hk⟩⟩ := S.high_indices hbad
    have h₁ := Data.excess_of_two p.2.1.blocksFun p.2.1.one_le_blocksFun hij hi hj
    have h₂ := Data.excess_of_high p.2.2.blocksFun p.2.2.one_le_blocksFun hk
    simp only [Composition.sum_blocksFun] at h₁ h₂
    have ha := p.1.isLt
    omega
  exact Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hdeep ⟨G,⟨S,hderived⟩,rfl⟩)

end ClassTwoProfile

end

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

/- KernelAuto -/
section

namespace ClassTwoProfile

theorem kernel_automorphisms_lower {s : ℕ} (b : Fin s → ℕ)
    (hb : ∀ i, 0 < b i) (hs : (∑ i,b i) = s+1) :
    2^((s-1)*(s-2)) ≤ Nat.card (Factors b ≃* Factors b) := by
  classical
  cases s with
  | zero => simp at hs
  | succ n =>
    obtain ⟨i,hi⟩ : ∃ i, 2 ≤ b i := by
      by_contra! h
      have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun j _ => (show b j ≤ 1 by have := h j; omega))
      simp at hsum
      omega
    have hrest (j : {j : Fin (n+1) // j ≠ i}) : b j = 1 := by
      have := hb j
      by_contra! h
      have h₂ := Data.excess_of_two b hb j.property.symm hi (show 2 ≤ b j by omega)
      omega
    let t := finSuccAboveEquiv i
    let split : Factors b ≃* Cyc (b i) × ((j : {j : Fin (n+1) // j ≠ i}) → Cyc (b j)) :=
      { Equiv.piSplitAt i (fun j => Cyc (b j)) with map_mul' := by intro x y; rfl }
    let reindex : ((j : {j : Fin (n+1) // j ≠ i}) → Cyc (b j)) ≃*
        ((j : Fin n) → Cyc (b (t j))) :=
      { Equiv.piCongrLeft' _ t.symm with map_mul' := by intro x y; rfl }
    let change : ((j : Fin n) → Cyc (b (t j))) ≃* (Fin n → Multiplicative (ZMod 2)) :=
      MulEquiv.piCongrRight fun j => by change Cyc (b (t j)) ≃* _; rw [hrest (t j)]; exact .refl _
    let tags : (Fin n → Multiplicative (ZMod 2)) ≃* Multiplicative (OrbitUp.V n) :=
      { toFun := fun f => Multiplicative.ofAdd (fun j => (f j).toAdd)
        invFun := fun f j => Multiplicative.ofAdd (f.toAdd j)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    let e := split.trans ((MulEquiv.refl (Cyc (b i))).prodCongr ((reindex.trans change).trans tags))
    let act (T : OrbitUp.L n) := e.trans
      (((MulEquiv.refl (Cyc (b i))).prodCongr (AddEquiv.toMultiplicative T.toAddEquiv)).trans e.symm)
    have hinj : Function.Injective act := by
      intro T S he
      apply LinearEquiv.ext
      intro v
      have hv := congrArg (fun f : Factors b ≃* Factors b =>
        (e (f (e.symm (1,Multiplicative.ofAdd v)))).2.toAdd) he
      simp only [act,MulEquiv.trans_apply,MulEquiv.apply_symm_apply] at hv
      exact hv
    simpa using (OrbitUp.gl_lower n).trans (Nat.card_le_card_of_injective act hinj)

end ClassTwoProfile

end

/- LayerThree -/
section

namespace Erdos1160Growth.LayerMargin

private theorem cubic_delta (d s : ℤ) (hd : 0 ≤ d) (hs : 0 ≤ s) (hsize : 4000 ≤ d+s+3) :
    0 ≤ 4*d^3-15*d^2*s+d^2+12*d*s^2-25*d*s-319*d+4*s^3+55*s^2-427*s-766 := by
  by_cases h : 2*s ≤ d
  · let z := d-2*s
    have hz : 0 ≤ z := by dsimp [z]; omega
    have hdz : d=2*s+z := by dsimp [z]; ring
    have hsum : 1200 ≤ s+z := by omega
    have hsquare := mul_nonneg (show 0 ≤ s+z-1200 by omega) (show 0 ≤ s+z by omega)
    have hmove := mul_nonneg hs (sq_nonneg (18*z-23))
    rw [hdz]
    nlinarith only [hsquare,hmove,hsum,hs,hz,sq_nonneg s,
      mul_nonneg hz (sq_nonneg z)]
  · let z := 2*s-d
    have hz : 0 ≤ z := by dsimp [z]; omega
    have hdz : 2*s=d+z := by dsimp [z]; ring
    have hsum : 2000 ≤ d+z := by omega
    have hsq := mul_nonneg (show 0 ≤ d+z-2000 by omega) (show 0 ≤ d+z by omega)
    have scaled :
        0 ≤ 9*d^2+60*d*z+55*z^2+18*d*z^2+2*z^3-2130*d-854*z-3064 := by
      nlinarith only [hsq,hsum,hd,hz,mul_nonneg hd hz,sq_nonneg z,mul_nonneg hd (sq_nonneg z),
        mul_nonneg hz (sq_nonneg z)]
    have eq :
        4*(4*d^3-15*d^2*s+d^2+12*d*s^2-25*d*s-319*d+4*s^3+55*s^2-427*s-766)
        = 9*d^2+60*d*z+55*z^2+18*d*z^2+2*z^3-2130*d-854*z-3064 := by
      dsimp [z]
      ring
    omega

/-- The three-extra-layer case with the output-basis saving. The two linear
dimensions per order parameter pay for the paired composition profiles. -/
theorem three_layer_margin {d s n price : ℕ} (hn : n=d+s+3) (hl : 4000 ≤ n)
    (hp : 2*price ≤ s*d*(d-1)+2*d*(s+1)+2) :
    27*(price+2*n+n*(n+1)/2)+10*(n+1)^2 ≤ 2*(n+1)^3+27*((s-1)*(s-2)) := by
  have hdiv := Nat.mul_div_le (n*(n+1)) 2
  have hpred : d*(d-1)+d=d^2 := by cases d <;> simp <;> ring
  have hpred' : s*d*(d-1)+s*d=s*d^2 := by nlinarith only [congrArg (s*·) hpred]
  have hs : s^2 ≤ (s-1)*(s-2)+3*s := by
    cases s with
    | zero => simp
    | succ v =>
      cases v with
      | zero => decide
      | succ v =>
        have h : v+1+1-2=v := by omega
        simp only [Nat.add_one_sub_one,h]
        nlinarith only
  subst n
  have hc := cubic_delta (d:ℤ) (s:ℤ) (by positivity) (by positivity) (by exact_mod_cast hl)
  zify at hdiv hp hpred' hs ⊢
  nlinarith only [hdiv,hp,hpred',hs,hc]

theorem three_layer_margin_of_price {d s n price : ℕ} (hn : n=d+s+3) (hl : 4000 ≤ n)
    (hp : price ≤ s*(d*(d-1)/2)+d*(s+1)+1) :
    27*(price+2*n+n*(n+1)/2)+10*(n+1)^2 ≤ 2*(n+1)^3+27*((s-1)*(s-2)) := by
  apply three_layer_margin hn hl
  have hdiv := Nat.mul_le_mul_left s (Nat.mul_div_le (d*(d-1)) 2)
  nlinarith only [hp,hdiv]

end Erdos1160Growth.LayerMargin

end

/- DerivedDescendants -/
section

namespace ClassTwoProfile

open Erdos1160Growth.LayerMargin Erdos1160.CentralLifts

private theorem power_budget (C P A u k N : ℕ) (hc : C*2^A ≤ 2^P)
    (hm : 27*(P+u)+k ≤ N+27*A) :
    (C*2^u)^27 * 2^k ≤ 2^N := by
  have h : (C*2^u)^27*2^k*(2^A)^27 ≤ 2^N*(2^A)^27 := calc
    _ = (C*2^A)^27*(2^u)^27*2^k := by ring
    _ ≤ (2^P)^27*(2^u)^27*2^k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc 27))
    _ = 2^(27*(P+u)+k) := by
      rw [←pow_mul,←pow_mul,←pow_add,←pow_add]
      congr 1
      ring
    _ ≤ 2^(N+27*A) := Nat.pow_le_pow_right (by decide) hm
    _ = _ := by rw [pow_add,←pow_mul,Nat.mul_comm 27]
  exact Nat.le_of_mul_le_mul_right h (Nat.pow_pos (Nat.pow_pos (by decide)))

lemma derived_profile_descendant_budget (n : ℕ) (hn : 4000 ≤ n) (p : CompositionProfiles n)
    (hp : p∈derivedCandidates n) :
    ((derivedListed p).ncard*2^(2*n+tailCost n 1))^27 * 2^(10*(n+1)^2) ≤ 2^(2*(n+1)^3) := by
  let c := (derivedListed p).ncard
  let d := p.2.1.length
  let s := p.2.2.length
  rcases (Finset.mem_filter.mp hp).2 with deep | ⟨hx,hy⟩
  · have hc : c ≤ 2^(price p) :=
      (Set.ncard_le_ncard (derived_subset _ _) (profileClasses_finite _ _)).trans (profileClasses_bound _ _)
    refine power_budget c (price p) 0 (2*n+tailCost n 1) (10*(n+1)^2) (2*(n+1)^3) ?_ ?_
    · simpa using hc
    · simpa only [Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using one_bit_deep_price n (by omega) p deep
  · have hs := p.2.2.sum_blocksFun.trans hy
    have ha := kernel_automorphisms_lower p.2.2.blocksFun p.2.2.one_le_blocksFun hs
    have hcount := (Nat.mul_le_mul_left c ha).trans (derived_profile_upper p.2.1.blocksFun p.2.2.blocksFun)
    refine power_budget c (price p) ((s-1)*(s-2)) (2*n+tailCost n 1) (10*(n+1)^2) (2*(n+1)^3) hcount ?_
    have hprice := three_price_le (by omega : 1 ≤ n) p hx hy
    change price p ≤ s*(d*(d-1)/2)+d*(s+1)+1 at hprice
    have htotal : n=d+s+3 := by
      change p.1.val=d+2 at hx
      change n-p.1.val=s+1 at hy
      have := p.1.isLt
      omega
    simpa only [tailCost,add_zero,zero_add,Nat.add_assoc] using three_layer_margin_of_price htotal hn hprice

/-- Uniform count of all groups admitting an order-two kernel with quotient
of class at most two and noncentral Frattini subgroup. -/
theorem noncentral_descendants_upper (n : ℕ) (hn : 4000 ≤ n) :
    (descendants n 1 (noncentralClasses n)).ncard^27*2^(10*(n+1)^2) ≤ 2^(2*(n+1)^3) := by
  classical
  let T := derivedCandidates n
  let S := noncentralClasses n
  have hfin : S.Finite := (Erdos1160.Tables.orderClasses_finite (2^n)).subset (by
    rintro _ ⟨G,h,rfl⟩; exact ⟨G,h.1,rfl⟩)
  have horder : S ⊆ Erdos1160.Tables.orderClasses (2^n) := by
    rintro _ ⟨G,h,rfl⟩
    exact ⟨G,h.1,rfl⟩
  have hf : (⋃ p ∈ T,derivedListed p).Finite :=
    T.finite_toSet.biUnion (fun p _ => (profileClasses_finite _ _).subset (derived_subset _ _))
  have hs := (Set.ncard_le_ncard (derived_cover n) hf).trans (T.set_ncard_biUnion_le derivedListed)
  have h := descendants_bound n 1 S hfin horder
  by_cases hT : T.Nonempty
  · obtain ⟨q,hq,hmax⟩ := T.exists_max_image (fun p=>(derivedListed p).ncard) hT
    have ht : T.card ≤ 2^(2*n) := by
      have hcard := Finset.card_le_univ T
      rw [←Nat.card_eq_fintype_card] at hcard
      exact hcard.trans (count_composition_profiles n)
    have hbase : S.ncard ≤ (derivedListed q).ncard * 2^(2*n) := hs.trans (calc
      _ ≤ ∑ _p∈T,(derivedListed q).ncard := Finset.sum_le_sum hmax
      _ = T.card*(derivedListed q).ncard := by simp
      _ ≤ 2^(2*n)*(derivedListed q).ncard := Nat.mul_le_mul_right _ ht
      _ = _ := mul_comm _ _)
    have hle := h.trans (Nat.mul_le_mul_right (2^(tailCost n 1)) hbase)
    rw [Nat.mul_assoc,←Nat.pow_add] at hle
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle 27)).trans
      (derived_profile_descendant_budget n hn q hq)
  · have hzero : S.ncard=0 := by
      have he := Finset.not_nonempty_iff_eq_empty.mp hT
      simpa [he] using hs
    simp [hzero] at h
    change (descendants n 1 S).ncard^27 * _ ≤ _
    simp [h]

end ClassTwoProfile

end

/- DerivedThird -/
section

namespace ThirdLowerCentral

abbrev third (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 2

theorem trivial_iff {G : Type*} [Group G] :
    third G = ⊥ ↔ commutator G ≤ Subgroup.center G := by
  change ⁅commutator G,(⊤ : Subgroup G)⁆ = ⊥ ↔ _
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  simp [Subgroup.centralizer_univ]

theorem order_two_central {G : Type*} [Group G] (K : Subgroup G) [hn : K.Normal]
    (hc : Nat.card K = 2) : K ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  by_cases h : x=1
  · simp [h]
  let a : K := ⟨x,hx⟩
  let b : K := ⟨y*x*y⁻¹,hn.conj_mem _ hx y⟩
  have ha : a ≠ 1 := fun e => h (congrArg Subtype.val e)
  have hb : b ≠ 1 := by
    intro h'
    have he : y*x*y⁻¹=1 := congrArg Subtype.val h'
    have he' : (y*x*y⁻¹)*y = y := by rw [he, one_mul]
    exact h (by simpa using he')
  have hab := (Nat.card_eq_two_iff' (1 : K)).mp hc
  have eq : b=a := hab.unique hb ha
  have hh : y*x*y⁻¹=x := congrArg Subtype.val eq
  simpa using congrArg (· * y) hh

theorem quotient_has_class_two (G : Type*) [Group G] :
    commutator (G ⧸ third G) ≤ Subgroup.center (G ⧸ third G) := by
  apply trivial_iff.mp
  let q := QuotientGroup.mk' (third G)
  have onto : (⊤ : Subgroup G).map q = ⊤ := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have he := (⊤ : Subgroup G).map_lowerCentralSeries q 2
  rw [onto] at he
  change (⊤ : Subgroup (G ⧸ third G)).lowerCentralSeries 2 = ⊥
  rw [← he]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])

theorem order_two_layer {G : Type*} [Group G] [Finite G]
    (h : ¬commutator G ≤ Subgroup.center G) (hc : Nat.card (third G) ≤ 2) :
    Nat.card (third G) = 2 ∧ third G ≤ Subgroup.center G ∧
      (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ ∧
      commutator (G ⧸ third G) ≤ Subgroup.center (G ⧸ third G) := by
  have hn : Nat.card (third G) ≠ 1 := fun e => h (trivial_iff.mp ((third G).eq_bot_of_card_eq e))
  have hpos := Nat.card_pos (α := third G)
  have hs : Nat.card (third G)=2 := by omega
  have hcent := order_two_central _ hs
  exact ⟨hs,hcent,(⊤ : Subgroup G).lowerCentralSeries_succ_eq_bot (n := 2) hcent,quotient_has_class_two G⟩

end ThirdLowerCentral

end

/- CountingBudget -/
section

namespace OrbitUp

def countingCap (m : ℕ) : ℕ := 2^((2*m^3-10*m^2)/27+1)

theorem count_le_cap {m X : ℕ} (hm : 10 ≤ m)
    (h : X^27*2^(10*m^2) ≤ 2^(2*m^3)) : X ≤ countingCap m := by
  let E := 2*m^3-10*m^2
  have hbig := Nat.mul_le_mul_right (m^2) hm
  have hpos : 10*m^2 ≤ 2*m^3 := by nlinarith only [hbig]
  have hE : E+10*m^2 = 2*m^3 := Nat.sub_add_cancel hpos
  have hx : X^27 ≤ 2^E := by
    apply Nat.le_of_mul_le_mul_right (c:=2^(10*m^2)) _ (Nat.two_pow_pos _)
    rwa [←Nat.pow_add,hE]
  apply (Nat.pow_le_pow_iff_left (by decide : 27 ≠ 0)).mp
  change _ ≤ (2^(E/27+1))^27
  rw [←Nat.pow_mul]
  exact hx.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Up to 2^(2m) elementary counting bounds can be summed, with a factor 256
remaining for combinations between the resulting families. -/
theorem cap_total_upper {A m : ℕ} (hm : 200 ≤ m) (h : A ≤ 2^(2*m)*countingCap m) :
    (256*A)^27 * 2^(9*m^2) ≤ 2^(2*m^3) := by
  let E := 2*m^3-10*m^2
  have hbig := Nat.mul_le_mul_right (m^2) hm
  have hsq := Nat.mul_le_mul_left m hm
  have hp : 10*m^2 ≤ 2*m^3 := by nlinarith only [hbig]
  have hE : E+10*m^2 = 2*m^3 := Nat.sub_add_cancel hp
  have bound : 256*A ≤ 2^(8+2*m+(E/27+1)) := calc
    _ ≤ 256*(2^(2*m)*2^(E/27+1)) := Nat.mul_le_mul_left _ h
    _ = _ := by rw [Nat.pow_add _ (8+2*m),Nat.pow_add _ 8,Nat.mul_assoc]
  have ehr : 27*(E/27) ≤ E := Nat.mul_div_le _ _
  have he : (8+2*m+(E/27+1))*27+9*m^2 ≤ 2*m^3 := by nlinarith only [hsq,hE,ehr,hm]
  calc
    _ ≤ (2^(8+2*m+(E/27+1)))^27*2^(9*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left bound 27)
    _ = _ := by rw [←Nat.pow_mul,←Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem sum_under_cap {ι : Type*} {m A : ℕ} (hm : 200 ≤ m)
    (I : Finset ι) (f : ι → ℕ) (hA : A ≤ ∑ i ∈ I, f i)
    (hc : I.card ≤ 2^(2*m)) (hf : ∀ i ∈ I, (f i)^27*2^(10*m^2) ≤ 2^(2*m^3)) :
    (256*A)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  apply cap_total_upper hm
  calc
    _ ≤ ∑ _i ∈ I,countingCap m :=
      hA.trans (Finset.sum_le_sum (fun i hi => count_le_cap (by omega) (hf i hi)))
    _ = I.card*countingCap m := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hc

end OrbitUp

end

/- SmallGammaStructure -/
section

namespace SmallGamma
open ClassTwoProfile ThirdLowerCentral CategoryTheory Erdos1160Growth.LowerTriangularUpper

def target (m : ℕ) : Set GroupId := Quotient.mk _ '' { G : FiniteGrp.{0} |
  Nat.card G=2^m ∧ ¬ commutator G ≤ Subgroup.center G ∧ Nat.card (third G) ≤ 2 }

private theorem desc_order {n e : ℕ} (S : Set GroupId) :
    descendants n e S ⊆ Erdos1160.Tables.orderClasses (2^(n+e)) := by
  rintro _ ⟨Q,hq,G,hG,_,rfl⟩
  exact ⟨G,hG,rfl⟩

theorem target_subset {m : ℕ} (hm : 1 ≤ m) {S : Set GroupId}
    (small : ∀ (G : FiniteGrp.{0}), Nat.card G=2^m →
      Nat.card (third G)=2 → frattini (G ⧸ third G) ≤ Subgroup.center _ →
        Nat.card (squareCore (frattini (G ⧸ third G))) ≤ 8 → Quotient.mk _ G ∈ S) :
    target m ⊆ S ∪ (descendants (m-1) 1 (noncentralClasses (m-1)) ∪
                     descendants (m-1) 1 (fourFrattiniClasses (m-1))) := by
  rintro _ ⟨G,⟨hc,hh,ht⟩,rfl⟩
  obtain ⟨hN,hn,_,hQ⟩ := order_two_layer hh ht
  let N := third G
  let Q := FiniteGrp.of (G ⧸ N)
  have hQord : Nat.card Q = 2^(m-1) := by
    have H := N.index_mul_card
    rw [Subgroup.index_eq_card,hc,show Nat.card N=2 from hN] at H
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    exact H.trans (by rw [←Nat.pow_succ];congr 1;omega)
  have lift : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G ∈ Erdos1160.CentralLifts.epiClasses 2 (m-1) 1 Q :=
    ⟨G,hc.trans (congrArg (2^·) (by omega)),⟨QuotientGroup.mk' N,QuotientGroup.mk'_surjective N⟩,rfl⟩
  by_cases hz : frattini Q ≤ Subgroup.center Q
  · by_cases hs : Nat.card (squareCore (frattini Q)) ≤ 8
    · exact Or.inl (small G hc hN hz hs)
    · have hdiv := (squareCore (frattini Q)).card_subgroup_dvd_card.trans (frattini Q).card_subgroup_dvd_card
      rw [hQord] at hdiv
      obtain ⟨a,_,ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
      have hb : 4 ≤ a := by
        by_contra! h
        exact hs (ha ▸ Nat.pow_le_pow_right (by decide) (show a ≤ 3 by omega))
      have hlarge : 16 ≤ Nat.card (squareCore (frattini Q)) := ha ▸ Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb
      exact Or.inr (Or.inr ⟨Q,⟨Q,⟨hQord,hz,hlarge⟩,rfl⟩,lift⟩)
  · exact Or.inr (Or.inl ⟨Q,⟨Q,⟨hQord,hQ,hz⟩,rfl⟩,lift⟩)

private theorem combine (a b c x T U : ℕ) (hx : x ≤ a+b+c)
    (hA : (32*a)^27*T ≤ U) (hB : (32*b)^27*T ≤ U) (hC : (32*c)^27*T ≤ U) :
    (8*x)^27*T ≤ U := by
  rcases le_total a b with hab|hba
  · rcases le_total b c with hbc|hcb
    · exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 8*x ≤ 32*c) 27)).trans hC
    · exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 8*x ≤ 32*b) 27)).trans hB
  · rcases le_total a c with hac|hca
    · exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 8*x ≤ 32*c) 27)).trans hC
    · exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 8*x ≤ 32*a) 27)).trans hA

private theorem reserve {m X : ℕ} (hm : 200 ≤ m) (h : X^27*2^(10*m^2) ≤ 2^(2*m^3)) :
    (32*X)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  have h' : X ≤ 2^(2*m)*OrbitUp.countingCap m :=
    (OrbitUp.count_le_cap (by omega) h).trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right X (by decide : 32 ≤ 256)) 27)).trans
    (OrbitUp.cap_total_upper hm h')

theorem target_bound {m : ℕ} (hm : 10000010 ≤ m) {S : Set GroupId} (hfin : S.Finite)
    (hs : (32*S.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3))
    (cover : target m ⊆ S ∪ (descendants (m-1) 1 (noncentralClasses (m-1)) ∪
                             descendants (m-1) 1 (fourFrattiniClasses (m-1)))) :
    (8*(target m).ncard)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  let B := descendants (m-1) 1 (noncentralClasses (m-1))
  let C := descendants (m-1) 1 (fourFrattiniClasses (m-1))
  have finite (K : Set GroupId) := (Erdos1160.Tables.orderClasses_finite (2^(m-1+1))).subset (desc_order (n:=m-1) (e:=1) K)
  have bfin : B.Finite := finite _
  have cfin : C.Finite := finite _
  have h : (target m).ncard ≤ S.ncard+B.ncard+C.ncard := calc
    _ ≤ (S∪(B∪C)).ncard := Set.ncard_le_ncard cover (hfin.union (bfin.union cfin))
    _ ≤ S.ncard+(B∪C).ncard := Set.ncard_union_le _ _
    _ ≤ S.ncard+(B.ncard+C.ncard) := Nat.add_le_add_left (Set.ncard_union_le _ _) _
    _ = _ := (Nat.add_assoc ..).symm
  have hB := noncentral_descendants_upper (m-1) (by omega)
  have hC := four_frattini_descendants (m-1) (by omega)
  rw [show m-1+1=m by omega] at hB hC
  exact combine _ _ _ _ _ _ h hs (reserve (by omega) hB) (reserve (by omega) hC)

end SmallGamma

end

/- PowerCountAggregate -/
section

namespace OrbitUp

theorem four_profiles_two_ranks (m A : ℕ) (hm : 200 ≤ m) (f g : ℕ → ℕ → ℕ)
    (hA : A ≤ ∑ a ∈ Finset.range 4, ∑ d ∈ Finset.range (m-1-a+1), (f a d+g a d))
    (hf : ∀ a ≤ 3, ∀ d ≤ m-1-a, (f a d)^27*2^(10*m^2) ≤ 2^(2*m^3))
    (hg : ∀ a ≤ 3, ∀ d ≤ m-1-a, (g a d)^27*2^(10*m^2) ≤ 2^(2*m^3)) :
    (256*A)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  let B := countingCap m
  have hrow (a : ℕ) (ha : a ∈ Finset.range 4) :
      ∑ d ∈ Finset.range (m-1-a+1), (f a d+g a d) ≤ m*(2*B) := calc
    _ ≤ ∑ _d ∈ Finset.range (m-1-a+1), 2*B := by
      apply Finset.sum_le_sum
      intro d hd
      have ha3 : a ≤ 3 := by have := Finset.mem_range.mp ha;omega
      have hdt : d ≤ m-1-a := by have := Finset.mem_range.mp hd;omega
      have h1 : f a d ≤ B := count_le_cap (by omega) (hf a ha3 d hdt)
      have h2 : g a d ≤ B := count_le_cap (by omega) (hg a ha3 d hdt)
      omega
    _ = (m-1-a+1)*(2*B) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have ht : A ≤ 4*(m*(2*B)) := hA.trans ((Finset.sum_le_sum hrow).trans_eq (by simp))
  have h8 : 8 ≤ (2:ℕ)^m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 3 ≤ m by omega)
  have hcount : 8*m ≤ 2^(2*m) := calc
    _ ≤ 2^m*2^m := Nat.mul_le_mul h8 (Nat.le_of_lt m.lt_two_pow_self)
    _ = _ := by rw [←Nat.pow_add];congr 1;omega
  apply cap_total_upper hm
  exact ht.trans ((le_of_eq (show 4*(m*(2*B))=(8*m)*B by ring)).trans (Nat.mul_le_mul_right _ hcount))

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
theorem far_move_pays {d s r k : ℕ} (hm : 10000000 ≤ d+s) (hlo : d ≤ 3*s)
    (hhi : 3*s ≤ 2*d) (hr : d/128 < r) (hmoves : r ≤ 2*k+2) :
    d*d+s*s ≤ s*slotsN k := by
  have hd : d ≤ 300*k := by omega
  have hs : 360000 ≤ s := by omega
  have hsd : s ≤ d := by omega
  have h1 := Nat.mul_le_mul hd hd
  have h2 := Nat.mul_le_mul hsd hsd
  have hk := twice_slots k
  have h3 := Nat.mul_le_mul_right (slotsN k) hs
  nlinarith only [h1,h2,hk,h3]

/-- At low input rank, a nonidentity output loses enough slots to absorb the number
of possible low-rank inputs and all output changes. -/
theorem low_move_pays {d s r f : ℕ} (hhi : 3*s ≤ 2*d)
    (hr : r ≤ d/128) (hf : r+f=d) :
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

theorem orbit_rank_far {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s ≤ d ∨ 2*d ≤ 3*s) :
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

/- SmallDefect -/
section

namespace OrbitUp

private theorem smallDefect_orbit_count_near {d t : ℕ} (hu : 10000000 ≤ d+t)
    (hn : d ≤ 3*t ∧ 3*t ≤ 2*d) :
    Nat.card (Classes d t)*2^(d*(d-1)+t*(t-1)) ≤
      2^(t*slotsN d+(2*d*(d/128)+2)) := by
  apply count_all_of_incidence
  apply incidence_stratified d t (d/128)
  · intro a ha
    obtain ⟨k,hk,hmove⟩ := exists_moves_rank a
    exact ⟨k,hmove,far_move_pays hu hn.1 hn.2 ha hk⟩
  · intro a ha
    exact low_move_pays hn.2 ha (rank_add_fixed a)

private theorem smallDefect_shifted_quadratic (t e : ℕ) :
    t*(t-1)+(2*t*e+e*(e-1)) = (t+e)*((t+e)-1) := by
  cases t <;> cases e <;> simp <;> ring

private theorem smallDefect_extra_linear {d t e : ℕ} (he : e ≤ 2) (hu : 10000000 ≤ d+t) :
    27*(2*d*(d/128)+2+8+e*t+(2*t*e+e*(e-1))) + 60*(d+(t+e)) ≤
      2*(d+(t+e))^2 := by
  have hR : 128*(d/128) ≤ d := by omega
  have hR2 := Nat.mul_le_mul_left d hR
  have ht := Nat.mul_le_mul_right t he
  have he2 : e*(e-1) ≤ 2 := (Nat.mul_le_mul he (show e-1 ≤ 1 by omega)).trans (by decide)
  have hbig := Nat.mul_le_mul_left (d+t) hu
  nlinarith only [hR2,ht,he2,hbig,hu,he]

private theorem smallDefect_reorder (a b c x y : ℕ) : (a*b*c)*(x*y) = ((b*x)*(a*c))*y := by ring

/-- Extend the near-rank Burnside estimate by at most two central binary dimensions. -/
theorem small_defect_near {d t e X : ℕ} (he : e ≤ 2) (hu : 10000000 ≤ d+t)
    (hn : d ≤ 3*t ∧ 3*t ≤ 2*d)
    (hx : X ≤ 2^8 * Nat.card (Classes d t) * 2^(e*(slotsN d+t))) :
    X^27 * 2^(10*(d+(t+e))^2) ≤ 2^(2*(d+(t+e))^3) := by
  let m := d+(t+e)
  let A := d*(d-1)+t*(t-1)
  let D := 2*t*e+e*(e-1)
  let W := 2*d*(d/128)+2+8+e*t+D
  let P := (t+e)*slotsN d
  have h := smallDefect_orbit_count_near hu hn
  have hm : X*2^(A+D) ≤ 2^(P+W) := calc
    _ ≤ (2^8*Nat.card (Classes d t)*2^(e*(slotsN d+t)))*2^(A+D) := Nat.mul_le_mul_right _ hx
    _ = ((Nat.card (Classes d t)*2^A)*(2^8*2^(e*(slotsN d+t))))*2^D := by
      rw [Nat.pow_add]
      exact smallDefect_reorder _ _ _ _ _
    _ ≤ (2^(t*slotsN d+(2*d*(d/128)+2))*(2^8*2^(e*(slotsN d+t))))*2^D :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
    _ = 2^(P+W) := by
      rw [←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]
      congr 1
      dsimp [P,W]
      ring
  have ha : A+D = d*(d-1)+(t+e)*((t+e)-1) := by
    dsimp [A,D]
    rw [Nat.add_assoc,smallDefect_shifted_quadratic]
  have hpoly := rank_powers d (t+e)
  change 27*P+12*m^2 ≤ 2*m^3+60*m+27*(d*(d-1)+(t+e)*((t+e)-1)) at hpoly
  rw [← ha] at hpoly
  have hw : 27*W+60*m ≤ 2*m^2 := smallDefect_extra_linear he hu
  have hexp : (P+W)*27+10*m^2 ≤ 2*m^3+(A+D)*27 := by omega
  have hp := Nat.pow_le_pow_left hm 27
  rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul] at hp
  apply Nat.le_of_mul_le_mul_right (c := 2^((A+D)*27)) _ (Nat.two_pow_pos _)
  calc
    _ = (X^27*2^((A+D)*27))*2^(10*m^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^((P+W)*27)*2^(10*m^2) := Nat.mul_le_mul_right _ hp
    _ = 2^((P+W)*27+10*m^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*m^3+(A+D)*27) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := Nat.pow_add _ _ _

end OrbitUp

end

/- FarDefect -/
section

namespace OrbitUp

theorem far_rank_slots_extra {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s ≤ d ∨ 2*d ≤ 3*s) :
    27*(s*slotsN d)+100*(d+s)^2 ≤ 2*(d+s)^3 := by
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

/-- The raw form count on a rank split far from the cubic maximum absorbs two extra layers. -/
theorem small_defect_far {d t e X : ℕ} (he : e ≤ 2) (hu : 10000000 ≤ d+t)
    (hf : 3*t ≤ d ∨ 2*d ≤ 3*t)
    (hx : X ≤ 2^8 * Nat.card (Classes d t)*2^(e*(slotsN d+t))) :
    X^27 * 2^(10*(d+(t+e))^2) ≤ 2^(2*(d+(t+e))^3) := by
  let u := d+t
  let m := d+(t+e)
  let P := t*slotsN d
  let E := e*(slotsN d+t)+8
  letI : Finite (Q d t) := Finite.of_injective _ (@coefficients_injective d t)
  have hc : Nat.card (Classes d t) ≤ Nat.card (Q d t) :=
    Nat.card_le_card_of_surjective Quotient.mk'' Quotient.mk''_surjective
  have small : X ≤ 2^(P+E) := hx.trans (calc
    _ ≤ (2^8*2^(t*slotsN d))*2^(e*(slotsN d+t)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hc.trans (count_forms d t)))
    _ = _ := by rw [← Nat.pow_add, ← Nat.pow_add];congr 1;dsimp [P,E];omega)
  have h1 := twice_slots d
  have h2 := Nat.mul_le_mul_right (slotsN d+t) he
  have h3 := Nat.mul_le_mul_left u hu
  have h4 := Nat.mul_le_mul he he
  have h5 := Nat.mul_le_mul_left u he
  have extra : 27*E+10*m^2 ≤ 100*u^2 := by
    dsimp [E,m,u] at *
    nlinarith only [h1,h2,h3,h4,h5,he,hu]
  have raw : 27*P+100*u^2 ≤ 2*u^3 := far_rank_slots_extra hu hf
  have order : u ≤ m := by dsimp [u,m];omega
  have mono := Nat.pow_le_pow_left order 3
  have he' : (P+E)*27+10*m^2 ≤ 2*m^3 := by omega
  calc
    _ ≤ (2^(P+E))^27*2^(10*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left small 27)
    _ = 2^((P+E)*27+10*m^2) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he'

theorem small_defect_uniform {d t e X : ℕ} (he : e ≤ 2) (hu : 10000000 ≤ d+t)
    (hx : X ≤ 2^8*Nat.card (Classes d t)*2^(e*(slotsN d+t))) :
    X^27*2^(10*(d+(t+e))^2) ≤ 2^(2*(d+(t+e))^3) := by
  by_cases hn : d ≤ 3*t ∧ 3*t ≤ 2*d
  · exact small_defect_near he hu hn hx
  · exact small_defect_far he hu (by omega) hx

end OrbitUp

end

/- BoundedAction -/
section

namespace OrbitUp

theorem far_rank_slots_slack {d s : ℕ} (hm : 10000000 ≤ d+s) (hfar : 3*s ≤ d ∨ 2*d ≤ 3*s) :
    27*(s*slotsN d)+2000*(d+s)^2 ≤ 2*(d+s)^3 := by
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

private theorem boundedAction_orbit_count_near {d t : ℕ} (hu : 10000000 ≤ d+t)
    (hn : d ≤ 3*t ∧ 3*t ≤ 2*d) :
    Nat.card (Classes d t)*2^(d*(d-1)+t*(t-1)) ≤
      2^(t*slotsN d+(2*d*(d/128)+2)) := by
  apply count_all_of_incidence
  apply incidence_stratified d t (d/128)
  · intro a ha
    obtain ⟨k,hk,hmove⟩ := exists_moves_rank a
    exact ⟨k,hmove,far_move_pays hu hn.1 hn.2 ha hk⟩
  · intro a ha
    exact low_move_pays hn.2 ha (rank_add_fixed a)

private theorem boundedAction_shifted_quadratic (t e : ℕ) :
    t*(t-1)+(2*t*e+e*(e-1)) = (t+e)*((t+e)-1) := by
  cases t <;> cases e <;> simp <;> ring

private theorem boundedAction_extra_linear {d t e : ℕ} (he : e ≤ 64) (hu : 10000000 ≤ d+t) :
    27*(2*d*(d/128)+2+(128*(d+t)+262144)+e*t+(2*t*e+e*(e-1))) + 60*(d+(t+e)) ≤
      2*(d+(t+e))^2 := by
  have hR : 128*(d/128) ≤ d := by omega
  have hR2 := Nat.mul_le_mul_left d hR
  have ht := Nat.mul_le_mul_right t he
  have he2 : e*(e-1) ≤ 4032 := (Nat.mul_le_mul he (show e-1 ≤ 63 by omega)).trans (by decide)
  have hbig := Nat.mul_le_mul_left (d+t) hu
  nlinarith only [hR2,ht,he2,hbig,hu,he]

private theorem boundedAction_reorder (a b c x y : ℕ) : (a*b*c)*(x*y) = ((b*x)*(a*c))*y := by ring

/-- Extend the near-rank Burnside estimate by at most sixty-four central binary dimensions. -/
theorem bounded_action_near {d t e X : ℕ} (he : e ≤ 64) (hu : 10000000 ≤ d+t)
    (hn : d ≤ 3*t ∧ 3*t ≤ 2*d)
    (hx : X ≤ 2^(128*(d+t)+262144) * Nat.card (Classes d t) * 2^(e*(slotsN d+t))) :
    X^27 * 2^(10*(d+(t+e))^2) ≤ 2^(2*(d+(t+e))^3) := by
  let m := d+(t+e)
  let A := d*(d-1)+t*(t-1)
  let D := 2*t*e+e*(e-1)
  let W := 2*d*(d/128)+2+(128*(d+t)+262144)+e*t+D
  let P := (t+e)*slotsN d
  have h := boundedAction_orbit_count_near hu hn
  have hm : X*2^(A+D) ≤ 2^(P+W) := calc
    _ ≤ (2^(128*(d+t)+262144)*Nat.card (Classes d t)*2^(e*(slotsN d+t)))*2^(A+D) := Nat.mul_le_mul_right _ hx
    _ = ((Nat.card (Classes d t)*2^A)*(2^(128*(d+t)+262144)*2^(e*(slotsN d+t))))*2^D := by
      rw [Nat.pow_add 2 A D]
      exact boundedAction_reorder _ _ _ _ _
    _ ≤ (2^(t*slotsN d+(2*d*(d/128)+2))*(2^(128*(d+t)+262144)*2^(e*(slotsN d+t))))*2^D :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
    _ = 2^(P+W) := by
      rw [←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]
      congr 1
      dsimp [P,W]
      ring
  have ha : A+D = d*(d-1)+(t+e)*((t+e)-1) := by
    dsimp [A,D]
    rw [Nat.add_assoc,boundedAction_shifted_quadratic]
  have hpoly := rank_powers d (t+e)
  change 27*P+12*m^2 ≤ 2*m^3+60*m+27*(d*(d-1)+(t+e)*((t+e)-1)) at hpoly
  rw [← ha] at hpoly
  have hw : 27*W+60*m ≤ 2*m^2 := boundedAction_extra_linear he hu
  have hexp : (P+W)*27+10*m^2 ≤ 2*m^3+(A+D)*27 := by omega
  have hp := Nat.pow_le_pow_left hm 27
  rw [Nat.mul_pow,←Nat.pow_mul,←Nat.pow_mul] at hp
  apply Nat.le_of_mul_le_mul_right (c := 2^((A+D)*27)) _ (Nat.two_pow_pos _)
  calc
    _ = (X^27*2^((A+D)*27))*2^(10*m^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^((P+W)*27)*2^(10*m^2) := Nat.mul_le_mul_right _ hp
    _ = 2^((P+W)*27+10*m^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*m^3+(A+D)*27) := Nat.pow_le_pow_right (by decide) hexp
    _ = _ := Nat.pow_add _ _ _

/-- The raw form count on a rank split far from the cubic maximum absorbs a bounded number of extra layers. -/
theorem bounded_action_far {d t e X : ℕ} (he : e ≤ 64) (hu : 10000000 ≤ d+t)
    (hf : 3*t ≤ d ∨ 2*d ≤ 3*t)
    (hx : X ≤ 2^(128*(d+t)+262144) * Nat.card (Classes d t)*2^(e*(slotsN d+t))) :
    X^27 * 2^(10*(d+(t+e))^2) ≤ 2^(2*(d+(t+e))^3) := by
  let u := d+t
  let m := d+(t+e)
  let P := t*slotsN d
  let E := e*(slotsN d+t)+(128*(d+t)+262144)
  letI : Finite (Q d t) := Finite.of_injective _ (@coefficients_injective d t)
  have hc : Nat.card (Classes d t) ≤ Nat.card (Q d t) :=
    Nat.card_le_card_of_surjective Quotient.mk'' Quotient.mk''_surjective
  have small : X ≤ 2^(P+E) := hx.trans (calc
    _ ≤ (2^(128*(d+t)+262144)*2^(t*slotsN d))*2^(e*(slotsN d+t)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hc.trans (count_forms d t)))
    _ = _ := by rw [← Nat.pow_add, ← Nat.pow_add];congr 1;dsimp [P,E];omega)
  have h1 := twice_slots d
  have h2 := Nat.mul_le_mul_right (slotsN d+t) he
  have h3 := Nat.mul_le_mul_left u hu
  have h4 := Nat.mul_le_mul he he
  have h5 := Nat.mul_le_mul_left u he
  have extra : 27*E+10*m^2 ≤ 2000*u^2 := by
    dsimp [E,m,u] at *
    nlinarith only [h1,h2,h3,h4,h5,he,hu]
  have raw : 27*P+2000*u^2 ≤ 2*u^3 := far_rank_slots_slack hu hf
  have order : u ≤ m := by dsimp [u,m];omega
  have mono := Nat.pow_le_pow_left order 3
  have he' : (P+E)*27+10*m^2 ≤ 2*m^3 := by nlinarith only [extra,raw,mono]
  calc
    _ ≤ (2^(P+E))^27*2^(10*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left small 27)
    _ = 2^((P+E)*27+10*m^2) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he'

theorem bounded_action_uniform {d t e X : ℕ} (he : e ≤ 64) (hu : 10000000 ≤ d+t)
    (hx : X ≤ 2^(128*(d+t)+262144)*Nat.card (Classes d t)*2^(e*(slotsN d+t))) :
    X^27*2^(10*(d+(t+e))^2) ≤ 2^(2*(d+(t+e))^3) := by
  by_cases hn : d ≤ 3*t ∧ 3*t ≤ 2*d
  · exact bounded_action_near he hu hn hx
  · exact bounded_action_far he hu (by omega) hx

end OrbitUp

end

/- HighActions -/
section

namespace OrbitUp

/-- A high-rank bracket enforces enough Jacobi identities to absorb both
the cost of its coordinate choices and the change-of-basis count. -/
theorem jacobi_high_gain {d t q : ℕ} (hu : 10000000 ≤ d+t)
    (ht : 3*t ≤ 2*d) (hq : 32 ≤ q) (hq' : q ≤ t) :
    d*(d-1)+(t+1)*t + (q*(d+t)+t+8) ≤ q*((d-q)*((d-q)-1)/2) := by
  let n := d-q
  let L := n*(n-1)/2
  have hd : 1000000 ≤ d := by omega
  have hn : d ≤ 3*n := by dsimp [n]; omega
  have hn' : n ≤ d := Nat.sub_le _ _
  have hchoose : 2*L+n = n^2 := by
    have h := twice_slots n
    change 2*(n+L) = n^2+n at h
    omega
  have hnn := Nat.mul_le_mul hn hn
  have hdd := Nat.mul_le_mul_left d hd
  have mult : d^2+21*(d+t) ≤ 21*L := by
    nlinarith only [hchoose,hnn,hdd,hn',ht,hu,hd]
  have hlarge := Nat.mul_le_mul_left q mult
  have qfloor := Nat.mul_le_mul_right (d^2) hq
  have ttop := Nat.mul_le_mul ht ht
  have hsub := Nat.mul_le_mul_left d (Nat.sub_le d 1)
  change _ ≤ q*L
  nlinarith only [hlarge,qfloor,ttop,hsub,hdd,ht,hd]

theorem high_action_near {d t q X : ℕ} (hu : 10000000 ≤ d+t)
    (ht : 3*t ≤ 2*d) (hq : 32 ≤ q) (hq' : q ≤ t)
    (hx : X*2^(q*((d-q)*((d-q)-1)/2)) ≤
      2^(t*slotsN d + q*(d+t) + slotsN d+t+8)) :
    X^27 * 2^(10*(d+(t+1))^2) ≤ 2^(2*(d+(t+1))^3) := by
  let m := d+(t+1)
  let P := (t+1)*slotsN d
  let A := d*(d-1)+(t+1)*t
  let W := q*(d+t)+t+8
  let L := q*((d-q)*((d-q)-1)/2)
  have hp : t*slotsN d + q*(d+t) + slotsN d+t+8 = P+W := by dsimp [P,W]; ring
  rw [hp,Nat.pow_add] at hx
  have hl : A+W ≤ L := jacobi_high_gain hu ht hq hq'
  have hm : X*2^A ≤ 2^P := by
    apply Nat.le_of_mul_le_mul_right (c := 2^W) _ (Nat.two_pow_pos _)
    rw [Nat.mul_assoc, ←Nat.pow_add]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hl)).trans hx
  have hr := rank_powers d (t+1)
  have ha : (t+1)-1=t := by omega
  rw [ha] at hr
  change 27*P+12*m^2 ≤ 2*m^3+60*m+27*A at hr
  have hbig : 10000000 ≤ m := by dsimp [m];omega
  have hlin := Nat.mul_le_mul_left m hbig
  have he : P*27+10*m^2 ≤ 2*m^3+A*27 := by nlinarith only [hr,hlin]
  have hh := Nat.pow_le_pow_left hm 27
  rw [Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul] at hh
  apply Nat.le_of_mul_le_mul_right (c := 2^(A*27)) _ (Nat.two_pow_pos _)
  calc
    _ = (X^27*2^(A*27))*2^(10*m^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^(P*27)*2^(10*m^2) := Nat.mul_le_mul_right _ hh
    _ = 2^(P*27+10*m^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*m^3+A*27) := Nat.pow_le_pow_right (by decide) he
    _ = _ := Nat.pow_add _ _ _

end OrbitUp

end

/- HighActionsFar -/
section

namespace OrbitUp

theorem high_action_far {d t q X : ℕ} (hu : 10000000 ≤ d+t)
    (ht : 2*d ≤ 3*t) (hq : q ≤ t)
    (hx : X*2^(q*((d-q)*((d-q)-1)/2)) ≤
      2^(t*slotsN d + q*(d+t) + slotsN d+t+8)) :
    X^27 * 2^(10*(d+(t+1))^2) ≤ 2^(2*(d+(t+1))^3) := by
  let u := d+t
  let m := d+(t+1)
  let P := t*slotsN d
  let W := q*(d+t)+slotsN d+t+8
  have hW : t*slotsN d + q*(d+t) + slotsN d+t+8 = P+W := by dsimp [P,W];omega
  rw [hW] at hx
  have hX : X ≤ 2^(P+W) := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans hx
  have ha : 27*P+100*u^2 ≤ 2*u^3 := far_rank_slots_extra hu (Or.inr ht)
  have hs := twice_slots d
  have hqa := Nat.mul_le_mul_right u (by dsimp [u];omega : q ≤ u)
  have hbig := Nat.mul_le_mul_left u hu
  have hlinear : 27*W+10*m^2 ≤ 100*u^2 := by
    dsimp [W,m,u] at *
    nlinarith only [hs,hqa,hbig,hu]
  have hpow := Nat.pow_le_pow_left (by dsimp [u,m];omega : u ≤ m) 3
  have he : (P+W)*27+10*m^2 ≤ 2*m^3 := by omega
  calc
    _ ≤ (2^(P+W))^27*2^(10*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hX 27)
    _ = 2^((P+W)*27+10*m^2) := by rw [←Nat.pow_mul,←Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem high_action_uniform {d t q X : ℕ} (hu : 10000000 ≤ d+t)
    (hq : 32 ≤ q) (hqt : q ≤ t)
    (hx : X*2^(q*((d-q)*((d-q)-1)/2)) ≤
      2^(t*slotsN d + q*(d+t) + slotsN d+t+8)) :
    X^27 * 2^(10*(d+(t+1))^2) ≤ 2^(2*(d+(t+1))^3) := by
  rcases le_total (3*t) (2*d) with h|h
  · exact high_action_near hu h hq hqt hx
  · exact high_action_far hu h hqt hx

end OrbitUp

end

/- BoundedPivot -/
section

namespace OrbitUp

theorem bounded_pivot_gain {d t : ℕ} (hu : 10000000 ≤ d+t) (ht : 3*t ≤ 2*d) :
    d*(d-1)+(t+1)*t+(d*t+t+(128*(d+t)+262144)) ≤ 32*((d-32)*((d-32)-1)/2) := by
  let n := d-32
  let L := n*(n-1)/2
  have hd : 1000000 ≤ d := by omega
  have hn : n+32=d := by dsimp [n];omega
  have hchoose : 2*L+n = n^2 := by
    have h := twice_slots n
    change 2*(n+L) = n^2+n at h
    omega
  have htd : t ≤ d := by omega
  have ht2 := Nat.mul_le_mul htd htd
  have hdt := Nat.mul_le_mul_left d htd
  have hsub := Nat.mul_le_mul_left d (Nat.sub_le d 1)
  have hbig := Nat.mul_le_mul_left d hd
  have hh := congrArg (fun x : ℕ => x^2) hn
  change _ ≤ 32*L
  nlinarith only [hh,hchoose,hn,hbig,hsub,hdt,ht2,htd,hd]

theorem bounded_pivot_near {d t X : ℕ} (hu : 10000000 ≤ d+t)
    (ht : 3*t ≤ 2*d)
    (hx : X*2^(32*((d-32)*((d-32)-1)/2)) ≤
      2^(t*slotsN d + d*t + slotsN d+t+(128*(d+t)+262144))) :
    X^27 * 2^(10*(d+(t+1))^2) ≤ 2^(2*(d+(t+1))^3) := by
  let m := d+(t+1)
  let P := (t+1)*slotsN d
  let A := d*(d-1)+(t+1)*t
  let W := d*t+t+(128*(d+t)+262144)
  let L := 32*((d-32)*((d-32)-1)/2)
  have hp : t*slotsN d + d*t + slotsN d+t+(128*(d+t)+262144) = P+W := by dsimp [P,W]; ring
  rw [hp,Nat.pow_add] at hx
  have hl : A+W ≤ L := bounded_pivot_gain hu ht
  have hm : X*2^A ≤ 2^P := by
    apply Nat.le_of_mul_le_mul_right (c := 2^W) _ (Nat.two_pow_pos _)
    rw [Nat.mul_assoc, ←Nat.pow_add]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hl)).trans hx
  have hr := rank_powers d (t+1)
  have ha : (t+1)-1=t := by omega
  rw [ha] at hr
  change 27*P+12*m^2 ≤ 2*m^3+60*m+27*A at hr
  have hbig : 10000000 ≤ m := hu.trans (Nat.le_succ _)
  have hlin := Nat.mul_le_mul_left m hbig
  have he : P*27+10*m^2 ≤ 2*m^3+A*27 := by nlinarith only [hr,hlin]
  have hh := Nat.pow_le_pow_left hm 27
  rw [Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul] at hh
  apply Nat.le_of_mul_le_mul_right (c := 2^(A*27)) _ (Nat.two_pow_pos _)
  calc
    _ = (X^27*2^(A*27))*2^(10*m^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^(P*27)*2^(10*m^2) := Nat.mul_le_mul_right _ hh
    _ = 2^(P*27+10*m^2) := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*m^3+A*27) := Nat.pow_le_pow_right (by decide) he
    _ = _ := Nat.pow_add _ _ _

theorem bounded_pivot_far {d t X : ℕ} (hu : 10000000 ≤ d+t)
    (ht : 2*d ≤ 3*t)
    (hx : X*2^(32*((d-32)*((d-32)-1)/2)) ≤
      2^(t*slotsN d + d*t + slotsN d+t+(128*(d+t)+262144))) :
    X^27 * 2^(10*(d+(t+1))^2) ≤ 2^(2*(d+(t+1))^3) := by
  let u := d+t
  let m := d+(t+1)
  let P := t*slotsN d
  let W := d*t+slotsN d+t+(128*(d+t)+262144)
  have hW : t*slotsN d + d*t + slotsN d+t+(128*(d+t)+262144) = P+W := by dsimp [P,W];omega
  rw [hW] at hx
  have hX : X ≤ 2^(P+W) := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans hx
  have ha : 27*P+100*u^2 ≤ 2*u^3 := far_rank_slots_extra hu (Or.inr ht)
  have hs := twice_slots d
  have hqa := Nat.mul_le_mul (by dsimp [u];omega : d ≤ u) (by dsimp [u];omega : t ≤ u)
  have hbig := Nat.mul_le_mul_left u hu
  have hlinear : 27*W+10*m^2 ≤ 100*u^2 := by
    dsimp [W,m,u] at *
    nlinarith only [hs,hqa,hbig,hu]
  have hpow := Nat.pow_le_pow_left (by dsimp [u,m];omega : u ≤ m) 3
  have he : (P+W)*27+10*m^2 ≤ 2*m^3 := by nlinarith only [ha,hlinear,hpow]
  calc
    _ ≤ (2^(P+W))^27*2^(10*m^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hX 27)
    _ = 2^((P+W)*27+10*m^2) := by rw [←Nat.pow_mul,←Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

theorem bounded_pivot_uniform {d t X : ℕ} (hu : 10000000 ≤ d+t)
    (hx : X*2^(32*((d-32)*((d-32)-1)/2)) ≤
      2^(t*slotsN d + d*t + slotsN d+t+(128*(d+t)+262144))) :
    X^27 * 2^(10*(d+(t+1))^2) ≤ 2^(2*(d+(t+1))^3) := by
  rcases le_total (3*t) (2*d) with h|h
  · exact bounded_pivot_near hu h hx
  · exact bounded_pivot_far hu h hx

end OrbitUp

end

/- DefectPrice -/
section

namespace ClassTwoProfile

private theorem cube_sum {ι : Type*} (I : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ I, (f i)^3 ≤ (∑ i ∈ I, f i)^3 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    nlinarith only [ih,Nat.zero_le (f i^2*(∑ j ∈ I, f j)), Nat.zero_le (f i*(∑ j ∈ I, f j)^2)]

theorem profile_price_excess {d t n D : ℕ} (a : Fin d → ℕ) (b : Fin t → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hs : (∑ i, a i)+(∑ j,b j) = n) (hD : d+t+D=n) :
    cost a b ≤ t*OrbitUp.slotsN d + d*D + D^3 := by
  classical
  have ha' (i) : a i ≤ n := (Finset.single_le_sum (s := Finset.univ) (f := a)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (by omega)
  have hb' (j) : b j ≤ n := (Finset.single_le_sum (s := Finset.univ) (f := b)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (by omega)
  let u (i : Fin (n+1)) := width a i.val
  let v (i : Fin (n+1)) := width b i.val
  let w (i : Fin (n+1)) := u i+v i
  let F (i : Fin (n+1)) := v i*(u i*(u i-1)/2)
  let T := (Finset.univ : Finset (Fin (n+1))).erase 0
  have hu : ∑ i,u i = ∑ i,a i := sum_width a ha'
  have hv : ∑ i,v i = ∑ i,b i := sum_width b hb'
  have h0 : u 0 = d := width_zero a ha
  have h1 : v 0 = t := width_zero b hb
  have htot : ∑ i,w i = n := by dsimp only [w];rw [Finset.sum_add_distrib,hu,hv,hs]
  have hT : ∑ i ∈ T, w i = D := by
    have h := Finset.add_sum_erase Finset.univ w (Finset.mem_univ 0)
    rw [htot] at h
    change (u 0 + v 0) + (∑ i ∈ T,w i) = n at h
    omega
  have hpoint (i) : F i ≤ (w i)^3 := by
    have he := (Nat.div_le_self (u i*(u i-1)) 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
    have hp := Nat.mul_le_mul_left (v i) he
    dsimp [F,w]
    nlinarith only [hp,Nat.zero_le ((u i)^3),Nat.zero_le (u i*(v i)^2),Nat.zero_le ((v i)^3),Nat.zero_le ((u i)^2*v i)]
  have hrest := (Finset.sum_le_sum (s:=T) (fun i _ => hpoint i)).trans (cube_sum T w)
  rw [hT] at hrest
  have hbst : ∑ i,b i ≤ t+D := by
    have had : d ≤ ∑ i,a i := by
      simpa using (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => ha i) : (∑ _i : Fin d,1) ≤ ∑ i,a i)
    omega
  have cross := Nat.mul_le_mul_left d hbst
  rw [cost_eq_width a b ha' hb']
  change (∑ i,F i)+d*(∑ i,b i) ≤ _
  rw [←Finset.add_sum_erase Finset.univ F (Finset.mem_univ 0)]
  change F 0+(∑ i ∈ T,F i)+d*(∑ i,b i) ≤ _
  dsimp only [F]
  rw [h0,h1]
  dsimp only [F] at hrest
  dsimp [OrbitUp.slotsN]
  nlinarith only [cross,hrest]

end ClassTwoProfile

end

/- ShiftBudget -/
section

namespace OrbitUp

/-- Once m ≥ 4 the numerical budget increases with m, despite the quadratic penalty. -/
theorem increase_order_budget {X k m : ℕ} (hk : 4 ≤ k) (hm : k ≤ m)
    (h : X^27*2^(10*k^2) ≤ 2^(2*k^3)) :
    X^27*2^(10*m^2) ≤ 2^(2*m^3) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hm
  have he : 2*k^3+10*(k+v)^2 ≤ 2*(k+v)^3+10*k^2 := by
    have h₁ := Nat.mul_le_mul_right (k*v) hk
    have h₂ := Nat.mul_le_mul_right (v^2) hk
    nlinarith only [h₁,h₂,Nat.zero_le (v^3),Nat.zero_le (k*v),Nat.zero_le (v^2)]
  apply Nat.le_of_mul_le_mul_right (c := 2^(10*k^2)) _ (Nat.two_pow_pos _)
  calc
    _ = (X^27*2^(10*k^2))*2^(10*(k+v)^2) := Nat.mul_right_comm _ _ _
    _ ≤ 2^(2*k^3)*2^(10*(k+v)^2) := Nat.mul_le_mul_right _ h
    _ = _ := (Nat.pow_add _ _ _).symm
    _ ≤ 2^(2*(k+v)^3+10*k^2) := Nat.pow_le_pow_right (by decide) he
    _ = _ := Nat.pow_add _ _ _

private theorem raw_cost {d s : ℕ} :
    216*(s*slotsN d) ≤ 16*(d+s)^3 + 27*(d+s)^2 := by
  have hslot := congrArg (fun z : ℕ => s*z) (twice_slots d)
  have hg : 27*s*d^2 ≤ 4*(d+s)^3 := by
    zify
    nlinarith only [mul_nonneg (sq_nonneg ((d:ℤ)-2*s)) (show 0 ≤ 4*(d:ℤ)+s by positivity)]
  have ha : 4*d*s ≤ (d+s)^2 := by zify; nlinarith only [sq_nonneg ((d:ℤ)-s)]
  nlinarith only [hslot,hg,ha]

theorem three_excess_raw {d t D X : ℕ} (hu : 10000000 ≤ d+t) (hD : 3 ≤ D)
    (hx : X ≤ 2^((t+1)*slotsN d+256*(d+t+1)+524288)) :
    X^27*2^(10*(d+t+D+1)^2) ≤ 2^(2*(d+t+D+1)^3) := by
  let u := d+(t+1)
  let P := (t+1)*slotsN d
  let W := 256*(d+t+1)+524288
  have hPW : (t+1)*slotsN d+256*(d+t+1)+524288 = P+W := Nat.add_assoc _ _ _
  rw [hPW] at hx
  have hr : 216*P ≤ 16*u^3+27*u^2 := raw_cost
  have hub : 10000000 ≤ u := hu.trans (Nat.le_succ _)
  have hbig := Nat.mul_le_mul_left u hub
  have he : (P+W)*27+10*(u+3)^2 ≤ 2*(u+3)^3 := by
    have hw : W = 256*u+524288 := rfl
    nlinarith only [hr,hbig,hw,hub]
  apply increase_order_budget (k:=u+3) (by dsimp [u];omega) (by dsimp [u];omega)
  calc
    _ ≤ (2^(P+W))^27*2^(10*(u+3)^2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hx 27)
    _ = 2^((P+W)*27+10*(u+3)^2) := by rw [←Nat.pow_mul,←Nat.pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) he

end OrbitUp

end

/- CentralCode -/
section

namespace CentralKernelCount

open scoped commutatorElement

abbrev PairSlot (d : ℕ) := (i : Fin d) × Fin i.val
abbrev CodeSlot (d t : ℕ) := Fin t ⊕ Fin d ⊕ PairSlot d
def second {d : ℕ} (p : PairSlot d) : Fin d := ⟨p.2.val,p.2.isLt.trans p.1.isLt⟩
def word {G : Type*} [Group G] {t : ℕ} (y : Fin t → G) (w : List (Fin t)) := (w.map y).prod

structure Pattern (d t : ℕ) where
  square : Fin d → List (Fin t)
  comm : PairSlot d → List (Fin t)

structure MarkedLift (B G : Type*) [Group B] [Group G] (d t : ℕ) where
  incl : B →* G
  z : Fin t → G
  x : Fin d → G
  kernelCentral : incl.range ≤ Subgroup.center G
  zCentral : ∀ i, z i ∈ Subgroup.center G
  generate : adjoin (adjoin incl.range z) x = ⊤

def Fits {B G : Type*} [Group B] [Group G] {d t : ℕ} (P : Pattern d t)
    (D : MarkedLift B G d t) (c : CodeSlot d t → B) : Prop :=
  (∀ i, D.z i ^ 2 = D.incl (c (.inl i))) ∧
  (∀ i, D.x i ^ 2 = D.incl (c (.inr (.inl i))) * word D.z (P.square i)) ∧
  (∀ p, ⁅D.x p.1,D.x (second p)⁆ = D.incl (c (.inr (.inr p))) * word D.z (P.comm p))

private theorem prod_central {E F : Type*} [Group E] [Group F] {e : E} {f : F}
    (he : e ∈ Subgroup.center E) (hf : f ∈ Subgroup.center F) :
    (e,f) ∈ Subgroup.center (E × F) := by
  apply Subgroup.mem_center_iff.mpr
  intro a
  exact Prod.ext (Subgroup.mem_center_iff.mp he a.1) (Subgroup.mem_center_iff.mp hf a.2)

theorem marked_lift_separation {B E F : Type*} [Group B] [Group E] [Group F]
    [Finite B] [Finite E] [Finite F] {d t : ℕ}
    (P : Pattern d t) (A : MarkedLift B E d t) (J : MarkedLift B F d t)
    (c : CodeSlot d t → B) (ha : Fits P A c) (hj : Fits P J c)
    (cardE : 2^d*(2^t*Nat.card B) ≤ Nat.card E)
    (cardF : 2^d*(2^t*Nat.card B) ≤ Nat.card F) : Nonempty (E ≃* F) := by
  let incl := A.incl.prod J.incl
  let D := incl.range
  let z (i : Fin t) := (A.z i,J.z i)
  let x (i : Fin d) := (A.x i,J.x i)
  let T := adjoin D z
  have zcentral (i : Fin t) : z i ∈ Subgroup.center (E × F) := prod_central (A.zCentral i) (J.zCentral i)
  have dc : D ≤ Subgroup.center (E × F) := by
    rintro _ ⟨k,rfl⟩
    exact prod_central (A.kernelCentral ⟨k,rfl⟩) (J.kernelCentral ⟨k,rfl⟩)
  letI := central_normal dc
  have tc : T ≤ Subgroup.center (E × F) := by
    apply sup_le dc
    rw [Subgroup.closure_le]
    rintro _ ⟨i,rfl⟩
    exact zcentral i
  letI := central_normal tc
  have capT : Nat.card T ≤ 2^t * Nat.card B := by
    apply (card_adjoin D z _ _).trans
    · exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ incl.rangeRestrict_surjective)
    · intro i
      exact ⟨c (.inl i),Prod.ext (ha.1 i).symm (hj.1 i).symm⟩
    · intro i j
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (zcentral j) (z i))]
      exact D.one_mem
  have tker (k : B) : incl k ∈ T := (show D ≤ T from le_sup_left) ⟨k,rfl⟩
  have tz (i : Fin t) : z i ∈ T :=
    (show Subgroup.closure (Set.range z) ≤ T from le_sup_right) (Subgroup.subset_closure ⟨i,rfl⟩)
  have tw (w : List (Fin t)) : (word A.z w,word J.z w) ∈ T := by
    induction w with
    | nil => exact T.one_mem
    | cons i v hv => exact T.mul_mem (tz i) hv
  have tpow (i : Fin d) : x i ^ 2 ∈ T := by
    have eq : x i ^ 2 = incl (c (.inr (.inl i))) * (word A.z (P.square i),word J.z (P.square i)) :=
      Prod.ext (ha.2.1 i) (hj.2.1 i)
    rw [eq]
    exact T.mul_mem (tker _) (tw _)
  have thalf (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ T := by
    have eq : ⁅x p.1,x (second p)⁆ =
        incl (c (.inr (.inr p))) * (word A.z (P.comm p),word J.z (P.comm p)) :=
      Prod.ext (ha.2.2 p) (hj.2.2 p)
    rw [eq]
    exact T.mul_mem (tker _) (tw _)
  have tcomm (i j : Fin d) : ⁅x i,x j⁆ ∈ T := by
    rcases lt_trichotomy i j with h | rfl | h
    · rw [← commutatorElement_inv]
      exact T.inv_mem (thalf ⟨j,⟨i.val,h⟩⟩)
    · simpa using T.one_mem
    · exact thalf ⟨i,⟨j.val,h⟩⟩
  have fstD : D.map (MonoidHom.fst E F) = A.incl.range := by
    rw [←MonoidHom.range_comp]
    rfl
  have sndD : D.map (MonoidHom.snd E F) = J.incl.range := by
    rw [←MonoidHom.range_comp]
    rfl
  apply paired_equiv T x (fun _ => 2) (fun _ => by decide) tpow tcomm
  · change adjoin ((adjoin D z).map _) A.x = ⊤
    rw [map_adjoin,fstD]
    exact A.generate
  · change adjoin ((adjoin D z).map _) J.x = ⊤
    rw [map_adjoin,sndD]
    exact J.generate
  · simpa using (Nat.mul_le_mul_left (2^d) capT).trans cardE
  · simpa using (Nat.mul_le_mul_left (2^d) capT).trans cardF

end CentralKernelCount

end

/- CentralReferences -/
section

namespace CentralKernelCount

open scoped commutatorElement

structure Reference (H : Type*) [Group H] (d t : ℕ) extends Pattern d t where
  z : Fin t → H
  x : Fin d → H
  z_square : ∀ i, z i ^ 2 = 1
  x_square : ∀ i, x i ^ 2 = word z (square i)
  x_comm : ∀ p, ⁅x p.1,x (second p)⁆ = word z (comm p)
  generate : adjoin (Subgroup.closure (Set.range z)) x = ⊤

structure Over {H : Type*} [Group H] {d t : ℕ} (R : Reference H d t)
    (B E : Type*) [Group B] [Group E] where
  incl : B →* E
  proj : E →* H
  surj : Function.Surjective proj
  ker : proj.ker = incl.range
  central : incl.range ≤ Subgroup.center E
  liftCentral : ∀ i, ∃ g ∈ Subgroup.center E, proj g = R.z i

theorem exists_lift_code {B E H : Type*} [Group B] [Group E] [Group H] {d t : ℕ}
    (R : Reference H d t) (L : Over R B E) :
    ∃ D : MarkedLift B E d t, ∃ c, Fits R.toPattern D c := by
  classical
  choose z hz hz' using L.liftCentral
  choose x hx using (fun i : Fin d => L.surj (R.x i))
  let S := adjoin (adjoin L.incl.range z) x
  have zimage : Set.range (fun i => L.proj (z i)) = Set.range R.z := by simp only [hz']
  have ximage : (fun i => L.proj (x i)) = R.x := funext hx
  have kerimage : L.incl.range.map L.proj = ⊥ := by
    rw [←L.ker,Subgroup.map_eq_bot_iff]
  have Simage : S.map L.proj = ⊤ := by
    change (adjoin (adjoin L.incl.range z) x).map L.proj = ⊤
    rw [map_adjoin,map_adjoin,kerimage,ximage]
    simpa only [adjoin,bot_sup_eq,zimage] using R.generate
  have sgen : S = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨w,hw,he⟩ : L.proj g ∈ S.map L.proj := by rw [Simage]; trivial
    have diff : g*w⁻¹ ∈ L.incl.range := by
      rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
    have pre : g*w⁻¹ ∈ S := ((show L.incl.range ≤ adjoin L.incl.range z from le_sup_left).trans
      (show adjoin L.incl.range z ≤ S from le_sup_left)) diff
    simpa using S.mul_mem pre hw
  let D : MarkedLift B E d t := ⟨L.incl,z,x,L.central,hz,sgen⟩
  have wmap (l : List (Fin t)) : L.proj (word z l) = word R.z l := by
    induction l with
    | nil => exact L.proj.map_one
    | cons i v h => exact (L.proj.map_mul ..).trans (congrArg₂ _ (hz' i) h)
  have solve (g h : E) (he : L.proj g = L.proj h) : ∃ k, g = L.incl k * h := by
    obtain ⟨k,hk⟩ : g*h⁻¹ ∈ L.incl.range := by
      rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
    exact ⟨k,by rw [hk,inv_mul_cancel_right]⟩
  have z2 (i : Fin t) : ∃ k, z i ^ 2 = L.incl k := by
    have : L.proj (z i ^ 2) = L.proj 1 := by rw [map_pow,hz',R.z_square,map_one]
    simpa only [mul_one] using solve (z i ^ 2) 1 this
  have x2 (i : Fin d) : ∃ k, x i ^ 2 = L.incl k * word z (R.square i) := by
    apply solve
    rw [map_pow,hx,R.x_square,wmap]
  have hc (p : PairSlot d) : ∃ k, ⁅x p.1,x (second p)⁆ = L.incl k * word z (R.comm p) := by
    apply solve
    rw [map_commutatorElement,hx,hx,R.x_comm,wmap]
  choose c1 h1 using z2
  choose c2 h2 using x2
  choose c3 h3 using hc
  exact ⟨D,Sum.elim c1 (Sum.elim c2 c3),h1,h2,h3⟩

/-- Class bound for all two-step framed lifts of one fixed quotient with one fixed
kernel group, valid for nonelementary central kernels as well. -/
theorem count_over_reference {B H I : Type*} [Group B] [Group H] [Finite B] {d t : ℕ}
    (R : Reference H d t) (E : I → Type*) [∀ i, Group (E i)] [∀ i, Finite (E i)]
    (overData : ∀ i, Nonempty (Over R B (E i)))
    (size : ∀ i, 2^d*(2^t*Nat.card B) ≤ Nat.card (E i))
    (separate : ∀ i j, Nonempty (E i ≃* E j) → i=j) :
    Nat.card I ≤ (Nat.card B)^(t+d+d*(d-1)/2) := by
  classical
  choose D c hc using fun i => exists_lift_code R (overData i).some
  have injective : Function.Injective c := by
    intro i j h
    exact separate i j <| marked_lift_separation R.toPattern (D i) (D j) (c i) (hc i)
      (h ▸ hc j) (size i) (size j)
  have pairs : Nat.card (PairSlot d) = d*(d-1)/2 := by
    rw [PairSlot,Nat.card_sigma]
    simp only [Nat.card_fin]
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
  have slots : Nat.card (CodeSlot d t) = t+d+d*(d-1)/2 := by
    change Nat.card (Fin t ⊕ (Fin d ⊕ PairSlot d)) = _
    rw [Nat.card_sum,Nat.card_sum,Nat.card_fin,Nat.card_fin,pairs,Nat.add_assoc]
  simpa only [Nat.card_fun,slots] using (Nat.card_le_card_of_injective c injective)

end CentralKernelCount

end

/- ThirdComparison -/
section

namespace CentralKernelCount

open scoped commutatorElement

theorem card_adjoin_normalized {G : Type*} [Group G] [Finite G] {d : ℕ} (T : Subgroup G)
    (x : Fin d → G) (hn : ∀ i,x i ∈ Subgroup.normalizer T)
    (hs : ∀ i,x i^2 ∈ T) (hc : ∀ i j, ⁅x i,x j⁆ ∈ T) :
    Nat.card (adjoin T x) ≤ 2^d * Nat.card T := by
  let N := Subgroup.normalizer (T : Set G)
  let U := T.subgroupOf N
  let y (i : Fin d) : N := ⟨x i,hn i⟩
  have su (i : Fin d) : y i ^ 2 ∈ U := hs i
  have cu (i j : Fin d) : ⁅y i,y j⁆ ∈ U := hc i j
  have count := card_adjoin U y su cu
  have lower : U.map N.subtype=T := Subgroup.map_subgroupOf_eq_of_le T.le_normalizer
  have map_eq : (adjoin U y).map N.subtype = adjoin T x := (map_adjoin ..).trans (by rw [lower];rfl)
  calc
    _ = Nat.card (adjoin U y) := map_eq ▸ Subgroup.card_map_of_injective N.subtype_injective
    _ ≤ 2^d * Nat.card U := count
    _ = _ := congrArg (2^d * ·) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe T.le_normalizer).toEquiv)

/-- A diagonal central subgroup and a family of paired lifts, whose cross commutators with x
are diagonal, generate an x-stable subgroup. -/
theorem normalizes_marked {G : Type*} [Group G] [Finite G] {t : ℕ} (D : Subgroup G)
    (hd : D ≤ Subgroup.center G) (z : Fin t → G) (x : G) (cross : ∀ j,⁅x,z j⁆∈D) :
    x ∈ Subgroup.normalizer (adjoin D z) := by
  let T := adjoin D z
  let f := (MulAut.conj x).toMonoidHom
  have dT : D ≤ T := le_sup_left
  have yT (j : Fin t) : z j ∈ T :=
    (show Subgroup.closure (Set.range z) ≤ T from le_sup_right) (Subgroup.subset_closure ⟨j,rfl⟩)
  have hle : T.map f ≤ T := by
    change (adjoin D z).map f ≤ T
    rw [map_adjoin]
    apply sup_le
    · rintro _ ⟨y,hy,rfl⟩
      change x*y*x⁻¹ ∈ T
      rw [Subgroup.mem_center_iff.mp (hd hy) x,mul_inv_cancel_right]
      exact dT hy
    · rw [Subgroup.closure_le]
      rintro _ ⟨j,rfl⟩
      change x*z j*x⁻¹ ∈ T
      have he : x*z j*x⁻¹= ⁅x,z j⁆*z j := by rw [commutatorElement_def];group
      exact he ▸ T.mul_mem (dT (cross j)) (yT j)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge

theorem paired_of_order {E F : Type*} [Group E] [Group F] [Finite E] [Finite F] {d : ℕ}
    (T : Subgroup (E×F)) (x : Fin d → E×F)
    (genE : adjoin (T.map (MonoidHom.fst E F)) (fun i => (x i).1)=⊤)
    (genF : adjoin (T.map (MonoidHom.snd E F)) (fun i => (x i).2)=⊤)
    (ce : Nat.card (adjoin T x) ≤ Nat.card E) (cf : Nat.card (adjoin T x) ≤ Nat.card F) :
    Nonempty (E ≃* F) := by
  let S := adjoin T x
  let a := (MonoidHom.fst E F).comp S.subtype
  let b := (MonoidHom.snd E F).comp S.subtype
  have sa : Function.Surjective a := by
    intro y
    change y∈a.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact genE ▸ (show y∈(⊤ : Subgroup E) from trivial)
  have sb : Function.Surjective b := by
    intro y
    change y∈b.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact genF ▸ (show y∈(⊤ : Subgroup F) from trivial)
  exact ⟨(MulEquiv.ofBijective a (sa.bijective_of_nat_card_le ce)).symm.trans
    (MulEquiv.ofBijective b (sb.bijective_of_nat_card_le cf))⟩

end CentralKernelCount

end

/- ThirdMarks -/
section

namespace CentralKernelCount

open scoped commutatorElement

structure ThirdMarks (B G : Type*) [Group B] [Group G] (d t : ℕ) where
  incl : B →* G
  z : Fin t → G
  x : Fin d → G
  central : incl.range ≤ Subgroup.center G
  zComm : ∀ i j,Commute (z i) (z j)
  generate : adjoin (adjoin incl.range z) x = ⊤

def ThirdFits {B G : Type*} [Group B] [Group G] {d t : ℕ} (P : Pattern d t)
    (D : ThirdMarks B G d t) (c : CodeSlot d t → B) : Prop :=
  (∀ i, D.z i ^ 2 = D.incl (c (.inl i))) ∧
  (∀ i, D.x i ^ 2 = D.incl (c (.inr (.inl i))) * word D.z (P.square i)) ∧
  (∀ p, ⁅D.x p.1,D.x (second p)⁆ = D.incl (c (.inr (.inr p))) * word D.z (P.comm p))

theorem third_separation {B E F : Type*} [Group B] [Group E] [Group F]
    [Finite B] [Finite E] [Finite F] {d t : ℕ}
    (P : Pattern d t) (A : ThirdMarks B E d t) (J : ThirdMarks B F d t)
    (c : CodeSlot d t → B) (ha : ThirdFits P A c) (hj : ThirdFits P J c)
    (M : Fin d → Fin t → B)
    (ac : ∀ i j, ⁅A.x i,A.z j⁆ = A.incl (M i j))
    (jc : ∀ i j, ⁅J.x i,J.z j⁆ = J.incl (M i j))
    (cardE : 2^d*(2^t*Nat.card B) ≤ Nat.card E)
    (cardF : 2^d*(2^t*Nat.card B) ≤ Nat.card F) : Nonempty (E ≃* F) := by
  let incl := A.incl.prod J.incl
  let D := incl.range
  let z (i : Fin t) := (A.z i,J.z i)
  let x (i : Fin d) := (A.x i,J.x i)
  let T := adjoin D z
  have zcomm (i j : Fin t) : Commute (z i) (z j) := Prod.ext (A.zComm i j).eq (J.zComm i j).eq
  have dc : D ≤ Subgroup.center (E × F) := by
    rintro _ ⟨k,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    exact Prod.ext (Subgroup.mem_center_iff.mp (A.central ⟨k,rfl⟩) v.1)
      (Subgroup.mem_center_iff.mp (J.central ⟨k,rfl⟩) v.2)
  letI := central_normal dc
  have norm (i : Fin d) : x i ∈ Subgroup.normalizer T := by
    apply normalizes_marked D dc z (x i)
    intro j
    exact ⟨M i j,Prod.ext (ac i j).symm (jc i j).symm⟩
  have capT : Nat.card T ≤ 2^t * Nat.card B := by
    apply (card_adjoin D z _ _).trans
    · exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ incl.rangeRestrict_surjective)
    · intro i
      exact ⟨c (.inl i),Prod.ext (ha.1 i).symm (hj.1 i).symm⟩
    · intro i j
      rw [commutatorElement_eq_one_iff_commute.mpr (zcomm i j)]
      exact D.one_mem
  have tker (k : B) : incl k ∈ T := (show D ≤ T from le_sup_left) ⟨k,rfl⟩
  have tz (i : Fin t) : z i ∈ T :=
    (show Subgroup.closure (Set.range z) ≤ T from le_sup_right) (Subgroup.subset_closure ⟨i,rfl⟩)
  have tw (w : List (Fin t)) : (word A.z w,word J.z w) ∈ T := by
    induction w with
    | nil => exact T.one_mem
    | cons i v hv => exact T.mul_mem (tz i) hv
  have tpow (i : Fin d) : x i ^ 2 ∈ T := by
    have eq : x i ^ 2 = incl (c (.inr (.inl i))) * (word A.z (P.square i),word J.z (P.square i)) :=
      Prod.ext (ha.2.1 i) (hj.2.1 i)
    rw [eq]
    exact T.mul_mem (tker _) (tw _)
  have thalf (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ T := by
    have eq : ⁅x p.1,x (second p)⁆ =
        incl (c (.inr (.inr p))) * (word A.z (P.comm p),word J.z (P.comm p)) :=
      Prod.ext (ha.2.2 p) (hj.2.2 p)
    rw [eq]
    exact T.mul_mem (tker _) (tw _)
  have tcomm (i j : Fin d) : ⁅x i,x j⁆ ∈ T := by
    rcases lt_trichotomy i j with h | rfl | h
    · rw [← commutatorElement_inv]
      exact T.inv_mem (thalf ⟨j,⟨i.val,h⟩⟩)
    · simpa using T.one_mem
    · exact thalf ⟨i,⟨j.val,h⟩⟩
  have fstD : D.map (MonoidHom.fst E F) = A.incl.range := by
    rw [←MonoidHom.range_comp]
    rfl
  have sndD : D.map (MonoidHom.snd E F) = J.incl.range := by
    rw [←MonoidHom.range_comp]
    rfl
  have cardS := (card_adjoin_normalized T x norm tpow tcomm).trans (Nat.mul_le_mul_left (2^d) capT)
  apply paired_of_order T x
  · change adjoin ((adjoin D z).map _) A.x = ⊤
    rw [map_adjoin,fstD]
    exact A.generate
  · change adjoin ((adjoin D z).map _) J.x = ⊤
    rw [map_adjoin,sndD]
    exact J.generate
  · exact cardS.trans cardE
  · exact cardS.trans cardF

end CentralKernelCount

end

/- PowerMarks -/
section

namespace CentralKernelCount

open scoped commutatorElement

theorem card_adjoin_normalized_orders {G : Type*} [Group G] [Finite G] {d : ℕ} (T : Subgroup G)
    (x : Fin d → G) (ord : Fin d→ℕ) (ho : ∀ i,0 < ord i) (hn : ∀ i,x i ∈ Subgroup.normalizer T)
    (hs : ∀ i,x i ^ ord i ∈ T) (hc : ∀ i j, ⁅x i,x j⁆ ∈ T) :
    Nat.card (adjoin T x) ≤ (∏ i,ord i) * Nat.card T := by
  let N := Subgroup.normalizer (T : Set G)
  let U := T.subgroupOf N
  let y (i : Fin d) : N := ⟨x i,hn i⟩
  have su (i : Fin d) : y i ^ ord i ∈ U := hs i
  have cu (i j : Fin d) : ⁅y i,y j⁆ ∈ U := hc i j
  have count := card_adjoin_orders U y ord ho su cu
  have lower : U.map N.subtype=T := Subgroup.map_subgroupOf_eq_of_le T.le_normalizer
  have map_eq : (adjoin U y).map N.subtype = adjoin T x := (map_adjoin ..).trans (by rw [lower];rfl)
  calc
    _ = Nat.card (adjoin U y) := map_eq ▸ Subgroup.card_map_of_injective N.subtype_injective
    _ ≤ (∏ i,ord i) * Nat.card U := count
    _ = _ := congrArg ((∏ i,ord i) * ·) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe T.le_normalizer).toEquiv)

def PowerFits {B G : Type*} [Group B] [Group G] {d t : ℕ} (e : Fin d→ℕ) (b : Fin t→ℕ) (P : Pattern d t)
    (D : ThirdMarks B G d t) (c : CodeSlot d t → B) : Prop :=
  (∀ i, D.z i ^ (2^b i) = D.incl (c (.inl i))) ∧
  (∀ i, D.x i ^ (2^e i) = D.incl (c (.inr (.inl i))) * word D.z (P.square i)) ∧
  (∀ p, ⁅D.x p.1,D.x (second p)⁆ = D.incl (c (.inr (.inr p))) * word D.z (P.comm p))

theorem power_separation {B E F : Type*} [Group B] [Group E] [Group F]
    [Finite B] [Finite E] [Finite F] {d t : ℕ}
    (e : Fin d→ℕ) (b : Fin t→ℕ) (P : Pattern d t) (A : ThirdMarks B E d t) (J : ThirdMarks B F d t)
    (c : CodeSlot d t → B) (ha : PowerFits e b P A c) (hj : PowerFits e b P J c)
    (M : Fin d → Fin t → B)
    (ac : ∀ i j, ⁅A.x i,A.z j⁆ = A.incl (M i j))
    (jc : ∀ i j, ⁅J.x i,J.z j⁆ = J.incl (M i j))
    (cardE : (∏ i,2^e i)*((∏ j,2^b j)*Nat.card B) ≤ Nat.card E)
    (cardF : (∏ i,2^e i)*((∏ j,2^b j)*Nat.card B) ≤ Nat.card F) : Nonempty (E ≃* F) := by
  let incl := A.incl.prod J.incl
  let D := incl.range
  let z (i : Fin t) := (A.z i,J.z i)
  let x (i : Fin d) := (A.x i,J.x i)
  let T := adjoin D z
  have zcomm (i j : Fin t) : Commute (z i) (z j) := Prod.ext (A.zComm i j).eq (J.zComm i j).eq
  have dc : D ≤ Subgroup.center (E × F) := by
    rintro _ ⟨k,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro v
    exact Prod.ext (Subgroup.mem_center_iff.mp (A.central ⟨k,rfl⟩) v.1)
      (Subgroup.mem_center_iff.mp (J.central ⟨k,rfl⟩) v.2)
  letI := central_normal dc
  have norm (i : Fin d) : x i ∈ Subgroup.normalizer T := by
    apply normalizes_marked D dc z (x i)
    intro j
    exact ⟨M i j,Prod.ext (ac i j).symm (jc i j).symm⟩
  have capT : Nat.card T ≤ (∏ j,2^b j) * Nat.card B := by
    apply (card_adjoin_orders D z (fun j => 2^b j) (fun _=>Nat.two_pow_pos _) _ _).trans
    · exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ incl.rangeRestrict_surjective)
    · intro i
      exact ⟨c (.inl i),Prod.ext (ha.1 i).symm (hj.1 i).symm⟩
    · intro i j
      rw [commutatorElement_eq_one_iff_commute.mpr (zcomm i j)]
      exact D.one_mem
  have tker (k : B) : incl k ∈ T := (show D ≤ T from le_sup_left) ⟨k,rfl⟩
  have tz (i : Fin t) : z i ∈ T :=
    (show Subgroup.closure (Set.range z) ≤ T from le_sup_right) (Subgroup.subset_closure ⟨i,rfl⟩)
  have tw (w : List (Fin t)) : (word A.z w,word J.z w) ∈ T := by
    induction w with
    | nil => exact T.one_mem
    | cons i v hv => exact T.mul_mem (tz i) hv
  have tpow (i : Fin d) : x i ^ (2^e i) ∈ T := by
    have eq : x i ^ (2^e i) = incl (c (.inr (.inl i))) * (word A.z (P.square i),word J.z (P.square i)) :=
      Prod.ext (ha.2.1 i) (hj.2.1 i)
    rw [eq]
    exact T.mul_mem (tker _) (tw _)
  have thalf (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ T := by
    have eq : ⁅x p.1,x (second p)⁆ =
        incl (c (.inr (.inr p))) * (word A.z (P.comm p),word J.z (P.comm p)) :=
      Prod.ext (ha.2.2 p) (hj.2.2 p)
    rw [eq]
    exact T.mul_mem (tker _) (tw _)
  have tcomm (i j : Fin d) : ⁅x i,x j⁆ ∈ T := by
    rcases lt_trichotomy i j with h | rfl | h
    · rw [← commutatorElement_inv]
      exact T.inv_mem (thalf ⟨j,⟨i.val,h⟩⟩)
    · simpa using T.one_mem
    · exact thalf ⟨i,⟨j.val,h⟩⟩
  have fstD : D.map (MonoidHom.fst E F) = A.incl.range := by
    rw [←MonoidHom.range_comp]
    rfl
  have sndD : D.map (MonoidHom.snd E F) = J.incl.range := by
    rw [←MonoidHom.range_comp]
    rfl
  have cardS := (card_adjoin_normalized_orders T x (fun i=>2^e i) (fun _=>Nat.two_pow_pos _) norm tpow tcomm).trans (Nat.mul_le_mul_left (∏ i,2^e i) capT)
  apply paired_of_order T x
  · change adjoin ((adjoin D z).map _) A.x = ⊤
    rw [map_adjoin,fstD]
    exact A.generate
  · change adjoin ((adjoin D z).map _) J.x = ⊤
    rw [map_adjoin,sndD]
    exact J.generate
  · exact cardS.trans cardE
  · exact cardS.trans cardF

end CentralKernelCount

end

/- RawCentral -/
section

namespace CentralKernelCount

open scoped commutatorElement

def twoTorsion (B : Type*) [Group B] := {b : B // b^2 = 1}

structure Raw {B E : Type*} [Group B] [Group E] (d : ℕ) where
  incl : B →* E
  inj : Function.Injective incl
  central : incl.range ≤ Subgroup.center E
  x : Fin d → E
  generate : adjoin incl.range x = ⊤
  square : ∀ i, x i ^ 2 ∈ incl.range
  comm : ∀ i j, ⁅x i,x j⁆ ∈ incl.range

private theorem comm_square {E : Type*} [Group E] {x y : E}
    (h : ⁅x,y⁆ ∈ Subgroup.center E) (hx : x^2 ∈ Subgroup.center E) : ⁅x,y⁆^2 = 1 := by
  let c := ⁅x,y⁆
  have hxcomm : c*x = x*c := (Subgroup.mem_center_iff.mp h x).symm
  have swap : c*y*x = x*y := by dsimp [c,commutatorElement_def]; group
  apply mul_right_cancel (b := y*x^2)
  calc
    c^2 * (y*x^2) = c*(c*y*x)*x := by simp [pow_two,mul_assoc]
    _ = c*(x*y)*x := by rw [swap]
    _ = (c*x)*(y*x) := by group
    _ = x*(c*y*x) := by rw [hxcomm]; group
    _ = x^2*y := by rw [swap]; simp [pow_two,mul_assoc]
    _ = 1*(y*x^2) := by rw [one_mul]; exact (Subgroup.mem_center_iff.mp hx y).symm

private abbrev RawCode (B : Type*) [Group B] (d : ℕ) :=
  (Fin d → B) × (PairSlot d → twoTorsion B)

private def rawFits {B E : Type*} [Group B] [Group E] {d : ℕ}
    (A : Raw (B := B) (E := E) d) (c : RawCode B d) : Prop :=
  (∀ i,A.incl (c.1 i) = A.x i ^ 2) ∧
  (∀ p,A.incl (c.2 p).val = ⁅A.x p.1,A.x (second p)⁆)

private theorem raw_exists {B E : Type*} [Group B] [Group E] {d : ℕ}
    (A : Raw (B := B) (E := E) d) : ∃ c, rawFits A c := by
  choose sq hsq using A.square
  choose cm hc using A.comm
  have ht (p : PairSlot d) : cm p.1 (second p) ^ 2 = 1 := by
    apply A.inj
    rw [map_pow,hc,map_one]
    exact comm_square (A.central (A.comm ..)) (A.central (A.square _))
  exact ⟨(sq,fun p => ⟨_,ht p⟩),hsq,fun _ => hc ..⟩

private theorem raw_separation {B E F : Type*} [Group B] [Group E] [Group F] [Finite B] [Finite E]
    [Finite F] {d : ℕ} (A : Raw (B := B) (E := E) d) (J : Raw (B := B) (E := F) d)
    (c : RawCode B d) (ha : rawFits A c) (hj : rawFits J c)
    (cE : 2^d*Nat.card B ≤ Nat.card E) (cF : 2^d*Nat.card B ≤ Nat.card F) : Nonempty (E ≃* F) := by
  let i := A.incl.prod J.incl
  let N := i.range
  let x (j : Fin d) := (A.x j,J.x j)
  have nc : N ≤ Subgroup.center (E × F) := by
    rintro _ ⟨b,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro k
    exact Prod.ext (Subgroup.mem_center_iff.mp (A.central ⟨b,rfl⟩) k.1)
      (Subgroup.mem_center_iff.mp (J.central ⟨b,rfl⟩) k.2)
  letI := central_normal nc
  have nsize : Nat.card N ≤ Nat.card B := Nat.card_le_card_of_surjective _ i.rangeRestrict_surjective
  have hp (j : Fin d) : x j ^ 2 ∈ N := ⟨c.1 j,Prod.ext (ha.1 j) (hj.1 j)⟩
  have hl (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ N :=
    ⟨(c.2 p).val,Prod.ext (ha.2 p) (hj.2 p)⟩
  have hc (j k : Fin d) : ⁅x j,x k⁆ ∈ N := by
    rcases lt_trichotomy j k with h | rfl | h
    · rw [←commutatorElement_inv]
      exact N.inv_mem (hl ⟨k,⟨j.val,h⟩⟩)
    · simp
    · exact hl ⟨j,⟨k.val,h⟩⟩
  apply paired_equiv N x (fun _ => 2) (fun _ => by decide) hp hc
  · change adjoin (i.range.map (MonoidHom.fst E F)) A.x = ⊤
    rw [← MonoidHom.range_comp]
    exact A.generate
  · change adjoin (i.range.map (MonoidHom.snd E F)) J.x = ⊤
    rw [← MonoidHom.range_comp]
    exact J.generate
  · simpa using (Nat.mul_le_mul_left (2^d) nsize).trans cE
  · simpa using (Nat.mul_le_mul_left (2^d) nsize).trans cF

/-- An arbitrary abelian central kernel permits only its two-torsion subgroup in
every commutator slot, even when generator squares have larger order. -/
theorem count_raw_central {B I : Type*} [Group B] [Finite B] {d : ℕ}
    (E : I → Type*) [∀ i,Group (E i)] [∀ i,Finite (E i)]
    (h : ∀ i, Nonempty (Raw (B := B) (E := E i) d))
    (size : ∀ i, 2^d * Nat.card B ≤ Nat.card (E i))
    (separate : ∀ i j, Nonempty (E i ≃* E j) → i=j) :
    Nat.card I ≤ (Nat.card B)^d * (Nat.card (twoTorsion B))^(d*(d-1)/2) := by
  classical
  let raw (i : I) := (h i).some
  choose c hc using fun i => raw_exists (raw i)
  have inj : Function.Injective c := by
    intro i j he
    exact separate i j <| raw_separation (raw i) (raw j) (c i) (hc i) (he ▸ hc j) (size i) (size j)
  have pairs : Nat.card (PairSlot d) = d*(d-1)/2 := by
    rw [PairSlot,Nat.card_sigma]
    simp only [Nat.card_fin]
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
  letI : Finite (twoTorsion B) := inferInstanceAs (Finite {b : B // b^2=1})
  have count := Nat.card_le_card_of_injective c inj
  simpa only [RawCode,Nat.card_prod,Nat.card_fun,Nat.card_fin,pairs] using count

end CentralKernelCount

end

/- CentralCoordinates -/
section

namespace CentralKernelCount

open scoped commutatorElement

abbrev BitGroup (d : ℕ) := Multiplicative (Fin d → ZMod 2)

def bit {d : ℕ} (i : Fin d) : BitGroup d := Multiplicative.ofAdd (Pi.single i 1)

theorem word_map {G H : Type*} [Group G] [Group H] {t : ℕ}
    (f : G →* H) (y : Fin t → G) (l : List (Fin t)) :
    f (word y l) = word (fun i => f (y i)) l := by
  induction l with
  | nil => exact f.map_one
  | cons i l h => exact (f.map_mul ..).trans (congrArg _ h)

theorem word_mem {G : Type*} [Group G] {t : ℕ}
    (S : Subgroup G) (y : Fin t → G) (hy : ∀ i, y i ∈ S) (l : List (Fin t)) : word y l ∈ S := by
  induction l with
  | nil => exact S.one_mem
  | cons i l h => exact S.mul_mem (hy i) h

theorem bits_word (d : ℕ) (w : BitGroup d) : ∃ l, word bit l = w := by
  change ∃ l, word bit l = Multiplicative.ofAdd w.toAdd
  induction w.toAdd using Pi.single_induction with
  | zero => exact ⟨[],rfl⟩
  | add x y hx hy =>
    obtain ⟨l,hl⟩ := hx
    obtain ⟨r,hr⟩ := hy
    use l++r
    simpa only [word,List.map_append,List.prod_append,ofAdd_add] using congrArg₂ (·*·) hl hr
  | single i c =>
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) c with rfl|rfl
    · exact ⟨[],by simp [word]⟩
    · exact ⟨[i],by simp [word,bit]⟩

theorem generate_lifts {E : Type*} [Group E] {d : ℕ}
    (q : E →* BitGroup d) (x : Fin d → E) (hx : ∀ i,q (x i)=bit i)
    (K : Subgroup E) (hq : q.ker ≤ K) : adjoin K x = ⊤ := by
  let S := adjoin K x
  have sx (i : Fin d) : x i ∈ S :=
    (show Subgroup.closure (Set.range x) ≤ S from le_sup_right) (Subgroup.subset_closure ⟨i,rfl⟩)
  apply top_unique
  intro g _
  obtain ⟨l,hl⟩ := bits_word d (q g)
  have qword : q (word x l) = q g := by rw [word_map]; simpa only [hx] using hl
  have diff : g*(word x l)⁻¹ ∈ q.ker := by rw [MonoidHom.mem_ker,map_mul,map_inv,qword,mul_inv_cancel]
  have hdiff : g*(word x l)⁻¹ ∈ S := (show K ≤ S from le_sup_left) (hq diff)
  simpa using S.mul_mem hdiff (word_mem S x sx l)

theorem bit_sq {d : ℕ} (x : BitGroup d) : x^2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  change x.toAdd+x.toAdd = 0
  funext i
  exact (show ∀ a : ZMod 2, a+a=0 by decide) _

theorem raw_of_bit_quotient {B E : Type*} [Group B] [Group E] {d : ℕ}
    (i : B →* E) (hi : Function.Injective i) (q : E →* BitGroup d) (hq : Function.Surjective q)
    (ker : q.ker=i.range) (z : i.range ≤ Subgroup.center E) : Nonempty (Raw (B := B) (E := E) d) := by
  choose x hx using fun j : Fin d => hq (bit j)
  refine ⟨⟨i,hi,z,x,generate_lifts q x hx _ ker.le,?_,?_⟩⟩
  · intro j
    rw [←ker,MonoidHom.mem_ker,map_pow,bit_sq]
  · intro j k
    rw [←ker,MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,mul_comm]

/-- Construct a reference whose central generators belong to the prescribed kernel.
No classification of the group extension is required. -/
theorem reference_of_coordinates {H : Type*} [Group H] {d t : ℕ}
    (i : BitGroup t →* H) (q : H →* BitGroup d) (hq : Function.Surjective q)
    (ker : q.ker=i.range) :
    ∃ R : Reference H d t, ∀ j, R.z j ∈ i.range := by
  classical
  let z (j : Fin t) := i (bit j)
  choose x hx using fun j : Fin d => hq (bit j)
  have words {h : H} (hh : h ∈ q.ker) : ∃ l, h = word z l := by
    rw [ker] at hh
    obtain ⟨v,rfl⟩ := hh
    obtain ⟨l,hl⟩ := bits_word t v
    exact ⟨l,by rw [←hl,word_map]⟩
  have xsq (j : Fin d) : x j^2 ∈ q.ker := by rw [MonoidHom.mem_ker,map_pow,bit_sq]
  have xc (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ q.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,mul_comm]
  choose sq hsq using fun j => words (xsq j)
  choose cm hcm using fun p => words (xc p)
  have mem (w : H) (hw : w ∈ q.ker) : w ∈ Subgroup.closure (Set.range z) := by
    obtain ⟨l,rfl⟩ := words hw
    exact word_mem (Subgroup.closure (Set.range z)) z (fun j => Subgroup.subset_closure ⟨j,rfl⟩) l
  have zs (j : Fin t) : z j^2=1 := by change i (bit j)^2 = 1; rw [←map_pow,bit_sq,map_one]
  exact ⟨⟨⟨sq,cm⟩,z,x,zs,hsq,hcm,generate_lifts q x hx _ (fun {w} hw => mem w hw)⟩,
    fun j => ⟨bit j,rfl⟩⟩

end CentralKernelCount

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
    have hds : d+s=m := Nat.pow_right_injective (by decide : 1 < 2) hi
    have hsd : m-d=s := by omega
    apply Set.mem_iUnion_of_mem d
    apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m + 1))
    change Quotient.mk _ G ∈ frattiniClasses d (m-d)
    exact ⟨G, ⟨hc, he, hsd ▸ hs', hd'⟩,rfl⟩
  have hfin : U.Finite := (Finset.range (m+1)).finite_toSet.biUnion (fun i _ => frattiniClasses_finite i _)
  exact (Set.ncard_le_ncard hs hfin).trans ((Finset.range (m+1)).set_ncard_biUnion_le F)

end Erdos1160Growth.LowerTriangularUpper

end

/- PresentationCount -/
section

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

end

/- CentralQuotient -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper

structure CentralBridge (B E H : Type*) [Group B] [Group E] [Group H] where
  incl : B →* E
  proj : E →* H
  onto : Function.Surjective proj
  ker : proj.ker = incl.range
  central : incl.range ≤ Subgroup.center E
  liftCentral : ∀ y ∈ frattini H, ∃ z ∈ Subgroup.center E, proj z=y

def SmallProfile (G : FiniteGrp.{0}) (d t e : ℕ) : Prop :=
  frattini G ≤ Subgroup.center G ∧ (frattini G).index = 2^d ∧
  Nat.card (frattini G) = 2^(t+e) ∧ Nat.card (squareCore (frattini G)) = 2^e

def smallClasses (d t e : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | SmallProfile G d t e}

theorem squareCore_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    (squareCore G).map f = squareCore H := by
  rw [squareCore,squareCore,MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_,⟨g,rfl⟩,rfl⟩
    exact ⟨f g,(f.map_mul ..).symm⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨x,rfl⟩ := hf g
    exact ⟨x*x,⟨x,rfl⟩,f.map_mul ..⟩

theorem profile_card {G : FiniteGrp.{0}} {d t e : ℕ} (h : SmallProfile G d t e) :
    Nat.card G = 2^d * (2^t * 2^e) := by
  rw [←(frattini G).index_mul_card,h.2.1,h.2.2.1,pow_add]

theorem split_profile {E : FiniteGrp.{0}} {d t e : ℕ} (h : SmallProfile E d t e) :
    ∃ B H : FiniteGrp.{0}, Nat.card B=2^e ∧ Quotient.mk _ H ∈ frattiniClasses d t ∧
      (frattini H ≤ Subgroup.center H ∧ (∀ y : frattini H, y*y=1) ∧
        Nat.card (frattini H)=2^t ∧ (frattini H).index=2^d) ∧ Nonempty (CentralBridge B E H) := by
  let K := frattini E
  let D := (squareCore K).map K.subtype
  have DK : D ≤ K := by rintro _ ⟨x,_,rfl⟩; exact x.property
  letI := central_normal (DK.trans h.1)
  let q := QuotientGroup.mk' D
  let H := E ⧸ D
  let J := K.map q
  have hb : Nat.card D=2^e := (Subgroup.card_map_of_injective K.subtype_injective).trans h.2.2.2
  have eg : Nat.card E = 2^(d+t+e) := (profile_card h).trans (by simp [pow_add,Nat.mul_assoc])
  have hg : Nat.card H = 2^(d+t) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos e)
    calc
      Nat.card H * 2^e = Nat.card E := by
        simpa only [H,← hb,D.index_eq_card] using D.index_mul_card
      _ = 2^(d+t) * 2^e := by rw [eg,pow_add]
  have qonto : Function.Surjective q := QuotientGroup.mk'_surjective D
  have core : frattini H = J := by
    change frattini H = (frattini E).map q
    rw [frattini_eq_squareCore hg,frattini_eq_squareCore eg,squareCore_map q qonto]
  have qker : q.ker = D := QuotientGroup.ker_mk' D
  have comap : J.comap q = K := Subgroup.comap_map_eq_self (qker.le.trans DK)
  have idx : J.index = 2^d := by
    rw [← J.index_comap_of_surjective qonto,comap]
    exact h.2.1
  have jc : Nat.card J = 2^t := by
    apply Nat.mul_left_cancel (Nat.two_pow_pos d)
    calc
      2^d * Nat.card J = Nat.card H := idx ▸ J.index_mul_card
      _ = 2^d * 2^t := by rw [hg,pow_add]
  have z : J ≤ Subgroup.center H := by
    rintro _ ⟨x,hx,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := qonto y
    exact (q.map_mul ..).symm.trans ((congrArg q (Subgroup.mem_center_iff.mp (h.1 hx) w)).trans (q.map_mul ..))
  have sq (y : J) : y*y=1 := by
    obtain ⟨x,hx,hxy⟩ := y.property
    apply Subtype.ext
    change y.val*y.val=1
    rw [←hxy,←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    let v : K := ⟨x,hx⟩
    exact ⟨v*v,Subgroup.subset_closure ⟨v,rfl⟩,rfl⟩
  have hclass : frattini H ≤ Subgroup.center H ∧ (∀ y : frattini H, y*y=1) ∧
      Nat.card (frattini H)=2^t ∧ (frattini H).index=2^d := by rw [core]; exact ⟨z,sq,jc,idx⟩
  refine ⟨FiniteGrp.of D,FiniteGrp.of H,hb,⟨FiniteGrp.of H,hclass,rfl⟩,hclass,
    ⟨⟨D.subtype,q,qonto,?_,?_,?_⟩⟩⟩
  · exact qker.trans (Subgroup.range_subtype D).symm
  · exact (Subgroup.range_subtype D).le.trans (DK.trans h.1)
  · intro y hy
    change y ∈ frattini H at hy
    rw [core] at hy
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨x,h.1 hx,hxy⟩

end CentralKernelCount

end

/- SmallKernelCount -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper

theorem reference_of_frattini (H : FiniteGrp.{0}) {d t : ℕ}
    (hc : frattini H ≤ Subgroup.center H) (ht : ∀ x : frattini H,x*x=1)
    (hK : Nat.card (frattini H)=2^t) (hd : (frattini H).index=2^d) :
    ∃ R : Reference H d t, ∀ j, R.z j ∈ frattini H := by
  let K := frattini H
  letI := central_normal hc
  have hcard : Nat.card H=2^(d+t) := by
    rw [←(frattini H).index_mul_card,hd,hK,pow_add]
  have sq (y : H ⧸ K) : y*y=1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective K y
    rw [←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    change x*x ∈ frattini H
    rw [frattini_eq_squareCore hcard]
    exact Subgroup.subset_closure ⟨x,rfl⟩
  obtain ⟨f⟩ := exist_elementary_coords ht hK
  obtain ⟨g⟩ := exist_elementary_coords sq ((Subgroup.index_eq_card K).symm.trans hd)
  let S := dataOfSubgroup K hc f g
  obtain ⟨R,hR⟩ := reference_of_coordinates S.incl S.proj S.proj_onto S.exact_ker
  refine ⟨R,fun j => ?_⟩
  obtain ⟨z,hz⟩ := hR j
  rw [←hz]
  exact (f.symm z).property

theorem transport_bridge {B B' H H' E : Type*} [Group B] [Group B'] [Group H] [Group H']
    [Group E] (D : CentralBridge B E H) (b : B ≃* B') (h : H ≃* H') :
    Nonempty (CentralBridge B' E H') := by
  let i := D.incl.comp b.symm.toMonoidHom
  let q := h.toMonoidHom.comp D.proj
  have ir : i.range = D.incl.range := by
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨b.symm w,rfl⟩
    · rintro ⟨w,rfl⟩
      exact ⟨b w,by simp [i]⟩
  have qk : q.ker=D.proj.ker := by
    ext w
    change h (D.proj w) = 1 ↔ D.proj w = 1
    rw [←h.map_one]
    exact h.injective.eq_iff
  refine ⟨⟨i,q,h.surjective.comp D.onto,qk.trans (D.ker.trans ir.symm),ir ▸ D.central,?_⟩⟩
  intro y hy
  have hpre : h.symm y ∈ frattini H :=
    (frattini_le_comap_frattini_of_surjective (φ := h.symm.toMonoidHom) h.symm.surjective) hy
  obtain ⟨z,hz,he⟩ := D.liftCentral _ hpre
  exact ⟨z,hz,by simp [q,he]⟩

private noncomputable def isom {B H : FiniteGrp.{0}}
    (p : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) B = Quotient.mk _ H) : B ≃* H :=
  ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact p))).groupIsoToMulEquiv

private theorem smallFinite (d t e : ℕ) : (smallClasses d t e).Finite := by
  apply (Erdos1160.Tables.orderClasses_finite (2^(d+t+e))).subset
  rintro _ ⟨G,h,rfl⟩
  exact ⟨G,(profile_card h).trans (by simp [pow_add,Nat.mul_assoc]),rfl⟩

/-- For Φ central and |2Φ|=2^e, pass to the elementary-Frattini quotient and
count precisely the remaining central relator values. -/
theorem small_kernel_count (d t e : ℕ) :
    (smallClasses d t e).ncard ≤
      (Erdos1160.g (2^e)*(frattiniClasses d t).ncard) * 2^(e*(t+d+d*(d-1)/2)) := by
  classical
  let C := ↥(smallClasses d t e)
  let Keys := Erdos1160.Tables.orderClasses (2^e) × frattiniClasses d t
  letI : Finite C := (smallFinite d t e).to_subtype
  letI := (Erdos1160.Tables.orderClasses_finite (2^e)).to_subtype
  letI := (frattiniClasses_finite d t).to_subtype
  have reps (u : C) : ∃ G : FiniteGrp.{0}, SmallProfile G d t e ∧ Quotient.mk _ G = u.val := u.property
  choose G prof rep using reps
  choose B H hb hh hspec bridge using fun u => split_profile (prof u)
  let key (u : C) : Keys := (⟨Quotient.mk _ (B u),B u,hb u,rfl⟩,⟨Quotient.mk _ (H u),hh u⟩)
  have fibers (k : Keys) : Nat.card {u : C // key u = k} ≤ 2^(e*(t+d+d*(d-1)/2)) := by
    let F := {u : C // key u=k}
    by_cases empty : Nonempty F
    · let r : F := empty.some
      let b := B r.val
      let h := H r.val
      have spec := hspec r.val
      obtain ⟨R,hr⟩ := reference_of_frattini h spec.1 spec.2.1 spec.2.2.1 spec.2.2.2
      have O (u : F) : Nonempty (Over R b (G u.val)) := by
        have eqK : key u.val = key r.val := u.property.trans r.property.symm
        let be : B u.val ≃* b := isom (congrArg (fun z : Keys => z.1.val) eqK)
        let he : H u.val ≃* h := isom (congrArg (fun z : Keys => z.2.val) eqK)
        obtain ⟨A⟩ := transport_bridge (bridge u.val).some be he
        exact ⟨⟨A.incl,A.proj,A.onto,A.ker,A.central,fun i => A.liftCentral _ (hr i)⟩⟩
      have size (u : F) : 2^d*(2^t*Nat.card b) ≤ Nat.card (G u.val) := by
        rw [profile_card (prof u.val),show Nat.card b=2^e from hb r.val]
      have sep (u v : F) (he : Nonempty (G u.val ≃* G v.val)) : u=v := by
        apply Subtype.ext
        apply Subtype.ext
        rw [←rep u.val,←rep v.val]
        apply Quotient.sound
        exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
          (MulEquiv.toGrpIso (X := (G u.val).toGrp) (Y := (G v.val).toGrp) he.some)⟩
      have bd := count_over_reference R (fun u : F => (G u.val : Type)) O size sep
      simpa only [show Nat.card b=2^e from hb r.val,←pow_mul] using bd
    · letI : IsEmpty F := not_nonempty_iff.mp empty
      change Nat.card F ≤ _
      simp
  have count := Erdos1160.PresentationCount.card_le_of_fiber_bound key _ fibers
  rw [show Nat.card Keys = Erdos1160.g (2^e)*(frattiniClasses d t).ncard from Nat.card_prod ..] at count
  exact count

end CentralKernelCount

end

/- ThirdOver -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement

abbrev Ctwo := Multiplicative (ZMod 2)

structure ThirdBridge (E H : Type*) [Group E] [Group H] where
  incl : Ctwo →* E
  inj : Function.Injective incl
  proj : E →* H
  onto : Function.Surjective proj
  ker : proj.ker=incl.range
  central : incl.range ≤ Subgroup.center E

private lemma ctwo_square (a : Ctwo) : a*a=1 := by
  change a.toAdd+a.toAdd=0
  exact (show ∀ z : ZMod 2,z+z=0 by decide) _

private lemma sq_commute_of_binary_commutator {E : Type*} [Group E] (x y : E)
    (hc : ⁅x,y⁆ ∈ Subgroup.center E) (ht : ⁅x,y⁆*⁅x,y⁆=1) : Commute (x*x) y := by
  let c := ⁅x,y⁆
  have cs : c*x=x*c := (Subgroup.mem_center_iff.mp hc x).symm
  have swap : c*y*x=x*y := by dsimp [c,commutatorElement_def];group
  calc
    (x*x)*y = x*(x*y) := mul_assoc ..
    _ = x*(c*y*x) := by rw [swap]
    _ = (c*x)*(y*x) := by rw [cs];group
    _ = c*(x*y)*x := by group
    _ = (c*c)*(y*(x*x)) := by rw [←swap];group
    _ = y*(x*x) := by rw [ht,one_mul]

theorem commutator_over_core {E H : Type*} [Group E] [Group H] (L : ThirdBridge E H)
    (zh : frattini H ≤ Subgroup.center H) {w : E} (hw : L.proj w ∈ frattini H) (g : E) :
    ⁅g,w⁆ ∈ L.incl.range := by
  rw [←L.ker,MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.mp (zh hw) _

theorem lifted_core_commutes {E H : Type*} [Group E] [Group H] (L : ThirdBridge E H)
    (zh : frattini H ≤ Subgroup.center H) (w : E) (hw : L.proj w ∈ frattini H) :
    ∀ y ∈ squareCore E, Commute y w := by
  have hbound : squareCore E ≤ Subgroup.centralizer {w} := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g,rfl⟩
    have hmem := commutator_over_core L zh hw g
    obtain ⟨b,hb⟩ := hmem
    have hc := sq_commute_of_binary_commutator g w (L.central ⟨b,hb⟩)
      (by rw [←hb,←map_mul,ctwo_square,map_one])
    apply Subgroup.mem_centralizer_iff.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact hc.eq.symm
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hbound hy) w (Set.mem_singleton _)).symm

/-- Every central C₂ extension of an elementary-Frattini quotient admits commuting
lifts of its Frattini generators. The x-z commutators encode a binary action matrix. -/
theorem exists_third_marks {E H : Type*} [Group E] [Group H] [Finite H]
    {d t : ℕ} (R : Reference H d t) (L : ThirdBridge E H) (hcardH : Nat.card H=2^(d+t))
    (zh : frattini H ≤ Subgroup.center H) (rz : ∀ j,R.z j∈frattini H) :
    ∃ (D : ThirdMarks Ctwo E d t) (c : CodeSlot d t → Ctwo) (M : Fin d → Fin t → ZMod 2),
      ThirdFits R.toPattern D c ∧
      (∀ i j, ⁅D.x i,D.z j⁆=D.incl (Multiplicative.ofAdd (M i j))) ∧
      D.incl=L.incl ∧ (∀ i,L.proj (D.x i)=R.x i) ∧ (∀ j,L.proj (D.z j)=R.z j) := by
  classical
  have lifts (j : Fin t) : ∃ z ∈ squareCore E,L.proj z=R.z j := by
    have h := rz j
    rw [frattini_eq_squareCore hcardH,←squareCore_map L.proj L.onto] at h
    exact h
  choose z zmem hz using lifts
  choose x hx using fun i : Fin d => L.onto (R.x i)
  have zc (i j : Fin t) : Commute (z i) (z j) :=
    lifted_core_commutes L zh (z j) (hz j ▸ rz j) _ (zmem i)
  have gen : adjoin (adjoin L.incl.range z) x=⊤ := by
    let S := adjoin (adjoin L.incl.range z) x
    have simage : S.map L.proj=⊤ := by
      change (adjoin (adjoin L.incl.range z) x).map L.proj=⊤
      have emptyimage : L.incl.range.map L.proj = ⊥ := by rw [←L.ker,Subgroup.map_eq_bot_iff]
      rw [map_adjoin,map_adjoin,emptyimage]
      simpa only [hx,hz,adjoin,bot_sup_eq] using R.generate
    apply top_unique
    intro g _
    obtain ⟨v,hv,he⟩ : L.proj g ∈ S.map L.proj := by rw [simage];trivial
    have hker : g*v⁻¹ ∈ L.incl.range := by rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
    have hw : g*v⁻¹∈S := ((show L.incl.range ≤ adjoin L.incl.range z from le_sup_left).trans
      (show adjoin L.incl.range z ≤ S from le_sup_left)) hker
    simpa using S.mul_mem hw hv
  let D : ThirdMarks Ctwo E d t := ⟨L.incl,z,x,L.central,zc,gen⟩
  have wmap (w : List (Fin t)) : L.proj (word z w) = word R.z w := by rw [word_map];simp only [hz]
  have solve (g h : E) (he : L.proj g=L.proj h) : ∃ k, g=L.incl k * h := by
    obtain ⟨b,hb⟩ : g*h⁻¹ ∈ L.incl.range := by rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
    exact ⟨b,by rw [hb,inv_mul_cancel_right]⟩
  have zsq (j : Fin t) : ∃ b,z j ^ 2 = L.incl b := by
    have h : L.proj (z j ^ 2)=L.proj 1 := by rw [map_pow,hz,R.z_square,map_one]
    simpa only [mul_one] using solve (z j^2) 1 h
  have xsq (i : Fin d) : ∃ b,x i ^ 2 = L.incl b * word z (R.square i) := by
    apply solve
    rw [map_pow,hx,R.x_square,wmap]
  have xcomm (p : PairSlot d) : ∃ b,⁅x p.1,x (second p)⁆=L.incl b*word z (R.comm p) := by
    apply solve
    rw [map_commutatorElement,hx,hx,R.x_comm,wmap]
  choose c1 h1 using zsq
  choose c2 h2 using xsq
  choose c3 h3 using xcomm
  choose m hm using fun i j => commutator_over_core L zh (show L.proj (z j)∈frattini H by rw [hz];exact rz j) (x i)
  refine ⟨D,Sum.elim c1 (Sum.elim c2 c3),fun i j => (m i j).toAdd,⟨h1,h2,h3⟩,?_,rfl,hx,hz⟩
  exact fun i j => (hm i j).symm

end CentralKernelCount

end

/- PowerReference -/
section

namespace CentralKernelCount

open ClassTwoProfile
open scoped commutatorElement

theorem cyclic_words {s : ℕ} (b : Fin s→ℕ) (v : Factors b) :
    ∃ w, word (gen b) w=v := by
  induction v using Pi.mulSingle_induction with
  | one => exact ⟨[],rfl⟩
  | mul v w hv hw =>
    obtain ⟨k,hk⟩ := hv
    obtain ⟨l,hl⟩ := hw
    exact ⟨k++l,by simpa only [word,List.map_append,List.prod_append] using congrArg₂ (·*·) hk hl⟩
  | mulSingle j y =>
    let a := y.toAdd.val
    have h : y=(Multiplicative.ofAdd (1 : ZMod (2^b j)))^a := by
      change y.toAdd=a • (1 : ZMod (2^b j))
      simp [a,nsmul_eq_mul]
    refine ⟨List.replicate a j,?_⟩
    change ((List.replicate a j).map (gen b)).prod=Pi.mulSingle j y
    rw [List.map_replicate,List.prod_replicate,gen,←Pi.mulSingle_pow,←h]

noncomputable def cyclicWord {s : ℕ} (b : Fin s→ℕ) (v : Factors b) : List (Fin s) :=
  (cyclic_words b v).choose

theorem cyclicWord_correct {s : ℕ} (b : Fin s→ℕ) (v : Factors b) :
    word (gen b) (cyclicWord b v)=v := (cyclic_words b v).choose_spec

noncomputable def cyclicPattern {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ} (p : Code e b) : Pattern d s :=
  ⟨fun i => cyclicWord b (p.1 i),fun l => cyclicWord b (p.2 l).val⟩

structure PowerReference (H : Type*) [Group H] {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ) where
  code : Code e b
  z : Fin s→H
  x : Fin d→H
  z_pow : ∀j,z j^(2^b j)=1
  z_central : ∀j,z j∈Subgroup.center H
  x_pow : ∀j,x j^(2^e j)=word z ((cyclicPattern code).square j)
  x_comm : ∀l,⁅x l.1,x (second l)⁆=word z ((cyclicPattern code).comm l)
  generate : adjoin (Subgroup.closure (Set.range z)) x=⊤

/-- Recover a reference after independently permuting the two ordered generator systems.
The cyclic orders move together with their generators. -/
noncomputable def powerRef {H : Type} [Group H] {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ}
    (S : Data H e b) (u : Equiv.Perm (Fin d)) (v : Equiv.Perm (Fin s)) :
    PowerReference H (e ∘ u) (b ∘ v) := by
  classical
  let pull : Factors b ≃* Factors (b ∘ v) :=
    { Equiv.piCongrLeft' (fun j => Cyc (b j)) v.symm with map_mul' := fun _ _ => rfl }
  let reindex := pull.symm
  have inv (z : Factors b) (j : Fin s) : (reindex.symm z) j = z (v j) := by rfl
  have reg (j : Fin s) : reindex (gen (b ∘ v) j)=gen b (v j) := by
    apply reindex.symm.injective
    rw [reindex.symm_apply_apply]
    funext l
    change gen (b ∘ v) j l=(gen b (v j)) (v l)
    by_cases h : j=l
    · subst l; simp [gen]
    · rw [gen,Pi.mulSingle_eq_of_ne (Ne.symm h),gen,Pi.mulSingle_eq_of_ne (v.injective.ne (Ne.symm h))]
  let z (j : Fin s) := S.incl (gen b (v j))
  let x (j : Fin d) := S.x (u j)
  let p : Code (e ∘ u) (b ∘ v) :=
    (fun i => reindex.symm (S.powCode (u i)),
      fun l => ⟨reindex.symm (S.commCode (u l.1) (u (second l))).val,by
        rw [←map_pow]; exact (congrArg reindex.symm (S.commCode (u l.1) (u (second l))).property).trans reindex.symm.map_one⟩)
  have wordVal (w : Factors b) : word z (cyclicWord (b ∘ v) (reindex.symm w))=S.incl w := by
    let f := S.incl.comp reindex.toMonoidHom
    have hgen : (fun j => f (gen (b ∘ v) j))=z := funext (fun j => congrArg S.incl (reg j))
    rw [←hgen,←word_map,cyclicWord_correct]
    simp [f]
  have hz : S.incl.range = Subgroup.closure (Set.range z) := by
    rw [S.incl.range_eq_map,←gen_closure b,S.incl.map_closure]
    congr 1
    change S.incl '' Set.range (gen b) = Set.range ((S.incl ∘ gen b) ∘ v)
    rw [Set.range_comp (S.incl ∘ gen b) v,v.surjective.range_eq,Set.image_univ,Set.range_comp]
  have hx : Set.range x=Set.range S.x := by
    change Set.range (S.x ∘ u)=_
    rw [Set.range_comp,u.surjective.range_eq,Set.image_univ]
  refine ⟨p,z,x,?_,fun j=>S.cent ⟨_,rfl⟩,?_,?_,?_⟩
  · intro j
    change S.incl (gen b (v j)) ^ (2^b (v j)) = 1
    rw [←map_pow,gen_pow,map_one]
  · intro j
    exact (S.powCode_spec (u j)).symm.trans (wordVal _).symm
  · intro l
    exact (S.commCode_spec (u l.1) (u (second l))).symm.trans (wordVal _).symm
  · rw [←hz,adjoin,hx]
    exact S.adjoin_eq

theorem powerRef_x {H : Type} [Group H] {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ}
    (S : Data H e b) (u : Equiv.Perm (Fin d)) (v : Equiv.Perm (Fin s)) (j : Fin d) :
    (powerRef S u v).x j = S.x (u j) := rfl
theorem powerRef_z {H : Type} [Group H] {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ}
    (S : Data H e b) (u : Equiv.Perm (Fin d)) (v : Equiv.Perm (Fin s)) (j : Fin s) :
    (powerRef S u v).z j = S.incl (gen b (v j)) := rfl

end CentralKernelCount

end

/- PowerOver -/
section

namespace CentralKernelCount

open ClassTwoProfile
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement

theorem power_marks_from {E H : Type*} [Group E] [Group H] {d s : ℕ}
    {e : Fin d→ℕ} {b : Fin s→ℕ}
    (R : PowerReference H e b) (L : ThirdBridge E H) (x : Fin d→E) (z : Fin s→E)
    (hx : ∀i,L.proj (x i)=R.x i) (hz : ∀j,L.proj (z j)=R.z j)
    (zc : ∀i j,Commute (z i) (z j)) :
    ∃ (D : ThirdMarks Ctwo E d s) (c : CodeSlot d s→Ctwo) (M : Fin d → Fin s → ZMod 2),
      PowerFits e b (cyclicPattern R.code) D c ∧
      (∀i j,⁅D.x i,D.z j⁆=D.incl (Multiplicative.ofAdd (M i j))) ∧
      D.incl=L.incl ∧ D.x=x ∧ D.z=z := by
  classical
  let S := adjoin (adjoin L.incl.range z) x
  have gen : S=⊤ := by
    have simage : S.map L.proj=⊤ := by
      change (adjoin (adjoin L.incl.range z) x).map L.proj=⊤
      have emptyimage : L.incl.range.map L.proj = ⊥ := by rw [←L.ker,Subgroup.map_eq_bot_iff]
      rw [map_adjoin,map_adjoin,emptyimage]
      simpa only [hx,hz,adjoin,bot_sup_eq] using R.generate
    apply top_unique
    intro g _
    obtain ⟨v,hv,he⟩ : L.proj g ∈ S.map L.proj := by rw [simage];trivial
    have hker : g*v⁻¹ ∈ L.incl.range := by rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
    have hw : g*v⁻¹∈S := ((show L.incl.range ≤ adjoin L.incl.range z from le_sup_left).trans
      (show adjoin L.incl.range z ≤ S from le_sup_left)) hker
    simpa using S.mul_mem hw hv
  let D : ThirdMarks Ctwo E d s := ⟨L.incl,z,x,L.central,zc,gen⟩
  have wmap (w : List (Fin s)) : L.proj (word z w) = word R.z w := by rw [word_map];simp only [hz]
  have solve (g h : E) (he : L.proj g=L.proj h) : ∃ k, g=L.incl k * h := by
    obtain ⟨a,ha⟩ : g*h⁻¹ ∈ L.incl.range := by rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
    exact ⟨a,by rw [ha,inv_mul_cancel_right]⟩
  have zsq (j : Fin s) : ∃ a, z j ^ (2^b j) = L.incl a := by
    have h : L.proj (z j ^ (2^b j))=L.proj 1 := by rw [map_pow,hz,R.z_pow,map_one]
    simpa only [mul_one] using solve (z j^(2^b j)) 1 h
  have xsq (i : Fin d) : ∃ a, x i ^ (2^e i) = L.incl a * word z ((cyclicPattern R.code).square i) := by
    apply solve
    rw [map_pow,hx,R.x_pow,wmap]
  have xcomm (p : PairSlot d) : ∃ a,⁅x p.1,x (second p)⁆=L.incl a*word z ((cyclicPattern R.code).comm p) := by
    apply solve
    rw [map_commutatorElement,hx,hx,R.x_comm,wmap]
  choose c1 h1 using zsq
  choose c2 h2 using xsq
  choose c3 h3 using xcomm
  have cross (i : Fin d) (j : Fin s) : ⁅x i,z j⁆∈L.incl.range := by
    rw [←L.ker,MonoidHom.mem_ker,map_commutatorElement,hz,commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (R.z_central j) _
  choose m hm using cross
  refine ⟨D,Sum.elim c1 (Sum.elim c2 c3),fun i j => (m i j).toAdd,⟨h1,h2,h3⟩,?_,rfl,rfl,rfl⟩
  exact fun i j => (hm i j).symm

/-- The derived subgroup of any group of class at most three is abelian. -/
theorem derived_abelian {E : Type*} [Group E] (h : ThirdLowerCentral.third E ≤ Subgroup.center E)
    {x y : E} (hx : x∈commutator E) (hy : y∈commutator E) : Commute x y := by
  let K := commutator E
  let T : Subgroup E := ⊤
  have hl : ⁅⁅K,T⁆,T⁆ = ⊥ := Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr h
  have hr : ⁅⁅T,K⁆,T⁆=⊥ := by rw [Subgroup.commutator_comm T K];exact hl
  have hab : ⁅K,K⁆=⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hr hl
  have sub := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hab
  exact (Subgroup.mem_centralizer_iff.mp (sub hx) y hy).symm

theorem map_derived {E H : Type*} [Group E] [Group H] (L : ThirdBridge E H) :
    (commutator E).map L.proj = commutator H := by
  rw [map_commutator_eq,MonoidHom.range_eq_top.mpr L.onto]
  rfl

/-- With K=H′ the kernel generators may be lifted into G′; with K=Φ(H) central they
may be lifted into the subgroup generated by squares. In either situation all lifts commute. -/
theorem commuting_power_lifts {E H : Type} [Group E] [Group H] [Finite H] {d s : ℕ}
    {e : Fin d→ℕ} {b : Fin s→ℕ} (S : Data H e b) (L : ThirdBridge E H)
    (h3 : ThirdLowerCentral.third E ≤ Subgroup.center E) {m : ℕ} (hsize : Nat.card H = 2^m)
    (hk : S.incl.range = commutator H ∨ S.incl.range = frattini H) :
    ∃ (x : Fin d→E) (z : Fin s→E), (∀ i, L.proj (x i) = S.x i) ∧
      (∀j,L.proj (z j)=S.incl (gen b j)) ∧ ∀j k,Commute (z j) (z k) := by
  classical
  choose x hx using fun i => L.onto (S.x i)
  have target (j : Fin s) : S.incl (gen b j)∈S.incl.range := ⟨_,rfl⟩
  rcases hk with h | h
  · have src (j : Fin s) : S.incl (gen b j)∈ (commutator E).map L.proj :=
      (map_derived L).symm ▸ (h ▸ target j)
    choose z hz he using src
    exact ⟨x,z,hx,he,fun j k => derived_abelian h3 (hz j) (hz k)⟩
  · have src (j : Fin s) : S.incl (gen b j) ∈ (squareCore E).map L.proj := by
      rw [squareCore_map L.proj L.onto,←frattini_eq_squareCore hsize,←h]
      exact target j
    choose z hz he using src
    have zH : frattini H ≤ Subgroup.center H := h ▸ S.cent
    refine ⟨x,z,hx,he,fun j k => lifted_core_commutes L zH (z k) ?_ _ (hz j)⟩
    rw [he,←h]
    exact target k

end CentralKernelCount

end

/- CanonicalReference -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement

noncomputable def standardWord {t : ℕ} (v : BitGroup t) : List (Fin t) :=
  (bits_word t v).choose

theorem standardWord_correct {t : ℕ} (v : BitGroup t) : word bit (standardWord v)=v :=
  (bits_word t v).choose_spec

structure Standard {H : Type*} [Group H] {d t : ℕ} (R : Reference H d t) : Prop where
  sq : ∀ i,∃ v : BitGroup t,R.square i=standardWord v
  comm : ∀ p,∃ v : BitGroup t,R.comm p=standardWord v

theorem standard_of_coords {H : Type*} [Group H] {d t : ℕ}
    (i : BitGroup t →* H) (q : H →* BitGroup d) (hq : Function.Surjective q)
    (ker : q.ker=i.range) :
    ∃ R : Reference H d t, Standard R ∧ (∀ j,R.z j = i (bit j)) ∧ (∀ j,q (R.x j) = bit j) := by
  classical
  let z (j : Fin t) := i (bit j)
  choose x hx using fun j : Fin d => hq (bit j)
  have get {h : H} (hh : h ∈ q.ker) : ∃ v : BitGroup t, h=word z (standardWord v) := by
    rw [ker] at hh
    obtain ⟨v,rfl⟩ := hh
    exact ⟨v,(congrArg i (standardWord_correct v)).symm.trans (word_map i bit _)⟩
  have xsq (j : Fin d) : x j^2 ∈ q.ker := by rw [MonoidHom.mem_ker,map_pow,bit_sq]
  have xc (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ q.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,mul_comm]
  choose sq hsq using fun j => get (xsq j)
  choose cm hcm using fun p => get (xc p)
  have mem (w : H) (hw : w ∈ q.ker) : w ∈ Subgroup.closure (Set.range z) := by
    obtain ⟨v,rfl⟩ := get hw
    exact word_mem (Subgroup.closure (Set.range z)) z (fun j => Subgroup.subset_closure ⟨j,rfl⟩) _
  have zs (j : Fin t) : z j^2=1 := by change i (bit j)^2=1; rw [←map_pow,bit_sq,map_one]
  refine ⟨⟨⟨fun j => standardWord (sq j),fun p => standardWord (cm p)⟩,z,x,zs,hsq,hcm,
    generate_lifts q x hx _ (fun {w} hw => mem w hw)⟩,?_,fun _ => rfl,hx⟩
  exact ⟨fun j => ⟨sq j,rfl⟩,fun p => ⟨cm p,rfl⟩⟩

/-- Recompute just the relations, keeping the requested ordered lifts. Needed to move pivot
rows/columns into the designated chart after a binary action has been measured. -/
theorem standard_reindexed {H : Type*} [Group H] {d t : ℕ}
    {R : Reference H d t} (i : BitGroup t →* H) (q : H →* BitGroup d)
    (ker : q.ker=i.range) (rz : ∀ j,R.z j=i (bit j)) (rx : ∀ j,q (R.x j)=bit j)
    (u : Equiv.Perm (Fin d)) (v : Equiv.Perm (Fin t)) :
    ∃ S : Reference H d t, Standard S ∧ (∀ j,S.z j=R.z (v j)) ∧ (∀ j,S.x j=R.x (u j)) := by
  classical
  let z (j : Fin t) := R.z (v j)
  let x (j : Fin d) := R.x (u j)
  let perm : BitGroup t →* BitGroup t :=
    { toFun := fun w => Multiplicative.ofAdd (fun j => w.toAdd (v.symm j))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have perm_bit (j : Fin t) : perm (bit j)=bit (v j) := by
    apply Multiplicative.toAdd.injective
    funext l
    change (Pi.single j (1 : ZMod 2) : Fin t → ZMod 2) (v.symm l) = (Pi.single (v j) (1 : ZMod 2) : Fin t → ZMod 2) l
    simp only [Pi.single_apply]
    by_cases he : v j = l
    · subst l; simp
    · have h2 : j ≠ v.symm l := by intro h; apply he; rw [h,v.apply_symm_apply]
      simp [he,Ne.symm he,h2,Ne.symm h2]
  have words {h : H} (hh : h ∈ q.ker) : ∃ w : BitGroup t,h=word z (standardWord w) := by
    rw [ker] at hh
    obtain ⟨w,rfl⟩ := hh
    let w' : BitGroup t := Multiplicative.ofAdd (fun j => w.toAdd (v j))
    have wcomp : perm w'=w := by apply Multiplicative.toAdd.injective; funext j; simp [perm,w']
    have mapbit : ∀j, (i.comp perm) (bit j)=z j := fun j => (congrArg i (perm_bit j)).trans (rz _).symm
    refine ⟨w',?_⟩
    calc
      _ = (i.comp perm) w' := (congrArg i wcomp).symm
      _ = (i.comp perm) (word bit (standardWord w')) := congrArg _ (standardWord_correct w').symm
      _ = _ := by rw [word_map]; simp only [mapbit]
  have xsq (j : Fin d) : x j^2 ∈ q.ker := by rw [MonoidHom.mem_ker,map_pow,bit_sq]
  have xc (p : PairSlot d) : ⁅x p.1,x (second p)⁆ ∈ q.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,mul_comm]
  choose sq hsq using fun j => words (xsq j)
  choose cm hcm using fun p => words (xc p)
  have gen : adjoin (Subgroup.closure (Set.range z)) x=⊤ := by
    have hz : Set.range z = Set.range R.z := by change Set.range (R.z ∘ v) = _; rw [Set.range_comp,v.surjective.range_eq,Set.image_univ]
    have hx : Set.range x = Set.range R.x := by change Set.range (R.x ∘ u) = _; rw [Set.range_comp,u.surjective.range_eq,Set.image_univ]
    simpa only [adjoin,hz,hx] using R.generate
  refine ⟨⟨⟨fun j => standardWord (sq j),fun p => standardWord (cm p)⟩,z,x,fun j => R.z_square _,hsq,hcm,gen⟩,
    ⟨fun j => ⟨sq j,rfl⟩,fun p => ⟨cm p,rfl⟩⟩,fun _ => rfl,fun _ => rfl⟩

end CentralKernelCount

end

/- RectangleRank -/
section

namespace OrbitUp

theorem count_small_rank_matrices (d t r : ℕ) :
    Nat.card {A : Matrix (Fin d) (Fin t) K // A.rank ≤ r} ≤ 2^(r*(d+t)) := by
  classical
  let _ (p q : ℕ) : Finite (V p →ₗ[K] V q) :=
    Finite.of_equiv (Matrix (Fin q) (Fin p) K) LinearMap.toMatrix'.symm.toEquiv
  have card (p q : ℕ) : Nat.card (V p →ₗ[K] V q) = 2^(p*q) := by
    rw [Nat.card_congr (LinearMap.toMatrix' : (V p →ₗ[K] V q) ≃ₗ[K] Matrix (Fin q) (Fin p) K).toEquiv]
    change Nat.card (Fin q → Fin p → ZMod 2) = _
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
  let S := {A : Matrix (Fin d) (Fin t) K // A.rank ≤ r}
  let f (A : S) := A.val.mulVecLin
  have fac (A : S) : ∃ z : (V t →ₗ[K] V r) × (V r →ₗ[K] V d), z.2.comp z.1 = f A := by
    have hdim : Module.finrank K (LinearMap.range (f A)) ≤ Module.finrank K (V r) := by
      rw [Module.finrank_fin_fun]; exact A.property
    obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.mp hdim
    obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
    refine ⟨⟨i.comp (f A).rangeRestrict, (f A).range.subtype.comp p⟩, ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun hp ((f A).rangeRestrict x))
  let code (A : S) := (fac A).choose
  have hi : Function.Injective code := by
    intro A B h
    have he : f A = f B := (fac A).choose_spec.symm.trans
      ((congrArg (fun z : (V t →ₗ[K] V r) × (V r →ₗ[K] V d) => z.2.comp z.1) h).trans (fac B).choose_spec)
    apply Subtype.ext
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using he)
  calc
    _ ≤ Nat.card ((V t →ₗ[K] V r) × (V r →ₗ[K] V d)) := Nat.card_le_card_of_injective code hi
    _ = _ := by rw [Nat.card_prod,card,card,←pow_add]; congr 1; ring

end OrbitUp

end

/- ThirdLow -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement

structure ChosenFrame (d t : ℕ) where
  H : FiniteGrp.{0}
  R : Reference H d t
  standard : Standard R
  i : BitGroup t →* H
  q : H →* BitGroup d
  ker : q.ker=i.range
  rz : ∀ j,R.z j=i (bit j)
  rx : ∀ j,q (R.x j)=bit j
  hz : ∀j, R.z j∈frattini H
  central : frattini H ≤ Subgroup.center H
  size : Nat.card H = 2^(d+t)

private theorem choose_frame (d t : ℕ) (u : frattiniClasses d t) :
    ∃ A : ChosenFrame d t, Quotient.mk _ A.H=u.val := by
  obtain ⟨H,hp,he⟩ := u.property
  change frattini H ≤ Subgroup.center H ∧ (∀ g : frattini H,g*g=1) ∧
    Nat.card (frattini H)=2^t ∧ (frattini H).index=2^d at hp
  let K := frattini H
  letI := central_normal hp.1
  have sz : Nat.card H=2^(d+t) := by rw [←(frattini H).index_mul_card,hp.2.2.2,hp.2.2.1,pow_add]
  have sq (x : H ⧸ K) : x*x=1 := by
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [←map_mul]
    apply (QuotientGroup.eq_one_iff _).mpr
    change g*g ∈ frattini H
    rw [frattini_eq_squareCore sz]
    exact Subgroup.subset_closure ⟨g,rfl⟩
  obtain ⟨e⟩ := exist_elementary_coords hp.2.1 hp.2.2.1
  obtain ⟨v⟩ := exist_elementary_coords sq ((Subgroup.index_eq_card K).symm.trans hp.2.2.2)
  let S := dataOfSubgroup K hp.1 e v
  obtain ⟨R,hR,rz,rx⟩ := standard_of_coords S.incl S.proj S.proj_onto S.exact_ker
  exact ⟨⟨H,R,hR,S.incl,S.proj,S.exact_ker,rz,rx,fun j => rz j ▸ (e.symm (bit j)).property,hp.1,sz⟩,he⟩

noncomputable def refFrame {d t : ℕ} (h : frattiniClasses d t) := (choose_frame d t h).choose

theorem refClass {d t : ℕ} (h : frattiniClasses d t) : Quotient.mk _ (refFrame h).H=h.val :=
  (choose_frame d t h).choose_spec

theorem third_transport {E H K : Type*} [Group E] [Group H] [Group K] (D : ThirdBridge E H)
    (h : H ≃* K) : Nonempty (ThirdBridge E K) := by
  refine ⟨⟨D.incl,D.inj,h.toMonoidHom.comp D.proj,h.surjective.comp D.onto,?_,D.central⟩⟩
  rw [←D.ker]
  ext w
  change h (D.proj w) = 1 ↔ D.proj w = 1
  rw [←h.map_one]
  exact h.injective.eq_iff

def ThirdOn (d t : ℕ) (E : FiniteGrp.{0}) : Prop :=
  Nat.card E=2^(d+t+1) ∧ ∃ h : frattiniClasses d t, Nonempty (ThirdBridge E (refFrame h).H)

def allThird (d t : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | ThirdOn d t E}

structure LowWitness (d t r : ℕ) (E : FiniteGrp.{0}) where
  key : frattiniClasses d t
  marks : ThirdMarks Ctwo E d t
  code : CodeSlot d t → Ctwo
  mat : Matrix (Fin d) (Fin t) (ZMod 2)
  fits : ThirdFits (refFrame key).R.toPattern marks code
  action : ∀ i j, ⁅marks.x i,marks.z j⁆=marks.incl (Multiplicative.ofAdd (mat i j))
  rank : mat.rank ≤ r

def lowThirdClasses (d t r : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | Nat.card E=2^(d+t+1) ∧ Nonempty (LowWitness d t r E)}

theorem low_third_count (d t r : ℕ) : (lowThirdClasses d t r).ncard ≤
    (frattiniClasses d t).ncard * 2^(r*(d+t)) * 2^(t+d+d*(d-1)/2) := by
  classical
  let C := ↥(lowThirdClasses d t r)
  let M := {A : Matrix (Fin d) (Fin t) (ZMod 2) // A.rank ≤ r}
  letI := (frattiniClasses_finite d t).to_subtype
  have witness (u : C) : ∃ G : FiniteGrp.{0}, (Nat.card G=2^(d+t+1) ∧ Nonempty (LowWitness d t r G))
      ∧ Quotient.mk _ G=u.val := u.property
  choose G gg he using witness
  let w (u : C) := (gg u).2.some
  let enc (u : C) : frattiniClasses d t × (M × (CodeSlot d t → Ctwo)) :=
    ⟨(w u).key,⟨(w u).mat,(w u).rank⟩,(w u).code⟩
  have cardC2 : Nat.card Ctwo=2 := Nat.card_zmod 2
  have sz (u : C) : 2^d*(2^t*Nat.card Ctwo) ≤ Nat.card (G u) := by
    rw [cardC2,(gg u).1,pow_succ,pow_add,Nat.mul_assoc]
  have inj : Function.Injective enc := by
    intro u v eq
    have keys : (w u).key=(w v).key := congrArg Prod.fst eq
    have mats : (w u).mat=(w v).mat := congrArg (fun z : frattiniClasses d t × (M × (CodeSlot d t → Ctwo)) => z.2.1.val) eq
    have codes : (w u).code=(w v).code := congrArg (fun z => z.2.2) eq
    have fit : ThirdFits (refFrame (w u).key).R.toPattern (w v).marks (w u).code := by rw [keys,codes];exact (w v).fits
    have act (i j) : ⁅(w v).marks.x i,(w v).marks.z j⁆=
        (w v).marks.incl (Multiplicative.ofAdd ((w u).mat i j)) := by rw [mats];exact (w v).action i j
    have iso := third_separation _ (w u).marks (w v).marks (w u).code (w u).fits fit _ (w u).action act (sz u) (sz v)
    apply Subtype.ext
    rw [←he u,←he v]
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (G u).toGrp) (Y := (G v).toGrp) iso.some)⟩
  have slots : Nat.card (CodeSlot d t)=t+d+d*(d-1)/2 := by
    have pr : Nat.card (PairSlot d)=d*(d-1)/2 := by
      rw [PairSlot,Nat.card_sigma]
      simp only [Nat.card_fin]
      exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
    rw [CodeSlot,Nat.card_sum,Nat.card_sum,Nat.card_fin,Nat.card_fin,pr,Nat.add_assoc]
  have mcount : Nat.card M ≤ 2^(r*(d+t)) := OrbitUp.count_small_rank_matrices d t r
  have size := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fun,cardC2,slots] at size
  exact size.trans <| (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ mcount)).trans_eq (Nat.mul_assoc ..).symm

end CentralKernelCount

end

/- DefectRanges -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper

def defectClasses (m e : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧ frattini G ≤ Subgroup.center G ∧
    Nat.card (squareCore (frattini G)) = 2^e}

theorem small_classes_finite (d t e : ℕ) : (smallClasses d t e).Finite := by
  apply (Erdos1160.Tables.orderClasses_finite (2^(d+t+e))).subset
  rintro _ ⟨G,h,rfl⟩
  exact ⟨G,(profile_card h).trans (by simp [pow_add,Nat.mul_assoc]),rfl⟩

theorem zero_small_subset (d t : ℕ) : smallClasses d t 0 ⊆ frattiniClasses d t := by
  rintro _ ⟨G,h,rfl⟩
  have hs : squareCore (frattini G) = ⊥ :=
    (squareCore (frattini G)).eq_bot_of_card_eq (by simpa using h.2.2.2)
  have hel (v : frattini G) : v*v=1 := by
    have hv : v*v ∈ squareCore (frattini G) := Subgroup.subset_closure ⟨v,rfl⟩
    rw [hs] at hv
    exact hv
  exact ⟨G,⟨h.1,hel,by simpa using h.2.2.1,h.2.1⟩,rfl⟩

theorem defect_subset_rank_union (m e : ℕ) :
    defectClasses m e ⊆ ⋃ d ∈ Finset.range (m-e+1), smallClasses d (m-e-d) e := by
  rintro _ ⟨G,⟨hc,hz,hb⟩,rfl⟩
  let K := frattini G
  have hk := K.index_mul_card
  rw [hc] at hk
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show K.index ∣ 2^m from ⟨_,hk.symm⟩)
  obtain ⟨s,_,hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card K ∣ 2^m from (dvd_mul_left _ _).trans (dvd_of_eq hk))
  have hsum : d+s=m := Nat.pow_right_injective (by decide : 1 < 2) (by rwa [hd,hs,←pow_add] at hk)
  have he : e ≤ s := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
    rw [←hs,←hb]
    exact (squareCore K).card_le_card_group)
  apply Set.mem_iUnion_of_mem d
  apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m-e+1))
  refine ⟨G,⟨hz,hd,?_,hb⟩,rfl⟩
  exact hs.trans (congrArg (2^·) (by omega))

theorem defectClasses_le_sum (m e : ℕ) :
    (defectClasses m e).ncard ≤ ∑ d ∈ Finset.range (m-e+1), (smallClasses d (m-e-d) e).ncard := by
  let F := fun d => smallClasses d (m-e-d) e
  have hfin : (⋃ d ∈ Finset.range (m-e+1), F d).Finite :=
    (Finset.range (m-e+1)).finite_toSet.biUnion (fun i _ => small_classes_finite i _ e)
  exact (Set.ncard_le_ncard (defect_subset_rank_union m e) hfin).trans
    ((Finset.range (m-e+1)).set_ncard_biUnion_le F)

end CentralKernelCount

end

/- PowerLow -/
section

namespace CentralKernelCount

open CategoryTheory ClassTwoProfile Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement

abbrev binaryOrders (d : ℕ) : Fin d → ℕ := fun _ => 1
abbrev classSpace := Quotient (isIsomorphicSetoid FiniteGrp.{0})

structure PowerFrame (H : FiniteGrp.{0}) (d t a : ℕ) where
  profile : SmallProfile H d t a
  b : Fin t → ℕ
  pos : ∀j,0 < b j
  total : ∑ j,b j=t+a
  coords : Data H (binaryOrders d) b
  image : coords.incl.range=frattini H

def powerBases (d t a : ℕ) : Set classSpace :=
  Quotient.mk _ '' {H : FiniteGrp.{0} | Nonempty (PowerFrame H d t a)}

theorem powerBases_subset_small (d t a : ℕ) : powerBases d t a ⊆ smallClasses d t a := by
  rintro _ ⟨H,⟨F⟩,rfl⟩
  exact ⟨H,F.profile,rfl⟩

noncomputable def powerBase {d t a : ℕ} (u : powerBases d t a) : FiniteGrp.{0} := u.property.choose
noncomputable def powerFrame {d t a : ℕ} (u : powerBases d t a) : PowerFrame (powerBase u) d t a :=
  u.property.choose_spec.1.some
theorem powerBase_rep {d t a : ℕ} (u : powerBases d t a) : Quotient.mk _ (powerBase u)=u.val :=
  u.property.choose_spec.2
noncomputable def firstRef {d t a : ℕ} (u : powerBases d t a) :=
  powerRef (powerFrame u).coords (Equiv.refl _) (Equiv.refl _)

structure LowPowerWitness (d t a r : ℕ) (E : FiniteGrp.{0}) where
  key : powerBases d t a
  marks : ThirdMarks Ctwo E d t
  code : CodeSlot d t → Ctwo
  mat : Matrix (Fin d) (Fin t) (ZMod 2)
  fits : PowerFits (binaryOrders d) (powerFrame key).b (cyclicPattern (firstRef key).code) marks code
  action : ∀i j, ⁅marks.x i,marks.z j⁆=marks.incl (Multiplicative.ofAdd (mat i j))
  rank : mat.rank ≤ r

def lowPowerClasses (d t a r : ℕ) : Set classSpace :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | Nat.card E=2^(d+t+a+1) ∧ Nonempty (LowPowerWitness d t a r E)}

theorem power_profile_size {d t a : ℕ} {b : Fin t → ℕ} (ht : ∑j,b j=t+a) :
    (∏i,2^binaryOrders d i)*((∏j,2^b j)*2) = 2^(d+t+a+1) := by
  simp only [binaryOrders,pow_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum,ht,pow_succ 2 (d+t+a),pow_add]
  ring

theorem code_slot_card (d t : ℕ) : Nat.card (CodeSlot d t)=t+d+d*(d-1)/2 := by
  have pr : Nat.card (PairSlot d)=d*(d-1)/2 := by
    rw [PairSlot,Nat.card_sigma]
    simp only [Nat.card_fin]
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
  rw [CodeSlot,Nat.card_sum,Nat.card_sum,Nat.card_fin,Nat.card_fin,pr,Nat.add_assoc]

theorem low_power_count (d t a r : ℕ) : (lowPowerClasses d t a r).ncard ≤
    (smallClasses d t a).ncard * 2^(r*(d+t)) * 2^(t+d+d*(d-1)/2) := by
  classical
  let C := ↥(lowPowerClasses d t a r)
  let M := {A : Matrix (Fin d) (Fin t) (ZMod 2) // A.rank ≤ r}
  have hfin := (small_classes_finite d t a).subset (powerBases_subset_small d t a)
  letI := hfin.to_subtype
  have witness (u : C) : ∃ G : FiniteGrp.{0}, (Nat.card G=2^(d+t+a+1) ∧ Nonempty (LowPowerWitness d t a r G))
      ∧ Quotient.mk _ G=u.val := u.property
  choose G gg he using witness
  let w (u : C) := (gg u).2.some
  let enc (u : C) : powerBases d t a × (M × (CodeSlot d t → Ctwo)) :=
    ⟨(w u).key,⟨(w u).mat,(w u).rank⟩,(w u).code⟩
  have cardC2 : Nat.card Ctwo=2 := Nat.card_zmod 2
  have sz (u : C) (k : powerBases d t a) :
      (∏i,2^binaryOrders d i)*((∏j,2^(powerFrame k).b j)*Nat.card Ctwo) ≤ Nat.card (G u) := by
    rw [cardC2,power_profile_size (powerFrame k).total,(gg u).1]
  have inj : Function.Injective enc := by
    intro u v eq
    have keys : (w u).key=(w v).key := congrArg Prod.fst eq
    have mats : (w u).mat=(w v).mat := congrArg (fun z : powerBases d t a × (M × (CodeSlot d t → Ctwo)) => z.2.1.val) eq
    have codes : (w u).code=(w v).code := congrArg (fun z => z.2.2) eq
    have fit : PowerFits (binaryOrders d) (powerFrame (w u).key).b (cyclicPattern (firstRef (w u).key).code) (w v).marks (w u).code := by
      rw [keys,codes];exact (w v).fits
    have act (i j) : ⁅(w v).marks.x i,(w v).marks.z j⁆=
        (w v).marks.incl (Multiplicative.ofAdd ((w u).mat i j)) := by rw [mats];exact (w v).action i j
    have iso := power_separation _ _ _ (w u).marks (w v).marks (w u).code (w u).fits fit _ (w u).action act (sz u _) (sz v _)
    apply Subtype.ext
    rw [←he u,←he v]
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (G u).toGrp) (Y := (G v).toGrp) iso.some)⟩
  have mcount : Nat.card M ≤ 2^(r*(d+t)) := OrbitUp.count_small_rank_matrices d t r
  have size := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fun,cardC2,code_slot_card] at size
  have ks : Nat.card (powerBases d t a) ≤ (smallClasses d t a).ncard :=
    Set.ncard_le_ncard (powerBases_subset_small d t a) (small_classes_finite d t a)
  exact size.trans <| (Nat.mul_le_mul ks (Nat.mul_le_mul_right _ mcount)).trans_eq (Nat.mul_assoc ..).symm

end CentralKernelCount

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

/- PowerArithmetic -/
section

namespace CentralKernelCount
open OrbitUp Erdos1160Growth.LowerTriangularUpper

private theorem factors (a b c d e : ℕ) : (a*b*c)*d*e = ((a*d)*b)*(c*e) := by ring

theorem low_power_upper (d t a : ℕ) (ha : a ≤ 3) (hu : 10000000 ≤ d+t) :
    (lowPowerClasses d t a 34).ncard^27*2^(10*(d+t+a+1)^2) ≤ 2^(2*(d+t+a+1)^3) := by
  let L := slotsN d+t
  have hcard : Erdos1160.g (2^a) ≤ 2^27 := calc
    _ ≤ Erdos1160.g (2^a)^6 := Nat.le_self_pow (by decide) _
    _ ≤ 2^(a^3) := Erdos1160.CentralLifts.prime_power_upper Nat.prime_two a
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left ha 3)
  have hex : t+d+d*(d-1)/2 = L := by dsimp [L,slotsN];omega
  have h₁ := low_power_count d t a 34
  have h₂ := small_kernel_count d t a
  rw [hex] at h₁ h₂
  have h0 : (smallClasses d t a).ncard ≤ (2^27*Nat.card (Classes d t))*2^(a*L) :=
    h₂.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hcard (frattini_le_quadraticOrbits d t)))
  have h3 : (lowPowerClasses d t a 34).ncard ≤
      (2^(128*(d+t)+262144)*Nat.card (Classes d t))*2^((a+1)*L) := h₁.trans (calc
    _ ≤ ((2^27*Nat.card (Classes d t))*2^(a*L))*2^(34*(d+t))*2^L :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
    _ = ((2^27*2^(34*(d+t)))*Nat.card (Classes d t))*(2^(a*L)*2^L) := factors _ _ _ _ _
    _ = (2^(27+34*(d+t))*Nat.card (Classes d t))*2^((a+1)*L) := by
      rw [←Nat.pow_add,←Nat.pow_add,Nat.add_mul,one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide)
      (show 27+34*(d+t) ≤ 128*(d+t)+262144 by omega))))
  have h := bounded_action_uniform (e:=a+1) (by omega) hu h3
  rwa [show d+(t+(a+1))=d+t+a+1 by omega] at h

theorem padded_estimate {d t a X : ℕ} (ha : a ≤ 3) (hu : 10000000 ≤ d+t)
    (hx : X*2^(32*((d-32)*((d-32)-1)/2)) ≤ 2^(t*slotsN d+d*t+slotsN d+t+d*a+2*t)) :
    X^27*2^(10*(d+t+a+1)^2) ≤ 2^(2*(d+t+a+1)^3) := by
  have hda := Nat.mul_le_mul_left d ha
  have hnum : t*slotsN d+d*t+slotsN d+t+d*a+2*t ≤
      t*slotsN d+d*t+slotsN d+t+(128*(d+t)+262144) := by omega
  have hh := bounded_pivot_uniform hu (hx.trans (Nat.pow_le_pow_right (by decide) hnum))
  exact increase_order_budget (k:=d+(t+1)) (by omega) (by omega) hh

end CentralKernelCount

end

/- JacobiCount -/
section

namespace Erdos1160.DeepJacobi

abbrev Bit := ZMod 2
abbrev V (s : ℕ) := Fin s → Bit
abbrev W (q s : ℕ) := V q × V s
abbrev Pair (n : ℕ) := (i : Fin n) × Fin i.val
abbrev Old (q n : ℕ) := Pair q ⊕ (Fin q × Fin n)
abbrev Array (q n s : ℕ) := (Old q n → W q s) × (Pair n → W q s)
abbrev Code (q n s : ℕ) := (Old q n → W q s) × (Pair n → V s)

variable {q n s : ℕ}

def encode (a : Array q n s) : Code q n s := (a.1, fun ij => (a.2 ij).2)

def mixed (a : Array q n s) (c : Fin q) (i : Fin n) : W q s := a.1 (.inr (c,i))

def low (ij : Pair n) : Fin n := ⟨ij.2.val, lt_trans ij.2.isLt ij.1.isLt⟩

/-- Jacobi for a triple consisting of one core generator and two outside generators,
after applying a fixed binary linear measurement to the third bracket layer. -/
def compatible (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (a : Array q n s) : Prop :=
  ∀ ij : Pair n, ∀ c : Fin q, core (a.2 ij) c =
    outside ij.1 (mixed a c (low ij)) - outside (low ij) (mixed a c ij.1)

lemma pivot_separates (core : W q s →+ V q)
    (h : Function.Injective (fun v : V q => core (v,0)))
    {u v : W q s} (hs : u.2 = v.2) (hc : core u = core v) : u = v := by
  apply Prod.ext _ hs
  apply h
  have hu : u = (u.1,0) + (0,u.2) := by simp
  have hv : v = (v.1,0) + (0,v.2) := by simp
  calc
    core (u.1,0) = core u - core (0,u.2) := by conv => rhs; rw [hu,map_add]; simp
    _ = core v - core (0,v.2) := by rw [hc,hs]
    _ = core (v.1,0) := by conv => lhs; rw [hv,map_add]; simp

theorem recover (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (h : Function.Injective (fun v : V q => core (v,0)))
    {a b : Array q n s} (ha : compatible core outside a) (hb : compatible core outside b)
    (e : encode a = encode b) : a = b := by
  have hOld : a.1 = b.1 := congrArg (fun w : Code q n s => w.1) e
  have hRest : ∀ ij, (a.2 ij).2 = (b.2 ij).2 := congrFun (congrArg (fun w : Code q n s => w.2) e)
  apply Prod.ext hOld
  funext ij
  apply pivot_separates core h (hRest ij)
  funext c
  rw [ha ij c, hb ij c]
  simp only [mixed,hOld]

theorem card_saved (q n s : ℕ) :
    Nat.card (Code q n s) * 2^(q*(n*(n-1)/2)) = Nat.card (Array q n s) := by
  change Nat.card ((Old q n → W q s) × (Pair n → V s)) * _ =
    Nat.card ((Old q n → W q s) × (Pair n → W q s))
  rw [Nat.card_prod,Nat.card_prod,Nat.mul_assoc]
  apply congrArg (Nat.card (Old q n → W q s) * ·)
  simp only [W,V,Nat.card_fun,Nat.card_prod,Nat.card_fin,Nat.card_zmod,
    ← pow_add, ← pow_mul, Erdos1160Growth.SharpFamily.triangular_card n]
  congr 1
  ring

/-- A fixed third bracket of pivot rank q removes q*binom(n,2) independent binary
coordinates from first-layer bracket arrays on q core and n outside generators. -/
theorem fixed_tensor_count (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (h : Function.Injective (fun v : V q => core (v,0))) :
    Nat.card {a : Array q n s // compatible core outside a} * 2^(q*(n*(n-1)/2))
      ≤ Nat.card (Array q n s) := by
  have he : Function.Injective (fun a : {a : Array q n s // compatible core outside a} => encode a.val) :=
    fun a b hab => Subtype.ext (recover core outside h a.property b.property hab)
  simpa only [card_saved] using Nat.mul_le_mul_right (2^(q*(n*(n-1)/2))) (Nat.card_le_card_of_injective _ he)

end Erdos1160.DeepJacobi

end

/- ClassThreeJacobi -/
section

namespace Erdos1160.DeepJacobi

open scoped commutatorElement

variable {G : Type*} [Group G]

def TripleCentral (G : Type*) [Group G] : Prop :=
  ∀ a b c : G, ⁅⁅a,b⁆,c⁆ ∈ Subgroup.center G

private lemma conj_center (a : G) {v : G} (hv : v ∈ Subgroup.center G) : a*v*a⁻¹=v := by
  rw [Subgroup.mem_center_iff.mp hv a, mul_inv_cancel_right]

private lemma discard_center_factor {v : G} (hv : v ∈ Subgroup.center G) (b c : G) :
    ⁅v*b,c⁆ = ⁅b,c⁆ := by
  have h₁ := (Subgroup.mem_center_iff.mp hv ⁅b,c⁆).symm
  have h₂ : Commute v c := (Subgroup.mem_center_iff.mp hv c).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h₁, mul_inv_cancel_right, h₂.commutator_eq, mul_one]

private lemma corrected_inner (H : TripleCentral G) (a b c : G) :
    ⁅⁅a⁻¹,b⁆,c⁆ = ⁅⁅b,a⁆,c⁆ := by
  have h : ⁅a⁻¹,⁅b,a⁆⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem (H b a a⁻¹)
  have he : a⁻¹*⁅b,a⁆*a = ⁅a⁻¹,⁅b,a⁆⁆ * ⁅b,a⁆ := by
    rw [commutatorElement_def (a⁻¹) ⁅b,a⁆]
    group
  rw [commutatorElement_inv_left,he,discard_center_factor h]

/-- Hall–Witt becomes the multiplicative Jacobi identity when all triple
commutators are central (in particular in a group of nilpotency class at most 3). -/
theorem triple_cycle (H : TripleCentral G) (x y z : G) :
    ⁅⁅x,y⁆,z⁆ * ⁅⁅z,x⁆,y⁆ * ⁅⁅y,z⁆,x⁆ = 1 := by
  have h := conj_commutatorElement_left_commutatorElement_mul y x z
  rw [corrected_inner H y x z, corrected_inner H z y x, corrected_inner H x z y] at h
  have hg : y*⁅⁅x,y⁆,z⁆*y⁻¹ * (z*⁅⁅y,z⁆,x⁆*z⁻¹) * (x*⁅⁅z,x⁆,y⁆*x⁻¹) = 1 := by
    simpa only [mul_assoc] using h
  rw [conj_center y (H x y z),conj_center z (H y z x),conj_center x (H z x y)] at hg
  have hc := Subgroup.mem_center_iff.mp (H y z x) ⁅⁅z,x⁆,y⁆
  simpa only [mul_assoc, hc] using hg

/-- Reverse the first commutator in a triple. -/
private theorem flip_triple (H : TripleCentral G) (a b c : G) :
    ⁅⁅b,a⁆,c⁆ = ⁅⁅a,b⁆,c⁆⁻¹ := by
  rw [← commutatorElement_inv a b, commutatorElement_inv_left]
  rw [← commutatorElement_inv ⁅a,b⁆ c]
  have h := (Subgroup.center G).inv_mem (H a b c)
  simpa using conj_center (⁅a,b⁆⁻¹) h

theorem triple_rearranged (H : TripleCentral G) (x y z : G) :
    ⁅⁅y,z⁆,x⁆ = ⁅⁅x,z⁆,y⁆ * ⁅⁅x,y⁆,z⁆⁻¹ := by
  have hc := triple_cycle H x y z
  rw [flip_triple H x z y] at hc
  exact (eq_inv_of_mul_eq_one_right hc).trans (by simp)

end Erdos1160.DeepJacobi

end

/- MarkedJacobi -/
section

namespace Erdos1160.DeepJacobi

open scoped commutatorElement
variable {G : Type*} [Group G] {J : Type*} {q n s : ℕ}

def inclBit (incl : Multiplicative Bit →* G) (b : Bit) : G := incl (Multiplicative.ofAdd b)

lemma inclBit_add (incl : Multiplicative Bit →* G) (a b : Bit) :
    inclBit incl (a+b) = inclBit incl a * inclBit incl b := incl.map_mul ..

lemma inclBit_sub (incl : Multiplicative Bit →* G) (a b : Bit) :
    inclBit incl (a-b) = inclBit incl a * (inclBit incl b)⁻¹ := by
  rw [sub_eq_add_neg,inclBit_add]
  exact congrArg (inclBit incl a * ·) (incl.map_inv (Multiplicative.ofAdd b))

lemma inclBit_injective {incl : Multiplicative Bit →* G} (h : Function.Injective incl) :
    Function.Injective (inclBit incl) := fun _ _ e => congrArg Multiplicative.toAdd (h e)

private lemma central_conj {v : G} (h : v ∈ Subgroup.center G) (g : G) :
    g*v*g⁻¹=v := by rw [Subgroup.mem_center_iff.mp h g,mul_inv_cancel_right]

def wordVector (coord : J → W q s) (l : List J) : W q s := (l.map coord).sum

/-- A central factor twisting a presentation relator disappears on taking
a further commutator. -/
lemma central_factor {a : G} (h : a ∈ Subgroup.center G) (b c : G) : ⁅a*b,c⁆ = ⁅b,c⁆ := by
  have h₁ := (Subgroup.mem_center_iff.mp h ⁅b,c⁆).symm
  have h₂ : Commute a c := (Subgroup.mem_center_iff.mp h c).symm
  rw [commutatorElement_mul_left_eq_conj_mul,h₁,mul_inv_cancel_right,h₂.commutator_eq,mul_one]

/-- The action of a generator on a word in second-layer lifts is the sum
of its action on the letters. -/
theorem word_action (incl : Multiplicative Bit →* G) (hc : incl.range ≤ Subgroup.center G)
    (coord : J → W q s) (z : J → G) (x : G) (row : W q s →+ Bit)
    (ha : ∀ j, ⁅z j,x⁆ = inclBit incl (row (coord j))) (l : List J) :
    ⁅(l.map z).prod,x⁆ = inclBit incl (row (wordVector coord l)) := by
  induction l with
  | nil => simpa [wordVector,inclBit] using (show incl (1 : Multiplicative Bit) = 1 from incl.map_one).symm
  | cons j l ih =>
    change ⁅z j*(l.map z).prod,x⁆ = inclBit incl (row (coord j + wordVector coord l))
    rw [commutatorElement_mul_left_eq_conj_mul,ih,ha,map_add,add_comm (row (coord j)),inclBit_add]
    rw [central_conj (show inclBit incl (row (wordVector coord l)) ∈ Subgroup.center G from hc ⟨_,rfl⟩)]

def WordArray (q n : ℕ) (J : Type*) := (Old q n → List J) × (Pair n → List J)

def parityArray (coord : J → W q s) (l : WordArray q n J) : Array q n s :=
  (fun i => wordVector coord (l.1 i),fun i => wordVector coord (l.2 i))

/-- In an actual marked class-three central extension by C₂, the binary
coordinates of the quotient commutator words satisfy the pivot-chart Jacobi
constraints; arbitrary central twists of those relators are allowed. -/
theorem marked_words_compatible (hG : TripleCentral G) (incl : Multiplicative Bit →* G)
    (hi : Function.Injective incl) (hc : incl.range ≤ Subgroup.center G) (z : J → G) (coord : J → W q s)
    (x : Fin q → G) (y : Fin n → G) (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (hcx : ∀ j i, ⁅z j,x i⁆ = inclBit incl (core (coord j) i))
    (hcy : ∀ j i, ⁅z j,y i⁆ = inclBit incl (outside i (coord j)))
    (l : WordArray q n J)
    (hmix : ∀ i j, ∃ b, ⁅x i,y j⁆ = inclBit incl b * ((l.1 (.inr (i,j))).map z).prod)
    (hoth : ∀ ij, ∃ b, ⁅y ij.1,y (low ij)⁆ = inclBit incl b * ((l.2 ij).map z).prod) :
    compatible core outside (parityArray coord l) := by
  intro ij c
  have hcin (b : Bit) : inclBit incl b ∈ Subgroup.center G := hc ⟨_,rfl⟩
  let r : W q s →+ Bit := (Pi.evalAddMonoidHom _ c).comp core
  have hx (j : J) : ⁅z j,x c⁆ = inclBit incl (r (coord j)) := hcx j c
  obtain ⟨b₁,h₁⟩ := hoth ij
  obtain ⟨b₂,h₂⟩ := hmix c (low ij)
  obtain ⟨b₃,h₃⟩ := hmix c ij.1
  have hj := triple_rearranged hG (x c) (y ij.1) (y (low ij))
  rw [h₁,h₂,h₃,central_factor (hcin _),central_factor (hcin _),central_factor (hcin _),
    word_action incl hc coord z (x c) r hx,
    word_action incl hc coord z (y ij.1) (outside ij.1) (fun j => hcy j ij.1),
    word_action incl hc coord z (y (low ij)) (outside (low ij)) (fun j => hcy j (low ij)),
    ← inclBit_sub] at hj
  exact inclBit_injective hi hj

end Erdos1160.DeepJacobi

end

/- GroupBracketLoss -/
section

namespace Erdos1160.DeepJacobi

open scoped commutatorElement
variable {q n s : ℕ} {G : Type*} [Group G]

abbrev Third (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 2

def triple (x y z : G) : Third G :=
  ⟨⁅⁅x,y⁆,z⁆,Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)) (Subgroup.mem_top z)⟩

theorem tripleCentral_of_class_le_three [Group.IsNilpotent G] (hc : Group.nilpotencyClass G ≤ 3) :
    TripleCentral G := by
  have h : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le).2 hc
  have hz : Third G ≤ Subgroup.center G := Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h
  exact fun a b c => hz (triple a b c).property

/-- A linear probe of the third lower-central layer, evaluated on an actual
triple commutator. -/
def probe (measure : Third G →* Multiplicative Bit) (x y z : G) : Bit :=
  (measure (triple x y z)).toAdd

theorem probe_jacobi (H : TripleCentral G) (measure : Third G →* Multiplicative Bit) (x y z : G) :
    probe measure y z x = probe measure x z y - probe measure x y z := by
  have hv : triple y z x = triple x z y * (triple x y z)⁻¹ := Subtype.ext (triple_rearranged H x y z)
  rw [probe, hv, map_mul, map_inv]
  change probe measure x z y + -(probe measure x y z) = _
  rw [sub_eq_add_neg]

/-- The measured brackets are realized by a finite group of class at most three.
Here the core and outside maps specify the third bracket data shared across the family. -/
def groupRealized (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit) (a : Array q n s) : Prop :=
  ∃ (G : FiniteGrp.{0}) (_ : Group.IsNilpotent G) (_ : Group.nilpotencyClass G ≤ 3)
      (measure : Third G →* Multiplicative Bit) (x : Fin q → G) (y : Fin n → G),
    (∀ ij c, core (a.2 ij) c = probe measure (y ij.1) (y (low ij)) (x c)) ∧
    (∀ c j i, outside i (mixed a c j) = probe measure (x c) (y j) (y i))

theorem compatible_of_group (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit) {a : Array q n s}
    (h : groupRealized core outside a) : compatible core outside a := by
  obtain ⟨G,hG,hc,measure,x,y,ha,hm⟩ := h
  intro ij c
  rw [ha,hm,hm]
  exact probe_jacobi (tripleCentral_of_class_le_three hc) _ _ _ _

/-- Uniform binary loss for the first-layer commutator tables of actual
finite class-three groups with the displayed rank-q minor in the fixed
measured third bracket tensor. -/
theorem class_three_array_bound (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (h : Function.Injective (fun v : V q => core (v,0))) :
    Nat.card {a : Array q n s // groupRealized core outside a} * 2^(q*(n*(n-1)/2))
      ≤ Nat.card (Array q n s) := by
  let f (a : {a : Array q n s // groupRealized core outside a}) :
      {a : Array q n s // compatible core outside a} := ⟨a.val,compatible_of_group _ _ a.property⟩
  have hf : Function.Injective f := fun _ _ hab => Subtype.ext (congrArg (fun a : {a : Array q n s // compatible core outside a} => a.val) hab)
  exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf)).trans (fixed_tensor_count _ _ h)

end Erdos1160.DeepJacobi

end

/- QuotientBracketLoss -/
section

namespace Erdos1160.DeepJacobi

variable {q n s : ℕ}

abbrev Fourth (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 3

abbrev ThroughThird (G : Type*) [Group G] := G ⧸ Fourth G

theorem quotient_fourth_vanishes (G : Type*) [Group G] :
    Fourth (ThroughThird G) = ⊥ := by
  let f := QuotientGroup.mk' (Fourth G)
  have ht : (⊤ : Subgroup G).map f = ⊤ :=
    by rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top_of_surjective f (QuotientGroup.mk'_surjective _)
  have h := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) f 3
  rw [ht] at h
  exact h.symm.trans (QuotientGroup.map_mk'_self (Fourth G))

theorem quotient_fourth_isNilpotent (G : Type*) [Group G] :
    Group.IsNilpotent (ThroughThird G) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3,quotient_fourth_vanishes G⟩

theorem quotient_fourth_class (G : Type*) [Group G] :
    Group.nilpotencyClass (ThroughThird G) ≤ 3 := by
  let := quotient_fourth_isNilpotent G
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp (quotient_fourth_vanishes G)

/-- The bracket arrays from the first three layers of arbitrary finite groups:
the measurement is taken modulo the fourth lower-central subgroup. -/
def groupLayerRealized (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (a : Array q n s) : Prop :=
  ∃ (G : FiniteGrp.{0}) (measure : Third (ThroughThird G) →* Multiplicative Bit)
      (x : Fin q → G) (y : Fin n → G),
    (∀ ij c, core (a.2 ij) c = probe measure (y ij.1 : ThroughThird G) (y (low ij)) (x c)) ∧
    (∀ c j i, outside i (mixed a c j) = probe measure (x c : ThroughThird G) (y j) (y i))

theorem groupRealized_of_layers (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    {a : Array q n s} (h : groupLayerRealized core outside a) : groupRealized core outside a := by
  obtain ⟨G,measure,x,y,ha,hm⟩ := h
  exact ⟨FiniteGrp.of (ThroughThird G),quotient_fourth_isNilpotent G,quotient_fourth_class G,measure,
    (fun i => (x i : ThroughThird G)),(fun i => (y i : ThroughThird G)),ha,hm⟩

/-- For unrestricted finite groups the same loss is forced in the first
three lower-central layers at every pivot rank. -/
theorem group_layer_array_bound (core : W q s →+ V q) (outside : Fin n → W q s →+ Bit)
    (h : Function.Injective (fun v : V q => core (v,0))) :
    Nat.card {a : Array q n s // groupLayerRealized core outside a} * 2^(q*(n*(n-1)/2))
      ≤ Nat.card (Array q n s) := by
  let f (a : {a : Array q n s // groupLayerRealized core outside a}) :
      {a : Array q n s // groupRealized core outside a} := ⟨a.val,groupRealized_of_layers _ _ a.property⟩
  have hf : Function.Injective f := fun _ _ e =>
    Subtype.ext (congrArg (fun a : {a : Array q n s // groupRealized core outside a} => a.val) e)
  exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf)).trans (class_three_array_bound _ _ h)

end Erdos1160.DeepJacobi

end

/- TensorChart -/
section

namespace Erdos1160.DeepJacobi

variable {q n s : ℕ}

abbrev Chart (q n s : ℕ) := ((Fin q ⊕ Fin s) → V q) × (Fin n → V q)

noncomputable def coreEquiv (q s : ℕ) : ((Fin q ⊕ Fin s) → V q) ≃ (W q s →+ V q) :=
  (((Pi.basisFun Bit (Fin q)).prod (Pi.basisFun Bit (Fin s))).constr Bit).toEquiv.trans
    (AddMonoidHom.toZModLinearMapEquiv 2).symm.toEquiv

noncomputable def rowEquiv (q : ℕ) : V q ≃ (V q →+ Bit) :=
  ((Pi.basisFun Bit (Fin q)).constr Bit).toEquiv.trans
    (AddMonoidHom.toZModLinearMapEquiv 2).symm.toEquiv

/-- The tensor row indexed by any outside generator must lie in the span of
the q chosen core rows. The core minor is nonsingular. -/
def inPivotChart (a : Array q n s) : Prop :=
  ∃ (core : W q s →+ V q) (rows : Fin n → V q →+ Bit),
    Function.Injective (fun v : V q => core (v,0)) ∧
      groupLayerRealized core (fun i => (rows i).comp core) a

theorem card_chart (q n s : ℕ) : Nat.card (Chart q n s) = 2^(q*(q+s+n)) := by
  simp only [Chart,V,Nat.card_prod,Nat.card_fun,Nat.card_sum,Nat.card_fin,Nat.card_zmod, ← pow_mul,← pow_add]
  congr 1
  ring

/-- Union over all third-layer tensors of rank q with the specified pivot minor.
The freedom in the varying tensors costs at most q*(q+s+n) binary parameters.
The multiplicative saving is relative to the number of unrestricted first-layer
bracket arrays in these fixed coordinates. -/
theorem varying_tensor_count (q n s : ℕ) :
    Nat.card {a : Array q n s // inPivotChart a} * 2^(q*(n*(n-1)/2))
      ≤ 2^(q*(q+s+n)) * Nat.card (Array q n s) := by
  classical
  let S := {a : Array q n s // inPivotChart a}
  let c (a : S) : W q s →+ V q := a.property.choose
  let r (a : S) : Fin n → V q →+ Bit := a.property.choose_spec.choose
  have hc (a : S) : Function.Injective (fun v : V q => c a (v,0)) := a.property.choose_spec.choose_spec.1
  have hg (a : S) : compatible (c a) (fun i => (r a i).comp (c a)) a.val :=
    compatible_of_group _ _ (groupRealized_of_layers _ _ a.property.choose_spec.choose_spec.2)
  let f (a : S) : Chart q n s × Code q n s :=
    ⟨⟨(coreEquiv q s).symm (c a),fun i => (rowEquiv q).symm (r a i)⟩,encode a.val⟩
  have hf : Function.Injective f := by
    intro a b e
    have hcore : c a = c b := (coreEquiv q s).symm.injective
      (congrArg (fun z : Chart q n s × Code q n s => z.1.1) e)
    have hrow : r a = r b := by
      funext i
      exact (rowEquiv q).symm.injective (congrArg (fun z : Chart q n s × Code q n s => z.1.2 i) e)
    have hgb := hg b
    rw [← hcore, ← hrow] at hgb
    exact Subtype.ext (recover _ _ (hc a) (hg a) hgb
      (congrArg (fun z : Chart q n s × Code q n s => z.2) e))
  have h := Nat.mul_le_mul_right (2^(q*(n*(n-1)/2))) (Nat.card_le_card_of_injective f hf)
  rw [Nat.card_prod (α := Chart q n s) (β := Code q n s),Nat.mul_assoc,card_saved,card_chart] at h
  exact h

end Erdos1160.DeepJacobi

end

/- HighRankChart -/
section

namespace Erdos1160.DeepJacobi

abbrev FullTensor (q n s : ℕ) :=
  ((Fin q ⊕ Fin s) → V q) × (Fin n → (Fin q ⊕ Fin s) → Bit)

noncomputable def scalarEquiv (q s : ℕ) : ((Fin q ⊕ Fin s) → Bit) ≃ (W q s →+ Bit) :=
  (((Pi.basisFun Bit (Fin q)).prod (Pi.basisFun Bit (Fin s))).constr Bit).toEquiv.trans
    (AddMonoidHom.toZModLinearMapEquiv 2).symm.toEquiv

variable {q n s : ℕ}

noncomputable def fullCore (t : FullTensor q n s) : W q s →+ V q := coreEquiv _ _ t.1
noncomputable def fullOutside (t : FullTensor q n s) (i : Fin n) : W q s →+ Bit := scalarEquiv _ _ (t.2 i)

def jointHighChart (q n s : ℕ) := {z : FullTensor q n s × Array q n s //
    Function.Injective (fun v : V q => fullCore z.1 (v,0)) ∧
      compatible (fullCore z.1) (fullOutside z.1) z.2}

theorem full_tensor_card (q n s : ℕ) : Nat.card (FullTensor q n s) = 2^((q+s)*(q+n)) := by
  simp only [FullTensor,V,Nat.card_prod,Nat.card_fun,Nat.card_sum,Nat.card_fin,Nat.card_zmod,← pow_mul,← pow_add]
  congr 1
  ring

/-- Jointly count all action tensors AND quotient commutator tables for a
specified nonsingular minor of size q. Higher tensor ranks are included. -/
theorem high_chart_joint_count (q n s : ℕ) :
    Nat.card (jointHighChart q n s) * 2^(q*(n*(n-1)/2)) ≤
      2^((q+s)*(q+n)) * Nat.card (Array q n s) := by
  let f (a : jointHighChart q n s) : FullTensor q n s × Code q n s := (a.val.1,encode a.val.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨t,a⟩,hi,ha⟩ ⟨⟨u,b⟩,hj,hb⟩ he
    have ht : t=u := congrArg Prod.fst he
    subst u
    have hA : a=b := recover (fullCore t) (fullOutside t) hi ha hb (congrArg Prod.snd he)
    subst b
    rfl
  have h := Nat.mul_le_mul_right (2^(q*(n*(n-1)/2))) (Nat.card_le_card_of_injective f hf)
  rw [Nat.card_prod (α := FullTensor q n s) (β := Code q n s),Nat.mul_assoc,card_saved,full_tensor_card] at h
  exact h

/-- Turn given core and outside row maps into the counted coordinate tensor. -/
noncomputable def packTensor (core : W q s →+ V q) (out : Fin n → W q s →+ Bit) :
    FullTensor q n s := ((coreEquiv _ _).symm core,fun i => (scalarEquiv _ _).symm (out i))

@[simp] theorem fullCore_pack (core : W q s →+ V q) (out : Fin n → W q s →+ Bit) :
    fullCore (packTensor core out) = core := by simp [fullCore,packTensor]

@[simp] theorem fullOutside_pack (core : W q s →+ V q) (out : Fin n → W q s →+ Bit) :
    fullOutside (packTensor core out) = out := by funext i; simp [fullOutside,packTensor]

end Erdos1160.DeepJacobi

end

/- ThirdChart -/
section

namespace Erdos1160.DeepJacobi

open CentralKernelCount
open scoped commutatorElement

variable {G : Type*} [Group G] {q n s : ℕ}

def coreMark (i : Fin q) : Fin (n+q) := Fin.natAdd n i
def outMark (i : Fin n) : Fin (n+q) := Fin.castAdd q i

def mixedSlot (i : Fin q) (j : Fin n) : PairSlot (n+q) :=
  ⟨coreMark i,⟨j.val,by change j.val < n+i.val; have := j.isLt; omega⟩⟩

def outsideSlot (ij : Pair n) : PairSlot (n+q) := ⟨outMark ij.1,ij.2⟩

def coreSlot (ij : Pair q) : PairSlot (n+q) :=
  ⟨coreMark ij.1,⟨n+ij.2.val,Nat.add_lt_add_left ij.2.isLt n⟩⟩

def markedWords (P : Pattern (n+q) (q+s)) : WordArray q n (Fin (q+s)) :=
  (fun ij => match ij with
    | .inl c => P.comm (coreSlot c)
    | .inr (c,j) => P.comm (mixedSlot c j), fun ij => P.comm (outsideSlot ij))

noncomputable def coordBasis (q s : ℕ) := (Pi.basisFun Bit (Fin q)).prod (Pi.basisFun Bit (Fin s))

noncomputable def markCoords (q s : ℕ) (j : Fin (q+s)) : W q s :=
  coordBasis q s (finSumFinEquiv.symm j)

def markTensor (M : Fin (n+q) → Fin (q+s) → Multiplicative Bit) : FullTensor q n s :=
  (fun j c => (M (coreMark c) (finSumFinEquiv j)).toAdd,
    fun i j => (M (outMark i) (finSumFinEquiv j)).toAdd)

theorem core_on_basis (t : FullTensor q n s) (j : Fin q ⊕ Fin s) :
    fullCore t (coordBasis q s j) = t.1 j := by
  change (coordBasis q s).constr Bit t.1 (coordBasis q s j) = _
  simp

theorem outside_on_basis (t : FullTensor q n s) (i : Fin n) (j : Fin q ⊕ Fin s) :
    fullOutside t i (coordBasis q s j) = t.2 i j := by
  change (coordBasis q s).constr Bit (t.2 i) (coordBasis q s j) = _
  simp

theorem reverse_action {incl : Multiplicative Bit →* G} {x z : G} {b : Multiplicative Bit}
    (h : ⁅x,z⁆ = incl b) : ⁅z,x⁆ = inclBit incl b.toAdd := by
  rw [← commutatorElement_inv x z,h,← map_inv]
  congr 1
  exact (show ∀ a : ZMod 2, -a = a by decide) b.toAdd

/-- For every marked group in the one-dimensional deep-central-layer count,
the tensor of x–z commutators and the parity table of the quotient reference
give a pair counted by the high-rank Jacobi bound. The pivot generators occur
last in the x tuple and first in the z tuple. -/
theorem thirdMarks_compatible (P : Pattern (n+q) (q+s))
    (D : ThirdMarks (Multiplicative Bit) G (n+q) (q+s)) (hG : TripleCentral G)
    (hi : Function.Injective D.incl) (c : CodeSlot (n+q) (q+s) → Multiplicative Bit)
    (hc : ThirdFits P D c) (M : Fin (n+q) → Fin (q+s) → Multiplicative Bit)
    (hm : ∀ i j, ⁅D.x i,D.z j⁆ = D.incl (M i j)) :
    compatible (fullCore (markTensor M)) (fullOutside (markTensor M))
      (parityArray (markCoords q s) (markedWords P)) := by
  apply marked_words_compatible hG D.incl hi D.central D.z (markCoords q s) (D.x ∘ coreMark) (D.x ∘ outMark)
  · intro j i
    simp only [markCoords,core_on_basis,markTensor,Equiv.apply_symm_apply,Function.comp_apply]
    exact reverse_action (hm _ _)
  · intro j i
    simp only [markCoords,outside_on_basis,markTensor,Equiv.apply_symm_apply,Function.comp_apply]
    exact reverse_action (hm _ _)
  · intro i j
    exact ⟨(c (.inr (.inr (mixedSlot i j)))).toAdd,hc.2.2 (mixedSlot i j)⟩
  · intro ij
    exact ⟨(c (.inr (.inr (outsideSlot ij)))).toAdd,hc.2.2 (outsideSlot ij)⟩

end Erdos1160.DeepJacobi

end

/- ChartRecovery -/
section

namespace Erdos1160.DeepJacobi

open CentralKernelCount

variable {q n s : ℕ}

theorem read_word (l : List (Fin (q+s))) (i : Fin (q+s)) :
    (coordBasis q s).repr (wordVector (markCoords q s) l) (finSumFinEquiv.symm i) =
      (word bit l).toAdd i := by
  induction l with
  | nil => simp [wordVector,word]
  | cons j l ih =>
    change (coordBasis q s).repr (markCoords q s j + wordVector (markCoords q s) l) (finSumFinEquiv.symm i)
      = (bit j).toAdd i + (word bit l).toAdd i
    rw [map_add,Finsupp.add_apply,ih]
    by_cases h : i=j
    · subst j; simp [markCoords,bit,Pi.single_apply,Finsupp.single_apply]
    · simp [markCoords,bit,Pi.single_apply,Finsupp.single_apply,h,Ne.symm h]

theorem canonical_word_recover (std : BitGroup (q+s) → List (Fin (q+s)))
    (hs : ∀ v, word bit (std v) = v) {a b : BitGroup (q+s)}
    (h : wordVector (markCoords q s) (std a) = wordVector (markCoords q s) (std b)) : a=b := by
  apply congrArg Multiplicative.ofAdd
  funext i
  have e := congrArg (fun w : W q s => (coordBasis q s).repr w (finSumFinEquiv.symm i)) h
  change a.toAdd i = b.toAdd i
  simpa only [read_word,hs] using e

def allSlots : Old q n ⊕ Pair n → PairSlot (n+q)
  | .inl (.inl c) => coreSlot c
  | .inl (.inr (c,i)) => mixedSlot c i
  | .inr i => outsideSlot i

private lemma pair_ext {d : ℕ} (a b : PairSlot d) (hi : a.1.val = b.1.val) (hj : a.2.val = b.2.val) :
    a=b := by
  obtain ⟨i,j⟩ := a
  obtain ⟨k,l⟩ := b
  have h : i=k := Fin.ext hi
  subst k
  have h : j=l := Fin.ext hj
  subst l
  rfl

theorem allSlots_surj (q n : ℕ) : Function.Surjective (@allSlots q n) := by
  rintro ⟨i,j⟩
  have hi := i.isLt
  have hj := j.isLt
  by_cases h₁ : i.val < n
  · exact ⟨.inr ⟨⟨i.val,h₁⟩,j⟩,pair_ext _ _ rfl rfl⟩
  by_cases h₂ : j.val < n
  · let c : Fin q := ⟨i.val-n,by omega⟩
    let a : Fin n := ⟨j.val,h₂⟩
    refine ⟨.inl (.inr (c,a)),pair_ext _ _ ?_ rfl⟩
    change n+(i.val-n)=i.val
    omega
  · let c : Fin q := ⟨i.val-n,by omega⟩
    let a : Fin c.val := ⟨j.val-n,by dsimp [c]; omega⟩
    refine ⟨.inl (.inl ⟨c,a⟩),pair_ext _ _ ?_ ?_⟩
    · change n+(i.val-n)=i.val; omega
    · change n+(j.val-n)=j.val; omega

def stdPattern (std : BitGroup (q+s) → List (Fin (q+s)))
    (sq : Fin (n+q) → BitGroup (q+s)) (br : PairSlot (n+q) → BitGroup (q+s)) :
    Pattern (n+q) (q+s) := ⟨std ∘ sq,std ∘ br⟩

theorem comm_word_recover (std : BitGroup (q+s) → List (Fin (q+s))) (hs : ∀ v,word bit (std v) = v)
    {sq sq' : Fin (n+q) → BitGroup (q+s)} {a b : PairSlot (n+q) → BitGroup (q+s)}
    (h : parityArray (markCoords q s) (markedWords (stdPattern std sq a)) =
      parityArray (markCoords q s) (markedWords (stdPattern std sq' b))) : a=b := by
  funext p
  obtain ⟨i,rfl⟩ := allSlots_surj q n p
  apply canonical_word_recover std hs
  cases i with
  | inl i =>
    cases i with
    | inl i => exact congrFun (congrArg Prod.fst h) (.inl i)
    | inr i => exact congrFun (congrArg Prod.fst h) (.inr i)
  | inr i => exact congrFun (congrArg Prod.snd h) i

theorem markTensor_injective : Function.Injective (@markTensor q n s) := by
  intro M T e
  funext i j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  refine Fin.addCases (fun i => ?_) (fun c => ?_) i
  · exact congrArg Multiplicative.ofAdd (congrFun (congrFun (congrArg Prod.snd e) i) j)
  · exact congrArg Multiplicative.ofAdd (congrFun (congrFun (congrArg Prod.fst e) j) c)

end Erdos1160.DeepJacobi

end

/- CyclicParity -/
section

namespace Erdos1160.DeepJacobi

open ClassTwoProfile CentralKernelCount

variable {q n s : ℕ}

def cycParity {k : ℕ} (hk : 0 < k) (v : Cyc k) : Bit :=
  ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hk)) (ZMod 2) v.toAdd

theorem binary_parity_inj {k : ℕ} (hk : 0 < k) (h : k=1) :
    Function.Injective (cycParity hk) := by
  subst k
  intro x y he
  apply congrArg Multiplicative.ofAdd
  change x.toAdd = y.toAdd
  simpa only [cycParity,pow_one,ZMod.castHom_apply,ZMod.cast_id] using he

def bitLift {k : ℕ} (h : k=1) (v : Bit) : Cyc k := h ▸ Multiplicative.ofAdd v

theorem bitLift_inj {k : ℕ} (h : k=1) : Function.Injective (bitLift h) := by subst k; exact fun _ _ e => congrArg Multiplicative.toAdd e

theorem bitLift_pow {k a : ℕ} (h : k=1) (ha : 0 < a) (v : Bit) : bitLift h v ^ (2^a)=1 := by
  subst k
  have hv : bitLift rfl v ^ 2=1 := by
    change (2:ℕ) • v=0
    rw [two_nsmul]; exact (show ∀ z : ZMod 2, z+z=0 by decide) v
  obtain ⟨j,hj⟩ := dvd_pow_self 2 (Nat.ne_of_gt ha)
  rw [hj,pow_mul,hv,one_pow]

def parityHom {t : ℕ} (b : Fin t → ℕ) (hb : ∀ j,0 < b j) : Factors b →* BitGroup t where
  toFun w := Multiplicative.ofAdd fun j => cycParity (hb j) (w j)
  map_one' := by
    apply congrArg Multiplicative.ofAdd; funext j
    exact map_zero _
  map_mul' x y := by
    apply congrArg Multiplicative.ofAdd; funext j
    exact map_add _ _ _

theorem parity_gen {t : ℕ} (b : Fin t → ℕ) (hb : ∀ j,0 < b j) (i : Fin t) :
    parityHom b hb (gen b i) = bit i := by
  apply congrArg Multiplicative.ofAdd
  funext j
  classical
  by_cases h : j=i
  · subst j
    change cycParity _ (gen b i i) = ((Pi.single i (1:Bit)) : Fin t → Bit) i
    rw [gen,Pi.mulSingle_eq_same,Pi.single_eq_same]
    exact map_one _
  · simp [parityHom,gen,bit,cycParity,Pi.mulSingle_eq_of_ne h,Pi.single_eq_of_ne h]

theorem cyclic_word_bits {t : ℕ} (b : Fin t → ℕ) (hb : ∀ j,0 < b j) (std : Factors b → List (Fin t))
    (hw : ∀ v,word (gen b) (std v) = v) (v : Factors b) :
    word bit (std v)=parityHom b hb v := by
  have hmap := word_map (parityHom b hb) (gen b) (std v)
  rw [hw] at hmap
  simpa only [Function.comp_def,parity_gen] using hmap.symm

lemma coords_left (l : List (Fin (q+s))) (i : Fin q) :
    (wordVector (markCoords q s) l).1 i = (word bit l).toAdd (Fin.castAdd s i) := by
  have h := read_word l (Fin.castAdd s i)
  simpa [coordBasis] using h

lemma coords_right (l : List (Fin (q+s))) (i : Fin s) :
    (wordVector (markCoords q s) l).2 i = (word bit l).toAdd (Fin.natAdd q i) := by
  have h := read_word l (Fin.natAdd q i)
  simpa [coordBasis] using h

theorem cyclic_left (b : Fin (q+s) → ℕ) (hb : ∀ j,0 < b j) (std : Factors b → List (Fin (q+s)))
    (hw : ∀ v,word (gen b) (std v)=v) (v : Factors b) (i : Fin q) :
    (wordVector (markCoords q s) (std v)).1 i = cycParity (hb _) (v (Fin.castAdd s i)) := by
  rw [coords_left,cyclic_word_bits b hb std hw]; rfl

theorem cyclic_right (b : Fin (q+s) → ℕ) (hb : ∀ j,0 < b j) (std : Factors b → List (Fin (q+s)))
    (hw : ∀ v,word (gen b) (std v)=v) (v : Factors b) (i : Fin s) :
    (wordVector (markCoords q s) (std v)).2 i = cycParity (hb _) (v (Fin.natAdd q i)) := by
  rw [coords_right,cyclic_word_bits b hb std hw]; rfl

end Erdos1160.DeepJacobi

end

/- ChartSize -/
section

namespace Erdos1160.DeepJacobi

lemma double_pairs (d : ℕ) : 2*(d*(d-1)/2) = d*(d-1) := by
  rw [mul_comm 2,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self d)]

lemma pairs_add (n q : ℕ) : q*(q-1)/2 + q*n + n*(n-1)/2 = (n+q)*(n+q-1)/2 := by
  cases n with
  | zero => simp
  | succ n =>
    cases q with
    | zero => simp
    | succ q =>
      have ha := double_pairs (q+1)
      have hb := double_pairs (n+1)
      have hc := double_pairs (n+1+(q+1))
      have hs : n+1+(q+1)-1 = n+q+1 := by omega
      simp only [Nat.add_sub_cancel,hs] at ha hb hc ⊢
      nlinarith only [ha,hb,hc]

theorem array_card (q n s : ℕ) :
    Nat.card (Array q n s) = 2^((q+s)*((n+q)*((n+q)-1)/2)) := by
  simp only [Array,Old,W,V,Nat.card_prod,Nat.card_fun,Nat.card_sum,Nat.card_fin,Nat.card_zmod,
    Erdos1160Growth.SharpFamily.triangular_card,← pow_add,← pow_mul,← Nat.mul_add,pairs_add]

/-- Numerical expression ready for the high-action H2 estimate with arbitrary q. -/
theorem raw_numeric {q n s X : ℕ} (h : X ≤ Nat.card (jointHighChart q n s) *
    (2^((q+s)*(n+q)) * 2^((q+s)+(n+q)+(n+q)*((n+q)-1)/2))) :
    X * 2^(q*(n*(n-1)/2)) ≤
      2^((q+s)*((n+q)*((n+q)-1)/2+(n+q)) + (n+q)*(q+s) +
        ((n+q)*((n+q)-1)/2+(n+q)) + (q+s)) := by
  let B := 2^((q+s)*(n+q)) * 2^((q+s)+(n+q)+(n+q)*((n+q)-1)/2)
  calc
    _ ≤ (Nat.card (jointHighChart q n s) * B) * 2^(q*(n*(n-1)/2)) := Nat.mul_le_mul_right _ h
    _ = (Nat.card (jointHighChart q n s) * 2^(q*(n*(n-1)/2))) * B := Nat.mul_right_comm .. 
    _ ≤ (2^((q+s)*(q+n)) * Nat.card (Array q n s)) * B := Nat.mul_le_mul_right _ (high_chart_joint_count q n s)
    _ = _ := by
      dsimp [B]
      rw [array_card]
      simp only [← pow_add]
      congr 1
      ring

end Erdos1160.DeepJacobi

end

/- CyclicChart -/
section

namespace Erdos1160.DeepJacobi
open ClassTwoProfile CentralKernelCount

variable {q n s : ℕ} {e : Fin (n+q) → ℕ} {b : Fin (q+s) → ℕ}

def expOn (e : Fin (n+q) → ℕ) (r : Pair (n+q)) := min (e (row r)) (e (col r))

abbrev BrData (e : Fin (n+q) → ℕ) (b : Fin (q+s)→ℕ) :=
  (r : Pair (n+q)) → Data.Tor (expOn e r) b

abbrev PackedBr (e : Fin (n+q) → ℕ) (b : Fin (q+s)→ℕ) :=
  (r : Old q n ⊕ Pair n) → Data.Tor (expOn e (allSlots r)) b

abbrev Spare (q n : ℕ) := Pair n → V q

noncomputable def slotEquiv (q n : ℕ) : Old q n ⊕ Pair n ≃ Pair (n+q) := by
  apply Equiv.ofBijective allSlots
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨allSlots_surj q n,?_⟩
  simp only [Old,Nat.card_sum,Nat.card_prod,Nat.card_fin,Erdos1160Growth.SharpFamily.triangular_card,pairs_add]

theorem packed_card (e : Fin (n+q) → ℕ) (b : Fin (q+s) → ℕ) :
    Nat.card (PackedBr e b) = Nat.card (BrData e b) :=
  Nat.card_congr (Equiv.piCongrLeft (fun r => Data.Tor (expOn e r) b) (slotEquiv q n))

def overwriteTor {k : ℕ} (hk : 0 < k) (hbin : ∀j : Fin q,b (Fin.castAdd s j)=1)
    (v : Data.Tor k b) (bits : V q) : Data.Tor k b :=
  ⟨Fin.addCases (fun j => bitLift (hbin j) (bits j)) (fun j => v.val (Fin.natAdd q j)), by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Pi.pow_apply,Pi.one_apply,Fin.addCases_left]
      exact bitLift_pow _ hk _
    · simp only [Pi.pow_apply,Pi.one_apply,Fin.addCases_right]
      exact congrFun v.property _⟩

def packCyclic (he : ∀i,0 < e i) (hbin : ∀j : Fin q,b (Fin.castAdd s j)=1)
    (br : BrData e b) (payload : Spare q n) : PackedBr e b
  | .inl r => br (allSlots (.inl r))
  | .inr r => overwriteTor (lt_min (he _) (he _)) hbin (br (allSlots (.inr r))) (payload r)

noncomputable def cyclicArray (std : Factors b → List (Fin (q+s))) (br : BrData e b) : Array q n s :=
  (fun r => wordVector (markCoords q s) (std (br (allSlots (.inl r))).val),
    fun r => wordVector (markCoords q s) (std (br (allSlots (.inr r))).val))

lemma marked_cyclic_array (std : Factors b → List (Fin (q+s)))
    (sq : Fin (n+q) → Factors b) (br : BrData e b) :
    parityArray (markCoords q s) (markedWords (⟨std ∘ sq,fun r => std (br r).val⟩ : Pattern (n+q) (q+s))) =
      cyclicArray std br := by
  apply Prod.ext
  · funext r
    cases r <;> rfl
  · rfl

/-- Recover the entire cyclic torsion coefficient table and independently
inserted bits. Only pivot factors of order two were overwritten; all other
coefficients, including long cyclic ones with vanishing parity, were kept. -/
theorem recover_cyclic (he : ∀i,0 < e i) (hb : ∀j,0 < b j) (hbin : ∀j : Fin q,b (Fin.castAdd s j)=1)
    (std : Factors b → List (Fin (q+s))) (hw : ∀ v,word (gen b) (std v)=v)
    {t : FullTensor q n s} (hi : Function.Injective (fun v : V q => fullCore t (v,0)))
    {br₁ br₂ : BrData e b} {p₁ p₂ : Spare q n}
    (hg₁ : compatible (fullCore t) (fullOutside t) (cyclicArray std br₁))
    (hg₂ : compatible (fullCore t) (fullOutside t) (cyclicArray std br₂))
    (h : packCyclic he hbin br₁ p₁ = packCyclic he hbin br₂ p₂) : br₁ = br₂ ∧ p₁=p₂ := by
  have hold (r : Old q n) : br₁ (allSlots (.inl r)) = br₂ (allSlots (.inl r)) := congrFun h (.inl r)
  have ht (r : Pair n) (j : Fin s) :
      (br₁ (allSlots (.inr r))).val (Fin.natAdd q j) = (br₂ (allSlots (.inr r))).val (Fin.natAdd q j) := by
    have H := congrArg (fun z : Data.Tor (expOn e (allSlots (.inr r))) b => z.val (Fin.natAdd q j)) (congrFun h (.inr r))
    simpa only [packCyclic,overwriteTor,Fin.addCases_right] using H
  have ha : cyclicArray std br₁ = cyclicArray std br₂ := by
    apply recover _ _ hi hg₁ hg₂
    apply Prod.ext
    · funext r
      change wordVector _ (std (br₁ _).val) = wordVector _ (std (br₂ _).val)
      rw [hold]
    · funext r j
      change (wordVector _ (std (br₁ _).val)).2 j = (wordVector _ (std (br₂ _).val)).2 j
      rw [cyclic_right b hb std hw,cyclic_right b hb std hw,ht]
  constructor
  · funext k
    obtain ⟨u,rfl⟩ := allSlots_surj q n k
    cases u with
    | inl r => exact hold r
    | inr r =>
      apply Subtype.ext
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ht r j) i
      apply binary_parity_inj (hb _) (hbin j)
      have hraw := congrArg (fun a : Array q n s => (a.2 r).1 j) ha
      simpa only [cyclicArray,cyclic_left b hb std hw] using hraw
  · funext r j
    apply bitLift_inj (hbin j)
    have H := congrArg (fun z : Data.Tor (expOn e (allSlots (.inr r))) b => z.val (Fin.castAdd s j)) (congrFun h (.inr r))
    simpa only [packCyclic,overwriteTor,Fin.addCases_left] using H

end Erdos1160.DeepJacobi

end

/- PowerChartCount -/
section

namespace Erdos1160.DeepJacobi
open ClassTwoProfile CentralKernelCount
open scoped commutatorElement

variable {q n s : ℕ} {e : Fin (n+q) → ℕ} {b : Fin (q+s) → ℕ}

def powerPattern (std : Factors b → List (Fin (q+s))) (sq : Fin (n+q) → Factors b)
    (br : BrData e b) : Pattern (n+q) (q+s) := ⟨std ∘ sq,fun r => std (br r).val⟩

theorem powerMarks_compatible {G : Type*} [Group G] (std : Factors b → List (Fin (q+s)))
    (sq : Fin (n+q) → Factors b) (br : BrData e b)
    (D : ThirdMarks (Multiplicative Bit) G (n+q) (q+s)) (hG : TripleCentral G) (hi : Function.Injective D.incl)
    (c : CodeSlot (n+q) (q+s) → Multiplicative Bit) (hc : PowerFits e b (powerPattern std sq br) D c)
    (M : Fin (n+q) → Fin (q+s) → Multiplicative Bit) (hm : ∀ i j,⁅D.x i,D.z j⁆ = D.incl (M i j)) :
    compatible (fullCore (markTensor M)) (fullOutside (markTensor M)) (cyclicArray std br) := by
  rw [← marked_cyclic_array std sq br]
  apply marked_words_compatible hG D.incl hi D.central D.z (markCoords q s) (D.x ∘ coreMark) (D.x ∘ outMark)
  · intro j i
    simp only [markCoords,core_on_basis,markTensor,Equiv.apply_symm_apply,Function.comp_apply]
    exact reverse_action (hm _ _)
  · intro j i
    simp only [markCoords,outside_on_basis,markTensor,Equiv.apply_symm_apply,Function.comp_apply]
    exact reverse_action (hm _ _)
  · intro i j
    exact ⟨(c (.inr (.inr (mixedSlot i j)))).toAdd,hc.2.2 (mixedSlot i j)⟩
  · intro ij
    exact ⟨(c (.inr (.inr (outsideSlot ij)))).toAdd,hc.2.2 (outsideSlot ij)⟩

/-- Entire isomorphism-class estimate for arbitrary cyclic invariant factors,
including deficient profiles. The chosen q output pivots have order two.
Every admissible torsion value on every unomitted entry is kept in full. -/
theorem arbitrary_power_high_count {I : Type*} (E : I → Type*) [∀i,Group (E i)] [∀i,Finite (E i)]
    (he : ∀j,0 < e j) (hb : ∀j,0 < b j) (hbin : ∀j : Fin q,b (Fin.castAdd s j)=1)
    (std : Factors b → List (Fin (q+s))) (hw : ∀v,word (gen b) (std v)=v)
    (sq : I → Fin (n+q) → Factors b) (br : I → BrData e b)
    (D : ∀i,ThirdMarks (Multiplicative Bit) (E i) (n+q) (q+s))
    (c : I → CodeSlot (n+q) (q+s) → Multiplicative Bit)
    (M : I → Fin (n+q) → Fin (q+s) → Multiplicative Bit)
    (fits : ∀i,PowerFits e b (powerPattern std (sq i) (br i)) (D i) (c i))
    (act : ∀i j k,⁅(D i).x j,(D i).z k⁆=(D i).incl (M i j k))
    (hG : ∀i,TripleCentral (E i)) (hincl : ∀i,Function.Injective (D i).incl)
    (hpivot : ∀i, Function.Injective (fun v : V q => fullCore (markTensor (M i)) (v,0)))
    (hsize : ∀i, (∏ j,2^(e j))*((∏ j,2^(b j))*2) ≤ Nat.card (E i))
    (hsep : ∀i j,Nonempty (E i ≃* E j) → i=j) :
    Nat.card I * 2^(q*(n*(n-1)/2)) ≤
      2^(ClassTwoProfile.cost e b + (n+q)*(q+s) + ((n+q)*((n+q)-1)/2+(n+q)) + (q+s)) := by
  let S := Fin (n+q) → Factors b
  let T := CodeSlot (n+q) (q+s) → Multiplicative Bit
  let Y := (S × PackedBr e b) × (FullTensor q n s × T)
  let f (u : I × Spare q n) : Y :=
    ((sq u.1,packCyclic he hbin (br u.1) u.2),markTensor (M u.1),c u.1)
  have hf : Function.Injective f := by
    rintro ⟨i,u⟩ ⟨j,v⟩ H
    have hsq : sq i = sq j := congrArg (fun y : Y => y.1.1) H
    have hp := congrArg (fun y : Y => y.1.2) H
    have hT : markTensor (M i) = markTensor (M j) := congrArg (fun y : Y => y.2.1) H
    have hM := markTensor_injective hT
    have hc : c i = c j := congrArg (fun y : Y => y.2.2) H
    have nice k := powerMarks_compatible std (sq k) (br k) (D k) (hG k) (hincl k) (c k) (fits k) (M k) (act k)
    have hj := nice j
    rw [←hT] at hj
    obtain ⟨hbr,hpayload⟩ := recover_cyclic he hb hbin std hw (hpivot i) (nice i) hj hp
    have hP : powerPattern std (sq i) (br i) = powerPattern std (sq j) (br j) := by rw [hsq,hbr]
    apply Prod.ext _ hpayload
    apply hsep
    apply power_separation e b (powerPattern std (sq i) (br i)) (D i) (D j) (c i) (fits i)
      (by rw [hP,hc]; exact fits j) (M i) (act i) (by rw [hM];exact act j)
    · simpa only [show Nat.card (Multiplicative Bit)=2 from Nat.card_zmod 2] using hsize i
    · simpa only [show Nat.card (Multiplicative Bit)=2 from Nat.card_zmod 2] using hsize j
  have hS : Nat.card (S × PackedBr e b) = 2^(ClassTwoProfile.cost e b) := by
    rw [Nat.card_prod,packed_card]
    exact (Nat.card_prod (α := S) (β := BrData e b)).symm.trans (ClassTwoProfile.card_code e b)
  have hT : Nat.card T=2^((q+s)+((n+q)+(n+q)*((n+q)-1)/2)) := by
    change Nat.card (CodeSlot (n+q) (q+s) → Multiplicative Bit) = _
    rw [Nat.card_fun,show Nat.card (Multiplicative Bit) = 2 from Nat.card_zmod 2]
    simp only [CodeSlot,Nat.card_sum,Nat.card_fin,PairSlot,Erdos1160Growth.SharpFamily.triangular_card]
  have hsp : Nat.card (Spare q n) = 2^(q*(n*(n-1)/2)) := by
    simp only [Spare,V,Nat.card_fun,Nat.card_fin,Nat.card_zmod,Erdos1160Growth.SharpFamily.triangular_card,←pow_mul]
  let _ : Finite Y := by dsimp [Y,S,T,PackedBr,ClassTwoProfile.Data.Tor]; infer_instance
  have h := Nat.card_le_card_of_injective f hf
  change Nat.card (I × Spare q n) ≤ Nat.card ((S × PackedBr e b) × (FullTensor q n s × T)) at h
  rw [Nat.card_prod (α := I),hsp,Nat.card_prod (α := S × PackedBr e b),hS,
    Nat.card_prod (α := FullTensor q n s),full_tensor_card,hT,←pow_add,←pow_add] at h
  convert h using 1
  congr 1
  ring

end Erdos1160.DeepJacobi

end

/- PowerHigh -/
section

namespace CentralKernelCount
open CategoryTheory ClassTwoProfile Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open scoped commutatorElement

structure HighPowerWitness (n s : ℕ) (b : Fin (32+s) → ℕ) (E : FiniteGrp.{0}) where
  base : Code (binaryOrders (n+32)) b
  marks : ThirdMarks Ctwo E (n+32) (32+s)
  code : CodeSlot (n+32) (32+s) → Ctwo
  mat : Fin (n+32) → Fin (32+s) → Ctwo
  fits : PowerFits (binaryOrders (n+32)) b (cyclicPattern base) marks code
  action : ∀ i j, ⁅marks.x i,marks.z j⁆=marks.incl (mat i j)
  pivot : Function.Injective (fun v : Erdos1160.DeepJacobi.V 32 => fullCore (markTensor mat) (v,0))
  inj : Function.Injective marks.incl
  triple : TripleCentral E

def singlePowerHigh (n s a : ℕ) (b : Fin (32+s)→ℕ) : Set classSpace :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | Nat.card E = 2^((n+32)+(32+s)+a+1) ∧
    (∀j,0 < b j) ∧ (∑j,b j=(32+s)+a) ∧ (∀j : Fin 32,b (Fin.castAdd s j)=1) ∧
    Nonempty (HighPowerWitness n s b E)}

theorem binary_cost {d t a : ℕ} (b : Fin t→ℕ) (hb : ∀j,0 < b j) (hs : ∑j,b j=t+a) :
    cost (binaryOrders d) b = t*OrbitUp.slotsN d + d*a := by
  have hc : Fintype.card (Tri d) = d*(d-1)/2 := by
    rw [←Nat.card_eq_fintype_card]
    exact Erdos1160Growth.SharpFamily.triangular_card d
  have kk (i : Tri d) (j : Fin t) : min (min (binaryOrders d (row i)) (binaryOrders d (col i))) (b j) = 1 := by
    simp only [binaryOrders,min_self,min_eq_left (show 1 ≤ b j from hb j)]
  simp only [cost,hs,kk,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,hc,OrbitUp.slotsN]
  ring

theorem single_power_high_count (n s a : ℕ) (b : Fin (32+s)→ℕ) :
    (singlePowerHigh n s a b).ncard * 2^(32*(n*(n-1)/2)) ≤
      2^((32+s)*OrbitUp.slotsN (n+32)+(n+32)*(32+s)+OrbitUp.slotsN (n+32)+(32+s)+(n+32)*a) := by
  classical
  let C := singlePowerHigh n s a b
  by_cases present : Nonempty C
  · have reps (u : C) : ∃E : FiniteGrp.{0}, (Nat.card E = 2^((n+32)+(32+s)+a+1) ∧
        (∀j,0 < b j) ∧ (∑j,b j=(32+s)+a) ∧ (∀j : Fin 32,b (Fin.castAdd s j)=1) ∧
        Nonempty (HighPowerWitness n s b E)) ∧ Quotient.mk _ E=u.val := u.property
    choose E h rep using reps
    let w (u : C) := (h u).2.2.2.2.some
    have h0 := h present.some
    have size (u : C) := (power_profile_size (d := n+32) h0.2.2.1).trans (h u).1.symm
    have sep (u v : C) (he : Nonempty (E u ≃* E v)) : u=v := by
      apply Subtype.ext
      rw [←rep u,←rep v]
      apply Quotient.sound
      exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
        (MulEquiv.toGrpIso (X := (E u).toGrp) (Y := (E v).toGrp) he.some)⟩
    have bd := arbitrary_power_high_count (q:=32) (fun u : C => (E u : Type))
      (e := binaryOrders (n+32)) (fun _ => Nat.zero_lt_one) h0.2.1 h0.2.2.2.1
      (cyclicWord b) (cyclicWord_correct b) (fun u => (w u).base.1) (fun u => (w u).base.2)
      (fun u => (w u).marks) (fun u => (w u).code) (fun u => (w u).mat) (fun u => (w u).fits)
      (fun u => (w u).action) (fun u => (w u).triple) (fun u => (w u).inj) (fun u => (w u).pivot)
      (fun u => (size u).le) sep
    rw [binary_cost b h0.2.1 h0.2.2.1] at bd
    change Nat.card C * _ ≤ _
    convert bd using 2 <;> unfold OrbitUp.slotsN <;> omega
  · letI : IsEmpty C := not_nonempty_iff.mp present
    change Nat.card C*_ ≤ _
    simp

abbrev shortOrders {t : ℕ} (p : Fin t → Fin 4) : Fin t → ℕ := fun j => (p j).val+1

def allPowerHigh (n s a : ℕ) : Set classSpace :=
  ⋃ p : Fin (32+s)→Fin 4, singlePowerHigh n s a (shortOrders p)

theorem singlePowerHigh_finite (n s a : ℕ) (b : Fin (32+s)→ℕ) : (singlePowerHigh n s a b).Finite := by
  apply (Erdos1160.Tables.orderClasses_finite _).subset
  rintro _ ⟨G,⟨h,_⟩,rfl⟩
  exact ⟨G,h,rfl⟩

theorem all_power_high_count (n s a : ℕ) :
    (allPowerHigh n s a).ncard*2^(32*(n*(n-1)/2)) ≤
      2^((32+s)*OrbitUp.slotsN (n+32)+(n+32)*(32+s)+OrbitUp.slotsN (n+32)+(32+s)+(n+32)*a+2*(32+s)) := by
  classical
  let C := Fin (32+s) → Fin 4
  let S (p : C) := singlePowerHigh n s a (shortOrders p)
  let P := 32*(n*(n-1)/2)
  let V := (32+s)*OrbitUp.slotsN (n+32)+(n+32)*(32+s)+OrbitUp.slotsN (n+32)+(32+s)+(n+32)*a
  have hd : Fintype.card C=2^(2*(32+s)) := by
    simp only [C,Fintype.card_fun,Fintype.card_fin,pow_mul];rfl
  have step : (allPowerHigh n s a).ncard ≤ ∑ p : C,(S p).ncard := by
    simpa only [allPowerHigh,Finset.mem_univ,Set.iUnion_true] using Finset.set_ncard_biUnion_le (Finset.univ : Finset C) S
  change (allPowerHigh n s a).ncard*2^P ≤ 2^(V+2*(32+s))
  calc
    _ ≤ (∑p : C,(S p).ncard)*2^P := Nat.mul_le_mul_right _ step
    _ = ∑p : C,(S p).ncard*2^P := Finset.sum_mul ..
    _ ≤ ∑_ : C,2^V := Finset.sum_le_sum (fun p _ => single_power_high_count n s a (shortOrders p))
    _ = Fintype.card C * 2^V := by rw [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    _ = _ := by rw [hd,Nat.pow_add 2 V (2*(32+s))];exact Nat.mul_comm ..

end CentralKernelCount

end

/- RankMinor -/
section

namespace OrbitUp

theorem select_independent {ι M : Type} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : ι → M) (k : ℕ) (hk : k ≤ Module.finrank K (Submodule.span K (Set.range f))) :
    ∃ e : Fin k ↪ ι, LinearIndependent K (f ∘ e) := by
  classical
  obtain ⟨T, hsub, hcard, _, hind⟩ := Submodule.exists_finset_span_eq_linearIndepOn K (Set.range f)
  let j : Fin k ↪ T := (Fin.castLEEmb (hk.trans_eq hcard.symm)).trans T.equivFin.symm.toEmbedding
  have hv (i : Fin k) : ∃ z : ι, f z = (j i).val := hsub (j i).property
  choose z hz using hv
  have hfamily : (f ∘ z) = fun i => (j i).val := funext hz
  have hli : LinearIndependent K (f ∘ z) := by
    rw [hfamily]
    exact hind.comp j j.injective
  exact ⟨⟨z,fun i l h => hli.injective (congrArg f h)⟩, hli⟩

/-- Rank at least k gives a nonsingular k-by-k minor, with injective row and column maps. -/
theorem exists_unit_minor {d t k : ℕ} (A : Matrix (Fin d) (Fin t) K) (hk : k ≤ A.rank) :
    ∃ rows : Fin k ↪ Fin d, ∃ cols : Fin k ↪ Fin t, IsUnit (A.submatrix rows cols) := by
  classical
  obtain ⟨rows, hr⟩ := select_independent A.row k (A.rank_eq_finrank_span_row ▸ hk)
  let B := A.submatrix rows id
  have hrows : LinearIndependent K B.row := hr
  have hcol : k ≤ Module.finrank K (Submodule.span K (Set.range B.col)) := by
    rw [← B.rank_eq_finrank_span_cols, hrows.rank_matrix, Fintype.card_fin]
  obtain ⟨cols, hc⟩ := select_independent B.col k hcol
  exact ⟨rows,cols,Matrix.linearIndependent_cols_iff_isUnit.mp hc⟩

end OrbitUp

end

/- PivotChart -/
section

namespace Erdos1160.DeepJacobi

theorem exists_permuted_pivot {q n s : ℕ} (A : Matrix (Fin (n+q)) (Fin (q+s)) Bit)
    (hr : q ≤ A.rank) :
    ∃ u : Equiv.Perm (Fin (n+q)), ∃ v : Equiv.Perm (Fin (q+s)),
      Function.Injective (fun x : V q => fullCore (markTensor
        (fun i j => Multiplicative.ofAdd ((A.submatrix u v) i j))) (x,0)) := by
  classical
  obtain ⟨rows, cols, hunit⟩ := OrbitUp.exists_unit_minor A hr
  let col (i : Fin q) : Fin (q+s) := finSumFinEquiv (Sum.inl i)
  have hrow : Function.Injective (@coreMark q n) := by
    intro i j h
    have hv : n+i.val = n+j.val := congrArg Fin.val h
    exact Fin.ext (Nat.add_left_cancel hv)
  have hcol : Function.Injective col := finSumFinEquiv.injective.comp Sum.inl_injective
  obtain ⟨u, hu⟩ := Equiv.Perm.exists_extending_pair (@coreMark q n) rows hrow rows.injective
  obtain ⟨v,hv⟩ := Equiv.Perm.exists_extending_pair col cols hcol cols.injective
  let B := A.submatrix rows cols
  let t : FullTensor q n s := markTensor (fun i j => Multiplicative.ofAdd ((A.submatrix u v) i j))
  let F : V q →ₗ[Bit] V q := ((fullCore t).toZModLinearMap 2).comp (LinearMap.inl Bit (V q) (V s))
  have he : F = B.mulVecLin := by
    apply (Pi.basisFun Bit (Fin q)).ext
    intro i
    have pair : coordBasis q s (.inl i) = ((Pi.basisFun Bit (Fin q)) i,0) := by
      apply Prod.ext
      · exact Module.Basis.prod_apply_inl_fst _ _ _
      · exact Module.Basis.prod_apply_inl_snd _ _ _
    change fullCore t ((Pi.basisFun Bit (Fin q)) i,0) = _
    rw [← pair,core_on_basis]
    funext j
    simp only [Pi.basisFun_apply,Matrix.mulVecLin_apply,Matrix.mulVec_single_one]
    change A (u (coreMark j)) (v (col i)) = A (rows j) (cols i)
    rw [hu,hv]
  refine ⟨u,v,?_⟩
  change Function.Injective F
  rw [he]
  exact Matrix.mulVec_injective_iff_isUnit.mpr hunit

end Erdos1160.DeepJacobi

end

/- RestrictedPivot -/
section

namespace Erdos1160.DeepJacobi

theorem exists_avoiding_minor {d t q δ : ℕ} (A : Matrix (Fin d) (Fin t) Bit)
    (L : Finset (Fin t)) (hcard : L.card ≤ δ) (hr : q+δ ≤ A.rank) :
    ∃ rows : Fin q ↪ Fin d, ∃ cols : Fin q ↪ Fin t,
      (∀ j, cols j ∉ L) ∧ IsUnit (A.submatrix rows cols) := by
  classical
  obtain ⟨cs,hcs⟩ := OrbitUp.select_independent A.col (q+δ) (A.rank_eq_finrank_span_cols ▸ hr)
  let Good := Finset.univ.filter (fun i => cs i ∉ L)
  have hbad : (Finset.univ.filter (fun i => cs i ∈ L)).card ≤ L.card :=
    Finset.card_le_card_of_injOn cs (fun i hi => (Finset.mem_filter.mp hi).2) cs.injective.injOn
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (q+δ)))) (fun i => cs i ∈ L)
  simp only [Finset.card_univ,Fintype.card_fin] at hsum
  have hc : q ≤ Good.card := by dsimp only [Good]; omega
  let i : Fin q ↪ Good := (Fin.castLEEmb hc).trans Good.equivFin.symm.toEmbedding
  let e : Fin q ↪ Fin (q+δ) := ⟨fun j => (i j).val, Subtype.val_injective.comp i.injective⟩
  let cols := e.trans cs
  have hg (j : Fin q) : cols j ∉ L := (Finset.mem_filter.mp (i j).property).2
  let B := A.submatrix id cols
  have hin : LinearIndependent Bit B.transpose.row := hcs.comp e e.injective
  have rankB : B.rank = q := by simpa only [Matrix.rank_transpose,Fintype.card_fin] using hin.rank_matrix
  obtain ⟨rows,hrows⟩ := OrbitUp.select_independent B.row q (by rw [←B.rank_eq_finrank_span_row,rankB])
  exact ⟨rows,cols,hg,Matrix.linearIndependent_rows_iff_isUnit.mp hrows⟩

theorem exists_permuted_pivot_avoiding {q n s δ : ℕ} (A : Matrix (Fin (n+q)) (Fin (q+s)) Bit)
    (L : Finset (Fin (q+s))) (hcard : L.card ≤ δ) (hr : q+δ ≤ A.rank) :
    ∃ u : Equiv.Perm (Fin (n+q)), ∃ v : Equiv.Perm (Fin (q+s)),
      (∀ j : Fin q, v (Fin.castAdd s j) ∉ L) ∧
      Function.Injective (fun x : V q => fullCore (markTensor
        (fun i j => Multiplicative.ofAdd ((A.submatrix u v) i j))) (x,0)) := by
  classical
  obtain ⟨rows,cols,hgood,hunit⟩ := exists_avoiding_minor A L hcard hr
  let col (i : Fin q) : Fin (q+s) := finSumFinEquiv (Sum.inl i)
  have hrow : Function.Injective (@coreMark q n) := by
    intro i j h
    have hv : n+i.val = n+j.val := congrArg Fin.val h
    exact Fin.ext (Nat.add_left_cancel hv)
  have hcol : Function.Injective col := finSumFinEquiv.injective.comp Sum.inl_injective
  obtain ⟨u, hu⟩ := Equiv.Perm.exists_extending_pair (@coreMark q n) rows hrow rows.injective
  obtain ⟨v,hv⟩ := Equiv.Perm.exists_extending_pair col cols hcol cols.injective
  let B := A.submatrix rows cols
  let t : FullTensor q n s := markTensor (fun i j => Multiplicative.ofAdd ((A.submatrix u v) i j))
  let F : V q →ₗ[Bit] V q := ((fullCore t).toZModLinearMap 2).comp (LinearMap.inl Bit (V q) (V s))
  have he : F = B.mulVecLin := by
    apply (Pi.basisFun Bit (Fin q)).ext
    intro i
    have pair : coordBasis q s (.inl i) = ((Pi.basisFun Bit (Fin q)) i,0) := by
      apply Prod.ext
      · exact Module.Basis.prod_apply_inl_fst _ _ _
      · exact Module.Basis.prod_apply_inl_snd _ _ _
    change fullCore t ((Pi.basisFun Bit (Fin q)) i,0) = _
    rw [← pair,core_on_basis]
    funext j
    simp only [Pi.basisFun_apply,Matrix.mulVecLin_apply,Matrix.mulVec_single_one]
    change A (u (coreMark j)) (v (col i)) = A (rows j) (cols i)
    rw [hu,hv]
  refine ⟨u,v,fun j => ?_,?_⟩
  · change v (col j) ∉ L
    rw [hv]
    exact hgood j
  change Function.Injective F
  rw [he]
  exact Matrix.mulVec_injective_iff_isUnit.mpr hunit

theorem exists_permuted_binary_pivot {q n s δ : ℕ} (A : Matrix (Fin (n+q)) (Fin (q+s)) Bit)
    (b : Fin (q+s) → ℕ) (hpos : ∀ j, 1 ≤ b j) (hbudget : (∑ j, b j) - (q+s) ≤ δ)
    (hr : q+δ ≤ A.rank) :
    ∃ u : Equiv.Perm (Fin (n+q)), ∃ v : Equiv.Perm (Fin (q+s)),
      (∀ j : Fin q, b (v (Fin.castAdd s j)) = 1) ∧
      Function.Injective (fun x : V q => fullCore (markTensor
        (fun i j => Multiplicative.ofAdd ((A.submatrix u v) i j))) (x,0)) := by
  classical
  let L := Finset.univ.filter (fun j => b j ≠ 1)
  have hL : L.card ≤ δ := by
    have hs : (∑ j, ((if b j ≠ 1 then 1 else 0)+1)) ≤ ∑ j, b j := by
      apply Finset.sum_le_sum
      intro j _
      split <;> have := hpos j <;> omega
    have he : (∑ j, ((if b j ≠ 1 then 1 else 0)+1)) = L.card+(q+s) := by
      simp [L,Finset.sum_add_distrib,Finset.sum_ite]
    rw [he] at hs
    omega
  obtain ⟨u,v,havoid,hpivot⟩ := exists_permuted_pivot_avoiding A L hL hr
  refine ⟨u,v,fun j => ?_,hpivot⟩
  by_contra hn
  exact havoid j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)

end Erdos1160.DeepJacobi

end

/- PowerSplit -/
section

namespace CentralKernelCount
open CategoryTheory ClassTwoProfile Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open scoped commutatorElement

def allPower (d t a : ℕ) : Set classSpace :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | Nat.card E=2^(d+t+a+1) ∧
    ∃u : powerBases d t a, Nonempty (ThirdBridge E (powerBase u))}

theorem bridge_centrality {E H : Type} [Group E] [Group H] {d s : ℕ} {e : Fin d→ℕ} {b : Fin s→ℕ}
    (S : Data H e b) (L : ThirdBridge E H) : TripleCentral E ∧ ThirdLowerCentral.third E ≤ Subgroup.center E := by
  have central : commutator H ≤ Subgroup.center H := Subgroup.commutator_le.mpr (fun x _ y _ => S.center_comm x y)
  have topmap : (⊤ : Subgroup E).map L.proj = ⊤ := by rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr L.onto]
  have lowmap := (⊤ : Subgroup E).map_lowerCentralSeries L.proj 2
  rw [topmap] at lowmap
  change (ThirdLowerCentral.third E).map L.proj = ThirdLowerCentral.third H at lowmap
  rw [ThirdLowerCentral.trivial_iff.mpr central] at lowmap
  have hh : ThirdLowerCentral.third E ≤ L.proj.ker := (Subgroup.map_eq_bot_iff _).mp lowmap
  rw [L.ker] at hh
  refine ⟨?_,hh.trans L.central⟩
  intro x y z
  apply L.central
  rw [← L.ker,MonoidHom.mem_ker,map_commutatorElement,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (S.center_comm (L.proj x) (L.proj y)) _).symm

theorem original_power_marks {E : FiniteGrp.{0}} {d t a : ℕ} (k : powerBases d t a)
    (L : ThirdBridge E (powerBase k)) :
    ∃(D : ThirdMarks Ctwo E d t) (c : CodeSlot d t→Ctwo) (M : Matrix (Fin d) (Fin t) (ZMod 2)),
      PowerFits (binaryOrders d) (powerFrame k).b (cyclicPattern (firstRef k).code) D c ∧
        (∀ i j, ⁅D.x i,D.z j⁆=D.incl (Multiplicative.ofAdd (M i j))) ∧
        D.incl=L.incl ∧ (∀i,L.proj (D.x i)=(powerFrame k).coords.x i) ∧
        (∀j,L.proj (D.z j)=(powerFrame k).coords.incl (gen (powerFrame k).b j)) := by
  let F := powerFrame k
  have card : Nat.card (powerBase k)=2^(d+t+a) := (profile_card F.profile).trans (by simp [pow_add,Nat.mul_assoc])
  obtain ⟨x,z,hx,hz,hc⟩ := commuting_power_lifts F.coords L (bridge_centrality F.coords L).2 card (Or.inr F.image)
  obtain ⟨D,c,M,fit,ac,inc,dx,dz⟩ := power_marks_from (firstRef k) L x z hx hz hc
  exact ⟨D,c,M,fit,ac,inc,dx ▸ hx,dz ▸ hz⟩

def paddedPowerHigh (d t a : ℕ) : Set classSpace :=
  if 32 ≤ d ∧ 32 ≤ t then allPowerHigh (d-32) (t-32) a else ∅

theorem padded_power_high_count (d t a : ℕ) : (paddedPowerHigh d t a).ncard *
    2^(32*((d-32)*((d-32)-1)/2)) ≤ 2^(t*OrbitUp.slotsN d+d*t+OrbitUp.slotsN d+t+d*a+2*t) := by
  by_cases h : 32 ≤ d ∧ 32 ≤ t
  · rw [paddedPowerHigh,if_pos h]
    simpa only [Nat.sub_add_cancel h.1,Nat.add_sub_of_le h.2] using all_power_high_count (d-32) (t-32) a
  · simp [paddedPowerHigh,h]

theorem max_cyclic_order {t a : ℕ} {b : Fin t→ℕ} (hp : ∀j,0 < b j) (hs : ∑j,b j=t+a)
    (j : Fin t) : b j ≤ a+1 := by
  have total : (∑i,(b i-1))+t=t+a := by
    calc
      _ = ∑i : Fin t,((b i-1)+1) := by simp [Finset.sum_add_distrib]
      _ = ∑i,b i := Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hp i))
      _ = _ := hs
  have one := Finset.single_le_sum (f := fun i=>b i-1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

theorem full_power_cover (n s a : ℕ) (ha : a ≤ 3) : allPower (n+32) (32+s) a ⊆
    lowPowerClasses (n+32) (32+s) a 34 ∪ allPowerHigh n s a := by
  classical
  rintro _ ⟨E,⟨he,k,⟨L⟩⟩,rfl⟩
  let F := powerFrame k
  obtain ⟨D,c,M,hc,ac,inc,hx,hz⟩ := original_power_marks k L
  by_cases low : M.rank ≤ 34
  · exact Or.inl ⟨E,⟨he,⟨k,D,c,M,hc,ac,low⟩⟩,rfl⟩
  obtain ⟨u,v,short,pivot⟩ := exists_permuted_binary_pivot (q:=32) (δ:=a) M F.b F.pos
    (by rw [F.total];omega) (by omega)
  let B := F.b ∘ v
  have hp (j) : 0 < B j := F.pos (v j)
  have hs : ∑j,B j=(32+s)+a := (Equiv.sum_comp v F.b).trans F.total
  let p (j : Fin (32+s)) : Fin 4 := ⟨B j-1,by
    have mx := max_cyclic_order hp hs j; have := hp j;omega⟩
  have pb : shortOrders p=B := funext (fun j => Nat.sub_add_cancel (hp j))
  let R := powerRef F.coords u v
  obtain ⟨D',c',M',fit,act,idc,dx,dz⟩ := power_marks_from R L (D.x ∘ u) (D.z ∘ v)
    (fun j => hx (u j)) (fun j => hz (v j)) (fun i j=>D.zComm (v i) (v j))
  have action (i j) : ⁅D'.x i,D'.z j⁆=D'.incl (Multiplicative.ofAdd ((M.submatrix u v) i j)) := by
    rw [dx,dz,idc,←inc]
    exact ac _ _
  right
  apply Set.mem_iUnion_of_mem p
  rw [pb]
  exact ⟨E,⟨he,hp,hs,short,⟨R.code,D',c',_,fit,action,pivot,idc ▸ L.inj,(bridge_centrality F.coords L).1⟩⟩,rfl⟩

theorem all_power_cover (d t a : ℕ) (ha : a ≤ 3) : allPower d t a ⊆
    lowPowerClasses d t a 34 ∪ paddedPowerHigh d t a := by
  by_cases h : 32 ≤ d ∧ 32 ≤ t
  · rw [paddedPowerHigh,if_pos h]
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le h.1
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le h.2
    simpa only [Nat.add_comm 32 n,Nat.add_sub_cancel,Nat.add_sub_cancel_left] using full_power_cover n s a ha
  · rintro _ ⟨E,⟨he,k,⟨L⟩⟩,rfl⟩
    obtain ⟨D,c,M,hc,ac,_,_,_⟩ := original_power_marks k L
    have rank : M.rank ≤ 34 := by
      have := M.rank_le_height;have := M.rank_le_width;omega
    exact Or.inl ⟨E,⟨he,⟨k,D,c,M,hc,ac,rank⟩⟩,rfl⟩

end CentralKernelCount

end

/- SmallFrattiniFactors -/
section

namespace ClassTwoProfile

open CategoryTheory Erdos1160Growth.LowerTriangularUpper CentralKernelCount

/-- A small central Frattini profile has marked cyclic coordinates at the
prescribed ranks, and every quotient factor has order two. -/
theorem small_frattini_coords {G : FiniteGrp.{0}} {d t a : ℕ} (hp : SmallProfile G d t a) :
    ∃ (b : Fin t → ℕ) (S : Data G (fun _ : Fin d => 1) b),
      (∀ j,0 < b j) ∧ (∑j,b j) = t+a ∧ S.incl.range = frattini G := by
  let K := frattini G
  have hc : Nat.card G = 2^(d+(t+a)) := (profile_card hp).trans (by rw [pow_add 2 d,pow_add 2 t])
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hp.1 y.property) x.val) }
  have hsq (x : G ⧸ K) : x*x=1 := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [←map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (squares_le_frattini hc (Subgroup.subset_closure ⟨u,rfl⟩))
  have hinv (x : G ⧸ K) : x⁻¹=x := inv_eq_of_mul_eq_one_left (hsq x)
  let _ : CommGroup (G ⧸ K) := { (inferInstance : Group (G ⧸ K)) with
    mul_comm := fun x y => by
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv] }
  have hq : Nat.card (G ⧸ K)=2^d := (Subgroup.index_eq_card K).symm.trans hp.2.1
  obtain ⟨r,e,he,hsum,⟨fu⟩⟩ := exists_cyclic_coords (G ⧸ K) hq
  obtain ⟨s,b,hb,hsb,⟨fv⟩⟩ := exists_cyclic_coords K hp.2.2.1
  have hones : e = fun _ => 1 := funext (elementary_factors fu he hsq)
  subst e
  have hr : r=d := by simpa using hsum
  subst r
  have hz := squareCore_size fv hb
  rw [hp.2.2.2,hsb,←pow_add] at hz
  have hs := Nat.pow_right_injective (by decide : 1 < 2) hz
  have hst : s=t := by omega
  subst s
  let S := Data.ofCentralSubgroup K hp.1 fv fu
  refine ⟨b,S,hb,hsb,?_⟩
  ext x
  constructor
  · rintro ⟨w,rfl⟩
    exact (fv.symm w).property
  · intro hx
    exact ⟨fv ⟨x,hx⟩,congrArg Subtype.val (fv.symm_apply_apply ⟨x,hx⟩)⟩

end ClassTwoProfile

end

/- ThirdSplit -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi
open scoped commutatorElement

theorem triple_of_bridge {d t : ℕ} (F : ChosenFrame d t) {E : Type*} [Group E]
    (L : ThirdBridge E F.H) : TripleCentral E := by
  intro a b c
  have hc : ⁅L.proj a,L.proj b⁆ ∈ F.i.range := by
    rw [← F.ker,MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,mul_comm]
  have zi : F.i.range ≤ frattini F.H := by
    rintro _ ⟨v,rfl⟩
    obtain ⟨l,hl⟩ := bits_word t v
    rw [←hl,word_map]
    exact word_mem _ _ (fun j => F.rz j ▸ F.hz j) l
  apply L.central
  rw [←L.ker,MonoidHom.mem_ker,map_commutatorElement,map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (F.central (zi hc)) _).symm

private lemma comm_same_lifts {E H : Type*} [Group E] [Group H] (L : ThirdBridge E H)
    {x y u v : E} (hx : L.proj x=L.proj u) (hy : L.proj y=L.proj v) :
    ⁅x,y⁆=⁅u,v⁆ := by
  have solve (a b : E) (h : L.proj a=L.proj b) : ∃ c ∈ Subgroup.center E,a=c*b := by
    have hk : a*b⁻¹ ∈ L.incl.range := by rw [←L.ker,MonoidHom.mem_ker,map_mul,map_inv,h,mul_inv_cancel]
    exact ⟨a*b⁻¹,L.central hk,(inv_mul_cancel_right _ _).symm⟩
  obtain ⟨c,hc,rfl⟩ := solve x u hx
  obtain ⟨b,hb,rfl⟩ := solve y v hy
  rw [central_factor hc,← commutatorElement_inv (b*v) u,central_factor hb,commutatorElement_inv]

structure HighWitness (n s : ℕ) (E : FiniteGrp.{0}) where
  square : Fin (n+32) → BitGroup (32+s)
  comm : PairSlot (n+32) → BitGroup (32+s)
  marks : ThirdMarks Ctwo E (n+32) (32+s)
  code : CodeSlot (n+32) (32+s) → Ctwo
  mat : Fin (n+32) → Fin (32+s) → Ctwo
  fits : ThirdFits (Pattern.mk (fun j => standardWord (square j)) (fun p => standardWord (comm p))) marks code
  action : ∀ i j, ⁅marks.x i,marks.z j⁆=marks.incl (mat i j)
  pivot : Function.Injective (fun v : Erdos1160.DeepJacobi.V 32 => fullCore (markTensor mat) (v,0))
  inj : Function.Injective marks.incl
  triple : TripleCentral E

def highThirdClasses (n s : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {E : FiniteGrp.{0} | Nat.card E=2^((n+32)+(32+s)+1) ∧ Nonempty (HighWitness n s E)}

theorem third_cover_both (n s : ℕ) : allThird (n+32) (32+s) ⊆
    lowThirdClasses (n+32) (32+s) 31 ∪ highThirdClasses n s := by
  classical
  rintro _ ⟨E,⟨he,h,⟨L⟩⟩,rfl⟩
  let F := refFrame h
  obtain ⟨D,c,A,hc,ha,hin,hx,hz⟩ := exists_third_marks F.R L F.size F.central F.hz
  let M : Matrix (Fin (n+32)) (Fin (32+s)) (ZMod 2) := A
  by_cases low : M.rank ≤ 31
  · left
    exact ⟨E,⟨he,⟨h,D,c,M,hc,ha,low⟩⟩,rfl⟩
  right
  obtain ⟨u,v,hpivot⟩ := exists_permuted_pivot (q := 32) M (by omega)
  obtain ⟨S,hs,sz,sx⟩ := standard_reindexed F.i F.q F.ker F.rz F.rx u v
  have core (j) : S.z j ∈ frattini F.H := sz j ▸ F.hz (v j)
  obtain ⟨D',c',A',hc',ha',hin',hx',hz'⟩ := exists_third_marks S L F.size F.central core
  have changeA (i j) : A' i j=A (u i) (v j) := by
    apply Multiplicative.ofAdd.injective
    apply L.inj
    calc
      _ = ⁅D'.x i,D'.z j⁆ := (hin' ▸ ha' i j).symm
      _ = ⁅D.x (u i),D.z (v j)⁆ := comm_same_lifts L ((hx' i).trans ((sx i).trans (hx _).symm))
        ((hz' j).trans ((sz j).trans (hz _).symm))
      _ = _ := hin ▸ ha _ _
  choose sq sqEq using hs.sq
  choose cm cmEq using hs.comm
  have ps : S.toPattern = ⟨fun i => standardWord (sq i),fun p => standardWord (cm p)⟩ := by
    cases S with
    | mk P z x zsq x2 xc g =>
      cases P with
      | mk p q => exact congrArg₂ Pattern.mk (funext sqEq) (funext cmEq)
  refine ⟨E,⟨he,⟨sq,cm,D',c',fun i j => Multiplicative.ofAdd ((M.submatrix u v) i j),
    ps ▸ hc',?_,hpivot,hin' ▸ L.inj,triple_of_bridge F L⟩⟩,rfl⟩
  intro i j
  exact (ha' i j).trans (congrArg (fun b => D'.incl (Multiplicative.ofAdd b)) (changeA i j))

theorem third_cover_low (d t : ℕ) (ht : d ≤ 31 ∨ t ≤ 31) :
    allThird d t ⊆ lowThirdClasses d t 31 := by
  rintro _ ⟨E,⟨he,h,⟨L⟩⟩,rfl⟩
  let F := refFrame h
  obtain ⟨D,c,M,hc,ha,_,_,_⟩ := exists_third_marks F.R L F.size F.central F.hz
  let A : Matrix (Fin d) (Fin t) (ZMod 2) := M
  have hlow : A.rank ≤ 31 := ht.elim (fun v => A.rank_le_height.trans v) (fun v => A.rank_le_width.trans v)
  exact ⟨E,⟨he,⟨h,D,c,A,hc,ha,hlow⟩⟩,rfl⟩

def highPadded (d t : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  if 32 ≤ d ∧ 32 ≤ t then highThirdClasses (d-32) (t-32) else ∅

theorem third_cover (d t : ℕ) : allThird d t ⊆ lowThirdClasses d t 31 ∪ highPadded d t := by
  by_cases h : 32 ≤ d ∧ 32 ≤ t
  · rw [highPadded,if_pos h]
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le h.1
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le h.2
    simpa only [Nat.add_comm 32 n,Nat.add_sub_cancel,Nat.add_sub_cancel_left] using third_cover_both n s
  · exact (third_cover_low d t (by omega)).trans Set.subset_union_left

end CentralKernelCount

end

/- HighGroupCount -/
section

namespace Erdos1160.DeepJacobi

open CentralKernelCount
open scoped commutatorElement

variable {q n s : ℕ}

/-- Count whole isomorphism classes with a marked one-dimensional deep
central layer and a size-q pivot minor. The group comparison uses all the
central twisting coefficients, while Jacobi compresses the quotient's
commutator words jointly with the action tensor. -/
theorem rawGroup_high_count {I : Type*} (E : I → Type*) [∀ i,Group (E i)] [∀ i,Finite (E i)]
    (std : BitGroup (q+s) → List (Fin (q+s))) (hs : ∀ v,word bit (std v) = v)
    (sq : I → Fin (n+q) → BitGroup (q+s)) (br : I → PairSlot (n+q) → BitGroup (q+s))
    (D : ∀ i, ThirdMarks (Multiplicative Bit) (E i) (n+q) (q+s))
    (c : I → CodeSlot (n+q) (q+s) → Multiplicative Bit)
    (M : I → Fin (n+q) → Fin (q+s) → Multiplicative Bit)
    (fits : ∀ i, ThirdFits (stdPattern std (sq i) (br i)) (D i) (c i))
    (act : ∀ i j k, ⁅(D i).x j,(D i).z k⁆ = (D i).incl (M i j k))
    (hG : ∀ i, TripleCentral (E i)) (hincl : ∀ i,Function.Injective (D i).incl)
    (hpivot : ∀ i,Function.Injective (fun v : V q => fullCore (markTensor (M i)) (v,0)))
    (hsize : ∀ i, 2^(n+q)*(2^(q+s)*2) ≤ Nat.card (E i))
    (hsep : ∀ i j,Nonempty (E i ≃* E j) → i=j) :
    Nat.card I ≤ Nat.card (jointHighChart q n s) *
      (2^((q+s)*(n+q)) * 2^((q+s)+(n+q)+(n+q)*((n+q)-1)/2)) := by
  let P (i : I) := stdPattern std (sq i) (br i)
  let A (i : I) := parityArray (markCoords q s) (markedWords (P i))
  let j (i : I) : jointHighChart q n s :=
    ⟨(markTensor (M i),A i),hpivot i,thirdMarks_compatible (P i) (D i) (hG i) (hincl i) (c i) (fits i) (M i) (act i)⟩
  let C := (Fin (n+q) → BitGroup (q+s)) × (CodeSlot (n+q) (q+s) → Multiplicative Bit)
  let f (i : I) : jointHighChart q n s × C := (j i,sq i,c i)
  have hf : Function.Injective f := by
    intro i k he
    have hh : j i = j k := congrArg Prod.fst he
    have hM : M i = M k := markTensor_injective (congrArg (fun z : jointHighChart q n s => z.val.1) hh)
    have hA : A i = A k := congrArg (fun z : jointHighChart q n s => z.val.2) hh
    have hb : br i = br k := comm_word_recover std hs hA
    have hsq : sq i = sq k := congrArg (fun z : jointHighChart q n s × C => z.2.1) he
    have hc : c i = c k := congrArg (fun z : jointHighChart q n s × C => z.2.2) he
    have hP : P i = P k := by simp only [P,hsq,hb]
    apply hsep
    apply third_separation (P i) (D i) (D k) (c i) (fits i) (by rw [hP,hc]; exact fits k) (M i) (act i)
      (by rw [hM]; exact act k)
    · simpa only [show Nat.card (Multiplicative Bit) = 2 from Nat.card_zmod 2] using hsize i
    · simpa only [show Nat.card (Multiplicative Bit) = 2 from Nat.card_zmod 2] using hsize k
  have hcode : Nat.card (CodeSlot (n+q) (q+s)) = (q+s)+(n+q)+(n+q)*((n+q)-1)/2 := by
    simp only [CodeSlot,Nat.card_sum,Nat.card_fin,PairSlot,Erdos1160Growth.SharpFamily.triangular_card,Nat.add_assoc]
  have hsizes : Nat.card C = 2^((q+s)*(n+q)) * 2^((q+s)+(n+q)+(n+q)*((n+q)-1)/2) := by
    change Nat.card ((Fin (n+q) → BitGroup (q+s)) × (CodeSlot (n+q) (q+s) → Multiplicative Bit)) = _
    have hbits : Nat.card (BitGroup (q+s)) = 2^(q+s) := by
      change Nat.card (Fin (q+s) → ZMod 2) = _
      rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
    rw [Nat.card_prod,Nat.card_fun,Nat.card_fun,hbits,Nat.card_fin,hcode,
      show Nat.card (Multiplicative Bit) = 2 from Nat.card_zmod 2,← pow_mul]
  let _ : Finite (jointHighChart q n s) := by unfold jointHighChart; infer_instance
  let _ : Finite C := by dsimp [C]; infer_instance
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod (α := jointHighChart q n s) (β := C),hsizes] at h

end Erdos1160.DeepJacobi

end

/- ThirdCount -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper Erdos1160.DeepJacobi

theorem high_third_count (n s : ℕ) :
    (highThirdClasses n s).ncard * 2^(32*(n*(n-1)/2)) ≤
      2^((32+s)*OrbitUp.slotsN (n+32)+(n+32)*(32+s)+OrbitUp.slotsN (n+32)+(32+s)) := by
  classical
  let C := highThirdClasses n s
  have reps (k : C) : ∃ E : FiniteGrp.{0}, (Nat.card E=2^((n+32)+(32+s)+1) ∧
      Nonempty (HighWitness n s E)) ∧ Quotient.mk _ E = k.val := k.property
  choose E spec he using reps
  let w (k : C) := (spec k).2.some
  have card (k : C) : 2^(n+32)*(2^(32+s)*2) ≤ Nat.card (E k) := by
    rw [(spec k).1,pow_succ 2 ((n+32)+(32+s)),pow_add 2 (n+32) (32+s),Nat.mul_assoc]
  have sep (k j : C) (h : Nonempty (E k ≃* E j)) : k=j := by
    apply Subtype.ext
    rw [←he k,←he j]
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (E k).toGrp) (Y := (E j).toGrp) h.some)⟩
  have bd := rawGroup_high_count (fun k : C => (E k : Type)) standardWord standardWord_correct
    (fun k => (w k).square) (fun k => (w k).comm) (fun k => (w k).marks)
    (fun k => (w k).code) (fun k => (w k).mat) (fun k => (w k).fits)
    (fun k => (w k).action) (fun k => (w k).triple) (fun k => (w k).inj)
    (fun k => (w k).pivot) card sep
  change Nat.card C * _ ≤ _
  simpa only [OrbitUp.slotsN,Nat.add_comm (n+32) ((n+32)*((n+32)-1)/2)] using raw_numeric bd

theorem high_padded_count (d t : ℕ) :
    (highPadded d t).ncard * 2^(32*((d-32)*((d-32)-1)/2)) ≤
      2^(t*OrbitUp.slotsN d+d*t+OrbitUp.slotsN d+t) := by
  by_cases pos : 32 ≤ d ∧ 32 ≤ t
  · rw [highPadded,if_pos pos]
    have hd : d-32+32=d := Nat.sub_add_cancel pos.1
    have ht : 32+(t-32)=t := Nat.add_sub_of_le pos.2
    simpa only [hd,ht] using high_third_count (d-32) (t-32)
  · simp [highPadded,pos]

theorem allThird_le_low_high (d t : ℕ) :
    (allThird d t).ncard ≤ (lowThirdClasses d t 31).ncard+(highPadded d t).ncard := by
  have lo : (lowThirdClasses d t 31).Finite := (Erdos1160.Tables.orderClasses_finite _).subset <| by
    rintro _ ⟨G,⟨h,_⟩,rfl⟩
    exact ⟨G,h,rfl⟩
  have hi : (highPadded d t).Finite := by
    by_cases h : 32 ≤ d ∧ 32 ≤ t
    · rw [highPadded,if_pos h]
      apply (Erdos1160.Tables.orderClasses_finite _).subset
      rintro _ ⟨G,⟨hg,_⟩,rfl⟩
      exact ⟨G,hg,rfl⟩
    · simp only [highPadded,if_neg h,Set.finite_empty]
  exact (Set.ncard_le_ncard (third_cover d t) (lo.union hi)).trans (Set.ncard_union_le ..)

end CentralKernelCount

end

/- ThirdOrder -/
section

namespace CentralKernelCount

open CategoryTheory Erdos1160Growth.LowerTriangularUpper

/-- The intrinsic order-m family: all central extensions by a subgroup of order two
whose quotient has central elementary abelian Frattini subgroup. -/
def thirdOrderClasses (m : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
    ∃ (N : Subgroup G) (_ : N.Normal), Nat.card N=2 ∧ N ≤ Subgroup.center G ∧
      frattini (G ⧸ N) ≤ Subgroup.center (G ⧸ N) ∧ ∀ y : frattini (G ⧸ N),y*y=1}

theorem thirdOrder_contains_gamma_three {G : FiniteGrp.{0}} {m : ℕ}
    (hc : Nat.card G=2^m) (h : Nat.card (ThirdLowerCentral.third G)=2)
    (hz : frattini (G ⧸ ThirdLowerCentral.third G) ≤ Subgroup.center _)
    (he : ∀ y : frattini (G ⧸ ThirdLowerCentral.third G),y*y=1) :
    Quotient.mk _ G ∈ thirdOrderClasses m :=
  ⟨G,⟨hc,ThirdLowerCentral.third G,inferInstance,h,ThirdLowerCentral.order_two_central _ h,hz,he⟩,rfl⟩

private def constBit : Ctwo ≃* BitGroup 1 where
  toFun x := Multiplicative.ofAdd (fun _ => x.toAdd)
  invFun x := Multiplicative.ofAdd (x.toAdd 0)
  left_inv _ := rfl
  right_inv v := by apply Multiplicative.toAdd.injective; funext j; exact congrArg v.toAdd (Subsingleton.elim _ _)
  map_mul' _ _ := rfl

theorem real_bridge {G : FiniteGrp.{0}} (N : Subgroup G) [N.Normal]
    (cn : Nat.card N=2) (hn : N ≤ Subgroup.center G) :
    Nonempty (ThirdBridge G (G ⧸ N)) := by
  have h2 (y : N) : y*y=1 := by
    have hh : y ^ Nat.card N = 1 := pow_card_eq_one'
    simpa only [cn,pow_two] using hh
  obtain ⟨e⟩ := exist_elementary_coords h2 (show Nat.card N=2^1 by simpa using cn)
  let inc := N.subtype.comp (constBit.trans e.symm).toMonoidHom
  have image : inc.range=N := by
    ext g
    constructor
    · rintro ⟨b,rfl⟩
      exact ((constBit.trans e.symm) b).property
    · intro hg
      exact ⟨(constBit.trans e.symm).symm ⟨g,hg⟩,by simp [inc]⟩
  exact ⟨⟨inc,N.subtype_injective.comp (constBit.trans e.symm).injective,QuotientGroup.mk' N,
    QuotientGroup.mk'_surjective N,(QuotientGroup.ker_mk' N).trans image.symm,image.le.trans hn⟩⟩

theorem thirdOrder_subset_ranks (m : ℕ) :
    thirdOrderClasses m ⊆ ⋃ d ∈ Finset.range m, allThird d (m-1-d) := by
  rintro _ ⟨G,⟨hc,N,ni,cn,hn,hz,he⟩,rfl⟩
  let H := FiniteGrp.of (G ⧸ N)
  have nh : Nat.card H * 2=2^m := by
    change Nat.card (G ⧸ N) * 2 = 2^m
    exact (congrArg₂ (·*·) (Subgroup.index_eq_card N).symm cn.symm).trans (N.index_mul_card.trans hc)
  have hm : 0 < m := by
    by_contra! hx
    have me : m=0 := by omega
    rw [me,pow_zero] at nh
    omega
  have hcard : Nat.card H=2^(m-1) := by
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    exact nh.trans (by rw [←pow_succ];congr 1;omega)
  let K := frattini H
  have hidx := K.index_mul_card
  rw [hcard] at hidx
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show K.index ∣ 2^(m-1) from ⟨_,hidx.symm⟩)
  obtain ⟨t,_,ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card K ∣ 2^(m-1) from (dvd_mul_left _ _).trans (dvd_of_eq hidx))
  have sum : d+t=m-1 := Nat.pow_right_injective (by decide : 1 < 2) (by rwa [hd,ht,←pow_add] at hidx)
  have ti : m-1-d=t := by omega
  apply Set.mem_iUnion_of_mem d
  apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m))
  rw [ti]
  have hh : Quotient.mk _ H ∈ frattiniClasses d t := ⟨H,⟨hz,he,ht,hd⟩,rfl⟩
  let key : frattiniClasses d t := ⟨Quotient.mk _ H,hh⟩
  have eq : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) H = Quotient.mk _ (refFrame key).H := (refClass key).symm
  let iso := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact eq))).groupIsoToMulEquiv
  refine ⟨G,⟨hc.trans (congrArg (2^·) (by omega)),key,third_transport (real_bridge N cn hn).some iso⟩,rfl⟩

theorem allThird_finite (d t : ℕ) : (allThird d t).Finite := by
  apply (Erdos1160.Tables.orderClasses_finite _).subset
  rintro _ ⟨G,⟨hc,_⟩,rfl⟩
  exact ⟨G,hc,rfl⟩

theorem thirdOrder_le_sum (m : ℕ) :
    (thirdOrderClasses m).ncard ≤ ∑ d ∈ Finset.range m,(allThird d (m-1-d)).ncard := by
  let F := fun d => allThird d (m-1-d)
  have hfin : (⋃ d ∈ Finset.range m,F d).Finite :=
    (Finset.range m).finite_toSet.biUnion (fun d _ => allThird_finite d _)
  exact (Set.ncard_le_ncard (thirdOrder_subset_ranks m) hfin).trans ((Finset.range m).set_ncard_biUnion_le F)

end CentralKernelCount

end

/- PowerOrder -/
section

namespace CentralKernelCount
open CategoryTheory ClassTwoProfile Erdos1160Growth.LowerTriangularUpper

def powerThirdOrders (m : ℕ) : Set classSpace :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G=2^m ∧
    ∃ (N : Subgroup G) (_ : N.Normal), Nat.card N=2 ∧ N ≤ Subgroup.center G ∧
      frattini (G ⧸ N) ≤ Subgroup.center (G ⧸ N) ∧ Nat.card (squareCore (frattini (G ⧸ N))) ≤ 8}

theorem powerThirdOrders_cover (m : ℕ) :
    powerThirdOrders m ⊆ ⋃ a ∈ Finset.range 4, ⋃ d ∈ Finset.range (m-1-a+1), allPower d (m-1-a-d) a := by
  rintro _ ⟨G,⟨hc,N,ni,cn,hn,hz,h8⟩,rfl⟩
  let H := FiniteGrp.of (G ⧸ N)
  have nh : Nat.card H * 2=2^m := by
    change Nat.card (G ⧸ N) * 2 = 2^m
    exact (congrArg₂ (·*·) (Subgroup.index_eq_card N).symm cn.symm).trans (N.index_mul_card.trans hc)
  have hm : 0 < m := by
    by_contra! hy
    rw [show m=0 by omega,pow_zero] at nh
    omega
  have ch : Nat.card H=2^(m-1) := by
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
    exact nh.trans (by rw [←pow_succ];congr 1;omega)
  let K := frattini H
  have hk := K.index_mul_card
  rw [ch] at hk
  obtain ⟨d,_,hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show K.index ∣ 2^(m-1) from ⟨_,hk.symm⟩)
  obtain ⟨s,_,hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card K ∣ 2^(m-1) from (dvd_mul_left _ _).trans (dvd_of_eq hk))
  obtain ⟨a,has,ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card (squareCore K) ∣ 2^s from hs ▸ (squareCore K).card_subgroup_dvd_card)
  have hsum : d+s=m-1 := Nat.pow_right_injective (by decide : 1 < 2) (by rwa [hd,hs,←pow_add] at hk)
  have hsmall : 2^a ≤ 2^3 := ha ▸ h8
  have a3 : a ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hsmall
  let t := m-1-a-d
  have st : t+a=s := by dsimp [t];omega
  have hp : SmallProfile H d t a := ⟨hz,hd,st ▸ hs,ha⟩
  obtain ⟨b,S,pos,total,im⟩ := small_frattini_coords hp
  let F : PowerFrame H d t a := ⟨hp,b,pos,total,S,im⟩
  let key : powerBases d t a := ⟨Quotient.mk _ H,H,⟨F⟩,rfl⟩
  let eq : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) H = Quotient.mk _ (powerBase key) := (powerBase_rep key).symm
  let iso := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact eq))).groupIsoToMulEquiv
  apply Set.mem_iUnion_of_mem a
  apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : a < 4))
  apply Set.mem_iUnion_of_mem d
  apply Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega : d < m-1-a+1))
  refine ⟨G,⟨hc.trans (congrArg (2^·) (show m=d+t+a+1 by omega)),key,?_⟩,rfl⟩
  exact third_transport (real_bridge N cn hn).some iso

theorem allPower_finite (d t a : ℕ) : (allPower d t a).Finite := by
  apply (Erdos1160.Tables.orderClasses_finite _).subset
  rintro _ ⟨G,⟨hc,_⟩,rfl⟩
  exact ⟨G,hc,rfl⟩

theorem allPower_le_sum (d t a : ℕ) (ha : a ≤ 3) :
    (allPower d t a).ncard ≤ (lowPowerClasses d t a 34).ncard+(paddedPowerHigh d t a).ncard := by
  have lo : (lowPowerClasses d t a 34).Finite := (Erdos1160.Tables.orderClasses_finite _).subset <| by
    rintro _ ⟨G,⟨h,_⟩,rfl⟩
    exact ⟨G,h,rfl⟩
  have hi : (paddedPowerHigh d t a).Finite := by
    by_cases h : 32 ≤ d ∧ 32 ≤ t
    · rw [paddedPowerHigh,if_pos h]
      exact Set.finite_iUnion (fun p=> singlePowerHigh_finite _ _ _ _)
    · simp only [paddedPowerHigh,if_neg h,Set.finite_empty]
  exact (Set.ncard_le_ncard (all_power_cover d t a ha) (lo.union hi)).trans (Set.ncard_union_le ..)

theorem powerThirdOrders_le_sum (m : ℕ) :
    (powerThirdOrders m).ncard ≤ ∑ a ∈ Finset.range 4, ∑ d ∈ Finset.range (m-1-a+1),
      ((lowPowerClasses d (m-1-a-d) a 34).ncard + (paddedPowerHigh d (m-1-a-d) a).ncard) := by
  let F (a : ℕ) := ⋃ d ∈ Finset.range (m-1-a+1), allPower d (m-1-a-d) a
  have hf (a : ℕ) : (F a).Finite := (Finset.range (m-1-a+1)).finite_toSet.biUnion (fun d _ => allPower_finite d _ a)
  have cover := Set.ncard_le_ncard (powerThirdOrders_cover m) ((Finset.range 4).finite_toSet.biUnion (fun a _=>hf a))
  apply (cover.trans ((Finset.range 4).set_ncard_biUnion_le F)).trans
  apply Finset.sum_le_sum
  intro a ha
  exact ((Finset.range (m-1-a+1)).set_ncard_biUnion_le (fun d => allPower d (m-1-a-d) a)).trans
    (Finset.sum_le_sum (fun d _=>allPower_le_sum d _ a (by have := Finset.mem_range.mp ha;omega)))

end CentralKernelCount

end

/- SmallGammaUpper -/
section

namespace SmallGamma
open CentralKernelCount OrbitUp ClassTwoProfile Erdos1160Growth.LowerTriangularUpper

theorem bounded_power_order (m : ℕ) (hm : 10000010 ≤ m) :
    (256*(powerThirdOrders m).ncard)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  apply four_profiles_two_ranks m _ (by omega) _ _ (powerThirdOrders_le_sum m)
  · intro a ha d hd
    have h := low_power_upper d (m-1-a-d) a ha (by omega)
    rwa [show d+(m-1-a-d)+a+1=m by omega] at h
  · intro a ha d hd
    have h := padded_estimate ha (by omega : 10000000 ≤ d+(m-1-a-d))
      (padded_power_high_count d (m-1-a-d) a)
    rwa [show d+(m-1-a-d)+a+1=m by omega] at h

/-- Sharp upper bound for all groups whose third lower central subgroup has
order at most two and whose commutator subgroup is noncentral. -/
theorem small_third_layer_upper (m : ℕ) (hm : 10000010 ≤ m) :
    (8*(target m).ncard)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  have fin : (powerThirdOrders m).Finite := (Erdos1160.Tables.orderClasses_finite (2^m)).subset (by
    rintro _ ⟨G,⟨h,_⟩,rfl⟩; exact ⟨G,h,rfl⟩)
  have hs := bounded_power_order m hm
  apply target_bound hm fin ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (by decide : 32 ≤ 256)) 27)).trans hs)
  apply target_subset (by omega)
  intro G hc hn hz hs
  exact ⟨G,⟨hc,ThirdLowerCentral.third G,inferInstance,hn,
    ThirdLowerCentral.order_two_central _ hn,hz,hs⟩,rfl⟩

end SmallGamma

end

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1.H2 := by
  exact Filter.eventually_atTop.mpr ⟨10000010, fun m hm => SmallGamma.small_third_layer_upper m hm⟩
