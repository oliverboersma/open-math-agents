import OMAReductions.R_Erdos551_erdos_551_variants_sufficiently_large_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# The cycle–clique Ramsey upper bound for `19 ≤ n ≤ k`

Credit: @MrSeizy. The graph-theoretic argument comes from the merged parent proof
at `db7611b`, adapted from `openai/math@3344da59991ed94f9ba711217b29c1d760badfa6`
(Apache-2.0). The final step extracts the containment assertion for H3.
-/

theorem SimpleGraph.ncard_neighborSet {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) [DecidableRel G.Adj] : (G.neighborSet v).ncard = G.degree v := by
  rw [Set.ncard_eq_toFinset_card, ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp

namespace OAI
namespace CycleClique.Construction
variable {V W : Type*}
def cycleNext {m : ℕ} (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩
def HasCycle (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ f : Fin m → V, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (cycleNext i))
def HasIndependent (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧ ∀ i j, ¬ G.Adj (f i) (f j)
def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasCycle G m ∨ HasIndependent G n
def IsRamseyNumber (m n N : ℕ) : Prop :=
  RamseyProperty m n N ∧ ∀ M < N, ¬ RamseyProperty m n M
theorem HasCycle.map {G : SimpleGraph V} {H : SimpleGraph W} {m : ℕ}
    (h : HasCycle G m) (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {x y}, G.Adj x y → H.Adj (f x) (f y)) : HasCycle H m := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨f ∘ c, hf.comp hc, fun i => hadj (he i)⟩
theorem HasIndependent.map {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (h : HasIndependent G n) (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {x y}, H.Adj (f x) (f y) → G.Adj x y) : HasIndependent H n := by
  obtain ⟨c, hc, he⟩ := h
  exact ⟨f ∘ c, hf.comp hc, fun i j h => he i j (hadj h)⟩
theorem HasIndependent.card_le [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (h : HasIndependent G n) : n ≤ Fintype.card V := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_injective f hf
theorem HasCycle.card_le [Fintype V] {G : SimpleGraph V} {m : ℕ}
    (h : HasCycle G m) : m ≤ Fintype.card V := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_injective f hf
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} [Fintype V]
def IndependenceBound (G : SimpleGraph V) (a : ℕ) : Prop :=
  ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card ≤ a
noncomputable def closedNeighborhood (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ I ∨ ∃ i ∈ I, G.Adj i v
@[simp] theorem mem_closedNeighborhood {G : SimpleGraph V} {I : Finset V} {v : V} :
    v ∈ closedNeighborhood G I ↔ v ∈ I ∨ ∃ i ∈ I, G.Adj i v := by
  classical
  simp [closedNeighborhood]
theorem subset_closedNeighborhood (G : SimpleGraph V) (I : Finset V) :
    I ⊆ closedNeighborhood G I := by
  intro v hv
  exact mem_closedNeighborhood.mpr (Or.inl hv)
omit [Fintype V] in
theorem independenceBound_iff_not_hasIndependent {G : SimpleGraph V} {a : ℕ} :
    IndependenceBound G a ↔ ¬ HasIndependent G (a + 1) := by
  classical
  constructor
  · intro h ⟨f, hf, he⟩
    let I := Finset.univ.image f
    have hI : G.IsIndepSet (I : Set V) := by
      intro x hx y hy _
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact he i j
    have hcard : I.card = a + 1 := by
      simp [I, Finset.card_image_of_injective _ hf]
    have := h I hI
    omega
  · intro h I hI
    by_contra hn
    obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show a + 1 ≤ I.card by omega)
    let e : Fin (a + 1) ≃ J := (Finset.equivFinOfCardEq hJ).symm
    apply h
    refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
    intro i j hij
    have hne : (e i).val ≠ (e j).val := G.ne_of_adj hij
    exact hI (hJI (e i).property) (hJI (e j).property) hne hij
theorem independent_union_outside [DecidableEq V] {G : SimpleGraph V} {I J : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hJ : G.IsIndepSet (J : Set V))
    (hout : ∀ v ∈ J, v ∉ closedNeighborhood G I) :
    G.IsIndepSet ((I ∪ J : Finset V) : Set V) := by
  classical
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · exact hI hx hy hxy
  · intro hadj
    exact hout y hy (mem_closedNeighborhood.mpr (Or.inr ⟨x, hx, hadj⟩))
  · intro hadj
    exact hout x hx (mem_closedNeighborhood.mpr (Or.inr ⟨y, hy, hadj.symm⟩))
  · exact hJ hx hy hxy
theorem independent_outside_bound {G : SimpleGraph V} {a : ℕ}
    (hG : IndependenceBound G a) {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) :
    IndependenceBound (G.induce {v | v ∉ closedNeighborhood G I}) (a - I.card) := by
  classical
  intro J hJ
  let J' : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
  have hJ' : G.IsIndepSet (J' : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact hJ hx' hy' (fun he => hxy (congrArg Subtype.val he))
  have hout : ∀ v ∈ J', v ∉ closedNeighborhood G I := by
    intro v hv
    obtain ⟨v', _, rfl⟩ := Finset.mem_map.mp hv
    exact v'.property
  have hdis : Disjoint I J' := by
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    exact hout v hvJ (subset_closedNeighborhood G I hvI)
  have hbound := hG (I ∪ J') (independent_union_outside hI hJ' hout)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_map] at hbound
  omega
theorem minimal_counterexample_expansion {G : SimpleGraph V} {k a : ℕ}
    (hcard : Fintype.card V = k * a + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hbound : IndependenceBound G a)
    (hsmall : ∀ (b : ℕ), b < a →
      ∀ (Y : Finset V),
        ¬ HasCycle (G.induce (Y : Set V)) (k + 1) →
        IndependenceBound (G.induce (Y : Set V)) b → Y.card ≤ k * b)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    k * I.card + 1 ≤ (closedNeighborhood G I).card := by
  classical
  let Y := Finset.univ \ closedNeighborhood G I
  have hY : (Y : Set V) = {v | v ∉ closedNeighborhood G I} := by
    ext v
    simp [Y]
  have hb : a - I.card < a := by
    have := hbound I hI
    have := Finset.card_pos.mpr hne
    omega
  have hcyY : ¬ HasCycle (G.induce (Y : Set V)) (k + 1) := by
    intro h
    exact hcycle (h.map Subtype.val Subtype.val_injective (fun h => h))
  have hindY : IndependenceBound (G.induce (Y : Set V)) (a - I.card) := by
    rw [hY]
    exact independent_outside_bound hbound hI
  have hs := hsmall (a - I.card) hb Y hcyY hindY
  have hsum : Y.card + (closedNeighborhood G I).card = k * a + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (closedNeighborhood G I))
    simpa [Y, hcard] using h
  have hi := hbound I hI
  have hmul : k * a = k * (a - I.card) + k * I.card := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hi]
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem independenceBound_indepNum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IndependenceBound G G.indepNum := fun _ h => h.card_le_indepNum
theorem indepNum_le_of_independenceBound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a : ℕ} (h : IndependenceBound G a) : G.indepNum ≤ a := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have := h I hI.isIndepSet
  simpa [hI.card_eq] using this
private theorem outside_indepNum_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    (G.induce {v | v ∉ closedNeighborhood G I}).indepNum ≤ G.indepNum - I.card := by
  classical
  exact indepNum_le_of_independenceBound
    (independent_outside_bound (independenceBound_indepNum G) hI)
theorem minimal_dense_expansion_even {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum ≤ Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card < s * (G.induce (Y : Set V)).indepNum)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    s * I.card ≤ (closedNeighborhood G I).card ∧
      ((closedNeighborhood G I).card < Fintype.card V →
        s * I.card < (closedNeighborhood G I).card) := by
  classical
  let Y : Finset V := Finset.univ \ closedNeighborhood G I
  have hY : (Y : Set V) = {v | v ∉ closedNeighborhood G I} := by ext v; simp [Y]
  have hsum : Y.card + (closedNeighborhood G I).card = Fintype.card V := by
    simpa [Y] using Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (closedNeighborhood G I))
  have hIcard := hI.card_le_indepNum
  have houtside : (G.induce (Y : Set V)).indepNum ≤ G.indepNum - I.card := by
    rw [hY]
    exact outside_indepNum_bound hI
  have hmul : s * G.indepNum = s * (G.indepNum - I.card) + s * I.card := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hIcard]
  have hclosedPos : 0 < (closedNeighborhood G I).card := by
    apply Finset.card_pos.mpr
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, subset_closedNeighborhood G I hv⟩
  by_cases hYempty : Y = ∅
  · have hYzero : Y.card = 0 := by simp [hYempty]
    have hmulI : s * I.card ≤ s * G.indepNum := Nat.mul_le_mul_left _ hIcard
    constructor <;> omega
  · have hYne := Finset.nonempty_iff_ne_empty.mpr hYempty
    have hmin := hminimal Y hYne (by omega)
    have hmulR := Nat.mul_le_mul_left s houtside
    constructor <;> omega
theorem minimal_dense_expansion_odd {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum < Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card ≤ s * (G.induce (Y : Set V)).indepNum)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    s * I.card < (closedNeighborhood G I).card := by
  classical
  let Y : Finset V := Finset.univ \ closedNeighborhood G I
  have hY : (Y : Set V) = {v | v ∉ closedNeighborhood G I} := by ext v; simp [Y]
  have hsum : Y.card + (closedNeighborhood G I).card = Fintype.card V := by
    simpa [Y] using Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (closedNeighborhood G I))
  have hIcard := hI.card_le_indepNum
  have houtside : (G.induce (Y : Set V)).indepNum ≤ G.indepNum - I.card := by
    rw [hY]
    exact outside_indepNum_bound hI
  have hmul : s * G.indepNum = s * (G.indepNum - I.card) + s * I.card := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hIcard]
  have hclosedPos : 0 < (closedNeighborhood G I).card := by
    apply Finset.card_pos.mpr
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, subset_closedNeighborhood G I hv⟩
  by_cases hYempty : Y = ∅
  · have hYzero : Y.card = 0 := by simp [hYempty]
    have hmulI : s * I.card ≤ s * G.indepNum := Nat.mul_le_mul_left _ hIcard
    omega
  · have hYne := Finset.nonempty_iff_ne_empty.mpr hYempty
    have hmin := hminimal Y hYne (by omega)
    have hmulR := Nat.mul_le_mul_left s houtside
    omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem indepNum_induce_add_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    (A B : Finset V) (hdis : Disjoint A B)
    (hanti : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    (G.induce (A : Set V)).indepNum + (G.induce (B : Set V)).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨I, hI⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  obtain ⟨J, hJ⟩ := (G.induce (B : Set V)).exists_isNIndepSet_indepNum
  let I' : Finset V := I.map ⟨Subtype.val, Subtype.val_injective⟩
  let J' : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
  have hIA : I' ⊆ A := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact i.property
  have hJB : J' ⊆ B := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact j.property
  have hI' : G.IsIndepSet (I' : Set V) := by
    intro x hx y hy hxy h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact hI.isIndepSet hi hj (fun h => hxy (congrArg Subtype.val h)) h
  have hJ' : G.IsIndepSet (J' : Set V) := by
    intro x hx y hy hxy h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact hJ.isIndepSet hi hj (fun h => hxy (congrArg Subtype.val h)) h
  have hIJ : G.IsIndepSet ((I' ∪ J' : Finset V) : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hI' hx hy hxy
    · exact hanti x (hIA hx) y (hJB hy)
    · exact fun h => hanti y (hIA hy) x (hJB hx) h.symm
    · exact hJ' hx hy hxy
  have hdis' : Disjoint I' J' := hdis.mono hIA hJB
  have hbound := hIJ.card_le_indepNum
  rw [Finset.card_union_of_disjoint hdis'] at hbound
  simpa [I', J', hI.card_eq, hJ.card_eq] using hbound
private structure DisconnectedPartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  cover : left ∪ right = Finset.univ
  disjoint : Disjoint left right
  anticomplete : ∀ x ∈ left, ∀ y ∈ right, ¬ G.Adj x y
private theorem disconnected_partition {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {G : SimpleGraph V} (hn : ¬ G.Connected) :
    Nonempty (DisconnectedPartition G) := by
  classical
  have hnp : ¬ G.Preconnected := fun h => hn ⟨h⟩
  change ¬ ∀ u v, G.Reachable u v at hnp
  push Not at hnp
  obtain ⟨u, v, huv⟩ := hnp
  let A : Finset V := Finset.univ.filter (G.Reachable u)
  let B : Finset V := Finset.univ.filter (fun x => ¬ G.Reachable u x)
  refine ⟨⟨A, B, ⟨u, by simp [A]⟩, ⟨v, by simp [B, huv]⟩, ?_, ?_, ?_⟩⟩
  · ext x
    simp [A, B]
    exact Classical.em _
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
  · intro x hx y hy hadj
    exact (Finset.mem_filter.mp hy).2 (((Finset.mem_filter.mp hx).2).trans hadj.reachable)
private theorem DisconnectedPartition.card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (p : DisconnectedPartition G) :
    p.left.card + p.right.card = Fintype.card V := by
  classical
  rw [← Finset.card_union_of_disjoint p.disjoint, p.cover, Finset.card_univ]
theorem minimal_dense_connected_even {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum ≤ Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card < s * (G.induce (Y : Set V)).indepNum) : G.Connected := by
  classical
  by_contra hn
  obtain ⟨p⟩ := disconnected_partition hn
  have hsum := p.card
  have hleftPos := Finset.card_pos.mpr p.left_nonempty
  have hrightPos := Finset.card_pos.mpr p.right_nonempty
  have hleft := hminimal p.left p.left_nonempty (by omega)
  have hright := hminimal p.right p.right_nonempty (by omega)
  have hbound := indepNum_induce_add_le p.left p.right p.disjoint p.anticomplete
  have hmul := Nat.mul_le_mul_left s hbound
  rw [Nat.mul_add] at hmul
  omega
theorem minimal_dense_connected_odd {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum < Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card ≤ s * (G.induce (Y : Set V)).indepNum) : G.Connected := by
  classical
  by_contra hn
  obtain ⟨p⟩ := disconnected_partition hn
  have hsum := p.card
  have hleftPos := Finset.card_pos.mpr p.left_nonempty
  have hrightPos := Finset.card_pos.mpr p.right_nonempty
  have hleft := hminimal p.left p.left_nonempty (by omega)
  have hright := hminimal p.right p.right_nonempty (by omega)
  have hbound := indepNum_induce_add_le p.left p.right p.disjoint p.anticomplete
  have hmul := Nat.mul_le_mul_left s hbound
  rw [Nat.mul_add] at hmul
  omega
theorem bipartite_order_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hbip : G.IsBipartite) : Fintype.card V ≤ 2 * G.indepNum := by
  classical
  obtain ⟨c⟩ := hbip
  let A : Finset V := Finset.univ.filter (fun v => c v = 0)
  let B : Finset V := Finset.univ.filter (fun v => ¬ c v = 0)
  have hA : G.IsIndepSet (A : Set V) := by
    intro x hx y hy _ hxy
    exact c.valid hxy (((Finset.mem_filter.mp hx).2).trans (Finset.mem_filter.mp hy).2.symm)
  have hB : G.IsIndepSet (B : Set V) := by
    intro x hx y hy _ hxy
    have hx1 := Fin.eq_one_of_ne_zero (c x) (Finset.mem_filter.mp hx).2
    have hy1 := Fin.eq_one_of_ne_zero (c y) (Finset.mem_filter.mp hy).2
    exact c.valid hxy (hx1.trans hy1.symm)
  have hsum : A.card + B.card = Fintype.card V := by
    simpa [A, B] using Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun v => c v = 0)
  have hleft := hA.card_le_indepNum
  have hright := hB.card_le_indepNum
  omega
theorem dense_nonbipartite {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ} (hs : 3 ≤ s)
    (hdense : s * G.indepNum ≤ Fintype.card V) : ¬ G.IsBipartite := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hsingle : G.IsIndepSet (({v} : Finset V) : Set V) := by simp
  have hpos : 1 ≤ G.indepNum := by simpa using hsingle.card_le_indepNum
  intro hbip
  have := bipartite_order_bound hbip
  nlinarith
theorem closedNeighborhood_singleton_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (closedNeighborhood G {v}).card = (G.neighborSet v).ncard + 1 := by
  classical
  have hclosed : closedNeighborhood G {v} = insert v (G.neighborFinset v) := by
    ext w
    simp [mem_closedNeighborhood]
  have hv : v ∉ G.neighborFinset v := by simp
  rw [hclosed, Finset.card_insert_of_notMem hv, Set.ncard_eq_toFinset_card]
  congr 2
  ext w
  simp
theorem dense_expansion_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : ℕ} (_hs : 1 ≤ s) (horder : 2 * s ≤ Fintype.card V)
    (hstrict : ∀ v : V, (closedNeighborhood G {v}).card < Fintype.card V →
      s < (closedNeighborhood G {v}).card) :
    ∀ v, s ≤ (G.neighborSet v).ncard := by
  intro v
  have hcard := closedNeighborhood_singleton_card G v
  have hle : (closedNeighborhood G {v}).card ≤ Fintype.card V :=
    Finset.card_le_univ _
  by_cases hfull : (closedNeighborhood G {v}).card = Fintype.card V
  · omega
  · have := hstrict v (by omega)
    omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem indepNum_le_of_induced_injection {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {x y}, H.Adj (f x) (f y) → G.Adj x y) : G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  let J : Finset W := I.map ⟨f, hf⟩
  have hJ : H.IsIndepSet (J : Set W) := by
    intro x hx y hy hxy hadjxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hI.isIndepSet ha hb (fun h => hxy (congrArg f h)) (hadj hadjxy)
  simpa [J, hI.card_eq] using hJ.card_le_indepNum
theorem indepNum_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : G.indepNum = H.indepNum := by
  apply Nat.le_antisymm
  · exact indepNum_le_of_induced_injection e e.injective (fun h => e.map_adj_iff.mp h)
  · exact indepNum_le_of_induced_injection e.symm e.symm.injective
      (fun h => e.symm.map_adj_iff.mp h)
private noncomputable def nestedInduceIso {V : Type*} (G : SimpleGraph V) (Y : Finset V)
    (Z : Finset Y) :
    (G.induce (Y : Set V)).induce (Z : Set Y) ≃g
      G.induce ((Z.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V) : Set V) := by
  classical
  let Z' : Finset V := Z.map ⟨Subtype.val, Subtype.val_injective⟩
  let f : Z → Z' := fun z => ⟨z.val.val, Finset.mem_map.mpr ⟨z.val, z.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Z' => z.val) h
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨a, ha, heq⟩ := Finset.mem_map.mp z.property
    refine ⟨⟨a, ha⟩, ?_⟩
    exact Subtype.ext heq
  refine { Equiv.ofBijective f ⟨hf, hs⟩ with map_rel_iff' := ?_ }
  rfl
theorem exists_minimal_dense_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : ℕ} (D : Finset V) (hD : D.Nonempty)
    (hdense : s * (G.induce (D : Set V)).indepNum ≤ D.card) :
    ∃ Y : Finset V, Y ⊆ D ∧ Y.Nonempty ∧
      s * (G.induce (Y : Set V)).indepNum ≤ Y.card ∧
      ∀ Z : Finset Y, Z.Nonempty → Z.card < Y.card →
        Z.card < s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum := by
  classical
  let P : Finset V → Prop := fun Y => Y ⊆ D ∧ Y.Nonempty ∧
    s * (G.induce (Y : Set V)).indepNum ≤ Y.card
  have hex : ∃ n, ∃ Y : Finset V, Y.card = n ∧ P Y :=
    ⟨D.card, D, rfl, Finset.Subset.refl _, hD, hdense⟩
  obtain ⟨Y, hYcard, hYP⟩ := Nat.find_spec hex
  have hmin : ∀ X : Finset V, P X → Y.card ≤ X.card := by
    intro X hX
    rw [hYcard]
    exact Nat.find_min' hex ⟨X, rfl, hX⟩
  refine ⟨Y, hYP.1, hYP.2.1, hYP.2.2, ?_⟩
  intro Z hZ hZcard
  by_contra hnot
  let Z' : Finset V := Z.map ⟨Subtype.val, Subtype.val_injective⟩
  have hZ'D : Z' ⊆ D := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
    exact hYP.1 a.property
  have hZ'ne : Z'.Nonempty := by simpa [Z'] using hZ
  have hIso := indepNum_eq_of_iso (nestedInduceIso G Y Z)
  have hZ'dense : s * (G.induce (Z' : Set V)).indepNum ≤ Z'.card := by
    rw [← hIso]
    simpa [Z'] using (show s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum ≤ Z.card by omega)
  have hm := hmin Z' ⟨hZ'D, hZ'ne, hZ'dense⟩
  have hc : Z'.card = Z.card := Finset.card_map _
  omega
theorem exists_minimal_dense_odd {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s : ℕ} (D : Finset V) (hD : D.Nonempty)
    (hdense : s * (G.induce (D : Set V)).indepNum < D.card) :
    ∃ Y : Finset V, Y ⊆ D ∧ Y.Nonempty ∧
      s * (G.induce (Y : Set V)).indepNum < Y.card ∧
      ∀ Z : Finset Y, Z.Nonempty → Z.card < Y.card →
        Z.card ≤ s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum := by
  classical
  let P : Finset V → Prop := fun Y => Y ⊆ D ∧ Y.Nonempty ∧
    s * (G.induce (Y : Set V)).indepNum < Y.card
  have hex : ∃ n, ∃ Y : Finset V, Y.card = n ∧ P Y :=
    ⟨D.card, D, rfl, Finset.Subset.refl _, hD, hdense⟩
  obtain ⟨Y, hYcard, hYP⟩ := Nat.find_spec hex
  have hmin : ∀ X : Finset V, P X → Y.card ≤ X.card := by
    intro X hX
    rw [hYcard]
    exact Nat.find_min' hex ⟨X, rfl, hX⟩
  refine ⟨Y, hYP.1, hYP.2.1, hYP.2.2, ?_⟩
  intro Z hZ hZcard
  by_contra hnot
  let Z' : Finset V := Z.map ⟨Subtype.val, Subtype.val_injective⟩
  have hZ'D : Z' ⊆ D := by
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
    exact hYP.1 a.property
  have hZ'ne : Z'.Nonempty := by simpa [Z'] using hZ
  have hIso := indepNum_eq_of_iso (nestedInduceIso G Y Z)
  have hZ'dense : s * (G.induce (Z' : Set V)).indepNum < Z'.card := by
    rw [← hIso]
    simpa [Z'] using (show s * ((G.induce (Y : Set V)).induce (Z : Set Y)).indepNum < Z.card by omega)
  have hm := hmin Z' ⟨hZ'D, hZ'ne, hZ'dense⟩
  have hc : Z'.card = Z.card := Finset.card_map _
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V ι : Type*}
theorem HasIndependent.mono {G : SimpleGraph V} {m n : ℕ}
    (h : HasIndependent G m) (hnm : n ≤ m) : HasIndependent G n := by
  obtain ⟨f, hf, hadj⟩ := h
  exact ⟨f ∘ Fin.castLE hnm, hf.comp (Fin.castLE_injective hnm),
    fun i j => hadj (Fin.castLE hnm i) (Fin.castLE hnm j)⟩
theorem exists_independent_subset {G : SimpleGraph V} {Y : Finset V} {n : ℕ}
    (h : HasIndependent (G.induce (Y : Set V)) n) :
    ∃ I : Finset V, I ⊆ Y ∧ G.IsIndepSet (I : Set V) ∧ I.card = n := by
  classical
  obtain ⟨f, hf, hadj⟩ := h
  let g : Fin n → V := fun i => (f i).val
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact (f i).property
  · intro v hv w hw _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    exact hadj i j
  · simp [Finset.card_image_of_injective _ hg]
theorem HasIndependent.le_indepNum [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (h : HasIndependent G n) : n ≤ G.indepNum := by
  classical
  obtain ⟨f, hf, hadj⟩ := h
  let I := Finset.univ.image f
  have hI : G.IsIndepSet (I : Set V) := by
    intro x hx y hy _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hadj i j
  have hc : I.card = n := by simp [I, Finset.card_image_of_injective _ hf]
  simpa [hc] using hI.card_le_indepNum
theorem hasIndependent_iff_le_indepNum [Fintype V] {G : SimpleGraph V} {n : ℕ} :
    HasIndependent G n ↔ n ≤ G.indepNum := by
  classical
  refine ⟨HasIndependent.le_indepNum, fun hn => ?_⟩
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hni : n ≤ I.card := by simpa only [hI.card_eq] using hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hni
  let e : Fin n ≃ J := (Finset.equivFinOfCardEq hJ).symm
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i j hadj
  exact hI.isIndepSet (hJI (e i).property) (hJI (e j).property)
    (G.ne_of_adj hadj) hadj
theorem hasIndependent_induce_mono {G : SimpleGraph V} {Y Z : Finset V} {n : ℕ}
    (hYZ : Y ⊆ Z) (h : HasIndependent (G.induce (Y : Set V)) n) :
    HasIndependent (G.induce (Z : Set V)) n := by
  let f : Y → Z := fun v => ⟨v.val, hYZ v.property⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : Z => z.val) he)
  exact h.map f hf (fun h => h)
theorem hasIndependent_one_of_nonempty {G : SimpleGraph V} {Y : Finset V}
    (hY : Y.Nonempty) : HasIndependent (G.induce (Y : Set V)) 1 := by
  obtain ⟨v, hv⟩ := hY
  exact ⟨fun _ => ⟨v, hv⟩, fun _ _ _ => Subsingleton.elim _ _, fun _ _ h => G.irrefl h⟩
theorem independent_packing [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    (hbound : IndependenceBound G k) (F : Finset ι) (I : ι → Finset V)
    (hind : ∀ i ∈ F, G.IsIndepSet (I i : Set V))
    (hdis : (F : Set ι).PairwiseDisjoint I)
    (hanti : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x ∈ I i, ∀ y ∈ I j, ¬ G.Adj x y) :
    ∑ i ∈ F, (I i).card ≤ k := by
  classical
  have hUnion : G.IsIndepSet ((F.biUnion I : Finset V) : Set V) := by
    intro x hx y hy hxy
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact hind i hi hx hy hxy
    · exact hanti i hi j hj hij x hx y hy
  have hc := hbound (F.biUnion I) hUnion
  simpa only [Finset.card_biUnion hdis] using hc
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
noncomputable def independentOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : Finset V := by
  classical
  exact (Classical.choose (G.induce (D : Set V)).exists_isNIndepSet_indepNum).map
    ⟨Subtype.val, Subtype.val_injective⟩
theorem independentOn_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : independentOn G D ⊆ D := by
  classical
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  exact i.property
theorem independentOn_independent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : G.IsIndepSet (independentOn G D : Set V) := by
  classical
  intro x hx y hy hxy h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
  exact (Classical.choose_spec (G.induce (D : Set V)).exists_isNIndepSet_indepNum).isIndepSet
    hi hj (fun h => hxy (congrArg Subtype.val h)) h
theorem independentOn_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) :
    (independentOn G D).card = (G.induce (D : Set V)).indepNum := by
  classical
  rw [independentOn, Finset.card_map]
  exact (Classical.choose_spec (G.induce (D : Set V)).exists_isNIndepSet_indepNum).card_eq
noncomputable def distanceLayer {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (j : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.Reachable root v ∧ G.dist root v = j
@[simp] theorem mem_distanceLayer {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root v : V} {j : ℕ} :
    v ∈ distanceLayer G root j ↔ G.Reachable root v ∧ G.dist root v = j := by
  classical
  simp [distanceLayer]
theorem distanceLayer_zero {V : Type*} [Fintype V] (G : SimpleGraph V) (root : V) :
    distanceLayer G root 0 = {root} := by
  classical
  ext v
  simp only [mem_distanceLayer, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    rcases G.dist_eq_zero_iff_eq_or_not_reachable.mp hd with h | h
    · exact h.symm
    · exact False.elim (h hr)
  · rintro rfl
    simp
theorem distanceLayers_disjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (distanceLayer G root i) (distanceLayer G root j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hi
  exact hij ((mem_distanceLayer.mp hv).2.symm.trans (mem_distanceLayer.mp hi).2)
theorem same_parity_layers_anticomplete {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root : V} {i j : ℕ} (hij : i ≠ j) (hparity : i % 2 = j % 2)
    {x y : V} (hx : x ∈ distanceLayer G root i) (hy : y ∈ distanceLayer G root j) :
    ¬ G.Adj x y := by
  intro h
  have hdiff := h.diff_dist_adj (u := root)
  rw [(mem_distanceLayer.mp hx).2, (mem_distanceLayer.mp hy).2] at hdiff
  omega
theorem distanceLayer_neighbor_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root x y : V} {i : ℕ}
    (hx : x ∈ distanceLayer G root i) (hxy : G.Adj x y) :
    ∃ j ≤ i + 1, y ∈ distanceLayer G root j := by
  have hx' := mem_distanceLayer.mp hx
  refine ⟨G.dist root y, ?_, mem_distanceLayer.mpr ⟨hx'.1.trans hxy.reachable, rfl⟩⟩
  have hdiff := hxy.diff_dist_adj (u := root)
  rw [hx'.2] at hdiff
  omega
theorem parity_layer_independence_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hbound : IndependenceBound G k) (root : V) (i : ℕ) :
    ∑ j ∈ (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2),
      (G.induce (distanceLayer G root j : Set V)).indepNum ≤ k := by
  classical
  let F := (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2)
  let I := fun j => independentOn G (distanceLayer G root j)
  have hind : ∀ j ∈ F, G.IsIndepSet (I j : Set V) := fun j _ => independentOn_independent _ _
  have hdis : (F : Set ℕ).PairwiseDisjoint I := by
    intro j _ l _ hjl
    exact (distanceLayers_disjoint G root hjl).mono
      (independentOn_subset _ _) (independentOn_subset _ _)
  have hanti : ∀ j ∈ F, ∀ l ∈ F, j ≠ l → ∀ x ∈ I j, ∀ y ∈ I l, ¬ G.Adj x y := by
    intro j hj l hl hjl x hx y hy
    apply same_parity_layers_anticomplete hjl
      (((Finset.mem_filter.mp hj).2).trans (Finset.mem_filter.mp hl).2.symm)
    · exact independentOn_subset _ _ hx
    · exact independentOn_subset _ _ hy
  have h := independent_packing hbound F I hind hdis hanti
  simpa only [I, independentOn_card] using h
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem exists_distance_predecessor {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) (hd : 0 < G.dist root v) :
    ∃ w, G.Adj v w ∧ G.dist root w + 1 = G.dist root v ∧ G.Reachable root w := by
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  rw [SimpleGraph.dist_comm] at hp
  cases p with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hp; omega
  | @cons v w root hvw p =>
    have hlen : p.length + 1 = G.dist root v := by simpa using hp
    have hupper : G.dist root w ≤ p.length := by simpa using G.dist_le p.reverse
    have hdiff := hvw.diff_dist_adj (u := root)
    exact ⟨w, hvw, by omega, p.reachable.symm⟩
noncomputable def bfsParent {V : Type*} (G : SimpleGraph V) (root v : V) : V := by
  classical
  exact if h : G.Reachable root v ∧ 0 < G.dist root v then
    Classical.choose (exists_distance_predecessor h.1 h.2) else v
theorem bfsParent_spec {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) (hd : 0 < G.dist root v) :
    G.Adj v (bfsParent G root v) ∧
      G.dist root (bfsParent G root v) + 1 = G.dist root v ∧
      G.Reachable root (bfsParent G root v) := by
  rw [bfsParent, dif_pos ⟨hr, hd⟩]
  exact Classical.choose_spec (exists_distance_predecessor hr hd)
@[simp] theorem bfsParent_root {V : Type*} (G : SimpleGraph V) (root : V) :
    bfsParent G root root = root := by classical exact (by simp [bfsParent])
theorem bfsAncestor_level {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) :
    ∀ j ≤ G.dist root v,
      G.Reachable root ((bfsParent G root)^[j] v) ∧
      G.dist root ((bfsParent G root)^[j] v) = G.dist root v - j := by
  intro j
  induction j with
  | zero => intro _; simpa using hr
  | succ j ih =>
    intro hj
    obtain ⟨hrj, hdj⟩ := ih (by omega)
    have hpos : 0 < G.dist root ((bfsParent G root)^[j] v) := by omega
    obtain ⟨_, hdnext, hrnext⟩ := bfsParent_spec hrj hpos
    rw [Function.iterate_succ_apply']
    exact ⟨hrnext, by omega⟩
theorem bfsAncestor_root {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) :
    (bfsParent G root)^[G.dist root v] v = root := by
  obtain ⟨hr', hd⟩ := bfsAncestor_level hr (G.dist root v) le_rfl
  have hz : G.dist root ((bfsParent G root)^[G.dist root v] v) = 0 := by omega
  rcases G.dist_eq_zero_iff_eq_or_not_reachable.mp hz with heq | hn
  · exact heq.symm
  · exact False.elim (hn hr')
theorem bfsAncestor_adjacent {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) {j : ℕ} (hj : j < G.dist root v) :
    G.Adj ((bfsParent G root)^[j] v) ((bfsParent G root)^[j + 1] v) := by
  obtain ⟨hrj, hdj⟩ := bfsAncestor_level hr j (by omega)
  have h := (bfsParent_spec hrj (by omega)).1
  simpa only [Function.iterate_succ_apply'] using h
theorem bfsAncestor_injective {V : Type*} {G : SimpleGraph V} {root v : V}
    (hr : G.Reachable root v) {d : ℕ} (hd : d ≤ G.dist root v) :
    Function.Injective (fun i : Fin (d + 1) => (bfsParent G root)^[i.val] v) := by
  intro i j hij
  have hi := (bfsAncestor_level hr i.val (by have := i.isLt; omega)).2
  have hj := (bfsAncestor_level hr j.val (by have := j.isLt; omega)).2
  have hlevel := congrArg (G.dist root) hij
  rw [hi, hj] at hlevel
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem exists_bfs_branch_partition {V : Type*} [Fintype V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d : ℕ}
    (hY : 2 ≤ Y.card)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d) :
    ∃ p, 1 ≤ p ∧ p ≤ d ∧ ∃ c, ∃ χ : Y → Fin 2,
      (∃ u v, χ u ≠ χ v) ∧
      (∀ v : Y, (bfsParent G root)^[p] v.val = c) ∧
      (∀ u v : Y, χ u ≠ χ v → ∀ j < p,
        (bfsParent G root)^[j] u.val ≠ (bfsParent G root)^[j] v.val) := by
  classical
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
  let P := bfsParent G root
  have hroot : ∀ v ∈ Y, P^[d] v = root := by
    intro v hv
    have h := bfsAncestor_root (hlayer v hv).1
    simpa only [(hlayer v hv).2] using h
  have hex : ∃ p, p ≤ d ∧ ∀ v ∈ Y, P^[p] v = P^[p] v₀ :=
    ⟨d, le_rfl, fun v hv => (hroot v hv).trans (hroot v₀ hv₀).symm⟩
  let p := Nat.find hex
  have hp := Nat.find_spec hex
  change p ≤ d ∧ ∀ v ∈ Y, P^[p] v = P^[p] v₀ at hp
  have hpos : 1 ≤ p := by
    by_contra hn
    have hpzero : p = 0 := by omega
    have hone : Y.card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha b hb
      have h₁ := hp.2 a ha
      have h₂ := hp.2 b hb
      simp only [hpzero, Function.iterate_zero, id_eq] at h₁ h₂
      exact h₁.trans h₂.symm)
    omega
  have hnot : ¬ ∀ v ∈ Y, P^[p - 1] v = P^[p - 1] v₀ := by
    intro hsame
    have hmin := Nat.find_min hex (show p - 1 < Nat.find hex by change p - 1 < p; omega)
    exact hmin ⟨by omega, hsame⟩
  push Not at hnot
  obtain ⟨v₁, hv₁, hdiff⟩ := hnot
  let χ : Y → Fin 2 := fun v => if P^[p - 1] v.val = P^[p - 1] v₀ then 0 else 1
  have hnonconstant : ∃ u v, χ u ≠ χ v := by
    refine ⟨⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩, ?_⟩
    simp [χ, hdiff]
  refine ⟨p, hpos, hp.1, P^[p] v₀, χ, hnonconstant,
    fun v => hp.2 v.val v.property, ?_⟩
  intro u v hχ j hj heq
  have hchild : P^[p - 1] u.val = P^[p - 1] v.val := by
    have h := congrArg (P^[p - 1 - j]) heq
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at h
    have hindex : p - 1 - j + j = p - 1 := by omega
    simpa only [hindex] using h
  apply hχ
  dsimp [χ]
  rw [hchild]
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def rotationIndex {r : ℕ} (p : Fin r) (i : Fin (r + 1)) : Fin (r + 1) :=
  ⟨if i.val ≤ p.val then i.val else r + p.val + 1 - i.val,
    by split_ifs <;> omega⟩
theorem rotationIndex_involutive {r : ℕ} (p : Fin r) :
    Function.Involutive (rotationIndex p) := by
  intro i
  apply Fin.ext
  dsimp [rotationIndex]
  split_ifs <;> omega
theorem rotationIndex_injective {r : ℕ} (p : Fin r) :
    Function.Injective (rotationIndex p) := (rotationIndex_involutive p).injective
@[simp] theorem rotationIndex_zero {r : ℕ} (p : Fin r) : rotationIndex p 0 = 0 := by
  apply Fin.ext
  simp [rotationIndex]
@[simp] theorem rotationIndex_last {r : ℕ} (p : Fin r) :
    rotationIndex p (Fin.last r) = p.succ := by
  apply Fin.ext
  dsimp [rotationIndex]
  split_ifs <;> omega
theorem rotationIndex_range {V : Type*} {r : ℕ} (f : Fin (r + 1) → V) (p : Fin r) :
    Set.range (f ∘ rotationIndex p) = Set.range f := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rotationIndex p i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨rotationIndex p i, congrArg f (rotationIndex_involutive p i)⟩
theorem rotate_path {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (f : Fin (r + 1) → V) (hf : Function.Injective f)
    (hchain : ∀ i : Fin r, G.Adj (f i.castSucc) (f i.succ))
    (p : Fin r) (hp : G.Adj (f (Fin.last r)) (f p.castSucc)) :
    Function.Injective (f ∘ rotationIndex p) ∧
      (∀ i : Fin r, G.Adj ((f ∘ rotationIndex p) i.castSucc)
        ((f ∘ rotationIndex p) i.succ)) ∧
      (f ∘ rotationIndex p) 0 = f 0 ∧
      (f ∘ rotationIndex p) (Fin.last r) = f p.succ ∧
      Set.range (f ∘ rotationIndex p) = Set.range f := by
  refine ⟨hf.comp (rotationIndex_injective p), ?_, by simp, by simp, rotationIndex_range f p⟩
  intro i
  change G.Adj (f (rotationIndex p i.castSucc)) (f (rotationIndex p i.succ))
  by_cases hlt : i.val < p.val
  · have hleft : rotationIndex p i.castSucc = i.castSucc := by
      apply Fin.ext
      simp only [rotationIndex, Fin.val_castSucc]
      split_ifs <;> omega
    have hright : rotationIndex p i.succ = i.succ := by
      apply Fin.ext
      simp only [rotationIndex, Fin.val_succ]
      split_ifs <;> omega
    simpa [hleft, hright] using hchain i
  · by_cases heq : i = p
    · subst i
      have hleft : rotationIndex p p.castSucc = p.castSucc := by
        apply Fin.ext
        simp [rotationIndex]
      have hright : rotationIndex p p.succ = Fin.last r := by
        apply Fin.ext
        simp only [rotationIndex, Fin.val_succ, Fin.val_last]
        split_ifs <;> omega
      simpa [hleft, hright] using hp.symm
    · have hgt : p.val < i.val := by
        have hneq : i.val ≠ p.val := fun h => heq (Fin.ext h)
        omega
      let j : Fin r := ⟨r + p.val - i.val, by omega⟩
      have hleft : rotationIndex p i.castSucc = j.succ := by
        apply Fin.ext
        simp only [rotationIndex, Fin.val_castSucc, Fin.val_succ, j]
        split_ifs <;> omega
      have hright : rotationIndex p i.succ = j.castSucc := by
        apply Fin.ext
        simp only [rotationIndex, Fin.val_castSucc, Fin.val_succ, j]
        split_ifs <;> omega
      simpa [hleft, hright] using (hchain j).symm
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem even_layer_growth_contradiction {s : ℕ} (_hs : 1 ≤ s) (p : ℕ → ℕ)
    (hzero : p 0 = 1) (hbound : p s ≤ 2 * s)
    (hstep : ∀ i < s,
      2 * s * p i < s * (p (i + 1) + p i - 1)) : False := by
  have hgrowth : ∀ i ≤ s, 1 + 2 * i ≤ p i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro his
      have hprev := ih (by omega)
      have hineq := hstep i (by omega)
      have hsum : p (i + 1) + p i - 1 + 1 = p (i + 1) + p i :=
        Nat.sub_add_cancel (by omega)
      have hincrement : p i + 2 ≤ p (i + 1) := by nlinarith
      omega
  have := hgrowth s le_rfl
  omega
theorem odd_layer_growth_contradiction {s : ℕ} (hs : 2 ≤ s) (p : ℕ → ℕ)
    (hzero : p 0 = 1) (hbound : p s ≤ 2 * s + 1)
    (hstep : ∀ i < s,
      (2 * s + 1) * p i ≤ s * (p (i + 1) + p i - 1)) : False := by
  have hgrowth : ∀ i ≤ s, 1 + 2 * i ≤ p i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro his
      have hprev := ih (by omega)
      have hineq := hstep i (by omega)
      have hsum : p (i + 1) + p i - 1 + 1 = p (i + 1) + p i :=
        Nat.sub_add_cancel (by omega)
      have hincrement : p i + 2 ≤ p (i + 1) := by nlinarith
      omega
  have hprev := hgrowth (s - 1) (by omega)
  have hineq := hstep (s - 1) (by omega)
  have hindex : s - 1 + 1 = s := by omega
  rw [hindex] at hineq
  have hsum : p s + p (s - 1) - 1 + 1 = p s + p (s - 1) :=
    Nat.sub_add_cancel (by omega)
  have hincrement : p (s - 1) + 3 ≤ p s := by nlinarith
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def parityIndices (i : ℕ) : Finset ℕ :=
  (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2)
def alternatingSum (α : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ parityIndices i, α j
@[simp] theorem alternatingSum_zero (α : ℕ → ℕ) : alternatingSum α 0 = α 0 := by
  simp [alternatingSum, parityIndices, Finset.filter_singleton]
theorem alternatingSum_partition (α : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    alternatingSum α i + alternatingSum α (i - 1) = ∑ j ∈ Finset.range (i + 1), α j := by
  have heq : ((Finset.range (i + 1)).filter fun j => ¬ j % 2 = i % 2) =
      parityIndices (i - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, parityIndices]
    omega
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.range (i + 1)) (fun j => j % 2 = i % 2) α
  rw [heq] at h
  exact h
theorem alternatingSum_shifted_partition (α : ℕ → ℕ) (hzero : α 0 = 1)
    {i : ℕ} (hi : 1 ≤ i) :
    ∑ j ∈ Finset.range i, α (j + 1) = alternatingSum α i + alternatingSum α (i - 1) - 1 := by
  have h := alternatingSum_partition α hi
  rw [Finset.sum_range_succ', hzero] at h
  omega
theorem alternatingSum_positive (α : ℕ → ℕ) (hzero : 1 ≤ α 0) (hone : 1 ≤ α 1)
    (i : ℕ) : 1 ≤ alternatingSum α i := by
  by_cases heven : i % 2 = 0
  · have hmem : 0 ∈ parityIndices i := by simp [parityIndices, heven]
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    exact hzero.trans h
  · have hodd : i % 2 = 1 := by omega
    have hipos : 1 ≤ i := by omega
    have hmem : 1 ∈ parityIndices i := by simp [parityIndices, hodd]; omega
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) hmem
    exact hone.trans h
theorem indepNum_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.indepNum ≤ Fintype.card V := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have := Finset.card_le_univ I
  simpa [hI.card_eq] using this
theorem indepNum_pos_of_nonempty {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ G.indepNum := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hI : G.IsIndepSet (({v} : Finset V) : Set V) := by simp
  simpa using hI.card_le_indepNum
theorem distanceLayer_zero_indepNum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) :
    (G.induce (distanceLayer G root 0 : Set V)).indepNum = 1 := by
  classical
  rw [distanceLayer_zero]
  let : Nonempty ({root} : Finset V) := ⟨⟨root, by simp⟩⟩
  have hle := indepNum_le_card (G.induce (({root} : Finset V) : Set V))
  have hge := indepNum_pos_of_nonempty (G.induce (({root} : Finset V) : Set V))
  apply Nat.le_antisymm
  · simpa using hle
  · exact hge
theorem distanceLayer_one_nonempty {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    (distanceLayer G root 1).Nonempty := by
  classical
  have h := hexpand {root} (by simp) (by simp)
  have hc := closedNeighborhood_singleton_card G root
  have hdegree : 0 < (G.neighborFinset root).card := by
    simp only [Finset.card_singleton, Nat.mul_one, SimpleGraph.ncard_neighborSet,
      ← SimpleGraph.card_neighborFinset_eq_degree] at h hc
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hdegree
  have hadj := (G.mem_neighborFinset root v).mp hv
  exact ⟨v, mem_distanceLayer.mpr ⟨hadj.reachable, SimpleGraph.dist_eq_one_iff_adj.mpr hadj⟩⟩
noncomputable def parityIndependent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V := by
  classical
  exact (parityIndices i).biUnion (fun j => independentOn G (distanceLayer G root j))
theorem parityIndependent_independent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) :
    G.IsIndepSet (parityIndependent G root i : Set V) := by
  classical
  intro x hx y hy hxy
  obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨l, hl, hy⟩ := Finset.mem_biUnion.mp hy
  by_cases hsame : j = l
  · subst l
    exact independentOn_independent _ _ hx hy hxy
  · apply same_parity_layers_anticomplete hsame
      (((Finset.mem_filter.mp hj).2).trans (Finset.mem_filter.mp hl).2.symm)
    · exact independentOn_subset _ _ hx
    · exact independentOn_subset _ _ hy
theorem parityIndependent_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) :
    (parityIndependent G root i).card =
      alternatingSum (fun j => (G.induce (distanceLayer G root j : Set V)).indepNum) i := by
  classical
  have hdis : (parityIndices i : Set ℕ).PairwiseDisjoint
      (fun j => independentOn G (distanceLayer G root j)) := by
    intro j _ l _ hjl
    exact (distanceLayers_disjoint G root hjl).mono
      (independentOn_subset _ _) (independentOn_subset _ _)
  simp only [parityIndependent, Finset.card_biUnion hdis, alternatingSum, independentOn_card]
theorem distanceLayer_order_sum {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (root : V) {i : ℕ} (hi : 1 ≤ i) :
    k * alternatingSum (fun j => (G.induce (distanceLayer G root j : Set V)).indepNum) (i - 1) ≤
      ∑ j ∈ Finset.range i, (distanceLayer G root (j + 1)).card := by
  classical
  let α := fun j => (G.induce (distanceLayer G root j : Set V)).indepNum
  have hαzero : α 0 = 1 := distanceLayer_zero_indepNum G root
  have hαone : 1 ≤ α 1 := by
    let : Nonempty (distanceLayer G root 1) :=
      (distanceLayer_one_nonempty hk hexpand root).to_subtype
    exact indepNum_pos_of_nonempty _
  have hpos := alternatingSum_positive α (by omega) hαone (i - 1)
  have hIne : (parityIndependent G root (i - 1)).Nonempty := by
    apply Finset.card_pos.mp
    rw [parityIndependent_card]
    exact hpos
  have hclosed := hexpand _ (parityIndependent_independent G root (i - 1)) hIne
  let U : Finset V := (Finset.range (i + 1)).biUnion (distanceLayer G root)
  have hsub : closedNeighborhood G (parityIndependent G root (i - 1)) ⊆ U := by
    intro y hy
    rcases mem_closedNeighborhood.mp hy with hy | ⟨x, hx, hxy⟩
    · obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
      have hjbound : j < i := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        omega
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), independentOn_subset _ _ hy⟩
    · obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
      have hjbound : j < i := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        omega
      obtain ⟨l, hl, hy⟩ := distanceLayer_neighbor_le (independentOn_subset _ _ hx) hxy
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_range.mpr (by omega), hy⟩
  have hdis : ((Finset.range (i + 1)) : Set ℕ).PairwiseDisjoint (distanceLayer G root) := by
    intro j _ l _ hjl
    exact distanceLayers_disjoint G root hjl
  have hU : U.card = ∑ j ∈ Finset.range (i + 1), (distanceLayer G root j).card :=
    Finset.card_biUnion hdis
  have hcard := Finset.card_le_card hsub
  rw [hU, Finset.sum_range_succ', distanceLayer_zero, Finset.card_singleton] at hcard
  rw [parityIndependent_card] at hclosed
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem exists_dense_distance_layer_even {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (hs : 1 ≤ s)
    (hInd : IndependenceBound G (2 * s))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      2 * s * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ (distanceLayer G root i).Nonempty ∧
      s * (G.induce (distanceLayer G root i : Set V)).indepNum ≤
        (distanceLayer G root i).card := by
  classical
  let α := fun j => (G.induce (distanceLayer G root j : Set V)).indepNum
  let p := alternatingSum α
  have hzero : α 0 = 1 := distanceLayer_zero_indepNum G root
  have hpzero : p 0 = 1 := by simpa [p] using hzero
  have hpbound : p s ≤ 2 * s := by
    simpa [p, α, alternatingSum, parityIndices] using
      parity_layer_independence_bound hInd root s
  have hone := distanceLayer_one_nonempty (by omega : 1 ≤ 2 * s) hexpand root
  by_contra hn
  have hsmall : ∀ j, 1 ≤ j → j ≤ s → (distanceLayer G root j).Nonempty →
      (distanceLayer G root j).card < s * α j := by
    intro j hj hjs hne
    by_contra h
    exact hn ⟨j, hj, hjs, hne, (show s * α j ≤ (distanceLayer G root j).card by omega)⟩
  apply even_layer_growth_contradiction hs p hpzero hpbound
  intro i his
  have hle : ∀ j ∈ Finset.range (i + 1),
      (distanceLayer G root (j + 1)).card ≤ s * α (j + 1) := by
    intro j hj
    by_cases hne : (distanceLayer G root (j + 1)).Nonempty
    · exact (hsmall (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega) hne).le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hsum := Finset.sum_lt_sum hle
    (show ∃ j ∈ Finset.range (i + 1),
      (distanceLayer G root (j + 1)).card < s * α (j + 1) from
      ⟨0, Finset.mem_range.mpr (by omega), by
        simpa using hsmall 1 (by omega) (by omega) hone⟩)
  have hpartition := alternatingSum_shifted_partition α hzero (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpartition
  rw [← Finset.mul_sum, hpartition] at hsum
  have hexp := distanceLayer_order_sum (by omega : 1 ≤ 2 * s) hexpand root
    (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hexp
  exact lt_of_le_of_lt hexp hsum
theorem exists_dense_distance_layer_odd {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (hs : 2 ≤ s)
    (hInd : IndependenceBound G (2 * s + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      (2 * s + 1) * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ (distanceLayer G root i).Nonempty ∧
      s * (G.induce (distanceLayer G root i : Set V)).indepNum <
        (distanceLayer G root i).card := by
  classical
  let α := fun j => (G.induce (distanceLayer G root j : Set V)).indepNum
  let p := alternatingSum α
  have hzero : α 0 = 1 := distanceLayer_zero_indepNum G root
  have hpzero : p 0 = 1 := by simpa [p] using hzero
  have hpbound : p s ≤ 2 * s + 1 := by
    simpa [p, α, alternatingSum, parityIndices] using
      parity_layer_independence_bound hInd root s
  by_contra hn
  have hsmall : ∀ j, 1 ≤ j → j ≤ s → (distanceLayer G root j).Nonempty →
      (distanceLayer G root j).card ≤ s * α j := by
    intro j hj hjs hne
    by_contra h
    exact hn ⟨j, hj, hjs, hne, (show s * α j < (distanceLayer G root j).card by omega)⟩
  apply odd_layer_growth_contradiction hs p hpzero hpbound
  intro i his
  have hle : ∀ j ∈ Finset.range (i + 1),
      (distanceLayer G root (j + 1)).card ≤ s * α (j + 1) := by
    intro j hj
    by_cases hne : (distanceLayer G root (j + 1)).Nonempty
    · exact hsmall (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega) hne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hsum := Finset.sum_le_sum hle
  have hpartition := alternatingSum_shifted_partition α hzero (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hpartition
  rw [← Finset.mul_sum, hpartition] at hsum
  have hexp := distanceLayer_order_sum (by omega : 1 ≤ 2 * s + 1) hexpand root
    (i := i + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hexp
  exact hexp.trans hsum
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem independent_pair_finset {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (hxy : ¬ G.Adj x y) : G.IsIndepSet (({x, y} : Finset V) : Set V) := by
  classical
  intro a ha b hb hne hadj
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hne rfl
  · exact hxy hadj
  · exact hxy hadj.symm
  · exact hne rfl
theorem complete_of_indepNum_le_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hα : G.indepNum ≤ 1) : G = ⊤ := by
  classical
  apply SimpleGraph.isClique_univ.mp
  intro x _ y _ hxy
  by_contra hn
  have h := (independent_pair_finset hn).card_le_indepNum
  simp only [Finset.card_pair hxy] at h
  omega
theorem dense_indepNum_two {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ}
    (hclique : G.cliqueNum < s) (hdense : s * G.indepNum ≤ Fintype.card V) :
    2 ≤ G.indepNum := by
  classical
  have hpos := indepNum_pos_of_nonempty G
  by_contra hn
  have htop := complete_of_indepNum_le_one (G := G) (by omega)
  have hfull : G.IsClique ((Finset.univ : Finset V) : Set V) := by rw [htop]; simp
  have hc := hfull.card_le_cliqueNum
  simp only [Finset.card_univ] at hc
  have hmul := Nat.mul_le_mul_left s hpos
  simp only [Nat.mul_one] at hmul
  omega
theorem dense_layer_interface_even {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s : ℕ} (hs : 4 ≤ s)
    (hclique : G.cliqueNum < s) (hInd : IndependenceBound G (2 * s))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      2 * s * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ ∃ Y : Finset V,
      Y ⊆ distanceLayer G root i ∧ Y.Nonempty ∧
      (G.induce (Y : Set V)).Connected ∧
      ¬ (G.induce (Y : Set V)).IsBipartite ∧ 2 * s ≤ Y.card ∧
      (∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard) ∧
      (∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
        2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {u, v}).card) := by
  classical
  obtain ⟨i, hi, his, hD, hdense⟩ := exists_dense_distance_layer_even
    (by omega) hInd hexpand root
  obtain ⟨Y, hYD, hYne, hYdense, hYmin⟩ := exists_minimal_dense_even _ hD hdense
  let : Nonempty Y := hYne.to_subtype
  let H := G.induce (Y : Set V)
  have hcard : Fintype.card Y = Y.card := Fintype.card_coe _
  have hdense' : s * H.indepNum ≤ Fintype.card Y := by simpa [hcard] using hYdense
  have hmin : ∀ Z : Finset Y, Z.Nonempty → Z.card < Fintype.card Y →
      Z.card < s * (H.induce (Z : Set Y)).indepNum := by
    simpa only [hcard] using hYmin
  have hconn := minimal_dense_connected_even hdense' hmin
  have hnonbip := dense_nonbipartite (by omega) hdense'
  have hHclique : H.cliqueNum < s := (G.cliqueNum_induce_le _).trans_lt hclique
  have hα := dense_indepNum_two hHclique hdense'
  have horder : 2 * s ≤ Fintype.card Y := by nlinarith
  have hdegree : ∀ v : Y, s ≤ (H.neighborSet v).ncard := by
    apply dense_expansion_degree (by omega) horder
    intro v hv
    have h := (minimal_dense_expansion_even hdense' hmin {v} (by simp) (by simp)).2 hv
    simpa using h
  have hpair : ∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
      2 * s ≤ (closedNeighborhood H {u, v}).card := by
    intro u v huv hnot
    have h := (minimal_dense_expansion_even hdense' hmin {u, v}
      (independent_pair_finset hnot) (by simp)).1
    simpa only [Finset.card_pair huv, Nat.mul_comm s 2] using h
  refine ⟨i, hi, his, Y, hYD, hYne, hconn, hnonbip, ?_, hdegree, hpair⟩
  simpa only [hcard] using horder
theorem dense_layer_interface_odd {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s : ℕ} (hs : 4 ≤ s)
    (hclique : G.cliqueNum < s) (hInd : IndependenceBound G (2 * s + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      (2 * s + 1) * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ ∃ Y : Finset V,
      Y ⊆ distanceLayer G root i ∧ Y.Nonempty ∧
      (G.induce (Y : Set V)).Connected ∧
      ¬ (G.induce (Y : Set V)).IsBipartite ∧ 2 * s + 1 ≤ Y.card ∧
      (∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard) ∧
      (∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
        2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {u, v}).card) := by
  classical
  obtain ⟨i, hi, his, hD, hdense⟩ := exists_dense_distance_layer_odd
    (by omega) hInd hexpand root
  obtain ⟨Y, hYD, hYne, hYdense, hYmin⟩ := exists_minimal_dense_odd _ hD hdense
  let : Nonempty Y := hYne.to_subtype
  let H := G.induce (Y : Set V)
  have hcard : Fintype.card Y = Y.card := Fintype.card_coe _
  have hdense' : s * H.indepNum < Fintype.card Y := by simpa [hcard] using hYdense
  have hmin : ∀ Z : Finset Y, Z.Nonempty → Z.card < Fintype.card Y →
      Z.card ≤ s * (H.induce (Z : Set Y)).indepNum := by
    simpa only [hcard] using hYmin
  have hconn := minimal_dense_connected_odd hdense' hmin
  have hnonbip := dense_nonbipartite (by omega) hdense'.le
  have hHclique : H.cliqueNum < s := (G.cliqueNum_induce_le _).trans_lt hclique
  have hα := dense_indepNum_two hHclique hdense'.le
  have horder : 2 * s + 1 ≤ Fintype.card Y := by nlinarith
  have hdegree : ∀ v : Y, s ≤ (H.neighborSet v).ncard := by
    apply dense_expansion_degree (by omega) (by omega)
    intro v _
    have h := minimal_dense_expansion_odd hdense' hmin {v} (by simp) (by simp)
    simpa using h
  have hpair : ∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
      2 * s ≤ (closedNeighborhood H {u, v}).card := by
    intro u v huv hnot
    have h := minimal_dense_expansion_odd hdense' hmin {u, v}
      (independent_pair_finset hnot) (by simp)
    simp only [Finset.card_pair huv, Nat.mul_comm s 2] at h
    omega
  refine ⟨i, hi, his, Y, hYD, hYne, hconn, hnonbip, ?_, hdegree, hpair⟩
  simpa only [hcard] using horder
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def IsSpanningPath {V : Type*} (G : SimpleGraph V) (x : V) (W : Finset V)
    {r : ℕ} (f : Fin (r + 1) → V) : Prop :=
  Function.Injective f ∧
    (∀ i : Fin r, G.Adj (f i.castSucc) (f i.succ)) ∧
    f 0 = x ∧ Set.range f = (W : Set V)
noncomputable def pathEnds {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) (W : Finset V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun e => ∃ f : Fin (r + 1) → V,
    IsSpanningPath G x W f ∧ f (Fin.last r) = e
@[simp] theorem mem_pathEnds {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x e : V} {W : Finset V} {r : ℕ} :
    e ∈ pathEnds G x W r ↔ ∃ f : Fin (r + 1) → V,
      IsSpanningPath G x W f ∧ f (Fin.last r) = e := by
  classical
  simp [pathEnds]
theorem pathEnds_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) (W : Finset V) (r : ℕ) : pathEnds G x W r ⊆ W := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := mem_pathEnds.mp he
  change f (Fin.last r) ∈ (W : Set V)
  rw [← hf.2.2.2]
  exact ⟨Fin.last r, rfl⟩
theorem start_not_pathEnds {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ} (hr : 1 ≤ r) :
    x ∉ pathEnds G x W r := by
  intro hx
  obtain ⟨f, hf, heq⟩ := mem_pathEnds.mp hx
  have hi := congrArg Fin.val (hf.1 (hf.2.2.1.trans heq.symm))
  simp only [Fin.val_zero, Fin.val_last] at hi
  omega
theorem successor_mem_pathEnds {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (i : Fin r) (hi : G.Adj (f (Fin.last r)) (f i.castSucc)) :
    f i.succ ∈ pathEnds G x W r := by
  have hrot := rotate_path f hf.1 hf.2.1 i hi
  exact mem_pathEnds.mpr ⟨f ∘ rotationIndex i,
    ⟨hrot.1, hrot.2.1, hrot.2.2.1.trans hf.2.2.1,
      hrot.2.2.2.2.trans hf.2.2.2⟩, hrot.2.2.2.1⟩
theorem clique_of_endpoint_neighbor_cover {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {E W Z : Finset V} {s : ℕ}
    (hEW : E ⊆ W)
    (hcover : ∀ e ∈ E, ∀ v, G.Adj e v → v ∈ W ∪ Z)
    (hsize : W.card + Z.card < 2 * s)
    (hexpand : ∀ a b, a ≠ b → ¬ G.Adj a b →
      2 * s ≤ (closedNeighborhood G {a, b}).card) : G.IsClique (E : Set V) := by
  classical
  intro a ha b hb hab
  by_contra hn
  have hsub : closedNeighborhood G {a, b} ⊆ W ∪ Z := by
    intro v hv
    rcases mem_closedNeighborhood.mp hv with hv | ⟨e, he, hev⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_union_left _ (hEW ha)
      · exact Finset.mem_union_left _ (hEW hb)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hcover _ ha v hev
      · exact hcover _ hb v hev
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le W Z)
  have hlow := hexpand a b hab hn
  omega
theorem endpoint_degree_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x e : V} {W : Finset V} {r : ℕ}
    (he : e ∈ pathEnds G x W r)
    (hneighbors : ∀ v, G.Adj e v → v ∈ W) :
    (G.neighborSet e).ncard ≤ (pathEnds G x W r).card := by
  classical
  obtain ⟨f, hf, hlast⟩ := mem_pathEnds.mp he
  have hex : ∀ v : G.neighborFinset e, ∃ i : Fin r, f i.castSucc = v.val := by
    intro v
    have hadj := (G.mem_neighborFinset e v.val).mp v.property
    have hv : v.val ∈ Set.range f := by
      rw [hf.2.2.2]
      exact hneighbors v.val hadj
    obtain ⟨j, hj⟩ := hv
    have hjlt : j.val < r := by
      have hneq : j ≠ Fin.last r := by
        intro heq
        subst j
        have heq' : e = v.val := hlast.symm.trans hj
        exact hadj.ne heq'
      have hval : j.val ≠ r := fun h => hneq (Fin.ext h)
      omega
    exact ⟨⟨j.val, hjlt⟩, by simpa using hj⟩
  let pivot : G.neighborFinset e → Fin r := fun v => Classical.choose (hex v)
  have hpivot : ∀ v : G.neighborFinset e, f (pivot v).castSucc = v.val :=
    fun v => Classical.choose_spec (hex v)
  let suc : G.neighborFinset e → pathEnds G x W r := fun v =>
    ⟨f (pivot v).succ, successor_mem_pathEnds hf (pivot v) (by
      rw [hlast, hpivot]
      exact (G.mem_neighborFinset e v.val).mp v.property)⟩
  have hinj : Function.Injective suc := by
    intro a b hab
    have hfin := hf.1 (congrArg Subtype.val hab)
    have hp : pivot a = pivot b := Fin.succ_injective r hfin
    apply Subtype.ext
    rw [← hpivot a, ← hpivot b, hp]
  have hcard := Fintype.card_le_of_injective suc hinj
  simpa only [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hcard
theorem pathEnds_successor_closed {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    {i : Fin r} (hi : f i.castSucc ∈ pathEnds G x W r) :
    f i.succ ∈ pathEnds G x W r := by
  apply successor_mem_pathEnds hf
  have he : f (Fin.last r) ∈ pathEnds G x W r := mem_pathEnds.mpr ⟨f, hf, rfl⟩
  apply hclique he hi
  intro heq
  have := congrArg Fin.val (hf.1 heq)
  simp only [Fin.val_last, Fin.val_castSucc] at this
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def IsIndexedPath {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (f : Fin (r + 1) → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin r, G.Adj (f i.castSucc) (f i.succ)
theorem indexedPath_snoc {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) {v : V}
    (hv : v ∉ Set.range f) (hadj : G.Adj (f (Fin.last r)) v) :
    IsIndexedPath G (Fin.snoc f v) := by
  refine ⟨Fin.snoc_injective_iff.mpr ⟨hf.1, hv⟩, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hadj
  · have heq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
    rw [heq]
    simpa only [Fin.snoc_castSucc] using hf.2 j
theorem exists_longest_path_from {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ f 0 = x ∧
      ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → g 0 = x → q ≤ r := by
  classical
  let b := Fintype.card V - 1
  have hex : ∃ d, ∃ r, ∃ f : Fin (r + 1) → V,
      IsIndexedPath G f ∧ f 0 = x ∧ r + d = b := by
    refine ⟨b, 0, fun _ => x, ⟨?_, ?_⟩, rfl, by omega⟩
    · intro i j _
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · exact fun i => Fin.elim0 i
  obtain ⟨r, f, hf, hstart, hd⟩ := Nat.find_spec hex
  refine ⟨r, f, hf, hstart, ?_⟩
  intro q g hg hgs
  have hqcard := Fintype.card_le_of_injective g hg.1
  simp only [Fintype.card_fin] at hqcard
  have hqb : q ≤ b := by dsimp [b]; omega
  have hmin := Nat.find_min' hex
    (show ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ f 0 = x ∧
      r + (b - q) = b from ⟨q, g, hg, hgs, Nat.add_sub_of_le hqb⟩)
  omega
theorem longest_path_endpoint_neighbors {V : Type*} {G : SimpleGraph V}
    {x : V} {r : ℕ} {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hstart : f 0 = x)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → g 0 = x → q ≤ r) :
    ∀ v, G.Adj (f (Fin.last r)) v → v ∈ Set.range f := by
  intro v hv
  by_contra hn
  have hp := indexedPath_snoc hf hn hv
  have h := hmax (r + 1) (Fin.snoc f v) hp (by simpa using hstart)
  omega
theorem longest_path_degree_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x : V} {r : ℕ} {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hstart : f 0 = x)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → g 0 = x → q ≤ r) :
    (G.neighborSet (f (Fin.last r))).ncard ≤ r := by
  classical
  let e := f (Fin.last r)
  have hneigh := longest_path_endpoint_neighbors hf hstart hmax
  have hex : ∀ v : G.neighborFinset e, ∃ i : Fin r, f i.castSucc = v.val := by
    intro v
    have hadj := (G.mem_neighborFinset e v.val).mp v.property
    obtain ⟨j, hj⟩ := hneigh v.val hadj
    have hjlt : j.val < r := by
      have hneq : j ≠ Fin.last r := by
        intro h
        subst j
        exact hadj.ne hj
      have hval : j.val ≠ r := fun h => hneq (Fin.ext h)
      omega
    exact ⟨⟨j.val, hjlt⟩, by simpa using hj⟩
  let index : G.neighborFinset e → Fin r := fun v => Classical.choose (hex v)
  have hindex : ∀ v : G.neighborFinset e, f (index v).castSucc = v.val :=
    fun v => Classical.choose_spec (hex v)
  have hinj : Function.Injective index := by
    intro a b hab
    apply Subtype.ext
    rw [← hindex a, ← hindex b, hab]
  have hcard := Fintype.card_le_of_injective index hinj
  simpa only [Fintype.card_coe, Fintype.card_fin,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.ncard_neighborSet] using hcard
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private def twoPathLabel {V : Type*} {a b : ℕ} (_hb : 2 ≤ b)
    (f : Fin (a + 1) → V) (g : Fin (b + 1) → V) (i : Fin (a + b)) : V :=
  if hi : i.val ≤ a then f ⟨i.val, by omega⟩ else g ⟨i.val - a, by have := i.isLt; omega⟩
private theorem twoPathLabel_left {V : Type*} {a b : ℕ} (hb : 2 ≤ b)
    (f : Fin (a + 1) → V) (g : Fin (b + 1) → V) {i : Fin (a + b)}
    (hi : i.val ≤ a) : twoPathLabel hb f g i = f ⟨i.val, by omega⟩ := by
  simp only [twoPathLabel, dif_pos hi]
private theorem twoPathLabel_right {V : Type*} {a b : ℕ} (hb : 2 ≤ b)
    (f : Fin (a + 1) → V) (g : Fin (b + 1) → V) {i : Fin (a + b)}
    (hi : a < i.val) : twoPathLabel hb f g i = g ⟨i.val - a, by have := i.isLt; omega⟩ := by
  simp only [twoPathLabel, dif_neg (by omega : ¬ i.val ≤ a)]
theorem cycle_of_two_indexed_paths {V : Type*} {H : SimpleGraph V} {a b : ℕ}
    (hb : 2 ≤ b) (f : Fin (a + 1) → V) (g : Fin (b + 1) → V)
    (hf : IsIndexedPath H f) (hg : IsIndexedPath H g)
    (hstart : g 0 = f (Fin.last a)) (hend : g (Fin.last b) = f 0)
    (hdisjoint : ∀ i : Fin (b + 1), 0 < i.val → i.val < b →
      ∀ j : Fin (a + 1), f j ≠ g i) : HasCycle H (a + b) := by
  let : NeZero b := ⟨by omega⟩
  refine ⟨twoPathLabel hb f g, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    by_cases hi : i.val ≤ a
    · by_cases hj : j.val ≤ a
      · rw [twoPathLabel_left hb f g hi, twoPathLabel_left hb f g hj] at hij
        exact congrArg (fun x : Fin (a + 1) => x.val) (hf.1 hij)
      · rw [twoPathLabel_left hb f g hi, twoPathLabel_right hb f g (by omega)] at hij
        exact False.elim (hdisjoint ⟨j.val - a, by have := j.isLt; omega⟩
          (by dsimp; omega) (by dsimp; have := j.isLt; omega) _ hij)
    · by_cases hj : j.val ≤ a
      · rw [twoPathLabel_right hb f g (by omega), twoPathLabel_left hb f g hj] at hij
        exact False.elim (hdisjoint ⟨i.val - a, by have := i.isLt; omega⟩
          (by dsimp; omega) (by dsimp; have := i.isLt; omega) _ hij.symm)
      · rw [twoPathLabel_right hb f g (by omega), twoPathLabel_right hb f g (by omega)] at hij
        have hval := congrArg Fin.val (hg.1 hij)
        dsimp at hval
        omega
  · intro i
    by_cases hlast : i.val + 1 = a + b
    · have hn : (cycleNext i).val = 0 := by simp [cycleNext, hlast]
      have hleft : twoPathLabel hb f g i = g ⟨b - 1, by omega⟩ := by
        rw [twoPathLabel_right hb f g (by omega)]
        congr 1
        apply Fin.ext
        dsimp
        omega
      have hright : twoPathLabel hb f g (cycleNext i) = f 0 := by
        rw [twoPathLabel_left hb f g (by omega)]
        congr 1
        apply Fin.ext
        simpa only [Fin.val_zero] using hn
      rw [hleft, hright, ← hend]
      have h := hg.2 ⟨b - 1, by omega⟩
      have hi : (⟨b - 1, by omega⟩ : Fin b).succ = Fin.last b := by
        apply Fin.ext
        change b - 1 + 1 = b
        omega
      rw [hi] at h
      exact h
    · have hn : (cycleNext i).val = i.val + 1 := Nat.mod_eq_of_lt (by have := i.isLt; omega)
      by_cases hbefore : i.val < a
      · let p : Fin a := ⟨i.val, hbefore⟩
        have hleft : twoPathLabel hb f g i = f p.castSucc := by
          rw [twoPathLabel_left hb f g (by omega)]
          rfl
        have hright : twoPathLabel hb f g (cycleNext i) = f p.succ := by
          rw [twoPathLabel_left hb f g (by omega)]
          congr 1
          exact Fin.ext hn
        rw [hleft, hright]
        exact hf.2 p
      · by_cases heq : i.val = a
        · have hleft : twoPathLabel hb f g i = f (Fin.last a) := by
            rw [twoPathLabel_left hb f g (by omega)]
            congr 1
            exact Fin.ext heq
          have hright : twoPathLabel hb f g (cycleNext i) = g (Fin.succ (0 : Fin b)) := by
            rw [twoPathLabel_right hb f g (by omega)]
            congr 1
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_zero]
            omega
          rw [hleft, hright, ← hstart]
          exact hg.2 0
        · let p : Fin b := ⟨i.val - a, by have := i.isLt; omega⟩
          have hleft : twoPathLabel hb f g i = g p.castSucc := by
            rw [twoPathLabel_right hb f g (by omega)]
            rfl
          have hright : twoPathLabel hb f g (cycleNext i) = g p.succ := by
            rw [twoPathLabel_right hb f g (by omega)]
            congr 1
            apply Fin.ext
            dsimp [p]
            omega
          rw [hleft, hright]
          exact hg.2 p
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
noncomputable def bfsBranchPath {V : Type*} (G : SimpleGraph V) (root u v : V) (p : ℕ)
    (i : Fin (2 * p + 1)) : V :=
  if i.val ≤ p then (bfsParent G root)^[i.val] u
  else (bfsParent G root)^[2 * p - i.val] v
@[simp] theorem bfsBranchPath_start {V : Type*} (G : SimpleGraph V) (root u v : V) (p : ℕ) :
    bfsBranchPath G root u v p 0 = u := by simp [bfsBranchPath]
@[simp] theorem bfsBranchPath_end {V : Type*} (G : SimpleGraph V) (root u v : V)
    {p : ℕ} (hp : 1 ≤ p) : bfsBranchPath G root u v p (Fin.last (2 * p)) = v := by
  simp [bfsBranchPath, show ¬ 2 * p ≤ p by omega]
theorem bfsBranchPath_isPath {V : Type*} {G : SimpleGraph V} {root u v : V} {p d : ℕ}
    (hu : G.Reachable root u) (hv : G.Reachable root v)
    (hdu : G.dist root u = d) (hdv : G.dist root v = d) (hp : p ≤ d)
    (hcommon : (bfsParent G root)^[p] u = (bfsParent G root)^[p] v)
    (hsplit : ∀ j < p, (bfsParent G root)^[j] u ≠ (bfsParent G root)^[j] v) :
    IsIndexedPath G (bfsBranchPath G root u v p) := by
  have hlu : ∀ j ≤ p, G.dist root ((bfsParent G root)^[j] u) = d - j := by
    intro j hj
    simpa only [hdu] using (bfsAncestor_level hu j (by omega)).2
  have hlv : ∀ j ≤ p, G.dist root ((bfsParent G root)^[j] v) = d - j := by
    intro j hj
    simpa only [hdv] using (bfsAncestor_level hv j (by omega)).2
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    by_cases hip : i.val ≤ p
    · by_cases hjp : j.val ≤ p
      · simp only [bfsBranchPath, if_pos hip, if_pos hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlu _ hip, hlu _ hjp] at hd
        omega
      · simp only [bfsBranchPath, if_pos hip, if_neg hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlu _ hip, hlv _ (by omega)] at hd
        have heq : i.val = 2 * p - j.val := by omega
        rw [← heq] at hij
        exact False.elim (hsplit i.val (by omega) hij)
    · by_cases hjp : j.val ≤ p
      · simp only [bfsBranchPath, if_neg hip, if_pos hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlv _ (by omega), hlu _ hjp] at hd
        have heq : j.val = 2 * p - i.val := by omega
        rw [← heq] at hij
        exact False.elim (hsplit j.val (by omega) hij.symm)
      · simp only [bfsBranchPath, if_neg hip, if_neg hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlv _ (by omega), hlv _ (by omega)] at hd
        omega
  · intro i
    have hi := i.isLt
    by_cases hbefore : i.val < p
    · have h := bfsAncestor_adjacent hu (show i.val < G.dist root u by omega)
      simpa only [bfsBranchPath, Fin.val_castSucc, Fin.val_succ,
        if_pos (show i.val ≤ p by omega), if_pos (show i.val + 1 ≤ p by omega)] using h
    · by_cases heq : i.val = p
      · have h := (bfsAncestor_adjacent hv (show p - 1 < G.dist root v by omega)).symm
        have hpone : p - 1 + 1 = p := by omega
        have hnext : 2 * p - (p + 1) = p - 1 := by omega
        simp only [hpone] at h
        simpa only [bfsBranchPath, Fin.val_castSucc, Fin.val_succ, heq,
          if_pos (show p ≤ p by omega), if_neg (show ¬ p + 1 ≤ p by omega),
          hnext, hcommon] using h
      · have h := (bfsAncestor_adjacent hv
          (show 2 * p - (i.val + 1) < G.dist root v by omega)).symm
        have hprev : 2 * p - (i.val + 1) + 1 = 2 * p - i.val := by omega
        simpa only [bfsBranchPath, Fin.val_castSucc, Fin.val_succ,
          if_neg (show ¬ i.val ≤ p by omega),
          if_neg (show ¬ i.val + 1 ≤ p by omega), hprev] using h
theorem bfsBranchPath_internal_level {V : Type*} {G : SimpleGraph V} {root u v : V}
    {p d : ℕ} (hu : G.Reachable root u) (hv : G.Reachable root v)
    (hdu : G.dist root u = d) (hdv : G.dist root v = d) (hp : p ≤ d)
    (i : Fin (2 * p + 1)) (hi : 0 < i.val) (hilast : i.val < 2 * p) :
    G.dist root (bfsBranchPath G root u v p i) < d := by
  by_cases hip : i.val ≤ p
  · have h := (bfsAncestor_level hu i.val (by omega)).2
    simp only [bfsBranchPath, if_pos hip]
    rw [h, hdu]
    omega
  · have h := (bfsAncestor_level hv (2 * p - i.val) (by omega)).2
    simp only [bfsBranchPath, if_neg hip]
    rw [h, hdv]
    omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem exists_longest_path_in {V : Type*} [Fintype V]
    (H : SimpleGraph V) (U : Finset V) {x : V} (hx : x ∈ U) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath H f ∧ f 0 = x ∧
      (∀ i, f i ∈ U) ∧
      ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
        (∀ i, g i ∈ U) → q ≤ r := by
  classical
  let K := H.induce (U : Set V)
  let x' : (U : Set V) := ⟨x, hx⟩
  obtain ⟨r, f, hf, hstart, hmax⟩ := exists_longest_path_from K x'
  refine ⟨r, fun i => (f i).val, ⟨Subtype.val_injective.comp hf.1, hf.2⟩,
    congrArg Subtype.val hstart, fun i => (f i).property, ?_⟩
  intro q g hg hgs hgU
  let g' : Fin (q + 1) → (U : Set V) := fun i => ⟨g i, hgU i⟩
  have hg' : IsIndexedPath K g' :=
    ⟨fun a b h => hg.1 (congrArg Subtype.val h), hg.2⟩
  exact hmax q g' hg' (Subtype.ext hgs)
theorem restricted_endpoint_neighbors {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U W : Finset V} {x e : V} {r : ℕ}
    (hWU : W ⊆ U)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r)
    (he : e ∈ pathEnds H x W r) :
    ∀ v ∈ U, H.Adj e v → v ∈ W := by
  intro v hvU hev
  obtain ⟨f, hf, hlast⟩ := mem_pathEnds.mp he
  by_contra hvW
  have hnotrange : v ∉ Set.range f := by
    rw [hf.2.2.2]
    exact hvW
  have hp := indexedPath_snoc ⟨hf.1, hf.2.1⟩ hnotrange (by simpa [hlast] using hev)
  have hU : ∀ i : Fin (r + 1 + 1), (Fin.snoc f v : Fin (r + 1 + 1) → V) i ∈ U := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hvU
    · rw [Fin.snoc_castSucc]
      apply hWU
      change f j ∈ (W : Set V)
      rw [← hf.2.2.2]
      exact ⟨j, rfl⟩
  have h := hmax (r + 1) (Fin.snoc f v) hp (by simpa using hf.2.2.1) hU
  omega
theorem restricted_endpoint_neighbor_cover {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U W : Finset V} {x y z : V} {r : ℕ}
    (hWU : W ⊆ U)
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r) :
    ∀ e ∈ pathEnds H x W r, ∀ v, H.Adj e v → v ∈ W ∨ v = y ∨ v = z := by
  intro e he v hev
  rcases hcover e (hWU (pathEnds_subset H x W r he)) v hev with hvU | hvy | hvz
  · exact Or.inl (restricted_endpoint_neighbors hWU hmax he v hvU hev)
  · exact Or.inr (Or.inl hvy)
  · exact Or.inr (Or.inr hvz)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem endpoint_neighbor_card_le {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x e : V} {W S : Finset V} {r : ℕ}
    (he : e ∈ pathEnds H x W r)
    (hS : ∀ v ∈ S, H.Adj e v ∧ v ∈ W) : S.card ≤ (pathEnds H x W r).card := by
  classical
  obtain ⟨f, hf, hlast⟩ := mem_pathEnds.mp he
  have hex : ∀ v : S, ∃ i : Fin r, f i.castSucc = v.val := by
    intro v
    obtain ⟨hadj, hvW⟩ := hS v.val v.property
    have hv : v.val ∈ Set.range f := by rw [hf.2.2.2]; exact hvW
    obtain ⟨j, hj⟩ := hv
    have hjlt : j.val < r := by
      have hneq : j ≠ Fin.last r := by
        intro heq
        subst j
        exact hadj.ne (hlast.symm.trans hj)
      have hval : j.val ≠ r := fun h => hneq (Fin.ext h)
      omega
    exact ⟨⟨j.val, hjlt⟩, by simpa using hj⟩
  let pivot : S → Fin r := fun v => Classical.choose (hex v)
  have hpivot : ∀ v : S, f (pivot v).castSucc = v.val := fun v => Classical.choose_spec (hex v)
  let suc : S → pathEnds H x W r := fun v =>
    ⟨f (pivot v).succ, successor_mem_pathEnds hf (pivot v) (by
      rw [hlast, hpivot]
      exact (hS v.val v.property).1)⟩
  have hinj : Function.Injective suc := by
    intro a b hab
    have hfin := hf.1 (congrArg Subtype.val hab)
    have hp : pivot a = pivot b := Fin.succ_injective r hfin
    apply Subtype.ext
    rw [← hpivot a, ← hpivot b, hp]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective suc hinj
theorem endpoint_degree_le_card_add_two {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x e y z : V} {W : Finset V} {r : ℕ}
    (he : e ∈ pathEnds H x W r)
    (hcover : ∀ v, H.Adj e v → v ∈ W ∨ v = y ∨ v = z) :
    (H.neighborSet e).ncard ≤ (pathEnds H x W r).card + 2 := by
  classical
  let S := (H.neighborFinset e).filter fun v => v ∈ W
  have hS : ∀ v ∈ S, H.Adj e v ∧ v ∈ W := by
    intro v hv
    exact ⟨(H.mem_neighborFinset e v).mp (Finset.mem_filter.mp hv).1,
      (Finset.mem_filter.mp hv).2⟩
  have hSbound := endpoint_neighbor_card_le he hS
  have hsub : H.neighborFinset e ⊆ S ∪ {y, z} := by
    intro v hv
    rcases hcover v ((H.mem_neighborFinset e v).mp hv) with hvW | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hvW⟩)
    · simp
    · simp
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le S {y, z})
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hdegree : (H.neighborFinset e).card ≤ (pathEnds H x W r).card + 2 := by omega
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hdegree
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem successor_closed_final_segment {r : ℕ} (P : Fin (r + 1) → Prop)
    (hzero : ¬ P 0) (hlast : P (Fin.last r))
    (hnext : ∀ i : Fin r, P i.castSucc → P i.succ) :
    ∃ t : Fin r, ∀ i : Fin (r + 1), P i ↔ t.val < i.val := by
  classical
  let A : Finset (Fin (r + 1)) := Finset.univ.filter P
  have hA : A.Nonempty := ⟨Fin.last r, by simpa [A] using hlast⟩
  let a := A.min' hA
  have ha : P a := (Finset.mem_filter.mp (A.min'_mem hA)).2
  have hapos : 1 ≤ a.val := by
    by_contra hn
    have heq : a = 0 := by
      apply Fin.ext
      simpa only [Fin.val_zero] using (show a.val = 0 by omega)
    exact hzero (heq ▸ ha)
  have hmin : ∀ i, P i → a.val ≤ i.val := by
    intro i hi
    exact Finset.min'_le A i (by simpa [A] using hi)
  have hup : ∀ j, ∀ hj : j < r + 1, a.val ≤ j → P ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj hle; omega
    | succ j ih =>
      intro hj hle
      by_cases heq : a.val = j + 1
      · have heq' : a = ⟨j + 1, hj⟩ := Fin.ext heq
        exact heq' ▸ ha
      · have hjr : j < r := by omega
        have hprev := ih (by omega) (by omega)
        exact hnext ⟨j, hjr⟩ hprev
  refine ⟨⟨a.val - 1, by have := a.isLt; omega⟩, ?_⟩
  intro i
  constructor
  · intro hi
    have := hmin i hi
    dsimp
    omega
  · intro hi
    apply hup i.val i.isLt
    dsimp at hi
    omega
theorem pathEnds_final_segment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    (hr : 1 ≤ r) {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (hclique : G.IsClique (pathEnds G x W r : Set V)) :
    ∃ t : Fin r, ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val := by
  apply successor_closed_final_segment (fun i => f i ∈ pathEnds G x W r)
  · rw [hf.2.2.1]
    exact start_not_pathEnds hr
  · exact mem_pathEnds.mpr ⟨f, hf, rfl⟩
  · intro i hi
    exact pathEnds_successor_closed hf hclique hi
theorem spanningPath_permute_tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W E : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (t : Fin r) (hfinal : ∀ i : Fin (r + 1), f i ∈ E ↔ t.val < i.val)
    (hclique : G.IsClique (E : Set V)) (σ : Equiv.Perm (Fin (r + 1)))
    (hfix : ∀ i : Fin (r + 1), i.val ≤ t.val + 1 → σ i = i) :
    IsSpanningPath G x W (f ∘ σ) := by
  have htail : ∀ i : Fin (r + 1), t.val < i.val → t.val < (σ i).val := by
    intro i hi
    by_contra hn
    have hs : σ (σ i) = σ i := hfix (σ i) (by omega)
    have heq : i = σ i := σ.injective hs.symm
    have hv := congrArg Fin.val heq
    omega
  refine ⟨hf.1.comp σ.injective, ?_, ?_, ?_⟩
  · intro i
    change G.Adj (f (σ i.castSucc)) (f (σ i.succ))
    by_cases hbefore : i.val ≤ t.val
    · rw [hfix i.castSucc (by change i.val ≤ t.val + 1; omega),
        hfix i.succ (by change i.val + 1 ≤ t.val + 1; omega)]
      exact hf.2.1 i
    · apply hclique ((hfinal _).mpr (htail _ (by simpa using (by omega : t.val < i.val))))
        ((hfinal _).mpr (htail _ (by simp; omega)))
      intro heq
      have hidx := σ.injective (hf.1 heq)
      have hv := congrArg Fin.val hidx
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
  · change f (σ 0) = x
    rw [hfix 0 (by simp)]
    exact hf.2.2.1
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      rw [← hf.2.2.2]
      exact ⟨σ i, rfl⟩
    · intro hv
      rw [← hf.2.2.2] at hv
      obtain ⟨i, rfl⟩ := hv
      exact ⟨σ.symm i, by simp⟩
theorem spanningPath_swap_tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W E : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (t : Fin r) (hfinal : ∀ i : Fin (r + 1), f i ∈ E ↔ t.val < i.val)
    (hclique : G.IsClique (E : Set V)) (i : Fin (r + 1))
    (hi : t.val + 1 < i.val) :
    ∃ g : Fin (r + 1) → V, IsSpanningPath G x W g ∧
      g (Fin.last r) = f i ∧
      ∀ j : Fin (r + 1), j.val ≤ t.val + 1 → g j = f j := by
  classical
  let σ := Equiv.swap i (Fin.last r)
  have hfix : ∀ j : Fin (r + 1), j.val ≤ t.val + 1 → σ j = j := by
    intro j hj
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have := congrArg Fin.val h
      omega
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      have := i.isLt
      omega
  exact ⟨f ∘ σ, spanningPath_permute_tail hf t hfinal hclique σ hfix,
    by simp [σ], fun j hj => congrArg f (hfix j hj)⟩
theorem partial_endpoint_attachment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f)
    (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    (hneighbors : ∀ e ∈ pathEnds G x W r, ∀ v, G.Adj e v → v ∈ W) :
    ∀ w ∈ pathEnds G x W r, w ≠ f t.succ →
      ∀ v, G.Adj w v → v ∈ pathEnds G x W r ∨ v = f t.castSucc := by
  intro w hw hwfirst v hwv
  have hwW : w ∈ (W : Set V) := pathEnds_subset G x W r hw
  rw [← hf.2.2.2] at hwW
  obtain ⟨i, hiw⟩ := hwW
  have hitail : t.val < i.val := (hfinal i).mp (hiw ▸ hw)
  have hi : t.val + 1 < i.val := by
    have hneq : i ≠ t.succ := fun h => hwfirst (hiw.symm.trans (congrArg f h))
    have hval : i.val ≠ t.val + 1 := fun h => hneq (Fin.ext h)
    omega
  obtain ⟨g, hg, hglast, hgfix⟩ := spanningPath_swap_tail hf t hfinal hclique i hi
  by_cases hv : v ∈ pathEnds G x W r
  · exact Or.inl hv
  · right
    have hvW : v ∈ (W : Set V) := hneighbors w hw v hwv
    rw [← hf.2.2.2] at hvW
    obtain ⟨j, hjv⟩ := hvW
    have hjbefore : j.val ≤ t.val := by
      by_contra hn
      exact hv (hjv ▸ (hfinal j).mpr (by omega))
    by_cases heq : j.val = t.val
    · have hj : j = t.castSucc := Fin.ext heq
      exact hjv.symm.trans (congrArg f hj)
    · let p : Fin r := ⟨j.val, by have := t.isLt; omega⟩
      have hgp : g p.castSucc = v := (hgfix p.castSucc (by dsimp [p]; omega)).trans
        ((congrArg f (Fin.ext rfl)).trans hjv)
      have hrot := successor_mem_pathEnds hg p (by rw [hglast, hiw, hgp]; exact hwv)
      rw [hgfix p.succ (by dsimp [p]; omega)] at hrot
      have hbound := (hfinal p.succ).mp hrot
      dsimp [p] at hbound
      omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem degree_le_of_neighbor_cover {V : Type*} [Fintype V]
    {H : SimpleGraph V} {v : V} {S : Finset V}
    (hcover : ∀ w, H.Adj v w → w ∈ S) : (H.neighborSet v).ncard ≤ S.card := by
  classical
  have hsub : H.neighborFinset v ⊆ S := fun w hw =>
    hcover w ((H.mem_neighborFinset v w).mp hw)
  simpa only [SimpleGraph.ncard_neighborSet,
    SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card hsub
theorem degree_cover_forces_neighbor {V : Type*} [Fintype V]
    {H : SimpleGraph V} {v w : V} {S : Finset V}
    (hcover : ∀ a, H.Adj v a → a ∈ S)
    (hdegree : S.card ≤ (H.neighborSet v).ncard) (hw : w ∈ S) : H.Adj v w := by
  classical
  have hsub : H.neighborFinset v ⊆ S := fun a ha =>
    hcover a ((H.mem_neighborFinset v a).mp ha)
  have hcard : S.card ≤ (H.neighborFinset v).card := by
    simpa only [SimpleGraph.ncard_neighborSet,
      SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  exact (H.mem_neighborFinset v w).mp (heq.symm ▸ hw)
theorem clique_extension_size {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u : V}
    (hclique : H.IsClique (E : Set V)) (hu : u ∉ E)
    (hadj : ∀ w ∈ E, H.Adj u w) : E.card + 1 ≤ H.cliqueNum := by
  have hQ : H.IsClique ((insert u E : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hclique.insert (fun w hw _ => hadj w hw)
  have h := hQ.card_le_cliqueNum
  simpa only [Finset.card_insert_of_notMem hu] using h
private theorem erased_pair_cover_card {V : Type*} [DecidableEq V]
    {E : Finset V} {w y z : V} (hw : w ∈ E) :
    ((E.erase w) ∪ {y, z}).card ≤ E.card + 1 := by
  have h := Finset.card_union_le (E.erase w) {y, z}
  have he := Finset.card_erase_add_one hw
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  omega
theorem endpoint_second_attachment {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u w₀ y z : V} {s : ℕ}
    (hs : 4 ≤ s) (hsize : s - 2 ≤ E.card ∧ E.card ≤ s - 1)
    (hclique : H.IsClique (E : Set V)) (hno : H.cliqueNum < s)
    (hy : y ∉ E) (hz : z ∉ E) (hw₀ : w₀ ∈ E)
    (hdegree : ∀ w ∈ E, s ≤ (H.neighborSet w).ncard)
    (hpartial : ∀ w ∈ E, w ≠ w₀ → ∀ v, H.Adj w v →
      v ∈ (E.erase w) ∪ {u, y, z})
    (hzero : ¬ H.Adj w₀ y → ¬ H.Adj w₀ z → (H.neighborSet w₀).ncard ≤ E.card) :
    ∃ w ∈ E, w ≠ w₀ ∧ H.Adj u w := by
  classical
  by_contra hn
  have hnotu : ∀ w ∈ E, w ≠ w₀ → ¬ H.Adj w u := by
    intro w hw hne hwu
    exact hn ⟨w, hw, hne, hwu.symm⟩
  have hcover : ∀ w ∈ E, w ≠ w₀ → ∀ v, H.Adj w v →
      v ∈ (E.erase w) ∪ {y, z} := by
    intro w hw hne v hwv
    rcases Finset.mem_union.mp (hpartial w hw hne v hwv) with hv | hv
    · exact Finset.mem_union_left _ hv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact False.elim (hnotu w hw hne hwv)
      · simp
      · simp
  by_cases hsmall : E.card = s - 2
  · obtain ⟨w, hw, hne⟩ := Finset.exists_mem_ne (by omega : 1 < E.card) w₀
    have hbound := degree_le_of_neighbor_cover (hcover w hw hne)
    have hcard := erased_pair_cover_card (y := y) (z := z) hw
    have hlow := hdegree w hw
    omega
  · have hlarge : E.card = s - 1 := by omega
    have hboth : ∀ w ∈ E, w ≠ w₀ → H.Adj w y ∧ H.Adj w z := by
      intro w hw hne
      have hc := erased_pair_cover_card (y := y) (z := z) hw
      have hd := hdegree w hw
      have hforce : ∀ a ∈ (E.erase w) ∪ {y, z}, H.Adj w a := fun a ha =>
        degree_cover_forces_neighbor (hcover w hw hne)
          (show ((E.erase w) ∪ {y, z}).card ≤ (H.neighborSet w).ncard by omega) ha
      exact ⟨hforce y (by simp), hforce z (by simp)⟩
    have hsome : H.Adj w₀ y ∨ H.Adj w₀ z := by
      by_contra hn
      have hny : ¬ H.Adj w₀ y := fun h => hn (Or.inl h)
      have hnz : ¬ H.Adj w₀ z := fun h => hn (Or.inr h)
      have h := hzero hny hnz
      have h' := hdegree w₀ hw₀
      omega
    rcases hsome with hwy | hwz
    · have hadj : ∀ w ∈ E, H.Adj y w := by
        intro w hw
        by_cases heq : w = w₀
        · subst w; exact hwy.symm
        · exact (hboth w hw heq).1.symm
      have h := clique_extension_size hclique hy hadj
      omega
    · have hadj : ∀ w ∈ E, H.Adj z w := by
        intro w hw
        by_cases heq : w = w₀
        · subst w; exact hwz.symm
        · exact (hboth w hw heq).2.symm
      have h := clique_extension_size hclique hz hadj
      omega
theorem endpoint_common_deleted_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u y z : V} {s : ℕ}
    (hs : 4 ≤ s) (hsize : s - 2 ≤ E.card ∧ E.card ≤ s - 1)
    (hclique : H.IsClique (E : Set V)) (hno : H.cliqueNum < s) (hu : u ∉ E)
    (hdegree : ∀ w ∈ E, s ≤ (H.neighborSet w).ncard)
    (hcover : ∀ w ∈ E, ∀ v, H.Adj w v → v ∈ (E.erase w) ∪ {u, y, z}) :
    ∃ w ∈ E, H.Adj w y ∧ H.Adj w z := by
  classical
  by_cases hsmall : E.card = s - 2
  · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
    have hc := Finset.card_union_le (E.erase w) {u, y, z}
    have he := Finset.card_erase_add_one hw
    have ht : ({u, y, z} : Finset V).card ≤ 3 := Finset.card_le_three
    have hd := hdegree w hw
    have hforce : ∀ a ∈ (E.erase w) ∪ {u, y, z}, H.Adj w a := fun a ha =>
      degree_cover_forces_neighbor (hcover w hw)
        (show ((E.erase w) ∪ {u, y, z}).card ≤ (H.neighborSet w).ncard by omega) ha
    exact ⟨w, hw, hforce y (by simp), hforce z (by simp)⟩
  · have hlarge : E.card = s - 1 := by omega
    by_contra hn
    have hadju : ∀ w ∈ E, H.Adj u w := by
      intro w hw
      by_contra hnu
      have hnotu : ¬ H.Adj w u := fun h => hnu h.symm
      have hpair : ¬ H.Adj w y ∨ ¬ H.Adj w z := by
        by_cases hwy : H.Adj w y
        · exact Or.inr (fun hwz => hn ⟨w, hw, hwy, hwz⟩)
        · exact Or.inl hwy
      have hbound : (H.neighborSet w).ncard ≤ E.card := by
        rcases hpair with hny | hnz
        · have hsub : ∀ v, H.Adj w v → v ∈ insert z (E.erase w) := by
            intro v hwv
            rcases Finset.mem_union.mp (hcover w hw v hwv) with hv | hv
            · exact Finset.mem_insert_of_mem hv
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl | rfl
              · exact False.elim (hnotu hwv)
              · exact False.elim (hny hwv)
              · simp
          have h := degree_le_of_neighbor_cover hsub
          have hc := Finset.card_insert_le z (E.erase w)
          have he := Finset.card_erase_add_one hw
          omega
        · have hsub : ∀ v, H.Adj w v → v ∈ insert y (E.erase w) := by
            intro v hwv
            rcases Finset.mem_union.mp (hcover w hw v hwv) with hv | hv
            · exact Finset.mem_insert_of_mem hv
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl | rfl
              · exact False.elim (hnotu hwv)
              · simp
              · exact False.elim (hnz hwv)
          have h := degree_le_of_neighbor_cover hsub
          have hc := Finset.card_insert_le y (E.erase w)
          have he := Finset.card_erase_add_one hw
          omega
      have hlow := hdegree w hw
      omega
    have h := clique_extension_size hclique hu hadju
    omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem spanningPath_first_tail_last {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    {w : V} (hw : w ∈ pathEnds G x W r) (hne : w ≠ f t.succ)
    (hadj : G.Adj (f t.castSucc) w) :
    ∃ g : Fin (r + 1) → V, IsSpanningPath G x W g ∧
      g (Fin.last r) = f t.succ ∧
      ∀ j : Fin (r + 1), j.val ≤ t.val → g j = f j := by
  have hwW : w ∈ (W : Set V) := pathEnds_subset G x W r hw
  rw [← hf.2.2.2] at hwW
  obtain ⟨i, hiw⟩ := hwW
  have hitail : t.val < i.val := (hfinal i).mp (hiw ▸ hw)
  have hi : t.val + 1 < i.val := by
    have hneq : i ≠ t.succ := fun h => hne (hiw.symm.trans (congrArg f h))
    have hval : i.val ≠ t.val + 1 := fun h => hneq (Fin.ext h)
    omega
  obtain ⟨g, hg, hglast, hgfix⟩ := spanningPath_swap_tail hf t hfinal hclique i hi
  have hrot := rotate_path g hg.1 hg.2.1 t (by
    rw [hglast, hiw, hgfix t.castSucc (by simp)]
    exact hadj.symm)
  refine ⟨g ∘ rotationIndex t, ⟨hrot.1, hrot.2.1,
    hrot.2.2.1.trans hg.2.2.1, hrot.2.2.2.2.trans hg.2.2.2⟩,
    hrot.2.2.2.1.trans (hgfix t.succ (by simp)), ?_⟩
  intro j hj
  have hidx : rotationIndex t j = j := by
    apply Fin.ext
    dsimp [rotationIndex]
    split_ifs
    omega
  change g (rotationIndex t j) = f j
  rw [hidx]
  exact hgfix j (by omega)
theorem endpoint_attachment_of_prefix_preserved {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x w : V} {W : Finset V} {r : ℕ}
    {f g : Fin (r + 1) → V} (hf : IsSpanningPath G x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hg : IsSpanningPath G x W g) (hglast : g (Fin.last r) = w)
    (hfix : ∀ j : Fin (r + 1), j.val ≤ t.val → g j = f j)
    (hneighbors : ∀ v, G.Adj w v → v ∈ W) :
    ∀ v, G.Adj w v → v ∈ pathEnds G x W r ∨ v = f t.castSucc := by
  intro v hwv
  by_cases hv : v ∈ pathEnds G x W r
  · exact Or.inl hv
  · right
    have hvW : v ∈ (W : Set V) := hneighbors v hwv
    rw [← hf.2.2.2] at hvW
    obtain ⟨j, hjv⟩ := hvW
    have hjbefore : j.val ≤ t.val := by
      by_contra hn
      exact hv (hjv ▸ (hfinal j).mpr (by omega))
    by_cases heq : j.val = t.val
    · have hj : j = t.castSucc := Fin.ext heq
      exact hjv.symm.trans (congrArg f hj)
    · let p : Fin r := ⟨j.val, by have := t.isLt; omega⟩
      have hgp : g p.castSucc = v := (hfix p.castSucc (by dsimp [p]; omega)).trans
        ((congrArg f (Fin.ext rfl)).trans hjv)
      have hrot := successor_mem_pathEnds hg p (by rw [hglast, hgp]; exact hwv)
      rw [hfix p.succ (by dsimp [p]; omega)] at hrot
      have hbound := (hfinal p.succ).mp hrot
      dsimp [p] at hbound
      omega
theorem full_endpoint_attachment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {x : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath G x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds G x W r ↔ t.val < i.val)
    (hclique : G.IsClique (pathEnds G x W r : Set V))
    (hneighbors : ∀ e ∈ pathEnds G x W r, ∀ v, G.Adj e v → v ∈ W)
    (hsecond : ∃ w ∈ pathEnds G x W r,
      w ≠ f t.succ ∧ G.Adj (f t.castSucc) w) :
    ∀ w ∈ pathEnds G x W r, ∀ v, G.Adj w v →
      v ∈ pathEnds G x W r ∨ v = f t.castSucc := by
  intro w hw
  by_cases heq : w = f t.succ
  · subst w
    obtain ⟨w₁, hw₁, hne, hadj⟩ := hsecond
    obtain ⟨g, hg, hlast, hfix⟩ := spanningPath_first_tail_last hf t hfinal hclique hw₁ hne hadj
    exact endpoint_attachment_of_prefix_preserved hf t hfinal hg hlast hfix
      (hneighbors _ hw)
  · exact partial_endpoint_attachment hf t hfinal hclique hneighbors w hw heq
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem endpoint_attachment_vertex_of_prefix_preserved {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x w v : V} {W : Finset V} {r : ℕ}
    {f g : Fin (r + 1) → V} (hf : IsSpanningPath H x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds H x W r ↔ t.val < i.val)
    (hg : IsSpanningPath H x W g) (hglast : g (Fin.last r) = w)
    (hfix : ∀ j : Fin (r + 1), j.val ≤ t.val → g j = f j)
    (hvW : v ∈ W) (hwv : H.Adj w v) :
    v ∈ pathEnds H x W r ∨ v = f t.castSucc := by
  by_cases hv : v ∈ pathEnds H x W r
  · exact Or.inl hv
  · right
    have hvW' : v ∈ (W : Set V) := hvW
    rw [← hf.2.2.2] at hvW'
    obtain ⟨j, hjv⟩ := hvW'
    have hjbefore : j.val ≤ t.val := by
      by_contra hn
      exact hv (hjv ▸ (hfinal j).mpr (by omega))
    by_cases heq : j.val = t.val
    · have hj : j = t.castSucc := Fin.ext heq
      exact hjv.symm.trans (congrArg f hj)
    · let p : Fin r := ⟨j.val, by have := t.isLt; omega⟩
      have hgp : g p.castSucc = v := (hfix p.castSucc (by dsimp [p]; omega)).trans
        ((congrArg f (Fin.ext rfl)).trans hjv)
      have hrot := successor_mem_pathEnds hg p (by rw [hglast, hgp]; exact hwv)
      rw [hfix p.succ (by dsimp [p]; omega)] at hrot
      have hbound := (hfinal p.succ).mp hrot
      dsimp [p] at hbound
      omega
theorem partial_endpoint_attachment_in_W {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x w v : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath H x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds H x W r ↔ t.val < i.val)
    (hclique : H.IsClique (pathEnds H x W r : Set V))
    (hw : w ∈ pathEnds H x W r) (hne : w ≠ f t.succ)
    (hvW : v ∈ W) (hwv : H.Adj w v) :
    v ∈ pathEnds H x W r ∨ v = f t.castSucc := by
  have hwW : w ∈ (W : Set V) := pathEnds_subset H x W r hw
  rw [← hf.2.2.2] at hwW
  obtain ⟨i, hiw⟩ := hwW
  have hitail : t.val < i.val := (hfinal i).mp (hiw ▸ hw)
  have hi : t.val + 1 < i.val := by
    have hneq : i ≠ t.succ := fun h => hne (hiw.symm.trans (congrArg f h))
    have hval : i.val ≠ t.val + 1 := fun h => hneq (Fin.ext h)
    omega
  obtain ⟨g, hg, hlast, hfix⟩ := spanningPath_swap_tail hf t hfinal hclique i hi
  apply endpoint_attachment_vertex_of_prefix_preserved hf t hfinal hg (hlast.trans hiw)
    (fun j hj => hfix j (by omega)) hvW hwv
theorem full_endpoint_attachment_in_W {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x w v : V} {W : Finset V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsSpanningPath H x W f) (t : Fin r)
    (hfinal : ∀ i : Fin (r + 1), f i ∈ pathEnds H x W r ↔ t.val < i.val)
    (hclique : H.IsClique (pathEnds H x W r : Set V))
    (hsecond : ∃ w ∈ pathEnds H x W r,
      w ≠ f t.succ ∧ H.Adj (f t.castSucc) w)
    (hw : w ∈ pathEnds H x W r) (hvW : v ∈ W) (hwv : H.Adj w v) :
    v ∈ pathEnds H x W r ∨ v = f t.castSucc := by
  by_cases heq : w = f t.succ
  · subst w
    obtain ⟨w₁, hw₁, hne, hadj⟩ := hsecond
    obtain ⟨g, hg, hlast, hfix⟩ := spanningPath_first_tail_last hf t hfinal hclique hw₁ hne hadj
    exact endpoint_attachment_vertex_of_prefix_preserved hf t hfinal hg hlast hfix hvW hwv
  · exact partial_endpoint_attachment_in_W hf t hfinal hclique hw heq hvW hwv
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem endpoint_structure {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U W : Finset V} {x y z : V} {r s : ℕ}
    (hs : 4 ≤ s) (hno : H.cliqueNum < s)
    (hdegree : ∀ v, s ≤ (H.neighborSet v).ncard)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).card)
    (hyU : y ∉ U) (hzU : z ∉ U) (hWU : W ⊆ U)
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    {f : Fin (r + 1) → V} (hf : IsSpanningPath H x W f)
    (hcard : W.card = r + 1) (hshort : W.card + 2 < 2 * s)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r) :
    let E := pathEnds H x W r
    H.IsClique (E : Set V) ∧ s - 2 ≤ E.card ∧ E.card ≤ s - 1 ∧
      ∃ u ∈ U, u ∉ E ∧
        (∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ H.Adj a u ∧ H.Adj b u) ∧
        (∀ e ∈ E, ∀ v, H.Adj e v → v ∈ E ∨ v = u ∨ v = y ∨ v = z) ∧
        ∃ w ∈ E, H.Adj w y ∧ H.Adj w z := by
  classical
  let E := pathEnds H x W r
  have hEW : E ⊆ W := pathEnds_subset H x W r
  have hEU : E ⊆ U := hEW.trans hWU
  have hyE : y ∉ E := fun hy => hyU (hEU hy)
  have hzE : z ∉ E := fun hz => hzU (hEU hz)
  have he : f (Fin.last r) ∈ E := mem_pathEnds.mpr ⟨f, hf, rfl⟩
  have hcoverE : ∀ e ∈ E, ∀ v, H.Adj e v → v ∈ W ∨ v = y ∨ v = z :=
    restricted_endpoint_neighbor_cover hWU hcover hmax
  have hclique : H.IsClique (E : Set V) := by
    apply clique_of_endpoint_neighbor_cover (s := s) hEW
      (Z := {y, z})
    · intro e he v hev
      rcases hcoverE e he v hev with hv | rfl | rfl
      · exact Finset.mem_union_left _ hv
      · simp
      · simp
    · have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
      omega
    · exact hexpand
  have hupper : E.card ≤ s - 1 := by
    have := hclique.card_le_cliqueNum
    omega
  have hlower : s - 2 ≤ E.card := by
    have hbound := endpoint_degree_le_card_add_two he (hcoverE _ he)
    change (H.neighborSet (f (Fin.last r))).ncard ≤ E.card + 2 at hbound
    have hlow := hdegree (f (Fin.last r))
    omega
  have hr : 1 ≤ r := by
    have hbound := Finset.card_le_card hEW
    omega
  obtain ⟨t, hfinal⟩ := pathEnds_final_segment hr hf hclique
  let u := f t.castSucc
  let w₀ := f t.succ
  have huU : u ∈ U := by
    apply hWU
    change f t.castSucc ∈ (W : Set V)
    rw [← hf.2.2.2]
    exact ⟨t.castSucc, rfl⟩
  have huE : u ∉ E := by
    intro hu
    have h := (hfinal t.castSucc).mp hu
    simp only [Fin.val_castSucc] at h
    omega
  have hw₀ : w₀ ∈ E := (hfinal t.succ).mpr (by simp)
  have huw₀ : H.Adj u w₀ := hf.2.1 t
  have hpartial : ∀ e ∈ E, e ≠ w₀ → ∀ v, H.Adj e v →
      v ∈ (E.erase e) ∪ {u, y, z} := by
    intro e he hne v hev
    rcases hcoverE e he v hev with hvW | rfl | rfl
    · rcases partial_endpoint_attachment_in_W hf t hfinal hclique he hne hvW hev with hvE | hveq
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hev.ne.symm, hvE⟩)
      · subst v
        exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · simp
    · simp
  have hzero : ¬ H.Adj w₀ y → ¬ H.Adj w₀ z → (H.neighborSet w₀).ncard ≤ E.card := by
    intro hny hnz
    apply endpoint_degree_le hw₀
    intro v hwv
    rcases hcoverE w₀ hw₀ v hwv with hv | rfl | rfl
    · exact hv
    · exact False.elim (hny hwv)
    · exact False.elim (hnz hwv)
  have hsecond := endpoint_second_attachment hs ⟨hlower, hupper⟩ hclique hno
    hyE hzE hw₀ (fun e _ => hdegree e) hpartial hzero
  have hfull : ∀ e ∈ E, ∀ v, H.Adj e v → v ∈ E ∨ v = u ∨ v = y ∨ v = z := by
    intro e he v hev
    rcases hcoverE e he v hev with hvW | hvy | hvz
    · rcases full_endpoint_attachment_in_W hf t hfinal hclique hsecond he hvW hev with hv | hvu
      · exact Or.inl hv
      · exact Or.inr (Or.inl hvu)
    · exact Or.inr (Or.inr (Or.inl hvy))
    · exact Or.inr (Or.inr (Or.inr hvz))
  have hfull' : ∀ e ∈ E, ∀ v, H.Adj e v → v ∈ (E.erase e) ∪ {u, y, z} := by
    intro e he v hev
    rcases hfull e he v hev with hv | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hev.ne.symm, hv⟩)
    · simp
    · simp
    · simp
  have hcommon := endpoint_common_deleted_neighbor hs ⟨hlower, hupper⟩ hclique hno
    huE (fun e _ => hdegree e) hfull'
  obtain ⟨b, hb, hbne, hub⟩ := hsecond
  exact ⟨hclique, hlower, hupper, u, huU, huE,
    ⟨w₀, hw₀, b, hb, hbne.symm, huw₀.symm, hub.symm⟩, hfull, hcommon⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem deleted_component_neighbor_cover {V : Type*} {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent)
    (u : C) {v : V} (h : H.Adj u.val.val v) :
    v = y ∨ v = z ∨ ∃ w : C, C.toSimpleGraph.Adj u w ∧ w.val.val = v := by
  by_cases hy : v = y
  · exact Or.inl hy
  by_cases hz : v = z
  · exact Or.inr (Or.inl hz)
  let w : {v : V | v ≠ y ∧ v ≠ z} := ⟨v, hy, hz⟩
  have hadj : (H.induce {v | v ≠ y ∧ v ≠ z}).Adj u.val w := h
  have hw := C.mem_supp_of_adj_mem_supp u.property hadj
  exact Or.inr (Or.inr ⟨⟨w, hw⟩, hadj, rfl⟩)
theorem deleted_component_degree_loss {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) (u : C) :
    (H.neighborSet u.val.val).ncard ≤ (C.toSimpleGraph.neighborSet u).ncard + 2 := by
  classical
  let f : C → V := fun v => v.val.val
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact Subtype.ext h
  let N : Finset V := (C.toSimpleGraph.neighborFinset u).map ⟨f, hf⟩
  have hsub : H.neighborFinset u.val.val ⊆ N ∪ {y, z} := by
    intro v hv
    have hadj := (H.mem_neighborFinset u.val.val v).mp hv
    rcases deleted_component_neighbor_cover C u hadj with rfl | rfl | ⟨w, hw, rfl⟩
    · simp
    · simp
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr
        ⟨w, (C.toSimpleGraph.mem_neighborFinset u w).mpr hw, rfl⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le N {y, z})
  have hpair : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hN : N.card = (C.toSimpleGraph.neighborFinset u).card := Finset.card_map _
  rw [hN] at hcard
  have hdegree : (H.neighborFinset u.val.val).card ≤
      (C.toSimpleGraph.neighborFinset u).card + 2 := by omega
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hdegree
theorem deleted_component_min_degree {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V} {s : ℕ}
    (hdegree : ∀ v, s ≤ (H.neighborSet v).ncard)
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    ∀ u : C, s - 2 ≤ (C.toSimpleGraph.neighborSet u).ncard := by
  intro u
  have h := deleted_component_degree_loss C u
  have h' := hdegree u.val.val
  omega
theorem deleted_component_cliqueNum_le {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    C.toSimpleGraph.cliqueNum ≤ H.cliqueNum := by
  exact ((H.induce {v | v ≠ y ∧ v ≠ z}).cliqueNum_induce_le C.supp).trans
    (H.cliqueNum_induce_le _)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def deletedComponentEmbedding {V : Type*} {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) : C ↪ V :=
  ⟨fun v => v.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
noncomputable def componentVertices {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.map (deletedComponentEmbedding C)
@[simp] theorem mem_componentVertices {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z v : V}
    {C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent} :
    v ∈ componentVertices C ↔ ∃ u : C, u.val.val = v := by
  classical
  constructor
  · intro hv
    change v ∈ Finset.univ.map (deletedComponentEmbedding C) at hv
    obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hv
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    change v ∈ Finset.univ.map (deletedComponentEmbedding C)
    exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩
theorem deleted_not_componentVertices {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    y ∉ componentVertices C ∧ z ∉ componentVertices C := by
  constructor
  · rintro hy
    obtain ⟨u, hu⟩ := mem_componentVertices.mp hy
    exact u.val.property.1 hu
  · rintro hz
    obtain ⟨u, hu⟩ := mem_componentVertices.mp hz
    exact u.val.property.2 hu
theorem componentVertices_neighbor_cover {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent)
    {u v : V} (hu : u ∈ componentVertices C) (h : H.Adj u v) :
    v ∈ componentVertices C ∨ v = y ∨ v = z := by
  obtain ⟨u', rfl⟩ := mem_componentVertices.mp hu
  rcases deleted_component_neighbor_cover C u' h with hy | hz | ⟨w, _, hw⟩
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr hz)
  · exact Or.inl (mem_componentVertices.mpr ⟨w, hw⟩)
theorem componentVertices_connected {V : Type*} [Fintype V]
    {H : SimpleGraph V} {y z : V}
    (C : (H.induce {v | v ≠ y ∧ v ≠ z}).ConnectedComponent) :
    (H.induce (componentVertices C : Set V)).Connected := by
  classical
  let f : C → (componentVertices C : Set V) := fun u =>
    ⟨u.val.val, mem_componentVertices.mpr ⟨u, rfl⟩⟩
  let φ : C.toSimpleGraph →g H.induce (componentVertices C : Set V) :=
    { toFun := f, map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro v
    obtain ⟨u, hu⟩ := mem_componentVertices.mp v.property
    exact ⟨u, Subtype.ext hu⟩
  exact C.connected_toSimpleGraph.map φ hsurj
theorem induced_degree_loss_pair {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U : Finset V} {y z : V}
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    (u : (U : Set V)) :
    (H.neighborSet u.val).ncard ≤ ((H.induce (U : Set V)).neighborSet u).ncard + 2 := by
  classical
  let K := H.induce (U : Set V)
  let N : Finset V := (K.neighborFinset u).map ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : H.neighborFinset u.val ⊆ N ∪ {y, z} := by
    intro v hv
    have hadj := (H.mem_neighborFinset u.val v).mp hv
    rcases hcover u.val u.property v hadj with hvU | rfl | rfl
    · let w : (U : Set V) := ⟨v, hvU⟩
      have hw : w ∈ K.neighborFinset u := (K.mem_neighborFinset u w).mpr hadj
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
    · simp
    · simp
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le N {y, z})
  have hpair : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hN : N.card = (K.neighborFinset u).card := Finset.card_map _
  rw [hN] at hcard
  have hdegree : (H.neighborFinset u.val).card ≤ (K.neighborFinset u).card + 2 := by omega
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hdegree
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem not_clique_of_two_deleted_neighborhoods {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U : Finset V} {y z : V} {s : ℕ}
    (hU : U.Nonempty) (hy : y ∉ U) (hno : H.cliqueNum < s)
    (hdegree : ∀ u ∈ U, s ≤ (H.neighborSet u).ncard)
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z) :
    ¬ H.IsClique (U : Set V) := by
  classical
  intro hclique
  have hUbound := hclique.card_le_cliqueNum
  have hcover' : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ (U.erase u) ∪ {y, z} := by
    intro u hu v huv
    rcases hcover u hu v huv with hv | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv.ne.symm, hv⟩)
    · simp
    · simp
  have hcard : ∀ u ∈ U, ((U.erase u) ∪ {y, z}).card ≤ U.card + 1 := by
    intro u hu
    have hc := Finset.card_union_le (U.erase u) {y, z}
    have he := Finset.card_erase_add_one hu
    have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨u, hu⟩ := hU
  have hbound := degree_le_of_neighbor_cover (hcover' u hu)
  have hc := hcard u hu
  have hd := hdegree u hu
  have hsize : U.card + 1 = s := by omega
  have hadj : ∀ v ∈ U, H.Adj y v := by
    intro v hv
    apply SimpleGraph.Adj.symm
    apply degree_cover_forces_neighbor (hcover' v hv)
      (show ((U.erase v) ∪ {y, z}).card ≤ (H.neighborSet v).ncard from
        (hcard v hv).trans (hsize.le.trans (hdegree v hv)))
    simp
  have hlarge := clique_extension_size hclique hy hadj
  omega
theorem two_deleted_component_order {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U : Finset V} {y z : V} {s : ℕ}
    (hnotclique : ¬ H.IsClique (U : Set V))
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).card) :
    2 * s - 2 ≤ U.card := by
  classical
  have hex : ∃ a ∈ U, ∃ b ∈ U, a ≠ b ∧ ¬ H.Adj a b := by
    by_contra hn
    apply hnotclique
    intro a ha b hb hab
    by_contra hnab
    exact hn ⟨a, ha, b, hb, hab, hnab⟩
  obtain ⟨a, ha, b, hb, hab, hnot⟩ := hex
  have hsub : closedNeighborhood H {a, b} ⊆ U ∪ {y, z} := by
    intro v hv
    rcases mem_closedNeighborhood.mp hv with hv | ⟨w, hw, hwv⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_left _ hb
    · have hwU : w ∈ U := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact ha
        · exact hb
      rcases hcover w hwU v hwv with hv | rfl | rfl
      · exact Finset.mem_union_left _ hv
      · simp
      · simp
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le U {y, z})
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hlow := hexpand a b hab hnot
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem connected_outside_single_attachment {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {E : Finset V} {u : V} (hu : u ∉ E)
    (hattach : ∀ e ∈ E, ∀ v, G.Adj e v → v ∉ E → v = u) :
    (G.induce {v | v ∉ E}).Connected := by
  classical
  let f : V → {v : V | v ∉ E} := fun v => if hv : v ∈ E then ⟨u, hu⟩ else ⟨v, hv⟩
  let : Nonempty {v : V | v ∉ E} := ⟨⟨u, hu⟩⟩
  have hedge : ∀ a b, G.Adj a b →
      (G.induce {v | v ∉ E}).Reachable (f a) (f b) := by
    intro a b hab
    by_cases ha : a ∈ E
    · by_cases hb : b ∈ E
      · simp only [f, dif_pos ha, dif_pos hb]
        exact SimpleGraph.Reachable.refl _
      · have heq := hattach a ha b hab hb
        subst b
        simp only [f, dif_pos ha, dif_neg hu]
        exact SimpleGraph.Reachable.refl _
    · by_cases hb : b ∈ E
      · have heq := hattach b hb a hab.symm ha
        subst a
        simp only [f, dif_neg hu, dif_pos hb]
        exact SimpleGraph.Reachable.refl _
      · simp only [f, dif_neg ha, dif_neg hb]
        exact (show (G.induce {v | v ∉ E}).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab).reachable
  have hmap : ∀ a b, G.Reachable a b →
      (G.induce {v | v ∉ E}).Reachable (f a) (f b) := by
    intro a b hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih => exact (hedge a b hab).trans ih
  refine ⟨?_⟩
  intro a b
  have h := hmap a.val b.val (hconn a.val b.val)
  simpa only [f, dif_neg a.property, dif_neg b.property] using h
theorem neighbors_outside_single_attachment {V : Type*} {G : SimpleGraph V}
    {E : Finset V} {u v : V} (hv : v ∉ E) (hvu : v ≠ u)
    (hattach : ∀ e ∈ E, ∀ w, G.Adj e w → w ∉ E → w = u) :
    G.neighborSet v ⊆ {w | w ∉ E} := by
  intro w hvw hw
  exact hvu (hattach w hw v hvw.symm hv)
theorem degree_outside_single_attachment {V : Type*} [Fintype V] {G : SimpleGraph V}
    {E : Finset V} {u : V} (v : {v : V | v ∉ E}) (hvu : v.val ≠ u)
    (hattach : ∀ e ∈ E, ∀ w, G.Adj e w → w ∉ E → w = u) :
    ((G.induce {v | v ∉ E}).neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  classical
  simp only [SimpleGraph.ncard_neighborSet]
  exact G.degree_induce_of_neighborSet_subset
    (neighbors_outside_single_attachment v.property hvu hattach)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem connected_induce_difference_single_attachment {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U E : Finset V} {u : V}
    (hconn : (H.induce (U : Set V)).Connected) (huU : u ∈ U) (huE : u ∉ E)
    (hattach : ∀ e ∈ E, ∀ v ∈ U, H.Adj e v → v ∉ E → v = u) :
    (H.induce {v | v ∈ U ∧ v ∉ E}).Connected := by
  classical
  let K := H.induce (U : Set V)
  let E' : Finset (U : Set V) := Finset.univ.filter fun v => v.val ∈ E
  let u' : (U : Set V) := ⟨u, huU⟩
  have hu' : u' ∉ E' := by simp [E', u', huE]
  have hattach' : ∀ e ∈ E', ∀ v, K.Adj e v → v ∉ E' → v = u' := by
    intro e he v hev hv
    have heE : e.val ∈ E := (Finset.mem_filter.mp he).2
    have hvE : v.val ∉ E := by simpa [E'] using hv
    exact Subtype.ext (hattach e.val heE v.val v.property hev hvE)
  have hc := connected_outside_single_attachment hconn hu' hattach'
  let f : {v : (U : Set V) | v ∉ E'} → {v : V | v ∈ U ∧ v ∉ E} := fun v =>
    ⟨v.val.val, v.val.property, by simpa [E'] using v.property⟩
  let φ : (K.induce {v | v ∉ E'}) →g H.induce {v | v ∈ U ∧ v ∉ E} :=
    { toFun := f, map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro v
    let w : {v : (U : Set V) | v ∉ E'} :=
      ⟨⟨v.val, v.property.1⟩, by simpa [E'] using v.property.2⟩
    exact ⟨w, rfl⟩
  exact hc.map φ hsurj
theorem restricted_longest_nontrivial {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U : Finset V} {x : V} {r : ℕ}
    (hconn : (H.induce (U : Set V)).Connected) (hcard : 2 ≤ U.card) (hx : x ∈ U)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r) : 1 ≤ r := by
  classical
  let K := H.induce (U : Set V)
  let : Nontrivial (U : Set V) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < U.card by omega))
  let x' : (U : Set V) := ⟨x, hx⟩
  have hpos := hconn.preconnected.degree_pos_of_nontrivial x'
  have hcardpos : 0 < (K.neighborFinset x').card := by
    rw [K.card_neighborFinset_eq_degree]
    exact hpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcardpos
  have hadj := (K.mem_neighborFinset x' v).mp hv
  let g : Fin 2 → V := Fin.cons x (fun _ : Fin 1 => v.val)
  have hg : IsIndexedPath H g := by
    refine ⟨?_, ?_⟩
    · apply Fin.cons_injective_iff.mpr
      constructor
      · rintro ⟨i, hi⟩
        exact hadj.ne (Subtype.ext hi.symm)
      · intro i j _
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
    · intro i
      have hi : i = 0 := by apply Fin.ext; have := i.isLt; omega
      subst i
      exact hadj
  have hgU : ∀ i, g i ∈ U := by
    intro i
    refine Fin.cases hx (fun _ => v.property) i
  exact hmax 1 g hg rfl hgU
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem indexedPath_ofFn_chain {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) :
    (List.ofFn f).Nodup ∧ (List.ofFn f).IsChain G.Adj := by
  refine ⟨List.nodup_ofFn.mpr hf.1, List.isChain_ofFn.mpr ?_⟩
  intro i hi
  exact hf.2 ⟨i, by omega⟩
theorem indexedPath_of_list {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : List V) (hL : L.Nodup) (hchain : L.IsChain G.Adj) (hlen : L.length = r + 1) :
    IsIndexedPath G (fun i : Fin (r + 1) => L.get (Fin.cast hlen.symm i)) := by
  refine ⟨hL.injective_get.comp (Fin.cast_injective _), ?_⟩
  intro i
  exact (List.isChain_iff_getElem.mp hchain) i.val (by have := i.isLt; omega)
private theorem chain_of_pairwise551 {V : Type*} {R : V → V → Prop} {L : List V}
    (h : L.Pairwise R) : L.IsChain R := by
  induction h with
  | nil => exact .nil
  | @cons a l hrel _ ih =>
    exact ih.cons (fun b hb => hrel b (List.mem_of_mem_head? hb))
theorem chain_of_clique_nodup {V : Type*} {G : SimpleGraph V} {E : Finset V}
    (hclique : G.IsClique (E : Set V)) {L : List V} (hL : L.Nodup)
    (hmem : ∀ v ∈ L, v ∈ E) : L.IsChain G.Adj := by
  apply chain_of_pairwise551
  exact hL.pairwise_of_forall_ne
    (fun a ha b hb hab => hclique (hmem a ha) (hmem b hb) hab)
theorem exists_clique_traversal {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {E : Finset V} (hclique : G.IsClique (E : Set V))
    {a b : V} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ L.length = E.card ∧
      L.head? = some a ∧ L.getLast? = some b ∧ ∀ v ∈ L, v ∈ E := by
  classical
  let M := ((E.erase a).erase b).toList
  let L := a :: (M ++ [b])
  have hM : ∀ v ∈ M, v ∈ E ∧ v ≠ a ∧ v ≠ b := by
    intro v hv
    have hm : v ∈ (E.erase a).erase b := by simpa [M] using hv
    exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm),
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1,
      (Finset.mem_erase.mp hm).1⟩
  have hL : L.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact (hM a h).2.1 rfl
      · have heq : a = b := by simpa using h
        exact hab heq
    · apply List.nodup_append.mpr
      refine ⟨Finset.nodup_toList _, by simp, ?_⟩
      intro v hv b' hb' heq
      have hb'eq : b' = b := by simpa using hb'
      exact (hM v hv).2.2 (heq.trans hb'eq)
  have hmem : ∀ v ∈ L, v ∈ E := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · rcases List.mem_append.mp hv with hv | hv
      · exact (hM v hv).1
      · have heq : v = b := by simpa using hv
        exact heq ▸ hb
  have hlen : L.length = E.card := by
    have hea := Finset.card_erase_add_one ha
    have hba : b ∈ E.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have heb := Finset.card_erase_add_one hba
    dsimp [L, M]
    simp only [List.length_cons, List.length_append, Finset.length_toList, List.length_nil]
    omega
  exact ⟨L, hL, chain_of_clique_nodup hclique hL hmem, hlen, rfl,
    by
      change ((a :: M) ++ [b]).getLast? = some b
      exact List.getLast?_append_cons (a :: M) b [], hmem⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private theorem color_eq_of_walk {V : Type*} {G : SimpleGraph V} (χ : V → Fin 2)
    (htwo : ∀ {u x v}, G.Adj u x → G.Adj x v → χ u = χ v)
    {u v w : V} (p : G.Walk v w) (huv : G.Adj u v) (heq : χ u = χ v) : χ w = χ v := by
  induction p generalizing u with
  | nil => rfl
  | @cons v z w hvz p ih =>
    have hχ : χ v = χ z := heq.symm.trans (htwo huv hvz)
    exact (ih hvz hχ).trans hχ.symm
theorem differently_colored_common_neighbors {V : Type*} {G : SimpleGraph V}
    (hconnected : G.Connected) (hnonbipartite : ¬ G.IsBipartite)
    (χ : V → Fin 2) (hnonconstant : ∃ u v, χ u ≠ χ v) :
    ∃ x y z, G.Adj x y ∧ G.Adj x z ∧ χ y ≠ χ z := by
  classical
  by_contra hnone
  have htwo : ∀ {u x v}, G.Adj u x → G.Adj x v → χ u = χ v := by
    intro u x v hux hxv
    by_contra hχ
    exact hnone ⟨x, u, v, hux.symm, hxv, hχ⟩
  have hproper : ∀ {u v}, G.Adj u v → χ u ≠ χ v := by
    intro u v huv heq
    have hconstant : ∀ w, χ w = χ v := by
      intro w
      obtain ⟨p⟩ := hconnected v w
      exact color_eq_of_walk χ htwo p huv heq
    obtain ⟨a, b, hab⟩ := hnonconstant
    exact hab ((hconstant a).trans (hconstant b).symm)
  exact hnonbipartite ⟨SimpleGraph.Coloring.mk χ hproper⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem indexedPath_prefix {V : Type*} {G : SimpleGraph V} {q r : ℕ}
    {f : Fin (q + 1) → V} (hf : IsIndexedPath G f) (hrq : r ≤ q) :
    IsIndexedPath G (fun i : Fin (r + 1) => f (Fin.castLE (by omega) i)) := by
  refine ⟨hf.1.comp (Fin.castLE_injective _), ?_⟩
  intro i
  exact hf.2 ⟨i.val, by have := i.isLt; omega⟩
theorem indexedPath_cons {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) {v : V}
    (hv : v ∉ Set.range f) (hadj : G.Adj v (f 0)) :
    IsIndexedPath G (Fin.cons v f) := by
  refine ⟨Fin.cons_injective_iff.mpr ⟨hv, hf.1⟩, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hadj
  · have heq : j.succ.castSucc = j.castSucc.succ := Fin.ext rfl
    rw [heq]
    simpa only [Fin.cons_succ] using hf.2 j
theorem colored_path_of_common_neighbor {V : Type*} {H : SimpleGraph V}
    {x y z : V} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (χ : V → Fin 2) (hyz : χ y ≠ χ z) {q : ℕ}
    {f : Fin (q + 1) → V} (hf : IsIndexedPath H f) (hstart : f 0 = x)
    (havoid : ∀ i, f i ≠ y ∧ f i ≠ z) :
    ∃ g : Fin (q + 1 + 1) → V, IsIndexedPath H g ∧
      χ (g 0) ≠ χ (g (Fin.last (q + 1))) := by
  have hyavoid : y ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact (havoid i).1 hi
  have hzavoid : z ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact (havoid i).2 hi
  by_cases hycol : χ y = χ (f (Fin.last q))
  · refine ⟨Fin.cons z f, indexedPath_cons hf hzavoid (by rw [hstart]; exact hxz.symm), ?_⟩
    simp only [Fin.cons_zero, Fin.cons_last]
    intro hzcol
    exact hyz (hycol.trans hzcol.symm)
  · refine ⟨Fin.cons y f, indexedPath_cons hf hyavoid (by rw [hstart]; exact hxy.symm), ?_⟩
    simpa only [Fin.cons_zero, Fin.cons_last] using hycol
theorem no_colored_path_start_bound {V : Type*} {H : SimpleGraph V}
    {x y z : V} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (χ : V → Fin 2) (hyz : χ y ≠ χ z) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hno : ¬ ∃ g : Fin (ℓ + 1) → V, IsIndexedPath H g ∧
      χ (g 0) ≠ χ (g (Fin.last ℓ)))
    {q : ℕ} {f : Fin (q + 1) → V} (hf : IsIndexedPath H f) (hstart : f 0 = x)
    (havoid : ∀ i, f i ≠ y ∧ f i ≠ z) : q + 1 < ℓ := by
  cases ℓ with
  | zero => omega
  | succ ℓ =>
    by_contra hn
    have hbound : ℓ ≤ q := by omega
    let f' : Fin (ℓ + 1) → V := fun i => f (Fin.castLE (by omega) i)
    have hf' : IsIndexedPath H f' := indexedPath_prefix hf hbound
    have hstart' : f' 0 = x := hstart
    have havoid' : ∀ i, f' i ≠ y ∧ f' i ≠ z := fun i => havoid _
    obtain ⟨g, hg, hcolor⟩ := colored_path_of_common_neighbor hxy hxz χ hyz hf' hstart' havoid'
    exact hno ⟨g, hg, hcolor⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem endpoint_residual_order {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E R : Finset V} {u v w y z : V} {s : ℕ}
    (hu : u ∈ R) (hv : v ∈ R) (hw : w ∈ E)
    (hcoverv : ∀ a, H.Adj v a → a ∈ R ∨ a = y ∨ a = z)
    (hcoverw : ∀ a, H.Adj w a → a ∈ E ∨ a = u ∨ a = y ∨ a = z)
    (hexpand : 2 * s ≤ (closedNeighborhood H {v, w}).card) :
    2 * s - 2 ≤ E.card + R.card := by
  classical
  have hsub : closedNeighborhood H {v, w} ⊆ (R ∪ E) ∪ {y, z} := by
    intro a ha
    rcases mem_closedNeighborhood.mp ha with ha | ⟨b, hb, hba⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · rcases hcoverv a hba with ha | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
        · simp
        · simp
      · rcases hcoverw a hba with ha | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
        · simp
        · simp
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (R ∪ E) {y, z})
  have hRE := Finset.card_union_le R E
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  omega
theorem clique_join_remaining_path {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u w : V}
    (hclique : H.IsClique (E : Set V)) (hw : w ∈ E)
    (hattach : ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ H.Adj a u ∧ H.Adj b u)
    (R : List V) (hR : R.Nodup) (hRchain : R.IsChain H.Adj)
    (hRhead : R.head? = some u) (hRoutside : ∀ v ∈ R, v ∉ E) :
    ∃ L : List V, L.Nodup ∧ L.IsChain H.Adj ∧ L.head? = some w ∧
      L.length = E.card + R.length ∧ ∀ v ∈ L, v ∈ E ∨ v ∈ R := by
  obtain ⟨a, ha, b, hb, hab, hau, hbu⟩ := hattach
  have hex : ∃ b ∈ E, w ≠ b ∧ H.Adj b u := by
    by_cases hwa : w = a
    · exact ⟨b, hb, hwa ▸ hab, hbu⟩
    · exact ⟨a, ha, hwa, hau⟩
  obtain ⟨b', hb', hwb', hb'u⟩ := hex
  obtain ⟨P, hP, hPchain, hPlen, hPhead, hPlast, hPmem⟩ :=
    exists_clique_traversal hclique hw hb' hwb'
  have hnodup : (P ++ R).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hP, hR, ?_⟩
    intro a ha b hb heq
    subst b
    exact hRoutside a hb (hPmem a ha)
  have hchain : (P ++ R).IsChain H.Adj := by
    apply List.isChain_append.mpr
    refine ⟨hPchain, hRchain, ?_⟩
    intro a ha b hb
    have hae : b' = a := by simpa only [hPlast, Option.mem_some_iff] using ha
    have hbe : u = b := by simpa only [hRhead, Option.mem_some_iff] using hb
    exact hae ▸ hbe ▸ hb'u
  refine ⟨P ++ R, hnodup, hchain, ?_, by simp only [List.length_append, hPlen], ?_⟩
  · simp only [List.head?_append, hPhead, Option.some_or]
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact Or.inl (hPmem v hv)
    · exact Or.inr hv
theorem no_colored_path_list_bound {V : Type*} {H : SimpleGraph V}
    {x y z : V} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (χ : V → Fin 2) (hyz : χ y ≠ χ z) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hno : ¬ ∃ g : Fin (ℓ + 1) → V, IsIndexedPath H g ∧
      χ (g 0) ≠ χ (g (Fin.last ℓ)))
    {L : List V} (hL : L.Nodup) (hchain : L.IsChain H.Adj)
    (hhead : L.head? = some x) (havoid : ∀ v ∈ L, v ≠ y ∧ v ≠ z) :
    L.length < ℓ := by
  cases L with
  | nil => simp only [List.length_nil]; omega
  | cons a L =>
    let f : Fin (L.length + 1) → V := (a :: L).get
    have hf : IsIndexedPath H f := indexedPath_of_list (a :: L) hL hchain rfl
    have hstart : f 0 = x := by simpa [f] using hhead
    have havoid' : ∀ i, f i ≠ y ∧ f i ≠ z := fun i => havoid _ (List.get_mem _ _)
    exact no_colored_path_start_bound hxy hxz χ hyz hℓ hno hf hstart havoid'
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private noncomputable def indexedSupport {V : Type*} {r : ℕ}
    (f : Fin (r + 1) → V) : Finset V := by
  classical
  exact Finset.univ.image f
private theorem mem_indexedSupport {V : Type*} {r : ℕ} {f : Fin (r + 1) → V} {v : V} :
    v ∈ indexedSupport f ↔ ∃ i, f i = v := by
  classical
  simp [indexedSupport]
private theorem indexedSupport_range {V : Type*} {r : ℕ} (f : Fin (r + 1) → V) :
    Set.range f = (indexedSupport f : Set V) := by
  ext v
  exact mem_indexedSupport.symm
private theorem indexedSupport_card {V : Type*} {r : ℕ} {f : Fin (r + 1) → V}
    (hf : Function.Injective f) : (indexedSupport f).card = r + 1 := by
  classical
  rw [indexedSupport, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
theorem colored_path_prescribed_length {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {s : ℕ} (hs : 4 ≤ s)
    (hconn : H.Connected) (hnonbip : ¬ H.IsBipartite) (hno : H.cliqueNum < s)
    (hdegree : ∀ v, s ≤ (H.neighborSet v).ncard)
    (hpair : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).card)
    (χ : V → Fin 2) (hnonconstant : ∃ a b, χ a ≠ χ b)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓmax : ℓ ≤ 2 * s - 2) :
    ∃ g : Fin (ℓ + 1) → V, IsIndexedPath H g ∧ χ (g 0) ≠ χ (g (Fin.last ℓ)) := by
  classical
  by_contra hnone
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ :=
    differently_colored_common_neighbors hconn hnonbip χ hnonconstant
  let D := H.induce {v | v ≠ y ∧ v ≠ z}
  let x' : {v : V | v ≠ y ∧ v ≠ z} := ⟨x, hxy.ne, hxz.ne⟩
  let C := D.connectedComponentMk x'
  let U := componentVertices C
  have hxU : x ∈ U := mem_componentVertices.mpr
    ⟨⟨x', SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, rfl⟩
  obtain ⟨hyU, hzU⟩ := deleted_not_componentVertices C
  change y ∉ U at hyU
  change z ∉ U at hzU
  have hUavoid : ∀ a ∈ U, a ≠ y ∧ a ≠ z := fun a ha =>
    ⟨ne_of_mem_of_not_mem ha hyU, ne_of_mem_of_not_mem ha hzU⟩
  have hcoverU : ∀ a ∈ U, ∀ b, H.Adj a b → b ∈ U ∨ b = y ∨ b = z := by
    intro a ha b hab
    exact componentVertices_neighbor_cover C ha hab
  have hUconn : (H.induce (U : Set V)).Connected := componentVertices_connected C
  obtain ⟨r, f, hf, hstart, hfU, hmax⟩ := exists_longest_path_in H U hxU
  let W := indexedSupport f
  have hWcard : W.card = r + 1 := indexedSupport_card hf.1
  have hWU : W ⊆ U := by
    intro v hv
    obtain ⟨i, rfl⟩ := mem_indexedSupport.mp hv
    exact hfU i
  have hspanning : IsSpanningPath H x W f := ⟨hf.1, hf.2, hstart, indexedSupport_range f⟩
  have havoid : ∀ i, f i ≠ y ∧ f i ≠ z := fun i => hUavoid _ (hfU i)
  have hrshort := no_colored_path_start_bound hxy hxz χ hyz hℓ hnone hf hstart havoid
  have hshort : W.card + 2 < 2 * s := by omega
  let E := pathEnds H x W r
  have hstructure := endpoint_structure hs hno hdegree hpair hyU hzU hWU hcoverU
    hspanning hWcard hshort hmax
  obtain ⟨hEclique, hElower, hEupper, u, huU, huE, htwo, hfull, w, hw, hwy, hwz⟩ := hstructure
  change H.IsClique (E : Set V) at hEclique
  change s - 2 ≤ E.card at hElower
  change E.card ≤ s - 1 at hEupper
  change u ∈ U at huU
  change u ∉ E at huE
  change w ∈ E at hw
  have hEU : E ⊆ U := (pathEnds_subset H x W r).trans hWU
  have hattach : ∀ e ∈ E, ∀ v ∈ U, H.Adj e v → v ∉ E → v = u := by
    intro e he v hv hev hvE
    rcases hfull e he v hev with hv' | hvu | rfl | rfl
    · exact False.elim (hvE hv')
    · exact hvu
    · exact False.elim (hyU hv)
    · exact False.elim (hzU hv)
  have hUnotclique := not_clique_of_two_deleted_neighborhoods
    ⟨x, hxU⟩ hyU hno (fun v _ => hdegree v) hcoverU
  have hUorder := two_deleted_component_order hUnotclique hcoverU hpair
  let T := U \ E
  have hTset : (T : Set V) = {v | v ∈ U ∧ v ∉ E} := by ext v; simp [T]
  have hTsum : T.card + E.card = U.card := Finset.card_sdiff_add_card_eq_card hEU
  have hTcard : 2 ≤ T.card := by omega
  have huT : u ∈ T := Finset.mem_sdiff.mpr ⟨huU, huE⟩
  have hTconn : (H.induce (T : Set V)).Connected := by
    rw [hTset]
    exact connected_induce_difference_single_attachment hUconn huU huE hattach
  obtain ⟨q, g, hg, hgstart, hgT, hgmax⟩ := exists_longest_path_in H T huT
  have hq : 1 ≤ q := restricted_longest_nontrivial hTconn hTcard huT hgmax
  let R := indexedSupport g
  let v := g (Fin.last q)
  have hRcard : R.card = q + 1 := indexedSupport_card hg.1
  have hRT : R ⊆ T := by
    intro a ha
    obtain ⟨i, rfl⟩ := mem_indexedSupport.mp ha
    exact hgT i
  have hvR : v ∈ R := mem_indexedSupport.mpr ⟨Fin.last q, rfl⟩
  have huR : u ∈ R := mem_indexedSupport.mpr ⟨0, hgstart⟩
  have hvU : v ∈ U := (Finset.mem_sdiff.mp (hRT hvR)).1
  have hvE : v ∉ E := (Finset.mem_sdiff.mp (hRT hvR)).2
  have hvu : v ≠ u := by
    intro heq
    have hidx := hg.1 (heq.trans hgstart.symm)
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  have hspanningR : IsSpanningPath H u R g :=
    ⟨hg.1, hg.2, hgstart, indexedSupport_range g⟩
  have hvEnd : v ∈ pathEnds H u R q := mem_pathEnds.mpr ⟨g, hspanningR, rfl⟩
  have hcoverv : ∀ a, H.Adj v a → a ∈ R ∨ a = y ∨ a = z := by
    intro a hva
    rcases hcoverU v hvU a hva with haU | hay | haz
    · have haE : a ∉ E := by
        intro ha
        exact hvu (hattach a ha v hvU hva.symm hvE)
      have haT : a ∈ T := Finset.mem_sdiff.mpr ⟨haU, haE⟩
      exact Or.inl (restricted_endpoint_neighbors hRT hgmax hvEnd a haT hva)
    · exact Or.inr (Or.inl hay)
    · exact Or.inr (Or.inr haz)
  have hvw : v ≠ w := (ne_of_mem_of_not_mem hw hvE).symm
  have hnonadj : ¬ H.Adj v w := fun h => hvu (hattach w hw v hvU h.symm hvE)
  have hcombined := endpoint_residual_order huR hvR hw hcoverv (hfull w hw)
    (hpair v w hvw hnonadj)
  change 2 * s - 2 ≤ E.card + R.card at hcombined
  have hRlist := indexedPath_ofFn_chain hg
  have hRhead : (List.ofFn g).head? = some u := by rw [List.ofFn_succ]; simp [hgstart]
  have hRmem : ∀ a ∈ List.ofFn g, a ∈ R := by
    intro a ha
    exact mem_indexedSupport.mpr ((List.mem_ofFn' g a).mp ha)
  have hRoutside : ∀ a ∈ List.ofFn g, a ∉ E := by
    intro a ha
    exact (Finset.mem_sdiff.mp (hRT (hRmem a ha))).2
  obtain ⟨L, hL, hLchain, hLhead, hLlen, hLmem⟩ := clique_join_remaining_path
    hEclique hw htwo (List.ofFn g) hRlist.1 hRlist.2 hRhead hRoutside
  have hLavoid : ∀ a ∈ L, a ≠ y ∧ a ≠ z := by
    intro a ha
    have haU : a ∈ U := by
      rcases hLmem a ha with haE | haR
      · exact hEU haE
      · exact (Finset.mem_sdiff.mp (hRT (hRmem a haR))).1
    exact hUavoid a haU
  have hLshort := no_colored_path_list_bound hwy hwz χ hyz hℓ hnone hL hLchain hLhead hLavoid
  simp only [List.length_ofFn] at hLlen
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem layer_cycle_of_two_branches {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d p s k : ℕ}
    (hs : 4 ≤ s) (hk : 2 * s ≤ k) (hk' : k ≤ 2 * s + 1)
    (hp : 2 ≤ p) (hps : p ≤ s) (hpd : p ≤ d)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d)
    (hconn : (G.induce (Y : Set V)).Connected)
    (hnonbip : ¬ (G.induce (Y : Set V)).IsBipartite)
    (hno : G.cliqueNum < s)
    (hdegree : ∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard)
    (hpair : ∀ a b : Y, a ≠ b → ¬ G.Adj a.val b.val →
      2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {a, b}).card)
    (c : V) (χ : Y → Fin 2) (hnonconstant : ∃ a b, χ a ≠ χ b)
    (hcommon : ∀ v : Y, (bfsParent G root)^[p] v.val = c)
    (hsplit : ∀ u v : Y, χ u ≠ χ v → ∀ j < p,
      (bfsParent G root)^[j] u.val ≠ (bfsParent G root)^[j] v.val) :
    HasCycle G (k + 1) := by
  classical
  let ℓ := k + 1 - 2 * p
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; omega
  have hℓmax : ℓ ≤ 2 * s - 2 := by dsimp [ℓ]; omega
  have hHno : (G.induce (Y : Set V)).cliqueNum < s :=
    (G.cliqueNum_induce_le _).trans_lt hno
  obtain ⟨f, hf, hfχ⟩ := colored_path_prescribed_length hs hconn hnonbip hHno
    hdegree hpair χ hnonconstant hℓ hℓmax
  let F : Fin (ℓ + 1) → V := fun i => (f i).val
  have hF : IsIndexedPath G F := by
    refine ⟨fun i j h => hf.1 (Subtype.ext h), fun i => hf.2 i⟩
  let u := f (Fin.last ℓ)
  let v := f 0
  have hu := hlayer u.val u.property
  have hv := hlayer v.val v.property
  let B := bfsBranchPath G root u.val v.val p
  have hB : IsIndexedPath G B := bfsBranchPath_isPath hu.1 hv.1 hu.2 hv.2 hpd
    ((hcommon u).trans (hcommon v).symm) (hsplit u v hfχ.symm)
  have hcycle : HasCycle G (ℓ + 2 * p) := cycle_of_two_indexed_paths (by omega)
    F B hF hB (bfsBranchPath_start _ _ _ _ _) (bfsBranchPath_end _ _ _ _ (by omega)) (by
      intro i hi hilast j heq
      have hlevel := (hlayer (f j).val (f j).property).2
      have hBlevel := bfsBranchPath_internal_level hu.1 hv.1 hu.2 hv.2 hpd i hi hilast
      change G.dist root (B i) < d at hBlevel
      change G.dist root (F j) = d at hlevel
      rw [← heq, hlevel] at hBlevel
      omega)
  have hsum : ℓ + 2 * p = k + 1 := by dsimp [ℓ]; omega
  simpa only [hsum] using hcycle
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem cycleNext_eq_add_one {r : ℕ} (i : Fin (r + 1)) : cycleNext i = i + 1 := by
  cases r with
  | zero =>
    apply Fin.ext
    have h₁ := (cycleNext i).isLt
    have h₂ := (i + 1).isLt
    omega
  | succ r => apply Fin.ext; rfl
theorem indexedPath_closed_cycle {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hclose : G.Adj (f (Fin.last r)) (f 0)) :
    ∀ i, G.Adj (f i) (f (cycleNext i)) := by
  intro i
  by_cases hi : i.val = r
  · have heq : i = Fin.last r := Fin.ext hi
    have hn : cycleNext i = 0 := by
      apply Fin.ext
      simp only [cycleNext, hi, Nat.mod_self, Fin.val_zero]
    rw [hn, heq]
    exact hclose
  · let j : Fin r := ⟨i.val, by have := i.isLt; omega⟩
    have hleft : j.castSucc = i := Fin.ext rfl
    have hright : j.succ = cycleNext i := by
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm
    simpa only [hleft, hright] using hf.2 j
theorem indexedPath_closed_ending {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hclose : G.Adj (f (Fin.last r)) (f 0)) (j : Fin (r + 1)) :
    ∃ g : Fin (r + 1) → V, IsIndexedPath G g ∧
      g (Fin.last r) = f j ∧ Set.range g = Set.range f := by
  let c := j - Fin.last r
  let g : Fin (r + 1) → V := fun i => f (i + c)
  have hadd : ∀ i : Fin r, i.succ = i.castSucc + (1 : Fin (r + 1)) := by
    intro i
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (show i.castSucc < Fin.last r from i.isLt)]
    rfl
  have hg : IsIndexedPath G g := by
    refine ⟨hf.1.comp (fun a b h => add_right_cancel h), ?_⟩
    intro i
    have h := indexedPath_closed_cycle hf hclose (i.castSucc + c)
    simpa only [g, cycleNext_eq_add_one, hadd, add_assoc, add_comm 1 c] using h
  refine ⟨g, hg, ?_, ?_⟩
  · change f (Fin.last r + (j - Fin.last r)) = f j
    congr 1
    abel
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i + c, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i - c, by simp [g]⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem exists_longest_path {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧
      ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → q ≤ r := by
  classical
  let x : V := Classical.choice inferInstance
  let b := Fintype.card V - 1
  have hex : ∃ d, ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ r + d = b := by
    refine ⟨b, 0, fun _ => x, ⟨?_, ?_⟩, by omega⟩
    · intro i j _
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · exact fun i => Fin.elim0 i
  obtain ⟨r, f, hf, hd⟩ := Nat.find_spec hex
  refine ⟨r, f, hf, ?_⟩
  intro q g hg
  have hcard := Fintype.card_le_of_injective g hg.1
  simp only [Fintype.card_fin] at hcard
  have hqb : q ≤ b := by dsimp [b]; omega
  have hmin := Nat.find_min' hex
    (show ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ r + (b - q) = b from
      ⟨q, g, hg, Nat.add_sub_of_le hqb⟩)
  omega
theorem indexedPath_reverse {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) :
    IsIndexedPath G (f ∘ Fin.rev) := by
  refine ⟨hf.1.comp Fin.rev_injective, ?_⟩
  intro i
  simpa only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_succ] using (hf.2 i.rev).symm
theorem connected_edge_leaving {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    {W : Set V} {u v : V} (hu : u ∈ W) (hv : v ∉ W) :
    ∃ a ∈ W, ∃ b ∉ W, G.Adj a b := by
  classical
  obtain ⟨p⟩ := hconn.preconnected u v
  have hcut : ∀ {x y : V}, G.Walk x y → x ∈ W → y ∉ W →
      ∃ a ∈ W, ∃ b ∉ W, G.Adj a b := by
    intro x y q
    induction q with
    | nil => intro hx hy; exact False.elim (hy hx)
    | @cons x z y hxz q ih =>
      intro hx hy
      by_cases hz : z ∈ W
      · exact ih hz hy
      · exact ⟨x, hx, z, hz, hxz⟩
  exact hcut p hu hv
theorem closed_longest_path_surjective {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (hconn : G.Connected) {f : Fin (r + 1) → V} (hf : IsIndexedPath G f)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath G g → q ≤ r)
    (hclose : G.Adj (f (Fin.last r)) (f 0)) : Function.Surjective f := by
  intro v
  by_contra hv
  have hv' : v ∉ Set.range f := hv
  obtain ⟨a, ⟨j, rfl⟩, b, hb, hab⟩ := connected_edge_leaving hconn
    (show f 0 ∈ Set.range f from ⟨0, rfl⟩) hv'
  obtain ⟨g, hg, hlast, hrange⟩ := indexedPath_closed_ending hf hclose j
  have hb' : b ∉ Set.range g := by rwa [hrange]
  have hadj : G.Adj (g (Fin.last r)) b := by rwa [hlast]
  have hp := indexedPath_snoc hg hb' hadj
  have h := hmax (r + 1) (Fin.snoc g b) hp
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private theorem last_degree_index_bound {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} {f : Fin (r + 1) → V}
    (hcover : ∀ v, G.Adj (f (Fin.last r)) v → v ∈ Set.range f) :
    (G.neighborSet (f (Fin.last r))).ncard ≤
      (Finset.univ.filter (fun i : Fin r => G.Adj (f (Fin.last r)) (f i.castSucc))).card := by
  classical
  let A := Finset.univ.filter (fun i : Fin r => G.Adj (f (Fin.last r)) (f i.castSucc))
  have hsub : G.neighborFinset (f (Fin.last r)) ⊆ A.image (fun i => f i.castSucc) := by
    intro v hv
    have hadj := (G.mem_neighborFinset _ _).mp hv
    obtain ⟨j, hj⟩ := hcover v hadj
    have hjne : j ≠ Fin.last r := fun h => hadj.ne (by simpa only [h] using hj)
    have hjlt : j.val < r := by
      have := j.isLt
      have hneq : j.val ≠ r := fun h => hjne (Fin.ext h)
      omega
    let i : Fin r := ⟨j.val, hjlt⟩
    have hij : i.castSucc = j := Fin.ext rfl
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hij, hj]
    · simpa only [hij] using hj
  have h := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.ncard_neighborSet] using h
private theorem first_degree_index_bound {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} {f : Fin (r + 1) → V}
    (hcover : ∀ v, G.Adj (f 0) v → v ∈ Set.range f) :
    (G.neighborSet (f 0)).ncard ≤
      (Finset.univ.filter (fun i : Fin r => G.Adj (f 0) (f i.succ))).card := by
  classical
  let B := Finset.univ.filter (fun i : Fin r => G.Adj (f 0) (f i.succ))
  have hsub : G.neighborFinset (f 0) ⊆ B.image (fun i => f i.succ) := by
    intro v hv
    have hadj := (G.mem_neighborFinset _ _).mp hv
    obtain ⟨j, hj⟩ := hcover v hadj
    have hjne : j ≠ 0 := fun h => hadj.ne (by simpa only [h] using hj)
    have hjpos : 1 ≤ j.val := by
      have hneq : j.val ≠ 0 := fun h => hjne (Fin.ext (by simpa only [Fin.val_zero] using h))
      omega
    let i : Fin r := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hij : i.succ = j := by apply Fin.ext; dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, ?_⟩
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [hij, hj]
    · simpa only [hij] using hj
  have h := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.ncard_neighborSet] using h
theorem connected_long_path {V : Type*} [Fintype V] {G : SimpleGraph V} {s k : ℕ}
    (hconn : G.Connected) (hdegree : ∀ v, s ≤ (G.neighborSet v).ncard)
    (hk : k ≤ 2 * s + 1) (hcard : k ≤ Fintype.card V) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath G f ∧ k ≤ r + 1 := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨r, f, hf, hmax⟩ := exists_longest_path G
  refine ⟨r, f, hf, ?_⟩
  by_contra hshort
  have hlast : ∀ v, G.Adj (f (Fin.last r)) v → v ∈ Set.range f :=
    longest_path_endpoint_neighbors hf rfl (fun q g hg _ => hmax q g hg)
  have hfirst : ∀ v, G.Adj (f 0) v → v ∈ Set.range f := by
    intro v hv
    have hrev := longest_path_endpoint_neighbors (indexedPath_reverse hf) rfl
      (fun q g hg _ => hmax q g hg) v (by simpa using hv)
    obtain ⟨j, hj⟩ := hrev
    exact ⟨j.rev, hj⟩
  let A := Finset.univ.filter (fun i : Fin r => G.Adj (f (Fin.last r)) (f i.castSucc))
  let B := Finset.univ.filter (fun i : Fin r => G.Adj (f 0) (f i.succ))
  have hA : s ≤ A.card := (hdegree _).trans (last_degree_index_bound hlast)
  have hB : s ≤ B.card := (hdegree _).trans (first_degree_index_bound hfirst)
  have hnotdisjoint : ¬ Disjoint A B := by
    intro hdisjoint
    have h := Finset.card_union_of_disjoint hdisjoint
    have hbound : (A ∪ B).card ≤ r := by
      have hsub : A ∪ B ⊆ Finset.univ := Finset.subset_univ _
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
    omega
  obtain ⟨p, hpA, hpB⟩ := Finset.not_disjoint_iff.mp hnotdisjoint
  have hpA' := (Finset.mem_filter.mp hpA).2
  have hpB' := (Finset.mem_filter.mp hpB).2
  obtain ⟨hrotinj, hrotchain, hrotfirst, hrotlast, _⟩ := rotate_path f hf.1 hf.2 p hpA'
  have hrot : IsIndexedPath G (f ∘ rotationIndex p) := ⟨hrotinj, hrotchain⟩
  have hclose : G.Adj ((f ∘ rotationIndex p) (Fin.last r)) ((f ∘ rotationIndex p) 0) := by
    rw [hrotfirst, hrotlast]
    exact hpB'.symm
  have hsurj := closed_longest_path_surjective hconn hrot hmax hclose
  have hfull := Fintype.card_le_of_surjective _ hsurj
  simp only [Fintype.card_fin] at hfull
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem layer_cycle_of_one_predecessor {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d s k : ℕ}
    (hk : 3 ≤ k) (hks : k ≤ 2 * s + 1) (hcard : k ≤ Y.card) (hd : 1 ≤ d)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d)
    (hconn : (G.induce (Y : Set V)).Connected)
    (hdegree : ∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard)
    (c : V) (hcommon : ∀ v : Y, (bfsParent G root)^[1] v.val = c) :
    HasCycle G (k + 1) := by
  classical
  obtain ⟨r, f, hf, hr⟩ := connected_long_path hconn hdegree hks
    (hcard.trans_eq (Fintype.card_coe Y).symm)
  let ℓ := k - 1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; omega
  have hℓr : ℓ ≤ r := by dsimp [ℓ]; omega
  let g : Fin (ℓ + 1) → Y := fun i => f (Fin.castLE (by omega) i)
  have hg : IsIndexedPath (G.induce (Y : Set V)) g := indexedPath_prefix hf hℓr
  let F : Fin (ℓ + 1) → V := fun i => (g i).val
  have hF : IsIndexedPath G F := ⟨fun i j h => hg.1 (Subtype.ext h), fun i => hg.2 i⟩
  let u := g (Fin.last ℓ)
  let v := g 0
  have hu := hlayer u.val u.property
  have hv := hlayer v.val v.property
  have hsplit : ∀ j < 1, (bfsParent G root)^[j] u.val ≠ (bfsParent G root)^[j] v.val := by
    intro j hj
    have hjzero : j = 0 := by omega
    simp only [hjzero, Function.iterate_zero, id_eq]
    intro heq
    have hindex := hg.1 (Subtype.ext heq)
    have hval := congrArg Fin.val hindex
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  let B := bfsBranchPath G root u.val v.val 1
  have hB : IsIndexedPath G B := bfsBranchPath_isPath hu.1 hv.1 hu.2 hv.2 hd
    ((hcommon u).trans (hcommon v).symm) hsplit
  have hcycle : HasCycle G (ℓ + 2 * 1) := cycle_of_two_indexed_paths (by omega)
    F B hF hB (bfsBranchPath_start _ _ _ _ _) (bfsBranchPath_end _ _ _ _ (by omega)) (by
      intro i hi hilast j heq
      have hlevel := (hlayer (g j).val (g j).property).2
      have hBlevel := bfsBranchPath_internal_level hu.1 hv.1 hu.2 hv.2 hd i hi hilast
      change G.dist root (B i) < d at hBlevel
      change G.dist root (F j) = d at hlevel
      rw [← heq, hlevel] at hBlevel
      omega)
  have hsum : ℓ + 2 * 1 = k + 1 := by dsimp [ℓ]; omega
  simpa only [hsum] using hcycle
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem RamseyProperty.mono {m n M N : ℕ} (h : RamseyProperty m n M) (hMN : M ≤ N) :
    RamseyProperty m n N := by
  intro G
  let f : Fin M → Fin N := Fin.castLE hMN
  have hf : Function.Injective f := Fin.castLE_injective hMN
  rcases h (G.comap f) with hc | hi
  · exact Or.inl (hc.map f hf (fun h => h))
  · exact Or.inr (hi.map f hf (fun h => h))
theorem not_ramseyProperty_mono {m n M N : ℕ}
    (h : ¬ RamseyProperty m n N) (hMN : M ≤ N) : ¬ RamseyProperty m n M :=
  fun hM => h (hM.mono hMN)
theorem isRamseyNumber_of_upper_lower {m n N : ℕ}
    (hupper : RamseyProperty m n (N + 1)) (hlower : ¬ RamseyProperty m n N) :
    IsRamseyNumber m n (N + 1) := by
  refine ⟨hupper, fun M hM => not_ramseyProperty_mono hlower ?_⟩
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V}
theorem hasCycle_three_of_edges {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) : HasCycle G 3 := by
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hxy.ne, hyz.ne, hzx.ne]
  · intro i
    fin_cases i
    · simpa [cycleNext] using hxy
    · simpa [cycleNext] using hyz
    · simpa [cycleNext] using hzx
theorem hasIndependent_three_of_distinct_nonadjacent {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy' : ¬ G.Adj x y) (hxz' : ¬ G.Adj x z) (hyz' : ¬ G.Adj y z) :
    HasIndependent G 3 := by
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j
    have hyx' : ¬ G.Adj y x := fun h => hxy' h.symm
    have hzx' : ¬ G.Adj z x := fun h => hxz' h.symm
    have hzy' : ¬ G.Adj z y := fun h => hyz' h.symm
    fin_cases i <;> fin_cases j <;> simp_all
theorem triangle_upper : RamseyProperty 3 3 6 := by
  intro G
  classical
  let red : Finset (Fin 5) := Finset.univ.filter (fun i => G.Adj 0 i.succ)
  let blue : Finset (Fin 5) := Finset.univ.filter (fun i => ¬ G.Adj 0 i.succ)
  have hsum : red.card + blue.card = 5 := by
    simpa [red, blue] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin 5 => G.Adj 0 i.succ)
  have hlarge : 2 < red.card ∨ 2 < blue.card := by omega
  rcases hlarge with hr | hb
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hr
    have hx' : G.Adj 0 x.succ := (Finset.mem_filter.mp hx).2
    have hy' : G.Adj 0 y.succ := (Finset.mem_filter.mp hy).2
    have hz' : G.Adj 0 z.succ := (Finset.mem_filter.mp hz).2
    by_cases hxy' : G.Adj x.succ y.succ
    · exact Or.inl (hasCycle_three_of_edges hx' hxy' hy'.symm)
    by_cases hxz' : G.Adj x.succ z.succ
    · exact Or.inl (hasCycle_three_of_edges hx' hxz' hz'.symm)
    by_cases hyz' : G.Adj y.succ z.succ
    · exact Or.inl (hasCycle_three_of_edges hy' hyz' hz'.symm)
    exact Or.inr (hasIndependent_three_of_distinct_nonadjacent ((Fin.succ_injective 5).ne hxy)
      ((Fin.succ_injective 5).ne hxz) ((Fin.succ_injective 5).ne hyz) hxy' hxz' hyz')
  · obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hb
    have hx' : ¬ G.Adj 0 x.succ := (Finset.mem_filter.mp hx).2
    have hy' : ¬ G.Adj 0 y.succ := (Finset.mem_filter.mp hy).2
    have hz' : ¬ G.Adj 0 z.succ := (Finset.mem_filter.mp hz).2
    by_cases hxy' : G.Adj x.succ y.succ
    · by_cases hxz' : G.Adj x.succ z.succ
      · by_cases hyz' : G.Adj y.succ z.succ
        · exact Or.inl (hasCycle_three_of_edges hxy' hyz' hxz'.symm)
        · exact Or.inr (hasIndependent_three_of_distinct_nonadjacent (Fin.succ_ne_zero y).symm
            (Fin.succ_ne_zero z).symm ((Fin.succ_injective 5).ne hyz) hy' hz' hyz')
      · exact Or.inr (hasIndependent_three_of_distinct_nonadjacent (Fin.succ_ne_zero x).symm
          (Fin.succ_ne_zero z).symm ((Fin.succ_injective 5).ne hxz) hx' hz' hxz')
    · exact Or.inr (hasIndependent_three_of_distinct_nonadjacent (Fin.succ_ne_zero x).symm
        (Fin.succ_ne_zero y).symm ((Fin.succ_injective 5).ne hxy) hx' hy' hxy')
def pentagon : SimpleGraph (Fin 5) where
  Adj x y := (x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro x h; rcases h with h | h <;> omega⟩
instance : DecidableRel pentagon.Adj := by unfold pentagon; infer_instance
private theorem pentagon_no_triangle :
    ∀ x y z : Fin 5, pentagon.Adj x y → pentagon.Adj y z → ¬ pentagon.Adj z x := by
  decide
private theorem pentagon_no_independent_triple :
    ∀ x y z : Fin 5, x ≠ y → x ≠ z → y ≠ z →
      ¬ pentagon.Adj x y → ¬ pentagon.Adj x z → pentagon.Adj y z := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide
theorem triangle_lower : ¬ RamseyProperty 3 3 5 := by
  intro h
  rcases h pentagon with ⟨f, hf, he⟩ | ⟨f, hf, he⟩
  · have h01 : pentagon.Adj (f 0) (f 1) := by simpa [cycleNext] using he 0
    have h12 : pentagon.Adj (f 1) (f 2) := by simpa [cycleNext] using he 1
    have h20 : pentagon.Adj (f 2) (f 0) := by simpa [cycleNext] using he 2
    exact pentagon_no_triangle _ _ _ h01 h12 h20
  · exact he 1 2 (pentagon_no_independent_triple (f 0) (f 1) (f 2)
      (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide)) (he 0 1) (he 0 2))
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem triangle_ramsey : IsRamseyNumber 3 3 6 :=
  isRamseyNumber_of_upper_lower triangle_upper triangle_lower
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private theorem cycleNext_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : cycleNext i ≠ i := by
  intro h
  have heq := congrArg Fin.val h
  change (i.val + 1) % m = i.val at heq
  by_cases hi : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi] at heq
    omega
  · have hlast : i.val + 1 = m := by omega
    rw [hlast, Nat.mod_self] at heq
    omega
theorem clique_contains_cycle {V : Type*} {G : SimpleGraph V} {Q : Finset V} {m : ℕ}
    (hm : 3 ≤ m) (hQ : G.IsClique (Q : Set V)) (hcard : m ≤ Q.card) : HasCycle G m := by
  classical
  obtain ⟨S, hSQ, hS⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin m ≃ S := (Finset.equivFinOfCardEq hS).symm
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  apply hQ (hSQ (e i).property) (hSQ (e (cycleNext i)).property)
  intro h
  have heq := e.injective (Subtype.ext h)
  exact cycleNext_ne (by omega) i heq.symm
theorem triangle_free_order_bound (a : ℕ) :
    ∀ {V : Type*} [Fintype V] {G : SimpleGraph V},
      IndependenceBound G a → ¬ HasCycle G 3 →
      2 * Fintype.card V ≤ a * (a + 3) := by
  induction a with
  | zero =>
    intro V _ G hI _
    have hempty : IsEmpty V := ⟨fun v => by
      have h := hI {v} (by simp)
      simp at h⟩
    simp
  | succ a ih =>
    intro V _ G hI htriangle
    classical
    by_cases hnonempty : Nonempty V
    · obtain ⟨v⟩ := hnonempty
      have hN : G.IsIndepSet (G.neighborFinset v : Set V) := by
        intro x hx y hy _ hxy
        exact htriangle (hasCycle_three_of_edges ((G.mem_neighborFinset v x).mp hx) hxy
          ((G.mem_neighborFinset v y).mp hy).symm)
      have hdegree := hI (G.neighborFinset v) hN
      have hclosed : closedNeighborhood G {v} = insert v (G.neighborFinset v) := by
        ext w
        simp [mem_closedNeighborhood]
      have hv : v ∉ G.neighborFinset v := by simp
      have hclosedCard : (closedNeighborhood G {v}).card ≤ a + 2 := by
        rw [hclosed, Finset.card_insert_of_notMem hv]
        omega
      let Y : Finset V := Finset.univ \ closedNeighborhood G {v}
      have hY : (Y : Set V) = {w | w ∉ closedNeighborhood G {v}} := by ext w; simp [Y]
      have hIY : IndependenceBound (G.induce (Y : Set V)) a := by
        rw [hY]
        simpa using independent_outside_bound hI (I := {v}) (by simp)
      have htriangleY : ¬ HasCycle (G.induce (Y : Set V)) 3 := by
        intro h
        exact htriangle (h.map Subtype.val Subtype.val_injective (fun h => h))
      have hYbound : 2 * Y.card ≤ a * (a + 3) := by simpa using ih hIY htriangleY
      have hsum : Y.card + (closedNeighborhood G {v}).card = Fintype.card V := by
        simpa [Y] using Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (closedNeighborhood G {v}))
      nlinarith
    · have : IsEmpty V := not_nonempty_iff.mp hnonempty
      simp
theorem cliqueNum_le_of_no_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 2 ≤ k) (hcycle : ¬ HasCycle G (k + 1)) : G.cliqueNum ≤ k := by
  by_contra hn
  obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
  have hsize := hQ.card_eq
  apply hcycle
  exact clique_contains_cycle (by omega) hQ.isClique (by omega)
theorem triangle_clique_bounds {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (_ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1)
    (hI : IndependenceBound G a) (hcycle : ¬ HasCycle G (k + 1)) :
    3 ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  classical
  have htriangle : HasCycle G 3 := by
    by_contra hn
    have hb := triangle_free_order_bound a hI hn
    have hparam : a + 3 ≤ 2 * k := by omega
    rw [hcard] at hb
    nlinarith
  obtain ⟨f, _, he⟩ := htriangle
  have h01 : G.Adj (f 0) (f 1) := by simpa [cycleNext] using he 0
  have h12 : G.Adj (f 1) (f 2) := by simpa [cycleNext] using he 1
  have h20 : G.Adj (f 2) (f 0) := by simpa [cycleNext] using he 2
  have hQ : G.IsNClique 3 {f 0, f 1, f 2} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h01, h20.symm, h12⟩
  refine ⟨?_, cliqueNum_le_of_no_cycle (by omega) hcycle⟩
  simpa [hQ.card_eq] using hQ.isClique.card_le_cliqueNum
theorem large_clique_small_k {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (hk7 : k ≤ 7) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1)
    (hI : IndependenceBound G a) (hcycle : ¬ HasCycle G (k + 1)) :
    max 3 (k / 2) ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  obtain ⟨hlo, hhi⟩ := triangle_clique_bounds hk ha hak hcard hI hcycle
  exact ⟨by omega, hhi⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private theorem dense_layer_forces_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d s k : ℕ}
    (hs : 4 ≤ s) (hk : 2 * s ≤ k) (hk' : k ≤ 2 * s + 1)
    (hd : d ≤ s) (hcard : k ≤ Y.card)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d)
    (hconn : (G.induce (Y : Set V)).Connected)
    (hnonbip : ¬ (G.induce (Y : Set V)).IsBipartite) (hno : G.cliqueNum < s)
    (hdegree : ∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard)
    (hpair : ∀ a b : Y, a ≠ b → ¬ G.Adj a.val b.val →
      2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {a, b}).card) :
    HasCycle G (k + 1) := by
  obtain ⟨p, hp, hpd, c, χ, hχ, hcommon, hsplit⟩ :=
    exists_bfs_branch_partition (by omega) hlayer
  by_cases hpone : p = 1
  · subst p
    exact layer_cycle_of_one_predecessor (by omega) hk' hcard hpd hlayer hconn hdegree c hcommon
  · exact layer_cycle_of_two_branches hs hk hk' (by omega) (hpd.trans hd) hpd
      hlayer hconn hnonbip hno hdegree hpair c χ hχ hcommon hsplit
theorem large_clique_bounds {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    max 3 (k / 2) ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  classical
  obtain ⟨htriangle, hupper⟩ := triangle_clique_bounds hk ha hak hcard hI hcycle
  refine ⟨?_, hupper⟩
  by_cases hk7 : k ≤ 7
  · omega
  · have hk8 : 8 ≤ k := by omega
    let s := k / 2
    have hs : 4 ≤ s := by dsimp [s]; omega
    have hks : 2 * s ≤ k := by dsimp [s]; omega
    have hks' : k ≤ 2 * s + 1 := by dsimp [s]; omega
    have hhalf : s ≤ G.cliqueNum := by
      by_contra hsmall
      have hno : G.cliqueNum < s := by omega
      have hIk : IndependenceBound G k := fun I hi => (hI I hi).trans hak
      let : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
      let root : V := Classical.choice inferInstance
      by_cases heven : k = 2 * s
      · have hInd : IndependenceBound G (2 * s) := by simpa only [← heven] using hIk
        have hExp : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
            2 * s * I.card + 1 ≤ (closedNeighborhood G I).card := by
          simpa only [← heven] using hexpand
        obtain ⟨d, _, hds, Y, hYD, _, hconn, hnonbip, hYcard, hdegree, hpair⟩ :=
          dense_layer_interface_even hs hno hInd hExp root
        have hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d :=
          fun v hv => mem_distanceLayer.mp (hYD hv)
        exact hcycle (dense_layer_forces_cycle hs hks hks' hds (by omega) hlayer
          hconn hnonbip hno hdegree hpair)
      · have hodd : k = 2 * s + 1 := by omega
        have hInd : IndependenceBound G (2 * s + 1) := by simpa only [← hodd] using hIk
        have hExp : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
            (2 * s + 1) * I.card + 1 ≤ (closedNeighborhood G I).card := by
          simpa only [← hodd] using hexpand
        obtain ⟨d, _, hds, Y, hYD, _, hconn, hnonbip, hYcard, hdegree, hpair⟩ :=
          dense_layer_interface_odd hs hno hInd hExp root
        have hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d :=
          fun v hv => mem_distanceLayer.mp (hYD hv)
        exact hcycle (dense_layer_forces_cycle hs hks hks' hds (by omega) hlayer
          hconn hnonbip hno hdegree hpair)
    dsimp [s] at hhalf
    omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V}
theorem hasCycle_of_isCycle {x : V} {p : G.Walk x x} (hp : p.IsCycle) :
    HasCycle G p.length := by
  refine ⟨fun i => p.getVert i.val, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) hij
  · intro i
    have hadj := p.adj_getVert_succ i.isLt
    by_cases hlast : i.val + 1 = p.length
    · have hn : (cycleNext i).val = 0 := by simp [cycleNext, hlast]
      simpa [hlast, hn] using hadj
    · have hn : (cycleNext i).val = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      simpa [hn] using hadj
theorem hasCycle_of_path_close {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) (hlen : 2 ≤ p.length) (hclose : G.Adj y x) :
    HasCycle G (p.length + 1) := by
  have hdis : p.support.tail.Disjoint hclose.toWalk.support.tail := by
    rw [hclose.support_toWalk]
    apply List.disjoint_left.mpr
    intro v hv hvx
    have hv' : v = x := by simpa using hvx
    subst v
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1 hv
  have hcycle := hp.isCycle_append hclose.isPath_toWalk hdis (Or.inl (by omega))
  have hc := hasCycle_of_isCycle hcycle
  simpa using hc
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private theorem chain_of_pairwise {α : Type*} {R : α → α → Prop} {L : List α}
    (h : L.Pairwise R) : L.IsChain R := by
  induction h with
  | nil => exact .nil
  | @cons a l hrel _ ih =>
    exact ih.cons (fun b hb => hrel b (List.mem_of_mem_head? hb))
theorem hasCycle_of_disjoint_clique_paths {V : Type*} {G : SimpleGraph V}
    {Q : Set V} (hQ : G.IsClique Q) (L : List (List V))
    (hnonempty : ∀ l ∈ L, l ≠ [])
    (hpaths : ∀ l ∈ L, l.Nodup ∧ l.IsChain G.Adj)
    (hdisjoint : L.Pairwise List.Disjoint)
    (hendpoints : ∀ l ∈ L,
      (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hlen : 3 ≤ L.flatten.length) : HasCycle G L.flatten.length := by
  have hflatne : L.flatten ≠ [] := by intro h; simp [h] at hlen
  have hLne : L ≠ [] := by intro h; simp [h] at hlen
  have hnodup : L.flatten.Nodup := List.nodup_flatten.mpr
    ⟨fun l hl => (hpaths l hl).1, hdisjoint⟩
  have hconnections : L.IsChain
      (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, G.Adj x y) := by
    apply chain_of_pairwise
    apply hdisjoint.imp_of_mem
    intro l₁ l₂ hl₁ hl₂ hd x hx y hy
    apply hQ ((hendpoints l₁ hl₁).2 x hx) ((hendpoints l₂ hl₂).1 y hy)
    intro heq
    subst y
    exact List.disjoint_left.mp hd (List.mem_of_mem_getLast? hx) (List.mem_of_mem_head? hy)
  have hchain : L.flatten.IsChain G.Adj :=
    (List.isChain_flatten (fun hempty => hnonempty [] hempty rfl)).mpr
      ⟨fun l hl => (hpaths l hl).2, hconnections⟩
  have hhead : L.flatten.head hflatne ∈ Q := by
    rw [List.head_flatten_eq_head_head hflatne (hnonempty _ (List.head_mem hLne))]
    apply (hendpoints _ (List.head_mem hLne)).1
    exact List.head?_eq_some_head (hnonempty _ (List.head_mem hLne))
  have hlast : L.flatten.getLast hflatne ∈ Q := by
    rw [List.getLast_flatten_eq_getLast_getLast hflatne
      (hnonempty _ (List.getLast_mem hLne))]
    apply (hendpoints _ (List.getLast_mem hLne)).2
    exact List.getLast?_eq_some_getLast (hnonempty _ (List.getLast_mem hLne))
  have hne : L.flatten.getLast hflatne ≠ L.flatten.head hflatne := by
    intro heq
    obtain ⟨v, hv⟩ := (hnodup.head_eq_getLast_iff hflatne).mp heq.symm
    simp [hv] at hlen
  let p := SimpleGraph.Walk.ofSupport L.flatten hflatne hchain
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa [p, SimpleGraph.Walk.support_ofSupport] using hnodup
  have hplength : p.length = L.flatten.length - 1 :=
    SimpleGraph.Walk.length_ofSupport hflatne hchain
  have hc := hasCycle_of_path_close hp (by omega) (hQ hlast hhead hne)
  have heq : p.length + 1 = L.flatten.length := by omega
  simpa [heq] using hc
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*}
structure ExpandedPathSystem (G : SimpleGraph V) (Q : Finset V) where
  chains : List (List V)
  nontrivial : ∀ l ∈ chains, 3 ≤ l.length
  paths : ∀ l ∈ chains, l.Nodup ∧ l.IsChain G.Adj
  disjoint : chains.Pairwise List.Disjoint
  endpoints : ∀ l ∈ chains,
    (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)
  no_clique_steps : ∀ l ∈ chains,
    l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))
namespace ExpandedPathSystem
variable {G : SimpleGraph V} {Q : Finset V}
def empty (G : SimpleGraph V) (Q : Finset V) : ExpandedPathSystem G Q where
  chains := []
  nontrivial := by simp
  paths := by simp
  disjoint := .nil
  endpoints := by simp
  no_clique_steps := by simp
noncomputable def vertices (S : ExpandedPathSystem G Q) : Finset V := by
  classical
  exact S.chains.flatten.toFinset
noncomputable def amount (S : ExpandedPathSystem G Q) : ℕ := by
  classical
  exact (S.vertices \ Q).card
noncomputable def incident (S : ExpandedPathSystem G Q) : ℕ := by
  classical
  exact (S.vertices ∩ Q).card
noncomputable def assignedCount (S : ExpandedPathSystem G Q) : ℕ :=
  S.incident - S.chains.length
theorem flatten_nodup (S : ExpandedPathSystem G Q) : S.chains.flatten.Nodup :=
  List.nodup_flatten.mpr ⟨fun l hl => (S.paths l hl).1, S.disjoint⟩
theorem vertices_card (S : ExpandedPathSystem G Q) :
    S.vertices.card = S.chains.flatten.length := by
  classical
  exact List.toFinset_card_of_nodup S.flatten_nodup
theorem length_eq_amount_add_incident (S : ExpandedPathSystem G Q) :
    S.chains.flatten.length = S.amount + S.incident := by
  classical
  rw [← S.vertices_card]
  exact (Finset.card_sdiff_add_card_inter S.vertices Q).symm
@[simp] theorem empty_amount (G : SimpleGraph V) (Q : Finset V) :
    (empty G Q).amount = 0 := by
  classical
  simp [amount, vertices, empty]
@[simp] theorem empty_assignedCount (G : SimpleGraph V) (Q : Finset V) :
    (empty G Q).assignedCount = 0 := by
  classical
  simp [assignedCount, incident, vertices, empty]
theorem forbidden_interval {k : ℕ} (hk : 3 ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (S : ExpandedPathSystem G Q)
    (hlow : k + 1 - Q.card ≤ S.amount)
    (hhigh : S.amount + S.incident ≤ k + 1) : False := by
  classical
  let u := k + 1 - (S.amount + S.incident)
  have hu : u ≤ (Q \ S.vertices).card := by
    have hcard := Finset.card_sdiff_add_card_inter Q S.vertices
    have hinter : (Q ∩ S.vertices).card = S.incident := by
      simp [incident, Finset.inter_comm]
    rw [hinter] at hcard
    omega
  obtain ⟨J, hJ, hJcard⟩ := Finset.exists_subset_card_eq hu
  let L := S.chains ++ J.toList.map (fun v => [v])
  have hnonempty : ∀ l ∈ L, l ≠ [] := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · have := S.nontrivial l hl
      intro heq
      simp [heq] at this
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      simp
  have hpaths : ∀ l ∈ L, l.Nodup ∧ l.IsChain G.Adj := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.paths l hl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact ⟨by simp, .singleton v⟩
  have hdisjoint : L.Pairwise List.Disjoint := by
    apply List.pairwise_append.mpr
    refine ⟨S.disjoint, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      apply J.nodup_toList.imp
      intro v w hvw
      simpa using hvw.symm
    · intro l hl m hm
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
      apply List.disjoint_left.mpr
      intro w hw hwv
      have heq : w = v := by simpa using hwv
      subst w
      have hvJ : v ∈ J := by simpa using hv
      have hvout := (Finset.mem_sdiff.mp (hJ hvJ)).2
      exact hvout (by
        change v ∈ S.chains.flatten.toFinset
        exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hl, hw⟩))
  have hends : ∀ l ∈ L,
      (∀ v ∈ l.head?, v ∈ (Q : Set V)) ∧ (∀ v ∈ l.getLast?, v ∈ (Q : Set V)) := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.endpoints l hl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      have hvJ : v ∈ J := Finset.mem_toList.mp hv
      have hvQ : v ∈ Q := (Finset.mem_sdiff.mp (hJ hvJ)).1
      simpa using And.intro hvQ hvQ
  have hlen : L.flatten.length = k + 1 := by
    have hsingle : ∀ l : List V, (l.map (fun v => [v])).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons v l ih => simpa using congrArg (List.cons v) ih
    simp only [L, List.flatten_append, List.length_append, hsingle, Finset.length_toList]
    rw [S.length_eq_amount_add_incident, hJcard]
    omega
  have hc := hasCycle_of_disjoint_clique_paths hQ L hnonempty hpaths hdisjoint hends
    (by omega)
  exact hcycle (by simpa [hlen] using hc)
end ExpandedPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem short_chain_in_clique {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)))
    (hlen : l.length < 3) : ∀ v ∈ l, v ∈ Q := by
  cases l with
  | nil => simp
  | cons x l =>
    cases l with
    | nil => simpa using hends.1
    | cons y l =>
      cases l with
      | nil =>
        have hx : x ∈ Q := hends.1 x (by simp)
        have hy : y ∈ Q := hends.2 y (by simp)
        have hxy : ¬ (x ∈ Q ∧ y ∈ Q) := by simpa using hsteps
        exact False.elim (hxy ⟨hx, hy⟩)
      | cons z l => simp only [List.length_cons] at hlen; omega
noncomputable def normalizeChains (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ExpandedPathSystem G Q where
  chains := C.filter (fun l => decide (3 ≤ l.length))
  nontrivial := by
    intro l hl
    exact of_decide_eq_true (List.mem_filter.mp hl).2
  paths := fun l hl => hpaths l (List.mem_filter.mp hl).1
  disjoint := hdis.filter _
  endpoints := fun l hl => hends l (List.mem_filter.mp hl).1
  no_clique_steps := fun l hl => hsteps l (List.mem_filter.mp hl).1
theorem normalizeChains_outside_vertices [DecidableEq V] (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    (normalizeChains C hpaths hdis hends hsteps).vertices \ Q = C.flatten.toFinset \ Q := by
  ext v
  simp only [Finset.mem_sdiff, ExpandedPathSystem.vertices, normalizeChains,
    List.mem_toFinset, List.mem_flatten, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l, ⟨hl, _⟩, hv⟩, hvQ⟩
    exact ⟨⟨l, hl, hv⟩, hvQ⟩
  · rintro ⟨⟨l, hl, hv⟩, hvQ⟩
    have hlen : 3 ≤ l.length := by
      by_contra hn
      exact hvQ (short_chain_in_clique (hends l hl) (hsteps l hl) (by omega) v hv)
    exact ⟨⟨l, ⟨hl, hlen⟩, hv⟩, hvQ⟩
theorem normalizeChains_amount [DecidableEq V] (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    (normalizeChains C hpaths hdis hends hsteps).amount = (C.flatten.toFinset \ Q).card := by
  classical
  unfold ExpandedPathSystem.amount
  convert congrArg Finset.card
    (@normalizeChains_outside_vertices V G Q (Classical.decEq V) C
      hpaths hdis hends hsteps) using 1
  congr 1
  ext v
  simp
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
noncomputable def chainCliqueCount (Q : Finset V) (l : List V) : ℕ := by
  classical
  exact (l.filter (fun v => decide (v ∈ Q))).length
noncomputable def rawAssignedCount (Q : Finset V) (C : List (List V)) : ℕ :=
  (C.map (fun l => chainCliqueCount Q l - 1)).sum
@[simp] theorem chainCliqueCount_append (A B : List V) :
    chainCliqueCount Q (A ++ B) = chainCliqueCount Q A + chainCliqueCount Q B := by
  classical
  simp [chainCliqueCount, List.filter_append]
@[simp] theorem chainCliqueCount_reverse (A : List V) :
    chainCliqueCount Q A.reverse = chainCliqueCount Q A := by
  classical
  simp [chainCliqueCount, List.filter_reverse]
theorem chainCliqueCount_eq_zero {J : List V} (hJ : ∀ z ∈ J, z ∉ Q) :
    chainCliqueCount Q J = 0 := by
  classical
  simp only [chainCliqueCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro z hz
  simpa using hJ z hz
@[simp] theorem rawAssignedCount_append (A B : List (List V)) :
    rawAssignedCount Q (A ++ B) = rawAssignedCount Q A + rawAssignedCount Q B := by
  simp [rawAssignedCount]
theorem chainCliqueCount_pos {l : List V} (hne : l ≠ [])
    (hhead : ∀ v ∈ l.head?, v ∈ Q) : 1 ≤ chainCliqueCount Q l := by
  classical
  have hm : l.head hne ∈ l.filter (fun v => decide (v ∈ Q)) := by
    apply List.mem_filter.mpr
    exact ⟨List.head_mem hne, by simpa using hhead _ (List.head?_eq_some_head hne)⟩
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hm)
theorem chainCliqueCount_pos_last {l : List V} (hne : l ≠ [])
    (hlast : ∀ v ∈ l.getLast?, v ∈ Q) : 1 ≤ chainCliqueCount Q l := by
  rw [← chainCliqueCount_reverse]
  exact chainCliqueCount_pos (by simpa using hne) (by simpa using hlast)
theorem chainCliqueCount_flatten (C : List (List V)) :
    chainCliqueCount Q C.flatten = (C.map (chainCliqueCount Q)).sum := by
  classical
  simp only [chainCliqueCount, List.filter_flatten, List.length_flatten, List.map_map,
    Function.comp_def]
  rfl
theorem rawAssignedCount_add_length (C : List (List V))
    (hpos : ∀ l ∈ C, 1 ≤ chainCliqueCount Q l) :
    rawAssignedCount Q C + C.length = chainCliqueCount Q C.flatten := by
  rw [chainCliqueCount_flatten]
  induction C with
  | nil => simp [rawAssignedCount]
  | cons l C ih =>
    have hl := hpos l (by simp)
    have hi := ih (fun l hl => hpos l (by simp [hl]))
    simp only [rawAssignedCount, List.map_cons, List.sum_cons, List.length_cons] at hi ⊢
    omega
theorem ExpandedPathSystem.incident_eq_chainCliqueCount (S : ExpandedPathSystem G Q) :
    S.incident = chainCliqueCount Q S.chains.flatten := by
  classical
  have heq : S.vertices ∩ Q =
      (S.chains.flatten.filter (fun v => decide (v ∈ Q))).toFinset := by
    ext v
    simp [ExpandedPathSystem.vertices]
    aesop
  unfold incident
  rw [heq, List.toFinset_card_of_nodup (S.flatten_nodup.filter _)]
  rfl
theorem ExpandedPathSystem.assignedCount_eq_raw (S : ExpandedPathSystem G Q) :
    S.assignedCount = rawAssignedCount Q S.chains := by
  have hpos : ∀ l ∈ S.chains, 1 ≤ chainCliqueCount Q l := by
    intro l hl
    apply chainCliqueCount_pos
    · intro heq
      have hh := S.nontrivial l hl
      simp [heq] at hh
    · exact (S.endpoints l hl).1
  have h := rawAssignedCount_add_length S.chains hpos
  rw [← S.incident_eq_chainCliqueCount] at h
  unfold assignedCount
  omega
theorem short_chainCliqueCount {l : List V} (hne : l ≠ [])
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)))
    (hlen : l.length < 3) : chainCliqueCount Q l = 1 := by
  classical
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons x l =>
    cases l with
    | nil =>
      have hx := hends.1 x (by simp)
      simp [chainCliqueCount, hx]
    | cons y l =>
      have hy := short_chain_in_clique hends hsteps hlen
      have hxQ := hy x (by simp)
      have hyQ := hy y (by simp)
      exact False.elim ((List.isChain_cons_cons.mp hsteps).1 ⟨hxQ, hyQ⟩)
theorem short_chainCliqueCount_le {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)))
    (hlen : l.length < 3) : chainCliqueCount Q l ≤ 1 := by
  by_cases he : l = []
  · subst l
    simp [chainCliqueCount]
  · rw [short_chainCliqueCount he hends hsteps hlen]
theorem normalizeChains_assignedCount (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    (normalizeChains C hpaths hdis hends hsteps).assignedCount = rawAssignedCount Q C := by
  classical
  rw [ExpandedPathSystem.assignedCount_eq_raw]
  change rawAssignedCount Q (C.filter (fun l => decide (3 ≤ l.length))) = _
  induction C with
  | nil => simp [rawAssignedCount]
  | cons l C ih =>
    have ht := ih (fun l hl => hpaths l (by simp [hl]))
      (List.pairwise_cons.mp hdis).2
      (fun l hl => hends l (by simp [hl]))
      (fun l hl => hsteps l (by simp [hl]))
    by_cases hl : 3 ≤ l.length
    · simpa [List.filter_cons, hl, rawAssignedCount] using
        congrArg (fun n => chainCliqueCount Q l - 1 + n) ht
    · have hc := short_chainCliqueCount_le
        (hends l (by simp)) (hsteps l (by simp)) (by omega)
      have hz : chainCliqueCount Q l - 1 = 0 := by omega
      simpa [List.filter_cons, hl, rawAssignedCount, hz] using ht
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem chain_outside_interior {V : Type*} {Q : Finset V} {x y : V} {J : List V}
    (hxy : ¬ (x ∈ Q ∧ y ∈ Q)) (hJ : ∀ z ∈ J, z ∉ Q) :
    (x :: (J ++ [y])).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
  induction J generalizing x with
  | nil => simpa using hxy
  | cons z J ih =>
    simp only [List.cons_append, List.isChain_cons_cons]
    refine ⟨fun h => hJ z (by simp) h.2, ?_⟩
    exact ih (fun h => hJ z (by simp) h.1) (fun w hw => hJ w (by simp [hw]))
theorem chain_outside_interior_of_ne_nil {V : Type*} {Q : Finset V}
    {x y : V} {J : List V} (hne : J ≠ []) (hJ : ∀ z ∈ J, z ∉ Q) :
    (x :: (J ++ [y])).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
  cases J with
  | nil => exact False.elim (hne rfl)
  | cons z J =>
    simp only [List.cons_append, List.isChain_cons_cons]
    refine ⟨fun h => hJ z (by simp) h.2, ?_⟩
    exact chain_outside_interior (fun h => hJ z (by simp) h.1)
      (fun w hw => hJ w (by simp [hw]))
theorem reverse_join_chain {V : Type*} {R : V → V → Prop}
    (hsym : ∀ ⦃a b⦄, R a b → R b a) {B D J : List V} {x y : V}
    (hleft : (x :: B).IsChain R) (hright : (y :: D).IsChain R)
    (hjoin : (x :: (J ++ [y])).IsChain R) :
    (B.reverse ++ x :: (J ++ y :: D)).IsChain R := by
  apply List.isChain_split.mpr
  constructor
  · have hr : (x :: B).reverse.IsChain R := List.isChain_reverse.mpr (hleft.imp hsym)
    simpa using hr
  · exact List.isChain_cons_split.mpr ⟨hjoin, hright⟩
theorem nodup_insert_list {V : Type*} {A B J : List V}
    (hold : (A ++ B).Nodup) (hJ : J.Nodup) (hdis : J.Disjoint (A ++ B)) :
    (A ++ J ++ B).Nodup := by
  have h := hold.append hJ hdis.symm
  have hp := (show (J ++ B).Perm (B ++ J) from List.perm_append_comm).append_left A
  have hn := hp.nodup_iff.mpr (show (A ++ (B ++ J)).Nodup by
    simpa only [List.append_assoc] using h)
  simpa only [List.append_assoc] using hn
theorem chain_insert_between {V : Type*} {R : V → V → Prop} {A B J : List V} {x y : V}
    (hold : (A ++ x :: y :: B).IsChain R)
    (hnew : (x :: (J ++ [y])).IsChain R) :
    (A ++ x :: (J ++ y :: B)).IsChain R := by
  have ho := List.isChain_append_cons_cons.mp hold
  apply List.isChain_split.mpr
  refine ⟨ho.1, ?_⟩
  exact List.isChain_cons_split.mpr ⟨hnew, ho.2.2⟩
theorem head_insert_between {V : Type*} (A B J : List V) (x y : V) :
    (A ++ x :: (J ++ y :: B)).head? = (A ++ x :: y :: B).head? := by
  simp
theorem last_insert_between {V : Type*} (A B J : List V) (x y : V) :
    (A ++ x :: (J ++ y :: B)).getLast? = (A ++ x :: y :: B).getLast? := by
  have htail : (y :: B).getLast? = some ((y :: B).getLast (by simp)) :=
    List.getLast?_eq_some_getLast (by simp)
  have hold : A ++ x :: y :: B = (A ++ [x]) ++ (y :: B) := by
    simp only [List.append_assoc, List.singleton_append]
  have hnew : A ++ x :: (J ++ y :: B) = (A ++ [x] ++ J) ++ (y :: B) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hold, hnew]
  simp only [List.getLast?_append, htail, Option.or]
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
structure RawPathSystem (G : SimpleGraph V) (Q : Finset V) where
  chains : List (List V)
  paths : ∀ l ∈ chains, l.Nodup ∧ l.IsChain G.Adj
  disjoint : chains.Pairwise List.Disjoint
  endpoints : ∀ l ∈ chains,
    (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)
  no_clique_steps : ∀ l ∈ chains,
    l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))
namespace RawPathSystem
noncomputable def normalize (S : RawPathSystem G Q) : ExpandedPathSystem G Q :=
  normalizeChains S.chains S.paths S.disjoint S.endpoints S.no_clique_steps
noncomputable def vertices (S : RawPathSystem G Q) : Finset V := by
  classical
  exact S.chains.flatten.toFinset
noncomputable def amount (S : RawPathSystem G Q) : ℕ := by
  classical
  exact (S.vertices \ Q).card
noncomputable def assignedCount (S : RawPathSystem G Q) : ℕ :=
  rawAssignedCount Q S.chains
theorem flatten_nodup (S : RawPathSystem G Q) : S.chains.flatten.Nodup :=
  List.nodup_flatten.mpr ⟨fun l hl => (S.paths l hl).1, S.disjoint⟩
@[simp] theorem normalize_amount (S : RawPathSystem G Q) :
    S.normalize.amount = S.amount := by
  classical
  exact normalizeChains_amount S.chains S.paths S.disjoint S.endpoints S.no_clique_steps
@[simp] theorem normalize_assignedCount (S : RawPathSystem G Q) :
    S.normalize.assignedCount = S.assignedCount :=
  normalizeChains_assignedCount S.chains S.paths S.disjoint S.endpoints S.no_clique_steps
end RawPathSystem
namespace ExpandedPathSystem
def toRaw (S : ExpandedPathSystem G Q) : RawPathSystem G Q where
  chains := S.chains
  paths := S.paths
  disjoint := S.disjoint
  endpoints := S.endpoints
  no_clique_steps := S.no_clique_steps
@[simp] theorem toRaw_amount (S : ExpandedPathSystem G Q) : S.toRaw.amount = S.amount := rfl
@[simp] theorem toRaw_assignedCount (S : ExpandedPathSystem G Q) :
    S.toRaw.assignedCount = S.assignedCount := S.assignedCount_eq_raw.symm
end ExpandedPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
noncomputable def completeClique (S : RawPathSystem G Q) : RawPathSystem G Q := by
  classical
  let U := Q \ S.vertices
  refine {
    chains := S.chains ++ U.toList.map (fun v => [v])
    paths := ?_
    disjoint := ?_
    endpoints := ?_
    no_clique_steps := ?_ }
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.paths l hl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact ⟨by simp, .singleton v⟩
  · apply List.pairwise_append.mpr
    refine ⟨S.disjoint, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      apply U.nodup_toList.imp
      intro v w hne
      simpa using hne.symm
    · intro l hl m hm
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
      apply List.disjoint_left.mpr
      intro w hw hwv
      have heq : w = v := by simpa using hwv
      subst w
      have hvU : v ∈ U := Finset.mem_toList.mp hv
      exact (Finset.mem_sdiff.mp hvU).2
        (List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hl, hw⟩))
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.endpoints l hl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      have hvQ : v ∈ Q := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
      simpa using And.intro hvQ hvQ
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact S.no_clique_steps l hl
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact .singleton v
theorem completeClique_vertices (S : RawPathSystem G Q) :
    S.completeClique.vertices = S.vertices ∪ Q := by
  classical
  ext v
  simp [vertices, completeClique]
  by_cases hv : ∃ l ∈ S.chains, v ∈ l <;> simp_all
@[simp] theorem completeClique_amount (S : RawPathSystem G Q) :
    S.completeClique.amount = S.amount := by
  classical
  unfold amount
  rw [completeClique_vertices, Finset.union_sdiff_distrib]
  simp
@[simp] theorem completeClique_assignedCount (S : RawPathSystem G Q) :
    S.completeClique.assignedCount = S.assignedCount := by
  classical
  unfold assignedCount
  change rawAssignedCount Q
    (S.chains ++ (Q \ S.vertices).toList.map (fun v => [v])) = _
  rw [rawAssignedCount_append]
  suffices h : rawAssignedCount Q ((Q \ S.vertices).toList.map (fun v => [v])) = 0 by
    simp [h]
  unfold rawAssignedCount
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
  have hvQ := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
  simp [chainCliqueCount, hvQ]
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
noncomputable def representativesFrom (Q : Finset V) (prev : V) : List V → List V
  | [] => []
  | x :: xs => (if prev ∈ Q then [x] else []) ++ representativesFrom Q x xs
noncomputable def chainRepresentatives (Q : Finset V) : List V → List V
  | [] => []
  | x :: xs => x :: representativesFrom Q x xs
theorem representativesFrom_sublist (prev : V) (xs : List V) :
    (representativesFrom Q prev xs).Sublist xs := by
  induction xs generalizing prev with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [representativesFrom]
    split_ifs
    · simpa using (ih x).cons_cons x
    · simpa using (ih x).cons x
theorem chainRepresentatives_sublist (l : List V) : (chainRepresentatives Q l).Sublist l := by
  cases l with
  | nil => exact .refl _
  | cons x xs => exact (representativesFrom_sublist x xs).cons_cons x
@[simp] theorem chainCliqueCount_cons (x : V) (xs : List V) :
    chainCliqueCount Q (x :: xs) = (if x ∈ Q then 1 else 0) + chainCliqueCount Q xs := by
  simp [chainCliqueCount, List.filter_cons]
  split_ifs <;> simp [Nat.add_comm]
theorem representativesFrom_length (prev : V) (xs : List V)
    (hlast : ∀ v ∈ (prev :: xs).getLast?, v ∈ Q) :
    (representativesFrom Q prev xs).length + 1 = chainCliqueCount Q (prev :: xs) := by
  induction xs generalizing prev with
  | nil =>
    have hp : prev ∈ Q := hlast prev (by simp)
    simp [representativesFrom, chainCliqueCount, hp]
  | cons x xs ih =>
    have hi := ih x (by simpa using hlast)
    rw [representativesFrom, List.length_append, chainCliqueCount_cons]
    have hlen : (if prev ∈ Q then [x] else []).length = (if prev ∈ Q then 1 else 0) := by
      split_ifs <;> rfl
    rw [hlen]
    omega
theorem chainRepresentatives_length (l : List V)
    (hlast : ∀ v ∈ l.getLast?, v ∈ Q) :
    (chainRepresentatives Q l).length = chainCliqueCount Q l := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simpa only [chainRepresentatives, List.length_cons] using representativesFrom_length x xs hlast
namespace RawPathSystem
variable {G : SimpleGraph V}
noncomputable def representatives (S : RawPathSystem G Q) : List V :=
  (S.chains.map (chainRepresentatives Q)).flatten
theorem representatives_sublist (S : RawPathSystem G Q) :
    S.representatives.Sublist S.chains.flatten := by
  have h : ∀ C : List (List V),
      (C.map (chainRepresentatives Q)).flatten.Sublist C.flatten := by
    intro C
    induction C with
    | nil => exact .refl _
    | cons l C ih =>
      exact (chainRepresentatives_sublist l).append ih
  exact h S.chains
theorem representatives_nodup (S : RawPathSystem G Q) : S.representatives.Nodup :=
  S.flatten_nodup.sublist S.representatives_sublist
theorem representatives_length (S : RawPathSystem G Q) :
    S.representatives.length = chainCliqueCount Q S.chains.flatten := by
  rw [chainCliqueCount_flatten]
  unfold representatives
  rw [List.length_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  exact chainRepresentatives_length l (S.endpoints l hl).2
theorem completeClique_representatives_length (S : RawPathSystem G Q) :
    S.completeClique.representatives.length = Q.card := by
  rw [representatives_length]
  have hnd := S.completeClique.flatten_nodup.filter (fun v => decide (v ∈ Q))
  have hset : (S.completeClique.chains.flatten.filter (fun v => decide (v ∈ Q))).toFinset = Q := by
    ext v
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hv
      constructor
      · have hm : v ∈ S.completeClique.vertices := by
          rw [completeClique_vertices]
          exact Finset.mem_union_right _ hv
        exact List.mem_toFinset.mp hm
      · exact hv
  unfold chainCliqueCount
  rw [← List.toFinset_card_of_nodup hnd, hset]
end RawPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
def RepCut (Q : Finset V) (l : List V) (x : V) : Prop :=
  ∃ A B : List V, l = A ++ x :: B ∧ ∀ v ∈ A.getLast?, v ∈ Q
theorem representativesFrom_mem_cut {prev x : V} {xs : List V}
    (hx : x ∈ representativesFrom Q prev xs) :
    ∃ A B : List V, prev :: xs = A ++ x :: B ∧
      (∀ v ∈ A.getLast?, v ∈ Q) ∧ A ≠ [] := by
  induction xs generalizing prev with
  | nil => simp [representativesFrom] at hx
  | cons z zs ih =>
    simp only [representativesFrom, List.mem_append] at hx
    by_cases hp : prev ∈ Q
    · simp only [hp, ↓reduceIte, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact ⟨[prev], zs, rfl, by simpa using hp, by simp⟩
      · obtain ⟨A, B, hEq, hA, hne⟩ := ih hx
        refine ⟨prev :: A, B, by simpa using congrArg (List.cons prev) hEq, ?_, by simp⟩
        cases A with
        | nil => exact False.elim (hne rfl)
        | cons a A => simpa using hA
    · simp only [hp, ↓reduceIte, List.not_mem_nil, false_or] at hx
      obtain ⟨A, B, hEq, hA, hne⟩ := ih hx
      refine ⟨prev :: A, B, by simpa using congrArg (List.cons prev) hEq, ?_, by simp⟩
      cases A with
      | nil => exact False.elim (hne rfl)
      | cons a A => simpa using hA
theorem chainRepresentatives_mem_cut {l : List V} {x : V}
    (hx : x ∈ chainRepresentatives Q l) : RepCut Q l x := by
  cases l with
  | nil => simp [chainRepresentatives] at hx
  | cons prev xs =>
    simp only [chainRepresentatives, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨[], xs, rfl, by simp⟩
    · obtain ⟨A, B, he, hA, _⟩ := representativesFrom_mem_cut hx
      exact ⟨A, B, he, hA⟩
private theorem cut_ordered_of_later {l A C D : List V} {x y : V}
    (hnd : l.Nodup) (hx : l = A ++ x :: C ++ y :: D)
    (hy : RepCut Q l y) (hA : ∀ v ∈ A.getLast?, v ∈ Q) :
    ∃ A' B' D' : List V, l = A' ++ (x :: B') ++ y :: D' ∧
      (∀ v ∈ A'.getLast?, v ∈ Q) ∧
      (∀ v ∈ (x :: B').getLast?, v ∈ Q) := by
  obtain ⟨E, F, he, hE⟩ := hy
  have hsplit : l = (A ++ x :: C) ++ y :: D := by simpa [List.append_assoc] using hx
  have hn : ((A ++ x :: C) ++ y :: D).Nodup := hsplit ▸ hnd
  have hny : y ∉ A ++ x :: C := by
    exact fun h => (List.nodup_append'.mp hn).2.2 h (by simp)
  have hnyD : y ∉ D := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
  have heq : (A ++ x :: C) ++ y :: D = E ++ y :: F := hsplit.symm.trans he
  have hpref := (List.append_cons_inj_of_notMem hny hnyD).mp heq
  have hlast : ∀ v ∈ (x :: C).getLast?, v ∈ Q := by
    intro v hv
    apply hE v
    rw [← hpref.1]
    have hs := List.getLast?_eq_some_getLast (show x :: C ≠ [] by simp)
    simpa only [List.getLast?_append, hs, Option.or] using hv
  exact ⟨A, C, D, by simpa [List.append_assoc] using hx, hA, hlast⟩
theorem repCuts_ordered {l : List V} {x y : V} (hnd : l.Nodup) (hne : x ≠ y)
    (hx : RepCut Q l x) (hy : RepCut Q l y) :
    (∃ A B D : List V, l = A ++ (x :: B) ++ y :: D ∧
      (∀ v ∈ A.getLast?, v ∈ Q) ∧ (∀ v ∈ (x :: B).getLast?, v ∈ Q)) ∨
    (∃ A B D : List V, l = A ++ (y :: B) ++ x :: D ∧
      (∀ v ∈ A.getLast?, v ∈ Q) ∧ (∀ v ∈ (y :: B).getLast?, v ∈ Q)) := by
  obtain ⟨A, B, he, hA⟩ := hx
  have hym : y ∈ l := by obtain ⟨C, D, h, _⟩ := hy; simp [h]
  rw [he] at hym
  simp only [List.mem_append, List.mem_cons] at hym
  rcases hym with hym | hye | hym
  · obtain ⟨C, D, hC⟩ := List.append_of_mem hym
    have he' : l = C ++ y :: (D ++ x :: B) := by simp [he, hC, List.append_assoc]
    obtain ⟨E, F, hyEq, hE⟩ := hy
    have hn : (C ++ y :: (D ++ x :: B)).Nodup := he' ▸ hnd
    have hny : y ∉ C := fun h => (List.nodup_append'.mp hn).2.2 h (by simp)
    have hnytail : y ∉ D ++ x :: B := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
    have hpref := (List.append_cons_inj_of_notMem hny hnytail).mp (he'.symm.trans hyEq)
    have hCends : ∀ v ∈ C.getLast?, v ∈ Q := by simpa [hpref.1] using hE
    apply Or.inr
    exact cut_ordered_of_later (A := C) (C := D) (D := B) hnd
      (by simp [he, hC, List.append_assoc])
      ⟨A, B, he, hA⟩ hCends
  · exact False.elim (hne hye.symm)
  · obtain ⟨C, D, hC⟩ := List.append_of_mem hym
    apply Or.inl
    exact cut_ordered_of_later (A := A) (C := C) (D := D) hnd
      (by simp [he, hC, List.append_assoc]) hy hA
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
theorem representativesFrom_outside {prev : V} {xs : List V}
    (hsteps : (prev :: xs).IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∀ x ∈ representativesFrom Q prev xs, x ∉ Q := by
  induction xs generalizing prev with
  | nil => simp [representativesFrom]
  | cons y ys ih =>
    have hs := List.isChain_cons_cons.mp hsteps
    intro x hx
    simp only [representativesFrom, List.mem_append] at hx
    by_cases hp : prev ∈ Q
    · simp only [hp, ↓reduceIte, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact fun hy => hs.1 ⟨hp, hy⟩
      · exact ih hs.2 x hx
    · simp only [hp, ↓reduceIte, List.not_mem_nil, false_or] at hx
      exact ih hs.2 x hx
noncomputable def chainOutsideCount (Q : Finset V) (l : List V) : ℕ :=
  (l.filter (fun v => decide (v ∉ Q))).length
theorem chainRepresentatives_outside_count {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    chainOutsideCount Q (chainRepresentatives Q l) = chainCliqueCount Q l - 1 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ Q := hends.1 x (by simp)
    have hfilter : (representativesFrom Q x xs).filter (fun v => decide (v ∉ Q)) =
        representativesFrom Q x xs := by
      apply List.filter_eq_self.mpr
      intro v hv
      simpa using representativesFrom_outside hsteps v hv
    have hlength := representativesFrom_length x xs hends.2
    simp only [chainOutsideCount, chainRepresentatives, List.filter_cons, hx,
      not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hfilter]
    omega
namespace RawPathSystem
variable {G : SimpleGraph V}
theorem representatives_outside_count (S : RawPathSystem G Q) :
    chainOutsideCount Q S.representatives = S.assignedCount := by
  unfold chainOutsideCount representatives assignedCount rawAssignedCount
  rw [List.filter_flatten, List.length_flatten, List.map_map]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  exact chainRepresentatives_outside_count (S.endpoints l hl) (S.no_clique_steps l hl)
theorem completed_representatives_outside_count (S : ExpandedPathSystem G Q) :
    chainOutsideCount Q S.toRaw.completeClique.representatives = S.assignedCount := by
  rw [representatives_outside_count, completeClique_assignedCount,
    ExpandedPathSystem.toRaw_assignedCount]
end RawPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem amount_eq_outside_count (S : RawPathSystem G Q) :
    S.amount = chainOutsideCount Q S.chains.flatten := by
  classical
  have heq : S.vertices \ Q =
      (S.chains.flatten.filter (fun v => decide (v ∉ Q))).toFinset := by
    ext v
    simp [vertices]
    aesop
  unfold amount chainOutsideCount
  rw [heq, List.toFinset_card_of_nodup (S.flatten_nodup.filter _)]
theorem delete_assigned_path (S : RawPathSystem G Q)
    {P R : List (List V)} {A J B : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: (J ++ y :: B)) :: R)
    (hx : x ∈ Q) (hy : y ∈ Q) (hJ : ∀ z ∈ J, z ∉ Q) :
    ∃ T : RawPathSystem G Q,
      T.chains = P ++ (A ++ [x]) :: (y :: B) :: R ∧
      T.amount + J.length = S.amount ∧
      T.assignedCount + 1 = S.assignedCount ∧
      T.vertices ⊆ S.vertices := by
  classical
  let K := P ++ (A ++ [x]) :: (y :: B) :: R
  have hold : A ++ x :: (J ++ y :: B) ∈ S.chains := by simp [hsys]
  have hp : (K.flatten ++ J).Perm S.chains.flatten := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [K, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons]
    simp only [List.count_nil]
    omega
  have hflat : K.flatten.Nodup := (List.nodup_append.mp
    (hp.nodup_iff.mpr S.flatten_nodup)).1
  have hpreFull : (A ++ [x]).IsChain G.Adj := by
    have hh := (S.paths _ hold).2
    exact
      (List.isChain_append.mp (show ((A ++ [x]) ++ (J ++ y :: B)).IsChain G.Adj by
        simpa [List.append_assoc] using hh)).1
  have hsufPath : (y :: B).IsChain G.Adj := by
    exact (List.isChain_append.mp
      (List.isChain_cons.mp (List.isChain_append.mp (S.paths _ hold).2).2.1).2).2.1
  have hpreSteps : (A ++ [x]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp (show ((A ++ [x]) ++ (J ++ y :: B)).IsChain
      (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) by
        simpa [List.append_assoc] using S.no_clique_steps _ hold)).1
  have hsufSteps : (y :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp
      (List.isChain_cons.mp (List.isChain_append.mp (S.no_clique_steps _ hold)).2.1).2).2.1
  let T : RawPathSystem G Q := {
    chains := K
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact (S.paths l (by simp [hsys, hl])).2
      · exact hpreFull
      · exact hsufPath
      · exact (S.paths l (by simp [hsys, hl])).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact S.endpoints l (by simp [hsys, hl])
      · refine ⟨?_, by simpa using hx⟩
        intro v hv
        cases A with
        | nil =>
          have heq : x = v := by simpa using hv
          simpa only [heq] using hx
        | cons a A =>
          exact (S.endpoints _ hold).1 v (by simpa using hv)
      · refine ⟨by simpa using hy, ?_⟩
        intro v hv
        apply (S.endpoints _ hold).2 v
        have hh := List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp)
        rw [List.getLast?_append, List.getLast?_cons_of_ne_nil (by simp),
          List.getLast?_append, hh]
        simpa only [hh, Option.or] using hv
      · exact S.endpoints l (by simp [hsys, hl])
    no_clique_steps := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact S.no_clique_steps l (by simp [hsys, hl])
      · exact hpreSteps
      · exact hsufSteps
      · exact S.no_clique_steps l (by simp [hsys, hl]) }
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · rw [T.amount_eq_outside_count, S.amount_eq_outside_count]
    have hh := hp.filter (fun v => decide (v ∉ Q))
    have hfilter : J.filter (fun v => decide (v ∉ Q)) = J := by
      apply List.filter_eq_self.mpr
      intro v hv
      simpa using hJ v hv
    simpa only [chainOutsideCount, List.filter_append, List.length_append, hfilter] using
      hh.length_eq
  · have hxcount : chainCliqueCount Q [x] = 1 := by simp [chainCliqueCount, hx]
    have hycount : 1 ≤ chainCliqueCount Q (y :: B) :=
      chainCliqueCount_pos (by simp) (by simpa using hy)
    have hzero := chainCliqueCount_eq_zero hJ
    change rawAssignedCount Q K + 1 = rawAssignedCount Q S.chains
    simp only [K, hsys, rawAssignedCount, List.map_append, List.map_cons,
      List.sum_append, List.sum_cons, chainCliqueCount_append, hxcount]
    have heq : chainCliqueCount Q (x :: (J ++ y :: B)) =
        1 + chainCliqueCount Q (y :: B) := by
      change chainCliqueCount Q ([x] ++ (J ++ y :: B)) = _
      rw [chainCliqueCount_append, chainCliqueCount_append, hxcount, hzero, Nat.zero_add]
    rw [heq]
    omega
  · intro v hv
    change v ∈ K.flatten.toFinset at hv
    apply List.mem_toFinset.mpr
    exact hp.mem_iff.mp (List.mem_append_left _ (List.mem_toFinset.mp hv))
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
inductive AssignedAmounts (Q : Finset V) : List V → List ℕ → Prop
  | nil : AssignedAmounts Q [] []
  | singleton {x : V} (hx : x ∈ Q) : AssignedAmounts Q [x] []
  | step {x y : V} {J B : List V} {w : List ℕ}
      (hx : x ∈ Q) (hy : y ∈ Q) (hJ : ∀ z ∈ J, z ∉ Q) (hne : J ≠ [])
      (tail : AssignedAmounts Q (y :: B) w) :
      AssignedAmounts Q (x :: (J ++ y :: B)) (J.length :: w)
theorem exists_first_clique {l : List V} (h : ∃ y ∈ l, y ∈ Q) :
    ∃ J y B, l = J ++ y :: B ∧ (∀ z ∈ J, z ∉ Q) ∧ y ∈ Q := by
  classical
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x ∈ Q
    · exact ⟨[], x, xs, rfl, by simp, hx⟩
    · have ht : ∃ y ∈ xs, y ∈ Q := by
        obtain ⟨y, hy, hyQ⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hx hyQ)
        · exact ⟨y, hy, hyQ⟩
      obtain ⟨J, y, B, heq, hJ, hy⟩ := ih ht
      refine ⟨x :: J, y, B, by simp only [List.cons_append, heq], ?_, hy⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hJ z hz
theorem exists_assignedAmounts {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∃ w, AssignedAmounts Q l w := by
  classical
  suffices hh : ∀ n, ∀ l : List V, l.length = n →
      ((∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)) →
      l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)) →
      ∃ w, AssignedAmounts Q l w by
    exact hh l.length l rfl hends hsteps
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hlen hends hsteps
    cases l with
    | nil => exact ⟨[], .nil⟩
    | cons x xs =>
      have hx : x ∈ Q := hends.1 x (by simp)
      by_cases hxs : xs = []
      · subst xs
        exact ⟨[], .singleton hx⟩
      · have hlast : xs.getLast hxs ∈ Q := by
          apply hends.2
          rw [List.getLast?_cons_of_ne_nil hxs]
          exact List.getLast?_eq_some_getLast hxs
        obtain ⟨J, y, B, heq, hJ, hy⟩ :=
          exists_first_clique ⟨xs.getLast hxs, List.getLast_mem hxs, hlast⟩
        have hJne : J ≠ [] := by
          intro he
          subst J
          simp only [List.nil_append] at heq
          subst xs
          exact (List.isChain_cons_cons.mp hsteps).1 ⟨hx, hy⟩
        have hsmall : (y :: B).length < n := by
          simp only [List.length_cons, heq, List.length_append] at hlen
          simp only [List.length_cons]
          omega
        have htends : (∀ v ∈ (y :: B).head?, v ∈ Q) ∧
            (∀ v ∈ (y :: B).getLast?, v ∈ Q) := by
          refine ⟨by simpa using hy, ?_⟩
          intro v hv
          apply hends.2 v
          rw [List.getLast?_cons_of_ne_nil hxs, heq, List.getLast?_append,
            List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp)]
          simpa only [List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp), Option.or]
            using hv
        have htsteps : (y :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
          have hh := (List.isChain_cons.mp hsteps).2
          rw [heq] at hh
          exact (List.isChain_append.mp hh).2.1
        obtain ⟨w, hw⟩ := ih _ hsmall (y :: B) rfl htends htsteps
        refine ⟨J.length :: w, ?_⟩
        rw [heq]
        exact .step hx hy hJ hJne hw
namespace AssignedAmounts
theorem positive {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    ∀ a ∈ w, 0 < a := by
  induction h with
  | nil => simp
  | singleton => simp
  | @step x y J B w hx hy hJ hne ht ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact List.length_pos_iff.mpr hne
    · exact ih a ha
theorem sum_eq {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    w.sum = chainOutsideCount Q l := by
  induction h with
  | nil => rfl
  | singleton hx => simp [chainOutsideCount, hx]
  | @step x y J B w hx hy hJ hne ht ih =>
    have hfilter : J.filter (fun z => decide (z ∉ Q)) = J := by
      apply List.filter_eq_self.mpr
      intro z hz
      simpa using hJ z hz
    simp only [List.sum_cons, chainOutsideCount, List.filter_cons, hx,
      not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
      List.filter_append, List.length_append, hfilter] at ih ⊢
    rw [ih]
theorem length_eq {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    w.length = chainCliqueCount Q l - 1 := by
  induction h with
  | nil => rfl
  | singleton hx => simp [chainCliqueCount, hx]
  | @step x y J B w hx hy hJ hne ht ih =>
    have hzero := chainCliqueCount_eq_zero hJ
    have hxcount : chainCliqueCount Q [x] = 1 := by simp [chainCliqueCount, hx]
    have hypos : 1 ≤ chainCliqueCount Q (y :: B) :=
      chainCliqueCount_pos (by simp) (by simpa using hy)
    change (_ :: _).length = chainCliqueCount Q ([x] ++ (J ++ y :: B)) - 1
    rw [chainCliqueCount_append, chainCliqueCount_append, hxcount, hzero]
    simp only [List.length_cons]
    omega
end AssignedAmounts
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.AssignedAmounts
open scoped Classical
variable {V : Type*} {Q : Finset V}
theorem cut {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w)
    {A B : List ℕ} {a : ℕ} (heq : w = A ++ a :: B) :
    ∃ P J R x y, l = P ++ x :: (J ++ y :: R) ∧ x ∈ Q ∧ y ∈ Q ∧
      (∀ z ∈ J, z ∉ Q) ∧ J.length = a ∧
      AssignedAmounts Q (P ++ [x]) A ∧ AssignedAmounts Q (y :: R) B := by
  induction h generalizing A B a with
  | nil => cases A <;> simp at heq
  | singleton hx => cases A <;> simp at heq
  | @step x y J R w hx hy hJ hne ht ih =>
    cases A with
    | nil =>
      have hh : J.length = a ∧ w = B := List.cons.inj heq
      obtain ⟨rfl, rfl⟩ := hh
      exact ⟨[], J, R, x, y, rfl, hx, hy, hJ, rfl, .singleton hx, ht⟩
    | cons b A =>
      have hh : J.length = b ∧ w = A ++ a :: B := List.cons.inj heq
      obtain ⟨P', J', R', x', y', heq', hx', hy', hJ', hlen', hpre, hsuf⟩ := ih hh.2
      have hpreNew : AssignedAmounts Q ((x :: (J ++ P')) ++ [x']) (J.length :: A) := by
        cases P' with
        | nil =>
          have hyx : y = x' := (List.cons.inj heq').1
          subst x'
          simpa only [List.append_nil, List.cons_append, List.nil_append] using
            (AssignedAmounts.step hx hy hJ hne hpre)
        | cons z P' =>
          have hyz : y = z := (List.cons.inj heq').1
          subst z
          simpa [List.append_assoc] using
            (AssignedAmounts.step hx hy hJ hne hpre)
      refine ⟨x :: (J ++ P'), J', R', x', y', ?_, hx', hy', hJ', hlen', ?_, hsuf⟩
      · rw [heq']
        simp only [List.cons_append, List.append_assoc]
      · simpa only [hh.1] using hpreNew
end CycleClique.Construction.AssignedAmounts
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
inductive SystemAssignedAmounts (Q : Finset V) : List (List V) → List ℕ → Prop
  | nil : SystemAssignedAmounts Q [] []
  | cons {l : List V} {C : List (List V)} {w W : List ℕ}
      (head : AssignedAmounts Q l w) (tail : SystemAssignedAmounts Q C W) :
      SystemAssignedAmounts Q (l :: C) (w ++ W)
namespace SystemAssignedAmounts
theorem exists_of_raw (S : RawPathSystem G Q) : ∃ w, SystemAssignedAmounts Q S.chains w := by
  have hex : ∀ C : List (List V), (∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q)) →
      (∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) →
      ∃ w, SystemAssignedAmounts Q C w := by
    intro C
    induction C with
    | nil => intros; exact ⟨[], .nil⟩
    | cons l C ih =>
      intro hends hsteps
      obtain ⟨w, hw⟩ := exists_assignedAmounts (hends l (by simp)) (hsteps l (by simp))
      obtain ⟨W, hW⟩ := ih (fun l hl => hends l (by simp [hl])) (fun l hl => hsteps l (by simp [hl]))
      exact ⟨w ++ W, .cons hw hW⟩
  exact hex S.chains S.endpoints S.no_clique_steps
theorem append {C D : List (List V)} {w W : List ℕ}
    (hC : SystemAssignedAmounts Q C w) (hD : SystemAssignedAmounts Q D W) :
    SystemAssignedAmounts Q (C ++ D) (w ++ W) := by
  induction hC with
  | nil => simpa using hD
  | cons h ht ih => simpa only [List.cons_append, List.append_assoc] using SystemAssignedAmounts.cons h ih
theorem sum_eq {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w) :
    w.sum = chainOutsideCount Q C.flatten := by
  induction h with
  | nil => rfl
  | cons hh ht ih =>
    simp only [List.sum_append, List.flatten_cons, hh.sum_eq, ih,
      chainOutsideCount, List.filter_append, List.length_append]
theorem length_eq {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w) :
    w.length = rawAssignedCount Q C := by
  induction h with
  | nil => rfl
  | cons hh ht ih =>
    simp only [List.length_append, hh.length_eq, ih, rawAssignedCount, List.map_cons, List.sum_cons]
theorem positive {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w) :
    ∀ a ∈ w, 0 < a := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hh.positive a ha
    · exact ih a ha
theorem cut {C : List (List V)} {w : List ℕ} (h : SystemAssignedAmounts Q C w)
    {A B : List ℕ} {a : ℕ} (heq : w = A ++ a :: B) :
    ∃ P R l A' B' U W,
      C = P ++ l :: R ∧ SystemAssignedAmounts Q P U ∧
      AssignedAmounts Q l (A' ++ a :: B') ∧ SystemAssignedAmounts Q R W ∧
      A = U ++ A' ∧ B = B' ++ W := by
  induction h generalizing A B a with
  | nil => cases A <;> simp at heq
  | @cons l C w W hh ht ih =>
    have htail (D : List ℕ) (hA : A = w ++ D) (hW : W = D ++ a :: B) :
        ∃ P R l' A' B' U W',
          l :: C = P ++ l' :: R ∧ SystemAssignedAmounts Q P U ∧
          AssignedAmounts Q l' (A' ++ a :: B') ∧ SystemAssignedAmounts Q R W' ∧
          A = U ++ A' ∧ B = B' ++ W' := by
      obtain ⟨P, R, l', A', B', U, W', hC, hP, hl, hR, hD, hB⟩ := ih hW
      refine ⟨l :: P, R, l', A', B', w ++ U, W', ?_, .cons hh hP, hl, hR, ?_, hB⟩
      · simp only [List.cons_append, hC]
      · rw [hA, hD, List.append_assoc]
    rcases List.append_eq_append_iff.mp heq with ⟨D, hA, hW⟩ | ⟨D, hw, hB⟩
    · exact htail D hA hW
    · cases D with
      | nil =>
        exact htail [] (by simpa using hw.symm) (by simpa using hB.symm)
      | cons b D =>
        have hb : a = b ∧ B = D ++ W := List.cons.inj hB
        obtain ⟨rfl, hB'⟩ := hb
        exact ⟨[], C, l, A, D, [], W, rfl, .nil, by simpa using hw ▸ hh, ht, rfl, hB'⟩
theorem delete_one (S : RawPathSystem G Q) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w)
    {A B : List ℕ} {a : ℕ} (heq : w = A ++ a :: B) :
    ∃ T : RawPathSystem G Q,
      SystemAssignedAmounts Q T.chains (A ++ B) ∧ T.vertices ⊆ S.vertices := by
  obtain ⟨P, R, l, A', B', U, W, hsys, hP, hl, hR, hA, hB⟩ := h.cut heq
  obtain ⟨D, J, E, x, y, hl, hx, hy, hJ, _, hpre, hsuf⟩ := hl.cut rfl
  obtain ⟨T, hT, _, _, hsub⟩ := S.delete_assigned_path (hsys.trans (by rw [hl])) hx hy hJ
  refine ⟨T, ?_, hsub⟩
  rw [hT, hA, hB]
  simpa only [List.append_assoc] using hP.append (.cons hpre (.cons hsuf hR))
theorem realize_sublist_aux {B C : List ℕ} (hBC : B.Sublist C) :
    ∀ (A : List ℕ) (S : RawPathSystem G Q),
      SystemAssignedAmounts Q S.chains (A ++ C) →
      ∃ T : RawPathSystem G Q,
        SystemAssignedAmounts Q T.chains (A ++ B) ∧ T.vertices ⊆ S.vertices := by
  induction hBC with
  | slnil => intro A S h; exact ⟨S, h, fun _ hv => hv⟩
  | @cons B C a hBC ih =>
    intro A S h
    obtain ⟨T, hT, hsub⟩ := delete_one S h rfl
    obtain ⟨U, hU, husub⟩ := ih A T hT
    exact ⟨U, hU, fun v hv => hsub (husub hv)⟩
  | @cons_cons B C a hBC ih =>
    intro A S h
    obtain ⟨T, hT, hsub⟩ := ih (A ++ [a]) S (by simpa only [List.append_assoc, List.singleton_append] using h)
    exact ⟨T, by simpa only [List.append_assoc, List.singleton_append] using hT, hsub⟩
theorem realize_sublist (S : RawPathSystem G Q) {w w' : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hsub : w'.Sublist w) :
    ∃ T : ExpandedPathSystem G Q, T.amount = w'.sum ∧ T.assignedCount = w'.length := by
  obtain ⟨T, hT, _⟩ := realize_sublist_aux hsub [] S (by simpa using h)
  refine ⟨T.normalize, ?_, ?_⟩
  · rw [RawPathSystem.normalize_amount, T.amount_eq_outside_count]
    exact hT.sum_eq.symm
  · rw [RawPathSystem.normalize_assignedCount]
    exact hT.length_eq.symm
end SystemAssignedAmounts
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {Q : Finset V}
private theorem outside_prefix_unique {J K B C : List V} {y z : V}
    (hJ : ∀ v ∈ J, v ∉ Q) (hK : ∀ v ∈ K, v ∉ Q) (hy : y ∈ Q) (hz : z ∈ Q)
    (heq : J ++ y :: B = K ++ z :: C) : J = K ∧ y = z ∧ B = C := by
  induction J generalizing K with
  | nil =>
    cases K with
    | nil => exact ⟨rfl, (List.cons.inj heq).1, (List.cons.inj heq).2⟩
    | cons k K =>
      have hyk : y = k := (List.cons.inj heq).1
      exact False.elim (hK k (by simp) (by simpa only [← hyk] using hy))
  | cons j J ih =>
    cases K with
    | nil =>
      have hjz : j = z := (List.cons.inj heq).1
      exact False.elim (hJ j (by simp) (by simpa only [hjz] using hz))
    | cons k K =>
      have hh : j = k ∧ J ++ y :: B = K ++ z :: C := List.cons.inj heq
      obtain ⟨hJK, hyz, hBC⟩ := ih (fun v hv => hJ v (by simp [hv]))
        (fun v hv => hK v (by simp [hv])) hh.2
      exact ⟨by simp [hh.1, hJK], hyz, hBC⟩
namespace AssignedAmounts
theorem equal_of_chain_eq {l l' : List V} {w w' : List ℕ}
    (h : AssignedAmounts Q l w) (h' : AssignedAmounts Q l' w') (heq : l = l') : w = w' := by
  induction h generalizing l' w' with
  | nil =>
    cases h' with
    | nil => rfl
    | singleton => simp at heq
    | step => simp at heq
  | singleton hx =>
    cases h' with
    | nil => simp at heq
    | singleton => rfl
    | @step x y J B w hx hy hJ hne ht =>
      have hh := congrArg List.length heq
      simp only [List.length_cons, List.length_append, List.length_nil] at hh
      omega
  | @step x y J B w hx hy hJ hne ht ih =>
    cases h' with
    | nil => simp at heq
    | singleton =>
      have hh := congrArg List.length heq
      simp only [List.length_cons, List.length_append, List.length_nil] at hh
      omega
    | @step x' y' K C W hx' hy' hK hKne ht' =>
      have hh : x = x' ∧ J ++ y :: B = K ++ y' :: C := List.cons.inj heq
      obtain ⟨hJK, hyy, hBC⟩ := outside_prefix_unique hJ hK hy hy' hh.2
      subst K
      subst y'
      subst C
      have hw := ih ht' rfl
      simp only [hw]
theorem unique {l : List V} {w w' : List ℕ}
    (h : AssignedAmounts Q l w) (h' : AssignedAmounts Q l w') : w = w' :=
  h.equal_of_chain_eq h' rfl
end AssignedAmounts
namespace SystemAssignedAmounts
theorem equal_of_chains_eq {C D : List (List V)} {w W : List ℕ}
    (h : SystemAssignedAmounts Q C w) (h' : SystemAssignedAmounts Q D W)
    (heq : C = D) : w = W := by
  induction h generalizing D W with
  | nil =>
    cases h' with
    | nil => rfl
    | cons => simp at heq
  | @cons l C w W hh ht ih =>
    cases h' with
    | nil => simp at heq
    | @cons l' D w' W' hh' ht' =>
      have hc := List.cons.inj heq
      rw [hh.equal_of_chain_eq hh' hc.1, ih ht' hc.2]
theorem unique {C : List (List V)} {w W : List ℕ}
    (h : SystemAssignedAmounts Q C w) (h' : SystemAssignedAmounts Q C W) : w = W :=
  h.equal_of_chains_eq h' rfl
end SystemAssignedAmounts
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def amountSequences : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | e + 1, b => [] :: (List.range b).flatMap (fun q =>
      (amountSequences e (b - (q + 1))).map (fun p => (q + 1) :: p))
theorem mem_amountSequences {e b : ℕ} {p : List ℕ} :
    p ∈ amountSequences e b ↔ p.length ≤ e ∧ p.sum ≤ b ∧ ∀ a ∈ p, 0 < a := by
  induction e generalizing b p with
  | zero =>
    simp only [amountSequences, List.mem_singleton, Nat.le_zero]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hp, _⟩
      simpa using hp
  | succ e ih =>
    cases p with
    | nil => simp [amountSequences]
    | cons a p =>
      constructor
      · intro h
        have hm : a :: p ∈ (List.range b).flatMap (fun q =>
            (amountSequences e (b - (q + 1))).map (fun p => (q + 1) :: p)) := by
          simpa only [amountSequences, List.mem_cons, List.cons_ne_nil, false_or] using h
        obtain ⟨q, hq, hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨p', hp', heq⟩ := List.mem_map.mp hm
        rcases List.cons.inj heq with ⟨rfl, rfl⟩
        obtain ⟨hlen, hsum, hpos⟩ := ih.mp hp'
        have hqb : q < b := List.mem_range.mp hq
        refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [List.sum_cons]
          omega
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · omega
          · exact hpos a ha
      · rintro ⟨hlen, hsum, hpos⟩
        have ha : 0 < a := hpos a (by simp)
        have haeq : a - 1 + 1 = a := by omega
        have hsum' : a + p.sum ≤ b := by simpa using hsum
        apply List.mem_cons.mpr
        right
        apply List.mem_flatMap.mpr
        refine ⟨a - 1, List.mem_range.mpr (by omega), List.mem_map.mpr ?_⟩
        refine ⟨p, ih.mpr ⟨?_, ?_, ?_⟩, ?_⟩
        · simp only [List.length_cons] at hlen
          omega
        · omega
        · intro c hc
          exact hpos c (by simp [hc])
        · simp [haeq]
def LexLE (a b : List ℕ) : Prop := a = b ∨ List.Lex (· < ·) a b
instance (a b : List ℕ) : Decidable (LexLE a b) := by
  unfold LexLE
  infer_instance
def pathPatterns (t b : ℕ) (first : List ℕ := []) : List (List (List ℕ)) :=
  match t with
  | 0 => [[]]
  | t + 1 =>
    ((amountSequences t b).filter (fun p => decide (LexLE first p ∧ LexLE p p.reverse))).flatMap
      (fun p => (pathPatterns (t - p.length) (b - p.sum) p).map (fun P => p :: P))
termination_by t
decreasing_by omega
def patternCount (k t : ℕ) : ℕ := (pathPatterns t (k - t)).length
def pathPatternsFuel : ℕ → ℕ → ℕ → List ℕ → List (List (List ℕ))
  | _, 0, _, _ => [[]]
  | 0, _ + 1, _, _ => []
  | f + 1, t + 1, b, first =>
    ((amountSequences t b).filter (fun p => decide (LexLE first p ∧ LexLE p p.reverse))).flatMap
      (fun p => (pathPatternsFuel f (t - p.length) (b - p.sum) p).map (fun P => p :: P))
theorem pathPatterns_eq_fuel {f t b : ℕ} {first : List ℕ} (h : t ≤ f) :
    pathPatterns t b first = pathPatternsFuel f t b first := by
  induction f generalizing t b first with
  | zero =>
    have : t = 0 := by omega
    subst t
    rw [pathPatterns, pathPatternsFuel]
  | succ f ih =>
    cases t with
    | zero => rw [pathPatterns, pathPatternsFuel]
    | succ t =>
      rw [pathPatterns, pathPatternsFuel]
      congr 1
      funext p
      rw [ih (show t - p.length ≤ f by omega)]
def patternNumberFuel : ℕ → ℕ → ℕ → List ℕ → ℕ
  | _, 0, _, _ => 1
  | 0, _ + 1, _, _ => 0
  | f + 1, t + 1, b, first =>
    (((amountSequences t b).filter (fun p => decide (LexLE first p ∧ LexLE p p.reverse))).map
      (fun p => patternNumberFuel f (t - p.length) (b - p.sum) p)).sum
theorem pathPatternsFuel_length {f t b : ℕ} {first : List ℕ} :
    (pathPatternsFuel f t b first).length = patternNumberFuel f t b first := by
  induction f generalizing t b first with
  | zero => cases t <;> rfl
  | succ f ih =>
    cases t with
    | zero => rfl
    | succ t => simp only [pathPatternsFuel, patternNumberFuel, List.length_flatMap,
        List.length_map, ih]
def amountSequenceSum : ℕ → ℕ → (List ℕ → ℕ) → ℕ
  | 0, _, F => F []
  | e + 1, b, F => F [] + ((List.range b).map (fun q =>
      amountSequenceSum e (b - (q + 1)) (fun p => F ((q + 1) :: p)))).sum
private theorem sum_flatMap_nat {α : Type*} (L : List α) (F : α → List ℕ) :
    (L.flatMap F).sum = (L.map (fun a => (F a).sum)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]
theorem amountSequenceSum_eq {e b : ℕ} {F : List ℕ → ℕ} :
    amountSequenceSum e b F = ((amountSequences e b).map F).sum := by
  induction e generalizing b F with
  | zero => simp [amountSequenceSum, amountSequences]
  | succ e ih => simp only [amountSequenceSum, amountSequences, List.map_cons,
      List.sum_cons, List.map_flatMap, sum_flatMap_nat, List.map_map, ih, Function.comp_def]
private theorem sum_map_filter {α : Type*} (L : List α) (p : α → Bool) (F : α → ℕ) :
    ((L.filter p).map F).sum = (L.map (fun a => if p a then F a else 0)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : p a <;> simp [h, ih]
def patternNumberShallow : ℕ → ℕ → ℕ → List ℕ → ℕ
  | _, 0, _, _ => 1
  | 0, _ + 1, _, _ => 0
  | f + 1, t + 1, b, first => amountSequenceSum t b (fun p =>
      if decide (LexLE first p ∧ LexLE p p.reverse)
      then patternNumberShallow f (t - p.length) (b - p.sum) p else 0)
theorem patternNumberFuel_eq_shallow {f t b : ℕ} {first : List ℕ} :
    patternNumberFuel f t b first = patternNumberShallow f t b first := by
  induction f generalizing t b first with
  | zero => cases t <;> rfl
  | succ f ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simp only [patternNumberFuel, patternNumberShallow, amountSequenceSum_eq,
        sum_map_filter, ih]
def patternVertices (P : List (List ℕ)) : ℕ := (P.map (fun p => p.length + 1)).sum
def patternAmount (P : List (List ℕ)) : ℕ := (P.map List.sum).sum
def PatternValid : List ℕ → List (List ℕ) → Prop
  | _, [] => True
  | first, p :: P =>
    LexLE first p ∧ LexLE p p.reverse ∧ (∀ a ∈ p, 0 < a) ∧ PatternValid p P
theorem mem_pathPatterns {t b : ℕ} {first : List ℕ} {P : List (List ℕ)} :
    P ∈ pathPatterns t b first ↔
      patternVertices P = t ∧ patternAmount P ≤ b ∧ PatternValid first P := by
  induction t using Nat.strong_induction_on generalizing b first P with
  | h t ih =>
    cases t with
    | zero =>
      rw [pathPatterns]
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        simp [patternVertices, patternAmount, PatternValid]
      · rintro ⟨hv, _, _⟩
        cases P with
        | nil => rfl
        | cons p P => simp [patternVertices] at hv
    | succ t =>
      rw [pathPatterns]
      cases P with
      | nil => simp [patternVertices]
      | cons p P =>
        constructor
        · intro hm
          obtain ⟨p', hp', hm⟩ := List.mem_flatMap.mp hm
          obtain ⟨P', hP', heq⟩ := List.mem_map.mp hm
          have hp'eq := (List.cons.inj heq).1
          have hP'eq := (List.cons.inj heq).2
          subst p'
          subst P'
          obtain ⟨hpseq, hporder⟩ := List.mem_filter.mp hp'
          obtain ⟨hplen, hpsum, hppos⟩ := mem_amountSequences.mp hpseq
          have hrest := (ih (t - p.length) (by omega)).mp hP'
          have horder : LexLE first p ∧ LexLE p p.reverse := of_decide_eq_true hporder
          refine ⟨?_, ?_, horder.1, horder.2, hppos, hrest.2.2⟩
          · simp only [patternVertices, List.map_cons, List.sum_cons] at *
            omega
          · simp only [patternAmount, List.map_cons, List.sum_cons] at *
            omega
        · rintro ⟨hv, hb, hvalid⟩
          have hplen : p.length ≤ t := by
            simp only [patternVertices, List.map_cons, List.sum_cons] at hv
            omega
          have hpsum : p.sum ≤ b := by
            simp only [patternAmount, List.map_cons, List.sum_cons] at hb
            omega
          obtain ⟨horder, hreverse, hpos, htail⟩ := hvalid
          apply List.mem_flatMap.mpr
          refine ⟨p, List.mem_filter.mpr ⟨mem_amountSequences.mpr ⟨hplen, hpsum, hpos⟩,
            by simp [horder, hreverse]⟩, List.mem_map.mpr ?_⟩
          refine ⟨P, (ih (t - p.length) (by omega)).mpr ⟨?_, ?_, htail⟩, rfl⟩
          · simp only [patternVertices, List.map_cons, List.sum_cons] at hv ⊢
            omega
          · simp only [patternAmount, List.map_cons, List.sum_cons] at hb ⊢
            omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
theorem exists_chain_profiles (C : List (List V))
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∃ P, List.Forall₂ (AssignedAmounts Q) C P := by
  induction C with
  | nil => exact ⟨[], .nil⟩
  | cons l C ih =>
    obtain ⟨w, hw⟩ := exists_assignedAmounts (hends l (by simp)) (hsteps l (by simp))
    obtain ⟨P, hP⟩ := ih (fun l hl => hends l (by simp [hl]))
      (fun l hl => hsteps l (by simp [hl]))
    exact ⟨w :: P, .cons hw hP⟩
namespace ChainProfiles
theorem amount {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    patternAmount P = chainOutsideCount Q C.flatten := by
  induction hp with
  | nil => rfl
  | @cons l w C P h hw ih =>
    have hs := h.sum_eq
    simp only [patternAmount, List.map_cons, List.sum_cons, List.flatten_cons,
      chainOutsideCount, List.filter_append, List.length_append] at hs ih ⊢
    omega
theorem assignedCount {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    (P.map List.length).sum = rawAssignedCount Q C := by
  induction hp with
  | nil => rfl
  | @cons l w C P h hw ih =>
    simp only [List.map_cons, List.sum_cons, rawAssignedCount] at ih ⊢
    rw [h.length_eq, ih]
theorem vertices {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P)
    (hne : ∀ l ∈ C, l ≠ [])
    (hhead : ∀ l ∈ C, ∀ v ∈ l.head?, v ∈ Q) :
    patternVertices P = chainCliqueCount Q C.flatten := by
  induction hp with
  | nil => rfl
  | @cons l w C P h hw ih =>
    have hl := h.length_eq
    have hpos := chainCliqueCount_pos (hne l (by simp)) (hhead l (by simp))
    have ht := ih (fun l hl => hne l (by simp [hl]))
      (fun l hl => hhead l (by simp [hl]))
    simp only [patternVertices, List.map_cons, List.sum_cons, List.flatten_cons,
      chainCliqueCount_append] at ht ⊢
    omega
theorem positive {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) :
    ∀ w ∈ P, ∀ a ∈ w, 0 < a := by
  induction hp with
  | nil => simp
  | @cons l w C P h hw ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.positive
    · exact ih u hu
end ChainProfiles
namespace ExpandedPathSystem
variable {G : SimpleGraph V}
theorem exists_complete_profile (S : ExpandedPathSystem G Q) :
    ∃ P : List (List ℕ),
      List.Forall₂ (AssignedAmounts Q) S.toRaw.completeClique.chains P ∧
      patternVertices P = Q.card ∧ patternAmount P = S.amount ∧
      (P.map List.length).sum = S.assignedCount ∧
      ∀ w ∈ P, ∀ a ∈ w, 0 < a := by
  obtain ⟨P, hp⟩ := exists_chain_profiles S.toRaw.completeClique.chains
    S.toRaw.completeClique.endpoints S.toRaw.completeClique.no_clique_steps
  have hnonempty : ∀ l ∈ S.toRaw.completeClique.chains, l ≠ [] := by
    intro l hl
    change l ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hl
    rcases List.mem_append.mp hl with hl | hl
    · have ht := S.nontrivial l hl
      intro he
      simp only [he, List.length_nil] at ht
      omega
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      simp
  refine ⟨P, hp, ?_, ?_, ?_, ChainProfiles.positive hp⟩
  · rw [ChainProfiles.vertices hp hnonempty
      (fun l hl => (S.toRaw.completeClique.endpoints l hl).1),
      ← S.toRaw.completeClique.representatives_length,
      S.toRaw.completeClique_representatives_length]
  · rw [ChainProfiles.amount hp, ← S.toRaw.completeClique.amount_eq_outside_count,
      RawPathSystem.completeClique_amount, toRaw_amount]
  · rw [ChainProfiles.assignedCount hp, ← RawPathSystem.assignedCount,
      RawPathSystem.completeClique_assignedCount, toRaw_assignedCount]
end ExpandedPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped BigOperators Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
namespace SystemAssignedAmounts
theorem of_profiles {C : List (List V)} {P : List (List ℕ)}
    (h : List.Forall₂ (AssignedAmounts Q) C P) :
    SystemAssignedAmounts Q C P.flatten := by
  induction h with
  | nil => exact .nil
  | cons hh ht ih => exact .cons hh ih
theorem realize_labels (S : RawPathSystem G Q) {ι : Type*}
    (labels : List ι) (wt : ι → ℕ) (hnodup : labels.Nodup)
    (h : SystemAssignedAmounts Q S.chains (labels.map wt))
    (J : Finset ι) (hJ : J ⊆ labels.toFinset) :
    ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card := by
  classical
  let K := labels.filter (fun i => decide (i ∈ J))
  have hKnodup : K.Nodup := hnodup.filter _
  have hKset : K.toFinset = J := by
    ext i
    simp only [K, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hi => ⟨List.mem_toFinset.mp (hJ hi), hi⟩⟩
  have hsub : (K.map wt).Sublist (labels.map wt) := (List.filter_sublist).map wt
  obtain ⟨T, hTa, hTe⟩ := h.realize_sublist S hsub
  refine ⟨T, ?_, ?_⟩
  · have hs := List.sum_toFinset wt hKnodup
    rw [hKset] at hs
    exact hTa.trans hs.symm
  · rw [hTe, List.length_map, ← List.toFinset_card_of_nodup hKnodup, hKset]
theorem realize_sublist_of_perm (S : RawPathSystem G Q) {w u v : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hp : w.Perm u) (hs : v.Sublist u) :
    ∃ T : ExpandedPathSystem G Q, T.amount = v.sum ∧ T.assignedCount = v.length := by
  obtain ⟨v', hvp, hvs⟩ := List.exists_perm_sublist hs hp.symm
  obtain ⟨T, hTa, hTe⟩ := h.realize_sublist S hvs
  exact ⟨T, hTa.trans hvp.sum_eq, hTe.trans hvp.length_eq⟩
theorem realize_labels_of_perm (S : RawPathSystem G Q) {ι : Type*}
    {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w)
    (labels : List ι) (wt : ι → ℕ) (hnodup : labels.Nodup)
    (hp : w.Perm (labels.map wt)) (J : Finset ι) (hJ : J ⊆ labels.toFinset) :
    ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card := by
  classical
  let K := labels.filter (fun i => decide (i ∈ J))
  have hKnodup : K.Nodup := hnodup.filter _
  have hKset : K.toFinset = J := by
    ext i
    simp only [K, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hi => ⟨List.mem_toFinset.mp (hJ hi), hi⟩⟩
  have hsub : (K.map wt).Sublist (labels.map wt) := (List.filter_sublist).map wt
  obtain ⟨T, hTa, hTe⟩ := h.realize_sublist_of_perm S hp hsub
  refine ⟨T, ?_, ?_⟩
  · have hs := List.sum_toFinset wt hKnodup
    rw [hKset] at hs
    exact hTa.trans hs.symm
  · rw [hTe, List.length_map, ← List.toFinset_card_of_nodup hKnodup, hKset]
theorem labelled_fin_range (S : RawPathSystem G Q) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) :
    ∃ wt : Fin w.length → ℕ,
      (∀ i, 0 < wt i) ∧ (∑ i, wt i) = S.amount ∧
      (∀ J : Finset (Fin w.length), ∃ T : ExpandedPathSystem G Q,
        T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card) := by
  classical
  let wt : Fin w.length → ℕ := w.get
  have hmap : (List.finRange w.length).map wt = w := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get w
  have hlabels : SystemAssignedAmounts Q S.chains ((List.finRange w.length).map wt) := by
    rw [hmap]
    exact h
  refine ⟨wt, ?_, ?_, ?_⟩
  · intro i
    exact h.positive (wt i) (List.get_mem w i)
  · have hs := List.sum_toFinset wt (List.nodup_finRange w.length)
    have hset : (List.finRange w.length).toFinset = Finset.univ := by ext i; simp
    rw [hset, hmap] at hs
    rw [hs, h.sum_eq, ← S.amount_eq_outside_count]
  · intro J
    exact hlabels.realize_labels S _ wt (List.nodup_finRange w.length) J (by intro i hi; simp only [List.mem_toFinset, List.mem_finRange])
end SystemAssignedAmounts
namespace RawPathSystem
theorem exists_labelled_amounts (S : RawPathSystem G Q) :
    ∃ e : ℕ, ∃ wt : Fin e → ℕ,
      e = S.assignedCount ∧ (∀ i, 0 < wt i) ∧ (∑ i, wt i) = S.amount ∧
      (∀ J : Finset (Fin e), ∃ T : ExpandedPathSystem G Q,
        T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card) := by
  obtain ⟨w, h⟩ := SystemAssignedAmounts.exists_of_raw S
  obtain ⟨wt, hpos, hsum, hreal⟩ := h.labelled_fin_range S
  exact ⟨w.length, wt, h.length_eq, hpos, hsum, hreal⟩
end RawPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.AssignedAmounts
open scoped Classical
variable {V : Type*} {Q : Finset V}
theorem append_segment {A J B : List V} {y : V} {w W : List ℕ}
    (hA : AssignedAmounts Q A w) (hAne : A ≠ [])
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ [])
    (hB : AssignedAmounts Q (y :: B) W) :
    AssignedAmounts Q (A ++ J ++ y :: B) (w ++ J.length :: W) := by
  have hy : y ∈ Q := by
    cases hB with
    | singleton hy => exact hy
    | step hy => exact hy
  induction hA with
  | nil => exact False.elim (hAne rfl)
  | singleton hx => simpa using AssignedAmounts.step hx hy hJ hJne hB
  | @step x z K C u hx hz hK hKne ht ih =>
    have hh := ih (by simp)
    simpa [List.append_assoc] using AssignedAmounts.step hx hz hK hKne hh
theorem reverse {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) :
    AssignedAmounts Q l.reverse w.reverse := by
  induction h with
  | nil => exact .nil
  | singleton hx => simpa using AssignedAmounts.singleton hx
  | @step x y J B w hx hy hJ hne ht ih =>
    have hrevJ : ∀ z ∈ J.reverse, z ∉ Q := by simpa using hJ
    have hh := append_segment ih (by simp) hrevJ (by simpa using hne) (.singleton hx)
    simpa [List.reverse_cons, List.reverse_append, List.append_assoc] using hh
end CycleClique.Construction.AssignedAmounts
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
namespace AssignedAmounts
theorem chain_length {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) (hne : l ≠ []) :
    l.length = w.sum + w.length + 1 := by
  induction h with
  | nil => exact False.elim (hne rfl)
  | singleton => simp
  | @step x y J B w hx hy hJ hJne ht ih =>
    have hh := ih (by simp)
    simp only [List.length_cons, List.length_append, List.sum_cons] at hh ⊢
    omega
theorem amount_two_shape {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) (hw : w = [2]) :
    ∃ q u v r, l = [q, u, v, r] ∧ q ∈ Q ∧ r ∈ Q ∧ u ∉ Q ∧ v ∉ Q := by
  cases h with
  | nil => simp at hw
  | singleton => simp at hw
  | @step q r J B w hq hr hJ hJne ht =>
    have hh : J.length = 2 ∧ w = [] := List.cons.inj hw
    obtain ⟨hlen, rfl⟩ := hh
    cases ht with
    | singleton hr =>
      obtain ⟨u, v, rfl⟩ := List.length_eq_two.mp hlen
      exact ⟨q, u, v, r, rfl, hq, hr, hJ u (by simp), hJ v (by simp)⟩
end AssignedAmounts
noncomputable def interiorRepresentatives (Q : Finset V) (l : List V) : List V :=
  (chainRepresentatives Q l).tail
noncomputable def selectedChain (Q : Finset V) (l : List V) : List V :=
  if l.length = 4 then (l.drop 1).take 2 else interiorRepresentatives Q l
theorem interiorRepresentatives_sublist (l : List V) :
    (interiorRepresentatives Q l).Sublist l :=
  (List.tail_sublist _).trans (chainRepresentatives_sublist l)
theorem interiorRepresentatives_outside {l : List V}
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∀ x ∈ interiorRepresentatives Q l, x ∉ Q := by
  cases l with
  | nil => simp [interiorRepresentatives, chainRepresentatives]
  | cons prev xs => exact representativesFrom_outside hsteps
theorem interiorRepresentatives_length {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hlast : ∀ v ∈ l.getLast?, v ∈ Q) :
    (interiorRepresentatives Q l).length = w.length := by
  rw [interiorRepresentatives, List.length_tail, chainRepresentatives_length l hlast, h.length_eq]
theorem selectedChain_sublist (l : List V) : (selectedChain Q l).Sublist l := by
  unfold selectedChain
  split_ifs
  · exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
  · exact interiorRepresentatives_sublist l
theorem twice_length_le_sum {w : List ℕ} (h : ∀ a ∈ w, 2 ≤ a) :
    2 * w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.length_cons, Nat.mul_succ, List.sum_cons]
    omega
theorem amount_profile_eq_two_of_length_four {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hl : l.length = 4) (hmin : ∀ a ∈ w, 2 ≤ a) : w = [2] := by
  have hne : l ≠ [] := by intro he; simp [he] at hl
  have hlen := h.chain_length hne
  have hbound := twice_length_le_sum hmin
  have hW : w.length = 1 := by
    by_cases hw : w = []
    · simp only [hw, List.length_nil, List.sum_nil] at hlen
      omega
    · have hp := List.length_pos_iff.mpr hw
      omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hW
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons, List.length_nil] at hlen
  have ha : a = 2 := by omega
  simp only [ha]
theorem selectedChain_outside {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∀ x ∈ selectedChain Q l, x ∉ Q := by
  unfold selectedChain
  split_ifs with hlen
  · obtain ⟨q, u, v, r, rfl, _, _, hu, hv⟩ :=
      h.amount_two_shape (amount_profile_eq_two_of_length_four h hlen hmin)
    simpa using (show ∀ x ∈ [u, v], x ∉ Q by simp [hu, hv])
  · exact interiorRepresentatives_outside hsteps
theorem selectedChain_length_bounds {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hw : w ≠ []) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hlast : ∀ v ∈ l.getLast?, v ∈ Q) :
    (selectedChain Q l).length + (if l.length = 4 then 0 else 1) = w.length + 1 ∧
      w.length + 1 + (if l.length = 4 then 0 else 1) ≤ w.sum := by
  have hlnil : l ≠ [] := by intro he; subst l; cases h; simp at hw
  have hlen := h.chain_length hlnil
  have hbound := twice_length_le_sum hmin
  have hpos := List.length_pos_iff.mpr hw
  by_cases hl : l.length = 4
  · have hW := amount_profile_eq_two_of_length_four h hl hmin
    simp [selectedChain, hl, List.length_take, hW]
  · have hsel : (selectedChain Q l).length = w.length := by
      simpa only [selectedChain, hl, ↓reduceIte] using interiorRepresentatives_length h hlast
    simp only [hl, ↓reduceIte, hsel]
    constructor
    · trivial
    · omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem terminal_increment_arithmetic {t k r j : ℕ}
    (ht : 9 ≤ t) (hk : k ≤ 2 * t + 1) (htk : t ≤ k)
    (hj : 1 ≤ j) (hj' : j ≤ 5) (hr : t + 1 ≤ 2 * r + j) :
    ¬ ((r - 1) * (j + 2) ≤ k - t) := by
  interval_cases j <;> omega
theorem terminal_classification_arithmetic {k t L e v d : ℕ}
    (ht : 9 ≤ t) (htk : t ≤ k) (hk : k ≤ 2 * t + 1)
    (hL : L = k - t) (hd : 2 ≤ d) (hd' : d ≤ 6)
    (hde : d * e ≤ L) (htv : t ≤ v + d) (hve : v ≤ 2 * e) :
    (d = 2 ∧ t ≤ v + 2) ∨
    (d = 3 ∧ (t = 9 ∨ t = 11) ∧ 2 * e = t - 3 ∧ v = t - 3) ∨
    (d = 5 ∧ t = 9 ∧ k = 19 ∧ e = 2 ∧ v = 4) := by
  interval_cases d <;> omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
structure IsOptimal (S : ExpandedPathSystem G Q) (k : ℕ) : Prop where
  budget : S.amount ≤ k - Q.card
  maximal : ∀ T : ExpandedPathSystem G Q, T.amount ≤ k - Q.card → T.amount ≤ S.amount
  minimal : ∀ T : ExpandedPathSystem G Q, T.amount = S.amount →
    S.assignedCount ≤ T.assignedCount
theorem exists_optimal (G : SimpleGraph V) (Q : Finset V) (k : ℕ) :
    ∃ S : ExpandedPathSystem G Q, S.IsOptimal k := by
  classical
  let b := k - Q.card
  have hex : ∃ d, ∃ T : ExpandedPathSystem G Q, T.amount + d = b := by
    exact ⟨b, empty G Q, by simp⟩
  obtain ⟨S₀, hS₀⟩ := Nat.find_spec hex
  have hmax : ∀ T : ExpandedPathSystem G Q, T.amount ≤ b → T.amount ≤ S₀.amount := by
    intro T hT
    have hd := Nat.find_min' hex (show ∃ S : ExpandedPathSystem G Q,
      S.amount + (b - T.amount) = b from ⟨T, Nat.add_sub_of_le hT⟩)
    omega
  have he : ∃ e, ∃ T : ExpandedPathSystem G Q,
      T.amount = S₀.amount ∧ T.assignedCount = e := ⟨S₀.assignedCount, S₀, rfl, rfl⟩
  obtain ⟨S, hSamount, hSe⟩ := Nat.find_spec he
  refine ⟨S, ⟨?_, ?_, ?_⟩⟩
  · change S.amount ≤ b
    omega
  · intro T hT
    rw [hSamount]
    exact hmax T hT
  · intro T hT
    rw [hSe]
    exact Nat.find_min' he ⟨T, hT.trans hSamount, rfl⟩
theorem incident_le (S : ExpandedPathSystem G Q) : S.incident ≤ Q.card := by
  classical
  exact Finset.card_le_card Finset.inter_subset_right
theorem IsOptimal.criterion {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (T : ExpandedPathSystem G Q)
    (hlow : S.amount + (if S.assignedCount ≤ T.assignedCount then 1 else 0) ≤ T.amount)
    (hhigh : T.amount + T.incident ≤ k + 1) : False := by
  by_cases hthreshold : k + 1 - Q.card ≤ T.amount
  · exact T.forbidden_interval hk hQ hcycle hthreshold hhigh
  have hTbudget : T.amount ≤ k - Q.card := by omega
  have hmax := hopt.maximal T hTbudget
  by_cases he : S.assignedCount ≤ T.assignedCount
  · simp only [he, ↓reduceIte] at hlow
    omega
  · simp only [he, ↓reduceIte, Nat.add_zero] at hlow
    have hamount : T.amount = S.amount := by omega
    exact he (hopt.minimal T hamount)
theorem IsOptimal.no_one_vertex_increase {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (T : ExpandedPathSystem G Q) (hinc : T.amount = S.amount + 1) : False := by
  apply hopt.criterion hk hQk hQ hcycle T
  · split_ifs <;> omega
  · have hb := hopt.budget
    have hi := T.incident_le
    omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem chain_clique_count_two (S : ExpandedPathSystem G Q) {l : List V}
    (hl : l ∈ S.chains) : 2 ≤ chainCliqueCount Q l := by
  have hlen := S.nontrivial l hl
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  let a := l.head hne
  let b := l.getLast hne
  have ha : a ∈ Q := (S.endpoints l hl).1 a (List.head?_eq_some_head hne)
  have hb : b ∈ Q := (S.endpoints l hl).2 b (List.getLast?_eq_some_getLast hne)
  have hab : a ≠ b := by
    intro he
    obtain ⟨v, hv⟩ := ((S.paths l hl).1.head_eq_getLast_iff hne).mp he
    simp [hv] at hlen
  let I := (l.filter (fun v => decide (v ∈ Q))).toFinset
  have haI : a ∈ I := by simp only [I, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]; exact ⟨List.head_mem hne, ha⟩
  have hbI : b ∈ I := by simp only [I, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]; exact ⟨List.getLast_mem hne, hb⟩
  have hc : 2 ≤ I.card := Finset.one_lt_card.mpr ⟨a, haI, b, hbI, hab⟩
  simpa only [I, List.toFinset_card_of_nodup ((S.paths l hl).1.filter _), chainCliqueCount]
    using hc
theorem chains_length_le_assignedCount (S : ExpandedPathSystem G Q) :
    S.chains.length ≤ S.assignedCount := by
  rw [S.assignedCount_eq_raw]
  have hpos : ∀ l ∈ S.chains, 1 ≤ chainCliqueCount Q l - 1 := by
    intro l hl
    have h := S.chain_clique_count_two hl
    omega
  generalize he : S.chains = C at hpos ⊢
  clear he
  induction C with
  | nil => simp [rawAssignedCount]
  | cons l C ih =>
    have hl := hpos l (by simp)
    have hi := ih (fun l hl => hpos l (by simp [hl]))
    simp only [List.length_cons, rawAssignedCount, List.map_cons, List.sum_cons] at hi ⊢
    omega
theorem amount_eq_zero_of_assignedCount_eq_zero (S : ExpandedPathSystem G Q)
    (he : S.assignedCount = 0) : S.amount = 0 := by
  have hl := S.chains_length_le_assignedCount
  have hc : S.chains = [] := List.length_eq_zero_iff.mp (by omega)
  simp [amount, vertices, hc]
theorem assignedCount_pos_of_amount_pos (S : ExpandedPathSystem G Q)
    (hL : 0 < S.amount) : 0 < S.assignedCount := by
  by_contra hn
  have he : S.assignedCount = 0 := by omega
  have h := S.amount_eq_zero_of_assignedCount_eq_zero he
  omega
theorem incident_eq_two_of_assignedCount_one (S : ExpandedPathSystem G Q)
    (he : S.assignedCount = 1) : S.incident = 2 := by
  have hl := S.chains_length_le_assignedCount
  have hl' : S.chains.length ≤ 1 := by omega
  have hne : S.chains ≠ [] := by
    intro hc
    have hh := S.assignedCount_eq_raw
    simp [hc, rawAssignedCount] at hh
    omega
  have hcpos : 1 ≤ S.chains.length := List.length_pos_iff.mpr hne
  unfold assignedCount at he
  omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped BigOperators Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem incident_le_twice_assignedCount (S : ExpandedPathSystem G Q) :
    S.incident ≤ 2 * S.assignedCount := by
  have hh := rawAssignedCount_add_length (Q := Q) S.chains (by
    intro l hl
    have hc := S.chain_clique_count_two hl
    omega)
  rw [← S.assignedCount_eq_raw, ← S.incident_eq_chainCliqueCount] at hh
  have hc := S.chains_length_le_assignedCount
  omega
theorem IsOptimal.terminal_increment_weights {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {ι : Type*} (old : Finset ι) (new : ι) (wt : ι → ℕ) (hnew : new ∉ old)
    (holdsum : ∑ i ∈ old, wt i ≤ S.amount)
    (holdcard : old.card ≤ S.assignedCount)
    (hfull : old.card = S.assignedCount → (∑ i ∈ old, wt i) = S.amount)
    (htotal : ∑ i ∈ insert new old, wt i = S.amount + d)
    (hrealize : ∀ J ⊆ insert new old, ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card) :
    S.amount = k - Q.card ∧ old.card = S.assignedCount ∧
      (∑ i ∈ old, wt i) = S.amount ∧ wt new = d ∧
      ∀ i ∈ insert new old, d ≤ wt i := by
  classical
  let R := insert new old
  let h := k + 1 - Q.card
  have hbudget := hopt.budget
  have hLh : S.amount < h := by dsimp [h]; omega
  have hRsum : ∑ i ∈ R, wt i = S.amount + d := htotal
  have hRlarge : h ≤ ∑ i ∈ R, wt i := by
    by_contra hn
    obtain ⟨T, hTa, _⟩ := hrealize R (Finset.Subset.refl _)
    have hb : T.amount ≤ k - Q.card := by dsimp [h] at hn; omega
    have hm := hopt.maximal T hb
    omega
  have hex : ∃ r, ∃ J : Finset ι, J ⊆ R ∧ h ≤ ∑ i ∈ J, wt i ∧ J.card = r :=
    ⟨R.card, R, Finset.Subset.refl _, hRlarge, rfl⟩
  obtain ⟨J, hJR, hJh, hJcard⟩ := Nat.find_spec hex
  have hminimal : ∀ K ⊆ R, h ≤ ∑ i ∈ K, wt i → J.card ≤ K.card := by
    intro K hKR hKh
    rw [hJcard]
    exact Nat.find_min' hex ⟨K, hKR, hKh, rfl⟩
  have hdelete : ∀ i ∈ J, (∑ a ∈ J.erase i, wt a) < h := by
    intro i hi
    by_contra hn
    have hm := hminimal (J.erase i) (fun a ha => hJR (Finset.mem_of_mem_erase ha)) (by omega)
    have hc := Finset.card_erase_of_mem hi
    have hp := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hnewJ : new ∈ J := by
    by_contra hn
    have hJo : J ⊆ old := by
      intro i hi
      rcases Finset.mem_insert.mp (hJR hi) with rfl | hiold
      · exact False.elim (hn hi)
      · exact hiold
    have hs : (∑ i ∈ J, wt i) ≤ ∑ i ∈ old, wt i :=
      Finset.sum_le_sum_of_subset_of_nonneg hJo (by intros; omega)
    omega
  let j := (∑ i ∈ J, wt i) - h
  have hsumJ : ∑ i ∈ J, wt i = h + j := by dsimp [j]; omega
  have hjupper : j ≤ 5 := by
    have hs : (∑ i ∈ J, wt i) ≤ ∑ i ∈ R, wt i :=
      Finset.sum_le_sum_of_subset_of_nonneg hJR (by intros; omega)
    omega
  obtain ⟨T, hTa, hTe⟩ := hrealize J hJR
  have hinterval : k + 1 < T.amount + T.incident := by
    by_contra hn
    exact T.forbidden_interval (by omega) hQ hcycle (by dsimp [h] at hJh; omega)
      (by omega)
  have hTi := T.incident_le
  have hTtwice := T.incident_le_twice_assignedCount
  have hjpos : 1 ≤ j := by dsimp [h] at hsumJ; omega
  have hr : Q.card + 1 ≤ 2 * J.card + j := by dsimp [h] at hsumJ; omega
  have hweights : ∀ i ∈ J, j + 1 ≤ wt i := by
    intro i hi
    have hdlt := hdelete i hi
    have hs := Finset.sum_erase_add J wt hi
    omega
  have hexact : ∃ i ∈ J, wt i = j + 1 := by
    by_contra hn
    have hall : ∀ i ∈ J, j + 2 ≤ wt i := by
      intro i hi
      have hb := hweights i hi
      have hne : wt i ≠ j + 1 := by intro he; exact hn ⟨i, hi, he⟩
      omega
    have hJo : J.erase new ⊆ old := by
      intro i hi
      have hne := (Finset.mem_erase.mp hi).1
      rcases Finset.mem_insert.mp (hJR (Finset.mem_of_mem_erase hi)) with he | hiold
      · exact False.elim (hne he)
      · exact hiold
    have hsmall : (J.card - 1) * (j + 2) ≤ k - Q.card := by
      calc
        (J.card - 1) * (j + 2) = ∑ _i ∈ J.erase new, (j + 2) := by
          simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hnewJ]
        _ ≤ ∑ i ∈ J.erase new, wt i :=
          Finset.sum_le_sum (fun i (hi : i ∈ J.erase new) =>
            hall i (Finset.mem_of_mem_erase hi))
        _ ≤ ∑ i ∈ old, wt i :=
          Finset.sum_le_sum_of_subset_of_nonneg hJo (by intros; omega)
        _ ≤ S.amount := holdsum
        _ ≤ k - Q.card := hbudget
    exact terminal_increment_arithmetic ht hkQ hQk hjpos hjupper hr hsmall
  obtain ⟨i, hi, hwi⟩ := hexact
  have hdeleteSum : ∑ a ∈ J.erase i, wt a = h - 1 := by
    have hs := Finset.sum_erase_add J wt hi
    dsimp [h] at hsumJ ⊢
    omega
  obtain ⟨U, hUa, hUe⟩ := hrealize (J.erase i) (fun a ha => hJR (Finset.mem_of_mem_erase ha))
  have hUbudget : U.amount ≤ k - Q.card := by rw [hUa, hdeleteSum]; dsimp [h]; omega
  have hUmax := hopt.maximal U hUbudget
  have hL : S.amount = k - Q.card := by rw [hUa, hdeleteSum] at hUmax; dsimp [h] at hUmax; omega
  have hUeq : U.amount = S.amount := by rw [hUa, hdeleteSum, hL]; dsimp [h]; omega
  have hUmin := hopt.minimal U hUeq
  have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hJsmall : J.card ≤ old.card + 1 := by
    have hc := Finset.card_le_card hJR
    have hcR : R.card = old.card + 1 := Finset.card_insert_of_notMem hnew
    omega
  have holdEq : old.card = S.assignedCount := by
    rw [hUe, Finset.card_erase_of_mem hi] at hUmin
    omega
  have hJReq : J = R := by
    apply Finset.eq_of_subset_of_card_le hJR
    rw [hUe, Finset.card_erase_of_mem hi] at hUmin
    have hcR : R.card = old.card + 1 := Finset.card_insert_of_notMem hnew
    omega
  have holdSumEq := hfull holdEq
  have hwnew : wt new = d := by
    rw [Finset.sum_insert hnew, holdSumEq] at htotal
    omega
  have hjd : j + 1 = d := by
    rw [hJReq, hRsum] at hsumJ
    dsimp [h] at hsumJ
    omega
  refine ⟨hL, holdEq, holdSumEq, hwnew, ?_⟩
  intro a ha
  rw [← hjd]
  exact hweights a (by simpa only [hJReq] using ha)
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped BigOperators Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem IsOptimal.terminal_classification_weights {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 2 ≤ d) (hd' : d ≤ 6)
    {ι : Type*} (old : Finset ι) (new : ι) (wt : ι → ℕ) (hnew : new ∉ old)
    (holdsum : ∑ i ∈ old, wt i ≤ S.amount)
    (holdcard : old.card ≤ S.assignedCount)
    (hfull : old.card = S.assignedCount → (∑ i ∈ old, wt i) = S.amount)
    (htotal : ∑ i ∈ insert new old, wt i = S.amount + d)
    (hrealize : ∀ J ⊆ insert new old, ∃ T : ExpandedPathSystem G Q,
      T.amount = ∑ i ∈ J, wt i ∧ T.assignedCount = J.card)
    (T : ExpandedPathSystem G Q) (hTa : T.amount = S.amount + d)
    (hTi : T.incident ≤ S.incident + 2) :
    S.amount = k - Q.card ∧ (∀ i ∈ old, d ≤ wt i) ∧
      ((d = 2 ∧ Q.card ≤ S.incident + 2) ∨
       (d = 3 ∧ (Q.card = 9 ∨ Q.card = 11) ∧
         2 * S.assignedCount = Q.card - 3 ∧ S.incident = Q.card - 3) ∨
       (d = 5 ∧ Q.card = 9 ∧ k = 19 ∧ S.assignedCount = 2 ∧ S.incident = 4)) := by
  obtain ⟨hL, he, hs, _, hw⟩ := hopt.terminal_increment_weights ht hQk hkQ hQ hcycle
    (by omega) hd' old new wt hnew holdsum holdcard hfull htotal hrealize
  have hde : d * S.assignedCount ≤ S.amount := by
    calc
      d * S.assignedCount = ∑ _i ∈ old, d := by simp [he, Nat.mul_comm]
      _ ≤ ∑ i ∈ old, wt i :=
        Finset.sum_le_sum (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      _ = S.amount := hs
  have hinc : k + 1 < T.amount + T.incident := by
    by_contra hn
    exact T.forbidden_interval (by omega) hQ hcycle (by omega) (by omega)
  have htv : Q.card ≤ S.incident + d := by omega
  exact ⟨hL, fun i hi => hw i (Finset.mem_insert_of_mem hi),
    terminal_classification_arithmetic ht hQk hkQ hL hd hd' hde htv
      S.incident_le_twice_assignedCount⟩
theorem assignedCount_add_chains_length (S : ExpandedPathSystem G Q) :
    S.assignedCount + S.chains.length = S.incident := by
  have hh := rawAssignedCount_add_length (Q := Q) S.chains (by
    intro l hl
    have hc := S.chain_clique_count_two hl
    omega)
  rwa [← S.assignedCount_eq_raw, ← S.incident_eq_chainCliqueCount] at hh
theorem matching_of_incident_eq_twice (S : ExpandedPathSystem G Q)
    (hv : S.incident = 2 * S.assignedCount) :
    ∀ l ∈ S.chains, chainCliqueCount Q l = 2 := by
  have hc := S.assignedCount_add_chains_length
  have hclen : S.chains.length = S.assignedCount := by omega
  have hraw := S.assignedCount_eq_raw
  have hmin : ∀ l ∈ S.chains, 1 ≤ chainCliqueCount Q l - 1 := by
    intro l hl
    have hh := S.chain_clique_count_two hl
    omega
  have hh : ∀ C : List (List V),
      (∀ l ∈ C, 1 ≤ chainCliqueCount Q l - 1) →
      rawAssignedCount Q C = C.length →
      ∀ l ∈ C, chainCliqueCount Q l = 2 := by
    intro C
    induction C with
    | nil => simp
    | cons a C ih =>
      intro hpos heq l hl
      have ha := hpos a (by simp)
      have ht : C.length ≤ rawAssignedCount Q C := by
        have hbound : ∀ D : List (List V),
            (∀ l ∈ D, 1 ≤ chainCliqueCount Q l - 1) →
            D.length ≤ rawAssignedCount Q D := by
          intro D
          induction D with
          | nil => simp [rawAssignedCount]
          | cons b D ih =>
            intro hb
            have hbb := hb b (by simp)
            have hD := ih (fun l hl => hb l (by simp [hl]))
            simp only [List.length_cons, rawAssignedCount, List.map_cons,
              List.sum_cons] at hD ⊢
            omega
        exact hbound C (fun l hl => hpos l (by simp [hl]))
      have heq' : chainCliqueCount Q a - 1 + rawAssignedCount Q C = C.length + 1 := by
        simpa only [rawAssignedCount, List.map_cons, List.sum_cons, List.length_cons] using heq
      have haeq : chainCliqueCount Q a = 2 := by omega
      have htail : rawAssignedCount Q C = C.length := by omega
      rcases List.mem_cons.mp hl with rfl | hl
      · exact haeq
      · exact ih (fun l hl => hpos l (by simp [hl])) htail l hl
  exact hh S.chains hmin (by omega)
theorem two_chains_of_terminal_two (S : ExpandedPathSystem G Q) {k : ℕ}
    (ht : 9 ≤ Q.card) (hk : k ≤ 2 * Q.card + 1)
    (hL : S.amount = k - Q.card) (hbudget : 2 * S.assignedCount ≤ S.amount)
    (hv : Q.card ≤ S.incident + 2) : 2 ≤ S.chains.length := by
  have hc := S.assignedCount_add_chains_length
  have hzero : S.chains.length ≠ 0 := by
    intro he
    have hnil := List.length_eq_zero_iff.mp he
    have hi : S.incident = 0 := by simp [incident, vertices, hnil]
    omega
  omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
noncomputable def selectedChains (Q : Finset V) (C : List (List V)) : List V :=
  (C.map (selectedChain Q)).flatten
noncomputable def selectionLoss (C : List (List V)) : ℕ :=
  (C.map (fun l => if l.length = 4 then 0 else 1)).sum
theorem selectedChains_sublist (C : List (List V)) :
    (selectedChains Q C).Sublist C.flatten := by
  induction C with
  | nil => exact .refl _
  | cons l C ih => exact (selectedChain_sublist l).append ih
namespace SystemAssignedAmounts
theorem selected_length_bounds {C : List (List V)} {w : List ℕ}
    (h : SystemAssignedAmounts Q C w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hlen : ∀ l ∈ C, 3 ≤ l.length)
    (hlast : ∀ l ∈ C, ∀ x ∈ l.getLast?, x ∈ Q) :
    (selectedChains Q C).length + selectionLoss C = w.length + C.length ∧
      w.length + C.length + selectionLoss C ≤ w.sum := by
  induction h with
  | nil => simp [selectedChains, selectionLoss]
  | @cons l C a w ha hw ih =>
    have hla := hlen l (by simp)
    have hane : a ≠ [] := by
      intro he
      have hh := ha.chain_length (by intro he'; simp [he'] at hla)
      simp only [he, List.sum_nil, List.length_nil, zero_add] at hh
      omega
    have hb := selectedChain_length_bounds ha hane
      (fun a ha => hmin a (List.mem_append_left _ ha)) (hlast l (by simp))
    have hi := ih (fun a ha => hmin a (List.mem_append_right _ ha))
      (fun l hl => hlen l (by simp [hl])) (fun l hl => hlast l (by simp [hl]))
    simp only [selectedChains, List.map_cons, List.flatten_cons, List.length_append,
      selectionLoss, List.sum_cons, List.length_cons] at hi ⊢
    simp only [List.sum_append]
    omega
end SystemAssignedAmounts
namespace ExpandedPathSystem
theorem selectedChains_nodup (S : ExpandedPathSystem G Q) :
    (selectedChains Q S.chains).Nodup :=
  S.flatten_nodup.sublist (selectedChains_sublist S.chains)
theorem selectedChains_mem_vertices (S : ExpandedPathSystem G Q) {x : V}
    (hx : x ∈ selectedChains Q S.chains) : x ∈ S.vertices :=
  List.mem_toFinset.mpr ((selectedChains_sublist S.chains).subset hx)
theorem selectedChains_large (S : ExpandedPathSystem G Q) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hincident : S.incident = Q.card) (hamount : S.amount ≤ Q.card + 1) :
    Q.card - 1 ≤ (selectedChains Q S.chains).length := by
  have hb := h.selected_length_bounds hmin S.nontrivial (fun l hl => (S.endpoints l hl).2)
  have hsum : w.sum = S.amount := by
    rw [h.sum_eq]
    exact S.toRaw.amount_eq_outside_count.symm
  have hwlen : w.length = S.assignedCount := by
    rw [h.length_eq, S.assignedCount_eq_raw]
  have hc := S.assignedCount_add_chains_length
  rw [hwlen, hsum] at hb
  rw [hincident] at hc
  omega
end ExpandedPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem reverse_flatten_perm (C : List (List V)) :
    (C.map List.reverse).flatten.Perm C.flatten := by
  induction C with
  | nil => exact .refl _
  | cons l C ih =>
    simpa using (List.reverse_perm l).append ih
def reverseChains (S : RawPathSystem G Q) : RawPathSystem G Q where
  chains := S.chains.map List.reverse
  paths := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    refine ⟨List.nodup_reverse.mpr (S.paths r hr).1, List.isChain_reverse.mpr ?_⟩
    apply (S.paths r hr).2.imp
    intro a b h
    exact h.symm
  disjoint := (List.nodup_flatten.mp
    ((reverse_flatten_perm S.chains).nodup_iff.mpr S.flatten_nodup)).2
  endpoints := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    simpa only [List.head?_reverse, List.getLast?_reverse] using (S.endpoints r hr).symm
  no_clique_steps := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    apply List.isChain_reverse.mpr
    apply (S.no_clique_steps r hr).imp
    intro a b h hab
    exact h hab.symm
@[simp] theorem reverseChains_vertices (S : RawPathSystem G Q) :
    S.reverseChains.vertices = S.vertices := by
  ext v
  simp only [vertices, reverseChains, List.mem_toFinset]
  exact (reverse_flatten_perm S.chains).mem_iff
@[simp] theorem reverseChains_amount (S : RawPathSystem G Q) :
    S.reverseChains.amount = S.amount := by
  unfold amount
  rw [reverseChains_vertices]
theorem chain_head_representative (S : RawPathSystem G Q) {l : List V} (hl : l ∈ S.chains)
    {x : V} (hx : x ∈ l.head?) : x ∈ S.representatives := by
  apply List.mem_flatten.mpr
  refine ⟨chainRepresentatives Q l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
  cases l with
  | nil => simp at hx
  | cons a l =>
    have he : a = x := by simpa using hx
    simp [chainRepresentatives, he]
theorem reversed_terminal_representative (S : RawPathSystem G Q)
    {l : List V} (hl : l ∈ S.chains) {x : V} (hx : x ∈ l.getLast?) :
    x ∈ S.reverseChains.representatives := by
  apply chain_head_representative S.reverseChains
    (List.mem_map.mpr ⟨l, hl, rfl⟩ : l.reverse ∈ S.reverseChains.chains)
  simpa only [List.head?_reverse] using hx
theorem completed_unused_representative (S : ExpandedPathSystem G Q) {x : V}
    (hxQ : x ∈ Q) (hxS : x ∉ S.vertices) :
    x ∈ S.toRaw.completeClique.representatives ∧
      x ∈ S.toRaw.completeClique.reverseChains.representatives := by
  have hmem : [x] ∈ S.toRaw.completeClique.chains := by
    change [x] ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v])
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨x, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hxQ, hxS⟩), rfl⟩
  exact ⟨chain_head_representative _ hmem (by simp), reversed_terminal_representative _ hmem (by simp)⟩
end CycleClique.Construction.RawPathSystem
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
theorem chainRepresentatives_clique_mem_head {l : List V} {x : V}
    (hsteps : l.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hx : x ∈ chainRepresentatives Q l) (hxQ : x ∈ Q) : x ∈ l.head? := by
  cases l with
  | nil => simp [chainRepresentatives] at hx
  | cons a l =>
    simp only [chainRepresentatives, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · exact False.elim (representativesFrom_outside hsteps x hx hxQ)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
def orientedChain (p : List V → Bool) (l : List V) : List V :=
  if p l then l.reverse else l
theorem orientedChain_perm (p : List V → Bool) (l : List V) :
    (orientedChain p l).Perm l := by
  unfold orientedChain
  split_ifs
  · exact List.reverse_perm l
  · exact .refl _
theorem oriented_flatten_perm (p : List V → Bool) (C : List (List V)) :
    (C.map (orientedChain p)).flatten.Perm C.flatten := by
  induction C with
  | nil => exact .refl _
  | cons l C ih =>
    exact (orientedChain_perm p l).append ih
def orientChains (S : RawPathSystem G Q) (p : List V → Bool) : RawPathSystem G Q where
  chains := S.chains.map (orientedChain p)
  paths := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    refine ⟨(orientedChain_perm p r).nodup_iff.mpr (S.paths r hr).1, ?_⟩
    unfold orientedChain
    split_ifs
    · exact List.isChain_reverse.mpr ((S.paths r hr).2.imp (fun _ _ h => h.symm))
    · exact (S.paths r hr).2
  disjoint := (List.nodup_flatten.mp
    ((oriented_flatten_perm p S.chains).nodup_iff.mpr S.flatten_nodup)).2
  endpoints := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    unfold orientedChain
    split_ifs
    · simpa only [List.head?_reverse, List.getLast?_reverse] using
        And.intro (S.endpoints r hr).2 (S.endpoints r hr).1
    · exact S.endpoints r hr
  no_clique_steps := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    unfold orientedChain
    split_ifs
    · exact List.isChain_reverse.mpr
        ((S.no_clique_steps r hr).imp (fun _ _ h h' => h h'.symm))
    · exact S.no_clique_steps r hr
@[simp] theorem orientChains_vertices (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).vertices = S.vertices := by
  ext v
  simp only [vertices, List.mem_toFinset]
  exact (oriented_flatten_perm p S.chains).mem_iff
@[simp] theorem orientChains_amount (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).amount = S.amount := by
  unfold amount
  rw [orientChains_vertices]
@[simp] theorem orientChains_assignedCount (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).assignedCount = S.assignedCount := by
  unfold assignedCount rawAssignedCount
  change ((S.chains.map (orientedChain p)).map (fun l => chainCliqueCount Q l - 1)).sum = _
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  unfold orientedChain
  split_ifs <;> simp only [chainCliqueCount_reverse]
theorem representatives_orientChains_unchanged (S : RawPathSystem G Q) {p : List V → Bool}
    {l : List V} (hl : l ∈ S.chains) (hp : p l = false) {x : V}
    (hx : x ∈ chainRepresentatives Q l) : x ∈ (S.orientChains p).representatives := by
  apply List.mem_flatten.mpr
  refine ⟨chainRepresentatives Q l, ?_, hx⟩
  apply List.mem_map.mpr
  refine ⟨l, ?_, rfl⟩
  apply List.mem_map.mpr
  exact ⟨l, hl, by simp [orientedChain, hp]⟩
theorem representatives_orientChains_terminal (S : RawPathSystem G Q) {p : List V → Bool}
    {l : List V} (hl : l ∈ S.chains) (hp : p l = true) {x : V}
    (hx : x ∈ l.getLast?) : x ∈ (S.orientChains p).representatives := by
  apply chain_head_representative (S.orientChains p) (l := l.reverse)
    (List.mem_map.mpr ⟨l, hl, by simp [orientedChain, hp]⟩)
  simpa only [List.head?_reverse] using hx
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
namespace SystemAssignedAmounts
theorem profile_of_mem {C : List (List V)} {w : List ℕ}
    (h : SystemAssignedAmounts Q C w) {l : List V} (hl : l ∈ C) :
    ∃ a, AssignedAmounts Q l a ∧ ∀ x ∈ a, x ∈ w := by
  induction h with
  | nil => simp at hl
  | @cons l' C a w ha hw ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨a, ha, fun x hx => List.mem_append_left _ hx⟩
    · obtain ⟨a', ha', hsub⟩ := ih hl
      exact ⟨a', ha', fun x hx => List.mem_append_right _ (hsub x hx)⟩
end SystemAssignedAmounts
theorem selectedChain_orientation {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hmin : ∀ a ∈ w, 2 ≤ a) {x : V}
    (hx : x ∈ selectedChain Q l) :
    ∃ b : Bool, x ∈ chainRepresentatives Q (RawPathSystem.orientedChain (fun _ => b) l) := by
  by_cases hl : l.length = 4
  · obtain ⟨q, u, v, r, rfl, hq, hr, hu, hv⟩ :=
      h.amount_two_shape (amount_profile_eq_two_of_length_four h hl hmin)
    have hx' : x = u ∨ x = v := by simpa [selectedChain] using hx
    rcases hx' with rfl | rfl
    · exact ⟨false, by simp [RawPathSystem.orientedChain, chainRepresentatives,
        representativesFrom, hq, hu, hv]⟩
    · exact ⟨true, by simp [RawPathSystem.orientedChain, chainRepresentatives,
        representativesFrom, hr, hu, hv]⟩
  · refine ⟨false, ?_⟩
    have hh : x ∈ interiorRepresentatives Q l := by simpa [selectedChain, hl] using hx
    exact List.mem_of_mem_tail hh
namespace RawPathSystem
theorem representative_of_oriented_chain (S : RawPathSystem G Q) (p : List V → Bool)
    {l : List V} (hl : l ∈ S.chains) {x : V}
    (hx : x ∈ chainRepresentatives Q (orientedChain p l)) :
    x ∈ (S.orientChains p).representatives := by
  apply List.mem_flatten.mpr
  refine ⟨chainRepresentatives Q (orientedChain p l), ?_, hx⟩
  apply List.mem_map.mpr
  refine ⟨orientedChain p l, ?_, rfl⟩
  exact List.mem_map.mpr ⟨l, hl, rfl⟩
theorem joint_orientation (S : RawPathSystem G Q) {l m : List V}
    (hl : l ∈ S.chains) (hm : m ∈ S.chains) (hne : l ≠ m)
    {x y : V} (bx by_ : Bool)
    (hx : x ∈ chainRepresentatives Q (orientedChain (fun _ => bx) l))
    (hy : y ∈ chainRepresentatives Q (orientedChain (fun _ => by_) m)) :
    ∃ p : List V → Bool, x ∈ (S.orientChains p).representatives ∧
      y ∈ (S.orientChains p).representatives := by
  classical
  let p := fun z : List V => if z = l then bx else if z = m then by_ else false
  have hpl : p l = bx := by simp [p]
  have hpm : p m = by_ := by simp [p, hne.symm]
  refine ⟨p, S.representative_of_oriented_chain p hl ?_,
    S.representative_of_oriented_chain p hm ?_⟩
  · simpa only [orientedChain, hpl] using hx
  · simpa only [orientedChain, hpm] using hy
end RawPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
structure AssignedCutProfile (Q : Finset V) (A : List V) (x : V) (B : List V) where
  before : List ℕ
  after : List ℕ
  removed : List ℕ
  lead : List V
  endpoint : V
  rest : List V
  tail_eq : x :: B = lead ++ endpoint :: rest
  outside : ∀ z ∈ lead, z ∉ Q
  endpoint_mem : endpoint ∈ Q
  before_profile : AssignedAmounts Q A before
  after_profile : AssignedAmounts Q (endpoint :: rest) after
  removed_sum : removed.sum = lead.length
  removed_eq : removed = if A = [] then [] else [lead.length]
  lead_nonempty : A ≠ [] → lead ≠ []
  removed_length : removed.length = if A = [] then 0 else 1
  full_profile : AssignedAmounts Q (A ++ x :: B) (before ++ removed ++ after)
theorem exists_assigned_cut_profile {A B : List V} {x : V}
    (hends : (∀ v ∈ (A ++ x :: B).head?, v ∈ Q) ∧
      (∀ v ∈ (A ++ x :: B).getLast?, v ∈ Q))
    (hsteps : (A ++ x :: B).IsChain (fun u v => ¬ (u ∈ Q ∧ v ∈ Q)))
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) :
    Nonempty (AssignedCutProfile Q A x B) := by
  classical
  by_cases hAne : A = []
  · subst A
    obtain ⟨w, hw⟩ := exists_assignedAmounts hends hsteps
    have hx : x ∈ Q := hends.1 x (by simp)
    exact ⟨{
      before := [], after := w, removed := [], lead := [], endpoint := x, rest := B
      tail_eq := rfl
      outside := by simp
      endpoint_mem := hx
      before_profile := .nil
      after_profile := hw
      removed_sum := rfl
      removed_eq := by simp
      lead_nonempty := by simp
      removed_length := by simp
      full_profile := by simpa using hw }⟩
  · have hx : x ∉ Q := by
      intro hx
      have hh := (List.isChain_append.mp hsteps).2.2
      exact hh (A.getLast hAne) (List.getLast?_eq_some_getLast hAne) x (by simp)
        ⟨hA _ (List.getLast?_eq_some_getLast hAne), hx⟩
    have hAends : (∀ v ∈ A.head?, v ∈ Q) ∧ (∀ v ∈ A.getLast?, v ∈ Q) := by
      refine ⟨?_, hA⟩
      intro v hv
      exact hends.1 v (List.mem_head?_append_of_mem_head? hv)
    obtain ⟨wa, hwa⟩ := exists_assignedAmounts hAends (List.isChain_append.mp hsteps).1
    have htailEnd : ∀ v ∈ (x :: B).getLast?, v ∈ Q := by
      intro v hv
      apply hends.2 v
      have he := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
      simpa only [List.getLast?_append, he, Option.or] using hv
    have hlastQ : (x :: B).getLast (by simp) ∈ Q :=
      htailEnd _ (List.getLast?_eq_some_getLast (by simp))
    obtain ⟨J, y, C, heq, hJ, hy⟩ := exists_first_clique
      ⟨(x :: B).getLast (by simp), List.getLast_mem (by simp), hlastQ⟩
    have hJne : J ≠ [] := by
      intro hj
      subst J
      have hxy : x = y := (List.cons.inj heq).1
      exact hx (by simpa only [hxy] using hy)
    have htailEnds : (∀ v ∈ (y :: C).head?, v ∈ Q) ∧
        (∀ v ∈ (y :: C).getLast?, v ∈ Q) := by
      refine ⟨by simpa using hy, ?_⟩
      intro v hv
      apply htailEnd v
      rw [heq, List.getLast?_append,
        List.getLast?_eq_some_getLast (show y :: C ≠ [] by simp)]
      simpa only [List.getLast?_eq_some_getLast (show y :: C ≠ [] by simp), Option.or] using hv
    have htailSteps : (y :: C).IsChain (fun u v => ¬ (u ∈ Q ∧ v ∈ Q)) := by
      have hh := (List.isChain_append.mp hsteps).2.1
      rw [heq] at hh
      exact (List.isChain_append.mp hh).2.1
    obtain ⟨wb, hwb⟩ := exists_assignedAmounts htailEnds htailSteps
    exact ⟨{
      before := wa, after := wb, removed := [J.length], lead := J, endpoint := y, rest := C
      tail_eq := heq
      outside := hJ
      endpoint_mem := hy
      before_profile := hwa
      after_profile := hwb
      removed_sum := by simp
      removed_eq := by simp [hAne]
      lead_nonempty := fun _ => hJne
      removed_length := by simp [hAne]
      full_profile := by
        rw [heq]
        simpa [List.append_assoc] using hwa.append_segment hAne hJ hJne hwb }⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {Q : Finset V}
namespace AssignedCutProfile
theorem reassemble {A B : List V} {x : V} (X : AssignedCutProfile Q A x B)
    (hA : A ≠ []) {w : List ℕ} (h : AssignedAmounts Q A w) :
    AssignedAmounts Q (A ++ x :: B) (w ++ X.removed ++ X.after) := by
  rw [X.tail_eq, X.removed_eq]
  simpa [hA, List.append_assoc] using
    h.append_segment hA X.outside (X.lead_nonempty hA) X.after_profile
theorem merged {A B C D J : List V} {x y : V}
    (X : AssignedCutProfile Q A x B) (Y : AssignedCutProfile Q C y D)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    AssignedAmounts Q (B.reverse ++ x :: (J ++ y :: D))
      (X.after.reverse ++ (J.length + (X.removed ++ Y.removed).sum) :: Y.after) := by
  let K := X.lead.reverse ++ J ++ Y.lead
  have hK : ∀ z ∈ K, z ∉ Q := by
    intro z hz
    simp only [K, List.mem_append, List.mem_reverse] at hz
    rcases hz with (hz | hz) | hz
    · exact X.outside z hz
    · exact hJ z hz
    · exact Y.outside z hz
  have hKne : K ≠ [] := by
    intro he
    have hn := congrArg List.length he
    simp only [K, List.length_append, List.length_reverse, List.length_nil] at hn
    have hpos := List.length_pos_iff.mpr hJne
    omega
  have hlen : K.length = J.length + (X.removed ++ Y.removed).sum := by
    simp only [K, List.length_append, List.length_reverse, List.sum_append,
      X.removed_sum, Y.removed_sum]
    omega
  have hh := X.after_profile.reverse.append_segment
    (by simp) hK hKne Y.after_profile
  have heq : B.reverse ++ x :: (J ++ y :: D) =
      (X.endpoint :: X.rest).reverse ++ K ++ Y.endpoint :: Y.rest := by
    have h0 : B.reverse ++ x :: (J ++ y :: D) = (x :: B).reverse ++ J ++ (y :: D) := by
      simp [List.append_assoc]
    rw [h0, X.tail_eq, Y.tail_eq]
    simp [K, List.reverse_append, List.append_assoc]
  rw [heq]
  simpa only [hlen] using hh
end AssignedCutProfile
theorem different_chain_profiles
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (X : AssignedCutProfile Q A x B) (Y : AssignedCutProfile Q C y D)
    {wp wm wr : List ℕ} (hP : SystemAssignedAmounts Q P wp)
    (hM : SystemAssignedAmounts Q M wm) (hR : SystemAssignedAmounts Q R wr)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q (P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R) original ∧
      SystemAssignedAmounts Q (P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R) output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  let kept := wp ++ X.before ++ X.after ++ wm ++ Y.before ++ Y.after ++ wr
  let removed := X.removed ++ Y.removed
  let original := wp ++ (X.before ++ X.removed ++ X.after) ++ wm ++
    (Y.before ++ Y.removed ++ Y.after) ++ wr
  let output := wp ++ X.before ++ wm ++ Y.before ++ X.after.reverse ++
    (J.length + removed.sum) :: (Y.after ++ wr)
  refine ⟨original, output, kept, removed, ?_, ?_, ?_, ?_⟩
  · simpa only [original, List.append_assoc] using
      hP.append ((SystemAssignedAmounts.cons X.full_profile hM).append
        (.cons Y.full_profile hR))
  · simpa only [output, removed, List.append_assoc, List.cons_append] using
      hP.append ((SystemAssignedAmounts.cons X.before_profile hM).append
        (.cons Y.before_profile (.cons (X.merged Y hJ hJne) hR)))
  · apply List.perm_iff_count.mpr
    intro a
    simp only [original, kept, removed, List.count_append]
    omega
  · apply List.perm_iff_count.mpr
    intro a
    simp only [output, kept, List.count_append, List.count_cons, List.count_reverse]
    omega
theorem same_chain_profiles
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (X : AssignedCutProfile Q A x B)
    (Y : AssignedCutProfile Q (A ++ x :: B) y D)
    {wp wr : List ℕ} (hP : SystemAssignedAmounts Q P wp)
    (hR : SystemAssignedAmounts Q R wr)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q (P ++ (A ++ (x :: B) ++ y :: D) :: R) original ∧
      SystemAssignedAmounts Q (P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R) output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  let kept := wp ++ X.before ++ X.after ++ Y.after ++ wr
  let removed := X.removed ++ Y.removed
  let original := wp ++ (X.before ++ X.removed ++ X.after ++ Y.removed ++ Y.after) ++ wr
  let output := wp ++ X.before ++ X.after.reverse ++
    (J.length + removed.sum) :: (Y.after ++ wr)
  refine ⟨original, output, kept, removed, ?_, ?_, ?_, ?_⟩
  · have hh := Y.reassemble (by simp) X.full_profile
    simpa only [original, List.append_assoc] using hP.append (.cons hh hR)
  · simpa only [output, removed, List.append_assoc, List.cons_append] using
      hP.append (.cons X.before_profile (.cons (X.merged Y hJ hJne) hR))
  · apply List.perm_iff_count.mpr
    intro a
    simp only [original, kept, removed, List.count_append]
    omega
  · apply List.perm_iff_count.mpr
    intro a
    simp only [output, kept, List.count_append, List.count_cons, List.count_reverse]
    omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem amount_union (S T : RawPathSystem G Q) {J : List V}
    (hverts : T.vertices = S.vertices ∪ J.toFinset)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q)
    (hdis : J.Disjoint S.chains.flatten) :
    T.amount = S.amount + J.length := by
  classical
  have hJdiff : J.toFinset \ Q = J.toFinset := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    apply Finset.disjoint_left.mpr
    intro v hv hvQ
    exact hJQ v (List.mem_toFinset.mp hv) hvQ
  have hdisfin : Disjoint (S.vertices \ Q) J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hv hvJ
    exact List.disjoint_left.mp hdis (List.mem_toFinset.mp hvJ)
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
  unfold amount
  rw [hverts, Finset.union_sdiff_distrib, hJdiff,
    Finset.card_union_of_disjoint hdisfin, List.toFinset_card_of_nodup hJ]
theorem replace_different_chains (S : RawPathSystem G Q)
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q,
      T.chains = P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length := by
  classical
  let merged := B.reverse ++ x :: (J ++ y :: D)
  let K := P ++ A :: M ++ C :: merged :: R
  have hold₁ : A ++ x :: B ∈ S.chains := by simp [hsys]
  have hold₂ : C ++ y :: D ∈ S.chains := by simp [hsys]
  have hremain : ∀ l, l ∈ P ∨ l ∈ M ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  have hp : K.flatten.Perm (S.chains.flatten ++ J) := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [K, merged, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons, List.count_reverse]
    omega
  have hflat : K.flatten.Nodup := hp.nodup_iff.mpr
    (S.flatten_nodup.append hJ hdis.symm)
  have hpaths₁ := List.isChain_append.mp (S.paths _ hold₁).2
  have hpaths₂ := List.isChain_append.mp (S.paths _ hold₂).2
  have hsteps₁ := List.isChain_append.mp (S.no_clique_steps _ hold₁)
  have hsteps₂ := List.isChain_append.mp (S.no_clique_steps _ hold₂)
  have hmerged : merged.IsChain G.Adj :=
    reverse_join_chain (fun _ _ h => h.symm) hpaths₁.2.1 hpaths₂.2.1 hpath
  have hmergedSteps : merged.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    reverse_join_chain (fun _ _ h h' => h h'.symm) hsteps₁.2.1 hsteps₂.2.1
      (chain_outside_interior_of_ne_nil hJpos hJQ)
  have hmergedEq : merged = (x :: B).reverse ++ J ++ (y :: D) := by
    simp [merged, List.append_assoc]
  have hhead : merged.head? = (x :: B).getLast? := by
    rw [hmergedEq, List.append_assoc,
      List.head?_append_of_ne_nil _ (by simp), List.head?_reverse]
  have hlast : merged.getLast? = (y :: D).getLast? := by
    rw [hmergedEq]
    have hyD := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simp only [List.getLast?_append, hyD, Option.or]
  let T : RawPathSystem G Q := {
    chains := K
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      simp only [K, List.mem_append, List.mem_cons, or_assoc] at hl
      rcases hl with hl | rfl | hl | rfl | rfl | hl
      · exact (S.paths l (hremain l (Or.inl hl))).2
      · exact hpaths₁.1
      · exact (S.paths l (hremain l (Or.inr (Or.inl hl)))).2
      · exact hpaths₂.1
      · exact hmerged
      · exact (S.paths l (hremain l (Or.inr (Or.inr hl)))).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons, or_assoc] at hl
      rcases hl with hl | rfl | hl | rfl | rfl | hl
      · exact S.endpoints l (hremain l (Or.inl hl))
      · refine ⟨?_, hA⟩
        intro v hv
        exact (S.endpoints _ hold₁).1 v (List.mem_head?_append_of_mem_head? hv)
      · exact S.endpoints l (hremain l (Or.inr (Or.inl hl)))
      · refine ⟨?_, hC⟩
        intro v hv
        exact (S.endpoints _ hold₂).1 v (List.mem_head?_append_of_mem_head? hv)
      · constructor
        · intro v hv
          rw [hhead] at hv
          apply (S.endpoints _ hold₁).2 v
          have hs := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
          simpa only [List.getLast?_append, hs, Option.or] using hv
        · intro v hv
          rw [hlast] at hv
          apply (S.endpoints _ hold₂).2 v
          have hs := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
          simpa only [List.getLast?_append, hs, Option.or] using hv
      · exact S.endpoints l (hremain l (Or.inr (Or.inr hl)))
    no_clique_steps := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons, or_assoc] at hl
      rcases hl with hl | rfl | hl | rfl | rfl | hl
      · exact S.no_clique_steps l (hremain l (Or.inl hl))
      · exact hsteps₁.1
      · exact S.no_clique_steps l (hremain l (Or.inr (Or.inl hl)))
      · exact hsteps₂.1
      · exact hmergedSteps
      · exact S.no_clique_steps l (hremain l (Or.inr (Or.inr hl))) }
  refine ⟨T, rfl, amount_union S T ?_ hJ hJQ hdis⟩
  ext v
  change v ∈ K.flatten.toFinset ↔ v ∈ S.chains.flatten.toFinset ∪ J.toFinset
  simp only [List.mem_toFinset, Finset.mem_union, ← List.mem_append]
  exact hp.mem_iff
theorem different_chain_count {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q)
    (hJQ : ∀ z ∈ J, z ∉ Q) :
    rawAssignedCount Q (P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R) +
        (if A = [] then 0 else 1) + (if C = [] then 0 else 1) =
      rawAssignedCount Q (P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R) + 1 := by
  have hBpos := chainCliqueCount_pos_last (show x :: B ≠ [] by simp) hB
  have hDpos := chainCliqueCount_pos_last (show y :: D ≠ [] by simp) hD
  have hJzero := chainCliqueCount_eq_zero hJQ
  have heq : B.reverse ++ x :: (J ++ y :: D) =
      (x :: B).reverse ++ J ++ (y :: D) := by simp [List.append_assoc]
  rw [heq]
  simp only [rawAssignedCount, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons, chainCliqueCount_append, chainCliqueCount_reverse, hJzero,
    Nat.add_zero]
  have hnil : chainCliqueCount Q ([] : List V) = 0 := rfl
  by_cases ha : A = []
  · by_cases hc : C = []
    · simp only [ha, hc, ↓reduceIte, hnil]
      omega
    · have hCpos := chainCliqueCount_pos_last hc hC
      simp only [ha, hc, ↓reduceIte, hnil]
      omega
  · have hApos := chainCliqueCount_pos_last ha hA
    by_cases hc : C = []
    · simp only [ha, hc, ↓reduceIte, hnil]
      omega
    · have hCpos := chainCliqueCount_pos_last hc hC
      simp only [ha, hc, ↓reduceIte]
      omega
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem replace_same_chain (S : RawPathSystem G Q)
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q,
      T.chains = P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length := by
  classical
  let merged := B.reverse ++ x :: (J ++ y :: D)
  let K := P ++ A :: merged :: R
  have hold : A ++ (x :: B) ++ y :: D ∈ S.chains := by simp [hsys]
  have hremain : ∀ l, l ∈ P ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  have hp : K.flatten.Perm (S.chains.flatten ++ J) := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [K, merged, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons, List.count_reverse]
    omega
  have hflat : K.flatten.Nodup := hp.nodup_iff.mpr
    (S.flatten_nodup.append hJ hdis.symm)
  have hp₀ := List.isChain_append.mp (S.paths _ hold).2
  have hp₁ := List.isChain_append.mp hp₀.1
  have hs₀ := List.isChain_append.mp (S.no_clique_steps _ hold)
  have hs₁ := List.isChain_append.mp hs₀.1
  have hmerged : merged.IsChain G.Adj :=
    reverse_join_chain (fun _ _ h => h.symm) hp₁.2.1 hp₀.2.1 hpath
  have hmergedSteps : merged.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    reverse_join_chain (fun _ _ h h' => h h'.symm) hs₁.2.1 hs₀.2.1
      (chain_outside_interior_of_ne_nil hJpos hJQ)
  have hmergedEq : merged = (x :: B).reverse ++ J ++ (y :: D) := by
    simp [merged, List.append_assoc]
  have hhead : merged.head? = (x :: B).getLast? := by
    rw [hmergedEq, List.append_assoc,
      List.head?_append_of_ne_nil _ (by simp), List.head?_reverse]
  have hlast : merged.getLast? = (y :: D).getLast? := by
    rw [hmergedEq]
    have hyD := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simp only [List.getLast?_append, hyD, Option.or]
  let T : RawPathSystem G Q := {
    chains := K
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact (S.paths l (hremain l (Or.inl hl))).2
      · exact hp₁.1
      · exact hmerged
      · exact (S.paths l (hremain l (Or.inr hl))).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact S.endpoints l (hremain l (Or.inl hl))
      · refine ⟨?_, hA⟩
        intro v hv
        exact (S.endpoints _ hold).1 v
          (List.mem_head?_append_of_mem_head? (List.mem_head?_append_of_mem_head? hv))
      · constructor
        · intro v hv
          rw [hhead] at hv
          exact hB v hv
        · intro v hv
          rw [hlast] at hv
          apply (S.endpoints _ hold).2 v
          have hs := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
          simpa only [List.getLast?_append, hs, Option.or] using hv
      · exact S.endpoints l (hremain l (Or.inr hl))
    no_clique_steps := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons] at hl
      rcases hl with hl | rfl | rfl | hl
      · exact S.no_clique_steps l (hremain l (Or.inl hl))
      · exact hs₁.1
      · exact hmergedSteps
      · exact S.no_clique_steps l (hremain l (Or.inr hl)) }
  refine ⟨T, rfl, amount_union S T ?_ hJ hJQ hdis⟩
  ext v
  change v ∈ K.flatten.toFinset ↔ v ∈ S.chains.flatten.toFinset ∪ J.toFinset
  simp only [List.mem_toFinset, Finset.mem_union, ← List.mem_append]
  exact hp.mem_iff
theorem same_chain_count {P R : List (List V)} {A B D J : List V} {x y : V}
    (hA : ∀ v ∈ A.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q)
    (hJQ : ∀ z ∈ J, z ∉ Q) :
    rawAssignedCount Q (P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R) +
        (if A = [] then 0 else 1) =
      rawAssignedCount Q (P ++ (A ++ (x :: B) ++ y :: D) :: R) := by
  have hBpos := chainCliqueCount_pos_last (show x :: B ≠ [] by simp) hB
  have hDpos := chainCliqueCount_pos_last (show y :: D ≠ [] by simp) hD
  have hJzero := chainCliqueCount_eq_zero hJQ
  have heq : B.reverse ++ x :: (J ++ y :: D) =
      (x :: B).reverse ++ J ++ (y :: D) := by simp [List.append_assoc]
  rw [heq]
  simp only [rawAssignedCount, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons, chainCliqueCount_append, chainCliqueCount_reverse, hJzero,
    Nat.add_zero]
  have hnil : chainCliqueCount Q ([] : List V) = 0 := rfl
  by_cases ha : A = []
  · simp only [ha, ↓reduceIte, hnil]
    omega
  · have hApos := chainCliqueCount_pos_last ha hA
    simp only [ha, ↓reduceIte]
    omega
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem exists_subchain_profile (S : RawPathSystem G Q) (C : List (List V))
    (hC : ∀ l ∈ C, l ∈ S.chains) :
    ∃ w, SystemAssignedAmounts Q C w := by
  obtain ⟨P, hP⟩ := exists_chain_profiles C
    (fun l hl => S.endpoints l (hC l hl))
    (fun l hl => S.no_clique_steps l (hC l hl))
  exact ⟨P.flatten, SystemAssignedAmounts.of_profiles hP⟩
theorem replacement_profiles_different (S T : RawPathSystem G Q)
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (htsys : T.chains = P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  have hmem₁ : A ++ x :: B ∈ S.chains := by simp [hsys]
  have hmem₂ : C ++ y :: D ∈ S.chains := by simp [hsys]
  obtain ⟨X⟩ := exists_assigned_cut_profile (S.endpoints _ hmem₁)
    (S.no_clique_steps _ hmem₁) hA
  obtain ⟨Y⟩ := exists_assigned_cut_profile (S.endpoints _ hmem₂)
    (S.no_clique_steps _ hmem₂) hC
  have hremain : ∀ l, l ∈ P ∨ l ∈ M ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  obtain ⟨wp, hp⟩ := S.exists_subchain_profile P (fun l hl => hremain l (Or.inl hl))
  obtain ⟨wm, hm⟩ := S.exists_subchain_profile M (fun l hl => hremain l (Or.inr (Or.inl hl)))
  obtain ⟨wr, hr⟩ := S.exists_subchain_profile R (fun l hl => hremain l (Or.inr (Or.inr hl)))
  obtain ⟨original, output, kept, removed, ho, ht, hop, htp⟩ :=
    different_chain_profiles X Y hp hm hr hJ hJne
  exact ⟨original, output, kept, removed, hsys.symm ▸ ho, htsys.symm ▸ ht, hop, htp⟩
theorem replacement_profiles_same (S T : RawPathSystem G Q)
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (htsys : T.chains = P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  have hmem : A ++ (x :: B) ++ y :: D ∈ S.chains := by simp [hsys]
  have hprefixEnd : ∀ v ∈ (A ++ x :: B).getLast?, v ∈ Q := by
    intro v hv
    apply hB v
    have he := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hprefixEnds : (∀ v ∈ (A ++ x :: B).head?, v ∈ Q) ∧
      (∀ v ∈ (A ++ x :: B).getLast?, v ∈ Q) := by
    refine ⟨?_, hprefixEnd⟩
    intro v hv
    exact (S.endpoints _ hmem).1 v (List.mem_head?_append_of_mem_head? hv)
  have hprefixSteps : (A ++ x :: B).IsChain (fun u v => ¬ (u ∈ Q ∧ v ∈ Q)) :=
    (List.isChain_append.mp (S.no_clique_steps _ hmem)).1
  obtain ⟨X⟩ := exists_assigned_cut_profile hprefixEnds hprefixSteps hA
  obtain ⟨Y⟩ := exists_assigned_cut_profile (S.endpoints _ hmem)
    (S.no_clique_steps _ hmem) hprefixEnd
  have hremain : ∀ l, l ∈ P ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  obtain ⟨wp, hp⟩ := S.exists_subchain_profile P (fun l hl => hremain l (Or.inl hl))
  obtain ⟨wr, hr⟩ := S.exists_subchain_profile R (fun l hl => hremain l (Or.inr hl))
  obtain ⟨original, output, kept, removed, ho, ht, hop, htp⟩ :=
    same_chain_profiles X Y hp hr hJ hJne
  exact ⟨original, output, kept, removed, hsys.symm ▸ ho, htsys.symm ▸ ht, hop, htp⟩
theorem replace_different_chains_profiled (S : RawPathSystem G Q)
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q, ∃ original output kept removed : List ℕ,
      T.chains = P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length ∧
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  obtain ⟨T, hT, hTa⟩ := S.replace_different_chains hsys hA hC hJ hJQ hJpos hdis hpath
  obtain ⟨original, output, kept, removed, ho, ht, hp, hq⟩ :=
    S.replacement_profiles_different T hsys hT hA hC hJQ hJpos
  exact ⟨T, original, output, kept, removed, hT, hTa, ho, ht, hp, hq⟩
theorem replace_same_chain_profiled (S : RawPathSystem G Q)
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q, ∃ original output kept removed : List ℕ,
      T.chains = P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length ∧
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  obtain ⟨T, hT, hTa⟩ := S.replace_same_chain hsys hA hB hJ hJQ hJpos hdis hpath
  obtain ⟨original, output, kept, removed, ho, ht, hp, hq⟩ :=
    S.replacement_profiles_same T hsys hT hA hB hJQ hJpos
  exact ⟨T, original, output, kept, removed, hT, hTa, ho, ht, hp, hq⟩
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
def restrictChains (S : RawPathSystem G Q) (C : List (List V)) (hC : C.Sublist S.chains) :
    RawPathSystem G Q where
  chains := C
  paths := fun l hl => S.paths l (hC.subset hl)
  disjoint := S.disjoint.sublist hC
  endpoints := fun l hl => S.endpoints l (hC.subset hl)
  no_clique_steps := fun l hl => S.no_clique_steps l (hC.subset hl)
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*}
def boundaryGraph (G : SimpleGraph V) (X : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (x ∉ X ∨ y ∉ X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩
def PositiveOutsidePath (G : SimpleGraph V) (X : Set V) (x y : V) (d : ℕ) : Prop :=
  ∃ p : (boundaryGraph G X).Walk x y,
    p.IsPath ∧ p.length = d + 1 ∧
    ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y
def OutsideBall (G : SimpleGraph V) (X : Set V) (x : V) (r : ℕ) : Set V :=
  {v | v ∉ X ∧ ∃ p : (boundaryGraph G X).Walk x v,
    p.length ≤ r + 1 ∧ ∀ w ∈ p.support, w ∈ X → w = x}
theorem OutsideBall.mono {G : SimpleGraph V} {X : Set V} {x : V} {r s : ℕ}
    (hrs : r ≤ s) : OutsideBall G X x r ⊆ OutsideBall G X x s := by
  rintro v ⟨hv, p, hp, hsupp⟩
  exact ⟨hv, p, by omega, hsupp⟩
theorem outsideBall_zero {G : SimpleGraph V} {X : Set V} {x v : V}
    (hx : x ∈ X) : v ∈ OutsideBall G X x 0 ↔ G.Adj x v ∧ v ∉ X := by
  constructor
  · rintro ⟨hv, p, hp, _⟩
    have hlen : p.length = 1 := by
      have hn : p.length ≠ 0 := fun h => hv (p.eq_of_length_eq_zero h ▸ hx)
      omega
    exact ⟨(p.adj_of_length_eq_one hlen).1, hv⟩
  · rintro ⟨h, hv⟩
    refine ⟨hv, (show (boundaryGraph G X).Adj x v from ⟨h, Or.inr hv⟩).toWalk, ?_, ?_⟩
    · simp
    · intro w hw hwX
      change w ∈ [x, v] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rfl
      · exact False.elim (hv hwX)
private theorem outside_path_of_walk [DecidableEq V] {G : SimpleGraph V} {X : Set V}
    {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (p : (boundaryGraph G X).Walk x y)
    (hsupp : ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y) :
    ∃ d, 1 ≤ d ∧ d + 1 ≤ p.length ∧ PositiveOutsidePath G X x y d := by
  have hzero : p.bypass.length ≠ 0 := fun h => hxy (p.bypass.eq_of_length_eq_zero h)
  have hone : p.bypass.length ≠ 1 := by
    intro h
    have hadj := p.bypass.adj_of_length_eq_one h
    rcases hadj.2 with h | h
    · exact h hx
    · exact h hy
  have htwo : 2 ≤ p.bypass.length := by omega
  refine ⟨p.bypass.length - 1, by omega, ?_, p.bypass, p.bypass_isPath, by omega, ?_⟩
  · have := p.length_bypass_le_length
    omega
  · intro v hv hvX
    exact hsupp v (p.support_bypass_subset_support hv) hvX
theorem outside_balls_separated {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) {r s : ℕ}
    (hforbid : ∀ d, 1 ≤ d → d ≤ r + s + 2 → ¬ PositiveOutsidePath G X x y d) :
    Disjoint (OutsideBall G X x r) (OutsideBall G X y s) ∧
    ∀ u ∈ OutsideBall G X x r, ∀ v ∈ OutsideBall G X y s, ¬ G.Adj u v := by
  classical
  constructor
  · apply Set.disjoint_left.mpr
    rintro z ⟨_, p, hp, hps⟩ ⟨_, q, hq, hqs⟩
    let w := p.append q.reverse
    have hsupp : ∀ v ∈ w.support, v ∈ X → v = x ∨ v = y := by
      intro v hv hvX
      rcases (SimpleGraph.Walk.mem_support_append_iff p q.reverse).mp hv with hv | hv
      · exact Or.inl (hps v hv hvX)
      · exact Or.inr (hqs v (by simpa using hv) hvX)
    obtain ⟨d, hd, hlen, hpath⟩ := outside_path_of_walk hx hy hxy w hsupp
    have hw : w.length ≤ r + s + 2 := by
      simpa [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using
        (show p.length + q.length ≤ r + s + 2 by omega)
    exact hforbid d hd (by omega) hpath
  · rintro u ⟨hu, p, hp, hps⟩ v ⟨hv, q, hq, hqs⟩ hadj
    have hedge : (boundaryGraph G X).Adj u v := ⟨hadj, Or.inl hu⟩
    let w := (p.concat hedge).append q.reverse
    have hsupp : ∀ z ∈ w.support, z ∈ X → z = x ∨ z = y := by
      intro z hz hzX
      rcases (SimpleGraph.Walk.mem_support_append_iff (p.concat hedge) q.reverse).mp hz with hz | hz
      · have hz' : z ∈ p.support ∨ z = v := by simpa using hz
        rcases hz' with hz' | rfl
        · exact Or.inl (hps z hz' hzX)
        · exact False.elim (hv hzX)
      · exact Or.inr (hqs z (by simpa using hz) hzX)
    obtain ⟨d, hd, hlen, hpath⟩ := outside_path_of_walk hx hy hxy w hsupp
    have hw : w.length ≤ r + s + 3 := by
      simpa [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_concat,
        SimpleGraph.Walk.length_reverse] using
        (show p.length + 1 + q.length ≤ r + s + 3 by omega)
    exact hforbid d hd (by omega) hpath
theorem singleton_outside_ball_separated {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) {r : ℕ}
    (hforbid : ∀ d, 1 ≤ d → d ≤ r + 1 → ¬ PositiveOutsidePath G X x y d) :
    ∀ v ∈ OutsideBall G X x r, ¬ G.Adj v y := by
  classical
  rintro v ⟨hv, p, hp, hps⟩ hadj
  have hedge : (boundaryGraph G X).Adj v y := ⟨hadj, Or.inl hv⟩
  let w := p.concat hedge
  have hsupp : ∀ z ∈ w.support, z ∈ X → z = x ∨ z = y := by
    intro z hz hzX
    have hz' : z ∈ p.support ∨ z = y := by simpa [w] using hz
    rcases hz' with hz' | rfl
    · exact Or.inl (hps z hz' hzX)
    · exact Or.inr rfl
  obtain ⟨d, hd, hlen, hpath⟩ := outside_path_of_walk hx hy hxy w hsupp
  have hw : w.length ≤ r + 2 := by simpa [w] using (show p.length + 1 ≤ r + 2 by omega)
  exact hforbid d hd (by omega) hpath
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V}
def OutsidePath (G : SimpleGraph V) (X : Set V) (x y : V) (d : ℕ) : Prop :=
  ∃ p : G.Walk x y, p.IsPath ∧ p.length = d + 1 ∧
    ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y
theorem outsidePath_zero {X : Set V} {x y : V} :
    OutsidePath G X x y 0 ↔ G.Adj x y := by
  constructor
  · rintro ⟨p, _, hp, _⟩
    exact p.adj_of_length_eq_one hp
  · intro h
    refine ⟨h.toWalk, h.isPath_toWalk, rfl, ?_⟩
    intro v hv _
    simpa using hv
theorem outsidePath_one_of_common_neighbor {X : Set V} {x y u : V}
    (hxy : x ≠ y) (hxu : G.Adj x u) (huy : G.Adj u y) (hu : u ∉ X) :
    OutsidePath G X x y 1 := by
  have hchain : [x, u, y].IsChain G.Adj := by simpa using And.intro hxu huy
  let p : G.Walk x y := SimpleGraph.Walk.ofSupport [x, u, y] (by simp) hchain
  have hsupp : p.support = [x, u, y] := SimpleGraph.Walk.support_ofSupport (by simp) hchain
  have hlen : p.length = 2 := SimpleGraph.Walk.length_ofSupport (by simp) hchain
  refine ⟨p, ?_, ?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [hsupp]
    simp [hxy, hxu.ne, huy.ne]
  · exact hlen
  · intro v hv hvX
    simp only [hsupp, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (hu hvX)
    · exact Or.inr rfl
def boundaryHom (G : SimpleGraph V) (X : Set V) : boundaryGraph G X →g G where
  toFun := id
  map_rel' := fun h => h.1
theorem PositiveOutsidePath.toOutside {X : Set V} {x y : V} {d : ℕ}
    (h : PositiveOutsidePath G X x y d) : OutsidePath G X x y d := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  let f := boundaryHom G X
  refine ⟨p.map f, hp.map Function.injective_id, ?_, ?_⟩
  · exact (SimpleGraph.Walk.length_map f p).trans hlen
  · intro v hv hvX
    have hv' : v ∈ p.support := by simpa [f, boundaryHom] using hv
    exact hsupp v hv' hvX
theorem OutsidePath.of_enlargement {X X' : Set V} {x y : V} {d : ℕ}
    (hXX' : X ⊆ X') (h : OutsidePath G X' x y d) : OutsidePath G X x y d := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  exact ⟨p, hp, hlen, fun v hv hvX => hsupp v hv (hXX' hvX)⟩
theorem OutsidePath.reverse {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) : OutsidePath G X y x d := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  refine ⟨p.reverse, hp.reverse, by simpa using hlen, ?_⟩
  intro v hv hvX
  exact (hsupp v (by simpa using hv) hvX).symm
theorem outsidePath_forbidden_enlargement {X X' : Set V} {x y : V} {d : ℕ}
    (hXX' : X ⊆ X') (h : ¬ OutsidePath G X x y d) : ¬ OutsidePath G X' x y d :=
  fun hp => h (hp.of_enlargement hXX')
theorem OutsidePath.interior {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) :
    ∃ J : List V, J.Nodup ∧ J.length = d ∧ (∀ z ∈ J, z ∉ X) ∧
      (x :: (J ++ [y])).IsChain G.Adj := by
  obtain ⟨p, hp, hlen, hsupp⟩ := h
  cases p with
  | nil => simp at hlen
  | cons hxy p =>
    let J := p.support.dropLast
    have hsuffix : J ++ [y] = p.support := by
      simpa only [J, p.getLast_support] using
        List.dropLast_concat_getLast p.support_ne_nil
    have hnd : (x :: (J ++ [y])).Nodup := by
      rw [hsuffix]
      exact hp.support_nodup
    have hJ : J.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).1
    have hJlen : J.length = d := by
      simp only [SimpleGraph.Walk.length_cons] at hlen
      simp only [J, List.length_dropLast, SimpleGraph.Walk.length_support]
      omega
    refine ⟨J, hJ, hJlen, ?_, ?_⟩
    · intro z hz hzX
      have hzsupport : z ∈ (SimpleGraph.Walk.cons hxy p).support := by
        simp only [SimpleGraph.Walk.support_cons, ← hsuffix]
        exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ hz))
      rcases hsupp z hzsupport hzX with rfl | rfl
      · exact (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hz)
      · exact List.disjoint_left.mp
          (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.2 hz (by simp)
    · rw [hsuffix]
      exact (SimpleGraph.Walk.cons hxy p).isChain_adj_support
private theorem start_not_mem_support_tail {x y : V} {p : G.Walk x y}
    (hp : p.IsPath) : x ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [← p.cons_tail_support] at hnd
  exact (List.nodup_cons.mp hnd).1
theorem hasCycle_of_required_outside_path {X : Set V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hpX : ∀ v ∈ p.support, v ∈ X)
    {d : ℕ} (houtside : OutsidePath G X x y d)
    (hlen : 2 ≤ p.length ∨ 1 ≤ d) : HasCycle G (p.length + (d + 1)) := by
  obtain ⟨q, hq, hqlen, hqX⟩ := houtside
  have hqr : q.reverse.IsPath := hq.reverse
  have hdis : p.support.tail.Disjoint q.reverse.support.tail := by
    apply List.disjoint_left.mpr
    intro v hvp hvq
    have hvp' : v ∈ p.support := List.mem_of_mem_tail hvp
    have hvq' : v ∈ q.support := by
      simpa using (List.mem_of_mem_tail hvq : v ∈ q.reverse.support)
    rcases hqX v hvq' (hpX v hvp') with rfl | rfl
    · exact start_not_mem_support_tail hp hvp
    · exact start_not_mem_support_tail hqr hvq
  have hc := hp.isCycle_append hqr hdis (by
    rcases hlen with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by simpa [hqlen] using (show 1 < d + 1 by omega)))
  have hcycle := hasCycle_of_isCycle hc
  simpa [hqlen] using hcycle
theorem required_path_forbids {X : Set V} {x y : V} {k : ℕ}
    (hk : 3 ≤ k) (hcycle : ¬ HasCycle G (k + 1))
    (p : G.Walk x y) (hp : p.IsPath) (hpX : ∀ v ∈ p.support, v ∈ X)
    (hpos : 1 ≤ p.length) (hbound : p.length ≤ k) :
    ¬ OutsidePath G X x y (k - p.length) := by
  intro h
  have hc := hasCycle_of_required_outside_path p hp hpX h
    (show 2 ≤ p.length ∨ 1 ≤ k - p.length by omega)
  exact hcycle (by convert hc using 1; omega)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
def reorder (S : RawPathSystem G Q) (C : List (List V)) (hp : C.Perm S.chains) :
    RawPathSystem G Q where
  chains := C
  paths := fun l hl => S.paths l (hp.mem_iff.mp hl)
  disjoint := (List.nodup_flatten.mp (hp.flatten.nodup_iff.mpr S.flatten_nodup)).2
  endpoints := fun l hl => S.endpoints l (hp.mem_iff.mp hl)
  no_clique_steps := fun l hl => S.no_clique_steps l (hp.mem_iff.mp hl)
@[simp] theorem reorder_vertices (S : RawPathSystem G Q) (C : List (List V))
    (hp : C.Perm S.chains) : (S.reorder C hp).vertices = S.vertices := by
  ext v
  simp only [vertices, reorder, List.mem_toFinset]
  exact hp.flatten.mem_iff
@[simp] theorem reorder_amount (S : RawPathSystem G Q) (C : List (List V))
    (hp : C.Perm S.chains) : (S.reorder C hp).amount = S.amount := by
  unfold amount
  rw [reorder_vertices]
@[simp] theorem reorder_assignedCount (S : RawPathSystem G Q) (C : List (List V))
    (hp : C.Perm S.chains) : (S.reorder C hp).assignedCount = S.assignedCount := by
  exact (hp.map (fun l => chainCliqueCount Q l - 1)).sum_eq
theorem bring_two_front (S : RawPathSystem G Q) {l m : List V}
    (hl : l ∈ S.chains) (hm : m ∈ S.chains) (hne : l ≠ m) :
    ∃ R : List (List V), (l :: m :: R).Perm S.chains := by
  have hm' : m ∈ S.chains.erase l := (List.mem_erase_of_ne hne.symm).mpr hm
  exact ⟨(S.chains.erase l).erase m,
    ((List.perm_cons_erase hm').cons l).symm.trans (List.perm_cons_erase hl).symm⟩
theorem disjoint_of_mem (S : RawPathSystem G Q) {l m : List V}
    (hl : l ∈ S.chains) (hm : m ∈ S.chains) (hne : l ≠ m) : l.Disjoint m := by
  obtain ⟨R, hp⟩ := S.bring_two_front hl hm hne
  have hnd := hp.flatten.nodup_iff.mpr S.flatten_nodup
  have hd := (List.nodup_flatten.mp hnd).2
  exact (List.pairwise_cons.mp hd).1 m (by simp)
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
noncomputable def activeCliqueCount (Q : Finset V) (l : List V) : ℕ :=
  if 3 ≤ l.length then chainCliqueCount Q l else 0
@[simp] theorem activeCliqueCount_nil : activeCliqueCount Q ([] : List V) = 0 := by
  simp [activeCliqueCount]
@[simp] theorem activeCliqueCount_singleton (x : V) : activeCliqueCount Q [x] = 0 := by
  simp [activeCliqueCount]
@[simp] theorem activeCliqueCount_reverse (l : List V) :
    activeCliqueCount Q l.reverse = activeCliqueCount Q l := by
  simp [activeCliqueCount]
theorem activeCliqueCount_add_singleton {l : List V} (hne : l ≠ [])
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    activeCliqueCount Q l + (if l.length = 1 then 1 else 0) = chainCliqueCount Q l := by
  classical
  by_cases hlen : 3 ≤ l.length
  · have hn : l.length ≠ 1 := by omega
    simp [activeCliqueCount, hlen, hn]
  · have hc := short_chainCliqueCount hne hends hsteps (by omega)
    have hall := short_chain_in_clique hends hsteps (by omega)
    have hlength : l.length = 1 := by
      cases l with
      | nil => exact False.elim (hne rfl)
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y xs =>
          exact False.elim ((List.isChain_cons_cons.mp hsteps).1
            ⟨hall x (by simp), hall y (by simp)⟩)
    simp [activeCliqueCount, hlength, hc]
namespace RawPathSystem
theorem normalize_incident (S : RawPathSystem G Q) :
    S.normalize.incident = (S.chains.map (activeCliqueCount Q)).sum := by
  rw [ExpandedPathSystem.incident_eq_chainCliqueCount, chainCliqueCount_flatten]
  change ((S.chains.filter (fun l => decide (3 ≤ l.length))).map (chainCliqueCount Q)).sum = _
  induction S.chains with
  | nil => rfl
  | cons l C ih =>
    by_cases hl : 3 ≤ l.length
    · simpa [List.filter_cons, hl, activeCliqueCount] using
        congrArg (fun n => chainCliqueCount Q l + n) ih
    · simpa [List.filter_cons, hl, activeCliqueCount] using ih
@[simp] theorem orientChains_normalize_incident (S : RawPathSystem G Q) (p : List V → Bool) :
    (S.orientChains p).normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  change ((S.chains.map (orientedChain p)).map (activeCliqueCount Q)).sum = _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  change activeCliqueCount Q (orientedChain p l) = activeCliqueCount Q l
  unfold orientedChain
  split_ifs <;> simp only [activeCliqueCount_reverse]
@[simp] theorem reorder_normalize_incident (S : RawPathSystem G Q)
    (K : List (List V)) (hp : K.Perm S.chains) :
    (S.reorder K hp).normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  exact (hp.map (activeCliqueCount Q)).sum_eq
@[simp] theorem completeClique_normalize_incident (S : RawPathSystem G Q) :
    S.completeClique.normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  change ((S.chains ++ (Q \ S.vertices).toList.map (fun v => [v])).map (activeCliqueCount Q)).sum = _
  simp [List.map_map, Function.comp_def]
end RawPathSystem
namespace ExpandedPathSystem
@[simp] theorem toRaw_normalize_incident (S : ExpandedPathSystem G Q) :
    S.toRaw.normalize.incident = S.incident := by
  rw [RawPathSystem.normalize_incident, incident_eq_chainCliqueCount, chainCliqueCount_flatten]
  change (S.chains.map (activeCliqueCount Q)).sum = _
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  simp only [activeCliqueCount, S.nontrivial l hl, ↓reduceIte]
end ExpandedPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
variable {Q₀ : Finset W} {Q : Finset V} {f : W → V}
theorem chainCliqueCount_map (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀) (l : List W) :
    chainCliqueCount Q (l.map f) = chainCliqueCount Q₀ l := by
  classical
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, chainCliqueCount_cons, hQ, ih]
theorem chainOutsideCount_map (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀) (l : List W) :
    chainOutsideCount Q (l.map f) = chainOutsideCount Q₀ l := by
  classical
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [chainOutsideCount, List.map_cons, List.filter_cons] at ih ⊢
    by_cases hx : x ∈ Q₀ <;> simp [hQ, hx] at ih ⊢ <;> omega
namespace RawPathSystem
def embed (S : RawPathSystem H Q₀) (f : W → V) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) : RawPathSystem G Q where
  chains := S.chains.map (List.map f)
  paths := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    exact ⟨(S.paths r hr).1.map hf, List.isChain_map_of_isChain f (fun _ _ h => hG h) (S.paths r hr).2⟩
  disjoint := by
    apply (List.nodup_flatten.mp ?_).2
    simpa only [← List.map_flatten] using S.flatten_nodup.map hf
  endpoints := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    constructor
    · intro v hv
      rw [List.head?_map] at hv
      obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hv
      exact (hQ w).mpr ((S.endpoints r hr).1 w hw)
    · intro v hv
      rw [List.getLast?_map] at hv
      obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hv
      exact (hQ w).mpr ((S.endpoints r hr).2 w hw)
  no_clique_steps := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    exact List.isChain_map_of_isChain f (fun _ _ hn hh =>
      hn ⟨(hQ _).mp hh.1, (hQ _).mp hh.2⟩) (S.no_clique_steps r hr)
@[simp] theorem embed_amount (S : RawPathSystem H Q₀) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (S.embed f hf hQ hG).amount = S.amount := by
  rw [amount_eq_outside_count, amount_eq_outside_count]
  change chainOutsideCount Q ((S.chains.map (List.map f)).flatten) = _
  rw [← List.map_flatten]
  exact chainOutsideCount_map hQ _
@[simp] theorem embed_assignedCount (S : RawPathSystem H Q₀) (hf : Function.Injective f)
    (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (S.embed f hf hQ hG).assignedCount = S.assignedCount := by
  change rawAssignedCount Q (S.chains.map (List.map f)) = rawAssignedCount Q₀ S.chains
  simp only [rawAssignedCount, List.map_map, Function.comp_def, chainCliqueCount_map hQ]
@[simp] theorem embed_normalize_incident (S : RawPathSystem H Q₀)
    (hf : Function.Injective f) (hQ : ∀ v, f v ∈ Q ↔ v ∈ Q₀)
    (hG : ∀ {x y}, H.Adj x y → G.Adj (f x) (f y)) :
    (S.embed f hf hQ hG).normalize.incident = S.normalize.incident := by
  rw [normalize_incident, normalize_incident]
  change ((S.chains.map (List.map f)).map (activeCliqueCount Q)).sum = _
  simp only [List.map_map, Function.comp_def, activeCliqueCount, List.length_map,
    chainCliqueCount_map hQ]
  rfl
theorem normalize_incident_le (S : RawPathSystem G Q) :
    S.normalize.incident ≤ chainCliqueCount Q S.chains.flatten := by
  rw [normalize_incident, chainCliqueCount_flatten]
  induction S.chains with
  | nil => simp
  | cons l C ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (by unfold activeCliqueCount; split_ifs <;> omega) ih
end RawPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem expand_outside_template (S : RawPathSystem G Q) {A B J : List V} {x y : V}
    (hold : (S.chains.flatten ++ (A ++ x :: y :: B)).Nodup)
    (hleft : (A ++ [x]).IsChain G.Adj) (hright : (y :: B).IsChain G.Adj)
    (hstart : ∀ v ∈ (A ++ [x]).head?, v ∈ Q)
    (hfinish : ∀ v ∈ (y :: B).getLast?, v ∈ Q)
    (hleftSteps : (A ++ [x]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hrightSteps : (y :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hJ : J.Nodup) (hJne : J ≠ []) (hJQ : ∀ v ∈ J, v ∉ Q)
    (hdis : J.Disjoint (S.chains.flatten ++ (A ++ x :: y :: B)))
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q,
      T.chains = S.chains ++ [A ++ x :: (J ++ y :: B)] ∧
      T.amount = chainOutsideCount Q (S.chains.flatten ++ (A ++ x :: y :: B)) + J.length ∧
      T.assignedCount = S.assignedCount + (chainCliqueCount Q (A ++ x :: y :: B) - 1) ∧
      T.normalize.incident ≤ chainCliqueCount Q (S.chains.flatten ++ (A ++ x :: y :: B)) := by
  classical
  let l := A ++ x :: (J ++ y :: B)
  let C := S.chains ++ [l]
  have hp : C.flatten.Perm ((S.chains.flatten ++ (A ++ x :: y :: B)) ++ J) := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [C, l, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.count_append, List.count_cons]
    omega
  have hflat : C.flatten.Nodup := hp.nodup_iff.mpr (hold.append hJ hdis.symm)
  have hleftRev : (x :: A.reverse).IsChain G.Adj := by
    simpa using List.isChain_reverse.mpr (hleft.imp (fun _ _ h => h.symm))
  have hleftRevSteps : (x :: A.reverse).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    simpa using List.isChain_reverse.mpr (hleftSteps.imp (fun _ _ h (h' : _ ∧ _) => h h'.symm))
  have hlpath : l.IsChain G.Adj := by
    simpa only [l, List.reverse_reverse] using
      reverse_join_chain (fun _ _ h => h.symm) hleftRev hright hpath
  have hlsteps : l.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    simpa only [l, List.reverse_reverse] using
      reverse_join_chain (fun _ _ h (h' : _ ∧ _) => h h'.symm) hleftRevSteps hrightSteps
        (chain_outside_interior_of_ne_nil hJne hJQ)
  have hlhead : l.head? = (A ++ [x]).head? := by
    cases A <;> rfl
  have hlrepl : l = (A ++ [x]) ++ J ++ (y :: B) := by simp [l, List.append_assoc]
  have hllast : l.getLast? = (y :: B).getLast? := by
    rw [hlrepl, List.getLast?_append,
      List.getLast?_eq_some_getLast (show y :: B ≠ [] by simp)]
    rfl
  let T : RawPathSystem G Q := {
    chains := C
    paths := by
      intro r hr
      refine ⟨(List.nodup_flatten.mp hflat).1 r hr, ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact (S.paths r hr).2
      · have he : r = l := by simpa using hr
        exact he.symm ▸ hlpath
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact S.endpoints r hr
      · have he : r = l := by simpa using hr
        subst r
        simpa only [hlhead, hllast] using And.intro hstart hfinish
    no_clique_steps := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact S.no_clique_steps r hr
      · have he : r = l := by simpa using hr
        exact he.symm ▸ hlsteps }
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · rw [T.amount_eq_outside_count]
    have hh := (hp.filter (fun v => decide (v ∉ Q))).length_eq
    have hfilter : J.filter (fun v => decide (v ∉ Q)) = J := by
      apply List.filter_eq_self.mpr
      intro v hv
      simpa using hJQ v hv
    simpa only [chainOutsideCount, List.filter_append, List.length_append, hfilter] using hh
  · change rawAssignedCount Q C = S.assignedCount + _
    have hlcount : chainCliqueCount Q l = chainCliqueCount Q (A ++ x :: y :: B) := by
      have hz := chainCliqueCount_eq_zero hJQ
      rw [hlrepl]
      simp only [chainCliqueCount_append, hz, Nat.add_zero]
      simp [chainCliqueCount_cons, Nat.add_assoc, show chainCliqueCount Q [] = 0 from rfl]
    simp only [C, rawAssignedCount, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hlcount]
    rfl
  · apply T.normalize_incident_le.trans
    have hh := (hp.filter (fun v => decide (v ∈ Q))).length_eq
    have hz := chainCliqueCount_eq_zero hJQ
    have he : chainCliqueCount Q T.chains.flatten =
        chainCliqueCount Q (S.chains.flatten ++ (A ++ x :: y :: B)) := by
      simpa only [chainCliqueCount, List.filter_append, List.length_append,
        show (J.filter (fun v => decide (v ∈ Q))).length = 0 from hz, Nat.add_zero] using hh
    exact he.le
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped BigOperators Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.terminal_increment_profiles {k d a : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U T : RawPathSystem G Q) (hUamount : U.amount = S.amount)
    (hUcount : U.assignedCount = S.assignedCount)
    {original output kept removed : List ℕ}
    (ho : SystemAssignedAmounts Q U.chains original)
    (hout : SystemAssignedAmounts Q T.chains output)
    (hp : original.Perm (kept ++ removed)) (hq : output.Perm (a :: kept))
    (hTa : T.amount = S.amount + d) :
    S.amount = k - Q.card ∧ removed = [] ∧ kept.length = S.assignedCount ∧
      a = d ∧ ∀ b ∈ original, d ≤ b := by
  classical
  let : DecidableEq (Fin (kept.length + 1)) := Classical.decEq _
  have hosum : original.sum = S.amount := by
    rw [ho.sum_eq, ← U.amount_eq_outside_count, hUamount]
  have hocount : original.length = S.assignedCount := ho.length_eq.trans hUcount
  have hsum : kept.sum + removed.sum = S.amount := by
    rw [← List.sum_append, ← hp.sum_eq, hosum]
  have hlen : kept.length + removed.length = S.assignedCount := by
    rw [← List.length_append, ← hp.length_eq, hocount]
  have houtsum : a + kept.sum = S.amount + d := by
    have hs := hq.sum_eq
    rw [hout.sum_eq, ← T.amount_eq_outside_count, hTa, List.sum_cons] at hs
    omega
  let wt : Fin (kept.length + 1) → ℕ := (a :: kept).get
  let fresh : Fin (kept.length + 1) := 0
  let old : Finset (Fin (kept.length + 1)) := Finset.univ.erase fresh
  have hmap : (List.finRange (kept.length + 1)).map wt = a :: kept := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get _
  have hlabels : (List.finRange (kept.length + 1)).toFinset = Finset.univ := by
    ext i
    simp
  have hwfresh : wt fresh = a := rfl
  have hwtotal : (∑ i, wt i) = a + kept.sum := by
    have hs := List.sum_toFinset wt (List.nodup_finRange (kept.length + 1))
    rw [hlabels, hmap, List.sum_cons] at hs
    exact hs
  have hcard : old.card = kept.length := by
    simp only [old, Finset.card_erase_of_mem (Finset.mem_univ fresh),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hnew : fresh ∉ old := by simp [old]
  have hinsert : insert fresh old = Finset.univ := by simp [old]
  have hwold : (∑ i ∈ old, wt i) = kept.sum := by
    have hs := Finset.sum_erase_add Finset.univ wt (Finset.mem_univ fresh)
    rw [hwfresh, hwtotal] at hs
    change (∑ i ∈ old, wt i) + a = a + kept.sum at hs
    omega
  have hfull : old.card = S.assignedCount → (∑ i ∈ old, wt i) = S.amount := by
    intro he
    rw [hcard] at he
    have hrem : removed = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [hrem, List.sum_nil, Nat.add_zero] at hsum
    rw [hwold, hsum]
  have hrealize : ∀ J ⊆ insert fresh old, ∃ Z : ExpandedPathSystem G Q,
      Z.amount = ∑ i ∈ J, wt i ∧ Z.assignedCount = J.card := by
    intro J hJ
    apply hout.realize_labels_of_perm T (List.finRange (kept.length + 1)) wt
      (List.nodup_finRange _) (by rw [hmap]; exact hq) J
    rw [hlabels]
    exact Finset.subset_univ _
  obtain ⟨hL, he, _, hwa, hall⟩ := hopt.terminal_increment_weights ht hQk hkQ hQ hcycle
    hd hd' old fresh wt hnew (by rw [hwold]; omega) (by rw [hcard]; omega) hfull
    (by rw [hinsert, hwtotal]; exact houtsum) hrealize
  have hkept : kept.length = S.assignedCount := by simpa only [hcard] using he
  have hremoved : removed = [] := List.length_eq_zero_iff.mp (by omega)
  refine ⟨hL, hremoved, hkept, hwfresh.symm.trans hwa, ?_⟩
  intro b hb
  have hbkept : b ∈ kept := by simpa only [hremoved, List.append_nil] using hp.mem_iff.mp hb
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_cons_of_mem a hbkept)
  have hi' : wt i = b := hi
  have hh := hall i (by rw [hinsert]; exact Finset.mem_univ _)
  omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.forbidden_amount_two_detour {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {P R : List (List V)} {A B : List V} {q r u v : V}
    (hsys : S.chains = P ++ (A ++ q :: u :: v :: r :: B) :: R)
    (hq : q ∈ Q) (hr : r ∈ Q) (hu : u ∉ Q) (hv : v ∉ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) u v d := by
  classical
  intro houtside
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := houtside.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hJne : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  let old := A ++ q :: u :: v :: r :: B
  have holdmem : old ∈ S.chains := by simp [old, hsys]
  have hrest : (P ++ R).Sublist S.toRaw.chains := by
    change (P ++ R).Sublist S.chains
    rw [hsys]
    exact (List.Sublist.refl P).append ((List.Sublist.refl R).cons _)
  let U := S.toRaw.restrictChains (P ++ R) hrest
  have hperm : (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)).Perm S.chains.flatten := by
    apply List.perm_iff_count.mpr
    intro z
    simp only [U, RawPathSystem.restrictChains, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons, List.count_nil]
    omega
  have hflat : (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)).Nodup :=
    hperm.nodup_iff.mpr S.flatten_nodup
  have hdis : J.Disjoint (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)) := by
    apply List.disjoint_left.mpr
    intro z hz hzold
    exact hJout z hz (Or.inr (List.mem_toFinset.mpr (hperm.mem_iff.mp hzold)))
  have holdsplit : old = ((A ++ [q]) ++ [u]) ++ (v :: r :: B) := by
    simp [old, List.append_assoc]
  have hleft : ((A ++ [q]) ++ [u]).IsChain G.Adj := by
    exact (List.isChain_append.mp (holdsplit ▸ (S.paths old holdmem).2)).1
  have hright : (v :: r :: B).IsChain G.Adj := by
    exact (List.isChain_append.mp (holdsplit ▸ (S.paths old holdmem).2)).2.1
  have hleftSteps : ((A ++ [q]) ++ [u]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp (holdsplit ▸ S.no_clique_steps old holdmem)).1
  have hrightSteps : (v :: r :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) := by
    exact (List.isChain_append.mp (holdsplit ▸ S.no_clique_steps old holdmem)).2.1
  have hstart : ∀ z ∈ ((A ++ [q]) ++ [u]).head?, z ∈ Q := by
    intro z hz
    apply (S.endpoints old holdmem).1 z
    rw [holdsplit]
    exact List.mem_head?_append_of_mem_head? hz
  have hfinish : ∀ z ∈ (v :: r :: B).getLast?, z ∈ Q := by
    intro z hz
    apply (S.endpoints old holdmem).2 z
    rw [holdsplit, List.getLast?_append,
      List.getLast?_eq_some_getLast (show v :: r :: B ≠ [] by simp)]
    simpa only [List.getLast?_eq_some_getLast (show v :: r :: B ≠ [] by simp), Option.or] using hz
  obtain ⟨T, hT, hTa, _, _⟩ := U.expand_outside_template hflat hleft hright hstart hfinish
    hleftSteps hrightSteps hJ hJne hJQ hdis hpath
  have hamount : T.amount = S.amount + d := by
    have hs := (hperm.filter (fun z => decide (z ∉ Q))).length_eq
    change chainOutsideCount Q (U.chains.flatten ++ ((A ++ [q]) ++ u :: v :: r :: B)) =
      chainOutsideCount Q S.chains.flatten at hs
    have hSoutside : chainOutsideCount Q S.chains.flatten = S.amount := by
      exact S.toRaw.amount_eq_outside_count.symm
    rw [hSoutside] at hs
    omega
  have hpreEnds : (∀ z ∈ (A ++ [q]).head?, z ∈ Q) ∧
      (∀ z ∈ (A ++ [q]).getLast?, z ∈ Q) := by
    refine ⟨?_, by simpa using hq⟩
    intro z hz
    apply (S.endpoints old holdmem).1 z
    simpa [old, List.append_assoc] using List.mem_head?_append_of_mem_head?
      (t := u :: v :: r :: B) hz
  have hpreSteps : (A ++ [q]).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    (List.isChain_append.mp hleftSteps).1
  have hsufEnds : (∀ z ∈ (r :: B).head?, z ∈ Q) ∧
      (∀ z ∈ (r :: B).getLast?, z ∈ Q) := by
    refine ⟨by simpa using hr, ?_⟩
    intro z hz
    apply hfinish z
    cases B with
    | nil => simpa using hz
    | cons b B => simpa using hz
  have hsufSteps : (r :: B).IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    (List.isChain_cons.mp hrightSteps).2
  obtain ⟨wa, hwa⟩ := exists_assignedAmounts hpreEnds hpreSteps
  obtain ⟨wb, hwb⟩ := exists_assignedAmounts hsufEnds hsufSteps
  have hOldProfile : AssignedAmounts Q old (wa ++ 2 :: wb) := by
    have hh := hwa.append_segment (by simp) (J := [u, v]) (by simp [hu, hv]) (by simp) hwb
    simpa [old, List.append_assoc] using hh
  have hNewProfile : AssignedAmounts Q ((A ++ [q]) ++ u :: (J ++ v :: r :: B))
      (wa ++ (d + 2) :: wb) := by
    have hOutside : ∀ z ∈ u :: (J ++ [v]), z ∉ Q := by
      intro z hz
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | hz | rfl
      · exact hu
      · exact hJQ z hz
      · exact hv
    have hh := hwa.append_segment (by simp) hOutside (by simp) hwb
    simpa [List.append_assoc, hJlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh
  obtain ⟨wp, hp⟩ := S.toRaw.exists_subchain_profile P (by intro l hl; change l ∈ S.chains; simp [hsys, hl])
  obtain ⟨wr, hr'⟩ := S.toRaw.exists_subchain_profile R (by intro l hl; change l ∈ S.chains; simp [hsys, hl])
  let original := wp ++ (wa ++ 2 :: wb) ++ wr
  let kept := wp ++ wa ++ wb ++ wr
  let output := (wp ++ wr) ++ (wa ++ (d + 2) :: wb)
  have ho : SystemAssignedAmounts Q S.toRaw.chains original := by
    rw [show S.toRaw.chains = P ++ old :: R by
      change S.chains = P ++ old :: R
      simpa [old] using hsys]
    simpa only [original, List.append_assoc] using hp.append (.cons hOldProfile hr')
  have ht' : SystemAssignedAmounts Q T.chains output := by
    rw [hT]
    change SystemAssignedAmounts Q ((P ++ R) ++ [_]) output
    simpa [output] using (hp.append hr').append (.cons hNewProfile .nil)
  have horig : original.Perm (kept ++ [2]) := by
    apply List.perm_iff_count.mpr
    intro z
    simp only [original, kept, List.count_append, List.count_cons, List.count_nil]
    omega
  have hout : output.Perm ((d + 2) :: kept) := by
    apply List.perm_iff_count.mpr
    intro z
    simp only [output, kept, List.count_append, List.count_cons]
    omega
  obtain ⟨_, _, _, ha, _⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle hd hd'
    S.toRaw T (by simp) (by simp) ho ht' horig hout hamount
  omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.no_one_vertex_raw {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (T : RawPathSystem G Q)
    (hinc : T.amount = S.amount + 1) : False :=
  hopt.no_one_vertex_increase hk hQk hQ hcycle T.normalize (by simpa using hinc)
theorem IsOptimal.forbidden_different_chain_one {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (U : RawPathSystem G Q)
    (hUamount : U.amount = S.amount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P M R : List (List V)} {A B C D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp [he] at hJlen
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, _, hamount⟩ := U.replace_different_chains hsys hA hC hJ hJQ hpos hdis hpath
  exact hopt.no_one_vertex_raw hk hQk hQ hcycle T (by omega)
theorem IsOptimal.forbidden_same_chain_one {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (U : RawPathSystem G Q)
    (hUamount : U.amount = S.amount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P R : List (List V)} {A B D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp [he] at hJlen
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, _, hamount⟩ := U.replace_same_chain hsys hA hB hJ hJQ hpos hdis hpath
  exact hopt.no_one_vertex_raw hk hQk hQ hcycle T (by omega)
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.representatives_one_exclusion {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (U : RawPathSystem G Q)
    (hUamount : U.amount = S.amount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {x y : V} (hx : x ∈ U.representatives) (hy : y ∈ U.representatives) (hne : x ≠ y) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l', hl', heql⟩ := List.mem_map.mp hl
  subst l
  obtain ⟨m, hm, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨m', hm', heqm⟩ := List.mem_map.mp hm
  subst m
  have hxc := chainRepresentatives_mem_cut hx
  have hyc := chainRepresentatives_mem_cut hy
  by_cases hlm : l' = m'
  · subst m'
    obtain ⟨P, R, hchains⟩ := List.append_of_mem hl'
    rcases repCuts_ordered (U.paths l' hl').1 hne hxc hyc with
      ⟨A, B, D, he, hA, hB⟩ | ⟨A, B, D, he, hA, hB⟩
    · exact hopt.forbidden_same_chain_one hk hQk hQ hcycle U hUamount hUvertices
        (by simpa [he] using hchains) hA hB
    · intro hout
      exact hopt.forbidden_same_chain_one hk hQk hQ hcycle U hUamount hUvertices
        (by simpa [he] using hchains) hA hB hout.reverse
  · obtain ⟨R, hp⟩ := U.bring_two_front hl' hm' hlm
    let U' := U.reorder (l' :: m' :: R) hp
    have hamount : U'.amount = S.amount := by simpa [U'] using hUamount
    have hvertices : ∀ v ∈ U'.vertices, v ∈ Q ∨ v ∈ S.vertices := by
      intro v hv
      apply hUvertices v
      simpa [U'] using hv
    obtain ⟨A, B, he₁, hA⟩ := hxc
    obtain ⟨C, D, he₂, hC⟩ := hyc
    apply hopt.forbidden_different_chain_one hk hQk hQ hcycle U' hamount hvertices
      (P := []) (M := []) (R := R) (A := A) (B := B) (C := C) (D := D)
    · simp [U', RawPathSystem.reorder, he₁, he₂]
    · exact hA
    · exact hC
theorem IsOptimal.completed_representatives_one_exclusion {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) {x y : V}
    (hx : x ∈ S.toRaw.completeClique.representatives)
    (hy : y ∈ S.toRaw.completeClique.representatives) (hne : x ≠ y) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  apply hopt.representatives_one_exclusion hk hQk hQ hcycle S.toRaw.completeClique
    (by simp) ?_ hx hy hne
  intro v hv
  rw [RawPathSystem.completeClique_vertices] at hv
  exact (Finset.mem_union.mp hv).symm
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} [Fintype V]
noncomputable def outsideBallFinset (G : SimpleGraph V) (X : Finset V)
    (x : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∈ OutsideBall G (X : Set V) x r)
@[simp] theorem mem_outsideBallFinset {G : SimpleGraph V} {X : Finset V}
    {x v : V} {r : ℕ} :
    v ∈ outsideBallFinset G X x r ↔ v ∈ OutsideBall G (X : Set V) x r := by
  classical
  simp [outsideBallFinset]
theorem outsideBallFinset_mono {G : SimpleGraph V} {X : Finset V} {x : V}
    {r s : ℕ} (hrs : r ≤ s) :
    outsideBallFinset G X x r ⊆ outsideBallFinset G X x s := by
  intro v hv
  exact mem_outsideBallFinset.mpr (OutsideBall.mono hrs (mem_outsideBallFinset.mp hv))
omit [Fintype V] in
theorem outsideBall_step {G : SimpleGraph V} {X : Set V} {x u v : V} {r : ℕ}
    (hu : u ∈ OutsideBall G X x r) (hv : v ∉ X) (hadj : G.Adj u v) :
    v ∈ OutsideBall G X x (r + 1) := by
  obtain ⟨huX, p, hp, hsupp⟩ := hu
  have hedge : (boundaryGraph G X).Adj u v := ⟨hadj, Or.inl huX⟩
  refine ⟨hv, p.concat hedge, ?_, ?_⟩
  · simp only [SimpleGraph.Walk.length_concat]
    omega
  · intro w hw hwX
    have : w ∈ p.support ∨ w = v := by simpa using hw
    rcases this with hw | rfl
    · exact hsupp w hw hwX
    · exact False.elim (hv hwX)
theorem closedNeighborhood_ball_subset [DecidableEq V] {G : SimpleGraph V} {X A I : Finset V}
    {x : V} {r : ℕ} (hI : I ⊆ outsideBallFinset G X x r)
    (havoid : ∀ v ∈ A, v ∉ closedNeighborhood G I) :
    closedNeighborhood G I ⊆ outsideBallFinset G X x (r + 1) ∪ (X \ A) := by
  classical
  intro v hv
  by_cases hvX : v ∈ X
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨hvX, fun hvA => havoid v hvA hv⟩)
  · apply Finset.mem_union_left
    apply mem_outsideBallFinset.mpr
    rcases mem_closedNeighborhood.mp hv with hvI | ⟨u, huI, huv⟩
    · exact OutsideBall.mono (Nat.le_succ r) (mem_outsideBallFinset.mp (hI hvI))
    · exact outsideBall_step (mem_outsideBallFinset.mp (hI huI)) hvX huv
theorem outsideBall_growth {G : SimpleGraph V} {k : ℕ} {X A I : Finset V}
    {x : V} {r : ℕ} (hAX : A ⊆ X)
    (hI : I ⊆ outsideBallFinset G X x r)
    (havoid : ∀ v ∈ A, v ∉ closedNeighborhood G I)
    (hexpand : k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    k * I.card + 1 + A.card ≤ (outsideBallFinset G X x (r + 1)).card + X.card := by
  classical
  have hc := Finset.card_le_card (closedNeighborhood_ball_subset hI havoid)
  have hu := Finset.card_union_le (outsideBallFinset G X x (r + 1)) (X \ A)
  have hd := Finset.card_sdiff_add_card_eq_card hAX
  omega
theorem outsideBall_initial_growth {G : SimpleGraph V} {k : ℕ}
    {X A : Finset V} {x : V} (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (hanti : ∀ v ∈ A, ¬ G.Adj x v)
    (hexpand : k + 1 ≤ (closedNeighborhood G {x}).card) :
    k + 1 + A.card ≤ (outsideBallFinset G X x 0).card + X.card := by
  classical
  have hsub : closedNeighborhood G {x} ⊆ outsideBallFinset G X x 0 ∪ (X \ A) := by
    intro v hv
    have hvA : v ∉ A := by
      intro hvA
      rcases mem_closedNeighborhood.mp hv with hvx | ⟨w, hw, h⟩
      · have : v = x := Finset.mem_singleton.mp hvx
        exact hxA (this ▸ hvA)
      · have : w = x := Finset.mem_singleton.mp hw
        exact hanti v hvA (this ▸ h)
    by_cases hvX : v ∈ X
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvX, hvA⟩)
    · apply Finset.mem_union_left
      apply mem_outsideBallFinset.mpr
      apply (outsideBall_zero hx).mpr
      refine ⟨?_, hvX⟩
      rcases mem_closedNeighborhood.mp hv with hvx | ⟨w, hw, h⟩
      · exact False.elim (hvX ((Finset.mem_singleton.mp hvx) ▸ hx))
      · exact (Finset.mem_singleton.mp hw) ▸ h
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (outsideBallFinset G X x 0) (X \ A)
  have hd := Finset.card_sdiff_add_card_eq_card hAX
  omega
theorem closedNeighborhood_avoids_forbidden {G : SimpleGraph V} {X A I : Finset V}
    {x : V} {r : ℕ} (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (hI : I ⊆ outsideBallFinset G X x r)
    (hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d) :
    ∀ y ∈ A, y ∉ closedNeighborhood G I := by
  intro y hy hclosed
  have hyX : y ∈ (X : Set V) := hAX hy
  rcases mem_closedNeighborhood.mp hclosed with hyI | ⟨v, hvI, hvy⟩
  · exact (mem_outsideBallFinset.mp (hI hyI)).1 hyX
  · exact singleton_outside_ball_separated hx hyX (fun h => hxA (h ▸ hy))
      (hforbid y hy) v (mem_outsideBallFinset.mp (hI hvI)) hvy
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} [Fintype V]
theorem cycleNext_ne_self {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : cycleNext i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (i.val + 1) % m = i.val at hv
  by_cases hi : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have he : i.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega
theorem complete_hasCycle {G : SimpleGraph V} {m : ℕ} (hm : 2 ≤ m)
    (hcomplete : ∀ x y, x ≠ y → G.Adj x y) (hcard : m ≤ Fintype.card V) :
    HasCycle G m := by
  classical
  obtain ⟨I, _, hI⟩ := Finset.exists_subset_card_eq
    (show m ≤ (Finset.univ : Finset V).card by simpa using hcard)
  let e : Fin m ≃ I := (Finset.equivFinOfCardEq hI).symm
  let f : Fin m → V := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  refine ⟨f, hf, fun i => hcomplete _ _ ?_⟩
  exact fun h => cycleNext_ne_self hm i (hf h).symm
omit [Fintype V] in
theorem independent_pair {G : SimpleGraph V} {x y : V} (hne : x ≠ y)
    (hadj : ¬ G.Adj x y) : HasIndependent G 2 := by
  refine ⟨![x, y], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j
    have hyx : ¬ G.Adj y x := fun h => hadj h.symm
    fin_cases i <;> fin_cases j <;> simp_all
theorem independenceBound_zero {G : SimpleGraph V} (h : IndependenceBound G 0) :
    Fintype.card V = 0 := by
  classical
  have hempty : IsEmpty V := ⟨fun v => by
    have hs : G.IsIndepSet (({v} : Finset V) : Set V) := by simp
    have := h {v} hs
    simp at this⟩
  exact Fintype.card_eq_zero
theorem independenceBound_one {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hcycle : ¬ HasCycle G (k + 1)) (h : IndependenceBound G 1) :
    Fintype.card V ≤ k := by
  have hn : ¬ HasIndependent G 2 := independenceBound_iff_not_hasIndependent.mp h
  have hcomplete : ∀ x y, x ≠ y → G.Adj x y := by
    intro x y hxy
    by_contra hnon
    exact hn (independent_pair hxy hnon)
  by_contra hcard
  exact hcycle (complete_hasCycle (by omega) hcomplete (by omega))
theorem card_lt_of_ramseyProperty {G : SimpleGraph V} {m n N : ℕ}
    (hRamsey : RamseyProperty m (n + 1) N)
    (hcycle : ¬ HasCycle G m) (hbound : IndependenceBound G n) :
    Fintype.card V < N := by
  classical
  by_contra hcard
  obtain ⟨I, _, hI⟩ := Finset.exists_subset_card_eq
    (show N ≤ (Finset.univ : Finset V).card by simpa using (show N ≤ Fintype.card V by omega))
  let e : Fin N ≃ I := (Finset.equivFinOfCardEq hI).symm
  let f : Fin N → V := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  rcases hRamsey (G.comap f) with hc | hi
  · exact hcycle (hc.map f hf (fun h => h))
  · exact (independenceBound_iff_not_hasIndependent.mp hbound)
      (hi.map f hf (fun h => h))
theorem smaller_parameter_bound {k a b : ℕ} (hk : 3 ≤ k) (hb : b < a)
    (hprior : ∀ c, 2 ≤ c → c < a → RamseyProperty (k + 1) (c + 1) (k * c + 1))
    (G : SimpleGraph V) (hcycle : ¬ HasCycle G (k + 1))
    (hbound : IndependenceBound G b) : Fintype.card V ≤ k * b := by
  by_cases hb0 : b = 0
  · subst b
    simp [independenceBound_zero hbound]
  by_cases hb1 : b = 1
  · subst b
    simpa using independenceBound_one (by omega) hcycle hbound
  have hc := card_lt_of_ramseyProperty (hprior b (by omega) hb) hcycle hbound
  omega
theorem expansion_of_smaller_ramsey {k a : ℕ} (hk : 3 ≤ k)
    (hprior : ∀ b, 2 ≤ b → b < a → RamseyProperty (k + 1) (b + 1) (k * b + 1))
    (G : SimpleGraph V) (hcard : Fintype.card V = k * a + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hbound : IndependenceBound G a)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    k * I.card + 1 ≤ (closedNeighborhood G I).card := by
  classical
  apply minimal_counterexample_expansion hcard hcycle hbound
    (fun b hb Y hcy hi => ?_) I hI hne
  simpa using smaller_parameter_bound hk hb hprior
    (G.induce (Y : Set V)) hcy hi
theorem exists_minimal_counterexample {k a₀ : ℕ} (hk : 3 ≤ k)
    (ha₀ : 2 ≤ a₀) (ha₀k : a₀ ≤ k)
    (hfail : ¬ RamseyProperty (k + 1) (a₀ + 1) (k * a₀ + 1)) :
    ∃ (a : ℕ) (G : SimpleGraph (Fin (k * a + 1))),
      2 ≤ a ∧ a ≤ k ∧ ¬ HasCycle G (k + 1) ∧ IndependenceBound G a ∧
      ∀ I : Finset (Fin (k * a + 1)),
        G.IsIndepSet (I : Set _) → I.Nonempty →
        k * I.card + 1 ≤ (closedNeighborhood G I).card := by
  classical
  let P : ℕ → Prop := fun a =>
    2 ≤ a ∧ a ≤ k ∧ ¬ RamseyProperty (k + 1) (a + 1) (k * a + 1)
  have hex : ∃ a, P a := ⟨a₀, ha₀, ha₀k, hfail⟩
  let a := Nat.find hex
  obtain ⟨ha, hak, hbad⟩ := Nat.find_spec hex
  have hprior : ∀ b, 2 ≤ b → b < a →
      RamseyProperty (k + 1) (b + 1) (k * b + 1) := by
    intro b hb hba
    by_contra h
    exact Nat.find_min hex hba ⟨hb, by omega, h⟩
  change ¬ ∀ G : SimpleGraph (Fin (k * a + 1)),
    HasCycle G (k + 1) ∨ HasIndependent G (a + 1) at hbad
  obtain ⟨G, hG⟩ := not_forall.mp hbad
  obtain ⟨hcy, hi⟩ := not_or.mp hG
  have hbound : IndependenceBound G a := independenceBound_iff_not_hasIndependent.mpr hi
  refine ⟨a, G, ha, hak, hcy, hbound, ?_⟩
  intro I hI hne
  exact expansion_of_smaller_ramsey hk hprior G (Fintype.card_fin _) hcy hbound I hI hne
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def CEAlphaTwo : Prop :=
  ∀ (V : Type) [Fintype V] (H : SimpleGraph V),
    6 ≤ Fintype.card V → H.Connected →
    (∀ v : V, (H.induce {w | w ≠ v}).Connected) →
    ¬ HasIndependent H 3 → HasCycle H (Fintype.card V)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private theorem cycleNext_eq_add_one551 {r : ℕ} [NeZero r] (hr : 1 < r) (i : Fin r) :
    cycleNext i = i + 1 := by
  apply Fin.ext
  change (i.val + 1) % r = (i.val + 1 % r) % r
  rw [Nat.mod_eq_of_lt hr]
private def skipOne {r : ℕ} (hr : 3 ≤ r) (i : Fin (r - 1)) : Fin r :=
  ⟨if i.val = 0 then 0 else i.val + 1, by split_ifs <;> omega⟩
private theorem skipOne_injective {r : ℕ} (hr : 3 ≤ r) :
    Function.Injective (skipOne hr) := by
  intro i j h
  have heq := congrArg Fin.val h
  dsimp [skipOne] at heq
  apply Fin.ext
  split_ifs at heq <;> omega
private theorem adjacent_of_successive_values {r : ℕ} {G : SimpleGraph (Fin r)}
    (hc : ∀ i, G.Adj i (cycleNext i)) {u v : Fin r} (h : u.val + 1 = v.val) :
    G.Adj u v := by
  have hn : cycleNext u = v := by
    apply Fin.ext
    change (u.val + 1) % r = v.val
    rw [h, Nat.mod_eq_of_lt v.isLt]
  simpa [hn] using hc u
private theorem shorten_at_zero {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    {G : SimpleGraph (Fin r)} (hc : ∀ i, G.Adj i (cycleNext i))
    (hchord : G.Adj 0 2) : HasCycle G (r - 1) := by
  refine ⟨skipOne hr, skipOne_injective hr, ?_⟩
  intro i
  have hi := i.isLt
  by_cases hzero : i.val = 0
  · have h0 : skipOne hr i = 0 := by apply Fin.ext; simp [skipOne, hzero]
    have h2 : skipOne hr (cycleNext i) = 2 := by
      apply Fin.ext
      have hmod : (i.val + 1) % (r - 1) = 1 := by rw [hzero]; exact Nat.mod_eq_of_lt (by omega)
      simp only [skipOne, cycleNext, hmod]
      change (if 1 = 0 then 0 else 1 + 1) = 2 % r
      simp [Nat.mod_eq_of_lt (by omega : 2 < r)]
    simpa [h0, h2] using hchord
  · by_cases hlast : i.val + 1 = r - 1
    · have hnext : (cycleNext i).val = 0 := by simp [cycleNext, hlast]
      have hcycle : cycleNext (skipOne hr i) = skipOne hr (cycleNext i) := by
        apply Fin.ext
        change ((if i.val = 0 then 0 else i.val + 1) + 1) % r =
          if (cycleNext i).val = 0 then 0 else (cycleNext i).val + 1
        simp only [hzero, ↓reduceIte, hnext]
        have heq : i.val + 1 + 1 = r := by omega
        rw [heq, Nat.mod_self]
      simpa [hcycle] using hc (skipOne hr i)
    · have hnext : (cycleNext i).val = i.val + 1 :=
        Nat.mod_eq_of_lt (by omega)
      apply adjacent_of_successive_values hc
      simp only [skipOne, hzero, ↓reduceIte, hnext]
      split_ifs <;> omega
private def stepFourLabel {r : ℕ} (hr : 7 ≤ r) (i : Fin (r - 1)) : Fin r :=
  ⟨if i.val < r - 6 then i.val + 1
    else if i.val = r - 6 then r - 2
    else if i.val = r - 5 then r - 1
    else i.val - 1, by split_ifs <;> omega⟩
private theorem stepFourLabel_injective {r : ℕ} (hr : 7 ≤ r) :
    Function.Injective (stepFourLabel hr) := by
  intro i j h
  have heq := congrArg Fin.val h
  dsimp [stepFourLabel] at heq
  apply Fin.ext
  split_ifs at heq <;> omega
private theorem adjacent_of_step_four_values {r : ℕ} [NeZero r] (hr : 7 ≤ r)
    {G : SimpleGraph (Fin r)} (hfour : ∀ i, G.Adj i (i + 4))
    {u v : Fin r} (h : (u.val + 4) % r = v.val) : G.Adj u v := by
  have hfin : u + 4 = v := by
    apply Fin.ext
    change (u.val + 4 % r) % r = v.val
    rw [Nat.mod_eq_of_lt (by omega : 4 < r)]
    exact h
  simpa [hfin] using hfour u
private theorem step_four_cycle {r : ℕ} [NeZero r] (hr : 7 ≤ r)
    {G : SimpleGraph (Fin r)} (hc : ∀ i, G.Adj i (cycleNext i))
    (hfour : ∀ i, G.Adj i (i + 4)) : HasCycle G (r - 1) := by
  refine ⟨stepFourLabel hr, stepFourLabel_injective hr, ?_⟩
  intro i
  have hi := i.isLt
  by_cases hlast : i.val = r - 2
  · have hnext : (cycleNext i).val = 0 := by
      change (i.val + 1) % (r - 1) = 0
      have heq : i.val + 1 = r - 1 := by omega
      rw [heq, Nat.mod_self]
    have hu : (stepFourLabel hr i).val = r - 3 := by
      simp only [stepFourLabel, hlast]
      split_ifs <;> omega
    have hv : (stepFourLabel hr (cycleNext i)).val = 1 := by
      simp only [stepFourLabel, hnext]
      split_ifs <;> omega
    apply adjacent_of_step_four_values hr hfour
    rw [hu, hv]
    have heq : r - 3 + 4 = r + 1 := by omega
    rw [heq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : 1 < r)]
  · have hnext : (cycleNext i).val = i.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    by_cases hfirst : i.val < r - 7
    · apply adjacent_of_successive_values hc
      simp only [stepFourLabel, hnext]
      split_ifs <;> omega
    · by_cases hboundary : i.val = r - 7
      · apply adjacent_of_step_four_values hr hfour
        have hu : (stepFourLabel hr i).val = r - 6 := by
          simp only [stepFourLabel, hboundary]; split_ifs <;> omega
        have hv : (stepFourLabel hr (cycleNext i)).val = r - 2 := by
          simp only [stepFourLabel, hnext, hboundary]; split_ifs <;> omega
        rw [hu, hv]
        have heq : r - 6 + 4 = r - 2 := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
      · by_cases hpenultimate : i.val = r - 5
        · apply SimpleGraph.Adj.symm
          apply adjacent_of_step_four_values hr hfour
          have hu : (stepFourLabel hr i).val = r - 1 := by
            simp only [stepFourLabel, hpenultimate]; split_ifs <;> omega
          have hv : (stepFourLabel hr (cycleNext i)).val = r - 5 := by
            simp only [stepFourLabel, hnext, hpenultimate]; split_ifs <;> omega
          rw [hu, hv]
          have heq : r - 5 + 4 = r - 1 := by omega
          rw [heq, Nat.mod_eq_of_lt (by omega)]
        · apply adjacent_of_successive_values hc
          simp only [stepFourLabel, hnext]
          split_ifs <;> omega
theorem labelled_cycle_shortening {r : ℕ} (hr : 7 ≤ r)
    {G : SimpleGraph (Fin r)} (hc : ∀ i, G.Adj i (cycleNext i))
    (hi : ¬ HasIndependent G 3) : HasCycle G (r - 1) := by
  let : NeZero r := ⟨by omega⟩
  by_cases hchord : ∃ i : Fin r, G.Adj i (i + 2)
  · obtain ⟨a, ha⟩ := hchord
    let H : SimpleGraph (Fin r) := G.comap (fun i => a + i)
    have hH : ∀ i, H.Adj i (cycleNext i) := by
      intro i
      change G.Adj (a + i) (a + cycleNext i)
      rw [cycleNext_eq_add_one551 (by omega), ← add_assoc,
        ← cycleNext_eq_add_one551 (by omega)]
      exact hc (a + i)
    have hH02 : H.Adj 0 2 := by change G.Adj (a + 0) (a + 2); simpa using ha
    exact (shorten_at_zero (by omega) hH hH02).map (fun i => a + i)
      (add_right_injective a) (fun h => h)
  · have htwo : ∀ i : Fin r, ¬ G.Adj i (i + 2) := by simpa using hchord
    have hconst : (2 : Fin r) + 2 = 4 := by
      apply Fin.ext
      change (2 % r + 2 % r) % r = 4 % r
      rw [Nat.mod_eq_of_lt (by omega : 2 < r), Nat.mod_eq_of_lt (by omega : 4 < r)]
    have hval2 : (2 : Fin r).val = 2 := by
      change 2 % r = 2
      exact Nat.mod_eq_of_lt (by omega)
    have hval4 : (4 : Fin r).val = 4 := by
      change 4 % r = 4
      exact Nat.mod_eq_of_lt (by omega)
    have h02 : (0 : Fin r) ≠ 2 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero, hval2] at hv
      omega
    have h04 : (0 : Fin r) ≠ 4 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero, hval4] at hv
      omega
    have h24 : (2 : Fin r) ≠ 4 := by
      intro h
      have hv := congrArg Fin.val h
      rw [hval2, hval4] at hv
      omega
    have hfour : ∀ i : Fin r, G.Adj i (i + 4) := by
      intro i
      by_contra hnot
      have hi2 : i ≠ i + 2 := by simpa using (add_right_injective i).ne h02
      have hi4 : i ≠ i + 4 := by simpa using (add_right_injective i).ne h04
      have hi24 : i + 2 ≠ i + 4 := (add_right_injective i).ne h24
      have hnot24 : ¬ G.Adj (i + 2) (i + 4) := by
        simpa [add_assoc, hconst] using htwo (i + 2)
      exact hi (hasIndependent_three_of_distinct_nonadjacent hi2 hi4 hi24
        (htwo i) hnot hnot24)
    exact step_four_cycle hr hc hfour
theorem cycle_shortening {V : Type*} {r : ℕ} (hr : 7 ≤ r) {G : SimpleGraph V}
    (hc : HasCycle G r) (hi : ¬ HasIndependent G 3) : HasCycle G (r - 1) := by
  obtain ⟨f, hf, he⟩ := hc
  let H : SimpleGraph (Fin r) := G.comap f
  have hH : ∀ i, H.Adj i (cycleNext i) := he
  have hI : ¬ HasIndependent H 3 := fun h => hi (h.map f hf (fun h => h))
  exact (labelled_cycle_shortening hr hH hI).map f hf (fun h => h)
theorem cycle_shorten_to {V : Type*} {G : SimpleGraph V} {q r : ℕ}
    (hq : 6 ≤ q) (hqr : q ≤ r) (hc : HasCycle G r)
    (hi : ¬ HasIndependent G 3) : HasCycle G q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqr
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    apply ih (by omega)
    have hshort := cycle_shortening (by omega : 7 ≤ q + (d + 1)) hc hi
    simpa using hshort
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
private structure TwoCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  cover : left ∪ right = Finset.univ
  disjoint : Disjoint left right
  left_clique : G.IsClique (left : Set V)
  right_clique : G.IsClique (right : Set V)
  anticomplete : ∀ x ∈ left, ∀ y ∈ right, ¬ G.Adj x y
private theorem two_clique_partition {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (hi : ¬ HasIndependent G 3) (hn : ¬ G.Connected) :
    Nonempty (TwoCliquePartition G) := by
  classical
  have hnp : ¬ G.Preconnected := fun h => hn ⟨h⟩
  change ¬ ∀ u v, G.Reachable u v at hnp
  push Not at hnp
  obtain ⟨u, v, huv⟩ := hnp
  let A : Finset V := Finset.univ.filter (G.Reachable u)
  let B : Finset V := Finset.univ.filter (fun x => ¬ G.Reachable u x)
  have hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
    intro x hx y hy hadj
    exact (Finset.mem_filter.mp hy).2 (((Finset.mem_filter.mp hx).2).trans hadj.reachable)
  have hA : G.IsClique (A : Set V) := by
    intro x hx y hy hxy
    by_contra hnxy
    have hxv : x ≠ v := by
      intro h; subst x; exact huv (Finset.mem_filter.mp hx).2
    have hyv : y ≠ v := by
      intro h; subst y; exact huv (Finset.mem_filter.mp hy).2
    have hv : v ∈ B := by simp [B, huv]
    exact hi (hasIndependent_three_of_distinct_nonadjacent hxy hxv hyv hnxy
      (hcross x hx v hv) (hcross y hy v hv))
  have hB : G.IsClique (B : Set V) := by
    intro x hx y hy hxy
    by_contra hnxy
    have hu : u ∈ A := by simp [A]
    have hxu : x ≠ u := by
      intro h; subst x; exact (Finset.mem_filter.mp hx).2 .rfl
    have hyu : y ≠ u := by
      intro h; subst y; exact (Finset.mem_filter.mp hy).2 .rfl
    exact hi (hasIndependent_three_of_distinct_nonadjacent hxy hxu hyu hnxy
      (fun h => hcross u hu x hx h.symm) (fun h => hcross u hu y hy h.symm))
  refine ⟨⟨A, B, ?_, ?_, hA, hB, hcross⟩⟩
  · ext x
    simp [A, B]
    exact Classical.em _
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2
private theorem TwoCliquePartition.card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (p : TwoCliquePartition G) :
    p.left.card + p.right.card = Fintype.card V := by
  classical
  rw [← Finset.card_union_of_disjoint p.disjoint, p.cover, Finset.card_univ]
private theorem connected_of_no_independent_triple {V : Type*} [Fintype V]
    {G : SimpleGraph V} {t : ℕ} (hi : ¬ HasIndependent G 3)
    (ht : G.cliqueNum ≤ t) (hcard : 2 * t < Fintype.card V) : G.Connected := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hn
  obtain ⟨p⟩ := two_clique_partition hi hn
  have hA := p.left_clique.card_le_cliqueNum.trans ht
  have hB := p.right_clique.card_le_cliqueNum.trans ht
  have := p.card
  omega
private theorem joined_clique_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (v : V) (A : Finset {w : V | w ≠ v})
    (hA : (G.induce {w | w ≠ v}).IsClique (A : Set {w : V | w ≠ v}))
    (hjoin : ∀ a ∈ A, G.Adj v a.val) : A.card + 1 ≤ G.cliqueNum := by
  classical
  let A' : Finset V := A.map ⟨Subtype.val, Subtype.val_injective⟩
  have hA' : G.IsClique (A' : Set V) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hA ha hb (fun h => hxy (congrArg Subtype.val h))
  have hv : v ∉ A' := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
    exact a.property ha
  have hQ : G.IsClique ((insert v A' : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    apply hA'.insert
    intro x hx _
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    exact hjoin a ha
  simpa [Finset.card_insert_of_notMem hv, A'] using hQ.card_le_cliqueNum
private theorem deletion_connected_of_no_independent_triple {V : Type*} [Fintype V]
    {G : SimpleGraph V} {t : ℕ} (hi : ¬ HasIndependent G 3)
    (ht : G.cliqueNum ≤ t) (hcard : 2 * t < Fintype.card V)
    (htpos : 1 ≤ t) (v : V) : (G.induce {w | w ≠ v}).Connected := by
  classical
  let W := {w : V | w ≠ v}
  let H : SimpleGraph W := G.induce {w | w ≠ v}
  have hW : Fintype.card W = Fintype.card V - 1 := by
    change Fintype.card {w : V // ¬ w = v} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl]
    simp
  let : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hI : ¬ HasIndependent H 3 := fun h => hi (h.map Subtype.val Subtype.val_injective (fun h => h))
  by_contra hn
  obtain ⟨p⟩ := two_clique_partition hI hn
  have hH : H.cliqueNum ≤ t := (G.cliqueNum_induce_le _).trans ht
  have hA := p.left_clique.card_le_cliqueNum.trans hH
  have hB := p.right_clique.card_le_cliqueNum.trans hH
  have hsum := p.card
  have hAeq : p.left.card = t := by omega
  have hBeq : p.right.card = t := by omega
  have hjoin : (∀ a ∈ p.left, G.Adj v a.val) ∨ (∀ b ∈ p.right, G.Adj v b.val) := by
    by_cases hleft : ∀ a ∈ p.left, G.Adj v a.val
    · exact Or.inl hleft
    · right
      push Not at hleft
      obtain ⟨a, ha, hna⟩ := hleft
      intro b hb
      by_contra hnb
      have hab : a.val ≠ b.val := by
        intro h
        have heq : a = b := Subtype.ext h
        exact Finset.disjoint_left.mp p.disjoint ha (heq.symm ▸ hb)
      exact hi (hasIndependent_three_of_distinct_nonadjacent a.property.symm b.property.symm hab
        hna hnb (p.anticomplete a ha b hb))
  rcases hjoin with hjoin | hjoin
  · have h := (joined_clique_card v p.left p.left_clique hjoin).trans ht
    omega
  · have h := (joined_clique_card v p.right p.right_clique hjoin).trans ht
    omega
theorem size_test_graph (hCE : CEAlphaTwo) {V : Type} [Fintype V]
    {G : SimpleGraph V} {k t : ℕ} (hk : 5 ≤ k) (ht : 1 ≤ t)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (hcard : max k (2 * t) < Fintype.card V) : HasIndependent G 3 := by
  classical
  by_contra hi
  have hcardk : k < Fintype.card V := (le_max_left _ _).trans_lt hcard
  have hcardt : 2 * t < Fintype.card V := (le_max_right _ _).trans_lt hcard
  have hconn := connected_of_no_independent_triple hi hclique hcardt
  have hdel := deletion_connected_of_no_independent_triple hi hclique hcardt ht
  have hham := hCE V G (by omega) hconn hdel hi
  exact hcycle (cycle_shorten_to (by omega) (by omega) hham hi)
theorem size_test (hCE : CEAlphaTwo) {V : Type} [Fintype V]
    {G : SimpleGraph V} {k t : ℕ} (hk : 5 ≤ k) (ht : 1 ≤ t)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (Y : Finset V) (hY : max k (2 * t) < Y.card) :
    HasIndependent (G.induce (Y : Set V)) 3 := by
  classical
  apply size_test_graph hCE hk ht
  · intro hc
    exact hcycle (hc.map Subtype.val Subtype.val_injective (fun h => h))
  · exact (G.cliqueNum_induce_le _).trans hclique
  · simpa using hY
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
omit [Fintype V] in
theorem independent_pair_of_not_clique {Y : Finset V}
    (hY : ¬ G.IsClique (Y : Set V)) : HasIndependent (G.induce (Y : Set V)) 2 := by
  by_contra hn
  apply hY
  intro x hx y hy hxy
  by_contra hadj
  exact hn (independent_pair (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (fun h => hxy (congrArg Subtype.val h)) hadj)
theorem independent_pair_of_card_gt_cliqueNum {Y : Finset V} {t : ℕ}
    (ht : G.cliqueNum ≤ t) (hcard : t < Y.card) :
    HasIndependent (G.induce (Y : Set V)) 2 := by
  apply independent_pair_of_not_clique
  intro h
  have := h.card_le_cliqueNum
  omega
theorem outsideBall_initial_pair {X : Finset V} {x : V} {t : ℕ}
    (hx : x ∈ X) (ht : G.cliqueNum ≤ t)
    (hcard : t ≤ (outsideBallFinset G X x 0).card) :
    HasIndependent (G.induce (outsideBallFinset G X x 0 : Set V)) 2 := by
  classical
  apply independent_pair_of_not_clique
  intro hclique
  have hxout : x ∉ outsideBallFinset G X x 0 := by
    intro h
    exact (mem_outsideBallFinset.mp h).1 hx
  have hjoin : G.IsClique ((insert x (outsideBallFinset G X x 0) : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    apply hclique.insert
    intro v hv _
    exact ((outsideBall_zero hx).mp (mem_outsideBallFinset.mp hv)).1
  have hb := hjoin.card_le_cliqueNum.trans ht
  rw [Finset.card_insert_of_notMem hxout] at hb
  omega
theorem outsideBall_exception_pair {X A : Finset V} {x : V} {r k t : ℕ}
    (hx : x ∈ X) (hAX : A ⊆ X) (hxA : x ∉ A)
    (ht : G.cliqueNum ≤ t)
    (hprev : t ≤ (outsideBallFinset G X x r).card)
    (hnum : X.card + t ≤ k + 1 + A.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ r + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d) :
    HasIndependent (G.induce (outsideBallFinset G X x (r + 1) : Set V)) 2 := by
  classical
  apply independent_pair_of_not_clique
  intro hclique
  let B := outsideBallFinset G X x r
  let C := outsideBallFinset G X x (r + 1)
  have hBC : B ⊆ C := outsideBallFinset_mono (Nat.le_succ r)
  have hCcard : C.card ≤ t := hclique.card_le_cliqueNum.trans ht
  have heq : B = C := Finset.eq_of_subset_of_card_le hBC (by
    change t ≤ B.card at hprev
    omega)
  have hCC : C.card = t := by
    have := Finset.card_le_card hBC
    change t ≤ B.card at hprev
    omega
  have hxC : x ∉ C := by
    intro h
    exact (mem_outsideBallFinset.mp h).1 hx
  have hxD : x ∈ X \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
  have hDpos : 0 < (X \ A).card := Finset.card_pos.mpr ⟨x, hxD⟩
  have hdcard := Finset.card_sdiff_add_card_eq_card hAX
  have herase := Finset.card_erase_of_mem hxD
  have hjoin : ∀ v ∈ C, G.Adj x v := by
    intro v hv
    have hvB : v ∈ B := heq.symm ▸ hv
    by_contra hnon
    have hsub : closedNeighborhood G {v} ⊆ C ∪ ((X \ A).erase x) := by
      intro w hw
      rcases mem_closedNeighborhood.mp hw with hwv | ⟨u, hu, huw⟩
      · have : w = v := Finset.mem_singleton.mp hwv
        exact Finset.mem_union_left _ (this ▸ hv)
      · have hueq : u = v := Finset.mem_singleton.mp hu
        subst u
        by_cases hwX : w ∈ X
        · apply Finset.mem_union_right
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_sdiff.mpr ⟨hwX, ?_⟩⟩
          · intro he
            subst w
            exact hnon huw.symm
          · intro hwA
            exact singleton_outside_ball_separated hx (hAX hwA)
              (fun he => hxA (he ▸ hwA)) (hforbid w hwA) v
              (mem_outsideBallFinset.mp hvB) huw
        · apply Finset.mem_union_left
          exact mem_outsideBallFinset.mpr
            (outsideBall_step (mem_outsideBallFinset.mp hvB) hwX huw)
    have hc := Finset.card_le_card hsub
    have hu := Finset.card_union_le C ((X \ A).erase x)
    have he := hexpand v
    omega
  have hbig : G.IsClique ((insert x C : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hclique.insert (fun v hv _ => hjoin v hv)
  have hc := hbig.card_le_cliqueNum.trans ht
  rw [Finset.card_insert_of_notMem hxC, hCC] at hc
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
variable {V : Type*} [Fintype V]
noncomputable def packingRegion (G : SimpleGraph V) (X : Finset V)
    (x : V) : ℕ → Finset V
  | 0 => {x}
  | r + 1 => outsideBallFinset G X x r
def PackingCompatible (G : SimpleGraph V) (X : Set V) (x : V) (r : ℕ) (y : V) (s : ℕ) : Prop :=
  if r = 0 ∧ s = 0 then ¬ OutsidePath G X x y 0
  else ∀ d, 1 ≤ d → d ≤ r + s → ¬ OutsidePath G X x y d
omit [Fintype V] in
theorem PackingCompatible.symm {G : SimpleGraph V} {X : Set V} {x y : V} {r s : ℕ}
    (h : PackingCompatible G X x r y s) : PackingCompatible G X y s x r := by
  unfold PackingCompatible at *
  by_cases hzero : r = 0 ∧ s = 0
  · have hzero' : s = 0 ∧ r = 0 := hzero.symm
    simp only [hzero] at h
    simp only [hzero']
    exact fun hp => h hp.reverse
  · have hzero' : ¬ (s = 0 ∧ r = 0) := fun hs => hzero hs.symm
    simp only [hzero, ↓reduceIte] at h
    simp only [hzero', ↓reduceIte]
    intro d hd hbound hp
    exact h d hd (by omega) hp.reverse
theorem packingRegions_separated {G : SimpleGraph V} {X : Finset V} {x y : V} {r s : ℕ}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hcompat : PackingCompatible G (X : Set V) x r y s) :
    Disjoint (packingRegion G X x r) (packingRegion G X y s) ∧
    ∀ u ∈ packingRegion G X x r, ∀ v ∈ packingRegion G X y s, ¬ G.Adj u v := by
  classical
  cases r with
  | zero =>
    cases s with
    | zero =>
      have hnon : ¬ G.Adj x y := by
        have h := hcompat
        simp only [PackingCompatible, and_self, ↓reduceIte] at h
        exact fun hadj => h (outsidePath_zero.mpr hadj)
      constructor
      · simpa [packingRegion] using hxy
      · simpa [packingRegion] using hnon
    | succ s =>
      have hf : ∀ d, 1 ≤ d → d ≤ s + 1 →
          ¬ PositiveOutsidePath G (X : Set V) y x d := by
        intro d hd hds hp
        have hc := hcompat.symm
        simp only [PackingCompatible, Nat.add_one_ne_zero, false_and, ↓reduceIte,
          Nat.add_zero] at hc
        exact hc d hd hds hp.toOutside
      constructor
      · apply Finset.disjoint_left.mpr
        intro v hv hball
        have he : v = x := by simpa [packingRegion] using hv
        subst v
        exact (mem_outsideBallFinset.mp hball).1 hx
      · intro u hu v hv hadj
        have he : u = x := by simpa [packingRegion] using hu
        subst u
        exact singleton_outside_ball_separated hy hx hxy.symm hf v
          (mem_outsideBallFinset.mp hv) hadj.symm
  | succ r =>
    cases s with
    | zero =>
      have hf : ∀ d, 1 ≤ d → d ≤ r + 1 →
          ¬ PositiveOutsidePath G (X : Set V) x y d := by
        intro d hd hds hp
        have hc := hcompat
        simp only [PackingCompatible, Nat.add_one_ne_zero, false_and, ↓reduceIte,
          Nat.add_zero] at hc
        exact hc d hd hds hp.toOutside
      constructor
      · apply Finset.disjoint_left.mpr
        intro v hball hv
        have he : v = y := by simpa [packingRegion] using hv
        subst v
        exact (mem_outsideBallFinset.mp hball).1 hy
      · intro u hu v hv hadj
        have he : v = y := by simpa [packingRegion] using hv
        subst v
        exact singleton_outside_ball_separated hx hy hxy hf u
          (mem_outsideBallFinset.mp hu) hadj
    | succ s =>
      have hf : ∀ d, 1 ≤ d → d ≤ r + s + 2 →
          ¬ PositiveOutsidePath G (X : Set V) x y d := by
        intro d hd hds hp
        have hc := hcompat
        simp only [PackingCompatible, Nat.add_one_ne_zero, false_and, ↓reduceIte] at hc
        exact hc d hd (by omega) hp.toOutside
      obtain ⟨hdis, hanti⟩ := outside_balls_separated hx hy hxy hf
      constructor
      · apply Finset.disjoint_left.mpr
        intro v hv hw
        exact Set.disjoint_left.mp hdis (mem_outsideBallFinset.mp hv)
          (mem_outsideBallFinset.mp hw)
      · intro u hu v hv
        exact hanti u (mem_outsideBallFinset.mp hu) v (mem_outsideBallFinset.mp hv)
theorem packing_test {ι : Type*} [Fintype ι] {G : SimpleGraph V} {k : ℕ}
    (hbound : IndependenceBound G k) (X : Finset V)
    (base : ι → V) (radius weight : ι → ℕ)
    (hbase : Function.Injective base) (hX : ∀ i, base i ∈ X)
    (hweight : ∀ i, HasIndependent (G.induce (packingRegion G X (base i) (radius i) : Set V))
      (weight i))
    (hcompat : ∀ i j, i ≠ j →
      PackingCompatible G (X : Set V) (base i) (radius i) (base j) (radius j)) :
    ∑ i, weight i ≤ k := by
  classical
  choose I hIsub hIind hIcard using fun i => exists_independent_subset (hweight i)
  have hsep := fun i j hij => packingRegions_separated (hX i) (hX j)
    (fun h => hij (hbase h)) (hcompat i j hij)
  have hdis : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint I := by
    intro i _ j _ hij
    exact (hsep i j hij).1.mono (hIsub i) (hIsub j)
  have hanti : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      ∀ u ∈ I i, ∀ v ∈ I j, ¬ G.Adj u v := by
    intro i _ j _ hij u hu v hv
    exact (hsep i j hij).2 u (hIsub i hu) v (hIsub j hv)
  have h := independent_packing hbound Finset.univ I (fun i _ => hIind i) hdis hanti
  simpa only [hIcard] using h
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {X R : Finset V} {x : V} {k : ℕ}
theorem representative_ball_one (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ¬ OutsidePath G (X : Set V) x y 1) :
    k + R.card ≤ (outsideBallFinset G X x 1).card + X.card := by
  have hxX := hRX hxR
  have hzero := outsideBall_initial_growth (A := ∅) hxX (by simp) (by simp)
    (by simp) (hexpand x)
  simp only [Finset.card_empty, Nat.add_zero] at hzero
  have hnonempty : (outsideBallFinset G X x 0).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, hu⟩ := hnonempty
  let A := R.erase x
  have hAX : A ⊆ X := fun _ hv => hRX (Finset.mem_of_mem_erase hv)
  have hxA : x ∉ A := by simp [A]
  have hf : ∀ y ∈ A, ∀ d, 1 ≤ d → d ≤ 0 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d := by
    intro y hy d hd hdb hp
    have he : d = 1 := by omega
    subst d
    exact hforbid y (Finset.mem_of_mem_erase hy)
      (Finset.ne_of_mem_erase hy).symm hp.toOutside
  have hI : ({u} : Finset V) ⊆ outsideBallFinset G X x 0 := by simpa using hu
  have havoid := closedNeighborhood_avoids_forbidden hxX hAX hxA hI hf
  have hg := outsideBall_growth hAX hI havoid (by simpa using hexpand u)
  have hc : A.card + 1 = R.card := Finset.card_erase_add_one hxR
  simp only [Finset.card_singleton, Nat.mul_one, Nat.reduceAdd] at hg
  omega
theorem representative_ball_two_pair (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 2 →
      ¬ OutsidePath G (X : Set V) x y d) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 2 := by
  have hfirst := representative_ball_one hxR hRX hXk hexpand
    (fun y hy hne => hforbid y hy hne 1 (by omega) (by omega))
  apply outsideBall_exception_pair (r := 1) (k := k) (t := R.card)
    (A := R.erase x) (hRX hxR) (fun _ hy => hRX (Finset.mem_of_mem_erase hy))
    (by simp) hclique (by omega)
  · have hc := Finset.card_erase_add_one hxR
    omega
  · exact hexpand
  · intro y hy d hd hdb hp
    exact hforbid y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      d hd hdb hp.toOutside
theorem representative_ball_two_triple (hCE : CEAlphaTwo) (hk : 5 ≤ k)
    (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k) (hRk : R.card < k)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 2 →
      ¬ OutsidePath G (X : Set V) x y d)
    (hnotclique : ¬ G.IsClique (outsideBallFinset G X x 1 : Set V)) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
  obtain ⟨I, hI, hind, hIcard⟩ := exists_independent_subset (independent_pair_of_not_clique hnotclique)
  have hAX : R.erase x ⊆ X := fun _ hy => hRX (Finset.mem_of_mem_erase hy)
  have hf : ∀ y ∈ R.erase x, ∀ d, 1 ≤ d → d ≤ 1 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d := by
    intro y hy d hd hdb hp
    exact hforbid y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      d hd hdb hp.toOutside
  have havoid := closedNeighborhood_avoids_forbidden (hRX hxR) hAX (by simp) hI hf
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth hAX hI havoid (hexpand I hind hne)
  have hc := Finset.card_erase_add_one hxR
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨x, hxR⟩
  apply size_test hCE hk hRpos hcycle hclique (outsideBallFinset G X x 2)
  rw [hIcard] at hg
  simp only [Nat.reduceAdd] at hg
  exact max_lt_iff.mpr ⟨by omega, by omega⟩
theorem exists_short_path_of_twice_card_gt (hbound : IndependenceBound G k)
    (hRX : R ⊆ X) (hXk : X.card ≤ k) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hlarge : k < 2 * R.card) :
    ∃ x ∈ R, ∃ y ∈ R, x ≠ y ∧ ∃ d, 1 ≤ d ∧ d ≤ 6 ∧
      OutsidePath G (X : Set V) x y d := by
  by_contra hn
  push Not at hn
  have hf : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d := by
    intro x hx y hy hne d hd hdb
    exact hn x hx y hy hne d hd hdb
  have hpack := packing_test hbound X (fun i : R => i.val) (fun _ => 3) (fun _ => 2)
    Subtype.val_injective (fun i => hRX i.property)
    (fun i => by
      have h := representative_ball_two_pair i.property hRX hXk hclique hexpand
        (fun y hy hne d hd hdb => hf i i.property y hy hne d hd (by omega))
      simpa [packingRegion] using h)
    (fun i j hij => by
      simp only [PackingCompatible, OfNat.ofNat_ne_zero, false_and, ↓reduceIte]
      intro d hd hdb
      exact hf i i.property j j.property (fun h => hij (Subtype.ext h)) d hd hdb)
  have hnum : 2 * R.card ≤ k := by simpa [mul_comm] using hpack
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
noncomputable def ground (S : ExpandedPathSystem G Q) : Finset V := Q ∪ S.vertices
noncomputable def representativeFinset (S : ExpandedPathSystem G Q) : Finset V :=
  S.toRaw.completeClique.representatives.toFinset
theorem ground_card (S : ExpandedPathSystem G Q) : S.ground.card = Q.card + S.amount := by
  have hc := Finset.card_union_add_card_inter Q S.vertices
  have hpart := Finset.card_sdiff_add_card_inter S.vertices Q
  have hi : (Q ∩ S.vertices).card = (S.vertices ∩ Q).card := by rw [Finset.inter_comm]
  unfold ground amount
  omega
theorem representativeFinset_card (S : ExpandedPathSystem G Q) :
    S.representativeFinset.card = Q.card := by
  rw [representativeFinset, List.toFinset_card_of_nodup S.toRaw.completeClique.representatives_nodup,
    RawPathSystem.completeClique_representatives_length]
theorem representativeFinset_subset_ground (S : ExpandedPathSystem G Q) :
    S.representativeFinset ⊆ S.ground := by
  intro v hv
  have hv' := S.toRaw.completeClique.representatives_sublist.subset (List.mem_toFinset.mp hv)
  have hvU : v ∈ S.toRaw.completeClique.vertices := List.mem_toFinset.mpr hv'
  rw [RawPathSystem.completeClique_vertices] at hvU
  exact Finset.mem_union.mpr (Finset.mem_union.mp hvU).symm
theorem IsOptimal.ground_card_le {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hQk : Q.card ≤ k) : S.ground.card ≤ k := by
  rw [ground_card]
  have h := hopt.budget
  omega
theorem IsOptimal.representativeFinset_one_exclusion {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {x y : V} (hx : x ∈ S.representativeFinset) (hy : y ∈ S.representativeFinset) (hne : x ≠ y) :
    ¬ OutsidePath G (S.ground : Set V) x y 1 := by
  simpa only [ground, Finset.coe_union] using
    hopt.completed_representatives_one_exclusion hk hQk hQ hcycle
      (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hne
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem normalize_ground (U : RawPathSystem G Q) :
    U.normalize.ground = Q ∪ U.vertices := by
  classical
  have he := normalizeChains_outside_vertices U.chains U.paths U.disjoint U.endpoints U.no_clique_steps
  change U.normalize.vertices \ Q = U.vertices \ Q at he
  ext x
  by_cases hx : x ∈ Q
  · simp [ExpandedPathSystem.ground, hx]
  · have hh := Finset.ext_iff.mp he x
    simpa [ExpandedPathSystem.ground, hx] using hh
theorem normalize_representative_mem (U : RawPathSystem G Q) {x : V}
    (hx : x ∈ U.representatives) : x ∈ U.normalize.representativeFinset := by
  classical
  obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hr
  have hxl : x ∈ l := (chainRepresentatives_sublist l).subset hxr
  by_cases hlen : 3 ≤ l.length
  · have hlE : l ∈ U.normalize.chains := List.mem_filter.mpr ⟨hl, by simpa using hlen⟩
    apply List.mem_toFinset.mpr
    apply List.mem_flatten.mpr
    refine ⟨chainRepresentatives Q l, ?_, hxr⟩
    apply List.mem_map.mpr
    exact ⟨l, List.mem_append_left _ hlE, rfl⟩
  · have hxQ : x ∈ Q := short_chain_in_clique (U.endpoints l hl)
      (U.no_clique_steps l hl) (by omega) x hxl
    have hxnot : x ∉ U.normalize.vertices := by
      intro hxE
      obtain ⟨m, hm, hxm⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hxE)
      have hmU : m ∈ U.chains := (List.mem_filter.mp hm).1
      have hmLen : 3 ≤ m.length := by simpa using (List.mem_filter.mp hm).2
      have hne : l ≠ m := by intro he; subst m; exact hlen hmLen
      exact List.disjoint_left.mp (U.disjoint_of_mem hl hmU hne) hxl hxm
    apply List.mem_toFinset.mpr
    apply List.mem_flatten.mpr
    refine ⟨chainRepresentatives Q [x], ?_, by simp [chainRepresentatives]⟩
    apply List.mem_map.mpr
    refine ⟨[x], ?_, rfl⟩
    change [x] ∈ U.normalize.chains ++ (Q \ U.normalize.toRaw.vertices).toList.map (fun v => [v])
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨x, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hxQ, hxnot⟩), rfl⟩
end CycleClique.Construction.RawPathSystem
namespace CycleClique.Construction.ExpandedPathSystem
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.of_amount_count {k : ℕ} (hopt : S.IsOptimal k)
    (T : ExpandedPathSystem G Q) (ha : T.amount = S.amount)
    (he : T.assignedCount = S.assignedCount) : T.IsOptimal k := by
  refine ⟨by simpa only [ha] using hopt.budget, ?_, ?_⟩
  · intro U hU
    simpa only [ha] using hopt.maximal U hU
  · intro U hU
    rw [he]
    exact hopt.minimal U (hU.trans ha)
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem representative_successor (U : RawPathSystem G Q) {x : V}
    (hx : x ∈ U.representatives) (hxQ : x ∉ Q) :
    ∃ l ∈ U.chains, ∃ A : List V, ∃ y : V, ∃ B : List V,
      l = A ++ x :: y :: B ∧ y ∉ U.representatives := by
  obtain ⟨r, hr, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, heqr⟩ := List.mem_map.mp hr
  subst r
  obtain ⟨A, B, he, _⟩ := chainRepresentatives_mem_cut hx
  have hBne : B ≠ [] := by
    intro hB
    have hxLast : x ∈ l.getLast? := by simp [he, hB]
    exact hxQ ((U.endpoints l hl).2 x hxLast)
  cases B with
  | nil => exact False.elim (hBne rfl)
  | cons y B =>
    refine ⟨l, hl, A, y, B, he, ?_⟩
    intro hy
    obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
    obtain ⟨m, hm, heqr⟩ := List.mem_map.mp hr
    subst r
    have hym : y ∈ m := (chainRepresentatives_sublist m).subset hy
    by_cases hlm : l = m
    · subst m
      obtain ⟨C, D, hc, hC⟩ := chainRepresentatives_mem_cut hy
      have he' : l = (A ++ [x]) ++ y :: B := by simpa [List.append_assoc] using he
      have hn : ((A ++ [x]) ++ y :: B).Nodup := he' ▸ (U.paths l hl).1
      have hny : y ∉ A ++ [x] := fun h => (List.nodup_append'.mp hn).2.2 h (by simp)
      have hnyB : y ∉ B := (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
      have hpref := (List.append_cons_inj_of_notMem hny hnyB).mp (he'.symm.trans hc)
      apply hxQ
      apply hC x
      rw [← hpref.1]
      simp
    · have hyl : y ∈ l := by simp [he]
      exact List.disjoint_left.mp (U.disjoint_of_mem hl hm hlm) hyl hym
theorem exists_two_outside_completed_representatives (S : ExpandedPathSystem G Q)
    (he : 2 ≤ S.assignedCount) :
    ∃ x ∈ S.toRaw.completeClique.representatives,
      ∃ y ∈ S.toRaw.completeClique.representatives, x ≠ y ∧ x ∉ Q ∧ y ∉ Q := by
  let L := S.toRaw.completeClique.representatives
  let O := L.filter (fun v => decide (v ∉ Q))
  have hO : O.Nodup := S.toRaw.completeClique.representatives_nodup.filter _
  have hcard : 2 ≤ O.toFinset.card := by
    rw [List.toFinset_card_of_nodup hO]
    change 2 ≤ chainOutsideCount Q S.toRaw.completeClique.representatives
    rw [completed_representatives_outside_count]
    exact he
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
  have hx' : x ∈ L ∧ x ∉ Q := by simpa [O] using hx
  have hy' : y ∈ L ∧ y ∉ Q := by simpa [O] using hy
  exact ⟨x, hx'.1, y, hy'.1, hxy, hx'.2, hy'.2⟩
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {X R : Finset V} {x y : V} {k : ℕ}
theorem representative_ball_one_extra (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hyX : y ∈ X) (hyR : y ∉ R)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ z ∈ R, x ≠ z → ¬ OutsidePath G (X : Set V) x z 1)
    (hmiss : ∀ u ∈ outsideBallFinset G X x 0, ¬ G.Adj u y) :
    R.card < (outsideBallFinset G X x 1).card := by
  have hxX := hRX hxR
  have hz := outsideBall_initial_growth (A := ∅) hxX (by simp) (by simp)
    (by simp) (hexpand x)
  simp only [Finset.card_empty, Nat.add_zero] at hz
  have hne : (outsideBallFinset G X x 0).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨u, hu⟩ := hne
  have hI : ({u} : Finset V) ⊆ outsideBallFinset G X x 0 := by simpa using hu
  have hAX : R.erase x ⊆ X := fun _ hv => hRX (Finset.mem_of_mem_erase hv)
  have hf : ∀ z ∈ R.erase x, ∀ d, 1 ≤ d → d ≤ 0 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x z d := by
    intro z hz d hd hdb hp
    have he : d = 1 := by omega
    subst d
    exact hforbid z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz).symm hp.toOutside
  have havoidR := closedNeighborhood_avoids_forbidden hxX hAX (by simp) hI hf
  have havoidy : y ∉ closedNeighborhood G {u} := by
    intro hc
    rcases mem_closedNeighborhood.mp hc with hcu | ⟨v, hv, hvy⟩
    · have he : y = u := Finset.mem_singleton.mp hcu
      exact (mem_outsideBallFinset.mp hu).1 (he ▸ hyX)
    · have he : v = u := Finset.mem_singleton.mp hv
      exact hmiss u hu (he ▸ hvy)
  have hAX' : insert y (R.erase x) ⊆ X := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hyX
    · exact hAX hz
  have havoid : ∀ z ∈ insert y (R.erase x), z ∉ closedNeighborhood G {u} := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact havoidy
    · exact havoidR z hz
  have hg := outsideBall_growth hAX' hI havoid (by simpa using hexpand u)
  have hyErase : y ∉ R.erase x := fun h => hyR (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hyErase] at hg
  have hc := Finset.card_erase_add_one hxR
  simp only [Finset.card_singleton, Nat.mul_one, Nat.reduceAdd] at hg
  omega
theorem representative_ball_one_not_clique (hxR : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hyX : y ∈ X) (hyR : y ∉ R) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (hforbid : ∀ z ∈ R, x ≠ z → ¬ OutsidePath G (X : Set V) x z 1)
    (hmiss : ∀ u ∈ outsideBallFinset G X x 0, ¬ G.Adj u y) :
    ¬ G.IsClique (outsideBallFinset G X x 1 : Set V) := by
  intro h
  have hcard := h.card_le_cliqueNum.trans hclique
  have hbig := representative_ball_one_extra hxR hRX hXk hyX hyR hexpand hforbid hmiss
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem exists_edge_detour (S : ExpandedPathSystem G Q)
    {P R : List (List V)} {A B J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q)
    (hJ : J.Nodup) (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : ExpandedPathSystem G Q,
      T.amount = S.amount + J.length ∧ T.incident = S.incident ∧
        T.assignedCount = S.assignedCount := by
  classical
  let old := A ++ x :: y :: B
  let new := A ++ x :: (J ++ y :: B)
  let C := P ++ new :: R
  have holdmem : old ∈ S.chains := by simp [hsys, old]
  have hflatold : S.chains.flatten =
      (P.flatten ++ A ++ [x]) ++ ((y :: B) ++ R.flatten) := by
    simp [hsys, List.append_assoc]
  have hflatnew : C.flatten =
      (P.flatten ++ A ++ [x]) ++ J ++ ((y :: B) ++ R.flatten) := by
    simp [C, new, List.append_assoc]
  have hflat : C.flatten.Nodup := by
    rw [hflatnew]
    apply nodup_insert_list
    · rw [← hflatold]
      exact S.flatten_nodup
    · exact hJ
    · rwa [← hflatold]
  have hnewpath : new.IsChain G.Adj := chain_insert_between
    (S.paths old holdmem).2 hpath
  have hxy : ¬ (x ∈ Q ∧ y ∈ Q) := by
    have h := List.isChain_append_cons_cons.mp (S.no_clique_steps old holdmem)
    exact h.2.1
  have hmid := chain_outside_interior hxy hJQ
  have hnewnoclique : new.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    chain_insert_between (S.no_clique_steps old holdmem) hmid
  have hmemOld : ∀ l, l ∈ P ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  let T : ExpandedPathSystem G Q := {
    chains := C
    nontrivial := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact S.nontrivial l (hmemOld l (Or.inl hl))
      · rcases List.mem_cons.mp hl with rfl | hl
        · have hlen := S.nontrivial old holdmem
          simp only [old, List.length_append, List.length_cons] at hlen
          simp only [new, List.length_append, List.length_cons]
          omega
        · exact S.nontrivial l (hmemOld l (Or.inr hl))
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      rcases List.mem_append.mp hl with hl | hl
      · exact (S.paths l (hmemOld l (Or.inl hl))).2
      · rcases List.mem_cons.mp hl with rfl | hl
        · exact hnewpath
        · exact (S.paths l (hmemOld l (Or.inr hl))).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact S.endpoints l (hmemOld l (Or.inl hl))
      · rcases List.mem_cons.mp hl with rfl | hl
        · have hh : new.head? = old.head? := head_insert_between A B J x y
          have ht : new.getLast? = old.getLast? := last_insert_between A B J x y
          rw [hh, ht]
          exact S.endpoints old holdmem
        · exact S.endpoints l (hmemOld l (Or.inr hl))
    no_clique_steps := by
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact S.no_clique_steps l (hmemOld l (Or.inl hl))
      · rcases List.mem_cons.mp hl with rfl | hl
        · exact hnewnoclique
        · exact S.no_clique_steps l (hmemOld l (Or.inr hl)) }
  have hverts : T.vertices = S.vertices ∪ J.toFinset := by
    ext v
    simp only [vertices, T, List.mem_toFinset, Finset.mem_union, hflatold, hflatnew,
      List.mem_append, List.mem_cons]
    tauto
  have hJdiff : J.toFinset \ Q = J.toFinset := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    apply Finset.disjoint_left.mpr
    intro v hv hvQ
    exact hJQ v (List.mem_toFinset.mp hv) hvQ
  have hJinter : J.toFinset ∩ Q = ∅ := by
    apply Finset.disjoint_iff_inter_eq_empty.mp
    exact Finset.sdiff_eq_self_iff_disjoint.mp hJdiff
  have hdisfin : Disjoint (S.vertices \ Q) J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hv hvJ
    exact List.disjoint_left.mp hdis (List.mem_toFinset.mp hvJ)
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
  have hamount : T.amount = S.amount + J.length := by
    change (T.vertices \ Q).card = (S.vertices \ Q).card + J.length
    rw [hverts, Finset.union_sdiff_distrib, hJdiff,
      Finset.card_union_of_disjoint hdisfin, List.toFinset_card_of_nodup hJ]
  have hincident : T.incident = S.incident := by
    simp only [incident, hverts, Finset.union_inter_distrib_right, hJinter, Finset.union_empty]
  have hcount : T.chains.length = S.chains.length := by
    simp [T, C, hsys]
  refine ⟨T, hamount, hincident, ?_⟩
  simp only [assignedCount, hincident, hcount]
theorem IsOptimal.no_edge_detour {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {P R : List (List V)} {A B J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q)
    (hJ : J.Nodup) (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) (hpos : J ≠ [])
    (hupper : S.amount + J.length + S.incident ≤ k + 1) : False := by
  obtain ⟨T, hamount, hincident, hcount⟩ :=
    S.exists_edge_detour hsys hJQ hJ hdis hpath
  apply hopt.criterion hk hQk hQ hcycle T
  · simp only [hcount, le_refl, ↓reduceIte, hamount]
    have : 0 < J.length := List.length_pos_iff.mpr hpos
    omega
  · simpa only [hamount, hincident] using hupper
theorem IsOptimal.forbidden_edge_detour {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {P R : List (List V)} {A B : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R)
    (hd : 1 ≤ d)
    (hupper : S.amount + d + S.incident ≤ k + 1) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
  classical
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hdis : J.Disjoint S.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzold
    exact hJout z hz (Or.inr (List.mem_toFinset.mpr hzold))
  apply hopt.no_edge_detour hk hQk hQ hcycle hsys hJQ hJ hdis hpath
  · intro he
    simp only [he, List.length_nil] at hJlen
    omega
  · simpa only [hJlen] using hupper
theorem IsOptimal.forbidden_one_vertex_edge_detour {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {P R : List (List V)} {A B : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: y :: B) :: R) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y 1 := by
  apply hopt.forbidden_edge_detour hk hQk hQ hcycle hsys (by omega)
  have hb := hopt.budget
  have hi := S.incident_le
  omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.interior_representative_extra_neighbor {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) {x : V}
    (hx : x ∈ S.representativeFinset) (hxQ : x ∉ Q) :
    ∃ y ∈ S.ground, y ∉ S.representativeFinset ∧
      ∀ u ∈ outsideBallFinset G S.ground x 0, ¬ G.Adj u y := by
  obtain ⟨l, hl, A, y, B, he, hy⟩ :=
    S.toRaw.completeClique.representative_successor (List.mem_toFinset.mp hx) hxQ
  have hlS : l ∈ S.chains := by
    change l ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hl
    · obtain ⟨v, hv, hlv⟩ := List.mem_map.mp hl
      have hxL : x ∈ l := by simp [he]
      have hxv : x = v := by simpa [← hlv] using hxL
      have hvQ := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).1
      exact False.elim (hxQ (hxv.symm ▸ hvQ))
  have hyL : y ∈ l := by simp [he]
  have hyS : y ∈ S.vertices := List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hlS, hyL⟩)
  refine ⟨y, Finset.mem_union_right _ hyS, ?_, ?_⟩
  · exact fun h => hy (List.mem_toFinset.mp h)
  · obtain ⟨P, R, hchains⟩ := List.append_of_mem hlS
    have hforbid := hopt.forbidden_one_vertex_edge_detour hk hQk hQ hcycle
      (by simpa [he] using hchains : S.chains = P ++ (A ++ x :: y :: B) :: R)
    have hc : (A ++ x :: y :: B).IsChain G.Adj := he ▸ (S.paths l hlS).2
    have hxy : G.Adj x y := (List.isChain_append_cons_cons.mp hc).2.1
    intro u hu huy
    have hball := mem_outsideBallFinset.mp hu
    have hxu := ((outsideBall_zero (S.representativeFinset_subset_ground hx)).mp hball).1
    apply hforbid
    simpa only [ground, Finset.coe_union] using
      outsidePath_one_of_common_neighbor hxy.ne hxu huy hball.1
theorem IsOptimal.two_interior_nonclique_balls {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (he : 2 ≤ S.assignedCount) :
    ∃ a ∈ S.representativeFinset, ∃ b ∈ S.representativeFinset, a ≠ b ∧
      ¬ G.IsClique (outsideBallFinset G S.ground a 1 : Set V) ∧
      ¬ G.IsClique (outsideBallFinset G S.ground b 1 : Set V) := by
  obtain ⟨a, ha, b, hb, hab, haQ, hbQ⟩ :=
    RawPathSystem.exists_two_outside_completed_representatives S he
  have haR : a ∈ S.representativeFinset := List.mem_toFinset.mpr ha
  have hbR : b ∈ S.representativeFinset := List.mem_toFinset.mpr hb
  have hclique' : G.cliqueNum ≤ S.representativeFinset.card := by
    simpa only [S.representativeFinset_card] using hclique
  have hnonclique : ∀ x ∈ S.representativeFinset, x ∉ Q →
      ¬ G.IsClique (outsideBallFinset G S.ground x 1 : Set V) := by
    intro x hx hxQ
    obtain ⟨y, hyX, hyR, hmiss⟩ := hopt.interior_representative_extra_neighbor hk hQk hQ hcycle hx hxQ
    exact representative_ball_one_not_clique hx S.representativeFinset_subset_ground
      (hopt.ground_card_le hQk) hyX hyR hclique' hexpand
      (fun z hz hne => hopt.representativeFinset_one_exclusion hk hQk hQ hcycle hx hz hne) hmiss
  exact ⟨a, haR, b, hbR, hab, hnonclique a haR haQ, hnonclique b hbR hbQ⟩
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
omit [Fintype V] in
theorem terminal_not_representative (S : ExpandedPathSystem G Q) {l : List V}
    (hl : l ∈ S.chains) {q : V} (hq : q ∈ l.getLast?) : q ∉ S.representativeFinset := by
  have hqQ := (S.endpoints l hl).2 q hq
  have hql : q ∈ l := List.mem_of_mem_getLast? hq
  have hqS : q ∈ S.vertices := List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨l, hl, hql⟩)
  intro hrep
  obtain ⟨r, hr, hqr⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hrep)
  obtain ⟨m, hm, her⟩ := List.mem_map.mp hr
  subst r
  have hqm : q ∈ m := (chainRepresentatives_sublist m).subset hqr
  change m ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hm
  rcases List.mem_append.mp hm with hm | hm
  · by_cases hlm : l = m
    · subst m
      have hhead := chainRepresentatives_clique_mem_head (S.no_clique_steps l hl) hqr hqQ
      have hlen := S.nontrivial l hl
      have hne : l ≠ [] := by intro he; simp [he] at hlen
      have hh : l.head hne = q := by
        simpa only [List.head?_eq_some_head hne, Option.mem_some_iff] using hhead
      have ht : l.getLast hne = q := by
        simpa only [List.getLast?_eq_some_getLast hne, Option.mem_some_iff] using hq
      obtain ⟨v, hv⟩ := ((S.paths l hl).1.head_eq_getLast_iff hne).mp (hh.trans ht.symm)
      simp [hv] at hlen
    · exact List.disjoint_left.mp (S.toRaw.disjoint_of_mem hl hm hlm) hql hqm
  · obtain ⟨v, hv, hmv⟩ := List.mem_map.mp hm
    have heq : q = v := by simpa [← hmv] using hqm
    have hvnot := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).2
    exact hvnot (heq ▸ hqS)
theorem IsOptimal.unused_representative_extra_neighbor {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hchains : S.chains ≠ [])
    {x : V} (hxQ : x ∈ Q) (hxS : x ∉ S.vertices) :
    ∃ y ∈ S.ground, y ∉ S.representativeFinset ∧
      ∀ u ∈ outsideBallFinset G S.ground x 0, ¬ G.Adj u y := by
  let l := S.chains.head hchains
  have hl : l ∈ S.chains := List.head_mem hchains
  have hlen := S.nontrivial l hl
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  let q := l.getLast hne
  have hq : q ∈ l.getLast? := List.getLast?_eq_some_getLast hne
  have hqQ := (S.endpoints l hl).2 q hq
  have hqS : q ∈ S.vertices := List.mem_toFinset.mpr
    (List.mem_flatten.mpr ⟨l, hl, List.getLast_mem hne⟩)
  have hqrep := S.terminal_not_representative hl hq
  have hxrep := RawPathSystem.completed_unused_representative S hxQ hxS
  have hqreverse : q ∈ S.toRaw.completeClique.reverseChains.representatives := by
    apply RawPathSystem.reversed_terminal_representative S.toRaw.completeClique
      (List.mem_append_left _ hl : l ∈ S.toRaw.completeClique.chains) hq
  have hvertices : ∀ v ∈ S.toRaw.completeClique.reverseChains.vertices,
      v ∈ Q ∨ v ∈ S.vertices := by
    intro v hv
    rw [RawPathSystem.reverseChains_vertices, RawPathSystem.completeClique_vertices] at hv
    exact (Finset.mem_union.mp hv).symm
  have hxq : x ≠ q := fun h => hxS (h.symm ▸ hqS)
  have hf := hopt.representatives_one_exclusion hk hQk hQ hcycle
    S.toRaw.completeClique.reverseChains (by simp) hvertices hxrep.2 hqreverse hxq
  refine ⟨q, Finset.mem_union_left _ hqQ, hqrep, ?_⟩
  intro u hu huq
  have hball := mem_outsideBallFinset.mp hu
  have hxX : x ∈ S.ground := Finset.mem_union_left _ hxQ
  have hxu := ((outsideBall_zero hxX).mp hball).1
  apply hf
  simpa only [ground, Finset.coe_union] using
    outsidePath_one_of_common_neighbor hxq hxu huq hball.1
theorem IsOptimal.two_unused_nonclique_balls {k : ℕ} (hopt : S.IsOptimal k)
    (hk : 3 ≤ k) (hQk : Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (he : S.assignedCount = 1) (ht : 4 ≤ Q.card) :
    ∃ a ∈ S.representativeFinset, ∃ b ∈ S.representativeFinset, a ≠ b ∧
      ¬ G.IsClique (outsideBallFinset G S.ground a 1 : Set V) ∧
      ¬ G.IsClique (outsideBallFinset G S.ground b 1 : Set V) := by
  have hinc := S.incident_eq_two_of_assignedCount_one he
  have hcard := Finset.card_sdiff_add_card_inter Q S.vertices
  have hinter : (Q ∩ S.vertices).card = S.incident := by
    simp [incident, Finset.inter_comm]
  have htwo : 1 < (Q \ S.vertices).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  have hchains : S.chains ≠ [] := by
    intro hc
    have hraw := S.assignedCount_eq_raw
    simp [hc, rawAssignedCount, he] at hraw
  have hclique' : G.cliqueNum ≤ S.representativeFinset.card := by
    simpa only [S.representativeFinset_card] using hclique
  have hnonclique : ∀ x ∈ Q \ S.vertices,
      x ∈ S.representativeFinset ∧ ¬ G.IsClique (outsideBallFinset G S.ground x 1 : Set V) := by
    intro x hx
    obtain ⟨hxQ, hxS⟩ := Finset.mem_sdiff.mp hx
    have hxR : x ∈ S.representativeFinset := List.mem_toFinset.mpr
      (RawPathSystem.completed_unused_representative S hxQ hxS).1
    obtain ⟨y, hyX, hyR, hmiss⟩ := hopt.unused_representative_extra_neighbor hk hQk hQ hcycle hchains hxQ hxS
    refine ⟨hxR, representative_ball_one_not_clique hxR S.representativeFinset_subset_ground
      (hopt.ground_card_le hQk) hyX hyR hclique' hexpand ?_ hmiss⟩
    exact fun z hz hne => hopt.representativeFinset_one_exclusion hk hQk hQ hcycle hxR hz hne
  exact ⟨a, (hnonclique a ha).1, b, (hnonclique b hb).1, hab,
    (hnonclique a ha).2, (hnonclique b hb).2⟩
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V}
omit [Fintype V] in
theorem exists_chain_avoiding (S : ExpandedPathSystem G Q)
    (hc : 2 ≤ S.chains.length) (x : V) : ∃ l ∈ S.chains, x ∉ l := by
  cases hcs : S.chains with
  | nil => simp only [hcs, List.length_nil] at hc; omega
  | cons l C =>
    cases C with
    | nil => simp only [hcs, List.length_cons, List.length_nil] at hc; omega
    | cons m C =>
      have hdis : l.Disjoint m :=
        (List.pairwise_cons.mp (show (l :: m :: C).Pairwise List.Disjoint by
          rw [← hcs]; exact S.disjoint)).1 m (by simp)
      by_cases hx : x ∈ l
      · exact ⟨m, by simp, fun hxm => List.disjoint_left.mp hdis hx hxm⟩
      · exact ⟨l, by simp, hx⟩
theorem IsOptimal.representative_extra_terminal {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hc : 2 ≤ S.chains.length) {x : V} (hx : x ∈ S.representativeFinset) :
    ∃ q ∈ S.ground, q ∉ S.representativeFinset ∧
      ∀ u ∈ outsideBallFinset G S.ground x 0, ¬ G.Adj u q := by
  obtain ⟨l, hl, hxl⟩ := S.exists_chain_avoiding hc x
  have hlen := S.nontrivial l hl
  have hne : l ≠ [] := by intro he; simp [he] at hlen
  let q := l.getLast hne
  have hq : q ∈ l.getLast? := List.getLast?_eq_some_getLast hne
  have hqQ := (S.endpoints l hl).2 q hq
  have hqrep := S.terminal_not_representative hl hq
  let U := S.toRaw.completeClique.orientChains (fun r => decide (r = l))
  have hqU : q ∈ U.representatives := by
    apply RawPathSystem.representatives_orientChains_terminal S.toRaw.completeClique
      (List.mem_append_left _ hl : l ∈ S.toRaw.completeClique.chains) (by simp) hq
  have hxU : x ∈ U.representatives := by
    obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hx)
    obtain ⟨m, hm, he⟩ := List.mem_map.mp hr
    subst r
    have hxm : x ∈ m := (chainRepresentatives_sublist m).subset hxr
    have hml : m ≠ l := by intro he; subst m; exact hxl hxm
    exact RawPathSystem.representatives_orientChains_unchanged S.toRaw.completeClique
      hm (by simp [hml]) hxr
  have hUamount : U.amount = S.amount := by simp [U]
  have hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices := by
    intro v hv
    simp only [U, RawPathSystem.orientChains_vertices,
      RawPathSystem.completeClique_vertices] at hv
    exact (Finset.mem_union.mp hv).symm
  have hxq : x ≠ q := by intro he; exact hqrep (he ▸ hx)
  have hf := hopt.representatives_one_exclusion hk hQk hQ hcycle U hUamount hUvertices
    hxU hqU hxq
  refine ⟨q, Finset.mem_union_left _ hqQ, hqrep, ?_⟩
  intro u hu huq
  have hball := mem_outsideBallFinset.mp hu
  have hxu := ((outsideBall_zero (S.representativeFinset_subset_ground hx)).mp hball).1
  apply hf
  simpa only [ground, Finset.coe_union] using
    outsidePath_one_of_common_neighbor hxq hxu huq hball.1
theorem IsOptimal.terminal_first_ball {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ Q.card) (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    {x : V} (hx : x ∈ S.representativeFinset) :
    Q.card + 1 ≤ (outsideBallFinset G S.ground x 1).card ∧
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2 := by
  obtain ⟨q, hqX, hqR, hmiss⟩ := hopt.representative_extra_terminal hk hQk hQ hcycle hc hx
  have hbig := representative_ball_one_extra hx S.representativeFinset_subset_ground
    (hopt.ground_card_le hQk) hqX hqR hexpand
    (fun y hy hne => hopt.representativeFinset_one_exclusion hk hQk hQ hcycle hx hy hne)
    hmiss
  rw [S.representativeFinset_card] at hbig
  refine ⟨by omega, independent_pair_of_not_clique ?_⟩
  intro hC
  have hh := hC.card_le_cliqueNum.trans hclique
  omega
end CycleClique.Construction.ExpandedPathSystem
namespace CycleClique.Construction
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V}
theorem outsideBall_two_triple_of_first_pair (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hkt : 2 * t ≤ k)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    {X : Finset V} {x : V} (hXk : X.card ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : HasIndependent (G.induce (outsideBallFinset G X x 1 : Set V)) 2) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
  obtain ⟨I, hI, hind, hIcard⟩ := exists_independent_subset hpair
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth (A := ∅) (by simp) hI (by simp) (hexpand I hind hne)
  rw [hIcard] at hg
  simp only [Finset.card_empty, Nat.add_zero, Nat.reduceAdd] at hg
  apply size_test hCE hk ht hcycle hclique (outsideBallFinset G X x 2)
  exact max_lt_iff.mpr ⟨by omega, by omega⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.terminal_oriented_first_ball {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ Q.card) (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card)
    (p : List V → Bool) {x : V}
    (hx : x ∈ (S.toRaw.completeClique.orientChains p).representatives) :
    Q.card + 1 ≤ (outsideBallFinset G S.ground x 1).card ∧
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2 := by
  let U := S.toRaw.completeClique.orientChains p
  let T := U.normalize
  have hTa : T.amount = S.amount := by simp [T, U]
  have hTe : T.assignedCount = S.assignedCount := by simp [T, U]
  have hTi : T.incident = S.incident := by simp [T, U]
  have hTground : T.ground = S.ground := by
    simp only [T, U, RawPathSystem.normalize_ground, RawPathSystem.orientChains_vertices,
      RawPathSystem.completeClique_vertices]
    change Q ∪ (S.vertices ∪ Q) = Q ∪ S.vertices
    ext v
    simp only [Finset.mem_union]
    tauto
  have hcT : 2 ≤ T.chains.length := by
    have hT := T.assignedCount_add_chains_length
    have hS := S.assignedCount_add_chains_length
    rw [hTe, hTi] at hT
    omega
  have hoptT := hopt.of_amount_count T hTa hTe
  have hxT : x ∈ T.representativeFinset := U.normalize_representative_mem hx
  obtain ⟨hcard, hpair⟩ :=
    hoptT.terminal_first_ball hk hQk hQ hcycle hclique hcT hexpand hxT
  refine ⟨by simpa only [hTground] using hcard, ?_⟩
  convert hpair using 1 <;> rw [hTground]
theorem IsOptimal.terminal_oriented_second_ball (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 5 ≤ k) (hQk : Q.card ≤ k) (ht : 1 ≤ Q.card)
    (hkt : 2 * Q.card ≤ k) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (p : List V → Bool) {x : V}
    (hx : x ∈ (S.toRaw.completeClique.orientChains p).representatives) :
    HasIndependent (G.induce (outsideBallFinset G S.ground x 2 : Set V)) 3 := by
  have hsingle : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa using hexpand {v} (by simp) (by simp)
  have hp := (hopt.terminal_oriented_first_ball (by omega) hQk hQ hcycle
    hclique hc hsingle p hx).2
  exact outsideBall_two_triple_of_first_pair hCE hk ht hkt hcycle hclique
    (hopt.ground_card_le hQk) hexpand hp
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
private theorem mul_length_le_sum {d : ℕ} {w : List ℕ} (h : ∀ b ∈ w, d ≤ b) :
    d * w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.length_cons, Nat.mul_succ, List.sum_cons]
    omega
theorem IsOptimal.terminal_different_chain_starts {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P M R : List (List V)} {A B C D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    S.amount = k - Q.card ∧ A = [] ∧ C = [] ∧ d * S.assignedCount ≤ S.amount := by
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, original, output, kept, removed, hT, hTa, ho, hout, hp, hq⟩ :=
    U.replace_different_chains_profiled hsys hA hC hJ hJQ hpos hdis hpath
  obtain ⟨hL, _, hkept, _, hweights⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle
    hd hd' U T hUa hUe ho hout hp hq (by omega)
  have hTcount : T.assignedCount = S.assignedCount + 1 := by
    have he := hq.length_eq
    rw [hout.length_eq, List.length_cons, hkept] at he
    change T.assignedCount = S.assignedCount + 1 at he
    exact he
  have hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q := by
    intro v hv
    apply (U.endpoints _ (show A ++ x :: B ∈ U.chains by simp [hsys])).2 v
    have he := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q := by
    intro v hv
    apply (U.endpoints _ (show C ++ y :: D ∈ U.chains by simp [hsys])).2 v
    have he := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hcount := RawPathSystem.different_chain_count (P := P) (M := M) (R := R) hA hC hB hD hJQ
  have hcount' : T.assignedCount + (if A = [] then 0 else 1) +
      (if C = [] then 0 else 1) = U.assignedCount + 1 := by
    simpa only [RawPathSystem.assignedCount, hT, hsys] using hcount
  rw [hTcount, hUe] at hcount'
  have hAnil : A = [] := by
    by_contra hn
    simp only [hn, ↓reduceIte] at hcount'
    omega
  have hCnil : C = [] := by
    by_contra hn
    simp only [hn, ↓reduceIte] at hcount'
    omega
  have hsum : original.sum = S.amount := by
    rw [ho.sum_eq, ← U.amount_eq_outside_count, hUa]
  have hlen : original.length = S.assignedCount := ho.length_eq.trans hUe
  have hbound := mul_length_le_sum hweights
  rw [hlen, hsum] at hbound
  exact ⟨hL, hAnil, hCnil, hbound⟩
theorem IsOptimal.terminal_same_chain_exclusion {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P R : List (List V)} {A B D : List V} {x y : V}
    (hsys : U.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q) :
    ¬ OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
  intro h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, original, output, kept, removed, hT, hTa, ho, hout, hp, hq⟩ :=
    U.replace_same_chain_profiled hsys hA hB hJ hJQ hpos hdis hpath
  obtain ⟨_, _, hkept, _, _⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle
    hd hd' U T hUa hUe ho hout hp hq (by omega)
  have hTcount : T.assignedCount = S.assignedCount + 1 := by
    have he := hq.length_eq
    rw [hout.length_eq, List.length_cons, hkept] at he
    change T.assignedCount = S.assignedCount + 1 at he
    exact he
  have hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q := by
    intro v hv
    apply (U.endpoints _ (show A ++ (x :: B) ++ y :: D ∈ U.chains by simp [hsys])).2 v
    have he := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hcount := RawPathSystem.same_chain_count (P := P) (R := R) hA hB hD hJQ
  have hcount' : T.assignedCount + (if A = [] then 0 else 1) = U.assignedCount := by
    simpa only [RawPathSystem.assignedCount, hT, hsys] using hcount
  rw [hTcount, hUe] at hcount'
  omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.RawPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem starting_replacement_incident (U T : RawPathSystem G Q)
    {P M R : List (List V)} {B D J : List V} {x y : V}
    (hsys : U.chains = P ++ (x :: B) :: M ++ (y :: D) :: R)
    (htsys : T.chains = P ++ [] :: M ++ [] :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    T.normalize.incident = U.normalize.incident +
      (if B = [] then 1 else 0) + (if D = [] then 1 else 0) := by
  have hmemB : x :: B ∈ U.chains := by simp [hsys]
  have hmemD : y :: D ∈ U.chains := by simp [hsys]
  have hB : activeCliqueCount Q (x :: B) + (if B = [] then 1 else 0) =
      chainCliqueCount Q (x :: B) := by
    simpa using activeCliqueCount_add_singleton (by simp)
      (U.endpoints _ hmemB) (U.no_clique_steps _ hmemB)
  have hD : activeCliqueCount Q (y :: D) + (if D = [] then 1 else 0) =
      chainCliqueCount Q (y :: D) := by
    simpa using activeCliqueCount_add_singleton (by simp)
      (U.endpoints _ hmemD) (U.no_clique_steps _ hmemD)
  have hmerged : activeCliqueCount Q (B.reverse ++ x :: (J ++ y :: D)) =
      chainCliqueCount Q (x :: B) + chainCliqueCount Q (y :: D) := by
    have heq : B.reverse ++ x :: (J ++ y :: D) = (x :: B).reverse ++ J ++ (y :: D) := by
      simp [List.append_assoc]
    have hlen : 3 ≤ (B.reverse ++ x :: (J ++ y :: D)).length := by
      have hh := List.length_pos_iff.mpr hJne
      simp only [List.length_append, List.length_reverse, List.length_cons]
      omega
    simp only [activeCliqueCount, hlen, ↓reduceIte]
    rw [heq, chainCliqueCount_append,
      chainCliqueCount_append, chainCliqueCount_reverse, chainCliqueCount_eq_zero hJQ]
    omega
  rw [normalize_incident, normalize_incident]
  simp only [htsys, hsys, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons, activeCliqueCount_nil]
  omega
theorem starting_replacement_incident_le (U T : RawPathSystem G Q)
    {P M R : List (List V)} {B D J : List V} {x y : V}
    (hsys : U.chains = P ++ (x :: B) :: M ++ (y :: D) :: R)
    (htsys : T.chains = P ++ [] :: M ++ [] :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    T.normalize.incident ≤ U.normalize.incident + 2 := by
  rw [starting_replacement_incident U T hsys htsys hJQ hJne]
  split_ifs <;> omega
end CycleClique.Construction.RawPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
theorem oriented_complete_singleton_iff (S : ExpandedPathSystem G Q)
    (p : List V → Bool) {l : List V} {x : V}
    (hl : l ∈ (S.toRaw.completeClique.orientChains p).chains) (hx : x ∈ l) :
    l.length = 1 ↔ x ∉ S.vertices := by
  classical
  change l ∈ S.toRaw.completeClique.chains.map (RawPathSystem.orientedChain p) at hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  have hp := RawPathSystem.orientedChain_perm p m
  have hmx : x ∈ m := hp.mem_iff.mp hx
  change m ∈ S.chains ++ (Q \ S.toRaw.vertices).toList.map (fun v => [v]) at hm
  rcases List.mem_append.mp hm with hm | hm
  · have hxS : x ∈ S.vertices :=
      List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨m, hm, hmx⟩)
    have hn := S.nontrivial m hm
    constructor
    · intro hlen
      have hh := hp.length_eq
      omega
    · intro hnot
      exact False.elim (hnot hxS)
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    have hxv : x = v := by simpa using hmx
    subst x
    have hvnot : v ∉ S.vertices := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hv)).2
    have hlen : (RawPathSystem.orientedChain p [v]).length = 1 := hp.length_eq
    exact ⟨fun _ => hvnot, fun _ => hlen⟩
theorem oriented_complete_tail_nil_iff (S : ExpandedPathSystem G Q)
    (p : List V → Bool) {B : List V} {x : V}
    (hl : x :: B ∈ (S.toRaw.completeClique.orientChains p).chains) :
    B = [] ↔ x ∉ S.vertices := by
  simpa using S.oriented_complete_singleton_iff p hl (by simp)
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*}
theorem subset_pair_of_card_le_indicators (M : Finset V) {x y : V} (hne : x ≠ y)
    (hcard : M.card ≤ (if x ∈ M then 1 else 0) + (if y ∈ M then 1 else 0)) :
    M ⊆ {x, y} := by
  classical
  by_cases hx : x ∈ M
  · by_cases hy : y ∈ M
    · have hsub : ({x, y} : Finset V) ⊆ M := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · obtain rfl := Finset.mem_singleton.mp hz
          exact hy
      have heq : ({x, y} : Finset V) = M := Finset.eq_of_subset_of_card_le hsub (by
        have hh : M.card ≤ 2 := by simpa [hx, hy] using hcard
        simpa [hne] using hh)
      rw [← heq]
    · have hsub : ({x} : Finset V) ⊆ M := by simp [hx]
      have heq : ({x} : Finset V) = M := Finset.eq_of_subset_of_card_le hsub (by
        simpa [hx, hy] using hcard)
      rw [← heq]
      simp
  · by_cases hy : y ∈ M
    · have hsub : ({y} : Finset V) ⊆ M := by simp [hy]
      have heq : ({y} : Finset V) = M := Finset.eq_of_subset_of_card_le hsub (by
        simpa [hx, hy] using hcard)
      rw [← heq]
      simp
    · have he : M = ∅ := Finset.card_eq_zero.mp (by simpa [hx, hy] using hcard)
      simp [he]
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.terminal_starting_classification {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount) (hUi : U.normalize.incident = S.incident)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    {P M R : List (List V)} {B D : List V} {x y : V}
    (hsys : U.chains = P ++ (x :: B) :: M ++ (y :: D) :: R)
    (hBx : B = [] ↔ x ∉ S.vertices) (hDy : D = [] ↔ y ∉ S.vertices)
    (hne : x ≠ y) (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    S.amount = k - Q.card ∧
      (∃ original, SystemAssignedAmounts Q U.chains original ∧ ∀ b ∈ original, d ≤ b) ∧
      ((d = 2 ∧ Q.card ≤ S.incident + 2 ∧ Q \ S.vertices ⊆ {x, y}) ∨
       (d = 3 ∧ (Q.card = 9 ∨ Q.card = 11) ∧
         2 * S.assignedCount = Q.card - 3 ∧ S.incident = Q.card - 3 ∧
         (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices) ∨
       (d = 5 ∧ Q.card = 9 ∧ k = 19 ∧ S.assignedCount = 2 ∧ S.incident = 4 ∧
         (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices)) := by
  classical
  obtain ⟨hL, _, _, hde⟩ := hopt.terminal_different_chain_starts ht hQk hkQ hQ hcycle hd hd'
    U hUa hUe hUvertices (A := []) (C := []) (by simpa using hsys) (by simp) (by simp) h
  obtain ⟨J, hJ, hJlen, hJout, hpath⟩ := h.interior
  have hJQ : ∀ z ∈ J, z ∉ Q := fun z hz hzQ => hJout z hz (Or.inl hzQ)
  have hpos : J ≠ [] := by intro he; simp only [he, List.length_nil] at hJlen; omega
  have hdis : J.Disjoint U.chains.flatten := by
    apply List.disjoint_left.mpr
    intro z hz hzU
    exact hJout z hz (hUvertices z (List.mem_toFinset.mpr hzU))
  obtain ⟨T, original, output, kept, removed, hT, hTa, ho, hout, hp, hq⟩ :=
    U.replace_different_chains_profiled (A := []) (C := [])
      (by simpa using hsys) (by simp) (by simp) hJ hJQ hpos hdis hpath
  obtain ⟨_, _, _, _, hweights⟩ := hopt.terminal_increment_profiles ht hQk hkQ hQ hcycle
    hd hd' U T hUa hUe ho hout hp hq (by omega)
  have hTchain : T.chains = P ++ [] :: M ++ [] ::
      (B.reverse ++ x :: (J ++ y :: D)) :: R := by simpa using hT
  have hTi := U.starting_replacement_incident T hsys hTchain hJQ hpos
  rw [hUi] at hTi
  have hTna : T.normalize.amount = S.amount + d := by
    rw [RawPathSystem.normalize_amount]
    omega
  have hd2 : 2 ≤ d := by
    by_contra hn
    have hd1 : d = 1 := by omega
    exact hopt.no_one_vertex_increase (by omega) hQk hQ hcycle T.normalize (by omega)
  have hinterval : k + 1 < T.normalize.amount + T.normalize.incident := by
    by_contra hn
    exact T.normalize.forbidden_interval (by omega) hQ hcycle (by omega) (by omega)
  have htarget : Q.card + 2 ≤ S.incident + d +
      (if B = [] then 1 else 0) + (if D = [] then 1 else 0) := by omega
  have htv : Q.card ≤ S.incident + d := by
    split_ifs at htarget <;> omega
  have hxQ : x ∈ Q := (U.endpoints _ (show x :: B ∈ U.chains by simp [hsys])).1 x (by simp)
  have hyQ : y ∈ Q := (U.endpoints _ (show y :: D ∈ U.chains by simp [hsys])).1 y (by simp)
  have hmissing : (Q \ S.vertices).card + S.incident = Q.card := by
    simpa only [incident, Finset.inter_comm] using Finset.card_sdiff_add_card_inter Q S.vertices
  have hBxM : B = [] ↔ x ∈ Q \ S.vertices := by
    simpa only [Finset.mem_sdiff, hxQ, true_and] using hBx
  have hDyM : D = [] ↔ y ∈ Q \ S.vertices := by
    simpa only [Finset.mem_sdiff, hyQ, true_and] using hDy
  have hboth (ha : 2 ≤ (if B = [] then 1 else 0) + (if D = [] then 1 else 0)) :
      x ∉ S.vertices ∧ y ∉ S.vertices := by
    have hBnil : B = [] := by by_contra hn; simp only [hn, ↓reduceIte] at ha; split_ifs at ha <;> omega
    have hDnil : D = [] := by by_contra hn; simp only [hn, ↓reduceIte] at ha; (split_ifs at ha; omega)
    exact ⟨hBx.mp hBnil, hDy.mp hDnil⟩
  refine ⟨hL, ⟨original, ho, hweights⟩, ?_⟩
  rcases terminal_classification_arithmetic ht hQk hkQ hL hd2 hd' hde htv
      S.incident_le_twice_assignedCount with htwo | hthree | hfive
  · obtain ⟨hd2, hv⟩ := htwo
    refine Or.inl ⟨hd2, hv, ?_⟩
    apply subset_pair_of_card_le_indicators _ hne
    simp only [← hBxM, ← hDyM]
    omega
  · obtain ⟨hd3, ht3, he3, hv3⟩ := hthree
    have hmiss := hboth (by omega)
    refine Or.inr (Or.inl ⟨hd3, ht3, he3, hv3, ?_, hmiss.1, hmiss.2⟩)
    exact S.matching_of_incident_eq_twice (by omega)
  · obtain ⟨hd5, ht5, hk5, he5, hv5⟩ := hfive
    have hmiss := hboth (by omega)
    refine Or.inr (Or.inr ⟨hd5, ht5, hk5, he5, hv5, ?_, hmiss.1, hmiss.2⟩)
    exact S.matching_of_incident_eq_twice (by omega)
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
abbrev TerminalAlternative (S : ExpandedPathSystem G Q) (k d : ℕ) (x y : V) : Prop :=
  (d = 2 ∧ Q.card ≤ S.incident + 2 ∧ Q \ S.vertices ⊆ {x, y}) ∨
  (d = 3 ∧ (Q.card = 9 ∨ Q.card = 11) ∧
    2 * S.assignedCount = Q.card - 3 ∧ S.incident = Q.card - 3 ∧
    (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices) ∨
  (d = 5 ∧ Q.card = 9 ∧ k = 19 ∧ S.assignedCount = 2 ∧ S.incident = 4 ∧
    (∀ l ∈ S.chains, chainCliqueCount Q l = 2) ∧ x ∉ S.vertices ∧ y ∉ S.vertices)
theorem IsOptimal.terminal_representative_classification {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (U : RawPathSystem G Q) (hUa : U.amount = S.amount)
    (hUe : U.assignedCount = S.assignedCount) (hUi : U.normalize.incident = S.incident)
    (hUvertices : ∀ v ∈ U.vertices, v ∈ Q ∨ v ∈ S.vertices)
    (hsingleton : ∀ l ∈ U.chains, ∀ x ∈ l, l.length = 1 ↔ x ∉ S.vertices)
    {x y : V} (hx : x ∈ U.representatives) (hy : y ∈ U.representatives) (hne : x ≠ y)
    (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    x ∈ Q ∧ y ∈ Q ∧ S.amount = k - Q.card ∧ d * S.assignedCount ≤ S.amount ∧
      TerminalAlternative S k d x y := by
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l', hl', heql⟩ := List.mem_map.mp hl
  subst l
  obtain ⟨m, hm, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨m', hm', heqm⟩ := List.mem_map.mp hm
  subst m
  have hxc := chainRepresentatives_mem_cut hx
  have hyc := chainRepresentatives_mem_cut hy
  by_cases hlm : l' = m'
  · subst m'
    obtain ⟨P, R, hchains⟩ := List.append_of_mem hl'
    rcases repCuts_ordered (U.paths l' hl').1 hne hxc hyc with
      ⟨A, B, D, he, hA, hB⟩ | ⟨A, B, D, he, hA, hB⟩
    · exact False.elim (hopt.terminal_same_chain_exclusion ht hQk hkQ hQ hcycle hd hd'
        U hUa hUe hUvertices (by simpa [he] using hchains) hA hB h)
    · exact False.elim (hopt.terminal_same_chain_exclusion ht hQk hkQ hQ hcycle hd hd'
        U hUa hUe hUvertices (by simpa [he] using hchains) hA hB h.reverse)
  · obtain ⟨R, hp⟩ := U.bring_two_front hl' hm' hlm
    let U' := U.reorder (l' :: m' :: R) hp
    have hUa' : U'.amount = S.amount := by simpa [U'] using hUa
    have hUe' : U'.assignedCount = S.assignedCount := by simpa [U'] using hUe
    have hUi' : U'.normalize.incident = S.incident := by simpa [U'] using hUi
    have hUvertices' : ∀ v ∈ U'.vertices, v ∈ Q ∨ v ∈ S.vertices := by
      simpa [U'] using hUvertices
    obtain ⟨A, B, he₁, hA⟩ := hxc
    obtain ⟨C, D, he₂, hC⟩ := hyc
    have hsys : U'.chains = [] ++ (A ++ x :: B) :: [] ++ (C ++ y :: D) :: R := by
      simp [U', RawPathSystem.reorder, he₁, he₂]
    obtain ⟨hL, hAnil, hCnil, hde⟩ := hopt.terminal_different_chain_starts ht hQk hkQ hQ hcycle
      hd hd' U' hUa' hUe' hUvertices' hsys hA hC h
    subst A
    subst C
    have hmemB : x :: B ∈ U.chains := by
      have hh := hl'
      rw [he₁] at hh
      simpa using hh
    have hmemD : y :: D ∈ U.chains := by
      have hh := hm'
      rw [he₂] at hh
      simpa using hh
    have hBx : B = [] ↔ x ∉ S.vertices := by simpa using hsingleton _ hmemB x (by simp)
    have hDy : D = [] ↔ y ∉ S.vertices := by simpa using hsingleton _ hmemD y (by simp)
    obtain ⟨_, _, halt⟩ := hopt.terminal_starting_classification ht hQk hkQ hQ hcycle hd hd'
      U' hUa' hUe' hUi' hUvertices' (P := []) (M := []) (R := R) (by simpa using hsys) hBx hDy hne h
    exact ⟨(U.endpoints _ hmemB).1 x (by simp),
      (U.endpoints _ hmemD).1 y (by simp), hL, hde, halt⟩
theorem IsOptimal.terminal_completed_classification {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    (p : List V → Bool) {x y : V}
    (hx : x ∈ (S.toRaw.completeClique.orientChains p).representatives)
    (hy : y ∈ (S.toRaw.completeClique.orientChains p).representatives) (hne : x ≠ y)
    (h : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    x ∈ Q ∧ y ∈ Q ∧ S.amount = k - Q.card ∧ d * S.assignedCount ≤ S.amount ∧
      TerminalAlternative S k d x y := by
  apply hopt.terminal_representative_classification ht hQk hkQ hQ hcycle hd hd'
    (S.toRaw.completeClique.orientChains p) (by simp) (by simp) (by simp) ?_
    (fun l hl x hx => S.oriented_complete_singleton_iff p hl hx) hx hy hne h
  intro v hv
  rw [RawPathSystem.orientChains_vertices, RawPathSystem.completeClique_vertices] at hv
  exact (Finset.mem_union.mp hv).symm
theorem TerminalAlternative.parameter_unique {k d d' : ℕ} {x y x' y' : V}
    (ht : 9 ≤ Q.card) (h : TerminalAlternative S k d x y)
    (h' : TerminalAlternative S k d' x' y') : d = d' := by
  rcases h with ⟨hd, hv, _⟩ | ⟨hd, _, _, hv, _, _, _⟩ | ⟨hd, ht9, _, _, hv, _, _, _⟩ <;>
    rcases h' with ⟨hd', hv', _⟩ | ⟨hd', _, _, hv', _, _, _⟩ |
      ⟨hd', ht9', _, _, hv', _, _, _⟩ <;> omega
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V}
theorem radius_two_triple_of_separated_first_pair (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) {X R : Finset V} {x : V}
    (hx : x ∈ R) (hRX : R ⊆ X) (hXk : X.card ≤ k) (hsize : 2 * t < k + R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hforbid : ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 2 →
      ¬ OutsidePath G (X : Set V) x y d)
    (hpair : HasIndependent (G.induce (outsideBallFinset G X x 1 : Set V)) 2) :
    HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
  obtain ⟨I, hI, hind, hIcard⟩ := exists_independent_subset hpair
  have hAX : R.erase x ⊆ X := fun _ hy => hRX (Finset.mem_of_mem_erase hy)
  have hf : ∀ y ∈ R.erase x, ∀ d, 1 ≤ d → d ≤ 1 + 1 →
      ¬ PositiveOutsidePath G (X : Set V) x y d := by
    intro y hy d hd hdb hp
    exact hforbid y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm
      d hd (by omega) hp.toOutside
  have havoid := closedNeighborhood_avoids_forbidden (hRX hx) hAX (by simp) hI hf
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hg := outsideBall_growth hAX hI havoid (hexpand I hind hne)
  rw [hIcard] at hg
  have hc := Finset.card_erase_add_one hx
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr ⟨x, hx⟩
  simp only [Nat.reduceAdd] at hg
  apply size_test hCE hk ht hcycle hclique (outsideBallFinset G X x 2)
  exact max_lt_iff.mpr ⟨by omega, by omega⟩
theorem radius_two_packing_bound {k : ℕ} (hbound : IndependenceBound G k)
    {X R : Finset V} (hRX : R ⊆ X)
    (hweight : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3)
    (hforbid : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d) : 3 * R.card ≤ k := by
  have hp := packing_test hbound X (fun i : R => i.val) (fun _ => 3) (fun _ => 3)
    Subtype.val_injective (fun i => hRX i.property)
    (fun i => by simpa only [packingRegion] using hweight i i.property)
    (fun i j hij => by
      simp only [PackingCompatible, OfNat.ofNat_ne_zero, false_and, ↓reduceIte]
      intro d hd hdb
      exact hforbid i i.property j j.property (fun h => hij (Subtype.ext h)) d hd
        (by omega))
  simpa [Nat.mul_comm] using hp
theorem terminal_uniform_packing_contradiction (hCE : CEAlphaTwo) {k t : ℕ}
    (ht : 9 ≤ t) (hklo : 2 * t - 2 ≤ k) (hkhi : k ≤ 2 * t + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (hbound : IndependenceBound G k) {X R : Finset V}
    (hRX : R ⊆ X) (hXk : X.card ≤ k) (hRlarge : t - 2 ≤ R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G X x 1 : Set V)) 2)
    (hforbid : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d) : False := by
  have htriple : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G X x 2 : Set V)) 3 := by
    intro x hx
    exact radius_two_triple_of_separated_first_pair hCE (by omega) (by omega) hcycle
      hclique hx hRX hXk (by omega) hexpand
      (fun y hy hne d hd hdb => hforbid x hx y hy hne d hd (by omega)) (hpair x hx)
  have hp := radius_two_packing_bound hbound hRX htriple hforbid
  omega
theorem terminal_mixed_packing_contradiction (hbound : IndependenceBound G 19)
    {X R A : Finset V} (hRX : R ⊆ X) (hAR : A ⊆ R)
    (hR : R.card = 9) (hA : A.card = 4)
    (hweight : ∀ x ∈ R, HasIndependent
      (G.induce (outsideBallFinset G X x (if x ∈ A then 2 else 1) : Set V))
      (if x ∈ A then 3 else 2))
    (hforbid : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d →
      d ≤ (if x ∈ A then 3 else 2) + (if y ∈ A then 3 else 2) →
      ¬ OutsidePath G (X : Set V) x y d) : False := by
  have hp := packing_test hbound X (fun i : R => i.val)
    (fun i => if i.val ∈ A then 3 else 2) (fun i => if i.val ∈ A then 3 else 2)
    Subtype.val_injective (fun i => hRX i.property)
    (fun i => by
      have hi := hweight i i.property
      have hregion : packingRegion G X (i : V) (if (i : V) ∈ A then 3 else 2) =
          outsideBallFinset G X (i : V) (if (i : V) ∈ A then 2 else 1) := by
        split_ifs <;> rfl
      change HasIndependent
        (G.induce (packingRegion G X (i : V) (if (i : V) ∈ A then 3 else 2) : Set V))
        (if (i : V) ∈ A then 3 else 2)
      rw [hregion]
      exact hi)
    (fun i j hij => by
      have hf := hforbid i i.property j j.property (fun h => hij (Subtype.ext h))
      by_cases hia : i.val ∈ A <;> by_cases hja : j.val ∈ A <;>
        simpa only [hia, hja, ↓reduceIte, PackingCompatible, OfNat.ofNat_ne_zero,
          false_and] using hf)
  have hcount : (∑ i : R, if i.val ∈ A then 3 else 2) = 22 := by
    have hpoint : ∀ i : R, (if i.val ∈ A then 3 else 2) =
        2 + (if i.val ∈ A then 1 else 0) := by intro i; split_ifs <;> rfl
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    have hfilter : (Finset.univ.filter (fun i : R => i.val ∈ A)).card = A.card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi j hj he
        exact Subtype.ext he
      · intro a ha
        exact ⟨⟨a, hAR ha⟩, by simp [ha], rfl⟩
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe,
      hR, Finset.sum_boole, hfilter, hA]
    decide
  rw [hcount] at hp
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
private theorem original_chain_in_completion {l : List V} (hl : l ∈ S.chains) :
    l ∈ S.toRaw.completeClique.chains := by
  exact List.mem_append_left _ hl
theorem selectedChains_outside {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w)
    (hmin : ∀ a ∈ w, 2 ≤ a) : ∀ x ∈ selectedChains Q S.chains, x ∉ Q := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨wl, hwl, hsub⟩ := h.profile_of_mem hl
  exact selectedChain_outside hwl (fun a ha => hmin a (hsub a ha)) (S.no_clique_steps l hl) x hx
theorem selectedChains_orientation {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w)
    (hmin : ∀ a ∈ w, 2 ≤ a) {x : V} (hx : x ∈ selectedChains Q S.chains) :
    ∃ p : List V → Bool, x ∈ (S.toRaw.completeClique.orientChains p).representatives := by
  obtain ⟨a, ha, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨wl, hwl, hsub⟩ := h.profile_of_mem hl
  obtain ⟨b, hb⟩ := selectedChain_orientation hwl (fun a ha => hmin a (hsub a ha)) hx
  exact ⟨fun _ => b, S.toRaw.completeClique.representative_of_oriented_chain _
    (original_chain_in_completion hl) hb⟩
theorem IsOptimal.selectedChains_forbidden {k : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) {w : List ℕ}
    (h : SystemAssignedAmounts Q S.chains w) (hmin : ∀ a ∈ w, 2 ≤ a)
    {x y : V} (hx : x ∈ selectedChains Q S.chains) (hy : y ∈ selectedChains Q S.chains)
    (hne : x ≠ y) {d : ℕ} (hd : 1 ≤ d) (hd' : d ≤ 6) :
    ¬ OutsidePath G (S.ground : Set V) x y d := by
  intro hout
  have hout' : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d := by
    simpa only [ground, Finset.coe_union] using hout
  obtain ⟨a, ha, hxl⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hb, hym⟩ := List.mem_flatten.mp hy
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
  obtain ⟨wl, hwl, hsubl⟩ := h.profile_of_mem hl
  obtain ⟨wm, hwm, hsubm⟩ := h.profile_of_mem hm
  have hminl : ∀ a ∈ wl, 2 ≤ a := fun a ha => hmin a (hsubl a ha)
  have hminm : ∀ a ∈ wm, 2 ≤ a := fun a ha => hmin a (hsubm a ha)
  have hcontra (p : List V → Bool)
      (hx' : x ∈ (S.toRaw.completeClique.orientChains p).representatives)
      (hy' : y ∈ (S.toRaw.completeClique.orientChains p).representatives) : False := by
    have hQx := (hopt.terminal_completed_classification ht hQk hkQ hQ hcycle
      hd hd' p hx' hy' hne hout').1
    exact selectedChains_outside h hmin x hx hQx
  by_cases hlm : l = m
  · subst m
    by_cases hlen : l.length = 4
    · obtain ⟨q, u, v, r, rfl, hq, hr, hu, hv⟩ :=
        hwl.amount_two_shape (amount_profile_eq_two_of_length_four hwl hlen hminl)
      have hx' : x = u ∨ x = v := by simpa [selectedChain] using hxl
      have hy' : y = u ∨ y = v := by simpa [selectedChain] using hym
      obtain ⟨P, R, hsys⟩ := List.append_of_mem hl
      have hf := hopt.forbidden_amount_two_detour ht hQk hkQ hQ hcycle hd hd'
        (A := []) (B := []) (by simpa using hsys) hq hr hu hv
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact hne rfl
      · exact hf hout'
      · exact hf hout'.reverse
      · exact hne rfl
    · have hx' : x ∈ chainRepresentatives Q l := by
        apply List.mem_of_mem_tail
        simpa [selectedChain, hlen, interiorRepresentatives] using hxl
      have hy' : y ∈ chainRepresentatives Q l := by
        apply List.mem_of_mem_tail
        simpa [selectedChain, hlen, interiorRepresentatives] using hym
      apply hcontra (fun _ => false)
      · exact S.toRaw.completeClique.representatives_orientChains_unchanged
          (original_chain_in_completion hl) rfl hx'
      · exact S.toRaw.completeClique.representatives_orientChains_unchanged
          (original_chain_in_completion hl) rfl hy'
  · obtain ⟨bx, hbx⟩ := selectedChain_orientation hwl hminl hxl
    obtain ⟨by_, hby⟩ := selectedChain_orientation hwm hminm hym
    obtain ⟨p, hp, hp'⟩ := S.toRaw.completeClique.joint_orientation
      (original_chain_in_completion hl) (original_chain_in_completion hm) hlm bx by_ hbx hby
    exact hcontra p hp hp'
variable [Fintype V]
theorem IsOptimal.terminal_spanning_interior_contradiction (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G k) (hc : 2 ≤ S.chains.length)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    {w : List ℕ} (h : SystemAssignedAmounts Q S.chains w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hincident : S.incident = Q.card) : False := by
  let R := (selectedChains Q S.chains).toFinset
  have hlarge : Q.card - 1 ≤ R.card := by
    rw [List.toFinset_card_of_nodup S.selectedChains_nodup]
    exact S.selectedChains_large h hmin hincident (by have hb := hopt.budget; omega)
  have hRX : R ⊆ S.ground := by
    intro x hx
    exact Finset.mem_union_right _ (S.selectedChains_mem_vertices (List.mem_toFinset.mp hx))
  have hpair : ∀ x ∈ R,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2 := by
    intro x hx
    obtain ⟨p, hp⟩ := selectedChains_orientation h hmin (List.mem_toFinset.mp hx)
    exact (hopt.terminal_oriented_first_ball (by omega) hQk hQ hcycle hclique hc
      (fun v => by simpa using hexpand {v} (by simp) (by simp)) p hp).2
  apply terminal_uniform_packing_contradiction hCE ht (by
    have hlen := h.length_eq
    have hsum := h.sum_eq
    have hb := twice_length_le_sum hmin
    have hc' := S.incident_le_twice_assignedCount
    rw [hincident] at hc'
    rw [← S.assignedCount_eq_raw] at hlen
    have hsum' : w.sum = S.amount := by exact hsum.trans S.toRaw.amount_eq_outside_count.symm
    have hbudget := hopt.budget
    omega) hkQ hcycle hclique hbound hRX (hopt.ground_card_le hQk)
    (by omega) hexpand hpair
  intro x hx y hy hne d hd hd'
  exact hopt.selectedChains_forbidden ht hQk hkQ hQ hcycle h hmin
    (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hne hd hd'
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
namespace SystemAssignedAmounts
theorem minimum_of_subset {C D : List (List V)} {W : List ℕ} {d : ℕ}
    (h : SystemAssignedAmounts Q D W) (hmin : ∀ a ∈ W, d ≤ a)
    (hsub : ∀ l ∈ C, l ∈ D) :
    ∃ w, SystemAssignedAmounts Q C w ∧ ∀ a ∈ w, d ≤ a := by
  induction C with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons l C ih =>
    obtain ⟨a, ha, hamin⟩ := h.profile_of_mem (hsub l (by simp))
    obtain ⟨w, hw, hwmin⟩ := ih (fun l hl => hsub l (by simp [hl]))
    refine ⟨a ++ w, .cons ha hw, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmin x (hamin x hx)
    · exact hwmin x hx
end SystemAssignedAmounts
theorem chainRepresentatives_clique_head {l : List V} {x : V}
    (hsteps : l.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)))
    (hx : x ∈ chainRepresentatives Q l) (hxQ : x ∈ Q) : ∃ B, l = x :: B := by
  cases l with
  | nil => simp [chainRepresentatives] at hx
  | cons a B =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨B, rfl⟩
    · exact False.elim (representativesFrom_outside hsteps x hx hxQ)
namespace ExpandedPathSystem
variable {S : ExpandedPathSystem G Q}
theorem complete_tail_nil_iff (S : ExpandedPathSystem G Q) {x : V} {B : List V}
    (hl : x :: B ∈ S.toRaw.completeClique.chains) : B = [] ↔ x ∉ S.vertices := by
  apply S.oriented_complete_tail_nil_iff (fun _ => false)
  simpa [RawPathSystem.orientChains, RawPathSystem.orientedChain] using hl
theorem IsOptimal.terminal_completed_profile_minimum {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {x y : V} (hx : x ∈ S.toRaw.completeClique.representatives)
    (hy : y ∈ S.toRaw.completeClique.representatives) (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hne : x ≠ y) (hout : OutsidePath G ((Q : Set V) ∪ (S.vertices : Set V)) x y d) :
    ∃ w, SystemAssignedAmounts Q S.chains w ∧ ∀ a ∈ w, d ≤ a := by
  let U := S.toRaw.completeClique
  obtain ⟨a, ha, hxa⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  obtain ⟨B, rfl⟩ := chainRepresentatives_clique_head (U.no_clique_steps l hl) hxa hxQ
  obtain ⟨b, hb, hyb⟩ := List.mem_flatten.mp hy
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
  obtain ⟨D, rfl⟩ := chainRepresentatives_clique_head (U.no_clique_steps m hm) hyb hyQ
  have hBD : x :: B ≠ y :: D := fun he => hne (List.cons.inj he).1
  obtain ⟨R, hp⟩ := U.bring_two_front hl hm hBD
  let U' := U.reorder ((x :: B) :: (y :: D) :: R) hp
  have hvertices : ∀ v ∈ U'.vertices, v ∈ Q ∨ v ∈ S.vertices := by
    intro v hv
    rw [RawPathSystem.reorder_vertices, RawPathSystem.completeClique_vertices] at hv
    exact (Finset.mem_union.mp hv).symm
  obtain ⟨_, ⟨w, hw, hmin⟩, _⟩ := hopt.terminal_starting_classification ht hQk hkQ hQ hcycle hd hd'
    U' (by simp [U', U]) (by simp [U', U]) (by simp [U', U]) hvertices
    (P := []) (M := []) (R := R) rfl (S.complete_tail_nil_iff hl) (S.complete_tail_nil_iff hm) hne hout
  apply hw.minimum_of_subset hmin
  intro l hl
  change l ∈ (x :: B) :: (y :: D) :: R
  apply hp.mem_iff.mpr
  exact List.mem_append_left _ hl
end ExpandedPathSystem
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}
noncomputable def incidentRepresentatives (S : ExpandedPathSystem G Q) : Finset V :=
  S.toRaw.representatives.toFinset
theorem incidentRepresentatives_card (S : ExpandedPathSystem G Q) :
    S.incidentRepresentatives.card = S.incident := by
  rw [incidentRepresentatives, List.toFinset_card_of_nodup S.toRaw.representatives_nodup,
    RawPathSystem.representatives_length, S.incident_eq_chainCliqueCount]
  rfl
theorem incidentRepresentatives_subset_vertices (S : ExpandedPathSystem G Q) :
    S.incidentRepresentatives ⊆ S.vertices := by
  intro x hx
  exact List.mem_toFinset.mpr (S.toRaw.representatives_sublist.subset (List.mem_toFinset.mp hx))
theorem complete_representatives_eq (S : ExpandedPathSystem G Q) :
    S.toRaw.completeClique.representatives = S.toRaw.representatives ++ (Q \ S.vertices).toList := by
  simp [RawPathSystem.representatives, RawPathSystem.completeClique, chainRepresentatives,
    representativesFrom, List.map_append, List.flatten_append, List.map_map, Function.comp_def]
  change ((Q \ S.vertices).toList.map (fun v => [v])).flatten = _
  generalize (Q \ S.vertices).toList = L
  induction L with
  | nil => rfl
  | cons x L ih => simpa using congrArg (List.cons x) ih
theorem representativeFinset_eq_union (S : ExpandedPathSystem G Q) :
    S.representativeFinset = S.incidentRepresentatives ∪ (Q \ S.vertices) := by
  rw [representativeFinset, S.complete_representatives_eq, List.toFinset_append]
  simp only [Finset.toList_toFinset, incidentRepresentatives]
theorem incidentRepresentatives_subset_representatives (S : ExpandedPathSystem G Q) :
    S.incidentRepresentatives ⊆ S.representativeFinset := by
  rw [S.representativeFinset_eq_union]
  exact Finset.subset_union_left
theorem missing_subset_representatives (S : ExpandedPathSystem G Q) :
    Q \ S.vertices ⊆ S.representativeFinset := by
  rw [S.representativeFinset_eq_union]
  exact Finset.subset_union_right
theorem missing_card_add_incident (S : ExpandedPathSystem G Q) :
    (Q \ S.vertices).card + S.incident = Q.card := by
  have hh := Finset.card_sdiff_add_card_inter Q S.vertices
  simpa only [incident, Finset.inter_comm] using hh
theorem IsOptimal.terminal_finset_classification {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {x y : V} (hx : x ∈ S.representativeFinset) (hy : y ∈ S.representativeFinset)
    (hne : x ≠ y) (hout : OutsidePath G (S.ground : Set V) x y d) :
    x ∈ Q ∧ y ∈ Q ∧ S.amount = k - Q.card ∧ d * S.assignedCount ≤ S.amount ∧
      TerminalAlternative S k d x y := by
  apply hopt.terminal_completed_classification ht hQk hkQ hQ hcycle hd hd' (fun _ => false)
    (x := x) (y := y)
  · simpa [RawPathSystem.representatives, RawPathSystem.orientChains,
      RawPathSystem.orientedChain] using List.mem_toFinset.mp hx
  · simpa [RawPathSystem.representatives, RawPathSystem.orientChains,
      RawPathSystem.orientedChain] using List.mem_toFinset.mp hy
  · exact hne
  · simpa only [ground, Finset.coe_union] using hout
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
private theorem terminal_five_packing_contradiction (hCE : CEAlphaTwo)
    (ht9 : Q.card = 9) (hcycle : ¬ HasCycle G 20) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G 19) (hXk : S.ground.card ≤ 19)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      19 * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : ∀ x ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2)
    (hclass : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 → OutsidePath G (S.ground : Set V) x y d →
      TerminalAlternative S 19 d x y)
    {x₀ y₀ : V} (hfixed : TerminalAlternative S 19 5 x₀ y₀) (hv : S.incident = 4) : False := by
  classical
  have hinc := S.incidentRepresentatives_subset_representatives
  have hincV := S.incidentRepresentatives_subset_vertices
  have hcard := S.incidentRepresentatives_card
  have hRcard : S.representativeFinset.card = 9 := by
    rw [S.representativeFinset_card, ht9]
  have hAcard : S.incidentRepresentatives.card = 4 := by omega
  have htriple : ∀ x ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 2 : Set V)) 3 := by
    intro x hx
    exact outsideBall_two_triple_of_first_pair (k := 19) (t := Q.card)
      (X := S.ground) (x := x) hCE (by omega) (by omega) (by omega)
      hcycle hclique hXk hexpand (hpair x hx)
  have hweight : ∀ x ∈ S.representativeFinset, HasIndependent
      (G.induce (outsideBallFinset G S.ground x
        (if x ∈ S.incidentRepresentatives then 2 else 1) : Set V))
      (if x ∈ S.incidentRepresentatives then 3 else 2) := by
    intro x hx
    by_cases hxa : x ∈ S.incidentRepresentatives
    · convert htriple x hx using 1
      · rw [if_pos hxa]
      · rw [if_pos hxa]
      · exact if_pos hxa
    · convert hpair x hx using 1
      · rw [if_neg hxa]
      · rw [if_neg hxa]
      · exact if_neg hxa
  apply terminal_mixed_packing_contradiction hbound S.representativeFinset_subset_ground
    hinc hRcard hAcard hweight
  intro x hx y hy hxy d hd hd' hout
  have hdb : d ≤ 6 := by split_ifs at hd' <;> omega
  have hc := hclass x hx y hy hxy d hd hdb hout
  have hd5 : d = 5 := (hfixed.parameter_unique (by omega) hc).symm
  have hmiss : x ∉ S.vertices ∧ y ∉ S.vertices := by
    rcases hc with ⟨hd2, _⟩ | ⟨hd3, _⟩ | ⟨_, _, _, _, _, _, hx', hy'⟩
    · omega
    · omega
    · exact ⟨hx', hy'⟩
  have hxnot : x ∉ S.incidentRepresentatives := fun hx' => hmiss.1 (hincV hx')
  have hynot : y ∉ S.incidentRepresentatives := fun hy' => hmiss.2 (hincV hy')
  simp only [hxnot, hynot, ↓reduceIte] at hd'
  omega
theorem terminal_packing_cases_contradiction (hCE : CEAlphaTwo) {k d₀ : ℕ}
    (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k) (hkQ : k ≤ 2 * Q.card + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G k) (hXk : S.ground.card ≤ k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hpair : ∀ x ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground x 1 : Set V)) 2)
    (hclass : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 → OutsidePath G (S.ground : Set V) x y d →
      TerminalAlternative S k d x y)
    (hL : S.amount = k - Q.card) (hde : d₀ * S.assignedCount ≤ S.amount)
    {x₀ y₀ : V} (halt : TerminalAlternative S k d₀ x₀ y₀)
    (hfull : S.incident = Q.card → False) : False := by
  classical
  have hinc := S.incidentRepresentatives_subset_representatives
  have hincV := S.incidentRepresentatives_subset_vertices
  have hincX : S.incidentRepresentatives ⊆ S.ground :=
    fun x hx => S.representativeFinset_subset_ground (hinc hx)
  have hcard := S.incidentRepresentatives_card
  have hmissing := S.missing_card_add_incident
  have hve := S.incident_le_twice_assignedCount
  have hfixed := halt
  rcases halt with ⟨rfl, hv, _⟩ | ⟨rfl, ht', he, hv, _, _, _⟩ |
    ⟨rfl, ht9, hk19, he, hv, _, _, _⟩
  · have hne : (Q \ S.vertices).Nonempty := by
      apply Finset.card_pos.mp
      have hile := S.incident_le
      have hn : S.incident ≠ Q.card := hfull
      omega
    obtain ⟨z, hz⟩ := hne
    have hzV := (Finset.mem_sdiff.mp hz).2
    apply terminal_uniform_packing_contradiction (k := k) (t := Q.card) hCE ht (by omega) hkQ hcycle hclique
      hbound hincX hXk (by omega) hexpand (fun x hx => hpair x (hinc hx))
    intro x hx y hy hxy d hd hd' hout
    have hc := hclass x (hinc hx) y (hinc hy) hxy d hd hd' hout
    have hd2 : d = 2 := (hfixed.parameter_unique ht hc).symm
    rcases hc with ⟨_, _, hcover⟩ | ⟨hd3, _⟩ | ⟨hd5, _⟩
    · have hzxy := hcover hz
      rcases Finset.mem_insert.mp hzxy with rfl | hzxy
      · exact hzV (hincV hx)
      · have hz_eq_y : z = y := Finset.mem_singleton.mp hzxy
        subst z
        exact hzV (hincV hy)
    · omega
    · omega
  · have hzexists : (Q \ S.vertices).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hz⟩ := hzexists
    have hzV := (Finset.mem_sdiff.mp hz).2
    have hzR : z ∈ S.representativeFinset := S.missing_subset_representatives hz
    have hznot : z ∉ S.incidentRepresentatives := fun hz' => hzV (hincV hz')
    let R := insert z S.incidentRepresentatives
    have hRrep : R ⊆ S.representativeFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hzR
      · exact hinc hx
    have hRcard : R.card = Q.card - 2 := by
      rw [Finset.card_insert_of_notMem hznot, hcard]
      omega
    apply terminal_uniform_packing_contradiction (k := k) (t := Q.card) hCE ht (by rcases ht' with ht' | ht' <;> omega)
      hkQ hcycle hclique hbound
      (fun x hx => S.representativeFinset_subset_ground (hRrep hx)) hXk (by omega)
      hexpand (fun x hx => hpair x (hRrep hx))
    intro x hx y hy hxy d hd hd' hout
    have hc := hclass x (hRrep hx) y (hRrep hy) hxy d hd hd' hout
    have hd3 : d = 3 := (hfixed.parameter_unique ht hc).symm
    have hmiss : x ∉ S.vertices ∧ y ∉ S.vertices := by
      rcases hc with ⟨hd2, _⟩ | ⟨_, _, _, _, _, hx', hy'⟩ | ⟨hd5, _⟩
      · omega
      · exact ⟨hx', hy'⟩
      · omega
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxy rfl
      · exact hmiss.2 (hincV hy)
    · exact hmiss.1 (hincV hx)
  · subst k
    exact terminal_five_packing_contradiction hCE ht9 hcycle hclique hbound hXk
      hexpand hpair hclass hfixed hv
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {X R : Finset V} {k : ℕ}
theorem exists_short_path_of_two_noncliques (hCE : CEAlphaTwo) (hk : 5 ≤ k)
    (hbound : IndependenceBound G k) (hRX : R ⊆ X) (hXk : X.card ≤ k)
    (hRk : R.card < k) (hkR : k ≤ 2 * R.card + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ R.card)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hspecial : ∃ a ∈ R, ∃ b ∈ R, a ≠ b ∧
      ¬ G.IsClique (outsideBallFinset G X a 1 : Set V) ∧
      ¬ G.IsClique (outsideBallFinset G X b 1 : Set V)) :
    ∃ x ∈ R, ∃ y ∈ R, x ≠ y ∧ ∃ d, 1 ≤ d ∧ d ≤ 6 ∧
      OutsidePath G (X : Set V) x y d := by
  obtain ⟨a, ha, b, hb, hab, hna, hnb⟩ := hspecial
  by_contra hn
  push Not at hn
  have hf : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G (X : Set V) x y d := by
    intro x hx y hy hne d hd hdb
    exact hn x hx y hy hne d hd hdb
  have hsingle : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa using hexpand {v} (by simp) (by simp)
  let α : R := ⟨a, ha⟩
  let β : R := ⟨b, hb⟩
  have hαβ : α ≠ β := fun h => hab (congrArg Subtype.val h)
  let weight : R → ℕ := fun i => 2 + (if i = α then 1 else 0) + (if i = β then 1 else 0)
  have hweight : ∀ i : R,
      HasIndependent (G.induce (packingRegion G X i 3 : Set V)) (weight i) := by
    intro i
    by_cases hia : i = α
    · subst i
      have h := representative_ball_two_triple hCE hk ha hRX hXk hRk hcycle hclique hexpand
        (fun y hy hne d hd hdb => hf a ha y hy hne d hd (by omega)) hna
      simpa [packingRegion, weight, α, hαβ] using h
    · by_cases hib : i = β
      · subst i
        have h := representative_ball_two_triple hCE hk hb hRX hXk hRk hcycle hclique hexpand
          (fun y hy hne d hd hdb => hf b hb y hy hne d hd (by omega)) hnb
        simpa [packingRegion, weight, β, hαβ.symm] using h
      · have h := representative_ball_two_pair i.property hRX hXk hclique hsingle
          (fun y hy hne d hd hdb => hf i i.property y hy hne d hd (by omega))
        simpa [packingRegion, weight, hia, hib] using h
  have hp := packing_test hbound X (fun i : R => i.val) (fun _ => 3) weight
    Subtype.val_injective (fun i => hRX i.property) hweight
    (fun i j hij => by
      simp only [PackingCompatible, OfNat.ofNat_ne_zero, false_and, ↓reduceIte]
      intro d hd hdb
      exact hf i i.property j j.property (fun h => hij (Subtype.ext h)) d hd hdb)
  have hsum : ∑ i : R, weight i = 2 * R.card + 2 := by
    simp [weight, Finset.sum_add_distrib, mul_comm]
  rw [hsum] at hp
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.short_representative_path (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 5 ≤ k) (ht : 9 ≤ Q.card)
    (hQk : Q.card ≤ k) (hkQ : k ≤ 2 * Q.card + 1)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ Q.card) (hbound : IndependenceBound G k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    ∃ x ∈ S.representativeFinset, ∃ y ∈ S.representativeFinset,
      x ≠ y ∧ ∃ d, 2 ≤ d ∧ d ≤ 6 ∧ OutsidePath G (S.ground : Set V) x y d := by
  have hRcard := S.representativeFinset_card
  have hRX := S.representativeFinset_subset_ground
  have hXk := hopt.ground_card_le hQk
  have hclique' : G.cliqueNum ≤ S.representativeFinset.card := by omega
  have hsingle : ∀ v, k + 1 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa using hexpand {v} (by simp) (by simp)
  have hf : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ¬ OutsidePath G (S.ground : Set V) x y 1 := by
    intro x hx y hy hne
    exact hopt.representativeFinset_one_exclusion (by omega) hQk hQ hcycle hx hy hne
  have hshort : ∃ x ∈ S.representativeFinset, ∃ y ∈ S.representativeFinset,
      x ≠ y ∧ ∃ d, 1 ≤ d ∧ d ≤ 6 ∧ OutsidePath G (S.ground : Set V) x y d := by
    by_cases hlarge : k < 2 * S.representativeFinset.card
    · exact exists_short_path_of_twice_card_gt hbound hRX hXk hclique' hsingle hlarge
    · have hRk : S.representativeFinset.card < k := by omega
      have hspecial : ∃ a ∈ S.representativeFinset, ∃ b ∈ S.representativeFinset,
          a ≠ b ∧ ¬ G.IsClique (outsideBallFinset G S.ground a 1 : Set V) ∧
          ¬ G.IsClique (outsideBallFinset G S.ground b 1 : Set V) := by
        by_cases he : 2 ≤ S.assignedCount
        · exact hopt.two_interior_nonclique_balls (by omega) hQk hQ hcycle hclique hsingle he
        · by_cases he0 : S.assignedCount = 0
          · have hL := S.amount_eq_zero_of_assignedCount_eq_zero he0
            have hXcard : S.ground.card < k := by rw [ground_card, hL]; omega
            have hnonclique : ∀ x ∈ S.representativeFinset,
                ¬ G.IsClique (outsideBallFinset G S.ground x 1 : Set V) := by
              intro x hx hC
              have hd := representative_ball_one hx hRX hXk hsingle (hf x hx)
              have hc := hC.card_le_cliqueNum.trans hclique'
              omega
            have htwo : 1 < S.representativeFinset.card := by omega
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
            exact ⟨a, ha, b, hb, hab, hnonclique a ha, hnonclique b hb⟩
          · have he1 : S.assignedCount = 1 := by omega
            exact hopt.two_unused_nonclique_balls (by omega) hQk hQ hcycle hclique hsingle he1 (by omega)
      exact exists_short_path_of_two_noncliques hCE hk hbound hRX hXk hRk (by omega)
        hcycle hclique' hexpand hspecial
  obtain ⟨x, hx, y, hy, hxy, d, hd, hdb, hp⟩ := hshort
  have hdne : d ≠ 1 := by intro he; subst d; exact hf x hx y hy hxy hp
  exact ⟨x, hx, y, hy, hxy, d, by omega, hdb, hp⟩
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction.ExpandedPathSystem
open scoped Classical
variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}
theorem IsOptimal.terminal_contradiction (hCE : CEAlphaTwo) {k : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ Q.card)
    (hbound : IndependenceBound G k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  obtain ⟨x, hx, y, hy, hxy, d, hd, hd', hout⟩ :=
    hopt.short_representative_path hCE (by omega) ht hQk hkQ hQ hcycle hclique hbound hexpand
  obtain ⟨hxQ, hyQ, hL, hde, halt⟩ := hopt.terminal_finset_classification
    ht hQk hkQ hQ hcycle (by omega) hd' hx hy hxy hout
  obtain ⟨w, hw, hwmin⟩ := hopt.terminal_completed_profile_minimum ht hQk hkQ hQ hcycle
    (by omega) hd' (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxQ hyQ hxy
    (by simpa only [ground, Finset.coe_union] using hout)
  have hmin : ∀ a ∈ w, 2 ≤ a := fun a ha => (by have hh := hwmin a ha; omega)
  have hc : 2 ≤ S.chains.length := by
    have hcount := S.assignedCount_add_chains_length
    rcases halt with ⟨hd2, hv, _⟩ | ⟨hd3, ht', he, hv, _⟩ |
      ⟨hd5, ht9, _, he, hv, _⟩
    · subst d
      exact S.two_chains_of_terminal_two ht hkQ hL hde hv
    · rcases ht' with ht' | ht' <;> omega
    · omega
  have hfirst : ∀ z ∈ S.representativeFinset,
      HasIndependent (G.induce (outsideBallFinset G S.ground z 1 : Set V)) 2 := by
    intro z hz
    exact (hopt.terminal_first_ball (by omega) hQk hQ hcycle hclique hc
      (fun v => by simpa using hexpand {v} (by simp) (by simp)) hz).2
  have hclass : ∀ x ∈ S.representativeFinset, ∀ y ∈ S.representativeFinset,
      x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 → OutsidePath G (S.ground : Set V) x y d →
      TerminalAlternative S k d x y := by
    intro x hx y hy hne d hd hd' hp
    exact (hopt.terminal_finset_classification ht hQk hkQ hQ hcycle hd hd' hx hy hne hp).2.2.2.2
  have hfull : S.incident = Q.card → False := by
    intro hi
    exact hopt.terminal_spanning_interior_contradiction hCE ht hQk hkQ hQ hcycle
      hclique hbound hc hexpand hw hmin hi
  exact terminal_packing_cases_contradiction hCE ht hQk hkQ hcycle hclique hbound
    (hopt.ground_card_le hQk) hexpand hfirst hclass hL hde halt hfull
end CycleClique.Construction.ExpandedPathSystem
end OAI


namespace OAI
namespace CycleClique.Construction
open scoped Classical
theorem finite_range_clique_bounds (hCE : CEAlphaTwo)
    {V : Type} [Fintype V] {G : SimpleGraph V} {k a : ℕ}
    (hk : 5 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    k ≤ 17 ∧ 3 ≤ G.cliqueNum ∧ G.cliqueNum ≤ min k 8 ∧ k / 2 ≤ G.cliqueNum := by
  classical
  obtain ⟨hlo, hhi⟩ := large_clique_bounds (by omega) ha hak hcard hI hcycle hexpand
  have hsmall : G.cliqueNum ≤ 8 := by
    by_contra hn
    obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
    have hQcard := hQ.card_eq
    obtain ⟨S, hopt⟩ := ExpandedPathSystem.exists_optimal G Q k
    exact hopt.terminal_contradiction hCE (by omega) (by omega) (by omega)
      hQ.isClique hcycle (by omega) (fun I hi => (hI I hi).trans hak) hexpand
  omega
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
def blockGraph (a k : ℕ) : SimpleGraph (Fin a × Fin k) where
  Adj x y := x ≠ y ∧ x.1 = y.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
@[simp] theorem blockGraph_adj {a k : ℕ} {x y : Fin a × Fin k} :
    (blockGraph a k).Adj x y ↔ x ≠ y ∧ x.1 = y.1 := Iff.rfl
private theorem cycleNext_castSucc {r : ℕ} (i : Fin r) :
    cycleNext i.castSucc = i.succ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)
theorem blockGraph_cycle_bound {a k m : ℕ} (hm : 0 < m)
    (h : HasCycle (blockGraph a k) m) : m ≤ k := by
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hfirst : ∀ i : Fin (r + 1), (f i).1 = (f 0).1 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hi := (he i.castSucc).2
      rw [cycleNext_castSucc] at hi
      exact hi.symm.trans ih
  have hinj : Function.Injective (fun i => (f i).2) := by
    intro i j hij
    apply hf
    exact Prod.ext ((hfirst i).trans (hfirst j).symm) hij
  simpa using Fintype.card_le_of_injective (fun i => (f i).2) hinj
theorem blockGraph_independent_bound {a k n : ℕ}
    (h : HasIndependent (blockGraph a k) n) : n ≤ a := by
  obtain ⟨f, hf, he⟩ := h
  have hinj : Function.Injective (fun i => (f i).1) := by
    intro i j hij
    by_contra hne
    exact he i j ⟨fun h => hne (hf h), hij⟩
  simpa using Fintype.card_le_of_injective (fun i => (f i).1) hinj
theorem blockGraph_not_ramsey {a k m n : ℕ} (hkm : k < m) (han : a < n) :
    ¬ RamseyProperty m n (k * a) := by
  let e : Fin (k * a) ≃ Fin a × Fin k :=
    (finCongr (Nat.mul_comm k a)).trans finProdFinEquiv.symm
  let G : SimpleGraph (Fin (k * a)) := (blockGraph a k).comap e
  intro h
  rcases h G with hc | hi
  · have hc' : HasCycle (blockGraph a k) m :=
      hc.map e e.injective (fun h => h)
    have := blockGraph_cycle_bound (by omega) hc'
    omega
  · have hi' : HasIndependent (blockGraph a k) n :=
      hi.map e e.injective (fun h => h)
    have := blockGraph_independent_bound hi'
    omega
theorem cycle_clique_lower_bound {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ¬ RamseyProperty m n ((m - 1) * (n - 1)) := by
  exact blockGraph_not_ramsey (by omega) (by omega)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem ramseyProperty_of_expanded_exclusion {k a : ℕ}
    (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hexclude : ∀ b, 2 ≤ b → b ≤ k →
      ∀ G : SimpleGraph (Fin (k * b + 1)),
        ¬ HasCycle G (k + 1) → IndependenceBound G b →
        (∀ I : Finset (Fin (k * b + 1)), G.IsIndepSet (I : Set _) → I.Nonempty →
          k * I.card + 1 ≤ (closedNeighborhood G I).card) → False) :
    RamseyProperty (k + 1) (a + 1) (k * a + 1) := by
  classical
  by_contra hfail
  obtain ⟨b, G, hb, hbk, hcycle, hI, hexpand⟩ :=
    exists_minimal_counterexample hk ha hak hfail
  exact hexclude b hb hbk G hcycle hI hexpand
theorem isRamseyNumber_of_expanded_exclusion {m n : ℕ}
    (hm : 4 ≤ m) (hn : 3 ≤ n) (hnm : n ≤ m)
    (hexclude : ∀ b, 2 ≤ b → b ≤ m - 1 →
      ∀ G : SimpleGraph (Fin ((m - 1) * b + 1)),
        ¬ HasCycle G m → IndependenceBound G b →
        (∀ I : Finset (Fin ((m - 1) * b + 1)), G.IsIndepSet (I : Set _) → I.Nonempty →
          (m - 1) * I.card + 1 ≤ (closedNeighborhood G I).card) → False) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) := by
  have hm' : m - 1 + 1 = m := by omega
  have hn' : n - 1 + 1 = n := by omega
  apply isRamseyNumber_of_upper_lower
  · have hupper := ramseyProperty_of_expanded_exclusion (k := m - 1) (a := n - 1)
      (by omega) (by omega) (by omega) (by simpa only [hm'] using hexclude)
    simpa only [hm', hn'] using hupper
  · exact blockGraph_not_ramsey (by omega) (by omega)
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem ce_external_ear {V : Type*} {H : SimpleGraph V}
    (hconn : H.Connected) (hdel : ∀ a : V, (H.induce {v | v ≠ a}).Connected)
    (S : Finset V) (hS : 2 ≤ S.card) (x : V) (hx : x ∉ S) :
    ∃ l, 2 ≤ l ∧ ∃ g : Fin (l + 1) → V, IsIndexedPath H g ∧
      g 0 ∈ S ∧ g (Fin.last l) ∈ S ∧
      ∀ i : Fin (l + 1), 0 < i.val → i.val < l → g i ∉ S := by
  classical
  let X := H.induce {v | v ∉ S}
  let x' : {v | v ∉ S} := ⟨x, hx⟩
  let W : Set V := {v | ∃ hv : v ∉ S, X.Reachable x' ⟨v, hv⟩}
  have hxW : x ∈ W := ⟨hx, .rfl⟩
  have hWout : ∀ v ∈ W, v ∉ S := fun _ ⟨hv, _⟩ => hv
  have hboundary : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → v ∈ S := by
    intro u hu v hv huv
    by_contra hvs
    obtain ⟨huS, huR⟩ := hu
    apply hv
    refine ⟨hvs, huR.trans ?_⟩
    exact (show X.Adj ⟨u, huS⟩ ⟨v, hvs⟩ from huv).reachable
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hyW : y ∉ W := fun h => hWout y h hy
  obtain ⟨u, hu, a, haW, hua⟩ := connected_edge_leaving hconn hxW hyW
  have ha : a ∈ S := hboundary u hu a haW hua
  have hxne : x ≠ a := fun h => hx (h ▸ ha)
  have hbex : ∃ b ∈ S, b ≠ a := by
    by_contra! hb
    have hsmall : S.card ≤ 1 := Finset.card_le_one.mpr (fun v hv w hw =>
      (hb v hv).trans (hb w hw).symm)
    omega
  obtain ⟨b, hb, hba⟩ := hbex
  let D := H.induce {v | v ≠ a}
  let W' : Set {v | v ≠ a} := {v | v.val ∈ W}
  have hxb : (⟨x, hxne⟩ : {v | v ≠ a}) ∈ W' := hxW
  have hbb : (⟨b, hba⟩ : {v | v ≠ a}) ∉ W' := fun h => hWout b h hb
  obtain ⟨u', hu', b', hb'W, hu'b'⟩ :=
    connected_edge_leaving (hdel a) hxb hbb
  have hb' : b'.val ∈ S := hboundary u'.val hu' b'.val hb'W hu'b'
  obtain ⟨huS, huR⟩ := hu
  obtain ⟨hu'S, hu'R⟩ := hu'
  obtain ⟨p, hp⟩ := (huR.symm.trans hu'R).exists_isPath
  let f : Fin (p.length + 1) → V := fun i => (p.getVert i.val).val
  have hf : IsIndexedPath H f := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
        (by change j.val ≤ p.length; omega) (Subtype.ext hij)
    · intro i
      exact p.adj_getVert_succ i.isLt
  have hfout : ∀ i, f i ∉ S := fun i => (p.getVert i.val).property
  have hf0 : f 0 = u := by simp [f]
  have hfl : f (Fin.last p.length) = u'.val := by simp [f]
  have hb'f : b'.val ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact hfout i (hi ▸ hb')
  have hsnoc : IsIndexedPath H (Fin.snoc f b'.val) :=
    indexedPath_snoc hf hb'f (by rw [hfl]; exact hu'b')
  have hasnoc : a ∉ Set.range (Fin.snoc f b'.val) := by
    rintro ⟨i, hi⟩
    have hn : ∀ k : Fin (p.length + 2), (Fin.snoc f b'.val : Fin (p.length + 2) → V) k ≠ a := by
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa only [Fin.snoc_last] using (show b'.val ≠ a from b'.property)
      · rw [Fin.snoc_castSucc]
        exact fun h => hfout j (h ▸ ha)
    exact hn i hi
  have hstart : H.Adj a ((Fin.snoc f b'.val : Fin (p.length + 2) → V) 0) := by
    have hz : (0 : Fin (p.length + 2)) = (0 : Fin (p.length + 1)).castSucc := rfl
    rw [hz, Fin.snoc_castSucc, hf0]
    exact hua.symm
  refine ⟨p.length + 2, by omega, Fin.cons a (Fin.snoc f b'.val),
    indexedPath_cons hsnoc hasnoc hstart, ?_, ?_, ?_⟩
  · simpa only [Fin.cons_zero] using ha
  · change (Fin.cons a (Fin.snoc f b'.val) : Fin (p.length + 3) → V)
      (Fin.last (p.length + 1)).succ ∈ S
    simpa only [Fin.cons_succ, Fin.snoc_last] using hb'
  · intro i hi hil
    let j : Fin (p.length + 1) := ⟨i.val - 1, by omega⟩
    have hij : j.castSucc.succ = i := by apply Fin.ext; dsimp [j]; omega
    rw [← hij, Fin.cons_succ, Fin.snoc_castSucc]
    exact hfout j
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem ce_cycle_to_indexed {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i))) : IsIndexedPath H c := by
  refine ⟨hc, fun i => ?_⟩
  have hn : cycleNext i.castSucc = i.succ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.succ.isLt
  simpa only [hn] using he i.castSucc
theorem ce_cycle_rotate {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i))) (a : Fin (r + 1)) :
    Function.Injective (fun i => c (i + a)) ∧
      ∀ i, H.Adj (c (i + a)) (c (cycleNext i + a)) := by
  refine ⟨hc.comp (fun _ _ h => add_right_cancel h), fun i => ?_⟩
  simpa only [cycleNext_eq_add_one, add_assoc, add_comm 1 a] using he (i + a)
theorem ce_consecutive_ear_cycle {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (a : Fin (r + 1)) {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c a) (hgl : g (Fin.last l) = c (a + 1))
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ j : Fin (r + 1), c j ≠ g i) : HasCycle H (r + l) := by
  let f : Fin (r + 1) → V := fun i => c (i + (a + 1))
  have hf : IsIndexedPath H f :=
    ce_cycle_to_indexed (ce_cycle_rotate hc he (a + 1)).1
      (ce_cycle_rotate hc he (a + 1)).2
  have hlast : (Fin.last r : Fin (r + 1)) + 1 = 0 := by
    rw [← cycleNext_eq_add_one]
    apply Fin.ext
    simp [cycleNext]
  have hflast : f (Fin.last r) = c a := by
    dsimp [f]
    congr 1
    calc
      Fin.last r + (a + 1) = (Fin.last r + 1) + a := by abel
      _ = a := by rw [hlast, zero_add]
  apply cycle_of_two_indexed_paths hl f g hf hg
  · exact hg0.trans hflast.symm
  · simpa only [f, zero_add] using hgl
  · intro i hi hil j
    exact hdis i hi hil (j + (a + 1))
private def ceChordIndex {r : ℕ} (j : Fin r) (i : Fin (r + 1)) : Fin (r + 1) :=
  ⟨if i.val < j.val then j.val - i.val else if i.val < r then i.val + 1 else 0,
    by split_ifs <;> have := j.isLt <;> omega⟩
private theorem ceChordIndex_injective {r : ℕ} (j : Fin r) :
    Function.Injective (ceChordIndex j) := by
  intro i k h
  have hv := congrArg Fin.val h
  dsimp [ceChordIndex] at hv
  apply Fin.ext
  have hi := i.isLt
  have hk := k.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega
private theorem ce_cycle_step {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    {i j : Fin (r + 1)} (h : i.val + 1 = j.val) : H.Adj (c i) (c j) := by
  have hn : cycleNext i = j := by
    apply Fin.ext
    change (i.val + 1) % (r + 1) = j.val
    rw [h, Nat.mod_eq_of_lt j.isLt]
  simpa only [hn] using he i
theorem ce_successor_chord_path {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (j : Fin r) (hj : 0 < j.val)
    (hchord : H.Adj (c ⟨1, by omega⟩) (c j.succ)) :
    ∃ f : Fin (r + 1) → V, IsIndexedPath H f ∧
      f 0 = c j.castSucc ∧ f (Fin.last r) = c 0 ∧
      Set.range f = Set.range c := by
  let f := c ∘ ceChordIndex j
  have hpath : IsIndexedPath H f := by
    refine ⟨hc.comp (ceChordIndex_injective j), fun i => ?_⟩
    by_cases hb : i.val + 1 < j.val
    · apply (ce_cycle_step he ?_).symm
      simp only [ceChordIndex, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> omega
    · by_cases heq : i.val + 1 = j.val
      · have hl : ceChordIndex j i.castSucc = ⟨1, by omega⟩ := by
          apply Fin.ext
          simp only [ceChordIndex, Fin.val_castSucc]
          split_ifs <;> omega
        have hr : ceChordIndex j i.succ = j.succ := by
          apply Fin.ext
          simp only [ceChordIndex, Fin.val_succ]
          split_ifs <;> have := j.isLt <;> omega
        simpa only [f, Function.comp_apply, hl, hr] using hchord
      · by_cases hlast : i.val + 1 = r
        · have hl : ceChordIndex j i.castSucc = Fin.last r := by
            apply Fin.ext
            simp only [ceChordIndex, Fin.val_castSucc, Fin.val_last]
            split_ifs <;> have := j.isLt <;> omega
          have hr : ceChordIndex j i.succ = 0 := by
            apply Fin.ext
            simp only [ceChordIndex, Fin.val_succ, Fin.val_zero]
            split_ifs <;> have := j.isLt <;> omega
          have hn : cycleNext (Fin.last r) = 0 := by
            apply Fin.ext
            simp [cycleNext]
          simpa only [f, Function.comp_apply, hl, hr, hn] using he (Fin.last r)
        · apply ce_cycle_step he
          simp only [ceChordIndex, Fin.val_succ, Fin.val_castSucc]
          split_ifs <;> have := i.isLt <;> omega
  refine ⟨f, hpath, ?_, ?_, ?_⟩
  · apply congrArg c
    apply Fin.ext
    simp [ceChordIndex, hj]
  · apply congrArg c
    apply Fin.ext
    simp [ceChordIndex, Nat.not_lt.mpr j.isLt.le]
  · have hsurj := Finite.surjective_of_injective (ceChordIndex_injective j)
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ceChordIndex j i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hsurj i
      exact ⟨k, by simp only [f, Function.comp_apply, hk]⟩
theorem ce_chord_ear_cycle {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i))) (j : Fin r) (hj : 0 < j.val)
    (hchord : H.Adj (c ⟨1, by omega⟩) (c j.succ))
    {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c 0) (hgl : g (Fin.last l) = c j.castSucc)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : HasCycle H (r + l) := by
  obtain ⟨f, hf, hf0, hfl, hrange⟩ := ce_successor_chord_path hc he j hj hchord
  apply cycle_of_two_indexed_paths hl f g hf hg (hg0.trans hfl.symm) (hgl.trans hf0.symm)
  intro i hi hil k
  obtain ⟨q, hq⟩ := hrange.subset ⟨k, rfl⟩
  exact fun h => hdis i hi hil q (hq.trans h)
theorem ce_indexedPath_tail {V : Type*} {H : SimpleGraph V} {r : ℕ}
    {g : Fin (r + 2) → V} (hg : IsIndexedPath H g) :
    IsIndexedPath H (fun i : Fin (r + 1) => g i.succ) := by
  refine ⟨hg.1.comp (Fin.succ_injective _), fun i => ?_⟩
  have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  simpa only [hi] using hg.2 i.succ
theorem ce_reverse_tail_snoc {V : Type*} {H : SimpleGraph V} {l : ℕ}
    (hl : 2 ≤ l) {g : Fin (l + 1) → V} (hg : IsIndexedPath H g) (v : V)
    (hv : ∀ i : Fin (l + 1), 0 < i.val → g i ≠ v)
    (hadj : H.Adj (g ⟨1, by omega⟩) v) :
    ∃ h : Fin (l + 1) → V, IsIndexedPath H h ∧
      h 0 = g (Fin.last l) ∧ h (Fin.last l) = v ∧
      ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
        ∃ j : Fin (l + 1), 0 < j.val ∧ j.val < l ∧ h i = g j := by
  obtain ⟨s, rfl⟩ : ∃ s, l = s + 2 := ⟨l - 2, by omega⟩
  let f : Fin (s + 2) → V := fun i => g i.rev.succ
  have hf : IsIndexedPath H f := indexedPath_reverse (ce_indexedPath_tail hg)
  have hfv : v ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact hv i.rev.succ (by simp) hi
  have hfl : f (Fin.last (s + 1)) = g ⟨1, by omega⟩ := by
    simp [f]
  refine ⟨Fin.snoc f v, indexedPath_snoc hf hfv (hfl.symm ▸ hadj), ?_, ?_, ?_⟩
  · have hz : (0 : Fin (s + 3)) = (0 : Fin (s + 2)).castSucc := rfl
    rw [hz, Fin.snoc_castSucc]
    simp [f]
  · exact Fin.snoc_last _ _
  · intro i hi hil
    let k : Fin (s + 2) := ⟨i.val, hil⟩
    have hki : k.castSucc = i := Fin.ext rfl
    refine ⟨k.rev.succ, by simp, ?_, ?_⟩
    · simp only [Fin.val_succ, Fin.val_rev]
      dsimp [k]
      omega
    · rw [← hki, Fin.snoc_castSucc]
theorem ce_no_external_common_neighbor {V : Type*} {H : SimpleGraph V} {r : ℕ}
    (hr : 2 ≤ r) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) {x : V}
    (hx : ∀ i, c i ≠ x) (h0 : H.Adj (c 0) x) :
    ¬ H.Adj (c ⟨1, by omega⟩) x := by
  intro h1
  let one : Fin (r + 1) := ⟨1, by omega⟩
  have h01 : c 0 ≠ c one := by
    intro h
    have hv := congrArg Fin.val (hc h)
    simp only [Fin.val_zero, one] at hv
    omega
  let g : Fin 3 → V := ![c 0, x, c one]
  have hg : IsIndexedPath H g := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [g]
      exact False.elim (hx one rfl)
    · intro i
      fin_cases i
      · simpa [g] using h0
      · simpa [g] using h1.symm
  have hend : g (Fin.last 2) = c ((0 : Fin (r + 1)) + 1) := by
    have h : (1 : Fin (r + 1)) = one := by
      apply Fin.ext
      simp [one, Nat.mod_eq_of_lt (show 1 < r + 1 by omega)]
    simp [g, h]
  have hd : ∀ i : Fin 3, 0 < i.val → i.val < 2 →
      ∀ j : Fin (r + 1), c j ≠ g i := by
    intro i hi hi' j
    have heq : i = 1 := by apply Fin.ext; simp; omega
    simpa [heq, g] using hx j
  have h := hmax (r + 2) (ce_consecutive_ear_cycle (by omega) hc he 0 hg (by simp [g]) hend hd)
  omega
theorem ce_nonwrapping_ear_impossible {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hr : 2 ≤ r) (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) (hα : ¬ HasIndependent H 3)
    (j : Fin r) (hj : 0 < j.val) {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c 0) (hgl : g (Fin.last l) = c j.castSucc)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : False := by
  let one : Fin (r + 1) := ⟨1, by omega⟩
  let first : Fin (l + 1) := ⟨1, by omega⟩
  have hx : ∀ k, c k ≠ g first := hdis first (by simp [first]) (by dsimp [first]; omega)
  have h01x : H.Adj (c 0) (g first) := by
    simpa only [hg0] using (show H.Adj (g 0) (g first) from hg.2 ⟨0, by omega⟩)
  have h1x : ¬ H.Adj (c one) (g first) :=
    ce_no_external_common_neighbor hr hc he hmax hx h01x
  have hchord : ¬ H.Adj (c one) (c j.succ) := by
    intro h
    have hn := hmax (r + l) (ce_chord_ear_cycle hl hc he j hj h hg hg0 hgl hdis)
    omega
  have hdist : c one ≠ c j.succ := by
    intro h
    have hv := congrArg Fin.val (hc h)
    simp only [one, Fin.val_succ] at hv
    omega
  have hnextx : H.Adj (c j.succ) (g first) := by
    by_contra h
    exact hα (hasIndependent_three_of_distinct_nonadjacent hdist (hx one) (hx j.succ)
      hchord h1x h)
  have hjnext : cycleNext j.castSucc = j.succ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt j.succ.isLt
  have hbnext : c j.castSucc ≠ c j.succ := (hjnext ▸ he j.castSucc).ne
  have hv : ∀ i : Fin (l + 1), 0 < i.val → g i ≠ c j.succ := by
    intro i hi
    by_cases hil : i.val < l
    · exact (hdis i hi hil j.succ).symm
    · have hi' : i = Fin.last l := by apply Fin.ext; have := i.isLt; simp; omega
      simpa only [hi', hgl] using hbnext
  obtain ⟨p, hp, hp0, hpl, hpm⟩ := ce_reverse_tail_snoc hl hg (c j.succ) hv hnextx.symm
  have hend : p (Fin.last l) = c (j.castSucc + 1) := by
    rw [← cycleNext_eq_add_one, hjnext]
    exact hpl
  have hd : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ p i := by
    intro i hi hil k
    obtain ⟨u, hu, hul, hiu⟩ := hpm i hi hil
    rw [hiu]
    exact hdis u hu hul k
  have hn := hmax (r + l) (ce_consecutive_ear_cycle hl hc he j.castSucc hp
    (hp0.trans hgl) hend hd)
  omega
theorem ce_rooted_ear_impossible {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hr : 2 ≤ r) (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) (hα : ¬ HasIndependent H 3)
    {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 = c 0) (hgl : g (Fin.last l) ∈ Set.range c)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : False := by
  obtain ⟨j, hj⟩ := hgl
  have hj0 : j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val (hg.1 (hj.symm.trans (h ▸ hg0.symm)))
    simp only [Fin.val_last, Fin.val_zero] at hv
    omega
  by_cases hjlast : j = Fin.last r
  · have hp : IsIndexedPath H (g ∘ Fin.rev) := indexedPath_reverse hg
    have hp0 : (g ∘ Fin.rev) 0 = c (Fin.last r) := by
      simpa only [Function.comp_apply, Fin.rev_zero, hjlast] using hj.symm
    have hn : cycleNext (Fin.last r) = 0 := by
      apply Fin.ext
      simp [cycleNext]
    have hpl : (g ∘ Fin.rev) (Fin.last l) = c (Fin.last r + 1) := by
      rw [← cycleNext_eq_add_one, hn]
      simpa only [Function.comp_apply, Fin.rev_last] using hg0
    have hd : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
        ∀ k : Fin (r + 1), c k ≠ (g ∘ Fin.rev) i := by
      intro i hi hil k
      apply hdis i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega) k
    have h := hmax (r + l) (ce_consecutive_ear_cycle hl hc he (Fin.last r) hp hp0 hpl hd)
    omega
  · have hjlt : j.val < r := by
      have hneq : j.val ≠ r := fun h => hjlast (Fin.ext h)
      have := j.isLt
      omega
    let j' : Fin r := ⟨j.val, hjlt⟩
    have hcast : j'.castSucc = j := Fin.ext rfl
    have hjpos : 0 < j'.val := by
      have hneq : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      dsimp [j']
      omega
    exact ce_nonwrapping_ear_impossible hr hl hc he hmax hα j' hjpos hg hg0
      (by simpa only [hcast] using hj.symm) hdis
theorem ce_external_ear_impossible {V : Type*} {H : SimpleGraph V} {r l : ℕ}
    (hr : 2 ≤ r) (hl : 2 ≤ l) {c : Fin (r + 1) → V} (hc : Function.Injective c)
    (he : ∀ i, H.Adj (c i) (c (cycleNext i)))
    (hmax : ∀ q, HasCycle H q → q ≤ r + 1) (hα : ¬ HasIndependent H 3)
    {g : Fin (l + 1) → V} (hg : IsIndexedPath H g)
    (hg0 : g 0 ∈ Set.range c) (hgl : g (Fin.last l) ∈ Set.range c)
    (hdis : ∀ i : Fin (l + 1), 0 < i.val → i.val < l →
      ∀ k : Fin (r + 1), c k ≠ g i) : False := by
  obtain ⟨a, ha⟩ := hg0
  let d : Fin (r + 1) → V := fun i => c (i + a)
  obtain ⟨hd, hde⟩ := ce_cycle_rotate hc he a
  have hd0 : g 0 = d 0 := by simpa only [d, zero_add] using ha.symm
  have hdlast : g (Fin.last l) ∈ Set.range d := by
    obtain ⟨b, hb⟩ := hgl
    exact ⟨b - a, by simpa only [d, sub_add_cancel] using hb⟩
  exact ce_rooted_ear_impossible hr hl hd hde hmax hα hg hd0 hdlast
    (fun i hi hil k => hdis i hi hil (k + a))
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique.Construction
theorem ce_exists_longest_cycle {V : Type*} [Fintype V] {H : SimpleGraph V}
    (hcard : 6 ≤ Fintype.card V) (hα : ¬ HasIndependent H 3) :
    ∃ r, 2 ≤ r ∧ ∃ c : Fin (r + 1) → V, Function.Injective c ∧
      (∀ i, H.Adj (c i) (c (cycleNext i))) ∧
      ∀ q, HasCycle H q → q ≤ r + 1 := by
  classical
  let f : Fin 6 → V := fun i => (Fintype.equivFin V).symm (Fin.castLE hcard i)
  have hf : Function.Injective f := (Fintype.equivFin V).symm.injective.comp
    (Fin.castLE_injective hcard)
  have hthree : HasCycle H 3 := by
    rcases triangle_upper (H.comap f) with h | h
    · exact h.map f hf (fun h => h)
    · exact False.elim (hα (h.map f hf (fun h => h)))
  let N := Fintype.card V
  have hex : ∃ d, ∃ q, HasCycle H q ∧ q + d = N :=
    ⟨N - 3, 3, hthree, by dsimp [N]; omega⟩
  obtain ⟨q, hq, hqd⟩ := Nat.find_spec hex
  have hmax : ∀ t, HasCycle H t → t ≤ q := by
    intro t ht
    have htcard : t ≤ N := ht.card_le
    have hm := Nat.find_min' hex
      (show ∃ q, HasCycle H q ∧ q + (N - t) = N from
        ⟨t, ht, Nat.add_sub_of_le htcard⟩)
    omega
  have hq3 : 3 ≤ q := hmax 3 hthree
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc, he⟩ := hq
  exact ⟨r, by omega, c, hc, he, hmax⟩
theorem ceAlphaTwo_proved : CEAlphaTwo := by
  intro V _ H hcard hconn hdel hα
  classical
  obtain ⟨r, hr, c, hc, he, hmax⟩ := ce_exists_longest_cycle hcard hα
  by_cases hsurj : Function.Surjective c
  · have hn : r + 1 = Fintype.card V := by
      simpa using Fintype.card_of_bijective ⟨hc, hsurj⟩
    exact hn ▸ (show HasCycle H (r + 1) from ⟨c, hc, he⟩)
  · change ¬ ∀ v, ∃ i, c i = v at hsurj
    push Not at hsurj
    obtain ⟨x, hx⟩ := hsurj
    let S : Finset V := Finset.univ.image c
    have hSmem : ∀ v, v ∈ S ↔ v ∈ Set.range c := by simp [S]
    have hScard : S.card = r + 1 := by
      simpa [S] using Finset.card_image_of_injective Finset.univ hc
    have hxS : x ∉ S := by
      intro h
      obtain ⟨i, hi⟩ := (hSmem x).mp h
      exact hx i hi
    obtain ⟨l, hl, g, hg, hg0, hgl, hgout⟩ := ce_external_ear hconn hdel S
      (by omega) x hxS
    apply False.elim
    apply ce_external_ear_impossible hr hl hc he hmax hα hg ((hSmem _).mp hg0)
      ((hSmem _).mp hgl)
    intro i hi hil k heq
    apply hgout i hi hil
    rw [← heq]
    exact (hSmem _).mpr ⟨k, rfl⟩
end CycleClique.Construction
end OAI


namespace OAI
namespace CycleClique
open scoped SimpleGraph
def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ
end CycleClique
end OAI
namespace OAI
namespace CycleClique.Construction
open scoped SimpleGraph
theorem hasCycle_iff_copy {V : Type*} {G : SimpleGraph V} {m : ℕ} (hm : 3 ≤ m) :
    HasCycle G m ↔ SimpleGraph.cycleGraph m ⊑ G := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hnext (i : Fin (k + 2)) : cycleNext i = i + 1 := by
    apply Fin.ext
    simp [cycleNext, Fin.val_add]
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro i j hij
    rcases SimpleGraph.cycleGraph_adj.mp hij with hij | hij
    · have h : i = j + 1 := (sub_eq_iff_eq_add').mp hij
      rw [h]
      exact (hnext j ▸ he j).symm
    · have h : j = i + 1 := (sub_eq_iff_eq_add').mp hij
      rw [h]
      exact hnext i ▸ he i
  · rintro ⟨f⟩
    refine ⟨f, f.injective, fun i => f.toHom.map_adj ?_⟩
    rw [hnext]
    apply SimpleGraph.cycleGraph_adj.mpr
    exact Or.inr (add_sub_cancel_left i 1)
theorem hasIndependent_iff_copy {V : Type*} {G : SimpleGraph V} {n : ℕ} :
    HasIndependent G n ↔ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro i j hij
    exact ⟨fun h => hij (hf h), he i j⟩
  · rintro ⟨f⟩
    refine ⟨f, f.injective, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst j
      exact G.loopless.irrefl _
    · exact (f.toHom.map_adj hij).2
theorem ramseyProperty_iff {m n N : ℕ} (hm : 3 ≤ m) :
    RamseyProperty m n N ↔ CycleClique.RamseyProperty m n N := by
  simp only [RamseyProperty, CycleClique.RamseyProperty, hasCycle_iff_copy hm,
    hasIndependent_iff_copy]
theorem isRamseyNumber_iff {m n N : ℕ} (hm : 3 ≤ m) :
    IsRamseyNumber m n N ↔
      CycleClique.RamseyProperty m n N ∧ ∀ M < N, ¬ CycleClique.RamseyProperty m n M := by
  simp only [IsRamseyNumber, ramseyProperty_iff hm]
end CycleClique.Construction
end OAI

open Filter OAI.CycleClique.Construction

theorem OMA.solution : OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R1.H3 := by
  unfold OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R1.H3
  filter_upwards [eventually_ge_atTop 19] with n hn
  intro k hnk _ C
  have hk : 3 ≤ k := by omega
  have h := isRamseyNumber_of_expanded_exclusion (m := k) (n := n) (by omega) (by omega) hnk (by
    intro b hb hbk G hcycle hI hexpand
    have hcycle' : ¬ HasCycle G ((k - 1) + 1) := by
      simpa only [show k - 1 + 1 = k by omega] using hcycle
    have h17 := (finite_range_clique_bounds ceAlphaTwo_proved (by omega : 5 ≤ k - 1)
      hb hbk (by simp) hI hcycle' hexpand).1
    omega)
  exact ((OAI.CycleClique.Construction.isRamseyNumber_iff hk).mp h).1 C
