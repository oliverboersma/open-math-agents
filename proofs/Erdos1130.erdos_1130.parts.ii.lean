import FormalConjectures.ErdosProblems.«1130»
import Mathlib
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Support
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Optimal interpolation arrays with their two exterior gaps

The interior gap heights must be equal. At each outer gap the height must
be at least their common value. The zero- and one-node cases are unrestricted.

The canonical equioscillation theorem of Kilgore and de Boor and Pinkus
is reused from the project's checked proof in PR 1754 (koolkao). The
affine normalization and invariance of the interior heights come from
PR 1714. For the exterior gaps, interpolation of the linear polynomial
shows that the Lebesgue function at t is at least the absolute value of t.
Shrinking a node array therefore raises both outer heights past any
prescribed threshold, without changing an interior height.
Credit for the exterior-gap extension: @ZedingZhang.
-/

/-
Erdos1130.erdos_1130.variants.canonical: the canonical characterization of Kilgore (1977, 1978) and de Boor and Pinkus
(J. Approx. Theory 24 (1978) 289-303): equioscillation of the interior local maxima, existence and
uniqueness of the equioscillating canonical node set, and the extremal properties that follow.

Proof. The de Boor-Pinkus theory (namespaces Randy1153 and Randy1153.DeBoorPinkus below) is the
Lean formalization by randyxian08, https://github.com/randyxian08/jsp000958-lean, commit
e1df51e950876056d8951f4a93fa7fef6863b422, MIT licence (notice below). It proves coordinatewise
rigidity of the gap heights (if every gap height of s is at most the corresponding one of t, then
s = t) and existence of an equioscillating endpoint-fixed array, following de Boor and Pinkus.
It is ported here from Lean v4.27 to the pinned Mathlib: the implicit function theorem API,
convert instance goals, a few simp normal forms, and three duplicated private lemmas. Comments
and declarations not needed for the final package were removed to fit the size limit.
The bridges (namespaces OMA.H1Bridge and OMA.Can) are new: a canonical node set is an endpoint
array whose gap heights are the local maxima gapMax x (g+1); the gaps cover [-1, 1], so Lambda is
the largest gap height; and rigidity against the equioscillating array gives each direction. It builds endpoint arrays from y and from the affine
rescaling of x onto [-1, 1], uses rigidity against the equioscillating array opt twice
(min_j height(y) <= height(opt) <= max_j height(x_c)), and uses affine invariance:
Lambda(x_c) <= Lambda(x).

MIT License

Copyright (c) 2026 randyxian08

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace Randy1153
open Polynomial
noncomputable section
structure NodeFamily (n : ℕ) where
  point : Fin n → ℝ
  injective : Function.Injective point
  mem_Icc : ∀ i, point i ∈ Set.Icc (-1 : ℝ) 1
def lagrangeBasis {n : ℕ} (nodes : NodeFamily n) (k : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ nodes.point k
def lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n)
    (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k,
    (t - nodes.point i) / (nodes.point k - nodes.point i)
lemma lagrangeBasis_eq_product {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeBasis nodes k =
      ∏ i ∈ Finset.univ.erase k,
        (Polynomial.X - Polynomial.C (nodes.point i)) *
          Polynomial.C (nodes.point k - nodes.point i)⁻¹ := by
  classical
  simp only [lagrangeBasis, Lagrange.basis, Lagrange.basisDivisor]
  apply Finset.prod_congr rfl
  intro i _
  exact mul_comm _ _
lemma lagrangeBasis_eval {n : ℕ} (nodes : NodeFamily n) (k : Fin n) (t : ℝ) :
    (lagrangeBasis nodes k).eval t = lagrangeFundamental nodes k t := by
  classical
  rw [lagrangeBasis_eq_product]
  simp only [lagrangeFundamental, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv]
@[simp]
lemma lagrangeBasis_eval_self {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (lagrangeBasis nodes k).eval (nodes.point k) = 1 := by
  simpa only [lagrangeBasis] using
    (Lagrange.eval_basis_self nodes.injective.injOn (Finset.mem_univ k))
@[simp]
lemma lagrangeBasis_eval_of_ne {n : ℕ} (nodes : NodeFamily n) {j k : Fin n}
    (hjk : j ≠ k) :
    (lagrangeBasis nodes k).eval (nodes.point j) = 0 := by
  simpa only [lagrangeBasis] using
    (Lagrange.eval_basis_of_ne (s := Finset.univ) (v := nodes.point)
      (i := k) (j := j) hjk.symm (Finset.mem_univ j))
def lebesgueFunction {n : ℕ} (nodes : NodeFamily n) (t : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeFundamental nodes k t|
lemma continuous_lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    Continuous (lagrangeFundamental nodes k) := by
  exact (lagrangeBasis nodes k).continuous.congr fun t => lagrangeBasis_eval nodes k t
lemma continuous_lebesgueFunction {n : ℕ} (nodes : NodeFamily n) :
    Continuous (lebesgueFunction nodes) := by
  classical
  exact continuous_finset_sum Finset.univ fun k _ =>
    (continuous_lagrangeFundamental nodes k).abs
def lebesgueOn {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) : ℝ :=
  sSup (lebesgueFunction nodes '' Set.Icc a b)
lemma exists_lebesgueOn_eq_and_ge {n : ℕ} (nodes : NodeFamily n) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ t ∈ Set.Icc a b,
      lebesgueOn nodes a b = lebesgueFunction nodes t ∧
        ∀ u ∈ Set.Icc a b, lebesgueFunction nodes u ≤ lebesgueFunction nodes t := by
  simpa only [lebesgueOn] using
    (isCompact_Icc.exists_sSup_image_eq_and_ge (Set.nonempty_Icc.mpr hab)
      (continuous_lebesgueFunction nodes).continuousOn)
end
end Randy1153
namespace Randy1153
open Polynomial
noncomputable section
lemma NodeFamily.ext {n : ℕ} {x y : NodeFamily n} (h : x.point = y.point) : x = y := by
  cases x
  cases y
  cases h
  rfl
@[simp]
lemma lagrangeFundamental_self {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeFundamental nodes k (nodes.point k) = 1 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_self nodes k
@[simp]
lemma lagrangeFundamental_of_ne {n : ℕ} (nodes : NodeFamily n) {j k : Fin n}
    (hjk : j ≠ k) :
    lagrangeFundamental nodes k (nodes.point j) = 0 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_of_ne nodes hjk
@[simp]
lemma lebesgueFunction_at_node {n : ℕ} (nodes : NodeFamily n) (j : Fin n) :
    lebesgueFunction nodes (nodes.point j) = 1 := by
  classical
  rw [lebesgueFunction, Fintype.sum_eq_single j]
  · simp
  · intro k hjk
    simp [lagrangeFundamental_of_ne nodes hjk.symm]
end
end Randy1153
namespace Randy1153
open Polynomial
noncomputable section
namespace NodeFamily
def reindex {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) : NodeFamily n where
  point := nodes.point ∘ e
  injective := nodes.injective.comp e.injective
  mem_Icc i := nodes.mem_Icc (e i)
@[simp]
lemma reindex_point {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (nodes.reindex e).point i = nodes.point (e i) :=
  rfl
@[simp]
lemma reindex_refl {n : ℕ} (nodes : NodeFamily n) :
    nodes.reindex (Equiv.refl (Fin n)) = nodes := by
  apply NodeFamily.ext
  rfl
end NodeFamily
structure OrderedNodes (n : ℕ) extends NodeFamily n where
  strictMono : StrictMono point
namespace OrderedNodes
instance {n : ℕ} : Coe (OrderedNodes n) (NodeFamily n) :=
  ⟨OrderedNodes.toNodeFamily⟩
@[simp]
lemma coe_point {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (nodes : NodeFamily n).point i = nodes.point i :=
  rfl
lemma point_lt {n : ℕ} (nodes : OrderedNodes n) {i j : Fin n} (hij : i < j) :
    nodes.point i < nodes.point j :=
  nodes.strictMono hij
lemma neg_one_le {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (-1 : ℝ) ≤ nodes.point i :=
  (nodes.mem_Icc i).1
lemma le_one {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    nodes.point i ≤ (1 : ℝ) :=
  (nodes.mem_Icc i).2
end OrderedNodes
namespace NodeFamily
def nodeFinset {n : ℕ} (nodes : NodeFamily n) : Finset ℝ :=
  Finset.univ.image nodes.point
@[simp]
lemma mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (x : ℝ) :
    x ∈ nodes.nodeFinset ↔ ∃ i : Fin n, nodes.point i = x := by
  simp [nodeFinset]
@[simp]
lemma card_nodeFinset {n : ℕ} (nodes : NodeFamily n) : nodes.nodeFinset.card = n := by
  classical
  rw [nodeFinset, Finset.card_image_of_injOn nodes.injective.injOn,
    Finset.card_univ, Fintype.card_fin]
def sortedPoint {n : ℕ} (nodes : NodeFamily n) : Fin n ↪o ℝ :=
  nodes.nodeFinset.orderEmbOfFin (card_nodeFinset nodes)
@[simp]
lemma sortedPoint_mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.sortedPoint i ∈ nodes.nodeFinset :=
  Finset.orderEmbOfFin_mem _ _ _
def sorted {n : ℕ} (nodes : NodeFamily n) : OrderedNodes n where
  point := nodes.sortedPoint
  injective := nodes.sortedPoint.injective
  mem_Icc i := by
    rcases (mem_nodeFinset nodes (nodes.sortedPoint i)).mp
      (sortedPoint_mem_nodeFinset nodes i) with ⟨j, hj⟩
    rw [← hj]
    exact nodes.mem_Icc j
  strictMono := nodes.sortedPoint.strictMono
@[simp]
lemma sorted_point {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.sorted.point i = nodes.sortedPoint i :=
  rfl
def rangeEquiv {n : ℕ} (nodes : NodeFamily n) : Fin n ≃ ↥nodes.nodeFinset :=
  Equiv.ofBijective
    (fun i => ⟨nodes.point i, (mem_nodeFinset nodes _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => nodes.injective (congrArg Subtype.val h), fun y => by
      rcases (mem_nodeFinset nodes y).mp y.property with ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩
@[simp]
lemma coe_rangeEquiv_apply {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    ((nodes.rangeEquiv i : nodes.nodeFinset) : ℝ) = nodes.point i :=
  rfl
end NodeFamily
end
end Randy1153
namespace Randy1153
open Polynomial
open scoped BigOperators
noncomputable section
def gapLeftIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val, by omega⟩
def gapRightIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val + 1, by omega⟩
@[simp]
lemma gapLeftIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (gapLeftIndex g).val = g.val :=
  rfl
@[simp]
lemma gapRightIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (gapRightIndex g).val = g.val + 1 :=
  rfl
lemma gapLeftIndex_lt_rightIndex {n : ℕ} (g : Fin (n - 1)) :
    gapLeftIndex g < gapRightIndex g := by
  simp [Fin.lt_def]
def closedGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : Set ℝ :=
  Set.Icc (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))
def openGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : Set ℝ :=
  Set.Ioo (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))
lemma gap_left_lt_right {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    nodes.point (gapLeftIndex g) < nodes.point (gapRightIndex g) :=
  nodes.point_lt (gapLeftIndex_lt_rightIndex g)
lemma openGap_nonempty {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (openGap nodes g).Nonempty :=
  Set.nonempty_Ioo.mpr (gap_left_lt_right nodes g)
def gapNegative {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) : Prop :=
  (j < k ∧ g.val < j.val) ∨ (k < j ∧ j.val ≤ g.val)
instance gapNegativeDecidable {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    Decidable (gapNegative g k j) := by
  unfold gapNegative
  infer_instance
def gapSignFactor {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) : ℝ :=
  if gapNegative g k j then -1 else 1
def gapCoefficient {n : ℕ} (g : Fin (n - 1)) (k : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.erase k, gapSignFactor g k j
lemma gapSignFactor_eq_one_or_neg_one {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    gapSignFactor g k j = 1 ∨ gapSignFactor g k j = -1 := by
  simp only [gapSignFactor]
  split_ifs <;> simp
@[simp]
lemma abs_gapSignFactor {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    |gapSignFactor g k j| = 1 := by
  rcases gapSignFactor_eq_one_or_neg_one g k j with h | h <;> simp [h]
lemma gapCoefficient_eq_one_or_neg_one {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    gapCoefficient g k = 1 ∨ gapCoefficient g k = -1 := by
  classical
  rw [gapCoefficient]
  generalize Finset.univ.erase k = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs]
      rcases gapSignFactor_eq_one_or_neg_one g k j with h | h <;>
        rcases ih with h' | h' <;> simp [h, h']
@[simp]
lemma abs_gapCoefficient {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    |gapCoefficient g k| = 1 := by
  rcases gapCoefficient_eq_one_or_neg_one g k with h | h <;> simp [h]
lemma gapCoefficient_ne_zero {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    gapCoefficient g k ≠ 0 := by
  intro h
  have habs := abs_gapCoefficient g k
  simp [h] at habs
private lemma prod_gapSignFactor_eq_pow_card_filter {n : ℕ}
    (g : Fin (n - 1)) (k : Fin n) (s : Finset (Fin n)) :
    (∏ j ∈ s, gapSignFactor g k j) =
      (-1 : ℝ) ^ (s.filter (gapNegative g k)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs, Finset.filter_insert, ih]
      by_cases hj : gapNegative g k j
      · have hjfilter : j ∉ s.filter (gapNegative g k) := by simp [hjs]
        simp [hj, hjfilter, gapSignFactor, pow_succ]
      · simp [hj, gapSignFactor]
private lemma negative_filter_eq_Ioc {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hkg : k.val ≤ g.val) :
    (Finset.univ.erase k).filter (gapNegative g k) =
      Finset.Ioc k (gapLeftIndex g) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_Ioc, gapNegative]
  constructor
  · rintro ⟨hjk, (⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩)⟩
    · have : j.val < k.val := hjklt
      omega
    · exact ⟨hkj, by simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hjg⟩
  · rintro ⟨hkj, hjg⟩
    refine ⟨hkj.ne', Or.inr ⟨hkj, ?_⟩⟩
    simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hjg
private lemma negative_filter_eq_Ioo {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hgk : g.val < k.val) :
    (Finset.univ.erase k).filter (gapNegative g k) =
      Finset.Ioo (gapLeftIndex g) k := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_Ioo, gapNegative]
  constructor
  · rintro ⟨hjk, (⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩)⟩
    · exact ⟨by simpa only [Fin.lt_def, gapLeftIndex_val] using hgj, hjklt⟩
    · have : k.val < j.val := hkj
      omega
  · rintro ⟨hgj, hjk⟩
    refine ⟨hjk.ne, Or.inl ⟨hjk, ?_⟩⟩
    simpa only [Fin.lt_def, gapLeftIndex_val] using hgj
lemma gapCoefficient_of_le {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hkg : k.val ≤ g.val) :
    gapCoefficient g k = (-1 : ℝ) ^ (g.val - k.val) := by
  classical
  rw [gapCoefficient, prod_gapSignFactor_eq_pow_card_filter,
    negative_filter_eq_Ioc g k hkg, Fin.card_Ioc]
  rfl
lemma gapCoefficient_of_lt {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hgk : g.val < k.val) :
    gapCoefficient g k = (-1 : ℝ) ^ (k.val - g.val - 1) := by
  classical
  rw [gapCoefficient, prod_gapSignFactor_eq_pow_card_filter,
    negative_filter_eq_Ioo g k hgk, Fin.card_Ioo]
  rfl
@[simp]
lemma gapCoefficient_left {n : ℕ} (g : Fin (n - 1)) :
    gapCoefficient g (gapLeftIndex g) = 1 := by
  rw [gapCoefficient_of_le]
  · simp
  · simp
@[simp]
lemma gapCoefficient_right {n : ℕ} (g : Fin (n - 1)) :
    gapCoefficient g (gapRightIndex g) = 1 := by
  rw [gapCoefficient_of_lt]
  · simp
  · simp
lemma gapCoefficient_right_eq_neg_left_of_ne {n : ℕ}
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    gapCoefficient g (gapRightIndex h) =
      -gapCoefficient g (gapLeftIndex h) := by
  rcases lt_or_gt_of_ne hhg with hhglt | hghlt
  · have hright_le : (gapRightIndex h).val ≤ g.val := by
      simp only [gapRightIndex_val]
      omega
    have hleft_le : (gapLeftIndex h).val ≤ g.val := by
      simp only [gapLeftIndex_val]
      omega
    rw [gapCoefficient_of_le g _ hright_le,
      gapCoefficient_of_le g _ hleft_le]
    have hexp : g.val - (gapLeftIndex h).val =
        (g.val - (gapRightIndex h).val) + 1 := by
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    rw [hexp, pow_succ]
    ring
  · have hgleft : g.val < (gapLeftIndex h).val := by
      simp only [gapLeftIndex_val]
      omega
    have hgright : g.val < (gapRightIndex h).val := by
      simp only [gapRightIndex_val]
      omega
    rw [gapCoefficient_of_lt g _ hgright,
      gapCoefficient_of_lt g _ hgleft]
    have hexp : (gapRightIndex h).val - g.val - 1 =
        ((gapLeftIndex h).val - g.val - 1) + 1 := by
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    rw [hexp, pow_succ]
    ring
def lowerAdjacentGap {n : ℕ} (q : Fin (n - 2)) : Fin (n - 1) :=
  ⟨q.val, by omega⟩
def upperAdjacentGap {n : ℕ} (q : Fin (n - 2)) : Fin (n - 1) :=
  ⟨q.val + 1, by omega⟩
def adjacentCommonNode {n : ℕ} (q : Fin (n - 2)) : Fin n :=
  ⟨q.val + 1, by omega⟩
@[simp]
lemma lowerAdjacentGap_val {n : ℕ} (q : Fin (n - 2)) :
    (lowerAdjacentGap q).val = q.val :=
  rfl
@[simp]
lemma upperAdjacentGap_val {n : ℕ} (q : Fin (n - 2)) :
    (upperAdjacentGap q).val = q.val + 1 :=
  rfl
@[simp]
lemma adjacentCommonNode_val {n : ℕ} (q : Fin (n - 2)) :
    (adjacentCommonNode q).val = q.val + 1 :=
  rfl
lemma exists_gapCoefficient_eq_neg_one {n : ℕ} (hn : 3 ≤ n) (g : Fin (n - 1)) :
    ∃ k : Fin n, gapCoefficient g k = -1 := by
  by_cases hg0 : g.val = 0
  · let k : Fin n := ⟨2, by omega⟩
    refine ⟨k, ?_⟩
    have hgk : g.val < k.val := by simp [k, hg0]
    rw [gapCoefficient_of_lt g k hgk]
    simp [k, hg0]
  · let k : Fin n := ⟨g.val - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hkg : k.val ≤ g.val := by simp [k]
    rw [gapCoefficient_of_le g k hkg]
    have hexp : g.val - k.val = 1 := by
      simp only [k]
      omega
    rw [hexp]
    norm_num
def gapPolynomial {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ nodes.point (gapCoefficient g)
lemma gapPolynomial_eval_node {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1))
    (k : Fin n) :
    (gapPolynomial nodes g).eval (nodes.point k) = gapCoefficient g k := by
  simpa only [gapPolynomial] using
    (Lagrange.eval_interpolate_at_node (r := gapCoefficient g)
      nodes.injective.injOn (Finset.mem_univ k))
@[simp]
lemma gapPolynomial_eval_left {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapLeftIndex g)) = 1 := by
  rw [gapPolynomial_eval_node, gapCoefficient_left]
@[simp]
lemma gapPolynomial_eval_right {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapRightIndex g)) = 1 := by
  rw [gapPolynomial_eval_node, gapCoefficient_right]
lemma degree_gapPolynomial_le {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).degree ≤ (n - 1 : ℕ) := by
  simpa only [gapPolynomial, Finset.card_univ, Fintype.card_fin] using
    (Lagrange.degree_interpolate_le (s := Finset.univ) (r := gapCoefficient g)
      nodes.injective.injOn)
private lemma numerator_nonneg_of_le_gap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hjg : j.val ≤ g.val)
    (ht : t ∈ closedGap nodes g) :
    0 ≤ t - nodes.point j := by
  rw [sub_nonneg]
  exact (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simpa using hjg))).trans ht.1
private lemma numerator_nonpos_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hgj : g.val < j.val)
    (ht : t ∈ closedGap nodes g) :
    t - nodes.point j ≤ 0 := by
  rw [sub_nonpos]
  exact ht.2.trans (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simp only [gapRightIndex_val]; omega)))
private lemma numerator_pos_of_le_gap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hjg : j.val ≤ g.val)
    (ht : t ∈ openGap nodes g) :
    0 < t - nodes.point j := by
  rw [sub_pos]
  exact (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simpa using hjg))).trans_lt ht.1
private lemma numerator_neg_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hgj : g.val < j.val)
    (ht : t ∈ openGap nodes g) :
    t - nodes.point j < 0 := by
  rw [sub_neg]
  exact ht.2.trans_le (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simp only [gapRightIndex_val]; omega)))
private lemma denominator_pos_of_lt {n : ℕ} (nodes : OrderedNodes n) {j k : Fin n}
    (hjk : j < k) :
    0 < nodes.point k - nodes.point j := by
  rw [sub_pos]
  exact nodes.point_lt hjk
private lemma denominator_neg_of_lt {n : ℕ} (nodes : OrderedNodes n) {j k : Fin n}
    (hkj : k < j) :
    nodes.point k - nodes.point j < 0 := by
  rw [sub_neg]
  exact nodes.point_lt hkj
lemma gapSignFactor_mul_div_nonneg {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {k j : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    0 ≤ gapSignFactor g k j *
      ((t - nodes.point j) / (nodes.point k - nodes.point j)) := by
  by_cases hneg : gapNegative g k j
  · rw [gapSignFactor, if_pos hneg, neg_one_mul]
    apply neg_nonneg.mpr
    rcases hneg with ⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩
    · exact div_nonpos_of_nonpos_of_nonneg
        (numerator_nonpos_of_gap_lt nodes g hgj ht)
        (denominator_pos_of_lt nodes hjklt).le
    · exact div_nonpos_of_nonneg_of_nonpos
        (numerator_nonneg_of_le_gap nodes g hjg ht)
        (denominator_neg_of_lt nodes hkj).le
  · rw [gapSignFactor, if_neg hneg, one_mul]
    rcases lt_or_gt_of_ne hjk with hjklt | hkj
    · have hjg : j.val ≤ g.val := by
        by_contra h
        apply hneg
        exact Or.inl ⟨hjklt, Nat.lt_of_not_ge h⟩
      exact div_nonneg
        (numerator_nonneg_of_le_gap nodes g hjg ht)
        (denominator_pos_of_lt nodes hjklt).le
    · have hgj : g.val < j.val := by
        by_contra h
        apply hneg
        exact Or.inr ⟨hkj, Nat.le_of_not_gt h⟩
      exact div_nonneg_of_nonpos
        (numerator_nonpos_of_gap_lt nodes g hgj ht)
        (denominator_neg_of_lt nodes hkj).le
lemma gapSignFactor_mul_div_pos {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {k j : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : t ∈ openGap nodes g) :
    0 < gapSignFactor g k j *
      ((t - nodes.point j) / (nodes.point k - nodes.point j)) := by
  by_cases hneg : gapNegative g k j
  · rw [gapSignFactor, if_pos hneg, neg_one_mul]
    apply neg_pos.mpr
    rcases hneg with ⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩
    · exact div_neg_of_neg_of_pos
        (numerator_neg_of_gap_lt nodes g hgj ht)
        (denominator_pos_of_lt nodes hjklt)
    · exact div_neg_of_pos_of_neg
        (numerator_pos_of_le_gap nodes g hjg ht)
        (denominator_neg_of_lt nodes hkj)
  · rw [gapSignFactor, if_neg hneg, one_mul]
    rcases lt_or_gt_of_ne hjk with hjklt | hkj
    · have hjg : j.val ≤ g.val := by
        by_contra h
        apply hneg
        exact Or.inl ⟨hjklt, Nat.lt_of_not_ge h⟩
      exact div_pos
        (numerator_pos_of_le_gap nodes g hjg ht)
        (denominator_pos_of_lt nodes hjklt)
    · have hgj : g.val < j.val := by
        by_contra h
        apply hneg
        exact Or.inr ⟨hkj, Nat.le_of_not_gt h⟩
      exact div_pos_of_neg_of_neg
        (numerator_neg_of_gap_lt nodes g hgj ht)
        (denominator_neg_of_lt nodes hkj)
lemma gapCoefficient_mul_lagrangeFundamental_nonneg {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    0 ≤ gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  rw [gapCoefficient, lagrangeFundamental, ← Finset.prod_mul_distrib]
  exact Finset.prod_nonneg fun j hj =>
    gapSignFactor_mul_div_nonneg nodes g (Finset.mem_erase.mp hj).1 ht
lemma gapCoefficient_mul_lagrangeFundamental_pos {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ openGap nodes g) :
    0 < gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  rw [gapCoefficient, lagrangeFundamental, ← Finset.prod_mul_distrib]
  exact Finset.prod_pos fun j hj =>
    gapSignFactor_mul_div_pos nodes g (Finset.mem_erase.mp hj).1 ht
lemma abs_lagrangeFundamental_eq_gapCoefficient_mul {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    |lagrangeFundamental nodes.toNodeFamily k t| =
      gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  calc
    |lagrangeFundamental nodes.toNodeFamily k t| =
        |gapCoefficient g k| * |lagrangeFundamental nodes.toNodeFamily k t| := by simp
    _ = |gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t| :=
      (abs_mul _ _).symm
    _ = gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t :=
      abs_of_nonneg (gapCoefficient_mul_lagrangeFundamental_nonneg nodes g k ht)
lemma gapPolynomial_eval_eq_sum {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (t : ℝ) :
    (gapPolynomial nodes g).eval t =
      ∑ k : Fin n, gapCoefficient g k *
        lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  simp only [gapPolynomial, Lagrange.interpolate_apply, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  change gapCoefficient g k * (lagrangeBasis nodes.toNodeFamily k).eval t = _
  rw [lagrangeBasis_eval]
lemma sum_lagrangeFundamental_eq_one {n : ℕ} (nodes : OrderedNodes n)
    (hn : 0 < n) (t : ℝ) :
    ∑ k : Fin n, lagrangeFundamental nodes.toNodeFamily k t = 1 := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hbasis := Lagrange.sum_basis nodes.injective.injOn huniv
  have heval := congrArg (Polynomial.eval t) hbasis
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_one] at heval
  calc
    ∑ k : Fin n, lagrangeFundamental nodes.toNodeFamily k t =
        ∑ k : Fin n, (Lagrange.basis Finset.univ nodes.point k).eval t := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← lagrangeBasis_eval]
      rfl
    _ = 1 := by simpa using heval
lemma lebesgueFunction_eq_eval_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ closedGap nodes g) :
    lebesgueFunction nodes.toNodeFamily t = (gapPolynomial nodes g).eval t := by
  rw [lebesgueFunction, gapPolynomial_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact abs_lagrangeFundamental_eq_gapCoefficient_mul nodes g k ht
lemma one_lt_eval_gapPolynomial_of_mem_openGap {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ openGap nodes g) :
    1 < (gapPolynomial nodes g).eval t := by
  obtain ⟨k, hcoeff⟩ := exists_gapCoefficient_eq_neg_one hn g
  let f : Fin n → ℝ := fun j => lagrangeFundamental nodes.toNodeFamily j t
  have hfk : f k < 0 := by
    have hpos := gapCoefficient_mul_lagrangeFundamental_pos nodes g k ht
    rw [hcoeff, neg_one_mul] at hpos
    exact neg_pos.mp hpos
  have hsum : ∑ j : Fin n, f j = 1 := by
    exact sum_lagrangeFundamental_eq_one nodes (by omega) t
  have hsumErase : ∑ j ∈ Finset.univ.erase k, f j = 1 - f k := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ k)] at hsum
    linarith
  have habsErase :
      |∑ j ∈ Finset.univ.erase k, f j| ≤
        ∑ j ∈ Finset.univ.erase k, |f j| :=
    Finset.abs_sum_le_sum_abs f (Finset.univ.erase k)
  have hlower : 1 - 2 * f k ≤ lebesgueFunction nodes.toNodeFamily t := by
    rw [lebesgueFunction, ← Finset.add_sum_erase Finset.univ
      (fun j => |f j|) (Finset.mem_univ k)]
    calc
      1 - 2 * f k = |f k| + |∑ j ∈ Finset.univ.erase k, f j| := by
        rw [abs_of_neg hfk, hsumErase, abs_of_pos (by linarith)]
        ring
      _ ≤ |f k| + ∑ j ∈ Finset.univ.erase k, |f j| :=
        add_le_add (le_refl _) habsErase
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g
    ⟨ht.1.le, ht.2.le⟩]
  linarith
def gapHeight {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  lebesgueOn nodes.toNodeFamily
    (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))
lemma exists_gapHeight_eq_eval_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    ∃ t ∈ closedGap nodes g,
      gapHeight nodes g = (gapPolynomial nodes g).eval t ∧
        ∀ u ∈ closedGap nodes g,
          (gapPolynomial nodes g).eval u ≤ (gapPolynomial nodes g).eval t := by
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
    (gap_left_lt_right nodes g).le
  refine ⟨t, ht, ?_, ?_⟩
  · rw [gapHeight, heq, ← lebesgueFunction_eq_eval_gapPolynomial nodes g ht]
  · intro u hu
    rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g hu,
      ← lebesgueFunction_eq_eval_gapPolynomial nodes g ht]
    exact hmax u hu
end
end Randy1153
namespace Randy1153.DeBoorPinkus
open Polynomial
open scoped Topology
noncomputable section
def gapArgmax {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  Classical.choose (exists_gapHeight_eq_eval_gapPolynomial nodes g)
lemma gapArgmax_mem_closedGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ closedGap nodes g :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).1
lemma gapHeight_eq_eval_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    gapHeight nodes g = (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).2.1
lemma gapPolynomial_eval_le_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ closedGap nodes g) :
    (gapPolynomial nodes g).eval t ≤
      (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).2.2 t ht
lemma gapArgmax_mem_openGap {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n)
    (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ openGap nodes g := by
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  have htgt : 1 < (gapPolynomial nodes g).eval t :=
    one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht
  have hmaxgt : 1 < (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
    htgt.trans_le (gapPolynomial_eval_le_gapArgmax nodes g ⟨ht.1.le, ht.2.le⟩)
  have hclosed := gapArgmax_mem_closedGap nodes g
  refine ⟨lt_of_le_of_ne hclosed.1 ?_, lt_of_le_of_ne hclosed.2 ?_⟩
  · intro heq
    rw [← heq, gapPolynomial_eval_left] at hmaxgt
    exact (lt_irrefl 1) hmaxgt
  · intro heq
    rw [heq, gapPolynomial_eval_right] at hmaxgt
    exact (lt_irrefl 1) hmaxgt
lemma gapPolynomial_derivative_eval_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.eval (gapArgmax nodes g) = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  have hopen := gapArgmax_mem_openGap nodes hn g
  have hmaxOn : IsMaxOn (fun t : ℝ => p.eval t) (closedGap nodes g)
      (gapArgmax nodes g) := by
    intro t ht
    exact gapPolynomial_eval_le_gapArgmax nodes g ht
  have hlocal : IsLocalMax (fun t : ℝ => p.eval t) (gapArgmax nodes g) :=
    hmaxOn.isLocalMax (Icc_mem_nhds hopen.1 hopen.2)
  simpa only [p] using hlocal.hasDerivAt_eq_zero (p.hasDerivAt (gapArgmax nodes g))
lemma gapPolynomial_derivative_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative ≠ 0 := by
  intro hderiv
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  have htgt := one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hderiv
  have heq := congrArg (Polynomial.eval t) hconst
  have heqLeft := congrArg
    (Polynomial.eval (nodes.point (gapLeftIndex g))) hconst
  simp only [Polynomial.eval_C] at heq heqLeft
  rw [gapPolynomial_eval_left] at heqLeft
  linarith
lemma gapArgmax_mem_derivative_roots {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ (gapPolynomial nodes g).derivative.roots := by
  rw [Polynomial.mem_roots (gapPolynomial_derivative_ne_zero nodes hn g)]
  exact gapPolynomial_derivative_eval_gapArgmax nodes hn g
private lemma gapPolynomial_ne_zero_critical {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapPolynomial nodes g ≠ 0 := by
  intro hzero
  have h := gapPolynomial_eval_left nodes g
  rw [hzero, Polynomial.eval_zero] at h
  norm_num at h
private abbrev CriticalOtherGapIndex {n : ℕ} (g : Fin (n - 1)) :=
  {h : Fin (n - 1) // h ≠ g}
@[simp]
private lemma card_criticalOtherGapIndex {n : ℕ} (g : Fin (n - 1)) :
    Fintype.card (CriticalOtherGapIndex g) = n - 2 := by
  classical
  change Fintype.card {h : Fin (n - 1) // ¬h = g} = n - 2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega
private theorem exists_criticalOtherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    ∃ r ∈ openGap nodes h, (gapPolynomial nodes g).eval r = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  let a : ℝ := nodes.point (gapLeftIndex h)
  let b : ℝ := nodes.point (gapRightIndex h)
  have hab : a ≤ b := (gap_left_lt_right nodes h).le
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuous.continuousOn
  have ha : p.eval a = gapCoefficient g (gapLeftIndex h) := by
    exact gapPolynomial_eval_node nodes g (gapLeftIndex h)
  have hb : p.eval b = -gapCoefficient g (gapLeftIndex h) := by
    simp only [p, b]
    rw [gapPolynomial_eval_node, gapCoefficient_right_eq_neg_left_of_ne g h hhg]
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex h) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz
private def criticalOtherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : CriticalOtherGapIndex g) : ℝ :=
  Classical.choose (exists_criticalOtherGapRoot nodes g h.1 h.property)
private lemma criticalOtherGapRoot_mem_openGap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : CriticalOtherGapIndex g) :
    criticalOtherGapRoot nodes g h ∈ openGap nodes h.1 :=
  (Classical.choose_spec
    (exists_criticalOtherGapRoot nodes g h.1 h.property)).1
private lemma gapPolynomial_eval_criticalOtherGapRoot {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : CriticalOtherGapIndex g) :
    (gapPolynomial nodes g).eval (criticalOtherGapRoot nodes g h) = 0 :=
  (Classical.choose_spec
    (exists_criticalOtherGapRoot nodes g h.1 h.property)).2
private lemma criticalOtherGapRoot_strictMono {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    StrictMono (criticalOtherGapRoot nodes g) := by
  intro h k hhk
  have hindex : gapRightIndex h.1 ≤ gapLeftIndex k.1 := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [gapRightIndex_val, gapLeftIndex_val]
    have hval : h.1.val < k.1.val := hhk
    omega
  calc
    criticalOtherGapRoot nodes g h < nodes.point (gapRightIndex h.1) :=
      (criticalOtherGapRoot_mem_openGap nodes g h).2
    _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
    _ < criticalOtherGapRoot nodes g k :=
      (criticalOtherGapRoot_mem_openGap nodes g k).1
theorem gapPolynomial_splits {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : (gapPolynomial nodes g).Splits := by
  classical
  let p : ℝ[X] := gapPolynomial nodes g
  let root : CriticalOtherGapIndex g → ℝ := criticalOtherGapRoot nodes g
  let D : ℝ[X] := ∏ h : CriticalOtherGapIndex g, (X - C (root h))
  have hrootInjective : Function.Injective root :=
    (criticalOtherGapRoot_strictMono nodes g).injective
  have hDvd : D ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro h
      rw [Polynomial.dvd_iff_isRoot]
      exact gapPolynomial_eval_criticalOtherGapRoot nodes g h
  obtain ⟨q, hq⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).Monic
    exact monic_prod_of_monic _ _ fun h _hh => monic_X_sub_C (root h)
  have hDsplits : D.Splits := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).Splits
    exact Polynomial.Splits.prod fun h _hh => Polynomial.Splits.X_sub_C (root h)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hp : p ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hqne : q ≠ 0 := by
    intro hzero
    apply hp
    rw [hzero, mul_zero] at hq
    exact hq
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_criticalOtherGapIndex]
  have hpdegree : p.natDegree ≤ n - 1 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  have hqdegree : q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hDne hqne, hDdegree] at hnat
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  change p.Splits
  rw [hq]
  exact hDsplits.mul (Polynomial.Splits.of_natDegree_le_one hqdegree)
private lemma gapPolynomial_root_not_mem_closedGap {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hr : r ∈ (gapPolynomial nodes g).roots) :
    r ∉ closedGap nodes g := by
  intro hrclosed
  have hroot : (gapPolynomial nodes g).eval r = 0 := by
    rw [← Polynomial.IsRoot]
    exact (Polynomial.mem_roots (gapPolynomial_ne_zero_critical nodes g)).mp hr
  by_cases hleft : r = nodes.point (gapLeftIndex g)
  · rw [hleft, gapPolynomial_eval_left] at hroot
    norm_num at hroot
  by_cases hright : r = nodes.point (gapRightIndex g)
  · rw [hright, gapPolynomial_eval_right] at hroot
    norm_num at hroot
  have hopen : r ∈ openGap nodes g :=
    ⟨lt_of_le_of_ne hrclosed.1 (Ne.symm hleft),
      lt_of_le_of_ne hrclosed.2 hright⟩
  have hpos := one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g hopen
  linarith
private lemma reciprocal_sub_strictAnti {a b x y r : ℝ}
    (hxy : x < y) (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hr : r < a ∨ b < r) :
    1 / (y - r) < 1 / (x - r) := by
  have hxr : x - r ≠ 0 := by
    rcases hr with hr | hr
    · exact ne_of_gt (sub_pos.mpr (hr.trans hx.1))
    · exact ne_of_lt (sub_neg.mpr (hx.2.trans hr))
  have hyr : y - r ≠ 0 := by
    rcases hr with hr | hr
    · exact ne_of_gt (sub_pos.mpr (hr.trans (hx.1.trans hxy)))
    · exact ne_of_lt (sub_neg.mpr (hy.2.trans hr))
  have hprod : 0 < (x - r) * (y - r) := by
    rcases hr with hr | hr
    · exact mul_pos (sub_pos.mpr (hr.trans hx.1))
        (sub_pos.mpr (hr.trans hy.1))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hx.2.trans hr))
        (sub_neg.mpr (hy.2.trans hr))
  rw [← sub_pos]
  rw [show 1 / (x - r) - 1 / (y - r) =
      (y - x) / ((x - r) * (y - r)) by field_simp; ring]
  exact div_pos (sub_pos.mpr hxy) hprod
private lemma hasDerivAt_reciprocal_sub (x r : ℝ) (hxr : x ≠ r) :
    HasDerivAt (fun y : ℝ => 1 / (y - r)) (-1 / (x - r) ^ 2) x := by
  have hne : x - r ≠ 0 := sub_ne_zero.mpr hxr
  simpa only [one_div, id_eq, sub_eq_add_neg, add_comm, Pi.inv_def] using
    ((hasDerivAt_id x).sub_const r).inv hne
private lemma hasDerivAt_rootReciprocalSum (roots : Multiset ℝ) (x : ℝ)
    (hx : ∀ r ∈ roots, x ≠ r) :
    HasDerivAt
      (fun y : ℝ => (roots.map fun r => 1 / (y - r)).sum)
      ((roots.map fun r => -1 / (x - r) ^ 2).sum) x := by
  induction roots using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | cons r roots ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (hasDerivAt_reciprocal_sub x r (hx r (by simp))).add
        (ih fun s hs => hx s (by simp [hs]))
theorem gapLogDerivative_strictAntiOn {n : ℕ} (nodes : OrderedNodes n)
    (hn : 4 ≤ n) (g : Fin (n - 1)) :
    StrictAntiOn
      (fun x => (gapPolynomial nodes g).derivative.eval x /
        (gapPolynomial nodes g).eval x)
      (openGap nodes g) := by
  intro x hx y hy hxy
  let p : ℝ[X] := gapPolynomial nodes g
  have hp : p ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hsplit : p.Splits := gapPolynomial_splits nodes g
  have hpx : p.eval x ≠ 0 := ne_of_gt
    (zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap nodes
      (by omega) g hx))
  have hpy : p.eval y ≠ 0 := ne_of_gt
    (zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap nodes
      (by omega) g hy))
  change p.derivative.eval y / p.eval y < p.derivative.eval x / p.eval x
  rw [hsplit.eval_derivative_div_eval_of_ne_zero hpx,
    hsplit.eval_derivative_div_eval_of_ne_zero hpy]
  apply Multiset.sum_lt_sum
  · intro r hr
    apply (reciprocal_sub_strictAnti hxy hx hy ?_).le
    have hrout := gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    simp only [closedGap, Set.mem_Icc, not_and_or, not_le] at hrout
    exact hrout
  · have hnat : p.natDegree ≠ 0 := by
      intro hzero
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hzero
      have hderiv : p.derivative = 0 := by rw [← hc]; simp
      exact (gapPolynomial_derivative_ne_zero nodes (by omega) g) hderiv
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero (hsplit.roots_ne_zero hnat)
    refine ⟨r, hr, reciprocal_sub_strictAnti hxy hx hy ?_⟩
    have hrout := gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    simp only [closedGap, Set.mem_Icc, not_and_or, not_le] at hrout
    exact hrout
lemma eq_gapArgmax_of_derivative_eval_eq_zero {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hrgap : r ∈ openGap nodes g)
    (hr : (gapPolynomial nodes g).derivative.eval r = 0) :
    r = gapArgmax nodes g := by
  have harggap := gapArgmax_mem_openGap nodes (by omega) g
  have harg := gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hanti := gapLogDerivative_strictAntiOn nodes hn g
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := hanti hrgap harggap hlt
    simp only [hr, harg, zero_div] at hstrict
    exact (lt_irrefl 0) hstrict
  · have hstrict := hanti harggap hrgap hgt
    simp only [hr, harg, zero_div] at hstrict
    exact (lt_irrefl 0) hstrict
lemma gapPolynomial_secondDerivative_eval_gapArgmax_neg {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.derivative.eval (gapArgmax nodes g) < 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  let τ : ℝ := gapArgmax nodes g
  have hτgap : τ ∈ openGap nodes g := gapArgmax_mem_openGap nodes (by omega) g
  have hpτpos : 0 < p.eval τ := zero_lt_one.trans
    (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hτgap)
  have hpτ : p.eval τ ≠ 0 := hpτpos.ne'
  have hcrit : p.derivative.eval τ = 0 := by
    exact gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hsplit : p.Splits := gapPolynomial_splits nodes g
  have hrootNe : ∀ r ∈ p.roots, τ ≠ r := by
    intro r hr heq
    apply gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    rw [← heq]
    exact gapArgmax_mem_closedGap nodes g
  have hsumDeriv := hasDerivAt_rootReciprocalSum p.roots τ hrootNe
  have hevent :
      (fun x : ℝ => p.derivative.eval x / p.eval x) =ᶠ[𝓝 τ]
        (fun x : ℝ => (p.roots.map fun r => 1 / (x - r)).sum) := by
    filter_upwards [Ioo_mem_nhds hτgap.1 hτgap.2] with x hx
    exact hsplit.eval_derivative_div_eval_of_ne_zero
      (ne_of_gt (zero_lt_one.trans
        (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hx)))
  have hquotDeriv : HasDerivAt
      (fun x : ℝ => p.derivative.eval x / p.eval x)
      (p.derivative.derivative.eval τ / p.eval τ) τ := by
    have hraw := (p.derivative.hasDerivAt τ).div (p.hasDerivAt τ) hpτ
    apply hraw.congr_deriv
    rw [hcrit]
    field_simp
    ring
  have hcoeff :
      p.derivative.derivative.eval τ / p.eval τ =
        (p.roots.map fun r => -1 / (τ - r) ^ 2).sum :=
    hquotDeriv.unique (hsumDeriv.congr_of_eventuallyEq hevent)
  have hroots : p.roots ≠ 0 := by
    have hnat : p.natDegree ≠ 0 := by
      intro hzero
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hzero
      have hderiv : p.derivative = 0 := by rw [← hc]; simp
      exact (gapPolynomial_derivative_ne_zero nodes (by omega) g) hderiv
    exact hsplit.roots_ne_zero hnat
  have hterm (r : ℝ) (hr : r ∈ p.roots) : -1 / (τ - r) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by norm_num)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr (hrootNe r hr)))
  have hsumneg : (p.roots.map fun r => -1 / (τ - r) ^ 2).sum < 0 := by
    have hlt : (p.roots.map fun r => -1 / (τ - r) ^ 2).sum <
        (p.roots.map fun _r => (0 : ℝ)).sum := by
      apply Multiset.sum_lt_sum
      · intro r hr
        exact (hterm r hr).le
      · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
        exact ⟨r, hr, hterm r hr⟩
    simpa using hlt
  have hratio : p.derivative.derivative.eval τ / p.eval τ < 0 := by
    rw [hcoeff]
    exact hsumneg
  rcases (div_neg_iff.mp hratio) with hbad | hneg
  · exact (not_lt_of_ge hpτpos.le hbad.2).elim
  · exact hneg.1
def gapDerivativeQuotient {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : ℝ[X] :=
  (gapPolynomial nodes g).derivative /ₘ (X - C (gapArgmax nodes g))
lemma X_sub_C_gapArgmax_mul_gapDerivativeQuotient {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (X - C (gapArgmax nodes g)) * gapDerivativeQuotient nodes g =
      (gapPolynomial nodes g).derivative := by
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (gapPolynomial_derivative_eval_gapArgmax nodes hn g)
lemma gapDerivativeQuotient_eval_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).eval (gapArgmax nodes g) =
      (gapPolynomial nodes g).derivative.derivative.eval (gapArgmax nodes g) := by
  have h := congrArg (Polynomial.eval (gapArgmax nodes g))
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      (gapPolynomial nodes g).derivative (gapArgmax nodes g))
  simpa [gapDerivativeQuotient] using h
lemma gapDerivativeQuotient_eval_gapArgmax_neg {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).eval (gapArgmax nodes g) < 0 := by
  rw [gapDerivativeQuotient_eval_gapArgmax]
  exact gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes hn g
lemma natDegree_gapDerivativeQuotient_le_sub_three {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).natDegree ≤ n - 3 := by
  have hp : gapPolynomial nodes g ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hpdegree : (gapPolynomial nodes g).natDegree ≤ n - 1 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  have hderivative :
      (gapPolynomial nodes g).derivative.natDegree ≤ n - 2 := by
    calc
      (gapPolynomial nodes g).derivative.natDegree ≤
          (gapPolynomial nodes g).natDegree - 1 :=
        Polynomial.natDegree_derivative_le _
      _ ≤ (n - 1) - 1 := Nat.sub_le_sub_right hpdegree 1
      _ = n - 2 := by omega
  rw [gapDerivativeQuotient,
    Polynomial.natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  calc
    (gapPolynomial nodes g).derivative.natDegree - 1 ≤ (n - 2) - 1 :=
      Nat.sub_le_sub_right hderivative 1
    _ = n - 3 := by omega
lemma natDegree_gapPolynomial_derivative_le_one_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) :
    (gapPolynomial nodes g).derivative.natDegree ≤ 1 := by
  have hp : gapPolynomial nodes g ≠ 0 := by
    intro hzero
    have h := gapPolynomial_eval_left nodes g
    rw [hzero, Polynomial.eval_zero] at h
    norm_num at h
  have hpdegree : (gapPolynomial nodes g).natDegree ≤ 2 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  exact (Polynomial.natDegree_derivative_le _).trans <| by omega
lemma eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) {r : ℝ}
    (hr : (gapPolynomial nodes g).derivative.eval r = 0) :
    r = gapArgmax nodes g := by
  let dp : ℝ[X] := (gapPolynomial nodes g).derivative
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero nodes (by norm_num) g
  have hrmem : r ∈ dp.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdp]
    exact hr
  have hamem : gapArgmax nodes g ∈ dp.roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact gapArgmax_mem_derivative_roots nodes (by norm_num) g
  by_contra hne
  have hpair : ({r, gapArgmax nodes g} : Finset ℝ) ⊆ dp.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hrmem
    · exact hamem
  have hcard : 2 ≤ dp.roots.toFinset.card := by
    have := Finset.card_le_card hpair
    simpa [hne] using this
  have hdegree : dp.roots.toFinset.card ≤ 1 :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' dp).trans
        (natDegree_gapPolynomial_derivative_le_one_of_three_nodes nodes g)
  omega
lemma gapPolynomial_eq_one_of_two_nodes (nodes : OrderedNodes 2) (g : Fin 1) :
    gapPolynomial nodes g = 1 := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  have hcoeff : (gapCoefficient (0 : Fin 1) : Fin 2 → ℝ) = 1 := by
    funext k
    fin_cases k <;> simp [gapCoefficient_of_le, gapCoefficient_of_lt]
  rw [gapPolynomial, hcoeff]
  exact Lagrange.interpolate_one nodes.injective.injOn
    ⟨(0 : Fin 2), Finset.mem_univ _⟩
@[simp]
lemma gapPolynomial_derivative_eq_zero_of_two_nodes (nodes : OrderedNodes 2)
    (g : Fin 1) :
    (gapPolynomial nodes g).derivative = 0 := by
  rw [gapPolynomial_eq_one_of_two_nodes]
  simp
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Polynomial
noncomputable section
lemma openGap_point_lt_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    {g h : Fin (n - 1)} (hgh : g < h) {x y : ℝ}
    (hx : x ∈ openGap nodes g) (hy : y ∈ openGap nodes h) :
    x < y := by
  have hindex : gapRightIndex g ≤ gapLeftIndex h := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [gapRightIndex_val, gapLeftIndex_val]
    omega
  calc
    x < nodes.point (gapRightIndex g) := hx.2
    _ ≤ nodes.point (gapLeftIndex h) := nodes.strictMono.monotone hindex
    _ < y := hy.1
abbrev OtherGapIndex {n : ℕ} (g : Fin (n - 1)) :=
  {h : Fin (n - 1) // h ≠ g}
@[simp]
lemma card_otherGapIndex {n : ℕ} (g : Fin (n - 1)) :
    Fintype.card (OtherGapIndex g) = n - 2 := by
  classical
  change Fintype.card {h : Fin (n - 1) // ¬h = g} = n - 2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Polynomial
open scoped BigOperators
noncomputable section
def gapPairParity {n : ℕ} (g h : Fin (n - 1)) : ℝ :=
  (-1 : ℝ) ^ (h.val - g.val)
lemma gapPairParity_eq_one_or_neg_one {n : ℕ} (g h : Fin (n - 1)) :
    gapPairParity g h = 1 ∨ gapPairParity g h = -1 := by
  rw [gapPairParity]
  generalize h.val - g.val = m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      rcases ih with ih | ih <;> simp [ih]
@[simp]
lemma sq_gapPairParity {n : ℕ} (g h : Fin (n - 1)) :
    gapPairParity g h ^ 2 = 1 := by
  rcases gapPairParity_eq_one_or_neg_one g h with hp | hp <;> simp [hp]
lemma gapPairParity_mul_gapCoefficient {n : ℕ} (g h : Fin (n - 1))
    (hgh : g < h) (k : Fin n) :
    gapPairParity g h * gapCoefficient h k =
      if k.val ≤ g.val ∨ h.val < k.val then
        gapCoefficient g k
      else
        -gapCoefficient g k := by
  by_cases hkg : k.val ≤ g.val
  · have hkh : k.val ≤ h.val := hkg.trans hgh.le
    rw [if_pos (Or.inl hkg), gapPairParity, gapCoefficient_of_le g k hkg,
      gapCoefficient_of_le h k hkh]
    have hexp : (h.val - g.val) + (h.val - k.val) =
        (g.val - k.val) + 2 * (h.val - g.val) := by omega
    rw [← pow_add, hexp, pow_add, pow_mul]
    norm_num
  · have hgk : g.val < k.val := Nat.lt_of_not_ge hkg
    by_cases hhk : h.val < k.val
    · rw [if_pos (Or.inr hhk), gapPairParity,
        gapCoefficient_of_lt g k hgk, gapCoefficient_of_lt h k hhk]
      have hexp : (h.val - g.val) + (k.val - h.val - 1) =
          k.val - g.val - 1 := by omega
      rw [← pow_add, hexp]
    · have hkle : k.val ≤ h.val := Nat.le_of_not_gt hhk
      rw [if_neg (by simp [hkg, hhk]), gapPairParity,
        gapCoefficient_of_lt g k hgk, gapCoefficient_of_le h k hkle]
      have hexp : (h.val - g.val) + (h.val - k.val) =
          (k.val - g.val - 1) + (2 * (h.val - k.val) + 1) := by omega
      rw [← pow_add, hexp, pow_add]
      have hodd : (-1 : ℝ) ^ (2 * (h.val - k.val) + 1) = -1 := by
        rw [pow_add, pow_mul]
        norm_num
      rw [hodd]
      ring
def gapDifferenceCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : ℝ[X] :=
  gapPolynomial nodes g - C (gapPairParity g h) * gapPolynomial nodes h
def gapSumCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : ℝ[X] :=
  gapPolynomial nodes g + C (gapPairParity g h) * gapPolynomial nodes h
lemma gapDifferenceCombination_eval_node {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (k : Fin n) :
    (gapDifferenceCombination nodes g h).eval (nodes.point k) =
      if k.val ≤ g.val ∨ h.val < k.val then 0
      else 2 * gapCoefficient g k := by
  rw [gapDifferenceCombination, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapPairParity_mul_gapCoefficient g h hgh k]
  split_ifs <;> ring
lemma gapSumCombination_eval_node {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (k : Fin n) :
    (gapSumCombination nodes g h).eval (nodes.point k) =
      if k.val ≤ g.val ∨ h.val < k.val then 2 * gapCoefficient g k
      else 0 := by
  rw [gapSumCombination, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapPairParity_mul_gapCoefficient g h hgh k]
  split_ifs <;> ring
lemma degree_gapDifferenceCombination_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapDifferenceCombination nodes g h).degree ≤ (n - 1 : ℕ) := by
  apply (degree_sub_le _ _).trans
  apply max_le
  · exact degree_gapPolynomial_le nodes g
  · exact (degree_mul_le _ _).trans <| by
      simpa using add_le_add degree_C_le (degree_gapPolynomial_le nodes h)
lemma degree_gapSumCombination_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapSumCombination nodes g h).degree ≤ (n - 1 : ℕ) := by
  apply (degree_add_le _ _).trans
  apply max_le
  · exact degree_gapPolynomial_le nodes g
  · exact (degree_mul_le _ _).trans <| by
      simpa using add_le_add degree_C_le (degree_gapPolynomial_le nodes h)
lemma gapDifferenceCombination_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    gapDifferenceCombination nodes g h ≠ 0 := by
  let k : Fin n := gapRightIndex g
  have hinside : ¬(k.val ≤ g.val ∨ h.val < k.val) := by
    simp only [k, gapRightIndex_val]
    omega
  have heval := gapDifferenceCombination_eval_node nodes g h hgh k
  rw [if_neg hinside] at heval
  intro hzero
  rw [hzero, Polynomial.eval_zero] at heval
  have hcoeff := gapCoefficient_ne_zero g k
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hcoeff) heval.symm
theorem exists_gapDifferenceCombination_root_in_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1))
    (hgh : g < h) (hgq : g < q) (hqh : q < h) :
    ∃ r ∈ openGap nodes q, (gapDifferenceCombination nodes g h).eval r = 0 := by
  let P : ℝ[X] := gapDifferenceCombination nodes g h
  let a : ℝ := nodes.point (gapLeftIndex q)
  let b : ℝ := nodes.point (gapRightIndex q)
  have hleftInside : ¬((gapLeftIndex q).val ≤ g.val ∨
      h.val < (gapLeftIndex q).val) := by
    simp only [gapLeftIndex_val]
    omega
  have hrightInside : ¬((gapRightIndex q).val ≤ g.val ∨
      h.val < (gapRightIndex q).val) := by
    simp only [gapRightIndex_val]
    omega
  have ha : P.eval a = 2 * gapCoefficient g (gapLeftIndex q) := by
    simpa only [P, a, if_neg hleftInside] using
      gapDifferenceCombination_eval_node nodes g h hgh (gapLeftIndex q)
  have hb : P.eval b = -(2 * gapCoefficient g (gapLeftIndex q)) := by
    have hqg : q ≠ g := ne_of_gt hgq
    calc
      P.eval b = 2 * gapCoefficient g (gapRightIndex q) := by
        simpa only [P, b, if_neg hrightInside] using
          gapDifferenceCombination_eval_node nodes g h hgh (gapRightIndex q)
      _ = -(2 * gapCoefficient g (gapLeftIndex q)) := by
        rw [gapCoefficient_right_eq_neg_left_of_ne g q hqg]
        ring
  have hab : a ≤ b := (gap_left_lt_right nodes q).le
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) :=
    P.continuous.continuousOn
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex q) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz
def gapDifferenceRootPoint {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1)) : ℝ :=
  if hqg : q.val ≤ g.val then
    nodes.point (gapLeftIndex q)
  else if hhq : h.val ≤ q.val then
    nodes.point (gapRightIndex q)
  else
    Classical.choose (exists_gapDifferenceCombination_root_in_middleGap
      nodes g h q hgh (by omega) (by omega))
lemma gapDifferenceRootPoint_eq_left_of_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hqg : q.val ≤ g.val) :
    gapDifferenceRootPoint nodes g h hgh q = nodes.point (gapLeftIndex q) := by
  simp [gapDifferenceRootPoint, hqg]
lemma gapDifferenceRootPoint_eq_right_of_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hhq : h.val ≤ q.val) :
    gapDifferenceRootPoint nodes g h hgh q = nodes.point (gapRightIndex q) := by
  have hnqg : ¬q.val ≤ g.val := by omega
  simp [gapDifferenceRootPoint, hnqg, hhq]
lemma gapDifferenceRootPoint_mem_openGap_of_between {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) (hgq : g < q) (hqh : q < h) :
    gapDifferenceRootPoint nodes g h hgh q ∈ openGap nodes q := by
  have hnqg : ¬q.val ≤ g.val := by omega
  have hnhq : ¬h.val ≤ q.val := by omega
  simp only [gapDifferenceRootPoint, dif_neg hnqg, dif_neg hnhq]
  exact (Classical.choose_spec (exists_gapDifferenceCombination_root_in_middleGap
    nodes g h q hgh hgq hqh)).1
lemma gapDifferenceCombination_eval_rootPoint {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) :
    (gapDifferenceCombination nodes g h).eval
      (gapDifferenceRootPoint nodes g h hgh q) = 0 := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg,
      gapDifferenceCombination_eval_node nodes g h hgh]
    simp [hqg]
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq,
        gapDifferenceCombination_eval_node nodes g h hgh]
      simp [hhq]
    · have hgq : g < q := by exact Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
      have hqh : q < h := by exact Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
      simp only [gapDifferenceRootPoint, dif_neg hqg, dif_neg hhq]
      exact (Classical.choose_spec (exists_gapDifferenceCombination_root_in_middleGap
        nodes g h q hgh hgq hqh)).2
lemma gapDifferenceRootPoint_mem_closedGap {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1)) :
    gapDifferenceRootPoint nodes g h hgh q ∈ closedGap nodes q := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg]
    exact ⟨le_rfl, (gap_left_lt_right nodes q).le⟩
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq]
      exact ⟨(gap_left_lt_right nodes q).le, le_rfl⟩
    · have hgq : g < q := Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
      have hqh : q < h := Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
      have hopen := gapDifferenceRootPoint_mem_openGap_of_between
        nodes g h hgh q hgq hqh
      exact ⟨hopen.1.le, hopen.2.le⟩
lemma gapDifferenceRootPoint_lt_right_of_lt {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hqh : q < h) :
    gapDifferenceRootPoint nodes g h hgh q < nodes.point (gapRightIndex q) := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg]
    exact gap_left_lt_right nodes q
  · have hgq : g < q := Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
    exact (gapDifferenceRootPoint_mem_openGap_of_between nodes g h hgh q hgq hqh).2
lemma left_lt_gapDifferenceRootPoint_of_lt {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hgq : g < q) :
    nodes.point (gapLeftIndex q) < gapDifferenceRootPoint nodes g h hgh q := by
  by_cases hhq : h.val ≤ q.val
  · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq]
    exact gap_left_lt_right nodes q
  · have hqh : q < h := Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
    exact (gapDifferenceRootPoint_mem_openGap_of_between nodes g h hgh q hgq hqh).1
lemma gapDifferenceRootPoint_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictMono (gapDifferenceRootPoint nodes g h hgh) := by
  intro q r hqr
  by_cases hqh : q < h
  · calc
      gapDifferenceRootPoint nodes g h hgh q < nodes.point (gapRightIndex q) :=
        gapDifferenceRootPoint_lt_right_of_lt nodes g h hgh q hqh
      _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ ≤ gapDifferenceRootPoint nodes g h hgh r :=
        (gapDifferenceRootPoint_mem_closedGap nodes g h hgh r).1
  · have hhq : h ≤ q := le_of_not_gt hqh
    have hgr : g < r := hgh.trans_le (hhq.trans hqr.le)
    calc
      gapDifferenceRootPoint nodes g h hgh q ≤ nodes.point (gapRightIndex q) :=
        (gapDifferenceRootPoint_mem_closedGap nodes g h hgh q).2
      _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ < gapDifferenceRootPoint nodes g h hgh r :=
        left_lt_gapDifferenceRootPoint_of_lt nodes g h hgh r hgr
lemma gapSumCombination_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    gapSumCombination nodes g h ≠ 0 := by
  let k : Fin n := gapLeftIndex g
  have houtside : k.val ≤ g.val ∨ h.val < k.val := by
    exact Or.inl (by simp only [k, gapLeftIndex_val]; exact le_rfl)
  have heval := gapSumCombination_eval_node nodes g h hgh k
  rw [if_pos houtside] at heval
  intro hzero
  rw [hzero, Polynomial.eval_zero] at heval
  have hcoeff := gapCoefficient_ne_zero g k
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hcoeff) heval.symm
theorem exists_gapSumCombination_root_in_outerGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1))
    (hgh : g < h) (hq : q < g ∨ h < q) :
    ∃ r ∈ openGap nodes q, (gapSumCombination nodes g h).eval r = 0 := by
  let P : ℝ[X] := gapSumCombination nodes g h
  let a : ℝ := nodes.point (gapLeftIndex q)
  let b : ℝ := nodes.point (gapRightIndex q)
  have hleftOutside : (gapLeftIndex q).val ≤ g.val ∨
      h.val < (gapLeftIndex q).val := by
    rcases hq with hqg | hhq
    · exact Or.inl (by simp only [gapLeftIndex_val]; omega)
    · exact Or.inr (by simp only [gapLeftIndex_val]; omega)
  have hrightOutside : (gapRightIndex q).val ≤ g.val ∨
      h.val < (gapRightIndex q).val := by
    rcases hq with hqg | hhq
    · exact Or.inl (by simp only [gapRightIndex_val]; omega)
    · exact Or.inr (by simp only [gapRightIndex_val]; omega)
  have ha : P.eval a = 2 * gapCoefficient g (gapLeftIndex q) := by
    simpa only [P, a, if_pos hleftOutside] using
      gapSumCombination_eval_node nodes g h hgh (gapLeftIndex q)
  have hb : P.eval b = -(2 * gapCoefficient g (gapLeftIndex q)) := by
    have hqg : q ≠ g := by rcases hq with hqg | hhq <;> omega
    calc
      P.eval b = 2 * gapCoefficient g (gapRightIndex q) := by
        simpa only [P, b, if_pos hrightOutside] using
          gapSumCombination_eval_node nodes g h hgh (gapRightIndex q)
      _ = -(2 * gapCoefficient g (gapLeftIndex q)) := by
        rw [gapCoefficient_right_eq_neg_left_of_ne g q hqg]
        ring
  have hab : a ≤ b := (gap_left_lt_right nodes q).le
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) :=
    P.continuous.continuousOn
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex q) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz
def gapSumRootPoint {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : OtherGapIndex h) : ℝ :=
  if hqg : q.1 < g then
    Classical.choose (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))
  else if hhq : h < q.1 then
    Classical.choose (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inr hhq))
  else
    nodes.point (gapRightIndex q.1)
lemma gapSumRootPoint_mem_openGap_of_outer {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hq : q.1 < g ∨ h < q.1) :
    gapSumRootPoint nodes g h hgh q ∈ openGap nodes q.1 := by
  rcases hq with hqg | hhq
  · simp only [gapSumRootPoint, dif_pos hqg]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))).1
  · have hnqg : ¬q.1 < g := by omega
    simp only [gapSumRootPoint, dif_neg hnqg, dif_pos hhq]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inr hhq))).1
lemma gapSumRootPoint_eq_right_of_between {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hgq : g ≤ q.1) (hqh : q.1 < h) :
    gapSumRootPoint nodes g h hgh q = nodes.point (gapRightIndex q.1) := by
  have hnqg : ¬q.1 < g := not_lt.mpr hgq
  have hnhq : ¬h < q.1 := not_lt.mpr hqh.le
  simp [gapSumRootPoint, hnqg, hnhq]
lemma gapSumCombination_eval_rootPoint {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) :
    (gapSumCombination nodes g h).eval
      (gapSumRootPoint nodes g h hgh q) = 0 := by
  by_cases hqg : q.1 < g
  · simp only [gapSumRootPoint, dif_pos hqg]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))).2
  · by_cases hhq : h < q.1
    · simp only [gapSumRootPoint, dif_neg hqg, dif_pos hhq]
      exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
        nodes g h q.1 hgh (Or.inr hhq))).2
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      have h1 : g.val ≤ (q.1 : Fin (n - 1)).val := hgq
      have h2 : (q.1 : Fin (n - 1)).val < h.val := hqh
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh,
        gapSumCombination_eval_node nodes g h hgh, if_neg]
      simp only [gapRightIndex_val, not_or, not_le, not_lt]
      constructor <;> omega
lemma gapSumRootPoint_mem_closedGap {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : OtherGapIndex h) :
    gapSumRootPoint nodes g h hgh q ∈ closedGap nodes q.1 := by
  by_cases hqg : q.1 < g
  · have hopen := gapSumRootPoint_mem_openGap_of_outer
      nodes g h hgh q (Or.inl hqg)
    exact ⟨hopen.1.le, hopen.2.le⟩
  · by_cases hhq : h < q.1
    · have hopen := gapSumRootPoint_mem_openGap_of_outer
        nodes g h hgh q (Or.inr hhq)
      exact ⟨hopen.1.le, hopen.2.le⟩
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
      exact ⟨(gap_left_lt_right nodes q.1).le, le_rfl⟩
lemma gapSumRootPoint_lt_right_of_outer {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hq : q.1 < g ∨ h < q.1) :
    gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
  (gapSumRootPoint_mem_openGap_of_outer nodes g h hgh q hq).2
lemma left_lt_gapSumRootPoint_of_g_le {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hgq : g ≤ q.1) :
    nodes.point (gapLeftIndex q.1) < gapSumRootPoint nodes g h hgh q := by
  by_cases hhq : h < q.1
  · exact (gapSumRootPoint_mem_openGap_of_outer
      nodes g h hgh q (Or.inr hhq)).1
  · have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
    rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
    exact gap_left_lt_right nodes q.1
lemma gapSumRootPoint_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictMono (gapSumRootPoint nodes g h hgh) := by
  intro q r hqr
  have hqrval : q.1 < r.1 := hqr
  by_cases hqg : q.1 < g
  · calc
      gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
        gapSumRootPoint_lt_right_of_outer nodes g h hgh q (Or.inl hqg)
      _ ≤ nodes.point (gapLeftIndex r.1) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ ≤ gapSumRootPoint nodes g h hgh r :=
        (gapSumRootPoint_mem_closedGap nodes g h hgh r).1
  · by_cases hhq : h < q.1
    · calc
        gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
          gapSumRootPoint_lt_right_of_outer nodes g h hgh q (Or.inr hhq)
        _ ≤ nodes.point (gapLeftIndex r.1) := nodes.strictMono.monotone <| by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        _ ≤ gapSumRootPoint nodes g h hgh r :=
          (gapSumRootPoint_mem_closedGap nodes g h hgh r).1
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      have hgr : g ≤ r.1 := hgq.trans hqrval.le
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
      calc
        nodes.point (gapRightIndex q.1) ≤ nodes.point (gapLeftIndex r.1) :=
          nodes.strictMono.monotone <| by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val, gapLeftIndex_val]
            omega
        _ < gapSumRootPoint nodes g h hgh r :=
          left_lt_gapSumRootPoint_of_g_le nodes g h hgh r hgr
lemma natDegree_gapSumCombination_le_sub_one {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    (gapSumCombination nodes g h).natDegree ≤ n - 1 := by
  have hdegree := degree_gapSumCombination_le nodes g h
  rw [Polynomial.degree_eq_natDegree
    (gapSumCombination_ne_zero nodes g h hgh)] at hdegree
  exact_mod_cast hdegree
private lemma neg_one_pow_card_filter_mul_prod_pos {α : Type*}
    [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hneg : ∀ x ∈ s, p x → f x < 0)
    (hpos : ∀ x ∈ s, ¬p x → 0 < f x) :
    0 < (-1 : ℝ) ^ (s.filter p).card * ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have ih' := ih (fun y hy => hneg y (Finset.mem_insert_of_mem hy))
        (fun y hy => hpos y (Finset.mem_insert_of_mem hy))
      by_cases hpx : p x
      · have hfx : f x < 0 := hneg x (Finset.mem_insert_self x s) hpx
        have hxfilter : x ∉ s.filter p := by simp [hxs]
        rw [Finset.filter_insert, if_pos hpx,
          Finset.card_insert_of_notMem hxfilter, pow_succ,
          Finset.prod_insert hxs]
        nlinarith
      · have hfx : 0 < f x := hpos x (Finset.mem_insert_self x s) hpx
        rw [Finset.filter_insert, if_neg hpx, Finset.prod_insert hxs]
        calc
          0 < ((-1 : ℝ) ^ (s.filter p).card * ∏ y ∈ s, f y) * f x :=
            mul_pos ih' hfx
          _ = (-1 : ℝ) ^ (s.filter p).card * (f x * ∏ y ∈ s, f y) := by ring
private lemma card_filter_middle_otherGapIndex {n : ℕ}
    (g h : Fin (n - 1)) :
    ((Finset.univ : Finset (OtherGapIndex h)).filter
      (fun q => g ≤ q.1 ∧ q.1 < h)).card = h.val - g.val := by
  let S := (Finset.univ : Finset (OtherGapIndex h)).filter
    (fun q => g ≤ q.1 ∧ q.1 < h)
  have himage : S.image (fun q => q.1) = Finset.Ico g h := by
    ext q
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨r, ⟨hgr, hrh⟩, rfl⟩
      exact ⟨hgr, hrh⟩
    · intro hq
      exact ⟨⟨q, ne_of_lt hq.2⟩, ⟨hq.1, hq.2⟩, rfl⟩
  calc
    S.card = (S.image (fun q => q.1)).card := by
      rw [Finset.card_image_of_injective S Subtype.val_injective]
    _ = (Finset.Ico g h).card := congrArg Finset.card himage
    _ = h.val - g.val := by simp
private lemma eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos
    (Q : ℝ[X]) {a b x : ℝ} (hdegree : Q.natDegree ≤ 1)
    (hprod : 0 < Q.eval a * Q.eval b) (hx : x ∈ Set.Ioo a b) :
    Q.eval x ≠ 0 := by
  intro hxzero
  have hxroot : Q.IsRoot x := hxzero
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hxroot
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hprod
    norm_num at hprod
  have hRne : R ≠ 0 := by
    intro hzero
    apply hQne
    rw [hzero, mul_zero] at hR
    exact hR
  have hRdegree : R.natDegree = 0 := by
    have hnat := congrArg Polynomial.natDegree hR
    rw [Polynomial.natDegree_mul (X_sub_C_ne_zero x) hRne,
      natDegree_X_sub_C] at hnat
    omega
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hRdegree
  have hc : c ≠ 0 := by
    intro hc
    apply hQne
    simpa [hc] using hR
  have hQprodNeg : Q.eval a * Q.eval b < 0 := by
    rw [hR]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    calc
      (a - x) * c * ((b - x) * c) =
          ((a - x) * (b - x)) * c ^ 2 := by ring
      _ < 0 := mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (sub_neg.mpr hx.1) (sub_pos.mpr hx.2))
        (sq_pos_of_ne_zero hc)
  exact hprod.not_gt hQprodNeg
private lemma eval_mul_eval_pos_of_no_root_between (P : ℝ[X])
    {a b : ℝ} (hab : a < b) (ha : P.eval a ≠ 0) (hb : P.eval b ≠ 0)
    (hroot : ∀ {x : ℝ}, x ∈ Set.Ioo a b → ¬P.IsRoot x) :
    0 < P.eval a * P.eval b := by
  have hprodne : P.eval a * P.eval b ≠ 0 := mul_ne_zero ha hb
  apply lt_of_le_of_ne (le_of_not_gt fun hneg => ?_) hprodne.symm
  rcases mul_neg_iff.mp hneg with hsign | hsign
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) :=
      ⟨hsign.2, hsign.1⟩
    obtain ⟨x, hx, hxzero⟩ := intermediate_value_Ioo' hab.le
      P.continuous.continuousOn hz
    exact hroot hx hxzero
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := hsign
    obtain ⟨x, hx, hxzero⟩ := intermediate_value_Ioo hab.le
      P.continuous.continuousOn hz
    exact hroot hx hxzero
def gapSumRootProduct {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : ℝ[X] :=
  ∏ k : OtherGapIndex h, (X - C (gapSumRootPoint nodes g h hgh k))
structure GapSumFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) where
  quotient : ℝ[X]
  factor : gapSumCombination nodes g h =
    gapSumRootProduct nodes g h hgh * quotient
  quotient_ne_zero : quotient ≠ 0
  quotient_natDegree_le_one : quotient.natDegree ≤ 1
  quotient_endpoint_product_pos :
    0 < quotient.eval (nodes.point (gapLeftIndex g)) *
      quotient.eval (nodes.point (gapRightIndex h))
private theorem exists_gapSumFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    Nonempty (GapSumFactorData nodes g h hgh) := by
  classical
  let P : ℝ[X] := gapSumCombination nodes g h
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let D : ℝ[X] := gapSumRootProduct nodes g h hgh
  have hP : P ≠ 0 := gapSumCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapSumRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro k
      rw [Polynomial.dvd_iff_isRoot]
      exact gapSumCombination_eval_rootPoint nodes g h hgh k
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (root k)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_otherGapIndex]
  have hQdegree : Q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      simpa only [P] using natDegree_gapSumCombination_le_sub_one nodes g h hgh
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (b - root k)
  let middle : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < h
  have hpairNeg : ∀ k : OtherGapIndex h, middle k → pairValue k < 0 := by
    intro k hk
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk.2
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootb : root k < b := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapRightIndex_val]
      omega
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootb)
  have hpairPos : ∀ k : OtherGapIndex h, ¬middle k → 0 < pairValue k := by
    intro k hk
    have hkouter : k.1 < g ∨ h < k.1 := by
      by_cases hkg : k.1 < g
      · exact Or.inl hkg
      · right
        have hgk : g ≤ k.1 := le_of_not_gt hkg
        have hnotlt : ¬k.1 < h := fun hlt => hk ⟨hgk, hlt⟩
        exact lt_of_le_of_ne (le_of_not_gt hnotlt) k.property.symm
    rcases hkouter with hkg | hhk
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hab))
    · have hbroot : b < root k := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inr hhk)
        have hindex : gapRightIndex h ≤ gapLeftIndex k.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          b = nodes.point (gapRightIndex h) := rfl
          _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
          _ < root k := by simpa only [root] using hmem.1
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans hbroot))
        (sub_neg.mpr hbroot)
  have hpairProduct :
      0 < gapPairParity g h * ∏ k : OtherGapIndex h, pairValue k := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) middle pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_middle_otherGapIndex g h] at hsign
    simpa [gapPairParity] using hsign
  have hDevalProduct : 0 < gapPairParity g h * (D.eval a * D.eval b) := by
    have heq : D.eval a * D.eval b = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, gapSumRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    exact hpairProduct
  have hPa : P.eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hPb : P.eval b = 2 * gapPairParity g h := by
    have houtside : (gapRightIndex h).val ≤ g.val ∨
        h.val < (gapRightIndex h).val := Or.inr (by simp)
    have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapRightIndex h)
    have hhval : h.val < (gapRightIndex h).val := by simp
    rw [if_pos houtside,
      gapCoefficient_of_lt h (gapRightIndex h) hhval] at hrel
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside, hrel.symm]
    simp only [gapRightIndex_val]
    norm_num
  have hPevalProduct : 0 < gapPairParity g h * (P.eval a * P.eval b) := by
    rw [hPa, hPb]
    nlinarith [sq_gapPairParity g h]
  have hQevalProduct : 0 < Q.eval a * Q.eval b := by
    have hfactor : gapPairParity g h * (P.eval a * P.eval b) =
        (gapPairParity g h * (D.eval a * D.eval b)) * (Q.eval a * Q.eval b) := by
      rw [hQ]
      simp only [Polynomial.eval_mul]
      ring
    have hmul : 0 < (gapPairParity g h * (D.eval a * D.eval b)) *
        (Q.eval a * Q.eval b) := by rwa [← hfactor]
    rcases mul_pos_iff.mp hmul with hgood | hbad
    · exact hgood.2
    · exact (hDevalProduct.not_gt hbad.1).elim
  refine ⟨⟨Q, ?_, hQne, hQdegree, ?_⟩⟩
  · simpa only [P, D] using hQ
  · simpa only [a, b] using hQevalProduct
private lemma card_filter_between_otherGapIndex {n : ℕ}
    (h g u : Fin (n - 1)) (huh : u < h) :
    ((Finset.univ : Finset (OtherGapIndex h)).filter
      (fun k => g ≤ k.1 ∧ k.1 < u)).card = u.val - g.val := by
  let S := (Finset.univ : Finset (OtherGapIndex h)).filter
    (fun k => g ≤ k.1 ∧ k.1 < u)
  have himage : S.image (fun k => k.1) = Finset.Ico g u := by
    ext k
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hgj, hju⟩, rfl⟩
      exact ⟨hgj, hju⟩
    · intro hk
      exact ⟨⟨k, ne_of_lt (hk.2.trans huh)⟩, ⟨hk.1, hk.2⟩, rfl⟩
  calc
    S.card = (S.image (fun k => k.1)).card := by
      rw [Finset.card_image_of_injective S Subtype.val_injective]
    _ = (Finset.Ico g u).card := congrArg Finset.card himage
    _ = u.val - g.val := by simp
theorem gapSumCombination_sign_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hgq : g ≤ q) (hqh : q < h) {x : ℝ} (hx : x ∈ openGap nodes q) :
    0 < (-1 : ℝ) ^ (q.val - g.val) *
      (gapSumCombination nodes g h).eval x := by
  classical
  let data := Classical.choice (exists_gapSumFactorData nodes g h hgh)
  let Q : ℝ[X] := data.quotient
  let D : ℝ[X] := gapSumRootProduct nodes g h hgh
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  have hax : a < x := by
    have hindex : gapLeftIndex g ≤ gapLeftIndex q := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapLeftIndex_val]
      omega
    exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
  have hxb : x < b := by
    have hindex : gapRightIndex q ≤ gapRightIndex h := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val]
      omega
    exact hx.2.trans_le (nodes.strictMono.monotone hindex)
  have hQa : Q.eval a ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt data.quotient_endpoint_product_pos)
  have hQx : Q.eval x ≠ 0 :=
    eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨hax, hxb⟩
  have hQax : 0 < Q.eval a * Q.eval x := by
    apply eval_mul_eval_pos_of_no_root_between Q hax hQa hQx
    intro z hz hzroot
    have hzne := eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨hz.1, hz.2.trans hxb⟩
    exact hzne hzroot
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (x - root k)
  let before : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < q
  have hpairNeg : ∀ k : OtherGapIndex h, before k → pairValue k < 0 := by
    intro k hk
    have hk_h : k.1 < h := hk.2.trans hqh
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk_h
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootx : root k < x := by
      rw [hrootEq]
      have hindex : gapRightIndex k.1 ≤ gapLeftIndex q := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootx)
  have hpairPos : ∀ k : OtherGapIndex h, ¬before k → 0 < pairValue k := by
    intro k hk
    by_cases hkg : k.1 < g
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hax))
    · have hgk : g ≤ k.1 := le_of_not_gt hkg
      have hqk : q ≤ k.1 := by
        by_contra hnot
        exact hk ⟨hgk, lt_of_not_ge hnot⟩
      have hxroot : x < root k := by
        by_cases hhk : h < k.1
        · have hmem := gapSumRootPoint_mem_openGap_of_outer
            nodes g h hgh k (Or.inr hhk)
          have hindex : gapRightIndex q ≤ gapLeftIndex k.1 := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val, gapLeftIndex_val]
            omega
          calc
            x < nodes.point (gapRightIndex q) := hx.2
            _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
            _ < root k := by simpa only [root] using hmem.1
        · have hkh : k.1 < h :=
            lt_of_le_of_ne (le_of_not_gt hhk) k.property
          have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
            simpa only [root] using gapSumRootPoint_eq_right_of_between
              nodes g h hgh k hgk hkh
          rw [hrootEq]
          have hindex : gapRightIndex q ≤ gapRightIndex k.1 := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val]
            omega
          exact hx.2.trans_le (nodes.strictMono.monotone hindex)
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hax.trans hxroot))
        (sub_neg.mpr hxroot)
  have hDax : 0 < (-1 : ℝ) ^ (q.val - g.val) * (D.eval a * D.eval x) := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) before pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_between_otherGapIndex h g q hqh] at hsign
    have heq : D.eval a * D.eval x = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, gapSumRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    simpa using hsign
  have hPa : (gapSumCombination nodes g h).eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hfactor : gapSumCombination nodes g h = D * Q := by
    simpa only [D, Q] using data.factor
  have htotal : 0 < (-1 : ℝ) ^ (q.val - g.val) *
      ((gapSumCombination nodes g h).eval a *
        (gapSumCombination nodes g h).eval x) := by
    rw [hfactor]
    simp only [Polynomial.eval_mul]
    nlinarith [mul_pos hDax hQax]
  rw [hPa] at htotal
  nlinarith
def gapDifferenceRootProduct {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : ℝ[X] :=
  ∏ q : Fin (n - 1), (X - C (gapDifferenceRootPoint nodes g h hgh q))
structure GapDifferenceFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) where
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  factor : gapDifferenceCombination nodes g h =
    gapDifferenceRootProduct nodes g h hgh * C scale
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Polynomial
open scoped BigOperators
noncomputable section
lemma gapArgmax_lt_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) {g h : Fin (n - 1)} (hgh : g < h) :
    gapArgmax nodes g < gapArgmax nodes h := by
  exact openGap_point_lt_of_gap_lt nodes hgh
    (gapArgmax_mem_openGap nodes hn g)
    (gapArgmax_mem_openGap nodes hn h)
lemma gapArgmax_strictMono {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    StrictMono (gapArgmax nodes) :=
  fun _g _h hgh => gapArgmax_lt_of_gap_lt nodes hn hgh
lemma gapDerivativeQuotient_eval_eq_derivative_div {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (i j : Fin (n - 1)) (hij : j ≠ i) :
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) =
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) /
        (gapArgmax nodes j - gapArgmax nodes i) := by
  have hargne : gapArgmax nodes j - gapArgmax nodes i ≠ 0 := by
    rw [sub_ne_zero]
    exact (gapArgmax_strictMono nodes hn).injective.ne hij
  have hfactor := congrArg (Polynomial.eval (gapArgmax nodes j))
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes hn i)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  rw [eq_div_iff hargne]
  calc
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) *
        (gapArgmax nodes j - gapArgmax nodes i) =
        (gapArgmax nodes j - gapArgmax nodes i) *
          (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) := by ring
    _ = (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) := hfactor
def DerivativeQuotientSignTable {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  (∀ i : Fin (n - 1),
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes i) < 0) ∧
  (∀ i j : Fin (n - 1), i ≠ j →
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j))
def CrossDerivativeCriticalSignTable {n : ℕ}
    (nodes : OrderedNodes n) : Prop :=
  (∀ i j : Fin (n - 1), i < j →
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j)) ∧
  (∀ i j : Fin (n - 1), j < i →
    (-1 : ℝ) ^ (i.val + j.val) *
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) < 0)
theorem derivativeQuotientSignTable_of_crossDerivativeCriticalSignTable
    {n : ℕ} (nodes : OrderedNodes n) (hn : 4 ≤ n)
    (hcross : CrossDerivativeCriticalSignTable nodes) :
    DerivativeQuotientSignTable nodes := by
  constructor
  · exact fun i => gapDerivativeQuotient_eval_gapArgmax_neg nodes hn i
  · intro i j hij
    rw [gapDerivativeQuotient_eval_eq_derivative_div nodes (by omega) i j hij.symm]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · simpa only [div_eq_mul_inv, mul_assoc] using
        div_pos (hcross.1 i j hijlt)
          (sub_pos.mpr (gapArgmax_lt_of_gap_lt nodes (by omega) hijlt))
    · simpa only [div_eq_mul_inv, mul_assoc] using
        div_pos_of_neg_of_neg (hcross.2 i j hjilt)
          (sub_neg.mpr (gapArgmax_lt_of_gap_lt nodes (by omega) hjilt))
private def finiteRootProduct {m : ℕ} (d : Fin m → ℝ) : ℝ[X] :=
  ∏ k : Fin m, (X - C (d k))
private def finiteRootComplement {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  ∏ l ∈ (Finset.univ.erase k : Finset (Fin m)), (X - C (d l))
private lemma finiteRootProduct_eq_mul_complement {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    finiteRootProduct d = (X - C (d k)) * finiteRootComplement d k := by
  classical
  rw [finiteRootProduct, Fintype.prod_eq_mul_prod_compl k]
  simp only [finiteRootComplement, Finset.compl_singleton]
private lemma finiteRootComplement_eval_self_ne_zero {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    (finiteRootComplement d k).eval (d k) ≠ 0 := by
  classical
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  exact sub_ne_zero.mpr (hd.ne hlk.symm)
private lemma finiteRootProduct_derivative_eval_root {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    (finiteRootProduct d).derivative.eval (d k) =
      (finiteRootComplement d k).eval (d k) := by
  rw [finiteRootProduct_eq_mul_complement d k, Polynomial.derivative_mul]
  simp
private def finiteRootBasis {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  C ((finiteRootComplement d k).eval (d k))⁻¹ *
    finiteRootComplement d k
private lemma finiteRootBasis_eval_self {m : ℕ} {d : Fin m → ℝ}
    (hd : Function.Injective d) (k : Fin m) :
    (finiteRootBasis d k).eval (d k) = 1 := by
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  exact inv_mul_cancel₀ (finiteRootComplement_eval_self_ne_zero hd k)
private lemma finiteRootBasis_eval_of_ne {m : ℕ} {d : Fin m → ℝ}
    (k l : Fin m) (hlk : l ≠ k) :
    (finiteRootBasis d k).eval (d l) = 0 := by
  classical
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  suffices (finiteRootComplement d k).eval (d l) = 0 by rw [this, mul_zero]
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩)
  simp
private lemma finiteRootBasis_eq_lagrangeBasis {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    finiteRootBasis d k = Lagrange.basis Finset.univ d k := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hd.injOn
  · have hEvalNe := finiteRootComplement_eval_self_ne_zero hd k
    have hComplementNe : finiteRootComplement d k ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.eval_zero] at hEvalNe
      exact hEvalNe rfl
    rw [finiteRootBasis, Polynomial.degree_mul,
      Polynomial.degree_C (inv_ne_zero hEvalNe), zero_add,
      Polynomial.degree_eq_natDegree hComplementNe,
      finiteRootComplement, natDegree_finset_prod_X_sub_C_eq_card,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · have hdegree := Lagrange.degree_basis hd.injOn (Finset.mem_univ k)
    rw [hdegree, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · intro l _hl
    by_cases hlk : l = k
    · subst l
      rw [finiteRootBasis_eval_self hd]
      exact (Lagrange.eval_basis_self hd.injOn (Finset.mem_univ k)).symm
    · rw [finiteRootBasis_eval_of_ne k l hlk]
      exact (Lagrange.eval_basis_of_ne (Ne.symm hlk) (Finset.mem_univ l)).symm
private lemma finiteRootBasis_wronskian {m : ℕ} (d : Fin m → ℝ)
    (scale : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (finiteRootBasis d k).eval x) =
      -(scale * ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  rw [finiteRootProduct_eq_mul_complement d k]
  simp only [finiteRootBasis, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring
private lemma finiteRootScaledBasis_wronskian {m : ℕ}
    (d : Fin m → ℝ) (scale value : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (C value * finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (C value * finiteRootBasis d k).eval x) =
      -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  have hbase := finiteRootBasis_wronskian d scale k x
  calc
    (finiteRootProduct d * C scale).eval x *
          (C value * finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (C value * finiteRootBasis d k).eval x =
        value * ((finiteRootProduct d * C scale).eval x *
          (finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (finiteRootBasis d k).eval x) := by
            simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
              zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_C]
            ring
    _ = value * (-(scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2) := by rw [hbase]
    _ = -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by ring
private def finiteRootInterpolant {m : ℕ} (d : Fin m → ℝ)
    (S : ℝ[X]) : ℝ[X] :=
  ∑ k : Fin m, C (S.eval (d k)) * finiteRootBasis d k
private lemma finiteRootInterpolant_eq_lagrange {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    finiteRootInterpolant d S =
      Lagrange.interpolate Finset.univ d (fun k => S.eval (d k)) := by
  classical
  rw [finiteRootInterpolant, Lagrange.interpolate_apply]
  simp only [finiteRootBasis_eq_lagrangeBasis hd]
private lemma finiteRootInterpolant_degree_lt {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    (finiteRootInterpolant d S).degree < m := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ) (v := d)
      (fun k => S.eval (d k)) hd.injOn
private lemma finiteRootInterpolant_eval_root {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X])
    (k : Fin m) :
    (finiteRootInterpolant d S).eval (d k) = S.eval (d k) := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  exact Lagrange.eval_interpolate_at_node _ hd.injOn (Finset.mem_univ k)
private lemma exists_finiteRootComplement_eval_ne_zero {m : ℕ}
    (hm : 0 < m) {d : Fin m → ℝ} (hd : Function.Injective d) (x : ℝ) :
    ∃ k : Fin m, (finiteRootComplement d k).eval x ≠ 0 := by
  classical
  by_cases hx : ∃ k : Fin m, x = d k
  · obtain ⟨k, rfl⟩ := hx
    exact ⟨k, finiteRootComplement_eval_self_ne_zero hd k⟩
  · let k : Fin m := ⟨0, hm⟩
    refine ⟨k, ?_⟩
    simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro l _hl
    exact sub_ne_zero.mpr (fun heq => hx ⟨l, heq⟩)
private theorem finite_markov_wronskian_neg {m : ℕ} (hm : 0 < m)
    (d : Fin m → ℝ) (hd : Function.Injective d) (scale : ℝ)
    (hscale : scale ≠ 0) (S : ℝ[X]) (hSdegree : S.natDegree ≤ m)
    (hresidue : ∀ k : Fin m,
      0 < S.eval (d k) *
        (finiteRootProduct d * C scale).derivative.eval (d k))
    (x : ℝ) :
    (finiteRootProduct d * C scale).eval x * S.derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x * S.eval x < 0 := by
  classical
  let M : ℝ[X] := finiteRootProduct d
  let D : ℝ[X] := M * C scale
  let R : ℝ[X] := finiteRootInterpolant d S
  have hMmonic : M.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)), (X - C (d k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (d k)
  have hMne : M ≠ 0 := hMmonic.ne_zero
  have hMdegree : M.natDegree = m := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)),
      (X - C (d k))).natDegree = m
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hRdegree : R.degree < m := by
    simpa only [R] using finiteRootInterpolant_degree_lt hd S
  have hRnatDegree : R.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hRdegree.le
  have hMdvd : M ∣ S - R := by
    change (∏ k : Fin m, (X - C (d k))) ∣ S - R
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hd
    · intro k
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
        Polynomial.eval_sub]
      change S.eval (d k) - (finiteRootInterpolant d S).eval (d k) = 0
      rw [finiteRootInterpolant_eval_root hd S k, sub_self]
  obtain ⟨Q, hQ⟩ := hMdvd
  have hSRdegree : (S - R).natDegree ≤ m :=
    (Polynomial.natDegree_sub_le S R).trans (max_le hSdegree hRnatDegree)
  have hQdegree : Q.natDegree = 0 := by
    by_cases hQzero : Q = 0
    · simp [hQzero]
    · have hproduct : (M * Q).natDegree ≤ m := by
        rw [← hQ]
        exact hSRdegree
      rw [Polynomial.natDegree_mul hMne hQzero, hMdegree] at hproduct
      omega
  obtain ⟨q, hq⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hSfactor : S = R + M * C q := by
    rw [← hq] at hQ
    calc
      S = (S - R) + R := by ring
      _ = M * C q + R := by rw [hQ]
      _ = R + M * C q := by ring
  have hWinvariant :
      D.eval x * S.derivative.eval x - D.derivative.eval x * S.eval x =
        D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x := by
    rw [hSfactor]
    dsimp only [D]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, mul_zero, add_zero,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  let coefficient : Fin m → ℝ := fun k =>
    S.eval (d k) * scale *
      ((finiteRootComplement d k).eval (d k))⁻¹
  have hcoefficient : ∀ k : Fin m, 0 < coefficient k := by
    intro k
    let e : ℝ := (finiteRootComplement d k).eval (d k)
    have he : e ≠ 0 := finiteRootComplement_eval_self_ne_zero hd k
    have hderivative : D.derivative.eval (d k) = e * scale := by
      simp only [D, M, Polynomial.derivative_mul, Polynomial.derivative_C,
        mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
      rw [finiteRootProduct_derivative_eval_root]
    have hpositive : 0 < S.eval (d k) * (e * scale) := by
      rw [← hderivative]
      simpa only [D, M] using hresidue k
    have he2 : 0 < e ^ 2 := sq_pos_of_ne_zero he
    have heq : coefficient k * e ^ 2 = S.eval (d k) * (e * scale) := by
      dsimp only [coefficient, e]
      field_simp
    nlinarith
  have hWsum :
      D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x =
        -∑ k : Fin m, coefficient k *
          ((finiteRootComplement d k).eval x) ^ 2 := by
    simp only [R, finiteRootInterpolant, Polynomial.derivative_sum,
      Polynomial.eval_finset_sum]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [finiteRootScaledBasis_wronskian]
    simp only [coefficient]
    ring
  have hsumPos : 0 < ∑ k : Fin m, coefficient k *
      ((finiteRootComplement d k).eval x) ^ 2 := by
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (hcoefficient k).le (sq_nonneg _)
    · obtain ⟨k, hk⟩ := exists_finiteRootComplement_eval_ne_zero hm hd x
      exact ⟨k, Finset.mem_univ k,
        mul_pos (hcoefficient k) (sq_pos_of_ne_zero hk)⟩
  rw [hWinvariant, hWsum]
  exact neg_neg_of_pos hsumPos
private lemma negOnePowFilter_mul_prod_pos {α : Type*}
    [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hneg : ∀ x ∈ s, p x → f x < 0)
    (hpos : ∀ x ∈ s, ¬p x → 0 < f x) :
    0 < (-1 : ℝ) ^ (s.filter p).card * ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have ih' := ih (fun y hy => hneg y (Finset.mem_insert_of_mem hy))
        (fun y hy => hpos y (Finset.mem_insert_of_mem hy))
      by_cases hpx : p x
      · have hfx : f x < 0 := hneg x (Finset.mem_insert_self x s) hpx
        have hxfilter : x ∉ s.filter p := by simp [hxs]
        rw [Finset.filter_insert, if_pos hpx,
          Finset.card_insert_of_notMem hxfilter, pow_succ,
          Finset.prod_insert hxs]
        nlinarith
      · have hfx : 0 < f x := hpos x (Finset.mem_insert_self x s) hpx
        rw [Finset.filter_insert, if_neg hpx, Finset.prod_insert hxs]
        calc
          0 < ((-1 : ℝ) ^ (s.filter p).card * ∏ y ∈ s, f y) * f x :=
            mul_pos ih' hfx
          _ = (-1 : ℝ) ^ (s.filter p).card *
              (f x * ∏ y ∈ s, f y) := by ring
private lemma card_filter_gt_erase_fin {m : ℕ} (k : Fin m) :
    (((Finset.univ.erase k : Finset (Fin m)).filter
      (fun l => k < l))).card = m - 1 - k.val := by
  have heq : (Finset.univ.erase k : Finset (Fin m)).filter
      (fun l => k < l) = Finset.Ioi k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_Ioi]
    omega
  rw [heq]
  simp
private lemma finiteRootComplement_checkerboard_sign {m : ℕ}
    {d : Fin m → ℝ} (hd : StrictMono d) (k : Fin m) :
    0 < (-1 : ℝ) ^ (m - 1 - k.val) *
      (finiteRootComplement d k).eval (d k) := by
  classical
  have hsign := negOnePowFilter_mul_prod_pos
    (Finset.univ.erase k : Finset (Fin m)) (fun l => k < l)
    (fun l => d k - d l)
    (fun l _hl hkl => sub_neg.mpr (hd hkl))
    (fun l hl hnkl => by
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      exact sub_pos.mpr (hd (lt_of_le_of_ne (le_of_not_gt hnkl) hlk)))
  rw [card_filter_gt_erase_fin k] at hsign
  simpa only [finiteRootComplement, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hsign
private theorem exists_markovGapDifferenceFactorData {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    Nonempty (GapDifferenceFactorData nodes g h hgh) := by
  classical
  let P : ℝ[X] := gapDifferenceCombination nodes g h
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let D : ℝ[X] := gapDifferenceRootProduct nodes g h hgh
  have hP : P ≠ 0 := gapDifferenceCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapDifferenceRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro q
      rw [Polynomial.dvd_iff_isRoot]
      exact gapDifferenceCombination_eval_rootPoint nodes g h hgh q
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ q ∈ (Finset.univ : Finset (Fin (n - 1))),
      (X - C (root q))).Monic
    exact monic_prod_of_monic _ _ fun q _hq => monic_X_sub_C (root q)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 1 := by
    change (∏ q ∈ (Finset.univ : Finset (Fin (n - 1))),
      (X - C (root q))).natDegree = n - 1
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hQdegree : Q.natDegree = 0 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      have hdegree := degree_gapDifferenceCombination_le nodes g h
      rw [Polynomial.degree_eq_natDegree hP] at hdegree
      exact_mod_cast hdegree
    omega
  obtain ⟨c, hcQ⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hc : c ≠ 0 := by
    intro hzero
    apply hQne
    rw [← hcQ, hzero, C_0]
  refine ⟨⟨c, hc, ?_⟩⟩
  calc
    gapDifferenceCombination nodes g h = P := rfl
    _ = D * Q := hQ
    _ = gapDifferenceRootProduct nodes g h hgh * C c := by
      rw [← hcQ]
private lemma negOnePow_add_eq_sub {a b : ℕ} (hab : a ≤ b) :
    (-1 : ℝ) ^ (a + b) = (-1 : ℝ) ^ (b - a) := by
  have heq : a + b = (b - a) + 2 * a := by omega
  rw [heq, pow_add, pow_mul]
  norm_num
@[simp]
private lemma sq_negOnePow (a : ℕ) : ((-1 : ℝ) ^ a) ^ 2 = 1 := by
  rw [← pow_mul]
  have heq : a * 2 = 2 * a := by omega
  rw [heq, pow_mul]
  norm_num
private lemma gapSumCombination_eval_differenceRoot_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h) :
    0 < (-1 : ℝ) ^ (g.val + q.val) *
      (gapSumCombination nodes g h).eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg,
      gapSumCombination_eval_node nodes g h hgh]
    have houtside : (gapLeftIndex q).val ≤ g.val ∨
        h.val < (gapLeftIndex q).val := Or.inl (by simpa using hqg)
    rw [if_pos houtside,
      gapCoefficient_of_le g (gapLeftIndex q) (by simpa using hqg)]
    simp only [gapLeftIndex_val]
    have hparity : (-1 : ℝ) ^ (g.val + q.val) =
        (-1 : ℝ) ^ (g.val - q.val) := by
      simpa only [Nat.add_comm] using negOnePow_add_eq_sub hqg
    rw [hparity]
    nlinarith [sq_negOnePow (g.val - q.val)]
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq,
        gapSumCombination_eval_node nodes g h hgh]
      have houtside : (gapRightIndex q).val ≤ g.val ∨
          h.val < (gapRightIndex q).val := Or.inr (by simp; omega)
      have hgk : g.val < (gapRightIndex q).val := by simp; omega
      rw [if_pos houtside, gapCoefficient_of_lt g (gapRightIndex q) hgk]
      simp only [gapRightIndex_val]
      have hgq : g.val ≤ q.val := by omega
      have hexp : q.val + 1 - g.val - 1 = q.val - g.val := by omega
      rw [hexp]
      rw [negOnePow_add_eq_sub hgq]
      nlinarith [sq_negOnePow (q.val - g.val)]
    · have hgq : g < q := Fin.lt_def.mpr (by omega)
      have hqh : q < h := Fin.lt_def.mpr (by omega)
      have hmem := gapDifferenceRootPoint_mem_openGap_of_between
        nodes g h hgh q hgq hqh
      have hsign := gapSumCombination_sign_middleGap
        nodes g h q hgh hgq.le hqh hmem
      have hparity : (-1 : ℝ) ^ (g.val + q.val) =
          (-1 : ℝ) ^ (q.val - g.val) :=
        negOnePow_add_eq_sub hgq.le
      rwa [hparity]
private lemma card_filter_gt_fin {m : ℕ} (g : Fin m) :
    ((Finset.univ : Finset (Fin m)).filter (fun q => g < q)).card =
      m - 1 - g.val := by
  have heq : (Finset.univ : Finset (Fin m)).filter (fun q => g < q) =
      Finset.Ioi g := by
    ext q
    simp
  rw [heq]
  simp
private lemma negOnePow_two_complements_eq_add {m : ℕ}
    (g q : Fin m) :
    (-1 : ℝ) ^ (m - 1 - g.val) * (-1 : ℝ) ^ (m - 1 - q.val) =
      (-1 : ℝ) ^ (g.val + q.val) := by
  have heq : (m - 1 - g.val) + (m - 1 - q.val) +
      (g.val + q.val) = 2 * (m - 1) := by omega
  have hproduct :
      ((-1 : ℝ) ^ (m - 1 - g.val) *
        (-1 : ℝ) ^ (m - 1 - q.val)) *
          (-1 : ℝ) ^ (g.val + q.val) = 1 := by
    rw [← pow_add, ← pow_add, heq, pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ (m - 1 - g.val) * (-1 : ℝ) ^ (m - 1 - q.val) =
        ((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) * 1 := by ring
    _ = ((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) *
        (((-1 : ℝ) ^ (g.val + q.val)) ^ 2) := by
          rw [sq_negOnePow]
    _ = ((((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) *
        (-1 : ℝ) ^ (g.val + q.val)) *
          (-1 : ℝ) ^ (g.val + q.val)) := by ring
    _ = (-1 : ℝ) ^ (g.val + q.val) := by rw [hproduct]; ring
private lemma gapDifferenceScale_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (-1 : ℝ) ^ (n - 2 - g.val) * data.scale := by
  classical
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  let y : ℝ := nodes.point (gapRightIndex g)
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hMySign : 0 < (-1 : ℝ) ^ (n - 2 - g.val) * M.eval y := by
    have hsign := negOnePowFilter_mul_prod_pos
      (Finset.univ : Finset (Fin (n - 1))) (fun q => g < q)
      (fun q => y - root q)
      (fun q _hq hgq => by
        have hleft : y ≤ nodes.point (gapLeftIndex q) := by
          apply nodes.strictMono.monotone
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        have hroot : nodes.point (gapLeftIndex q) < root q := by
          simpa only [root] using left_lt_gapDifferenceRootPoint_of_lt
            nodes g h hgh q hgq
        exact sub_neg.mpr (hleft.trans_lt hroot))
      (fun q _hq hngq => by
        have hqg : q.val ≤ g.val := by omega
        have hroot : root q = nodes.point (gapLeftIndex q) := by
          simpa only [root] using gapDifferenceRootPoint_eq_left_of_le
            nodes g h hgh q hqg
        change 0 < y - root q
        rw [hroot]
        exact sub_pos.mpr (nodes.strictMono (by
          apply Fin.lt_def.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega)))
    rw [card_filter_gt_fin g] at hsign
    simpa only [Nat.sub_sub, M, finiteRootProduct, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, root, y]
      using hsign
  have hDy : (gapDifferenceCombination nodes g h).eval y = 2 := by
    rw [gapDifferenceCombination_eval_node nodes g h hgh]
    have hinside : ¬((gapRightIndex g).val ≤ g.val ∨
        h.val < (gapRightIndex g).val) := by
      simp only [gapRightIndex_val]
      omega
    rw [if_neg hinside]
    simp
  have hMscale : M.eval y * data.scale = 2 := by
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C] at hDy
    exact hDy
  have hsquare := sq_negOnePow (n - 2 - g.val)
  by_contra hnot
  have hle : (-1 : ℝ) ^ (n - 2 - g.val) * data.scale ≤ 0 :=
    le_of_not_gt hnot
  have hproduct := mul_nonpos_of_nonneg_of_nonpos hMySign.le hle
  have heq :
      ((-1 : ℝ) ^ (n - 2 - g.val) * M.eval y) *
          ((-1 : ℝ) ^ (n - 2 - g.val) * data.scale) =
        M.eval y * data.scale := by nlinarith
  rw [heq, hMscale] at hproduct
  norm_num at hproduct
private lemma gapDifference_derivative_eval_root_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (-1 : ℝ) ^ (g.val + q.val) *
      (gapDifferenceCombination nodes g h).derivative.eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  let e : ℝ := (finiteRootComplement root q).eval (root q)
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hderivative :
      (gapDifferenceCombination nodes g h).derivative.eval (root q) =
        e * data.scale := by
    rw [hfactor]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
      mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
    rw [finiteRootProduct_derivative_eval_root]
  have hscale := gapDifferenceScale_checkerboard nodes g h hgh data
  have hcomplement :
      0 < (-1 : ℝ) ^ (n - 2 - q.val) * e := by
    simpa only [Nat.sub_sub, e, root] using finiteRootComplement_checkerboard_sign
      (gapDifferenceRootPoint_strictMono nodes g h hgh) q
  have hparity := negOnePow_two_complements_eq_add
    (m := n - 1) g q
  rw [show n - 1 - 1 = n - 2 by omega] at hparity
  rw [hderivative, ← hparity]
  nlinarith [mul_pos hscale hcomplement]
private lemma gapDifference_sum_residue_pos {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (gapSumCombination nodes g h).eval
        (gapDifferenceRootPoint nodes g h hgh q) *
      (gapDifferenceCombination nodes g h).derivative.eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  have hsum := gapSumCombination_eval_differenceRoot_checkerboard
    nodes g h q hgh
  have hderiv := gapDifference_derivative_eval_root_checkerboard
    nodes g h q hgh data
  have hsquare := sq_negOnePow (g.val + q.val)
  nlinarith [mul_pos hsum hderiv]
theorem gapCombination_wronskian_neg {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (x : ℝ) :
    (gapDifferenceCombination nodes g h).eval x *
        (gapSumCombination nodes g h).derivative.eval x -
      (gapDifferenceCombination nodes g h).derivative.eval x *
        (gapSumCombination nodes g h).eval x < 0 := by
  let data := Classical.choice
    (exists_markovGapDifferenceFactorData nodes g h hgh)
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  have hm : 0 < n - 1 := by
    have := g.isLt
    omega
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hmarkov := finite_markov_wronskian_neg hm root
    (gapDifferenceRootPoint_strictMono nodes g h hgh).injective
    data.scale data.scale_ne_zero (gapSumCombination nodes g h)
    (natDegree_gapSumCombination_le_sub_one nodes g h hgh)
    (fun q => by
      have hr := gapDifference_sum_residue_pos nodes g h q hgh data
      rw [hfactor] at hr
      simpa only [root] using hr) x
  rw [← hfactor] at hmarkov
  exact hmarkov
private lemma gapCombination_wronskian_eq_gapPolynomials {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (x : ℝ) :
    (gapDifferenceCombination nodes g h).eval x *
        (gapSumCombination nodes g h).derivative.eval x -
      (gapDifferenceCombination nodes g h).derivative.eval x *
        (gapSumCombination nodes g h).eval x =
      2 * gapPairParity g h *
        ((gapPolynomial nodes g).eval x *
            (gapPolynomial nodes h).derivative.eval x -
          (gapPolynomial nodes g).derivative.eval x *
            (gapPolynomial nodes h).eval x) := by
  simp only [gapDifferenceCombination, gapSumCombination,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring
theorem crossDerivativeCriticalSignTable {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    CrossDerivativeCriticalSignTable nodes := by
  constructor
  · intro i j hij
    let x : ℝ := gapArgmax nodes j
    have hw := gapCombination_wronskian_neg nodes i j hij x
    rw [gapCombination_wronskian_eq_gapPolynomials] at hw
    have hjderiv := gapPolynomial_derivative_eval_gapArgmax nodes hn j
    have hjpos : 0 < (gapPolynomial nodes j).eval x := by
      exact zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap
        nodes hn j (gapArgmax_mem_openGap nodes hn j))
    have hprod : 0 < (gapPairParity i j *
        (gapPolynomial nodes i).derivative.eval x) *
          (gapPolynomial nodes j).eval x := by
      rw [show (gapPolynomial nodes j).derivative.eval x = 0 from hjderiv]
        at hw
      nlinarith
    have htarget : 0 < gapPairParity i j *
        (gapPolynomial nodes i).derivative.eval x := by
      rcases mul_pos_iff.mp hprod with hgood | hbad
      · exact hgood.1
      · exact (not_lt_of_ge hjpos.le hbad.2).elim
    have hparity : (-1 : ℝ) ^ (i.val + j.val) = gapPairParity i j := by
      rw [gapPairParity]
      exact negOnePow_add_eq_sub hij.le
    rwa [hparity]
  · intro i j hji
    let x : ℝ := gapArgmax nodes j
    have hw := gapCombination_wronskian_neg nodes j i hji x
    rw [gapCombination_wronskian_eq_gapPolynomials] at hw
    have hjderiv := gapPolynomial_derivative_eval_gapArgmax nodes hn j
    have hjpos : 0 < (gapPolynomial nodes j).eval x := by
      exact zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap
        nodes hn j (gapArgmax_mem_openGap nodes hn j))
    have hprod : (gapPairParity j i *
        (gapPolynomial nodes i).derivative.eval x) *
          (gapPolynomial nodes j).eval x < 0 := by
      rw [show (gapPolynomial nodes j).derivative.eval x = 0 from hjderiv]
        at hw
      nlinarith
    have htarget : gapPairParity j i *
        (gapPolynomial nodes i).derivative.eval x < 0 := by
      rcases mul_neg_iff.mp hprod with hgood | hbad
      · exact (not_lt_of_ge hjpos.le hgood.2).elim
      · exact hbad.1
    have hparity : (-1 : ℝ) ^ (i.val + j.val) = gapPairParity j i := by
      rw [gapPairParity, Nat.add_comm]
      exact negOnePow_add_eq_sub hji.le
    rwa [hparity]
theorem derivativeQuotientSignTable {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) :
    DerivativeQuotientSignTable nodes :=
  derivativeQuotientSignTable_of_crossDerivativeCriticalSignTable nodes hn
    (crossDerivativeCriticalSignTable nodes (by omega))
lemma natDegree_gapDerivativeQuotient_eq_zero_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) :
    (gapDerivativeQuotient nodes i).natDegree = 0 := by
  rw [gapDerivativeQuotient,
    Polynomial.natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  have hdegree := natDegree_gapPolynomial_derivative_le_one_of_three_nodes nodes i
  omega
lemma gapDerivativeQuotient_eval_eq_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x y : ℝ) :
    (gapDerivativeQuotient nodes i).eval x =
      (gapDerivativeQuotient nodes i).eval y := by
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp
    (natDegree_gapDerivativeQuotient_eq_zero_of_three_nodes nodes i)
  rw [← hc]
  simp
lemma gapDerivativeQuotient_eval_neg_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x : ℝ) :
    (gapDerivativeQuotient nodes i).eval x < 0 := by
  let p : ℝ[X] := gapPolynomial nodes i
  let a : ℝ := nodes.point (gapLeftIndex i)
  let τ : ℝ := gapArgmax nodes i
  have haτ : a < τ := (gapArgmax_mem_openGap nodes (by norm_num) i).1
  have hpa : p.eval a = 1 := by
    simpa only [p, a] using gapPolynomial_eval_left nodes i
  have hpτ : 1 < p.eval τ := by
    exact one_lt_eval_gapPolynomial_of_mem_openGap nodes (by norm_num) i
      (gapArgmax_mem_openGap nodes (by norm_num) i)
  obtain ⟨z, hz, hderiv⟩ := exists_deriv_eq_slope p.eval haτ
    p.continuous.continuousOn p.differentiable.differentiableOn
  have hslope : 0 < (p.eval τ - p.eval a) / (τ - a) :=
    div_pos (by rw [hpa]; linarith) (sub_pos.mpr haτ)
  have hdpz : 0 < p.derivative.eval z := by
    have hpderiv : deriv p.eval z = p.derivative.eval z := by
      simp only [Polynomial.deriv]
    rw [← hpderiv, hderiv]
    exact hslope
  have hfactor := congrArg (Polynomial.eval z)
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes (by norm_num) i)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  have hzτ : z - τ < 0 := sub_neg.mpr hz.2
  have hqz : (gapDerivativeQuotient nodes i).eval z < 0 := by
    have hmul : 0 < (z - τ) * (gapDerivativeQuotient nodes i).eval z := by
      rwa [hfactor]
    rcases mul_pos_iff.mp hmul with hbad | hgood
    · exact (not_lt_of_ge hbad.1.le hzτ).elim
    · exact hgood.2
  rw [gapDerivativeQuotient_eval_eq_of_three_nodes nodes i x z]
  exact hqz
theorem derivativeQuotientSignTable_three_nodes (nodes : OrderedNodes 3) :
    DerivativeQuotientSignTable nodes := by
  constructor
  · intro i
    exact gapDerivativeQuotient_eval_neg_of_three_nodes nodes i _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals
      exact gapDerivativeQuotient_eval_neg_of_three_nodes nodes _ _
theorem derivativeQuotientSignTable_of_three_le {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    DerivativeQuotientSignTable nodes := by
  by_cases heq : n = 3
  · subst n
    exact derivativeQuotientSignTable_three_nodes nodes
  · exact derivativeQuotientSignTable nodes (by omega)
@[simp]
lemma gapDerivativeQuotient_eq_zero_of_two_nodes
    (nodes : OrderedNodes 2) (g : Fin 1) :
    gapDerivativeQuotient nodes g = 0 := by
  rw [gapDerivativeQuotient, gapPolynomial_derivative_eq_zero_of_two_nodes]
  simp
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
noncomputable section
def AdmissibleInterval (A B : ℝ) : Prop :=
  (-1 : ℝ) ≤ A ∧ A < B ∧ B ≤ 1
def endpointLeftIndex (d : ℕ) : Fin (d + 2) :=
  ⟨0, by omega⟩
def endpointRightIndex (d : ℕ) : Fin (d + 2) :=
  Fin.last (d + 1)
def interiorNodeIndex {d : ℕ} (i : Fin d) : Fin (d + 2) :=
  ⟨i.val + 1, by omega⟩
@[simp]
lemma endpointLeftIndex_val (d : ℕ) : (endpointLeftIndex d).val = 0 :=
  rfl
@[simp]
lemma endpointRightIndex_val (d : ℕ) : (endpointRightIndex d).val = d + 1 :=
  rfl
@[simp]
lemma interiorNodeIndex_val {d : ℕ} (i : Fin d) :
    (interiorNodeIndex i).val = i.val + 1 :=
  rfl
lemma endpointLeftIndex_lt_interior {d : ℕ} (i : Fin d) :
    endpointLeftIndex d < interiorNodeIndex i := by
  simp [Fin.lt_def]
lemma interior_lt_endpointRightIndex {d : ℕ} (i : Fin d) :
    interiorNodeIndex i < endpointRightIndex d := by
  simp [Fin.lt_def]
lemma interiorNodeIndex_strictMono {d : ℕ} :
    StrictMono (interiorNodeIndex : Fin d → Fin (d + 2)) := by
  intro i j hij
  simpa only [Fin.lt_def, interiorNodeIndex_val] using Nat.add_lt_add_right hij 1
structure EndpointArray (d : ℕ) (A B : ℝ) extends OrderedNodes (d + 2) where
  left_endpoint : point (endpointLeftIndex d) = A
  right_endpoint : point (endpointRightIndex d) = B
namespace EndpointArray
def interior {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i => nodes.point (interiorNodeIndex i)
@[simp]
lemma interior_apply {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    nodes.interior i = nodes.point (interiorNodeIndex i) :=
  rfl
lemma left_lt_interior {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    A < nodes.interior i := by
  calc
    A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
    _ < nodes.point (interiorNodeIndex i) :=
      nodes.strictMono (endpointLeftIndex_lt_interior i)
    _ = nodes.interior i := rfl
lemma interior_lt_right {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    nodes.interior i < B := by
  calc
    nodes.interior i = nodes.point (interiorNodeIndex i) := rfl
    _ < nodes.point (endpointRightIndex d) :=
      nodes.strictMono (interior_lt_endpointRightIndex i)
    _ = B := nodes.right_endpoint
lemma interior_strictMono {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    StrictMono nodes.interior :=
  nodes.strictMono.comp interiorNodeIndex_strictMono
lemma endpoints_lt {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : A < B := by
  calc
    A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
    _ < nodes.point (endpointRightIndex d) := nodes.strictMono (by simp [Fin.lt_def])
    _ = B := nodes.right_endpoint
lemma neg_one_le_left {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    (-1 : ℝ) ≤ A := by
  rw [← nodes.left_endpoint]
  exact nodes.neg_one_le _
lemma right_le_one {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    B ≤ (1 : ℝ) := by
  rw [← nodes.right_endpoint]
  exact nodes.le_one _
lemma admissibleInterval {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    AdmissibleInterval A B :=
  ⟨nodes.neg_one_le_left, nodes.endpoints_lt, nodes.right_le_one⟩
def height {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  gapHeight nodes.toOrderedNodes g
end EndpointArray
def endpointNodeSpace (d : ℕ) (A B : ℝ) : Set (Fin d → ℝ) :=
  {u | (∀ i, A < u i) ∧ StrictMono u ∧ ∀ i, u i < B}
lemma EndpointArray.interior_mem_endpointNodeSpace {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    nodes.interior ∈ endpointNodeSpace d A B :=
  ⟨nodes.left_lt_interior, nodes.interior_strictMono, nodes.interior_lt_right⟩
instance endpointArrayTopologicalSpace (d : ℕ) (A B : ℝ) :
    TopologicalSpace (EndpointArray d A B) :=
  TopologicalSpace.induced EndpointArray.interior inferInstance
lemma isOpen_endpointNodeSpace (d : ℕ) (A B : ℝ) :
    IsOpen (endpointNodeSpace d A B) := by
  have hopenLeft : IsOpen {u : Fin d → ℝ | ∀ i, A < u i} := by
    rw [show {u : Fin d → ℝ | ∀ i, A < u i} =
        ⋂ i : Fin d, {u | A < u i} by ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hopenRight : IsOpen {u : Fin d → ℝ | ∀ i, u i < B} := by
    rw [show {u : Fin d → ℝ | ∀ i, u i < B} =
        ⋂ i : Fin d, {u | u i < B} by ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hopenMono : IsOpen {u : Fin d → ℝ | StrictMono u} := by
    rw [show {u : Fin d → ℝ | StrictMono u} =
        ⋂ i : Fin d, ⋂ j : Fin d, ⋂ (_h : i < j), {u | u i < u j} by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _h => isOpen_lt (continuous_apply i) (continuous_apply j)
  rw [show endpointNodeSpace d A B =
      {u : Fin d → ℝ | ∀ i, A < u i} ∩
        ({u : Fin d → ℝ | StrictMono u} ∩ {u : Fin d → ℝ | ∀ i, u i < B}) by
    ext u
    simp [endpointNodeSpace]]
  exact hopenLeft.inter (hopenMono.inter hopenRight)
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
noncomputable section
lemma endpoint_index_cases {d : ℕ} (k : Fin (d + 2)) :
    k = endpointLeftIndex d ∨ k = endpointRightIndex d ∨
      ∃ i : Fin d, k = interiorNodeIndex i := by
  by_cases hk0 : k.val = 0
  · exact Or.inl (Fin.ext hk0)
  by_cases hkLast : k.val = d + 1
  · exact Or.inr (Or.inl (Fin.ext hkLast))
  right
  right
  let i : Fin d := ⟨k.val - 1, by omega⟩
  exact ⟨i, Fin.ext (by simp [i]; omega)⟩
def endpointPoint {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k : Fin (d + 2)) : ℝ :=
  if hkLeft : k = endpointLeftIndex d then A
  else if hkRight : k = endpointRightIndex d then B
  else u ⟨k.val - 1, by
    have hkPos : 0 < k.val := by
      by_contra hk
      have hk0 : k.val = 0 := Nat.eq_zero_of_not_pos hk
      exact hkLeft (Fin.ext hk0)
    have hkLt : k.val < d + 1 := by
      have := k.isLt
      have hkNe : k.val ≠ d + 1 := by
        intro hk
        exact hkRight (Fin.ext hk)
      omega
    omega⟩
@[simp]
lemma endpointPoint_left {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) :
    endpointPoint A B u (endpointLeftIndex d) = A := by
  simp [endpointPoint]
@[simp]
lemma endpointPoint_right {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) :
    endpointPoint A B u (endpointRightIndex d) = B := by
  have hne : endpointRightIndex d ≠ endpointLeftIndex d := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [endpointPoint, hne]
@[simp]
lemma endpointPoint_interior {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (i : Fin d) :
    endpointPoint A B u (interiorNodeIndex i) = u i := by
  have hleft : interiorNodeIndex i ≠ endpointLeftIndex d :=
    (endpointLeftIndex_lt_interior i).ne'
  have hright : interiorNodeIndex i ≠ endpointRightIndex d :=
    (interior_lt_endpointRightIndex i).ne
  simp only [endpointPoint, dif_neg hleft, dif_neg hright]
  congr 1
lemma endpointPoint_strictMono {d : ℕ} {A B : ℝ} {u : Fin d → ℝ}
    (hAB : A < B) (hu : u ∈ endpointNodeSpace d A B) :
    StrictMono (endpointPoint A B u) := by
  intro i j hij
  rcases endpoint_index_cases i with hi | hi | ⟨r, hi⟩
  · subst i
    rcases endpoint_index_cases j with hj | hj | ⟨s, hj⟩
    · subst j
      exact (lt_irrefl _ hij).elim
    · subst j
      simpa using hAB
    · subst j
      simpa using hu.1 s
  · subst i
    have : ¬endpointRightIndex d < j := by
      simp only [Fin.lt_def, endpointRightIndex_val]
      omega
    exact (this hij).elim
  · subst i
    rcases endpoint_index_cases j with hj | hj | ⟨s, hj⟩
    · subst j
      have : ¬interiorNodeIndex r < endpointLeftIndex d := by simp [Fin.lt_def]
      exact (this hij).elim
    · subst j
      simpa using hu.2.2 r
    · subst j
      have hrs : r < s := by
        change r.val + 1 < s.val + 1 at hij
        exact Fin.lt_def.mpr (Nat.add_lt_add_iff_right.mp hij)
      simpa using hu.2.1 hrs
lemma endpointPoint_mem_Icc {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) {u : Fin d → ℝ}
    (hu : u ∈ endpointNodeSpace d A B) (k : Fin (d + 2)) :
    endpointPoint A B u k ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    rw [endpointPoint_left]
    exact ⟨hAB.1, le_trans hAB.2.1.le hAB.2.2⟩
  · subst k
    rw [endpointPoint_right]
    exact ⟨hAB.1.trans hAB.2.1.le, hAB.2.2⟩
  · subst k
    rw [endpointPoint_interior]
    exact ⟨hAB.1.trans (hu.1 i).le, (hu.2.2 i).le.trans hAB.2.2⟩
def endpointArrayOfInterior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    EndpointArray d A B where
  point := endpointPoint A B u.1
  injective := (endpointPoint_strictMono hAB.2.1 u.2).injective
  mem_Icc := endpointPoint_mem_Icc hAB u.2
  strictMono := endpointPoint_strictMono hAB.2.1 u.2
  left_endpoint := endpointPoint_left A B u.1
  right_endpoint := endpointPoint_right A B u.1
@[simp]
lemma endpointArrayOfInterior_point {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) :
    (endpointArrayOfInterior hAB u).point k = endpointPoint A B u.1 k :=
  rfl
@[simp]
lemma interior_endpointArrayOfInterior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (endpointArrayOfInterior hAB u).interior = u.1 := by
  funext i
  exact endpointPoint_interior A B u.1 i
lemma EndpointArray.ext {d : ℕ} {A B : ℝ} {x y : EndpointArray d A B}
    (h : ∀ k, x.point k = y.point k) : x = y := by
  cases x with
  | mk x hxLeft hxRight => cases x with
    | mk x hxMono =>
      cases y with
      | mk y hyLeft hyRight => cases y with
        | mk y hyMono =>
            simp only [EndpointArray.mk.injEq, OrderedNodes.mk.injEq]
            exact NodeFamily.ext (funext h)
lemma EndpointArray.ext_interior {d : ℕ} {A B : ℝ}
    {x y : EndpointArray d A B} (h : x.interior = y.interior) : x = y := by
  apply EndpointArray.ext
  intro k
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    rw [x.left_endpoint, y.left_endpoint]
  · subst k
    rw [x.right_endpoint, y.right_endpoint]
  · subst k
    exact congrFun h i
@[simp]
lemma endpointArrayOfInterior_interior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (nodes : EndpointArray d A B) :
    endpointArrayOfInterior hAB
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ = nodes := by
  apply EndpointArray.ext_interior
  exact interior_endpointArrayOfInterior hAB _
def endpointArrayEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} where
  toFun nodes := ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  invFun := endpointArrayOfInterior hAB
  left_inv := endpointArrayOfInterior_interior hAB
  right_inv u := Subtype.ext (interior_endpointArrayOfInterior hAB u)
def endpointArrayHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} where
  toEquiv := endpointArrayEquiv hAB
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_induced_dom _
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous (fun u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} ↦
      (endpointArrayOfInterior hAB u).interior)
    convert (continuous_subtype_val : Continuous
      (fun u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} ↦ u.1)) using 1
    all_goals try rfl
    funext u
    exact interior_endpointArrayOfInterior hAB u
def positiveSpacingSimplex (d : ℕ) (L : ℝ) : Set (Fin (d + 1) → ℝ) :=
  {s | (∀ g, 0 < s g) ∧ ∑ g, s g = L}
def logRatioDenominator {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  1 + ∑ i, Real.exp (z i)
lemma logRatioDenominator_pos {d : ℕ} (z : Fin d → ℝ) :
    0 < logRatioDenominator z := by
  unfold logRatioDenominator
  positivity
def softmaxSpacing {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    Fin (d + 1) → ℝ :=
  fun g ↦ Fin.lastCases
    (L / logRatioDenominator z)
    (fun i ↦ L * Real.exp (z i) / logRatioDenominator z) g
@[simp]
lemma softmaxSpacing_last {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    softmaxSpacing L z (Fin.last d) = L / logRatioDenominator z := by
  simp [softmaxSpacing]
@[simp]
lemma softmaxSpacing_castSucc {d : ℕ} (L : ℝ) (z : Fin d → ℝ)
    (i : Fin d) :
    softmaxSpacing L z i.castSucc =
      L * Real.exp (z i) / logRatioDenominator z := by
  simp [softmaxSpacing]
lemma softmaxSpacing_pos {d : ℕ} {L : ℝ} (hL : 0 < L)
    (z : Fin d → ℝ) (g : Fin (d + 1)) :
    0 < softmaxSpacing L z g := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · rw [softmaxSpacing_last]
    exact div_pos hL (logRatioDenominator_pos z)
  · rw [softmaxSpacing_castSucc]
    exact div_pos (mul_pos hL (Real.exp_pos _)) (logRatioDenominator_pos z)
lemma sum_softmaxSpacing {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    ∑ g, softmaxSpacing L z g = L := by
  rw [Fin.sum_univ_castSucc]
  simp only [softmaxSpacing_castSucc, softmaxSpacing_last]
  have hden : logRatioDenominator z ≠ 0 :=
    (logRatioDenominator_pos z).ne'
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  unfold logRatioDenominator at *
  field_simp
  ring
lemma softmaxSpacing_mem_positiveSpacingSimplex {d : ℕ} {L : ℝ}
    (hL : 0 < L) (z : Fin d → ℝ) :
    softmaxSpacing L z ∈ positiveSpacingSimplex d L :=
  ⟨softmaxSpacing_pos hL z, sum_softmaxSpacing L z⟩
def spacingLogRatio {d : ℕ} (s : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i ↦ Real.log (s i.castSucc / s (Fin.last d))
@[simp]
lemma spacingLogRatio_softmaxSpacing {d : ℕ} {L : ℝ} (hL : 0 < L)
    (z : Fin d → ℝ) :
    spacingLogRatio (softmaxSpacing L z) = z := by
  funext i
  unfold spacingLogRatio
  rw [softmaxSpacing_castSucc, softmaxSpacing_last]
  have hL0 : L ≠ 0 := hL.ne'
  have hden : logRatioDenominator z ≠ 0 :=
    (logRatioDenominator_pos z).ne'
  have hratio :
      (L * Real.exp (z i) / logRatioDenominator z) /
          (L / logRatioDenominator z) = Real.exp (z i) := by
    field_simp
  rw [hratio, Real.log_exp]
lemma exp_spacingLogRatio {d : ℕ} {s : Fin (d + 1) → ℝ}
    (hs : ∀ g, 0 < s g) (i : Fin d) :
    Real.exp (spacingLogRatio s i) = s i.castSucc / s (Fin.last d) := by
  unfold spacingLogRatio
  exact Real.exp_log (div_pos (hs _) (hs _))
lemma logRatioDenominator_spacingLogRatio {d : ℕ}
    {s : Fin (d + 1) → ℝ} (hs : ∀ g, 0 < s g) :
    logRatioDenominator (spacingLogRatio s) =
      (∑ g, s g) / s (Fin.last d) := by
  unfold logRatioDenominator
  simp_rw [exp_spacingLogRatio hs]
  rw [Fin.sum_univ_castSucc]
  have href : s (Fin.last d) ≠ 0 := (hs _).ne'
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  field_simp
  ring
@[simp]
lemma softmaxSpacing_spacingLogRatio {d : ℕ} {L : ℝ} (hL : 0 < L)
    (s : Fin (d + 1) → ℝ) (hs : ∀ g, 0 < s g)
    (hsum : ∑ g, s g = L) :
    softmaxSpacing L (spacingLogRatio s) = s := by
  funext g
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · rw [softmaxSpacing_last,
      logRatioDenominator_spacingLogRatio hs, hsum]
    have hL0 : L ≠ 0 := hL.ne'
    have href : s (Fin.last d) ≠ 0 := (hs _).ne'
    field_simp
  · rw [softmaxSpacing_castSucc, exp_spacingLogRatio hs,
      logRatioDenominator_spacingLogRatio hs, hsum]
    have hL0 : L ≠ 0 := hL.ne'
    have href : s (Fin.last d) ≠ 0 := (hs _).ne'
    field_simp
def positiveSpacingLogRatioEquiv {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (Fin d → ℝ) ≃
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} where
  toFun z := ⟨softmaxSpacing L z, softmaxSpacing_mem_positiveSpacingSimplex hL z⟩
  invFun s := spacingLogRatio s.1
  left_inv := spacingLogRatio_softmaxSpacing hL
  right_inv s := Subtype.ext
    (softmaxSpacing_spacingLogRatio hL s.1 s.2.1 s.2.2)
lemma continuous_logRatioDenominator {d : ℕ} :
    Continuous (logRatioDenominator : (Fin d → ℝ) → ℝ) := by
  unfold logRatioDenominator
  exact continuous_const.add (continuous_finset_sum Finset.univ fun i _ ↦
    (continuous_apply i).rexp)
lemma continuous_softmaxSpacing {d : ℕ} (L : ℝ) :
    Continuous (softmaxSpacing L : (Fin d → ℝ) → Fin (d + 1) → ℝ) := by
  apply continuous_pi
  intro g
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · simpa only [softmaxSpacing_last, Pi.div_def] using
      continuous_const.div continuous_logRatioDenominator
        (fun z ↦ (logRatioDenominator_pos z).ne')
  · simpa only [softmaxSpacing_castSucc, Pi.div_def, Pi.mul_def] using
      (continuous_const.mul (continuous_apply i).rexp).div
        continuous_logRatioDenominator
        (fun z ↦ (logRatioDenominator_pos z).ne')
lemma continuous_spacingLogRatio_positive {d : ℕ} {L : ℝ} :
    Continuous (fun s :
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} ↦
        spacingLogRatio s.1) := by
  apply continuous_pi
  intro i
  let X := {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L}
  have hnum : Continuous (fun s : X ↦ s.1 i.castSucc) :=
    (continuous_apply i.castSucc).comp continuous_subtype_val
  have href : Continuous (fun s : X ↦ s.1 (Fin.last d)) :=
    (continuous_apply (Fin.last d)).comp continuous_subtype_val
  have hdiv : Continuous (fun s : X ↦ s.1 i.castSucc / s.1 (Fin.last d)) :=
    hnum.div href (fun s ↦ (s.2.1 _).ne')
  exact hdiv.log (fun s ↦ div_ne_zero (s.2.1 _).ne' (s.2.1 _).ne')
def positiveSpacingLogRatioHomeomorph {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (Fin d → ℝ) ≃ₜ
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} where
  toEquiv := positiveSpacingLogRatioEquiv hL
  continuous_toFun := Continuous.subtype_mk (continuous_softmaxSpacing L) _
  continuous_invFun := continuous_spacingLogRatio_positive
def endpointSpacing {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Fin (d + 1) → ℝ :=
  fun g ↦ nodes.point (gapRightIndex g) - nodes.point (gapLeftIndex g)
lemma endpointSpacing_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) :
    0 < endpointSpacing nodes g := by
  exact sub_pos.mpr (nodes.point_lt
    (gapLeftIndex_lt_rightIndex (n := d + 2) g))
lemma sum_endpointSpacing {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    ∑ g, endpointSpacing nodes g = B - A := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (d + 1), by omega⟩
  rw [Finset.sum_fin_eq_sum_range]
  have htel := Finset.sum_range_sub f (d + 1)
  rw [show f (d + 1) = nodes.point (endpointRightIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointRightIndex],
    show f 0 = nodes.point (endpointLeftIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointLeftIndex]] at htel
  calc
    (∑ i ∈ Finset.range (d + 1),
        if h : i < d + 1 then endpointSpacing nodes ⟨i, h⟩ else 0) =
        ∑ i ∈ Finset.range (d + 1), (f (i + 1) - f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < d + 1 := Finset.mem_range.mp hi
      rw [dif_pos hi']
      unfold endpointSpacing
      simp only [gapRightIndex, gapLeftIndex, f]
      congr 2
      · apply Fin.ext
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        exact (Nat.min_eq_left hi'.le).symm
    _ = nodes.point (endpointRightIndex d) -
        nodes.point (endpointLeftIndex d) := htel
    _ = B - A := by rw [nodes.right_endpoint, nodes.left_endpoint]
lemma endpointSpacing_mem_positiveSpacingSimplex {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    endpointSpacing nodes ∈ positiveSpacingSimplex d (B - A) :=
  ⟨endpointSpacing_pos nodes, sum_endpointSpacing nodes⟩
def spacingPoint {d : ℕ} (A : ℝ) (s : Fin (d + 1) → ℝ)
    (k : Fin (d + 2)) : ℝ :=
  A + ∑ i ∈ Finset.range k.val,
    if hi : i < d + 1 then s ⟨i, hi⟩ else 0
@[simp]
lemma spacingPoint_left {d : ℕ} (A : ℝ) (s : Fin (d + 1) → ℝ) :
    spacingPoint A s (endpointLeftIndex d) = A := by
  simp [spacingPoint, endpointLeftIndex]
lemma spacingPoint_strictMono {d : ℕ} (A : ℝ) {s : Fin (d + 1) → ℝ}
    (hs : ∀ g, 0 < s g) :
    StrictMono (spacingPoint A s) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change A + ∑ r ∈ Finset.range i.val,
      (if hr : r < d + 1 then s ⟨r, hr⟩ else 0) <
    A + ∑ r ∈ Finset.range (i.val + 1),
      (if hr : r < d + 1 then s ⟨r, hr⟩ else 0)
  rw [Finset.sum_range_succ, dif_pos i.isLt]
  calc
    A + ∑ r ∈ Finset.range i.val,
        (if hr : r < d + 1 then s ⟨r, hr⟩ else 0) <
        (A + ∑ r ∈ Finset.range i.val,
          (if hr : r < d + 1 then s ⟨r, hr⟩ else 0)) + s i :=
      lt_add_of_pos_right _ (hs i)
    _ = A + ((∑ r ∈ Finset.range i.val,
          if hr : r < d + 1 then s ⟨r, hr⟩ else 0) + s i) := by ring
@[simp]
lemma spacingPoint_right {d : ℕ} {A B : ℝ}
    {s : Fin (d + 1) → ℝ} (hsum : ∑ g, s g = B - A) :
    spacingPoint A s (endpointRightIndex d) = B := by
  unfold spacingPoint
  simp only [endpointRightIndex_val]
  rw [← Finset.sum_fin_eq_sum_range, hsum]
  ring
def endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (s : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)}) :
    EndpointArray d A B where
  point := spacingPoint A s.1
  injective := (spacingPoint_strictMono A s.2.1).injective
  mem_Icc k := by
    have hmono := (spacingPoint_strictMono A s.2.1).monotone
    constructor
    · calc
        (-1 : ℝ) ≤ A := hAB.1
        _ = spacingPoint A s.1 (endpointLeftIndex d) :=
          (spacingPoint_left A s.1).symm
        _ ≤ spacingPoint A s.1 k :=
          hmono (by simp [Fin.le_iff_val_le_val])
    · calc
        spacingPoint A s.1 k ≤ spacingPoint A s.1 (endpointRightIndex d) :=
          hmono (by
            apply Fin.le_iff_val_le_val.mpr
            simp only [endpointRightIndex_val]
            omega)
        _ = B := spacingPoint_right s.2.2
        _ ≤ 1 := hAB.2.2
  strictMono := spacingPoint_strictMono A s.2.1
  left_endpoint := spacingPoint_left A s.1
  right_endpoint := spacingPoint_right s.2.2
@[simp]
lemma endpointSpacing_endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (s : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)}) :
    endpointSpacing (endpointArrayOfSpacings hAB s) = s.1 := by
  funext g
  unfold endpointSpacing endpointArrayOfSpacings spacingPoint
  simp only [gapRightIndex_val, gapLeftIndex_val]
  rw [Finset.sum_range_succ, dif_pos g.isLt]
  ring
lemma spacingPoint_endpointSpacing {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (k : Fin (d + 2)) :
    spacingPoint A (endpointSpacing nodes) k = nodes.point k := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (d + 1), by omega⟩
  have hk : k.val ≤ d + 1 := by omega
  have htel := Finset.sum_range_sub f k.val
  rw [show f k.val = nodes.point k by
      apply congrArg nodes.point
      apply Fin.ext
      simp [Nat.min_eq_left hk],
    show f 0 = nodes.point (endpointLeftIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointLeftIndex]] at htel
  unfold spacingPoint
  calc
    A + ∑ i ∈ Finset.range k.val,
          (if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0) =
      nodes.point (endpointLeftIndex d) +
        ∑ i ∈ Finset.range k.val,
          (if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0) := by
      exact congrArg (fun x ↦ x + ∑ i ∈ Finset.range k.val,
        if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0)
          nodes.left_endpoint.symm
    _ = nodes.point (endpointLeftIndex d) +
        ∑ i ∈ Finset.range k.val, (f (i + 1) - f i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hiMem
      have hiK : i < k.val := Finset.mem_range.mp hiMem
      have hi : i < d + 1 := lt_of_lt_of_le hiK hk
      rw [dif_pos hi]
      unfold endpointSpacing
      simp only [gapRightIndex, gapLeftIndex, f]
      congr 2
      · apply Fin.ext
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        exact (Nat.min_eq_left hi.le).symm
    _ = nodes.point k := by rw [htel]; ring
@[simp]
lemma endpointArrayOfSpacings_endpointSpacing {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (nodes : EndpointArray d A B) :
    endpointArrayOfSpacings hAB
      ⟨endpointSpacing nodes, endpointSpacing_mem_positiveSpacingSimplex nodes⟩ = nodes := by
  apply EndpointArray.ext
  exact spacingPoint_endpointSpacing nodes
def endpointArraySpacingEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d (B - A)} where
  toFun nodes := ⟨endpointSpacing nodes,
    endpointSpacing_mem_positiveSpacingSimplex nodes⟩
  invFun := endpointArrayOfSpacings hAB
  left_inv := endpointArrayOfSpacings_endpointSpacing hAB
  right_inv s := Subtype.ext (endpointSpacing_endpointArrayOfSpacings hAB s)
lemma continuous_endpointArray_point {d : ℕ} {A B : ℝ}
    (k : Fin (d + 2)) :
    Continuous (fun nodes : EndpointArray d A B ↦ nodes.point k) := by
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    convert (continuous_const : Continuous (fun _ : EndpointArray d A B ↦ A)) using 1
    all_goals try rfl
    funext nodes
    exact nodes.left_endpoint
  · subst k
    convert (continuous_const : Continuous (fun _ : EndpointArray d A B ↦ B)) using 1
    all_goals try rfl
    funext nodes
    exact nodes.right_endpoint
  · subst k
    exact (continuous_apply i).comp
      (continuous_induced_dom : Continuous
        (fun nodes : EndpointArray d A B ↦ nodes.interior))
lemma continuous_endpointSpacing {d : ℕ} {A B : ℝ} :
    Continuous (endpointSpacing : EndpointArray d A B → Fin (d + 1) → ℝ) := by
  apply continuous_pi
  intro g
  exact (continuous_endpointArray_point (gapRightIndex g)).sub
    (continuous_endpointArray_point (gapLeftIndex g))
lemma continuous_endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    Continuous (endpointArrayOfSpacings (d := d) hAB) := by
  rw [continuous_induced_rng]
  change Continuous (fun s :
    {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
      (endpointArrayOfSpacings hAB s).interior)
  apply continuous_pi
  intro i
  change Continuous (fun s :
    {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
      spacingPoint A s.1 (interiorNodeIndex i))
  unfold spacingPoint
  apply continuous_const.add
  apply continuous_finset_sum
  intro r hr
  split_ifs with h
  · let k : Fin (d + 1) := ⟨r, h⟩
    have hc : Continuous (fun s :
        {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
          s.1 k) :=
      (continuous_apply k).comp continuous_subtype_val
    exact hc
  · exact continuous_const
def endpointArraySpacingHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d (B - A)} where
  toEquiv := endpointArraySpacingEquiv hAB
  continuous_toFun := Continuous.subtype_mk continuous_endpointSpacing _
  continuous_invFun := continuous_endpointArrayOfSpacings hAB
def endpointArrayLogRatioHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
  (endpointArraySpacingHomeomorph hAB).trans
    (positiveSpacingLogRatioHomeomorph (sub_pos.mpr hAB.2.1)).symm
lemma endpointArray_zero_unique {A B : ℝ} (x y : EndpointArray 0 A B) :
    x = y := by
  apply EndpointArray.ext_interior
  exact Subsingleton.elim _ _
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Polynomial
open scoped BigOperators Topology
noncomputable section
def coordinateLagrangePolynomial {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k : Fin (d + 2)) : ℝ[X] :=
  ∏ i ∈ Finset.univ.erase k,
    (X - C (endpointPoint A B u i)) *
      C (endpointPoint A B u k - endpointPoint A B u i)⁻¹
def coordinateGapPolynomial {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) : ℝ[X] :=
  ∑ k : Fin (d + 2),
    C (gapCoefficient g k) * coordinateLagrangePolynomial A B u k
def coordinateGapValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  (coordinateGapPolynomial A B u g).eval x
def coordinateCriticalValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  (coordinateGapPolynomial A B u g).derivative.eval x
lemma coordinateLagrangePolynomial_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) :
    coordinateLagrangePolynomial A B u.1 k =
      lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily k := by
  rw [lagrangeBasis_eq_product]
  rfl
lemma coordinateGapPolynomial_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) :
    coordinateGapPolynomial A B u.1 g =
      gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g := by
  classical
  simp only [coordinateGapPolynomial, gapPolynomial, Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coordinateLagrangePolynomial_eq hAB u]
  rfl
lemma coordinateGapValue_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    coordinateGapValue A B u.1 g x =
      (gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).eval x := by
  rw [coordinateGapValue, coordinateGapPolynomial_eq hAB u]
lemma coordinateCriticalValue_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    coordinateCriticalValue A B u.1 g x =
      (gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).derivative.eval x := by
  rw [coordinateCriticalValue, coordinateGapPolynomial_eq hAB u]
def coordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : ℝ :=
  gapHeight (endpointArrayOfInterior hAB u).toOrderedNodes g
def coordinateGapArgmax {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : ℝ :=
  gapArgmax (endpointArrayOfInterior hAB u).toOrderedNodes g
lemma coordinateGapHeight_eq_value_at_argmax {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) :
    coordinateGapHeight hAB u g =
      coordinateGapValue A B u.1 g (coordinateGapArgmax hAB u g) := by
  rw [coordinateGapHeight, coordinateGapArgmax, coordinateGapValue_eq hAB u]
  exact gapHeight_eq_eval_gapArgmax _ _
def coordinateNodalValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) (x : ℝ) : ℝ :=
  ∏ k : Fin (d + 2), (x - endpointPoint A B u k)
def coordinateBasisDenominator {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (j : Fin d) : ℝ :=
  ∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
    (endpointPoint A B u (interiorNodeIndex j) - endpointPoint A B u k)
lemma coordinateNodalValue_eq_mul_erase {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (x : ℝ) :
    coordinateNodalValue A B u x =
      (x - endpointPoint A B u (interiorNodeIndex j)) *
        ∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
          (x - endpointPoint A B u k) := by
  classical
  exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 2)))
    (fun k => x - endpointPoint A B u k) (Finset.mem_univ _)).symm
lemma lagrangeFundamental_interior_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) (x : ℝ) :
    lagrangeFundamental (endpointArrayOfInterior hAB u).toNodeFamily
        (interiorNodeIndex j) x =
      (∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
          (x - endpointPoint A B u.1 k)) *
        (coordinateBasisDenominator A B u.1 j)⁻¹ := by
  classical
  rw [lagrangeFundamental]
  simp only [endpointArrayOfInterior_point, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rfl
def gapJacobianRowFactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  coordinateNodalValue A B nodes.interior (gapArgmax nodes.toOrderedNodes g)
def gapJacobianColumnFactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) : ℝ :=
  (coordinateBasisDenominator A B nodes.interior j)⁻¹
def gapQuotientEvaluationMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun g j => (gapDerivativeQuotient nodes.toOrderedNodes g).eval
    (nodes.point (interiorNodeIndex j))
def gapHeightJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun g j => gapJacobianRowFactor nodes g *
    gapQuotientEvaluationMatrix nodes g j * gapJacobianColumnFactor nodes j
lemma gapPolynomial_derivative_eval_interior_eq {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) (j : Fin d) :
    (gapPolynomial nodes.toOrderedNodes g).derivative.eval
        (nodes.point (interiorNodeIndex j)) =
      (nodes.point (interiorNodeIndex j) - gapArgmax nodes.toOrderedNodes g) *
        (gapDerivativeQuotient nodes.toOrderedNodes g).eval
          (nodes.point (interiorNodeIndex j)) := by
  have h := congrArg (Polynomial.eval (nodes.point (interiorNodeIndex j)))
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes.toOrderedNodes
      (by have := j.isLt; omega) g)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using h.symm
lemma gapHeightJacobianModel_apply_eq {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) (j : Fin d) :
    gapHeightJacobianModel nodes g j =
      -(gapPolynomial nodes.toOrderedNodes g).derivative.eval
          (nodes.point (interiorNodeIndex j)) *
        lagrangeFundamental nodes.toNodeFamily (interiorNodeIndex j)
          (gapArgmax nodes.toOrderedNodes g) := by
  let hAB := nodes.admissibleInterval
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  have hnodes : endpointArrayOfInterior hAB u = nodes :=
    endpointArrayOfInterior_interior hAB nodes
  have hnodal := coordinateNodalValue_eq_mul_erase A B nodes.interior j
    (gapArgmax nodes.toOrderedNodes g)
  have hfund := lagrangeFundamental_interior_eq hAB u j
    (gapArgmax nodes.toOrderedNodes g)
  dsimp [u] at hfund
  rw [hnodes] at hfund
  rw [gapHeightJacobianModel, gapJacobianRowFactor,
    gapQuotientEvaluationMatrix, gapJacobianColumnFactor,
    gapPolynomial_derivative_eval_interior_eq, hfund, hnodal]
  simp only [endpointPoint_interior, EndpointArray.interior_apply]
  ring
def deletedRowMinor {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (omitted : Fin (d + 1)) : ℝ :=
  (M.submatrix omitted.succAbove id).det
theorem deletedRowMinor_gapHeightJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted =
      (∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
        deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
          ∏ j : Fin d, gapJacobianColumnFactor nodes j := by
  let R : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i => gapJacobianRowFactor nodes (omitted.succAbove i))
  let Q : Matrix (Fin d) (Fin d) ℝ :=
    (gapQuotientEvaluationMatrix nodes).submatrix omitted.succAbove id
  let C : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (gapJacobianColumnFactor nodes)
  have hmatrix :
      (gapHeightJacobianModel nodes).submatrix omitted.succAbove id = R * Q * C := by
    ext i j
    simp [R, Q, C, gapHeightJacobianModel, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  rw [deletedRowMinor, hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp [R, Q, C, deletedRowMinor]
lemma coordinateCriticalValue_zero_dim {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B})
    (g : Fin 1) (x : ℝ) :
    coordinateCriticalValue A B u.1 g x = 0 := by
  rw [coordinateCriticalValue_eq hAB u,
    gapPolynomial_derivative_eq_zero_of_two_nodes]
  simp
lemma coordinateGapHeight_zero_dim {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B}) (g : Fin 1) :
    coordinateGapHeight hAB u g = 1 := by
  rw [coordinateGapHeight, gapHeight_eq_eval_gapArgmax,
    gapPolynomial_eq_one_of_two_nodes]
  simp
lemma gapHeightJacobianModel_zero_dim {A B : ℝ}
    (nodes : EndpointArray 0 A B) :
    gapHeightJacobianModel nodes = (0 : Matrix (Fin 1) (Fin 0) ℝ) := by
  ext g j
  exact Fin.elim0 j
lemma deletedRowMinor_zero_dim {A B : ℝ} (nodes : EndpointArray 0 A B)
    (omitted : Fin 1) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted = 1 := by
  rw [gapHeightJacobianModel_zero_dim]
  simp [deletedRowMinor]
def coordinateGapValueMap {d : ℕ} (A B : ℝ) (g : Fin (d + 1)) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z => coordinateGapValue A B z.1 g z.2
def coordinateCriticalMap {d : ℕ} (A B : ℝ) (g : Fin (d + 1)) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z => coordinateCriticalValue A B z.1 g z.2
def criticalVerticalCoefficient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  (gapPolynomial nodes.toOrderedNodes g).derivative.derivative.eval
    (gapArgmax nodes.toOrderedNodes g)
lemma criticalVerticalCoefficient_neg {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) (g : Fin (d + 1)) :
    criticalVerticalCoefficient nodes g < 0 := by
  exact gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes.toOrderedNodes
    (by omega) g
lemma criticalVerticalCoefficient_ne_zero_of_one_coordinate {A B : ℝ}
    (nodes : EndpointArray 1 A B) (g : Fin 2) :
    criticalVerticalCoefficient nodes g ≠ 0 := by
  let dp : ℝ[X] := (gapPolynomial nodes.toOrderedNodes g).derivative
  have hdegree : dp.natDegree ≤ 1 :=
    natDegree_gapPolynomial_derivative_le_one_of_three_nodes
      nodes.toOrderedNodes g
  obtain ⟨a, b, hab⟩ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one hdegree
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero
    nodes.toOrderedNodes (by norm_num) g
  have hcrit : dp.eval (gapArgmax nodes.toOrderedNodes g) = 0 :=
    gapPolynomial_derivative_eval_gapArgmax nodes.toOrderedNodes
      (by norm_num) g
  change dp.derivative.eval (gapArgmax nodes.toOrderedNodes g) ≠ 0
  intro hsecond
  rw [hab] at hdp hcrit hsecond
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one,
    zero_add] at hsecond
  have ha : a = 0 := by simpa using hsecond
  rw [ha] at hdp hcrit
  simp at hdp hcrit
  exact hdp hcrit
lemma criticalVerticalCoefficient_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    criticalVerticalCoefficient nodes g ≠ 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact criticalVerticalCoefficient_ne_zero_of_one_coordinate nodes g
  · exact ne_of_lt (criticalVerticalCoefficient_neg nodes (by omega) g)
lemma coordinateCriticalMap_eq_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    coordinateCriticalMap A B g (u.1, coordinateGapArgmax hAB u g) = 0 := by
  rw [coordinateCriticalMap, coordinateGapArgmax,
    coordinateCriticalValue_eq hAB u]
  exact gapPolynomial_derivative_eval_gapArgmax
    (endpointArrayOfInterior hAB u).toOrderedNodes (by omega) g
structure GapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) where
  criticalDifferential : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ
  valueDifferential : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ
  hasFDerivAt_critical : HasFDerivAt (coordinateCriticalMap A B g)
    criticalDifferential (u.1, coordinateGapArgmax hAB u g)
  contDiffAt_critical : ContDiffAt ℝ 1 (coordinateCriticalMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  critical_vertical :
    criticalDifferential.comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (criticalVerticalCoefficient (endpointArrayOfInterior hAB u) g)
  hasFDerivAt_value : HasFDerivAt (coordinateGapValueMap A B g)
    valueDifferential (u.1, coordinateGapArgmax hAB u g)
  value_vertical :
    valueDifferential.comp
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) = 0
  value_horizontal_sensitivity : ∀ j : Fin d,
    (valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) =
      -(gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).derivative.eval
          ((endpointArrayOfInterior hAB u).point (interiorNodeIndex j)) *
        lagrangeFundamental (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j) (coordinateGapArgmax hAB u g)
private lemma continuousLinearMap_bijective_of_apply_one_ne_zero
    (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : Function.Bijective L := by
  have hformula (x : ℝ) : L x = x * L 1 := by
    calc
      L x = L (x • (1 : ℝ)) := by simp
      _ = x • L 1 := map_smul L x 1
      _ = x * L 1 := by simp [smul_eq_mul]
  constructor
  · intro x y hxy
    have hx := hformula x
    have hy := hformula y
    exact mul_right_cancel₀ h (hx.symm.trans (hxy.trans hy))
  · intro y
    refine ⟨y / L 1, ?_⟩
    rw [hformula]
    exact div_mul_cancel₀ y h
lemma port_isInvertible_of_bijective_real {L : ℝ →L[ℝ] ℝ} (h : Function.Bijective L) :
    L.IsInvertible :=
  ⟨(LinearEquiv.ofBijective (L : ℝ →ₗ[ℝ] ℝ) h).toContinuousLinearEquiv, by ext; rfl⟩
lemma port_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E × ℝ → ℝ} {f' : E × ℝ →L[ℝ] ℝ} {u : E × ℝ} (H : IsContDiffImplicitAt 1 f f' u) :
    (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
  rw [H.hasFDerivAt.fderiv]
  exact port_isInvertible_of_bijective_real H.bijective
noncomputable def port_ifun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E × ℝ → ℝ} {f' : E × ℝ →L[ℝ] ℝ} {u : E × ℝ} (H : IsContDiffImplicitAt 1 f f' u) :
    E → ℝ :=
  H.contDiffAt.implicitFunction H.ne_zero (port_inv H)
def gapCriticalIsContDiffImplicitAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    IsContDiffImplicitAt 1 (coordinateCriticalMap A B g)
      data.criticalDifferential (u.1, coordinateGapArgmax hAB u g) where
  hasFDerivAt := data.hasFDerivAt_critical
  contDiffAt := data.contDiffAt_critical
  bijective := by
    rw [data.critical_vertical]
    apply continuousLinearMap_bijective_of_apply_one_ne_zero
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      one_smul]
    exact criticalVerticalCoefficient_ne_zero
      (endpointArrayOfInterior hAB u) hd g
  ne_zero := by norm_num
def localGapCriticalPoint {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) : (Fin d → ℝ) → ℝ :=
  port_ifun (gapCriticalIsContDiffImplicitAt hAB u hd g data)
lemma localGapCriticalPoint_eq_at_base {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    localGapCriticalPoint hAB u hd g data u.1 = coordinateGapArgmax hAB u g := by
  let hIFT := gapCriticalIsContDiffImplicitAt hAB u hd g data
  exact ContDiffAt.implicitFunction_apply_self hIFT.contDiffAt hIFT.ne_zero (port_inv hIFT)
lemma contDiffAt_localGapCriticalPoint {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ContDiffAt ℝ 1 (localGapCriticalPoint hAB u hd g data) u.1 :=
  ContDiffAt.contDiffAt_implicitFunction (gapCriticalIsContDiffImplicitAt hAB u hd g data).contDiffAt
    (gapCriticalIsContDiffImplicitAt hAB u hd g data).ne_zero (port_inv (gapCriticalIsContDiffImplicitAt hAB u hd g data))
lemma eventually_coordinateCriticalMap_localGapCriticalPoint_eq_zero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1,
      coordinateCriticalMap A B g
        (v, localGapCriticalPoint hAB u hd g data v) = 0 := by
  have hevent :=
    ContDiffAt.eventually_apply_implicitFunction (gapCriticalIsContDiffImplicitAt hAB u hd g data).contDiffAt
      (gapCriticalIsContDiffImplicitAt hAB u hd g data).ne_zero (port_inv (gapCriticalIsContDiffImplicitAt hAB u hd g data))
  rw [coordinateCriticalMap_eq_zero hAB u (by omega) g] at hevent
  exact hevent
lemma localGapCriticalPoint_eq_gapArgmax_of_mem_openGap
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g)
    (v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hcritical : coordinateCriticalMap A B g
      (v.1, localGapCriticalPoint hAB u hd g data v.1) = 0)
    (hgap : localGapCriticalPoint hAB u hd g data v.1 ∈
      openGap (endpointArrayOfInterior hAB v).toOrderedNodes g) :
    localGapCriticalPoint hAB u hd g data v.1 =
      coordinateGapArgmax hAB v g := by
  have hderiv :
      (gapPolynomial (endpointArrayOfInterior hAB v).toOrderedNodes g).derivative.eval
        (localGapCriticalPoint hAB u hd g data v.1) = 0 := by
    rw [← coordinateCriticalValue_eq hAB v]
    exact hcritical
  by_cases hd1 : d = 1
  · subst d
    exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes
      (endpointArrayOfInterior hAB v).toOrderedNodes g hderiv
  · exact eq_gapArgmax_of_derivative_eval_eq_zero
      (endpointArrayOfInterior hAB v).toOrderedNodes (by omega) g hgap hderiv
lemma hasFDerivAt_envelope_of_vertical_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} {F' : E × ℝ →L[ℝ] ℝ} {τ : E → ℝ}
    {τ' : E →L[ℝ] ℝ} {u : E}
    (hF : HasFDerivAt F F' (u, τ u)) (hτ : HasFDerivAt τ τ' u)
    (hvertical : F'.comp (ContinuousLinearMap.inr ℝ E ℝ) = 0) :
    HasFDerivAt (fun v => F (v, τ v))
      (F'.comp (ContinuousLinearMap.inl ℝ E ℝ)) u := by
  have hpair : HasFDerivAt (fun v : E => (v, τ v))
      ((1 : E →L[ℝ] E).prod τ') u :=
    (hasFDerivAt_id u).prodMk hτ
  have hcomp := hF.comp u hpair
  have hmaps : F'.comp ((1 : E →L[ℝ] E).prod τ') =
      F'.comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    ext v
    have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L (τ' v)) hvertical
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.zero_apply] at hv
    change F' (v, τ' v) = F' (v, 0)
    rw [show (v, τ' v) = (v, 0) + (0, τ' v) by ext <;> simp]
    rw [map_add, hv, add_zero]
  rw [hmaps] at hcomp
  simpa only [Function.comp_def] using hcomp
def localGapCriticalHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) : (Fin d → ℝ) → ℝ :=
  fun v => coordinateGapValue A B v g
    (localGapCriticalPoint hAB u hd g data v)
private lemma continuous_endpointPoint_coordinate {d : ℕ} (A B : ℝ)
    (k : Fin (d + 2)) :
    Continuous (fun v : Fin d → ℝ => endpointPoint A B v k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split
    · fun_prop
    · fun_prop
lemma eventually_localGapCriticalPoint_mem_coordinate_openGap
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1,
      endpointPoint A B v (gapLeftIndex (n := d + 2) g) <
          localGapCriticalPoint hAB u hd g data v ∧
        localGapCriticalPoint hAB u hd g data v <
          endpointPoint A B v (gapRightIndex (n := d + 2) g) := by
  have hτcont : ContinuousAt (localGapCriticalPoint hAB u hd g data) u.1 :=
    (contDiffAt_localGapCriticalPoint hAB u hd g data).continuousAt
  have hopen := gapArgmax_mem_openGap
    (endpointArrayOfInterior hAB u).toOrderedNodes (by omega) g
  have hbaseLeft :
      endpointPoint A B u.1 (gapLeftIndex (n := d + 2) g) <
        localGapCriticalPoint hAB u hd g data u.1 := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact hopen.1
  have hbaseRight :
      localGapCriticalPoint hAB u hd g data u.1 <
        endpointPoint A B u.1 (gapRightIndex (n := d + 2) g) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact hopen.2
  exact ((continuous_endpointPoint_coordinate A B
      (gapLeftIndex (n := d + 2) g)).continuousAt.eventually_lt
        hτcont hbaseLeft).and
    (hτcont.eventually_lt
      (continuous_endpointPoint_coordinate A B
        (gapRightIndex (n := d + 2) g)).continuousAt hbaseRight)
lemma eventually_localGapCriticalHeight_eq_coordinateGapHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1, ∀ hv : v ∈ endpointNodeSpace d A B,
      localGapCriticalHeight hAB u hd g data v =
        coordinateGapHeight hAB ⟨v, hv⟩ g := by
  filter_upwards
      [eventually_coordinateCriticalMap_localGapCriticalPoint_eq_zero
        hAB u hd g data,
       eventually_localGapCriticalPoint_mem_coordinate_openGap
        hAB u hd g data] with v hcritical hgap
  intro hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  have hgap' : localGapCriticalPoint hAB u hd g data v ∈
      openGap (endpointArrayOfInterior hAB v').toOrderedNodes g := hgap
  have harg := localGapCriticalPoint_eq_gapArgmax_of_mem_openGap
    hAB u hd g data v' hcritical hgap'
  rw [coordinateGapHeight_eq_value_at_argmax]
  change coordinateGapValue A B v g
      (localGapCriticalPoint hAB u hd g data v) =
    coordinateGapValue A B v g (coordinateGapArgmax hAB v' g)
  rw [harg]
def extendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) (v : Fin d → ℝ) : ℝ := by
  classical
  exact if hv : v ∈ endpointNodeSpace d A B then
      coordinateGapHeight hAB ⟨v, hv⟩ g
    else localGapCriticalHeight hAB u hd g data v
lemma hasFDerivAt_localGapCriticalHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    HasFDerivAt (localGapCriticalHeight hAB u hd g data)
      (data.valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 := by
  have hτdiff : DifferentiableAt ℝ
      (localGapCriticalPoint hAB u hd g data) u.1 :=
    (contDiffAt_localGapCriticalPoint hAB u hd g data).differentiableAt
      (by norm_num)
  have hτ := hτdiff.hasFDerivAt
  have hvalue : HasFDerivAt (coordinateGapValueMap A B g)
      data.valueDifferential
      (u.1, localGapCriticalPoint hAB u hd g data u.1) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact data.hasFDerivAt_value
  exact hasFDerivAt_envelope_of_vertical_eq_zero hvalue hτ data.value_vertical
lemma hasFDerivAt_extendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    HasFDerivAt (extendedCoordinateGapHeight hAB u hd g data)
      (data.valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 := by
  apply (hasFDerivAt_localGapCriticalHeight hAB u hd g data).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 u.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  filter_upwards [hspace,
    eventually_localGapCriticalHeight_eq_coordinateGapHeight
      hAB u hd g data] with v hv heq
  rw [extendedCoordinateGapHeight, dif_pos hv]
  exact (heq hv).symm
def QuotientEvaluationMaximalMinorsNonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  ∀ omitted : Fin (d + 1),
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0
def coordinateLagrangeFactorValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k i : Fin (d + 2)) (x : ℝ) : ℝ :=
  (x - endpointPoint A B u i) *
    (endpointPoint A B u k - endpointPoint A B u i)⁻¹
lemma coordinateLagrangePolynomial_eval_eq_prod_factor {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangePolynomial A B u k).eval x =
      ∏ i ∈ Finset.univ.erase k,
        coordinateLagrangeFactorValue A B u k i x := by
  simp only [coordinateLagrangePolynomial, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, coordinateLagrangeFactorValue]
lemma differentiable_endpointPoint_coordinate {d : ℕ} (A B : ℝ)
    (k : Fin (d + 2)) :
    Differentiable ℝ (fun u : Fin d → ℝ => endpointPoint A B u k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split <;> fun_prop
lemma endpointPoint_sub_ne_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) :
    endpointPoint A B u.1 k - endpointPoint A B u.1 i ≠ 0 := by
  exact sub_ne_zero.mpr
    ((endpointPoint_strictMono hAB.2.1 u.2).injective.ne hki)
lemma differentiableAt_coordinateLagrangeFactorValue {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) :
    DifferentiableAt ℝ (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeFactorValue A B z.1 k i z.2) (u.1, x) := by
  unfold coordinateLagrangeFactorValue
  apply DifferentiableAt.mul
  · exact differentiableAt_snd.sub
      ((differentiable_endpointPoint_coordinate A B i).differentiableAt.comp
        _ differentiableAt_fst)
  · apply DifferentiableAt.inv
    · exact ((differentiable_endpointPoint_coordinate A B k).differentiableAt.comp
          _ differentiableAt_fst).sub
        ((differentiable_endpointPoint_coordinate A B i).differentiableAt.comp
          _ differentiableAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u hki
lemma differentiableAt_coordinateLagrangePolynomial_eval {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) (x : ℝ) :
    DifferentiableAt ℝ (fun z : (Fin d → ℝ) × ℝ =>
      (coordinateLagrangePolynomial A B z.1 k).eval z.2) (u.1, x) := by
  simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
  let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
    fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
  have hfac : ∀ i ∈ Finset.univ.erase k,
      DifferentiableAt ℝ (fac i) (u.1, x) := by
    intro i hi
    exact differentiableAt_coordinateLagrangeFactorValue hAB u
      (Finset.mem_erase.mp hi).1.symm x
  have hprod := HasFDerivAt.finset_prod
    (g' := fun i => fderiv ℝ (fac i) (u.1, x))
    (fun i hi => (hfac i hi).hasFDerivAt)
  exact hprod.differentiableAt
lemma differentiableAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    DifferentiableAt ℝ (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  have hsum := DifferentiableAt.sum (u := Finset.univ)
    (A := fun k (z : (Fin d → ℝ) × ℝ) => gapCoefficient g k *
      (coordinateLagrangePolynomial A B z.1 k).eval z.2)
    (fun k _ => (differentiableAt_const (c := gapCoefficient g k)).mul
      (differentiableAt_coordinateLagrangePolynomial_eval hAB u k x))
  convert hsum using 1
  all_goals try rfl
  funext z
  simp
def coordinateLagrangeCriticalFormula {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase k,
    (∏ m ∈ (Finset.univ.erase k).erase i,
      coordinateLagrangeFactorValue A B u k m x) *
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹
lemma hasDerivAt_coordinateLagrangeFactorValue_evaluation {d : ℕ}
    {A B : ℝ} {u : Fin d → ℝ} {k i : Fin (d + 2)} {x : ℝ} :
    HasDerivAt (fun y => coordinateLagrangeFactorValue A B u k i y)
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹ x := by
  unfold coordinateLagrangeFactorValue
  convert ((hasDerivAt_id x).sub_const
    (endpointPoint A B u i)).mul_const
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹ using 1
  all_goals try rfl
  all_goals first | ring | (funext y; simp only [id]; ring)
lemma coordinateLagrangeCriticalFormula_eq {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangePolynomial A B u k).derivative.eval x =
      coordinateLagrangeCriticalFormula A B u k x := by
  have hp := (coordinateLagrangePolynomial A B u k).hasDerivAt x
  have hprod := HasDerivAt.finset_prod (x := x)
    (u := Finset.univ.erase k)
    (f := fun i y => coordinateLagrangeFactorValue A B u k i y)
    (f' := fun i => (endpointPoint A B u k - endpointPoint A B u i)⁻¹)
    (fun _i _ => hasDerivAt_coordinateLagrangeFactorValue_evaluation)
  have hprod' : HasDerivAt
      (fun y => ∏ i ∈ Finset.univ.erase k,
        coordinateLagrangeFactorValue A B u k i y)
      (coordinateLagrangeCriticalFormula A B u k x) x := by
    convert hprod using 1
    all_goals try rfl
    funext y
    simp
  have heqfun :
      (fun y => (coordinateLagrangePolynomial A B u k).eval y) =
        fun y => ∏ i ∈ Finset.univ.erase k,
          coordinateLagrangeFactorValue A B u k i y := by
    funext y
    exact coordinateLagrangePolynomial_eval_eq_prod_factor A B u k y
  rw [heqfun] at hp
  exact hp.unique hprod'
def coordinateGapCriticalFormula {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  ∑ k : Fin (d + 2), gapCoefficient g k *
    coordinateLagrangeCriticalFormula A B u k x
lemma coordinateGapCriticalFormula_eq {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (x : ℝ) :
    coordinateCriticalValue A B u g x =
      coordinateGapCriticalFormula A B u g x := by
  simp only [coordinateCriticalValue, coordinateGapPolynomial,
    Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    coordinateGapCriticalFormula, coordinateLagrangeCriticalFormula_eq]
lemma contDiff_endpointPoint_coordinate {d : ℕ} (n : WithTop ℕ∞)
    (A B : ℝ) (k : Fin (d + 2)) :
    ContDiff ℝ n (fun u : Fin d → ℝ => endpointPoint A B u k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split <;> fun_prop
private lemma contDiffAt_finset_prod_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (1 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))
private lemma contDiffAt_finset_sum_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (0 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))
lemma contDiffAt_coordinateLagrangeFactorValue {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeFactorValue A B z.1 k i z.2) (u.1, x) := by
  unfold coordinateLagrangeFactorValue
  apply ContDiffAt.mul
  · exact contDiffAt_snd.sub
      ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
        (u.1, x) contDiffAt_fst)
  · apply ContDiffAt.inv
    · exact ((contDiff_endpointPoint_coordinate n A B k).contDiffAt.comp
          (u.1, x) contDiffAt_fst).sub
        ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
          (u.1, x) contDiffAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u hki
lemma contDiffAt_coordinateLagrangeCriticalFormula {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeCriticalFormula A B z.1 k z.2) (u.1, x) := by
  unfold coordinateLagrangeCriticalFormula
  apply contDiffAt_finset_sum_scalar
  intro i hi
  apply ContDiffAt.mul
  · apply contDiffAt_finset_prod_scalar
    intro m hm
    exact contDiffAt_coordinateLagrangeFactorValue hAB u (by
      have hm' := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1
      exact hm'.symm) x n
  · apply ContDiffAt.inv
    · exact ((contDiff_endpointPoint_coordinate n A B k).contDiffAt.comp
          (u.1, x) contDiffAt_fst).sub
        ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
          (u.1, x) contDiffAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u
        (Finset.mem_erase.mp hi).1.symm
lemma contDiffAt_coordinateCriticalMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (coordinateCriticalMap A B g) (u.1, x) := by
  rw [show coordinateCriticalMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        coordinateLagrangeCriticalFormula A B z.1 k z.2 by
    funext z
    exact coordinateGapCriticalFormula_eq A B z.1 g z.2]
  apply contDiffAt_finset_sum_scalar
  intro k _
  exact contDiffAt_const.mul
    (contDiffAt_coordinateLagrangeCriticalFormula hAB u k x n)
private lemma fderiv_comp_inr_eq_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hx : HasDerivAt (fun y => f (u, y)) c x) :
    (fderiv ℝ f (u, x)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c := by
  have hcurve : HasFDerivAt (fun y : ℝ => (u, y))
      (ContinuousLinearMap.inr ℝ E ℝ) x := by
    convert (hasFDerivAt_const (x := x) (c := u)).prodMk
      (hasFDerivAt_id x) using 1
    all_goals try rfl
  have hcomp := hf.hasFDerivAt.comp x hcurve
  exact hcomp.unique hx
lemma coordinateGapValueMap_fderiv_vertical {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    (fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)).comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (coordinateCriticalValue A B u.1 g x) := by
  apply fderiv_comp_inr_eq_of_hasDeriv
    (differentiableAt_coordinateGapValueMap hAB u g x)
  change HasDerivAt (fun y => coordinateGapValue A B u.1 g y)
    (coordinateCriticalValue A B u.1 g x) x
  simpa only [coordinateGapValue, coordinateCriticalValue] using
    (coordinateGapPolynomial A B u.1 g).hasDerivAt x
lemma coordinateCriticalMap_fderiv_vertical {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    (fderiv ℝ (coordinateCriticalMap A B g) (u.1, x)).comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((coordinateGapPolynomial A B u.1 g).derivative.derivative.eval x) := by
  apply fderiv_comp_inr_eq_of_hasDeriv
    ((contDiffAt_coordinateCriticalMap hAB u g x 1).differentiableAt
      (by norm_num))
  change HasDerivAt (fun y => coordinateCriticalValue A B u.1 g y)
    ((coordinateGapPolynomial A B u.1 g).derivative.derivative.eval x) x
  simpa only [coordinateCriticalValue] using
    (coordinateGapPolynomial A B u.1 g).derivative.hasDerivAt x
def coordinateDirection {d : ℕ} (j : Fin d) : Fin d → ℝ := Pi.single j 1
def coordinateShift {d : ℕ} (u : Fin d → ℝ) (j : Fin d) (s : ℝ) :
    Fin d → ℝ :=
  u + s • coordinateDirection j
@[simp]
lemma coordinateShift_zero {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    coordinateShift u j 0 = u := by
  ext i
  simp [coordinateShift]
lemma coordinateShift_apply_self {d : ℕ} (u : Fin d → ℝ)
    (j : Fin d) (s : ℝ) :
    coordinateShift u j s j = u j + s := by
  simp [coordinateShift, coordinateDirection]
lemma coordinateShift_apply_of_ne {d : ℕ} (u : Fin d → ℝ)
    {j i : Fin d} (hij : i ≠ j) (s : ℝ) :
    coordinateShift u j s i = u i := by
  simp [coordinateShift, coordinateDirection, hij]
def coordinateNodeVelocity {d : ℕ} (j : Fin d) (k : Fin (d + 2)) : ℝ :=
  if k = interiorNodeIndex j then 1 else 0
lemma hasDerivAt_endpointPoint_coordinateShift {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) :
    HasDerivAt (fun s => endpointPoint A B (coordinateShift u j s) k)
      (coordinateNodeVelocity j k) 0 := by
  rcases endpoint_index_cases k with rfl | rfl | ⟨i, rfl⟩
  · simp only [endpointPoint_left]
    have hne : endpointLeftIndex d ≠ interiorNodeIndex j :=
      (endpointLeftIndex_lt_interior j).ne
    simpa [coordinateNodeVelocity, hne] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := A))
  · simp only [endpointPoint_right]
    have hne : endpointRightIndex d ≠ interiorNodeIndex j :=
      (interior_lt_endpointRightIndex j).ne'
    simpa [coordinateNodeVelocity, hne] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := B))
  · simp only [endpointPoint_interior]
    by_cases hij : i = j
    · subst i
      simp only [coordinateShift_apply_self]
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := u j)).add
        (hasDerivAt_id 0) using 1
      all_goals try rfl
      simp [coordinateNodeVelocity]
    · have hfun : (fun s => coordinateShift u j s i) = fun _ => u i := by
        funext s
        exact coordinateShift_apply_of_ne u hij s
      have hnode : interiorNodeIndex i ≠ interiorNodeIndex j :=
        interiorNodeIndex_strictMono.injective.ne hij
      rw [hfun]
      simpa [coordinateNodeVelocity, hnode] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := u i))
lemma hasFDerivAt_coordinateShift {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    HasFDerivAt (coordinateShift u j)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (coordinateDirection j)) 0 := by
  let L : ℝ →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (coordinateDirection j)
  have h := (hasFDerivAt_const (x := (0 : ℝ)) (c := u)).add L.hasFDerivAt
  simpa [coordinateShift, L, smul_eq_mul, mul_comm] using h
def coordinateLagrangeFactorPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k i : Fin (d + 2)) : ℝ[X] :=
  (X - C (endpointPoint A B u i)) *
    C (endpointPoint A B u k - endpointPoint A B u i)⁻¹
def coordinateLagrangeFactorPartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k i : Fin (d + 2)) : ℝ[X] :=
  (C (-(coordinateNodeVelocity j i) *
        (endpointPoint A B u k - endpointPoint A B u i)) -
      (X - C (endpointPoint A B u i)) *
        C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)) *
    C (((endpointPoint A B u k - endpointPoint A B u i) ^ 2)⁻¹)
lemma coordinateLagrangeFactorPolynomial_eval {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k i : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangeFactorPolynomial A B u k i).eval x =
      coordinateLagrangeFactorValue A B u k i x := by
  simp [coordinateLagrangeFactorPolynomial,
    coordinateLagrangeFactorValue]
lemma hasDerivAt_coordinateLagrangeFactor_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) :
    HasDerivAt (fun s => coordinateLagrangeFactorValue A B
      (coordinateShift u.1 j s) k i x)
      ((coordinateLagrangeFactorPartialPolynomial A B u.1 j k i).eval x) 0 := by
  have hti := hasDerivAt_endpointPoint_coordinateShift A B u.1 j i
  have htk := hasDerivAt_endpointPoint_coordinateShift A B u.1 j k
  have hnum : HasDerivAt
      (fun s => x - endpointPoint A B (coordinateShift u.1 j s) i)
      (-(coordinateNodeVelocity j i)) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := x)).sub hti using 1
    all_goals try rfl
    all_goals simp [coordinateNodeVelocity]
  have hden : HasDerivAt
      (fun s => endpointPoint A B (coordinateShift u.1 j s) k -
        endpointPoint A B (coordinateShift u.1 j s) i)
      (coordinateNodeVelocity j k - coordinateNodeVelocity j i) 0 := by
    exact htk.sub hti
  have hne := endpointPoint_sub_ne_zero hAB u hki
  have hquot := hnum.div hden (by simpa using hne)
  convert hquot using 1
  all_goals try rfl
  simp only [coordinateLagrangeFactorPartialPolynomial,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, coordinateShift_zero]
  field_simp [hne]
def coordinateLagrangePartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) : ℝ[X] :=
  ∑ i ∈ Finset.univ.erase k,
    coordinateLagrangeFactorPartialPolynomial A B u j k i *
      ∏ m ∈ (Finset.univ.erase k).erase i,
        coordinateLagrangeFactorPolynomial A B u k m
def coordinateGapPartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (j : Fin d) : ℝ[X] :=
  ∑ k : Fin (d + 2), C (gapCoefficient g k) *
    coordinateLagrangePartialPolynomial A B u j k
lemma hasDerivAt_coordinateLagrange_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) (k : Fin (d + 2)) (x : ℝ) :
    HasDerivAt (fun s =>
      (coordinateLagrangePolynomial A B (coordinateShift u.1 j s) k).eval x)
      ((coordinateLagrangePartialPolynomial A B u.1 j k).eval x) 0 := by
  let fac : Fin (d + 2) → ℝ → ℝ := fun i s =>
    coordinateLagrangeFactorValue A B (coordinateShift u.1 j s) k i x
  have hprod := HasDerivAt.finset_prod (x := (0 : ℝ))
    (u := Finset.univ.erase k) (f := fac)
    (f' := fun i =>
      (coordinateLagrangeFactorPartialPolynomial A B u.1 j k i).eval x)
    (fun i hi => hasDerivAt_coordinateLagrangeFactor_coordinateShift
      hAB u j (Finset.mem_erase.mp hi).1.symm x)
  convert hprod using 1
  all_goals try rfl
  · funext s
    rw [coordinateLagrangePolynomial_eval_eq_prod_factor]
    simp [fac]
  · simp only [coordinateLagrangePartialPolynomial,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod,
      fac, coordinateLagrangeFactorPolynomial_eval, smul_eq_mul,
      coordinateShift_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring
private lemma hasDerivAt_finset_sum_scalar {ι : Type*} {s : Finset ι}
    {f : ι → ℝ → ℝ} {f' : ι → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, f' i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (x := x) (c := (0 : ℝ))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      convert (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi]))) using 1
      all_goals try rfl
lemma hasDerivAt_coordinateGapValue_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    HasDerivAt (fun s => coordinateGapValue A B
      (coordinateShift u.1 j s) g x)
      ((coordinateGapPartialPolynomial A B u.1 g j).eval x) 0 := by
  rw [show (fun s => coordinateGapValue A B
      (coordinateShift u.1 j s) g x) =
      fun s => ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B
          (coordinateShift u.1 j s) k).eval x by
    funext s
    simp only [coordinateGapValue, coordinateGapPolynomial,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]]
  have hsum := hasDerivAt_finset_sum_scalar (s := Finset.univ)
    (f := fun k s => gapCoefficient g k *
      (coordinateLagrangePolynomial A B
        (coordinateShift u.1 j s) k).eval x)
    (f' := fun k => gapCoefficient g k *
      (coordinateLagrangePartialPolynomial A B u.1 j k).eval x)
    (fun k _ => (hasDerivAt_coordinateLagrange_coordinateShift
      hAB u j k x).const_mul (gapCoefficient g k))
  convert hsum using 1
  all_goals try rfl
  simp only [coordinateGapPartialPolynomial,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
private lemma fderiv_apply_inl_direction_eq_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u v : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hv : HasFDerivAt (fun s : ℝ => u + s • v)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0)
    (hx : HasDerivAt (fun s : ℝ => f (u + s • v, x)) c 0) :
    fderiv ℝ f (u, x) (v, 0) = c := by
  have hcurve : HasFDerivAt (fun s : ℝ => (u + s • v, x))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v).prod
        (0 : ℝ →L[ℝ] ℝ)) 0 :=
    hv.prodMk (hasFDerivAt_const (x := (0 : ℝ)) (c := x))
  have hfbase : HasFDerivAt f (fderiv ℝ f (u, x))
      (u + (0 : ℝ) • v, x) := by
    simpa using hf.hasFDerivAt
  have hcomp := hfbase.comp 0 hcurve
  have hvalue := hcomp.unique (by
    simpa only [Function.comp_def] using hx.hasFDerivAt)
  have happly := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hvalue
  simpa using happly
lemma coordinateGapValueMap_fderiv_horizontal_explicit {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)
        (coordinateDirection j, 0) =
      (coordinateGapPartialPolynomial A B u.1 g j).eval x := by
  apply fderiv_apply_inl_direction_eq_of_hasDeriv
    (differentiableAt_coordinateGapValueMap hAB u g x)
  · exact hasFDerivAt_coordinateShift u.1 j
  · simpa only [coordinateGapValueMap, coordinateShift] using
      hasDerivAt_coordinateGapValue_coordinateShift hAB u g j x
lemma eventually_coordinateShift_mem_endpointNodeSpace {d : ℕ}
    {A B : ℝ}
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) (j : Fin d) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      coordinateShift u.1 j s ∈ endpointNodeSpace d A B := by
  have hmem : endpointNodeSpace d A B ∈ 𝓝 (coordinateShift u.1 j 0) := by
    simpa using (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  exact (hasFDerivAt_coordinateShift u.1 j).continuousAt.eventually hmem
lemma eventually_coordinateGapValue_shift_at_node {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (k : Fin (d + 2)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      coordinateGapValue A B (coordinateShift u.1 j s) g
        (endpointPoint A B (coordinateShift u.1 j s) k) =
          gapCoefficient g k := by
  filter_upwards [eventually_coordinateShift_mem_endpointNodeSpace u j] with s hs
  let v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} :=
    ⟨coordinateShift u.1 j s, hs⟩
  rw [coordinateGapValue_eq hAB v]
  exact gapPolynomial_eval_node
    (endpointArrayOfInterior hAB v).toOrderedNodes g k
lemma coordinateGapPartialPolynomial_eval_node {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (k : Fin (d + 2)) :
    (coordinateGapPartialPolynomial A B u.1 g j).eval
        (endpointPoint A B u.1 k) =
      -(coordinateNodeVelocity j k) *
        (coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 k) := by
  let t : ℝ := endpointPoint A B u.1 k
  let L := fderiv ℝ (coordinateGapValueMap A B g) (u.1, t)
  have hdiff := differentiableAt_coordinateGapValueMap hAB u g t
  have hpoint := hasDerivAt_endpointPoint_coordinateShift A B u.1 j k
  have hcurve : HasFDerivAt
      (fun s : ℝ => (coordinateShift u.1 j s,
        endpointPoint A B (coordinateShift u.1 j s) k))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (coordinateDirection j)).prod
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (coordinateNodeVelocity j k))) 0 :=
    (hasFDerivAt_coordinateShift u.1 j).prodMk hpoint.hasFDerivAt
  have hbase : (coordinateShift u.1 j 0,
      endpointPoint A B (coordinateShift u.1 j 0) k) = (u.1, t) := by
    simp [t]
  have hFbase : HasFDerivAt (coordinateGapValueMap A B g) L
      (coordinateShift u.1 j 0,
        endpointPoint A B (coordinateShift u.1 j 0) k) := by
    rw [hbase]
    exact hdiff.hasFDerivAt
  have hcomp := hFbase.comp 0 hcurve
  have hevent :
      (fun s => coordinateGapValueMap A B g
        (coordinateShift u.1 j s,
          endpointPoint A B (coordinateShift u.1 j s) k)) =ᶠ[𝓝 0]
      (fun _ => gapCoefficient g k) := by
    exact eventually_coordinateGapValue_shift_at_node hAB u g j k
  have hzero : HasFDerivAt
      (fun s => coordinateGapValueMap A B g
        (coordinateShift u.1 j s,
          endpointPoint A B (coordinateShift u.1 j s) k))
      (0 : ℝ →L[ℝ] ℝ) 0 := by
    exact (hasFDerivAt_const (x := (0 : ℝ))
      (c := gapCoefficient g k)).congr_of_eventuallyEq hevent
  have hmaps := hcomp.unique hzero
  have happly := congrArg (fun M : ℝ →L[ℝ] ℝ => M 1) hmaps
  have hhorizontal := coordinateGapValueMap_fderiv_horizontal_explicit
    hAB u g j t
  have hverticalMap := coordinateGapValueMap_fderiv_vertical hAB u g t
  have hvertical := congrArg (fun M : ℝ →L[ℝ] ℝ =>
    M (coordinateNodeVelocity j k)) hverticalMap
  change L (coordinateDirection j, 0) =
      (coordinateGapPartialPolynomial A B u.1 g j).eval t at hhorizontal
  change L (0, coordinateNodeVelocity j k) =
      coordinateNodeVelocity j k *
        coordinateCriticalValue A B u.1 g t at hvertical
  have hsplit : L (coordinateDirection j, coordinateNodeVelocity j k) =
      L (coordinateDirection j, 0) +
        L (0, coordinateNodeVelocity j k) := by
    calc
      L (coordinateDirection j, coordinateNodeVelocity j k) =
          L ((coordinateDirection j, 0) +
            (0, coordinateNodeVelocity j k)) := by congr <;> simp
      _ = _ := map_add L _ _
  have happly' : L (coordinateDirection j, coordinateNodeVelocity j k) = 0 := by
    simpa using happly
  rw [hsplit, hhorizontal, hvertical] at happly'
  rw [coordinateCriticalValue] at happly'
  change (coordinateGapPartialPolynomial A B u.1 g j).eval t =
    -(coordinateNodeVelocity j k) *
      (coordinateGapPolynomial A B u.1 g).derivative.eval t
  linarith
lemma degree_coordinateLagrangeFactorPolynomial_le_one {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (k i : Fin (d + 2)) :
    (coordinateLagrangeFactorPolynomial A B u k i).degree ≤ 1 := by
  unfold coordinateLagrangeFactorPolynomial
  have hc : (C (endpointPoint A B u k - endpointPoint A B u i)⁻¹ :
      ℝ[X]).degree ≤ 0 := degree_C_le
  exact (degree_mul_le _ _).trans <| by
    simpa using add_le_add
      (degree_X_sub_C_le (R := ℝ) (endpointPoint A B u i)) hc
lemma degree_coordinateLagrangeFactorPartialPolynomial_le_one {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (j : Fin d)
    (k i : Fin (d + 2)) :
    (coordinateLagrangeFactorPartialPolynomial A B u j k i).degree ≤ 1 := by
  unfold coordinateLagrangeFactorPartialPolynomial
  apply (degree_mul_le _ _).trans
  have hcvel : (C (coordinateNodeVelocity j k -
      coordinateNodeVelocity j i) : ℝ[X]).degree ≤ 0 := degree_C_le
  have hmul : ((X - C (endpointPoint A B u i)) *
      C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)).degree ≤ 1 :=
    (degree_mul_le _ _).trans <| by
      simpa using add_le_add
        (degree_X_sub_C_le (R := ℝ) (endpointPoint A B u i)) hcvel
  have hcfirst : (C (-(coordinateNodeVelocity j i) *
      (endpointPoint A B u k - endpointPoint A B u i)) : ℝ[X]).degree ≤ 0 :=
    degree_C_le
  have hsub : (C (-(coordinateNodeVelocity j i) *
        (endpointPoint A B u k - endpointPoint A B u i)) -
      (X - C (endpointPoint A B u i)) *
        C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)).degree ≤ 1 :=
    (degree_sub_le _ _).trans <| by
      exact max_le (hcfirst.trans (by simp)) hmul
  have hclast :
      (C (((endpointPoint A B u k - endpointPoint A B u i) ^ 2)⁻¹) :
        ℝ[X]).degree ≤ 0 := degree_C_le
  simpa using add_le_add hsub hclast
lemma degree_coordinateLagrangePartialPolynomial_le {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) :
    (coordinateLagrangePartialPolynomial A B u j k).degree ≤
      (d + 1 : ℕ) := by
  classical
  unfold coordinateLagrangePartialPolynomial
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i hi
  apply (degree_mul_le _ _).trans
  have hcard : ((Finset.univ.erase k).erase i).card = d := by
    rw [Finset.card_erase_of_mem hi,
      Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hprod :
      (∏ m ∈ (Finset.univ.erase k).erase i,
        coordinateLagrangeFactorPolynomial A B u k m).degree ≤ (d : ℕ) := by
    apply (degree_prod_le _ _).trans
    calc
      (∑ m ∈ (Finset.univ.erase k).erase i,
          (coordinateLagrangeFactorPolynomial A B u k m).degree) ≤
          ∑ _m ∈ (Finset.univ.erase k).erase i, (1 : WithBot ℕ) :=
        Finset.sum_le_sum fun m _ =>
          degree_coordinateLagrangeFactorPolynomial_le_one A B u k m
      _ = (d : ℕ) := by simp [hcard]
  simpa [Nat.cast_add, Nat.cast_one, add_comm] using
    add_le_add
      (degree_coordinateLagrangeFactorPartialPolynomial_le_one A B u j k i)
      hprod
lemma degree_coordinateGapPartialPolynomial_lt {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (j : Fin d) :
    (coordinateGapPartialPolynomial A B u g j).degree < (d + 2 : ℕ) := by
  classical
  unfold coordinateGapPartialPolynomial
  have hle : (∑ k : Fin (d + 2), C (gapCoefficient g k) *
      coordinateLagrangePartialPolynomial A B u j k).degree ≤
      (d + 1 : ℕ) := by
    apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro k _
    apply (degree_mul_le _ _).trans
    have hc : (C (gapCoefficient g k) : ℝ[X]).degree ≤ 0 := degree_C_le
    simpa using add_le_add hc
      (degree_coordinateLagrangePartialPolynomial_le A B u j k)
  exact hle.trans_lt (by
    rw [Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe]
    omega)
lemma coordinateGapPartialPolynomial_eq_sourceSensitivity {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) :
    coordinateGapPartialPolynomial A B u.1 g j =
      C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
        (endpointPoint A B u.1 (interiorNodeIndex j))) *
        coordinateLagrangePolynomial A B u.1 (interiorNodeIndex j) := by
  classical
  let rhs : ℝ[X] :=
    C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
      (endpointPoint A B u.1 (interiorNodeIndex j))) *
      coordinateLagrangePolynomial A B u.1 (interiorNodeIndex j)
  have hdegLeft : (coordinateGapPartialPolynomial A B u.1 g j).degree <
      ((Finset.univ : Finset (Fin (d + 2))).card : ℕ) := by
    simpa using degree_coordinateGapPartialPolynomial_lt A B u.1 g j
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    (endpointPoint_strictMono hAB.2.1 u.2).injective.injOn hdegLeft
  · have hbasis := Lagrange.degree_basis
      (s := Finset.univ) (v := (endpointArrayOfInterior hAB u).point)
      (endpointArrayOfInterior hAB u).injective.injOn
      (Finset.mem_univ (interiorNodeIndex j))
    have hcoord : (coordinateLagrangePolynomial A B u.1
        (interiorNodeIndex j)).degree = (d + 1 : ℕ) := by
      rw [coordinateLagrangePolynomial_eq hAB u, lagrangeBasis]
      simpa using hbasis
    have hright : rhs.degree < (d + 2 : ℕ) := by
      unfold rhs
      apply (degree_mul_le _ _).trans_lt
      have hc : (C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 (interiorNodeIndex j))) : ℝ[X]).degree ≤ 0 :=
        degree_C_le
      calc
        (C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
              (endpointPoint A B u.1 (interiorNodeIndex j)))).degree +
            (coordinateLagrangePolynomial A B u.1
              (interiorNodeIndex j)).degree ≤
            0 + (d + 1 : ℕ) := add_le_add hc hcoord.le
        _ < (d + 2 : ℕ) := by
          rw [zero_add, Nat.cast_withBot, Nat.cast_withBot,
            WithBot.coe_lt_coe]
          omega
    simpa only [Finset.card_univ, Fintype.card_fin] using hright
  · intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      coordinateGapPartialPolynomial_eval_node hAB u g j k]
    by_cases hk : k = interiorNodeIndex j
    · subst k
      simp only [coordinateNodeVelocity]
      rw [coordinateLagrangePolynomial_eq hAB u]
      change _ = _ *
        (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j)).eval
            ((endpointArrayOfInterior hAB u).point (interiorNodeIndex j))
      rw [lagrangeBasis_eval_self, mul_one]
      norm_num
    · rw [show coordinateNodeVelocity j k = 0 by
        simp [coordinateNodeVelocity, hk]]
      simp only [neg_zero, zero_mul]
      rw [coordinateLagrangePolynomial_eq hAB u]
      have heval :
          (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
            (interiorNodeIndex j)).eval
              ((endpointArrayOfInterior hAB u).point k) = 0 :=
        lagrangeBasis_eval_of_ne _ hk
      change 0 = _ *
        (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j)).eval
            ((endpointArrayOfInterior hAB u).point k)
      rw [heval, mul_zero]
lemma coordinateGapValueMap_fderiv_horizontal_source {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)
        (coordinateDirection j, 0) =
      -(coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 (interiorNodeIndex j)) *
        (coordinateLagrangePolynomial A B u.1
          (interiorNodeIndex j)).eval x := by
  rw [coordinateGapValueMap_fderiv_horizontal_explicit hAB u g j x,
    coordinateGapPartialPolynomial_eq_sourceSensitivity hAB u g j,
    Polynomial.eval_mul, Polynomial.eval_C]
def concreteGapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : GapCoordinateDerivativesAt hAB u g where
  criticalDifferential := fderiv ℝ (coordinateCriticalMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  valueDifferential := fderiv ℝ (coordinateGapValueMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  hasFDerivAt_critical :=
    ((contDiffAt_coordinateCriticalMap hAB u g
      (coordinateGapArgmax hAB u g) 1).differentiableAt
        (by norm_num)).hasFDerivAt
  contDiffAt_critical :=
    contDiffAt_coordinateCriticalMap hAB u g
      (coordinateGapArgmax hAB u g) 1
  critical_vertical := by
    rw [coordinateCriticalMap_fderiv_vertical hAB u g
      (coordinateGapArgmax hAB u g)]
    rw [coordinateGapPolynomial_eq hAB u]
    rfl
  hasFDerivAt_value :=
    (differentiableAt_coordinateGapValueMap hAB u g
      (coordinateGapArgmax hAB u g)).hasFDerivAt
  value_vertical := by
    rw [coordinateGapValueMap_fderiv_vertical hAB u g
      (coordinateGapArgmax hAB u g)]
    have hcrit : coordinateCriticalValue A B u.1 g
        (coordinateGapArgmax hAB u g) = 0 := by
      by_cases hd : d = 0
      · subst d
        exact coordinateCriticalValue_zero_dim hAB u g _
      · exact coordinateCriticalMap_eq_zero hAB u
          (Nat.one_le_iff_ne_zero.mpr hd) g
    rw [hcrit]
    ext
    simp
  value_horizontal_sensitivity := by
    intro j
    change fderiv ℝ (coordinateGapValueMap A B g)
      (u.1, coordinateGapArgmax hAB u g) (Pi.single j 1, 0) = _
    rw [show Pi.single j 1 = coordinateDirection j by rfl,
      coordinateGapValueMap_fderiv_horizontal_source hAB u g j
        (coordinateGapArgmax hAB u g)]
    rw [coordinateGapPolynomial_eq hAB u,
      coordinateLagrangePolynomial_eq hAB u, lagrangeBasis_eval]
    rfl
def canonicalExtendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) : (Fin d → ℝ) → ℝ :=
  extendedCoordinateGapHeight hAB u hd g
    (concreteGapCoordinateDerivativesAt hAB u g)
theorem hasFDerivAt_canonicalExtendedCoordinateGapHeight {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    HasFDerivAt (canonicalExtendedCoordinateGapHeight hAB u hd g)
      ((concreteGapCoordinateDerivativesAt hAB u g).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 :=
  hasFDerivAt_extendedCoordinateGapHeight hAB u hd g
    (concreteGapCoordinateDerivativesAt hAB u g)
theorem canonicalCoordinateGapHeight_fderiv_basis_eq_model {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) (j : Fin d) :
    fderiv ℝ (canonicalExtendedCoordinateGapHeight hAB u hd g) u.1
        (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) g j := by
  rw [(hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd g).fderiv]
  exact ((concreteGapCoordinateDerivativesAt hAB u g).value_horizontal_sensitivity
    j).trans
      (gapHeightJacobianModel_apply_eq
        (endpointArrayOfInterior hAB u) g j).symm
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Polynomial
open scoped BigOperators
noncomputable section
private theorem eq_zero_of_eval_mul_next_neg {d : ℕ} (p : ℝ[X])
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hdegree : p.natDegree < d)
    (hsign : ∀ j : Fin d,
      p.eval (τ j.castSucc) * p.eval (τ j.succ) < 0) :
    p = 0 := by
  classical
  have hexists (j : Fin d) :
      ∃ x ∈ Set.Ioo (τ j.castSucc) (τ j.succ), p.eval x = 0 := by
    have hab : τ j.castSucc ≤ τ j.succ :=
      (hτ Fin.castSucc_lt_succ).le
    have hcont : ContinuousOn (fun x => p.eval x)
        (Set.Icc (τ j.castSucc) (τ j.succ)) :=
      p.continuous.continuousOn
    rcases mul_neg_iff.mp (hsign j) with hj | hj
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (τ j.succ))
          (p.eval (τ j.castSucc)) := ⟨hj.2, hj.1⟩
      exact intermediate_value_Ioo' hab hcont hz
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (τ j.castSucc))
          (p.eval (τ j.succ)) := hj
      exact intermediate_value_Ioo hab hcont hz
  let r : Fin d → ℝ := fun j => Classical.choose (hexists j)
  have hr_mem (j : Fin d) : r j ∈ Set.Ioo (τ j.castSucc) (τ j.succ) :=
    (Classical.choose_spec (hexists j)).1
  have hr_eval (j : Fin d) : p.eval (r j) = 0 :=
    (Classical.choose_spec (hexists j)).2
  have hr_strictMono : StrictMono r := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by omega
    have hmiddle : τ i.succ ≤ τ j.castSucc := by
      apply hτ.monotone
      exact Fin.le_iff_val_le_val.mpr (by simpa using hij')
    exact ((hr_mem i).2.trans_le hmiddle).trans (hr_mem j).1
  let s : Finset ℝ := Finset.univ.image r
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hr_strictMono.injective,
      Finset.card_univ, Fintype.card_fin]
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
  · rw [hs_card]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr hdegree)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    exact hr_eval j
private lemma ordered_gap_nodalProduct_sign {n : ℕ} (t : Fin n → ℝ)
    (ht : StrictMono t) (g : Fin (n - 1)) {x : ℝ}
    (hx : t (gapLeftIndex g) < x ∧ x < t (gapRightIndex g)) :
    0 < (-1 : ℝ) ^ (n - 1 - g.val) * ∏ k : Fin n, (x - t k) := by
  classical
  let L : Finset (Fin n) := Finset.Iic (gapLeftIndex g)
  let U : Finset (Fin n) := Finset.Ioi (gapLeftIndex g)
  have hdis : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkU
    have hkle : k ≤ gapLeftIndex g := by simpa [L] using hkL
    have hgk : gapLeftIndex g < k := by simpa [U] using hkU
    exact (not_lt_of_ge hkle) hgk
  have hunion : L ∪ U = Finset.univ := by
    ext k
    simp only [L, U, Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi,
      Finset.mem_univ, iff_true]
    exact le_or_gt k (gapLeftIndex g)
  have hleft : 0 < ∏ k ∈ L, (x - t k) := by
    apply Finset.prod_pos
    intro k hk
    have hkle : k ≤ gapLeftIndex g := by simpa [L] using hk
    exact sub_pos.mpr ((ht.monotone hkle).trans_lt hx.1)
  have hright : 0 < ∏ k ∈ U, (t k - x) := by
    apply Finset.prod_pos
    intro k hk
    have hgk : gapLeftIndex g < k := by simpa [U] using hk
    have hright_le : gapRightIndex g ≤ k := by
      apply Fin.le_iff_val_le_val.mpr
      change g.val + 1 ≤ k.val
      change g.val < k.val at hgk
      omega
    exact sub_pos.mpr (hx.2.trans_le (ht.monotone hright_le))
  have hprod : (∏ k : Fin n, (x - t k)) =
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (x - t k) := by
    rw [← Finset.prod_union hdis, hunion]
  have hright_sign : (∏ k ∈ U, (x - t k)) =
      (-1 : ℝ) ^ U.card * ∏ k ∈ U, (t k - x) := by
    simpa only [neg_sub] using
      (Finset.prod_neg (s := U) (fun k => t k - x))
  have hcard : U.card = n - 1 - g.val := by
    simp [U, gapLeftIndex_val]
  let s : ℝ := (-1 : ℝ) ^ (n - 1 - g.val)
  have hs : s ^ 2 = 1 := sq_negOnePow (n - 1 - g.val)
  have hboth : 0 <
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (t k - x) :=
    mul_pos hleft hright
  rw [hprod, hright_sign, hcard]
  change 0 < s * ((∏ k ∈ L, (x - t k)) *
    (s * ∏ k ∈ U, (t k - x)))
  rw [show s * ((∏ k ∈ L, (x - t k)) *
      (s * ∏ k ∈ U, (t k - x))) =
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (t k - x) by
    calc
      s * ((∏ k ∈ L, (x - t k)) *
          (s * ∏ k ∈ U, (t k - x))) =
          s ^ 2 * ((∏ k ∈ L, (x - t k)) *
            ∏ k ∈ U, (t k - x)) := by ring
      _ = _ := by rw [hs, one_mul]]
  exact hboth
private lemma ordered_basisDenominator_sign {n : ℕ} (t : Fin n → ℝ)
    (ht : StrictMono t) (r : Fin n) :
    0 < (-1 : ℝ) ^ (n - 1 - r.val) *
      ∏ k ∈ Finset.univ.erase r, (t r - t k) := by
  classical
  let L : Finset (Fin n) := Finset.Iio r
  let U : Finset (Fin n) := Finset.Ioi r
  have hdis : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkU
    have hkr : k < r := by simpa [L] using hkL
    have hrk : r < k := by simpa [U] using hkU
    exact (not_lt_of_ge hkr.le) hrk
  have hunion : L ∪ U = Finset.univ.erase r := by
    ext k
    simp only [L, U, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h
      rcases h with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h
    · intro h
      exact lt_or_gt_of_ne h
  have hleft : 0 < ∏ k ∈ L, (t r - t k) := by
    apply Finset.prod_pos
    intro k hk
    exact sub_pos.mpr (ht (by simpa [L] using hk))
  have hright : 0 < ∏ k ∈ U, (t k - t r) := by
    apply Finset.prod_pos
    intro k hk
    exact sub_pos.mpr (ht (by simpa [U] using hk))
  have hprod : (∏ k ∈ Finset.univ.erase r, (t r - t k)) =
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t r - t k) := by
    rw [← Finset.prod_union hdis, hunion]
  have hright_sign : (∏ k ∈ U, (t r - t k)) =
      (-1 : ℝ) ^ U.card * ∏ k ∈ U, (t k - t r) := by
    simpa only [neg_sub] using
      (Finset.prod_neg (s := U) (fun k => t k - t r))
  have hcard : U.card = n - 1 - r.val := by simp [U]
  let s : ℝ := (-1 : ℝ) ^ (n - 1 - r.val)
  have hs : s ^ 2 = 1 := sq_negOnePow (n - 1 - r.val)
  have hboth : 0 <
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t k - t r) :=
    mul_pos hleft hright
  rw [hprod, hright_sign, hcard]
  change 0 < s * ((∏ k ∈ L, (t r - t k)) *
    (s * ∏ k ∈ U, (t k - t r)))
  rw [show s * ((∏ k ∈ L, (t r - t k)) *
      (s * ∏ k ∈ U, (t k - t r))) =
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t k - t r) by
    calc
      s * ((∏ k ∈ L, (t r - t k)) *
          (s * ∏ k ∈ U, (t k - t r))) =
          s ^ 2 * ((∏ k ∈ L, (t r - t k)) *
            ∏ k ∈ U, (t k - t r)) := by ring
      _ = _ := by rw [hs, one_mul]]
  exact hboth
private lemma endpointPoint_eq_endpointArray_point {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (k : Fin (d + 2)) :
    endpointPoint A B nodes.interior k = nodes.point k := by
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  have harr := endpointArrayOfInterior_interior nodes.admissibleInterval nodes
  have hpoint := congrArg (fun z : EndpointArray d A B => z.point k) harr
  exact hpoint
theorem gapJacobianRowFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ (d + 1 - g.val) * gapJacobianRowFactor nodes g := by
  rw [gapJacobianRowFactor, coordinateNodalValue]
  simp_rw [endpointPoint_eq_endpointArray_point nodes]
  have h := ordered_gap_nodalProduct_sign nodes.point nodes.strictMono g
    (gapArgmax_mem_openGap nodes.toOrderedNodes (by omega) g)
  simpa using h
theorem gapJacobianColumnFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    0 < (-1 : ℝ) ^ (d - j.val) * gapJacobianColumnFactor nodes j := by
  have hden := ordered_basisDenominator_sign nodes.point nodes.strictMono
    (interiorNodeIndex j)
  have hden' : 0 < (-1 : ℝ) ^ (d - j.val) *
      coordinateBasisDenominator A B nodes.interior j := by
    rw [coordinateBasisDenominator]
    simp_rw [endpointPoint_eq_endpointArray_point nodes]
    have hexp : d + 2 - 1 - (interiorNodeIndex j).val = d - j.val := by
      simp only [interiorNodeIndex_val]
      omega
    rw [hexp] at hden
    exact hden
  rw [gapJacobianColumnFactor]
  rcases neg_one_pow_eq_or ℝ (d - j.val) with hs | hs
  · rw [hs] at hden' ⊢
    simp only [one_mul] at hden' ⊢
    exact inv_pos.mpr hden'
  · rw [hs] at hden' ⊢
    simp only [neg_one_mul] at hden' ⊢
    have hneg : coordinateBasisDenominator A B nodes.interior j < 0 := by
      linarith
    exact neg_pos.mpr (inv_lt_zero.mpr hneg)
def heightMinorFactorParity (d : ℕ) (omitted : Fin (d + 1)) : ℝ :=
  (∏ i : Fin d, (-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val)) *
    ∏ j : Fin d, (-1 : ℝ) ^ (d - j.val)
lemma heightMinorFactorParity_eq_negOnePow (d : ℕ)
    (omitted : Fin (d + 1)) :
    heightMinorFactorParity d omitted = (-1 : ℝ) ^ omitted.val := by
  classical
  let S : Finset (Fin d) :=
    Finset.univ.filter fun i => i.castSucc < omitted
  have hcard : S.card = omitted.val := by
    calc
      S.card = (Finset.Iio omitted).card := by
        apply Finset.card_bij (fun i _hi => i.castSucc)
        · intro i hi
          simpa [S] using (Finset.mem_filter.mp hi).2
        · intro i _hi j _hj hij
          exact Fin.castSucc_inj.mp hij
        · intro k hk
          have hko : k < omitted := by simpa using hk
          let i : Fin d := ⟨k.val, by
            have ho : omitted.val ≤ d := by omega
            exact lt_of_lt_of_le (Fin.lt_def.mp hko) ho⟩
          refine ⟨i, ?_, ?_⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ i, by simpa [i] using hko⟩
          · ext
            rfl
      _ = omitted.val := Fin.card_Iio omitted
  rw [heightMinorFactorParity, ← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin d,
        (-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val) *
          (-1 : ℝ) ^ (d - i.val)) =
        ∏ i : Fin d, if i.castSucc < omitted then (-1 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hio : i.castSucc < omitted
      · rw [if_pos hio, Fin.succAbove_of_castSucc_lt omitted i hio]
        simp only [Fin.val_castSucc]
        have hexp : d + 1 - i.val = (d - i.val) + 1 := by omega
        rw [hexp, pow_succ]
        have hs := sq_negOnePow (d - i.val)
        nlinarith
      · have hoi : omitted ≤ i.castSucc := le_of_not_gt hio
        rw [if_neg hio, Fin.succAbove_of_le_castSucc omitted i hoi]
        simp only [Fin.val_succ]
        have hexp : d + 1 - (i.val + 1) = d - i.val := by omega
        rw [hexp]
        simpa only [pow_two] using sq_negOnePow (d - i.val)
    _ = (-1 : ℝ) ^ S.card := by
      rw [← Finset.prod_filter (s := Finset.univ)
        (fun i : Fin d => i.castSucc < omitted) (fun _ => (-1 : ℝ))]
      change (∏ _i ∈ S, (-1 : ℝ)) = (-1 : ℝ) ^ S.card
      simp
    _ = (-1 : ℝ) ^ omitted.val := by rw [hcard]
def sourceQuotientNormalizer {m : ℕ} (i : Fin (m + 1)) : ℝ :=
  if i = 0 then -1 else (-1 : ℝ) ^ i.val
lemma sourceQuotientNormalizer_ne_zero {m : ℕ} (i : Fin (m + 1)) :
    sourceQuotientNormalizer i ≠ 0 := by
  rw [sourceQuotientNormalizer]
  split
  · norm_num
  · exact pow_ne_zero _ (by norm_num)
lemma sourceQuotientNormalizer_sq {m : ℕ} (i : Fin (m + 1)) :
    sourceQuotientNormalizer i ^ 2 = 1 := by
  rw [sourceQuotientNormalizer]
  split
  · norm_num
  · exact sq_negOnePow i.val
def sourceNormalizedQuotient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (i : Fin (d + 1)) : ℝ[X] :=
  C (sourceQuotientNormalizer i) *
    gapDerivativeQuotient nodes.toOrderedNodes i
lemma natDegree_sourceNormalizedQuotient_le {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) (i : Fin (d + 1)) :
    (sourceNormalizedQuotient nodes i).natDegree ≤ d - 1 := by
  have hq := natDegree_gapDerivativeQuotient_le_sub_three
    (n := d + 2) nodes.toOrderedNodes (by omega) i
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by omega)
lemma sourceNormalizedQuotient_eval_first_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    0 < (sourceNormalizedQuotient nodes i).eval
      (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  by_cases hi : i = 0
  · subst i
    simpa [sourceNormalizedQuotient, sourceQuotientNormalizer]
      using neg_pos.mpr (htable.1 ⟨0, by omega⟩)
  · have h := htable.2 i ⟨0, by omega⟩ hi
    simpa [sourceNormalizedQuotient, sourceQuotientNormalizer, hi,
      Polynomial.eval_mul, Polynomial.eval_C] using h
lemma sourceNormalizedQuotient_first_eval_later_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (j : Fin (d + 1)) (hj : j ≠ 0) :
    0 < (-1 : ℝ) ^ (j.val + 1) *
      (sourceNormalizedQuotient nodes 0).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  have h := htable.2 ⟨0, by omega⟩ j hj.symm
  simpa [sourceNormalizedQuotient, sourceQuotientNormalizer,
    Polynomial.eval_mul, Polynomial.eval_C, pow_succ] using h
lemma sourceNormalizedQuotient_offDiagonal_eval_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (i j : Fin (d + 1)) (hi : i ≠ 0) (hij : i ≠ j) :
    0 < (-1 : ℝ) ^ j.val *
      (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  have h := htable.2 i j hij
  simpa [sourceNormalizedQuotient, sourceQuotientNormalizer, hi,
    Polynomial.eval_mul, Polynomial.eval_C, pow_add, mul_assoc,
    mul_left_comm, mul_comm] using h
private def negativeLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => a i < 0
private def positiveLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => 0 < a i
private lemma sum_eq_first_add_negative_add_positive {d : ℕ}
    (a v : Fin (d + 1) → ℝ) :
    (∑ i, a i * v i) =
      a 0 * v 0 +
        ∑ i ∈ negativeLaterIndices a, a i * v i +
          ∑ i ∈ positiveLaterIndices a, a i * v i := by
  classical
  let I : Finset (Fin (d + 1)) := Finset.univ.erase 0
  let N := negativeLaterIndices a
  let P := positiveLaterIndices a
  have hNsub : N ⊆ I := Finset.filter_subset _ _
  have hPsub : P ⊆ I := Finset.filter_subset _ _
  have hdis : Disjoint N P := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiN hiP
    have hneg : a i < 0 := (Finset.mem_filter.mp hiN).2
    have hpos : 0 < a i := (Finset.mem_filter.mp hiP).2
    linarith
  have hcover :
      (∑ i ∈ N ∪ P, a i * v i) = ∑ i ∈ I, a i * v i := by
    apply Finset.sum_subset (Finset.union_subset hNsub hPsub)
    intro i hiI hiNP
    have hiN : i ∉ N := fun h => hiNP (Finset.mem_union_left P h)
    have hiP : i ∉ P := fun h => hiNP (Finset.mem_union_right N h)
    have hnneg : ¬a i < 0 := by
      intro h
      exact hiN (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hnpos : ¬0 < a i := by
      intro h
      exact hiP (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hai : a i = 0 := le_antisymm (le_of_not_gt hnpos) (le_of_not_gt hnneg)
    simp [hai]
  rw [Finset.sum_union hdis] at hcover
  have herase := Finset.sum_erase_add Finset.univ (fun i => a i * v i)
    (Finset.mem_univ (0 : Fin (d + 1)))
  change (∑ i ∈ I, a i * v i) + a 0 * v 0 = ∑ i, a i * v i at herase
  rw [← herase, ← hcover]
  dsimp only [N, P]
  ring
theorem sourceNormalizedQuotient_relation_sign_pattern {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ)
    (hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0)
    (ha : a ≠ 0) :
    (0 < a 0 ∧ ∀ i, i ≠ 0 → a i < 0) ∨
      (a 0 < 0 ∧ ∀ i, i ≠ 0 → 0 < a i) := by
  classical
  let orient : ℝ := if 0 ≤ a 0 then 1 else -1
  let b : Fin (d + 1) → ℝ := fun i => orient * a i
  have horient : orient = 1 ∨ orient = -1 := by
    dsimp [orient]
    split <;> simp
  have horient_ne : orient ≠ 0 := by
    rcases horient with h | h <;> rw [h] <;> norm_num
  have hbfirst : 0 ≤ b 0 := by
    dsimp [b, orient]
    split_ifs with h
    · simpa using h
    · have hlt : a 0 < 0 := lt_of_not_ge h
      simp only [neg_one_mul]
      exact neg_nonneg.mpr hlt.le
  have hbne : b ≠ 0 := by
    intro hb
    apply ha
    funext i
    have hi := congrFun hb i
    dsimp [b] at hi
    exact (mul_eq_zero.mp hi).resolve_left horient_ne
  have hbrel : (∑ i, C (b i) * sourceNormalizedQuotient nodes i) = 0 := by
    calc
      (∑ i, C (b i) * sourceNormalizedQuotient nodes i) =
          C orient * (∑ i, C (a i) * sourceNormalizedQuotient nodes i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [b, map_mul]
            ring
      _ = 0 := by rw [hrel, mul_zero]
  have hbrel_eval (x : ℝ) :
      (∑ i, b i * (sourceNormalizedQuotient nodes i).eval x) = 0 := by
    have h := congrArg (Polynomial.eval x) hbrel
    simpa only [Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_zero] using h
  let N := negativeLaterIndices b
  let P := positiveLaterIndices b
  have hN : N.Nonempty := by
    by_contra hNempty
    rw [Finset.not_nonempty_iff_eq_empty] at hNempty
    have hbnonneg (i : Fin (d + 1)) : 0 ≤ b i := by
      by_cases hi : i = 0
      · simpa [hi] using hbfirst
      · apply le_of_not_gt
        intro hneg
        have hiN : i ∈ N := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hneg⟩
        rw [hNempty] at hiN
        simp at hiN
    obtain ⟨i, hbi⟩ := Function.ne_iff.mp hbne
    have hbipos : 0 < b i := lt_of_le_of_ne (hbnonneg i) (Ne.symm hbi)
    have hterm_nonneg (k : Fin (d + 1)) :
        0 ≤ b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) :=
      mul_nonneg (hbnonneg k)
        (sourceNormalizedQuotient_eval_first_pos nodes (by omega) k).le
    have hterm_pos :
        0 < b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) :=
      mul_pos hbipos
        (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
    have hsumpos : 0 <
        ∑ k, b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
      rw [Finset.sum_pos_iff_of_nonneg (fun k _hk => hterm_nonneg k)]
      exact ⟨i, Finset.mem_univ i, hterm_pos⟩
    rw [hbrel_eval] at hsumpos
    exact (lt_irrefl 0) hsumpos
  let f : ℝ[X] := C (b 0) * sourceNormalizedQuotient nodes 0 +
    ∑ i ∈ N, C (b i) * sourceNormalizedQuotient nodes i
  have hf_eval (x : ℝ) : f.eval x =
      b 0 * (sourceNormalizedQuotient nodes 0).eval x +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval x := by
    simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_finset_sum]
  have hf_eval_eq_neg_pos (x : ℝ) : f.eval x =
      -∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval x := by
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => (sourceNormalizedQuotient nodes i).eval x)
    have hzero := hbrel_eval x
    change (∑ i, b i * (sourceNormalizedQuotient nodes i).eval x) =
      b 0 * (sourceNormalizedQuotient nodes 0).eval x +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval x +
          ∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval x at hsplit
    rw [hf_eval]
    linarith
  have hNmem {i : Fin (d + 1)} (hi : i ∈ N) : i ≠ 0 ∧ b i < 0 := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hPmem {i : Fin (d + 1)} (hi : i ∈ P) : i ≠ 0 ∧ 0 < b i := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hfzero : f = 0 := by
    by_cases hP : P.Nonempty
    · have hf_sign (j : Fin (d + 1)) :
          0 < (-1 : ℝ) ^ (j.val + 1) * f.eval
            (gapArgmax nodes.toOrderedNodes j) := by
        by_cases hj0 : j = 0
        · subst j
          have hsumpos : 0 < ∑ i ∈ P,
              b i * (sourceNormalizedQuotient nodes i).eval
                (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
            apply Finset.sum_pos
            · intro i hi
              exact mul_pos (hPmem hi).2
                (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
            · exact hP
          rw [hf_eval_eq_neg_pos]
          simpa using hsumpos
        · by_cases hjP : j ∈ P
          · have hfirst : 0 ≤
                b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                  (sourceNormalizedQuotient nodes 0).eval
                    (gapArgmax nodes.toOrderedNodes j)) :=
              mul_nonneg hbfirst
                (sourceNormalizedQuotient_first_eval_later_sign
                  nodes (by omega) j hj0).le
            have hNsum : 0 < ∑ i ∈ N,
                (-1 : ℝ) ^ (j.val + 1) *
                  (b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j)) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hNmem hi).1
                have hibneg := (hNmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  linarith [hibneg, (hPmem hjP).2]
                have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
                  nodes (by omega) i j hine hij
                calc
                  0 < (-b i) * ((-1 : ℝ) ^ j.val *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) :=
                    mul_pos (neg_pos.mpr hibneg) hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (b i * (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := by
                    rw [pow_succ]
                    ring
              · exact hN
            rw [hf_eval]
            calc
              0 < b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                    (sourceNormalizedQuotient nodes 0).eval
                      (gapArgmax nodes.toOrderedNodes j)) +
                  ∑ i ∈ N, (-1 : ℝ) ^ (j.val + 1) *
                    (b i * (sourceNormalizedQuotient nodes i).eval
                      (gapArgmax nodes.toOrderedNodes j)) :=
                add_pos_of_nonneg_of_pos hfirst hNsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (b 0 * (sourceNormalizedQuotient nodes 0).eval
                      (gapArgmax nodes.toOrderedNodes j) +
                    ∑ i ∈ N, b i *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := by
                rw [← Finset.mul_sum]
                ring
          · have hjnotpos : ¬0 < b j := by
              intro hjpos
              exact hjP (Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩, hjpos⟩)
            have hPsum : 0 < ∑ i ∈ P,
                (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j))) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hPmem hi).1
                have hibpos := (hPmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  exact hjnotpos hibpos
                have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
                  nodes (by omega) i j hine hij
                calc
                  0 < b i * ((-1 : ℝ) ^ j.val *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := mul_pos hibpos hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (-(b i * (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j))) := by
                    rw [pow_succ]
                    ring
              · exact hP
            rw [hf_eval_eq_neg_pos]
            calc
              0 < ∑ i ∈ P, (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j))) := hPsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (-∑ i ∈ P, b i *
                    (sourceNormalizedQuotient nodes i).eval
                      (gapArgmax nodes.toOrderedNodes j)) := by
                rw [← Finset.mul_sum]
                congr 1
                rw [← Finset.sum_neg_distrib]
      apply eq_zero_of_eval_mul_next_neg f
          (gapArgmax nodes.toOrderedNodes)
          (gapArgmax_strictMono nodes.toOrderedNodes (by omega))
      · have hfirstDegree :
            (C (b 0) * sourceNormalizedQuotient nodes 0).natDegree ≤ d - 1 :=
          (Polynomial.natDegree_C_mul_le _ _).trans
            (natDegree_sourceNormalizedQuotient_le nodes hd 0)
        have hsumDegree :
            (∑ i ∈ N, C (b i) * sourceNormalizedQuotient nodes i).natDegree ≤
              d - 1 := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro i hi
          exact (Polynomial.natDegree_C_mul_le _ _).trans
            (natDegree_sourceNormalizedQuotient_le nodes hd i)
        exact (Polynomial.natDegree_add_le _ _).trans_lt (by omega)
      · intro j
        have hleft := hf_sign j.castSucc
        have hright := hf_sign j.succ
        simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
        rw [show j.val + 1 + 1 = (j.val + 1) + 1 by omega, pow_succ] at hright
        nlinarith [sq_negOnePow (j.val + 1)]
    · apply Polynomial.funext
      have heval : ∀ x : ℝ, f.eval x = 0 := by
        intro x
        rw [hf_eval_eq_neg_pos]
        rw [Finset.not_nonempty_iff_eq_empty.mp hP]
        simp
      intro x
      simpa using heval x
  have hPempty : P = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hP
    have hsumpos : 0 < ∑ i ∈ P,
        b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
      apply Finset.sum_pos
      · intro i hi
        exact mul_pos (hPmem hi).2
          (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
      · exact hP
    have hf0 := congrArg
      (fun p : ℝ[X] => p.eval (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩)) hfzero
    have hf0' : f.eval (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) = 0 := by
      simpa only [Polynomial.eval_zero] using hf0
    rw [hf_eval_eq_neg_pos] at hf0'
    linarith
  have hblater (i : Fin (d + 1)) (hi0 : i ≠ 0) : b i ≠ 0 := by
    intro hbi
    have hiP : i ∉ P := by rw [hPempty]; simp
    have hibnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hiP (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩, hpos⟩)
    have hiN : i ∉ N := by
      intro hiN
      exact (hNmem hiN).2.ne hbi
    have hfirst : 0 ≤ b 0 * ((-1 : ℝ) ^ (i.val + 1) *
        (sourceNormalizedQuotient nodes 0).eval
          (gapArgmax nodes.toOrderedNodes i)) :=
      mul_nonneg hbfirst
        (sourceNormalizedQuotient_first_eval_later_sign
          nodes (by omega) i hi0).le
    have hNsum : 0 < ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
        (b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes i)) := by
      apply Finset.sum_pos
      · intro k hk
        have hk0 := (hNmem hk).1
        have hkbneg := (hNmem hk).2
        have hki : k ≠ i := by
          intro hki
          subst k
          exact hiN hk
        have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
          nodes (by omega) k i hk0 hki
        calc
          0 < (-b k) * ((-1 : ℝ) ^ i.val *
              (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) :=
            mul_pos (neg_pos.mpr hkbneg) hq
          _ = (-1 : ℝ) ^ (i.val + 1) *
              (b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) := by
            rw [pow_succ]
            ring
      · exact hN
    have hfpos : 0 < (-1 : ℝ) ^ (i.val + 1) *
        f.eval (gapArgmax nodes.toOrderedNodes i) := by
      rw [hf_eval]
      calc
        0 < b 0 * ((-1 : ℝ) ^ (i.val + 1) *
              (sourceNormalizedQuotient nodes 0).eval
                (gapArgmax nodes.toOrderedNodes i)) +
            ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
              (b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) :=
          add_pos_of_nonneg_of_pos hfirst hNsum
        _ = (-1 : ℝ) ^ (i.val + 1) *
            (b 0 * (sourceNormalizedQuotient nodes 0).eval
                (gapArgmax nodes.toOrderedNodes i) +
              ∑ k ∈ N, b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) := by
          rw [← Finset.mul_sum]
          ring
    rw [hfzero] at hfpos
    simp at hfpos
  have hbzero : b 0 ≠ 0 := by
    intro hb0
    have hNsumneg :
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) < 0 := by
      apply Finset.sum_neg
      · intro i hi
        exact mul_neg_of_neg_of_pos (hNmem hi).2
          (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
      · exact hN
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩))
    change (∑ i, b i * (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩)) =
      b 0 * (sourceNormalizedQuotient nodes 0).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) +
        ∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) at hsplit
    rw [hbrel_eval, hb0, hPempty] at hsplit
    simp at hsplit
    exact (ne_of_lt hNsumneg) hsplit.symm
  have hbfirstpos : 0 < b 0 := lt_of_le_of_ne hbfirst (Ne.symm hbzero)
  have hblaterneg (i : Fin (d + 1)) (hi : i ≠ 0) : b i < 0 := by
    have hnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have hiP : i ∈ P := Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hpos⟩
      rw [hPempty] at hiP
      simp at hiP
    exact lt_of_le_of_ne hnonpos (hblater i hi)
  rcases horient with horient | horient
  · left
    constructor
    · simpa [b, horient] using hbfirstpos
    · intro i hi
      simpa [b, horient] using hblaterneg i hi
  · right
    constructor
    · have := hbfirstpos
      simp only [b, horient, neg_one_mul] at this
      linarith
    · intro i hi
      have := hblaterneg i hi
      simp only [b, horient, neg_one_mul] at this
      linarith
theorem sourceNormalizedQuotient_relation_coeff_ne_zero {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ)
    (hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0)
    (ha : a ≠ 0) :
    ∀ i, a i ≠ 0 := by
  rcases sourceNormalizedQuotient_relation_sign_pattern nodes hd a hrel ha with
    h | h
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ne_of_gt h.1
    · exact ne_of_lt (h.2 i hi)
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ne_of_lt h.1
    · exact ne_of_gt (h.2 i hi)
def normalizedDeletedQuotientEvaluationMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j i => (sourceNormalizedQuotient nodes (omitted.succAbove i)).eval
    (nodes.point (interiorNodeIndex j))
theorem normalizedDeletedQuotientEvaluationMatrix_det_ne_zero {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (omitted : Fin (d + 1)) :
    (normalizedDeletedQuotientEvaluationMatrix nodes omitted).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : ℝ[X] := ∑ i : Fin d,
    C (c i) * sourceNormalizedQuotient nodes (omitted.succAbove i)
  have hpdegree : p.natDegree < d := by
    have hle : p.natDegree ≤ d - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (natDegree_sourceNormalizedQuotient_le nodes hd _)
    omega
  have hp_eval (j : Fin d) : p.eval (nodes.point (interiorNodeIndex j)) = 0 := by
    have hj := congrFun hc j
    simp only [normalizedDeletedQuotientEvaluationMatrix, Matrix.mulVec,
      dotProduct, p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Pi.zero_apply] at hj ⊢
    simpa only [mul_comm] using hj
  let s : Finset ℝ := Finset.univ.image
    (fun j : Fin d => nodes.point (interiorNodeIndex j))
  have hxinj : Function.Injective
      (fun j : Fin d => nodes.point (interiorNodeIndex j)) :=
    nodes.strictMono.injective.comp interiorNodeIndex_strictMono.injective
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ,
      Fintype.card_fin]
  have hpzero : p = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
    · rw [hs_card]
      exact Polynomial.degree_le_natDegree.trans_lt
        (WithBot.coe_lt_coe.mpr hpdegree)
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
      exact hp_eval j
  let a : Fin (d + 1) → ℝ :=
    Fin.succAboveCases (α := fun _ => ℝ) omitted 0 c
  have harel :
      (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0 := by
    rw [Fin.sum_univ_succAbove
      (fun i => C (a i) * sourceNormalizedQuotient nodes i) omitted]
    simp [a]
    exact hpzero
  have hane : a ≠ 0 := by
    intro ha
    apply hcne
    funext i
    have hi := congrFun ha (omitted.succAbove i)
    simpa [a] using hi
  have hall := sourceNormalizedQuotient_relation_coeff_ne_zero
    nodes hd a harel hane omitted
  exact hall (by simp [a])
lemma normalizedDeletedQuotientEvaluationMatrix_transpose_factorization
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B)
    (omitted : Fin (d + 1)) :
    (normalizedDeletedQuotientEvaluationMatrix nodes omitted).transpose =
      Matrix.diagonal
        (fun i => sourceQuotientNormalizer (omitted.succAbove i)) *
      (gapQuotientEvaluationMatrix nodes).submatrix omitted.succAbove id := by
  ext i j
  simp [normalizedDeletedQuotientEvaluationMatrix, sourceNormalizedQuotient,
    gapQuotientEvaluationMatrix, Matrix.diagonal_mul]
theorem deletedRowMinor_gapQuotientEvaluationMatrix_ne_zero_of_two_le
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0 := by
  have hnormalized :=
    normalizedDeletedQuotientEvaluationMatrix_det_ne_zero nodes hd omitted
  have hfactor := congrArg Matrix.det
    (normalizedDeletedQuotientEvaluationMatrix_transpose_factorization
      nodes omitted)
  rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal] at hfactor
  have hnormalizer :
      (∏ i : Fin d, sourceQuotientNormalizer (omitted.succAbove i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _hi => sourceQuotientNormalizer_ne_zero _
  rw [deletedRowMinor]
  intro hminor
  rw [hminor, mul_zero] at hfactor
  exact hnormalized hfactor
theorem quotientEvaluationMaximalMinorsNonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    QuotientEvaluationMaximalMinorsNonzero nodes := by
  intro omitted
  by_cases hd0 : d = 0
  · subst d
    simp [deletedRowMinor]
  by_cases hd1 : d = 1
  · subst d
    rw [deletedRowMinor]
    have hentry := gapDerivativeQuotient_eval_neg_of_three_nodes
      nodes.toOrderedNodes (omitted.succAbove 0)
        (nodes.point (interiorNodeIndex 0))
    simpa [gapQuotientEvaluationMatrix, Matrix.det_fin_one] using
      (ne_of_lt hentry)
  · exact deletedRowMinor_gapQuotientEvaluationMatrix_ne_zero_of_two_le
      nodes (by omega) omitted
def gapQuotientCofactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (i : Fin (d + 1)) : ℝ :=
  (-1 : ℝ) ^ i.val *
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) i
private def duplicateQuotientColumnMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases (gapQuotientEvaluationMatrix nodes i j)
    (fun k' => gapQuotientEvaluationMatrix nodes i k') k
lemma gapQuotientCofactor_evaluation_sum_eq_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    ∑ i : Fin (d + 1), gapQuotientCofactor nodes i *
      gapQuotientEvaluationMatrix nodes i j = 0 := by
  let M := duplicateQuotientColumnMatrix nodes j
  have hcols : ∀ i, M i 0 = M i j.succ := by
    intro i
    simp [M, duplicateQuotientColumnMatrix]
  have hne : (0 : Fin (d + 1)) ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hdet : M.det = 0 := Matrix.det_zero_of_column_eq hne hcols
  have hexpand := Matrix.det_succ_column M (0 : Fin (d + 1))
  rw [hdet] at hexpand
  have hminor (i : Fin (d + 1)) :
      (M.submatrix i.succAbove (0 : Fin (d + 1)).succAbove).det =
        deletedRowMinor (gapQuotientEvaluationMatrix nodes) i := by
    rw [deletedRowMinor]
    congr 1
  simp only [Fin.val_zero, Nat.add_zero, M, duplicateQuotientColumnMatrix,
    Fin.cases_zero, hminor] at hexpand
  simpa [gapQuotientCofactor, mul_assoc, mul_left_comm, mul_comm] using
    hexpand.symm
theorem gapQuotientCofactor_polynomial_relation {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) :
    (∑ i : Fin (d + 1), C (gapQuotientCofactor nodes i) *
      gapDerivativeQuotient nodes.toOrderedNodes i) = 0 := by
  let p : ℝ[X] := ∑ i : Fin (d + 1), C (gapQuotientCofactor nodes i) *
    gapDerivativeQuotient nodes.toOrderedNodes i
  have hpdegree : p.natDegree < d := by
    have hle : p.natDegree ≤ d - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (by
          have hq := natDegree_gapDerivativeQuotient_le_sub_three
            (n := d + 2) nodes.toOrderedNodes (by omega) i
          omega)
    omega
  let s : Finset ℝ := Finset.univ.image
    (fun j : Fin d => nodes.point (interiorNodeIndex j))
  have hxinj : Function.Injective
      (fun j : Fin d => nodes.point (interiorNodeIndex j)) :=
    nodes.strictMono.injective.comp interiorNodeIndex_strictMono.injective
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ,
      Fintype.card_fin]
  change p = 0
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
  · rw [hs_card]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr hpdegree)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact gapQuotientCofactor_evaluation_sum_eq_zero nodes j
theorem gapQuotientCofactor_alternating_sign {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) :
    (∀ i : Fin (d + 1),
      (-1 : ℝ) ^ i.val * gapQuotientCofactor nodes i < 0) ∨
    (∀ i : Fin (d + 1),
      0 < (-1 : ℝ) ^ i.val * gapQuotientCofactor nodes i) := by
  let a : Fin (d + 1) → ℝ := fun i =>
    sourceQuotientNormalizer i * gapQuotientCofactor nodes i
  have hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0 := by
    calc
      (∑ i, C (a i) * sourceNormalizedQuotient nodes i) =
          ∑ i, C (gapQuotientCofactor nodes i) *
            gapDerivativeQuotient nodes.toOrderedNodes i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [sourceNormalizedQuotient]
        have hs := sourceQuotientNormalizer_sq i
        change C (sourceQuotientNormalizer i * gapQuotientCofactor nodes i) *
            (C (sourceQuotientNormalizer i) *
              gapDerivativeQuotient nodes.toOrderedNodes i) = _
        rw [← mul_assoc, ← map_mul]
        congr 2
        calc
          sourceQuotientNormalizer i * gapQuotientCofactor nodes i *
              sourceQuotientNormalizer i =
              gapQuotientCofactor nodes i *
                sourceQuotientNormalizer i ^ 2 := by ring
          _ = gapQuotientCofactor nodes i := by rw [hs, mul_one]
      _ = 0 := gapQuotientCofactor_polynomial_relation nodes hd
  have hane : a ≠ 0 := by
    intro ha
    have h0 := congrFun ha (0 : Fin (d + 1))
    have hc0 := quotientEvaluationMaximalMinorsNonzero nodes (0 : Fin (d + 1))
    have hcofactor0 : gapQuotientCofactor nodes 0 ≠ 0 := by
      simpa [gapQuotientCofactor] using hc0
    dsimp [a] at h0
    exact hcofactor0 ((mul_eq_zero.mp h0).resolve_left
      (sourceQuotientNormalizer_ne_zero 0))
  rcases sourceNormalizedQuotient_relation_sign_pattern nodes hd a hrel hane with
    hneg | hpos
  · left
    intro i
    by_cases hi : i = 0
    · subst i
      dsimp [a, sourceQuotientNormalizer] at hneg
      simpa using hneg.1
    · have hi' := hneg.2 i hi
      dsimp [a, sourceQuotientNormalizer] at hi'
      rw [if_neg hi] at hi'
      exact hi'
  · right
    intro i
    by_cases hi : i = 0
    · subst i
      dsimp [a, sourceQuotientNormalizer] at hpos
      simpa using hpos.1
    · have hi' := hpos.2 i hi
      dsimp [a, sourceQuotientNormalizer] at hi'
      rw [if_neg hi] at hi'
      exact hi'
theorem gapQuotientEvaluation_deletedRowMinors_coherent_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) :
    (∀ omitted : Fin (d + 1),
      deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted < 0) ∨
    (∀ omitted : Fin (d + 1),
      0 < deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted) := by
  by_cases hd0 : d = 0
  · subst d
    right
    intro omitted
    simp [deletedRowMinor]
  by_cases hd1 : d = 1
  · subst d
    left
    intro omitted
    rw [deletedRowMinor]
    simpa [gapQuotientEvaluationMatrix, Matrix.det_fin_one] using
      gapDerivativeQuotient_eval_neg_of_three_nodes nodes.toOrderedNodes
        (omitted.succAbove 0) (nodes.point (interiorNodeIndex 0))
  · rcases gapQuotientCofactor_alternating_sign nodes (by omega) with
      hneg | hpos
    · left
      intro omitted
      have h := hneg omitted
      rw [gapQuotientCofactor] at h
      nlinarith [sq_negOnePow omitted.val]
    · right
      intro omitted
      have h := hpos omitted
      rw [gapQuotientCofactor] at h
      nlinarith [sq_negOnePow omitted.val]
theorem gapHeightMinor_diagonalFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (omitted : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ omitted.val *
      ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
        ∏ j : Fin d, gapJacobianColumnFactor nodes j) := by
  have hrow : 0 < ∏ i : Fin d,
      ((-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val) *
        gapJacobianRowFactor nodes (omitted.succAbove i)) := by
    apply Finset.prod_pos
    intro i _hi
    exact gapJacobianRowFactor_parity_pos nodes hd _
  have hcol : 0 < ∏ j : Fin d,
      ((-1 : ℝ) ^ (d - j.val) * gapJacobianColumnFactor nodes j) := by
    apply Finset.prod_pos
    intro j _hj
    exact gapJacobianColumnFactor_parity_pos nodes j
  have hboth := mul_pos hrow hcol
  rw [← heightMinorFactorParity_eq_negOnePow d omitted]
  simpa [heightMinorFactorParity, Finset.prod_mul_distrib, mul_assoc,
    mul_left_comm, mul_comm] using hboth
def AlternatingHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  (∀ omitted : Fin (d + 1),
      (-1 : ℝ) ^ omitted.val *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted < 0) ∨
  (∀ omitted : Fin (d + 1),
      0 < (-1 : ℝ) ^ omitted.val *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted)
theorem alternatingHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    AlternatingHeightMaximalMinorSigns nodes := by
  by_cases hd0 : d = 0
  · subst d
    right
    intro omitted
    simp [deletedRowMinor_zero_dim]
  have hd : 1 ≤ d := by omega
  rcases gapQuotientEvaluation_deletedRowMinors_coherent_sign nodes with
    hqneg | hqpos
  · left
    intro omitted
    rw [deletedRowMinor_gapHeightJacobianModel]
    have hfactor := gapHeightMinor_diagonalFactor_parity_pos nodes hd omitted
    have hq := hqneg omitted
    calc
      (-1 : ℝ) ^ omitted.val *
          ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j) =
          ((-1 : ℝ) ^ omitted.val *
            ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted := by ring
      _ < 0 := mul_neg_of_pos_of_neg hfactor hq
  · right
    intro omitted
    rw [deletedRowMinor_gapHeightJacobianModel]
    have hfactor := gapHeightMinor_diagonalFactor_parity_pos nodes hd omitted
    have hq := hqpos omitted
    calc
      0 < ((-1 : ℝ) ^ omitted.val *
            ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted :=
        mul_pos hfactor hq
      _ = (-1 : ℝ) ^ omitted.val *
          ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j) := by ring
def augmentedGapHeightJacobianMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases 1 (fun j => gapHeightJacobianModel nodes i j) k
theorem augmentedGapHeightJacobianMatrix_det_sign {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    (augmentedGapHeightJacobianMatrix nodes).det < 0 ∨
      0 < (augmentedGapHeightJacobianMatrix nodes).det := by
  have hexpand := Matrix.det_succ_column_zero
    (augmentedGapHeightJacobianMatrix nodes)
  simp only [augmentedGapHeightJacobianMatrix, Fin.cases_zero, mul_one] at hexpand
  rcases alternatingHeightMaximalMinorSigns nodes with hneg | hpos
  · left
    rw [hexpand]
    apply Finset.sum_neg
    · intro i _hi
      exact hneg i
    · exact Finset.univ_nonempty
  · right
    rw [hexpand]
    apply Finset.sum_pos
    · intro i _hi
      exact hpos i
    · exact Finset.univ_nonempty
theorem augmentedGapHeightJacobianMatrix_det_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    (augmentedGapHeightJacobianMatrix nodes).det ≠ 0 := by
  rcases augmentedGapHeightJacobianMatrix_det_sign nodes with h | h
  · exact ne_of_lt h
  · exact ne_of_gt h
theorem gapHeightJacobianModel_consecutiveDifference_det_ne_zero
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Matrix.det (fun i j : Fin d =>
      gapHeightJacobianModel nodes i.succ j -
        gapHeightJacobianModel nodes i.castSucc j) ≠ 0 := by
  classical
  intro hdet
  let D : Matrix (Fin d) (Fin d) ℝ := fun i j =>
    gapHeightJacobianModel nodes i.succ j -
      gapHeightJacobianModel nodes i.castSucc j
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (show D.det = 0 from hdet)
  let rowValue : Fin (d + 1) → ℝ := fun i =>
    ∑ j : Fin d, gapHeightJacobianModel nodes i j * v j
  have hadj (i : Fin d) : rowValue i.succ = rowValue i.castSucc := by
    have hi := congrFun hv i
    simp only [D, Matrix.mulVec, dotProduct, Pi.zero_apply, rowValue] at hi ⊢
    simp_rw [sub_mul] at hi
    rw [Finset.sum_sub_distrib] at hi
    linarith
  have hconst (i : Fin (d + 1)) : rowValue i = rowValue 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).trans ih
  let w : Fin (d + 1) → ℝ :=
    Fin.cases (-(rowValue 0)) v
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    funext j
    have hj := congrFun hw j.succ
    simpa [w] using hj
  have hAw : (augmentedGapHeightJacobianMatrix nodes).mulVec w = 0 := by
    funext i
    rw [show (augmentedGapHeightJacobianMatrix nodes).mulVec w i =
        -(rowValue 0) + rowValue i by
      simp [Matrix.mulVec, dotProduct, augmentedGapHeightJacobianMatrix,
        w, Fin.sum_univ_succ, rowValue]]
    rw [hconst i]
    simp
  have hA0 : (augmentedGapHeightJacobianMatrix nodes).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hwne, hAw⟩
  exact (augmentedGapHeightJacobianMatrix_det_ne_zero nodes) hA0
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
noncomputable section
def gapDifference {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i => nodes.height i.succ - nodes.height i.castSucc
def Equioscillates {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Prop :=
  ∀ i j : Fin (d + 1), nodes.height i = nodes.height j
def GapDifferenceHomeomorphismStatement (d : ℕ) (A B : ℝ) : Prop :=
  AdmissibleInterval A B →
    IsHomeomorph (gapDifference : EndpointArray d A B → Fin d → ℝ)
def GapHeightLeRigidityStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ s t : EndpointArray d A B,
    (∀ i : Fin (d + 1), s.height i ≤ t.height i) → s = t
def ExistsUniqueEquioscillatingStatement (d : ℕ) (A B : ℝ) : Prop :=
  AdmissibleInterval A B →
    ∃! nodes : EndpointArray d A B, Equioscillates nodes
structure ComparisonPackage (d : ℕ) (A B : ℝ) : Prop where
  gapHeight_le_rigidity : GapHeightLeRigidityStatement d A B
  exists_unique_equioscillating : ExistsUniqueEquioscillatingStatement d A B
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open scoped BigOperators Topology
open Filter
noncomputable section
lemma lagrangeFundamental_eval_transport {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {x y : ℝ}
    (hx : ∀ j : Fin n, j ≠ k → x ≠ nodes.point j) :
    lagrangeFundamental nodes k y =
      lagrangeFundamental nodes k x *
        ∏ j ∈ Finset.univ.erase k,
          ((y - nodes.point j) / (x - nodes.point j)) := by
  classical
  unfold lagrangeFundamental
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hxj : x - nodes.point j ≠ 0 := sub_ne_zero.mpr (hx j hjk)
  field_simp
lemma abs_lagrangeFundamental_eval_transport {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {x y : ℝ}
    (hx : ∀ j : Fin n, j ≠ k → x ≠ nodes.point j) :
    |lagrangeFundamental nodes k y| =
      |lagrangeFundamental nodes k x| *
        ∏ j ∈ Finset.univ.erase k,
          |(y - nodes.point j) / (x - nodes.point j)| := by
  rw [lagrangeFundamental_eval_transport nodes k hx, abs_mul,
    Finset.abs_prod]
lemma mul_le_lebesgueFunction_of_cardinal_domination {n : ℕ}
    (nodes : NodeFamily n) {K x y : ℝ}
    (hdom : ∀ k : Fin n,
      K * |lagrangeFundamental nodes k x| ≤
        |lagrangeFundamental nodes k y|) :
    K * lebesgueFunction nodes x ≤ lebesgueFunction nodes y := by
  classical
  simp only [lebesgueFunction, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ hdom k
lemma one_le_lebesgueFunction_endpointArray {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (x : ℝ) :
    1 ≤ lebesgueFunction nodes.toNodeFamily x := by
  have hsum :
      ∑ k : Fin (d + 2),
        lagrangeFundamental nodes.toNodeFamily k x = 1 :=
    sum_lagrangeFundamental_eq_one nodes.toOrderedNodes (by omega) x
  calc
    1 = |∑ k : Fin (d + 2),
        lagrangeFundamental nodes.toNodeFamily k x| := by rw [hsum, abs_one]
    _ ≤ ∑ k : Fin (d + 2),
        |lagrangeFundamental nodes.toNodeFamily k x| := Finset.abs_sum_le_sum_abs _ _
    _ = lebesgueFunction nodes.toNodeFamily x := rfl
lemma lebesgueFunction_le_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) {x : ℝ}
    (hx : x ∈ closedGap nodes.toOrderedNodes g) :
    lebesgueFunction nodes.toNodeFamily x ≤ nodes.height g := by
  obtain ⟨t, ht, heq, hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes g).le
  exact (hmax x hx).trans_eq heq.symm
lemma one_le_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) :
    1 ≤ nodes.height g := by
  exact (one_le_lebesgueFunction_endpointArray nodes
    (nodes.point (gapLeftIndex g))).trans
      (lebesgueFunction_le_height nodes g
      ⟨le_rfl, (gap_left_lt_right nodes.toOrderedNodes g).le⟩)
lemma one_lt_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    1 < nodes.height g := by
  obtain ⟨x, hx⟩ := openGap_nonempty nodes.toOrderedNodes g
  have hxClosed : x ∈ closedGap nodes.toOrderedNodes g := ⟨hx.1.le, hx.2.le⟩
  have hpoly := one_lt_eval_gapPolynomial_of_mem_openGap
    nodes.toOrderedNodes (by omega) g hx
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hxClosed] at hpoly
  exact hpoly.trans_le (lebesgueFunction_le_height nodes g hxClosed)
lemma exists_height_eq_lebesgueFunction_mem_openGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ∃ x ∈ openGap nodes.toOrderedNodes g,
      nodes.height g = lebesgueFunction nodes.toNodeFamily x := by
  obtain ⟨x, hx, heq, _hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes g).le
  have hheight : 1 < nodes.height g := one_lt_height nodes hd g
  have hleft : x ≠ nodes.point (gapLeftIndex g) := by
    intro h
    subst x
    have hclosed : nodes.point (gapLeftIndex g) ∈ closedGap nodes.toOrderedNodes g :=
      ⟨le_rfl, (gap_left_lt_right nodes.toOrderedNodes g).le⟩
    have hvalue : lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapLeftIndex g)) = 1 := by
      rw [lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hclosed,
        gapPolynomial_eval_left]
    have heq' : nodes.height g = lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapLeftIndex g)) := heq
    rw [heq', hvalue] at hheight
    exact (lt_irrefl 1 hheight)
  have hright : x ≠ nodes.point (gapRightIndex g) := by
    intro h
    subst x
    have hclosed : nodes.point (gapRightIndex g) ∈ closedGap nodes.toOrderedNodes g :=
      ⟨(gap_left_lt_right nodes.toOrderedNodes g).le, le_rfl⟩
    have hvalue : lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapRightIndex g)) = 1 := by
      rw [lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hclosed,
        gapPolynomial_eval_right]
    have heq' : nodes.height g = lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapRightIndex g)) := heq
    rw [heq', hvalue] at hheight
    exact (lt_irrefl 1 hheight)
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 hleft.symm,
    lt_of_le_of_ne hx.2 hright⟩, heq⟩
def AdjacentCardinalAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (K : ℝ) : Prop :=
  ∃ y ∈ closedGap nodes.toOrderedNodes q.castSucc,
    ∀ x ∈ openGap nodes.toOrderedNodes q.succ,
      ∀ k : Fin (d + 2),
        K * |lagrangeFundamental nodes.toNodeFamily k x| ≤
          |lagrangeFundamental nodes.toNodeFamily k y|
def boundaryMidpoint {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (nodes.point (gapLeftIndex q.castSucc) +
    nodes.point (gapRightIndex q.castSucc)) / 2
def boundaryAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (endpointSpacing nodes q.castSucc /
      (2 * endpointSpacing nodes q.succ)) *
    (endpointSpacing nodes q.castSucc / (2 * (B - A))) ^ d
lemma boundary_common_index {d : ℕ} (q : Fin d) :
    gapRightIndex (n := d + 2) q.castSucc =
      gapLeftIndex (n := d + 2) q.succ := by
  apply Fin.ext
  rfl
lemma boundaryMidpoint_mem_lowerGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) :
    boundaryMidpoint nodes q ∈ closedGap nodes.toOrderedNodes q.castSucc := by
  have h := gap_left_lt_right nodes.toOrderedNodes q.castSucc
  constructor <;> unfold boundaryMidpoint <;> linarith
lemma upperGap_point_ne_node {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    x ≠ nodes.point j := by
  intro heq
  by_cases hj : j.val ≤ q.val + 1
  · have hjCommon : j ≤ gapLeftIndex q.succ := by
      change j.val ≤ q.val + 1
      exact hj
    have := (nodes.strictMono.monotone hjCommon).trans_lt hx.1
    rw [heq] at this
    exact (lt_irrefl _ this)
  · have hrightj : gapRightIndex q.succ ≤ j := by
      change q.val + 2 ≤ j.val
      omega
    have := hx.2.trans_le (nodes.strictMono.monotone hrightj)
    rw [heq] at this
    exact (lt_irrefl _ this)
lemma half_lowerSpacing_le_midpoint_distance {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (j : Fin (d + 2)) :
    endpointSpacing nodes q.castSucc / 2 ≤
      |boundaryMidpoint nodes q - nodes.point j| := by
  have hgap := gap_left_lt_right nodes.toOrderedNodes q.castSucc
  by_cases hj : j.val ≤ q.val
  · have hjleft : j ≤ gapLeftIndex q.castSucc := by
      change j.val ≤ q.val
      exact hj
    have hpoint := nodes.strictMono.monotone hjleft
    have hnonneg : 0 ≤ boundaryMidpoint nodes q - nodes.point j := by
      unfold boundaryMidpoint
      linarith
    rw [abs_of_nonneg hnonneg]
    unfold endpointSpacing boundaryMidpoint
    linarith
  · have hcommonj : gapRightIndex q.castSucc ≤ j := by
      change q.val + 1 ≤ j.val
      omega
    have hpoint := nodes.strictMono.monotone hcommonj
    have hnonpos : boundaryMidpoint nodes q - nodes.point j ≤ 0 := by
      unfold boundaryMidpoint
      linarith
    rw [abs_of_nonpos hnonpos]
    unfold endpointSpacing boundaryMidpoint
    linarith
lemma upperGap_distance_le_intervalLength {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    |x - nodes.point j| ≤ B - A := by
  have hAj : A ≤ nodes.point j := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point j := nodes.strictMono.monotone (by
        simp [Fin.le_iff_val_le_val, endpointLeftIndex])
  have hjB : nodes.point j ≤ B := by
    calc
      nodes.point j ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          change j.val ≤ d + 1
          omega)
      _ = B := nodes.right_endpoint
  have hAx : A < x := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point (gapLeftIndex q.succ) :=
        nodes.strictMono.monotone (by simp [Fin.le_iff_val_le_val, endpointLeftIndex])
      _ < x := hx.1
  have hxB : x < B := by
    calc
      x < nodes.point (gapRightIndex q.succ) := hx.2
      _ ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          simp [Fin.le_iff_val_le_val, endpointRightIndex])
      _ = B := nodes.right_endpoint
  rw [abs_le]
  constructor <;> linarith
private lemma half_div_le_div_of_bounds {L D a b : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hb : 0 < b)
    (ha : L / 2 ≤ a) (hbD : b ≤ D) :
    L / (2 * D) ≤ a / b := by
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hD) hb]
  have h₁ : L * b ≤ L * D := mul_le_mul_of_nonneg_left hbD hL
  have h₂ : (2 * D) * (L / 2) ≤ (2 * D) * a :=
    mul_le_mul_of_nonneg_left ha (mul_pos (by norm_num) hD).le
  nlinarith
lemma boundary_base_le_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    endpointSpacing nodes q.castSucc / (2 * (B - A)) ≤
      |(boundaryMidpoint nodes q - nodes.point j) /
        (x - nodes.point j)| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact sub_pos.mpr nodes.endpoints_lt
  · exact abs_pos.mpr (sub_ne_zero.mpr (upperGap_point_ne_node nodes q hx j))
  · exact half_lowerSpacing_le_midpoint_distance nodes q j
  · exact upperGap_distance_le_intervalLength nodes q hx j
lemma boundary_ratio_le_common_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) :
    endpointSpacing nodes q.castSucc /
        (2 * endpointSpacing nodes q.succ) ≤
      |(boundaryMidpoint nodes q -
          nodes.point (gapRightIndex q.castSucc)) /
        (x - nodes.point (gapRightIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact endpointSpacing_pos nodes q.succ
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (upperGap_point_ne_node nodes q hx (gapRightIndex q.castSucc)))
  · exact half_lowerSpacing_le_midpoint_distance nodes q
      (gapRightIndex q.castSucc)
  · rw [boundary_common_index q]
    rw [abs_of_pos (sub_pos.mpr hx.1)]
    unfold endpointSpacing
    linarith [hx.2]
lemma boundary_ratio_le_upperRight_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) :
    endpointSpacing nodes q.castSucc /
        (2 * endpointSpacing nodes q.succ) ≤
      |(boundaryMidpoint nodes q - nodes.point (gapRightIndex q.succ)) /
        (x - nodes.point (gapRightIndex q.succ))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact endpointSpacing_pos nodes q.succ
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (upperGap_point_ne_node nodes q hx (gapRightIndex q.succ)))
  · exact half_lowerSpacing_le_midpoint_distance nodes q (gapRightIndex q.succ)
  · rw [abs_of_neg (sub_neg.mpr hx.2)]
    unfold endpointSpacing
    linarith [hx.1]
lemma exists_boundary_ratio_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (k : Fin (d + 2)) :
    ∃ r ∈ Finset.univ.erase k,
      endpointSpacing nodes q.castSucc /
          (2 * endpointSpacing nodes q.succ) ≤
        |(boundaryMidpoint nodes q - nodes.point r) /
          (x - nodes.point r)| := by
  by_cases hk : gapRightIndex q.castSucc = k
  · refine ⟨gapRightIndex q.succ, ?_,
      boundary_ratio_le_upperRight_factor nodes q hx⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply (gapLeftIndex_lt_rightIndex (n := d + 2) q.succ).ne
    rw [← boundary_common_index q, hk, h]
  · exact ⟨gapRightIndex q.castSucc, by simp [hk],
      boundary_ratio_le_common_factor nodes q hx⟩
lemma boundaryAmplification_le_factorProduct {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (k : Fin (d + 2)) :
    boundaryAmplification nodes q ≤
      ∏ j ∈ Finset.univ.erase k,
        |(boundaryMidpoint nodes q - nodes.point j) /
          (x - nodes.point j)| := by
  classical
  let s : Finset (Fin (d + 2)) := Finset.univ.erase k
  let f : Fin (d + 2) → ℝ := fun j ↦
    |(boundaryMidpoint nodes q - nodes.point j) / (x - nodes.point j)|
  let c : ℝ := endpointSpacing nodes q.castSucc / (2 * (B - A))
  let R : ℝ := endpointSpacing nodes q.castSucc /
    (2 * endpointSpacing nodes q.succ)
  obtain ⟨r, hrs, hrR⟩ := exists_boundary_ratio_factor nodes q hx k
  have hc : ∀ j ∈ s, c ≤ f j := by
    intro j _hj
    exact boundary_base_le_factor nodes q hx j
  have hc0 : 0 ≤ c := by
    exact div_nonneg (endpointSpacing_pos nodes q.castSucc).le
      (mul_nonneg (by norm_num) (sub_pos.mpr nodes.endpoints_lt).le)
  have hpow : c ^ (s.erase r).card ≤ ∏ j ∈ s.erase r, f j := by
    have h := Finset.prod_le_prod (s := s.erase r)
      (f := fun _ ↦ c) (g := f)
      (fun _ _ ↦ hc0)
      (fun j hj ↦ hc j (Finset.mem_of_mem_erase hj))
    simpa using h
  have hcard : (s.erase r).card = d := by
    have hrs' : r ∈ s := hrs
    simp only [s, Finset.card_erase_of_mem hrs', Finset.card_erase_of_mem
      (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hpow' : c ^ d ≤ ∏ j ∈ s.erase r, f j := by
    rwa [hcard] at hpow
  have hrR' : R ≤ f r := hrR
  have hprod : R * c ^ d ≤ ∏ j ∈ s, f j := by
    calc
      R * c ^ d ≤ f r * c ^ d :=
        mul_le_mul_of_nonneg_right hrR' (pow_nonneg hc0 d)
      _ ≤ f r * ∏ j ∈ s.erase r, f j :=
        mul_le_mul_of_nonneg_left hpow' (abs_nonneg _)
      _ = ∏ j ∈ s, f j := Finset.mul_prod_erase s f hrs
  simpa only [boundaryAmplification, s, f, c, R] using hprod
theorem adjacentCardinalAmplification_boundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) :
    AdjacentCardinalAmplification nodes q (boundaryAmplification nodes q) := by
  refine ⟨boundaryMidpoint nodes q, boundaryMidpoint_mem_lowerGap nodes q, ?_⟩
  intro x hx k
  have hxnodes : ∀ j : Fin (d + 2), j ≠ k → x ≠ nodes.point j := by
    intro j _hjk
    exact upperGap_point_ne_node nodes q hx j
  have htransport := abs_lagrangeFundamental_eval_transport nodes.toNodeFamily k
    (x := x) (y := boundaryMidpoint nodes q) hxnodes
  rw [htransport]
  have hprod := boundaryAmplification_le_factorProduct nodes q hx k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (lagrangeFundamental nodes.toNodeFamily k x))
theorem tendsto_boundaryAmplification_atTop_of_upperSpacing
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (hzero : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
      atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta)
    (hlower : ∀ᶠ m in atTop,
      delta ≤ endpointSpacing (nodes m) q.castSucc) :
    Tendsto (fun m ↦ boundaryAmplification (nodes m) q) atTop atTop := by
  let C : ℝ := (delta / 2) * (delta / (2 * (B - A))) ^ d
  have hD : 0 < B - A := sub_pos.mpr (nodes 0).endpoints_lt
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hpositive : ∀ᶠ m in atTop,
      endpointSpacing (nodes m) q.succ ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun m ↦ endpointSpacing_pos (nodes m) q.succ
  have hGT : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hinv : Tendsto
      (fun m ↦ (endpointSpacing (nodes m) q.succ)⁻¹) atTop atTop :=
    hGT.inv_tendsto_nhdsGT_zero
  have hCinv : Tendsto
      (fun m ↦ C * (endpointSpacing (nodes m) q.succ)⁻¹) atTop atTop :=
    hinv.const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hCinv
  filter_upwards [hlower] with m hm
  have hLowerPos : 0 < endpointSpacing (nodes m) q.castSucc :=
    endpointSpacing_pos (nodes m) q.castSucc
  have hUpperPos : 0 < endpointSpacing (nodes m) q.succ :=
    endpointSpacing_pos (nodes m) q.succ
  have hbase : delta / (2 * (B - A)) ≤
      endpointSpacing (nodes m) q.castSucc / (2 * (B - A)) := by
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hD.le)
  have hpow : (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hbase d
  have hhalf : delta / 2 ≤ endpointSpacing (nodes m) q.castSucc / 2 := by
    linarith
  have hinner : (delta / 2) * (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.castSucc / 2) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
    exact mul_le_mul hhalf hpow (by positivity) (by positivity)
  dsimp only [C]
  rw [boundaryAmplification, div_eq_mul_inv]
  calc
    (delta / 2 * (delta / (2 * (B - A))) ^ d) *
        (endpointSpacing (nodes m) q.succ)⁻¹ ≤
      ((endpointSpacing (nodes m) q.castSucc / 2) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d) *
          (endpointSpacing (nodes m) q.succ)⁻¹ :=
      mul_le_mul_of_nonneg_right hinner (inv_nonneg.mpr hUpperPos.le)
    _ = (endpointSpacing (nodes m) q.castSucc *
          (2 * endpointSpacing (nodes m) q.succ)⁻¹) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
      field_simp
theorem gapDifference_le_one_sub_of_adjacentCardinalAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) {K : ℝ}
    (hK : 1 ≤ K) (hamp : AdjacentCardinalAmplification nodes q K) :
    gapDifference nodes q ≤ 1 - K := by
  rcases hamp with ⟨y, hy, hdom⟩
  obtain ⟨x, hx, heq⟩ :=
    exists_height_eq_lebesgueFunction_mem_openGap nodes (by
      have := q.isLt
      omega) q.succ
  have hsum :
      K * lebesgueFunction nodes.toNodeFamily x ≤
        lebesgueFunction nodes.toNodeFamily y :=
    mul_le_lebesgueFunction_of_cardinal_domination nodes.toNodeFamily
      (hdom x hx)
  have hlower :
      lebesgueFunction nodes.toNodeFamily y ≤ nodes.height q.castSucc :=
    lebesgueFunction_le_height nodes q.castSucc hy
  have hupper : nodes.height q.succ = lebesgueFunction nodes.toNodeFamily x := by
    exact heq
  have hone : 1 ≤ nodes.height q.succ := one_le_height nodes q.succ
  unfold gapDifference
  rw [hupper] at hone ⊢
  nlinarith
theorem tendsto_norm_gapDifference_atTop_of_amplification
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hamp : ∀ m, AdjacentCardinalAmplification (nodes m) q (K m)) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hK.eventually (eventually_ge_atTop (max 1 (R + 1)))] with m hm
  have hKm : 1 ≤ K m := le_trans (le_max_left _ _) hm
  have hgap := gapDifference_le_one_sub_of_adjacentCardinalAmplification
    (nodes m) q hKm (hamp m)
  rw [Real.norm_eq_abs]
  have hneg : gapDifference (nodes m) q ≤ 0 := by linarith
  rw [abs_of_nonpos hneg]
  have hR : R + 1 ≤ K m := le_trans (le_max_right _ _) hm
  linarith
def RightAdjacentCardinalAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (K : ℝ) : Prop :=
  ∃ y ∈ closedGap nodes.toOrderedNodes q.succ,
    ∀ x ∈ openGap nodes.toOrderedNodes q.castSucc,
      ∀ k : Fin (d + 2),
        K * |lagrangeFundamental nodes.toNodeFamily k x| ≤
          |lagrangeFundamental nodes.toNodeFamily k y|
def rightBoundaryMidpoint {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (nodes.point (gapLeftIndex q.succ) +
    nodes.point (gapRightIndex q.succ)) / 2
def rightBoundaryAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (endpointSpacing nodes q.succ /
      (2 * endpointSpacing nodes q.castSucc)) *
    (endpointSpacing nodes q.succ / (2 * (B - A))) ^ d
lemma rightBoundaryMidpoint_mem_upperGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) :
    rightBoundaryMidpoint nodes q ∈ closedGap nodes.toOrderedNodes q.succ := by
  have h := gap_left_lt_right nodes.toOrderedNodes q.succ
  constructor <;> unfold rightBoundaryMidpoint <;> linarith
lemma lowerGap_point_ne_node {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    x ≠ nodes.point j := by
  intro heq
  by_cases hj : j.val ≤ q.val
  · have hjleft : j ≤ gapLeftIndex q.castSucc := by
      change j.val ≤ q.val
      exact hj
    have := (nodes.strictMono.monotone hjleft).trans_lt hx.1
    rw [heq] at this
    exact (lt_irrefl _ this)
  · have hrightj : gapRightIndex q.castSucc ≤ j := by
      change q.val + 1 ≤ j.val
      omega
    have := hx.2.trans_le (nodes.strictMono.monotone hrightj)
    rw [heq] at this
    exact (lt_irrefl _ this)
lemma half_upperSpacing_le_rightMidpoint_distance {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (j : Fin (d + 2)) :
    endpointSpacing nodes q.succ / 2 ≤
      |rightBoundaryMidpoint nodes q - nodes.point j| := by
  have hgap := gap_left_lt_right nodes.toOrderedNodes q.succ
  by_cases hj : j.val ≤ q.val + 1
  · have hjleft : j ≤ gapLeftIndex q.succ := by
      change j.val ≤ q.val + 1
      exact hj
    have hpoint := nodes.strictMono.monotone hjleft
    have hnonneg : 0 ≤ rightBoundaryMidpoint nodes q - nodes.point j := by
      unfold rightBoundaryMidpoint
      linarith
    rw [abs_of_nonneg hnonneg]
    unfold endpointSpacing rightBoundaryMidpoint
    linarith
  · have hrightj : gapRightIndex q.succ ≤ j := by
      change q.val + 2 ≤ j.val
      omega
    have hpoint := nodes.strictMono.monotone hrightj
    have hnonpos : rightBoundaryMidpoint nodes q - nodes.point j ≤ 0 := by
      unfold rightBoundaryMidpoint
      linarith
    rw [abs_of_nonpos hnonpos]
    unfold endpointSpacing rightBoundaryMidpoint
    linarith
lemma lowerGap_distance_le_intervalLength {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    |x - nodes.point j| ≤ B - A := by
  have hAj : A ≤ nodes.point j := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point j := nodes.strictMono.monotone (by
        simp [Fin.le_iff_val_le_val, endpointLeftIndex])
  have hjB : nodes.point j ≤ B := by
    calc
      nodes.point j ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          change j.val ≤ d + 1
          omega)
      _ = B := nodes.right_endpoint
  have hAx : A < x := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point (gapLeftIndex q.castSucc) :=
        nodes.strictMono.monotone (by simp [Fin.le_iff_val_le_val, endpointLeftIndex])
      _ < x := hx.1
  have hxB : x < B := by
    calc
      x < nodes.point (gapRightIndex q.castSucc) := hx.2
      _ ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          simp [Fin.le_iff_val_le_val, endpointRightIndex])
      _ = B := nodes.right_endpoint
  rw [abs_le]
  constructor <;> linarith
lemma rightBoundary_base_le_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    endpointSpacing nodes q.succ / (2 * (B - A)) ≤
      |(rightBoundaryMidpoint nodes q - nodes.point j) /
        (x - nodes.point j)| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact sub_pos.mpr nodes.endpoints_lt
  · exact abs_pos.mpr (sub_ne_zero.mpr (lowerGap_point_ne_node nodes q hx j))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q j
  · exact lowerGap_distance_le_intervalLength nodes q hx j
lemma rightBoundary_ratio_le_common_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) :
    endpointSpacing nodes q.succ /
        (2 * endpointSpacing nodes q.castSucc) ≤
      |(rightBoundaryMidpoint nodes q -
          nodes.point (gapRightIndex q.castSucc)) /
        (x - nodes.point (gapRightIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact endpointSpacing_pos nodes q.castSucc
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (lowerGap_point_ne_node nodes q hx (gapRightIndex q.castSucc)))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q
      (gapRightIndex q.castSucc)
  · rw [abs_of_neg (sub_neg.mpr hx.2)]
    unfold endpointSpacing
    linarith [hx.1]
lemma rightBoundary_ratio_le_lowerLeft_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) :
    endpointSpacing nodes q.succ /
        (2 * endpointSpacing nodes q.castSucc) ≤
      |(rightBoundaryMidpoint nodes q -
          nodes.point (gapLeftIndex q.castSucc)) /
        (x - nodes.point (gapLeftIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact endpointSpacing_pos nodes q.castSucc
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (lowerGap_point_ne_node nodes q hx (gapLeftIndex q.castSucc)))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q
      (gapLeftIndex q.castSucc)
  · rw [abs_of_pos (sub_pos.mpr hx.1)]
    unfold endpointSpacing
    linarith [hx.2]
lemma exists_rightBoundary_ratio_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (k : Fin (d + 2)) :
    ∃ r ∈ Finset.univ.erase k,
      endpointSpacing nodes q.succ /
          (2 * endpointSpacing nodes q.castSucc) ≤
        |(rightBoundaryMidpoint nodes q - nodes.point r) /
          (x - nodes.point r)| := by
  by_cases hk : gapRightIndex q.castSucc = k
  · refine ⟨gapLeftIndex q.castSucc, ?_,
      rightBoundary_ratio_le_lowerLeft_factor nodes q hx⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply (gapLeftIndex_lt_rightIndex (n := d + 2) q.castSucc).ne
    rw [h, hk]
  · exact ⟨gapRightIndex q.castSucc, by simp [hk],
      rightBoundary_ratio_le_common_factor nodes q hx⟩
lemma rightBoundaryAmplification_le_factorProduct {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (k : Fin (d + 2)) :
    rightBoundaryAmplification nodes q ≤
      ∏ j ∈ Finset.univ.erase k,
        |(rightBoundaryMidpoint nodes q - nodes.point j) /
          (x - nodes.point j)| := by
  classical
  let s : Finset (Fin (d + 2)) := Finset.univ.erase k
  let f : Fin (d + 2) → ℝ := fun j ↦
    |(rightBoundaryMidpoint nodes q - nodes.point j) / (x - nodes.point j)|
  let c : ℝ := endpointSpacing nodes q.succ / (2 * (B - A))
  let R : ℝ := endpointSpacing nodes q.succ /
    (2 * endpointSpacing nodes q.castSucc)
  obtain ⟨r, hrs, hrR⟩ := exists_rightBoundary_ratio_factor nodes q hx k
  have hc : ∀ j ∈ s, c ≤ f j := by
    intro j _hj
    exact rightBoundary_base_le_factor nodes q hx j
  have hc0 : 0 ≤ c := by
    exact div_nonneg (endpointSpacing_pos nodes q.succ).le
      (mul_nonneg (by norm_num) (sub_pos.mpr nodes.endpoints_lt).le)
  have hpow : c ^ (s.erase r).card ≤ ∏ j ∈ s.erase r, f j := by
    have h := Finset.prod_le_prod (s := s.erase r)
      (f := fun _ ↦ c) (g := f)
      (fun _ _ ↦ hc0)
      (fun j hj ↦ hc j (Finset.mem_of_mem_erase hj))
    simpa using h
  have hcard : (s.erase r).card = d := by
    have hrs' : r ∈ s := hrs
    simp only [s, Finset.card_erase_of_mem hrs', Finset.card_erase_of_mem
      (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hpow' : c ^ d ≤ ∏ j ∈ s.erase r, f j := by rwa [hcard] at hpow
  have hprod : R * c ^ d ≤ ∏ j ∈ s, f j := by
    calc
      R * c ^ d ≤ f r * c ^ d :=
        mul_le_mul_of_nonneg_right hrR (pow_nonneg hc0 d)
      _ ≤ f r * ∏ j ∈ s.erase r, f j :=
        mul_le_mul_of_nonneg_left hpow' (abs_nonneg _)
      _ = ∏ j ∈ s, f j := Finset.mul_prod_erase s f hrs
  simpa only [rightBoundaryAmplification, s, f, c, R] using hprod
theorem rightAdjacentCardinalAmplification_rightBoundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) :
    RightAdjacentCardinalAmplification nodes q
      (rightBoundaryAmplification nodes q) := by
  refine ⟨rightBoundaryMidpoint nodes q, rightBoundaryMidpoint_mem_upperGap nodes q, ?_⟩
  intro x hx k
  have hxnodes : ∀ j : Fin (d + 2), j ≠ k → x ≠ nodes.point j := by
    intro j _hjk
    exact lowerGap_point_ne_node nodes q hx j
  have htransport := abs_lagrangeFundamental_eval_transport nodes.toNodeFamily k
    (x := x) (y := rightBoundaryMidpoint nodes q) hxnodes
  rw [htransport]
  have hprod := rightBoundaryAmplification_le_factorProduct nodes q hx k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (lagrangeFundamental nodes.toNodeFamily k x))
theorem gapDifference_ge_sub_one_of_rightAdjacentCardinalAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) {K : ℝ}
    (hK : 1 ≤ K) (hamp : RightAdjacentCardinalAmplification nodes q K) :
    K - 1 ≤ gapDifference nodes q := by
  rcases hamp with ⟨y, hy, hdom⟩
  obtain ⟨x, hx, heq⟩ :=
    exists_height_eq_lebesgueFunction_mem_openGap nodes (by
      have := q.isLt
      omega) q.castSucc
  have hsum : K * lebesgueFunction nodes.toNodeFamily x ≤
      lebesgueFunction nodes.toNodeFamily y :=
    mul_le_lebesgueFunction_of_cardinal_domination nodes.toNodeFamily (hdom x hx)
  have hupp : lebesgueFunction nodes.toNodeFamily y ≤ nodes.height q.succ :=
    lebesgueFunction_le_height nodes q.succ hy
  have hlower : nodes.height q.castSucc = lebesgueFunction nodes.toNodeFamily x := heq
  have hone : 1 ≤ nodes.height q.castSucc := one_le_height nodes q.castSucc
  unfold gapDifference
  rw [hlower] at hone ⊢
  nlinarith
theorem tendsto_rightBoundaryAmplification_atTop_of_lowerSpacing
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (hzero : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
      atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta)
    (hupper : ∀ᶠ m in atTop, delta ≤ endpointSpacing (nodes m) q.succ) :
    Tendsto (fun m ↦ rightBoundaryAmplification (nodes m) q) atTop atTop := by
  let C : ℝ := (delta / 2) * (delta / (2 * (B - A))) ^ d
  have hD : 0 < B - A := sub_pos.mpr (nodes 0).endpoints_lt
  have hC : 0 < C := by dsimp [C]; positivity
  have hpositive : ∀ᶠ m in atTop,
      endpointSpacing (nodes m) q.castSucc ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun m ↦ endpointSpacing_pos (nodes m) q.castSucc
  have hGT : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hinv : Tendsto (fun m ↦ (endpointSpacing (nodes m) q.castSucc)⁻¹)
      atTop atTop := hGT.inv_tendsto_nhdsGT_zero
  have hCinv : Tendsto
      (fun m ↦ C * (endpointSpacing (nodes m) q.castSucc)⁻¹) atTop atTop :=
    hinv.const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hCinv
  filter_upwards [hupper] with m hm
  have hLowerPos : 0 < endpointSpacing (nodes m) q.castSucc :=
    endpointSpacing_pos (nodes m) q.castSucc
  have hUpperPos : 0 < endpointSpacing (nodes m) q.succ :=
    endpointSpacing_pos (nodes m) q.succ
  have hbase : delta / (2 * (B - A)) ≤
      endpointSpacing (nodes m) q.succ / (2 * (B - A)) := by
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hD.le)
  have hpow : (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hbase d
  have hhalf : delta / 2 ≤ endpointSpacing (nodes m) q.succ / 2 := by linarith
  have hinner : (delta / 2) * (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.succ / 2) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
    exact mul_le_mul hhalf hpow (by positivity) (by positivity)
  dsimp only [C]
  rw [rightBoundaryAmplification, div_eq_mul_inv]
  calc
    (delta / 2 * (delta / (2 * (B - A))) ^ d) *
        (endpointSpacing (nodes m) q.castSucc)⁻¹ ≤
      ((endpointSpacing (nodes m) q.succ / 2) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d) *
          (endpointSpacing (nodes m) q.castSucc)⁻¹ :=
      mul_le_mul_of_nonneg_right hinner (inv_nonneg.mpr hLowerPos.le)
    _ = (endpointSpacing (nodes m) q.succ *
          (2 * endpointSpacing (nodes m) q.castSucc)⁻¹) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
      field_simp
theorem tendsto_norm_gapDifference_atTop_of_rightAmplification
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hamp : ∀ m, RightAdjacentCardinalAmplification (nodes m) q (K m)) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hK.eventually (eventually_ge_atTop (max 1 (R + 1)))] with m hm
  have hKm : 1 ≤ K m := le_trans (le_max_left _ _) hm
  have hgap := gapDifference_ge_sub_one_of_rightAdjacentCardinalAmplification
    (nodes m) q hKm (hamp m)
  rw [Real.norm_eq_abs]
  have hpos : 0 ≤ gapDifference (nodes m) q := by linarith
  rw [abs_of_nonneg hpos]
  have hR : R + 1 ≤ K m := le_trans (le_max_right _ _) hm
  linarith
def LeftNeighborBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ (nodes : ℕ → EndpointArray d A B) (q : Fin d),
    Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ) atTop (nhds 0) →
    (∃ δ > 0, ∀ᶠ m in atTop, δ ≤ endpointSpacing (nodes m) q.castSucc) →
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop
def RightNeighborBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ (nodes : ℕ → EndpointArray d A B) (q : Fin d),
    Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc) atTop (nhds 0) →
    (∃ δ > 0, ∀ᶠ m in atTop, δ ≤ endpointSpacing (nodes m) q.succ) →
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop
theorem boundaryEscape_leftNeighbor (d : ℕ) (A B : ℝ) :
    LeftNeighborBoundaryEscapeStatement d A B := by
  intro nodes q hzero hdelta
  rcases hdelta with ⟨delta, hdelta, hlower⟩
  have hK := tendsto_boundaryAmplification_atTop_of_upperSpacing
    nodes q hzero hdelta hlower
  exact tendsto_norm_gapDifference_atTop_of_amplification nodes q
    (fun m ↦ boundaryAmplification (nodes m) q) hK
    (fun m ↦ adjacentCardinalAmplification_boundaryAmplification (nodes m) q)
theorem boundaryEscape_rightNeighbor (d : ℕ) (A B : ℝ) :
    RightNeighborBoundaryEscapeStatement d A B := by
  intro nodes q hzero hdelta
  rcases hdelta with ⟨delta, hdelta, hupper⟩
  have hK := tendsto_rightBoundaryAmplification_atTop_of_lowerSpacing
    nodes q hzero hdelta hupper
  exact tendsto_norm_gapDifference_atTop_of_rightAmplification nodes q
    (fun m ↦ rightBoundaryAmplification (nodes m) q) hK
    (fun m ↦ rightAdjacentCardinalAmplification_rightBoundaryAmplification
      (nodes m) q)
lemma exists_adjacent_zero_positive {d : ℕ} (s : Fin (d + 1) → ℝ)
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    ∃ q : Fin d,
      (0 < s q.castSucc ∧ s q.succ = 0) ∨
        (s q.castSucc = 0 ∧ 0 < s q.succ) := by
  induction d with
  | zero =>
      obtain ⟨z, hz⟩ := hzero
      obtain ⟨p, hp⟩ := hpos
      have hz0 : z = 0 := Fin.eq_zero z
      have hp0 : p = 0 := Fin.eq_zero p
      rw [hz0] at hz
      rw [hp0, hz] at hp
      exact (lt_irrefl 0 hp).elim
  | succ d ih =>
      let tail : Fin (d + 1) → ℝ := fun i ↦ s i.succ
      by_cases h0 : s 0 = 0
      · by_cases h1 : s (Fin.succ 0) = 0
        · have htailZero : ∃ g, tail g = 0 := ⟨0, h1⟩
          obtain ⟨p, hp⟩ := hpos
          have hp0 : p ≠ 0 := by
            intro hpzero
            subst p
            rw [h0] at hp
            exact (lt_irrefl 0 hp)
          obtain ⟨p', rfl⟩ := Fin.exists_succ_eq.mpr hp0
          have htailPos : ∃ g, 0 < tail g := ⟨p', hp⟩
          obtain ⟨q, hq⟩ := ih tail (fun g ↦ hs g.succ) htailZero htailPos
          refine ⟨q.succ, ?_⟩
          simpa [tail] using hq
        · refine ⟨0, Or.inr ⟨h0, ?_⟩⟩
          exact lt_of_le_of_ne (hs (Fin.succ 0)) (Ne.symm h1)
      · have h0pos : 0 < s 0 := lt_of_le_of_ne (hs 0) (Ne.symm h0)
        by_cases h1 : s (Fin.succ 0) = 0
        · exact ⟨0, Or.inl ⟨h0pos, h1⟩⟩
        · have htailPos : ∃ g, 0 < tail g :=
            ⟨0, lt_of_le_of_ne (hs (Fin.succ 0)) (Ne.symm h1)⟩
          obtain ⟨z, hz⟩ := hzero
          have hz0 : z ≠ 0 := by
            intro hzzero
            subst z
            exact h0 hz
          obtain ⟨z', rfl⟩ := Fin.exists_succ_eq.mpr hz0
          have htailZero : ∃ g, tail g = 0 := ⟨z', hz⟩
          obtain ⟨q, hq⟩ := ih tail (fun g ↦ hs g.succ) htailZero htailPos
          refine ⟨q.succ, ?_⟩
          simpa [tail] using hq
theorem exists_coordinate_escape_of_boundarySpacingProfile
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (s : Fin (d + 1) → ℝ)
    (hconv : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes m) g) atTop (nhds (s g)))
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    ∃ q : Fin d,
      Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  obtain ⟨q, hq⟩ := exists_adjacent_zero_positive s hs hzero hpos
  refine ⟨q, ?_⟩
  rcases hq with hleft | hright
  · have hzero' : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
        atTop (nhds 0) := by simpa [hleft.2] using hconv q.succ
    have hevent : ∀ᶠ m in atTop,
        s q.castSucc / 2 ≤ endpointSpacing (nodes m) q.castSucc :=
      ((hconv q.castSucc).eventually_const_lt (half_lt_self hleft.1)).mono
        fun _ h ↦ h.le
    exact boundaryEscape_leftNeighbor d A B nodes q hzero'
      ⟨s q.castSucc / 2, half_pos hleft.1, hevent⟩
  · have hzero' : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
        atTop (nhds 0) := by simpa [hright.1] using hconv q.castSucc
    have hevent : ∀ᶠ m in atTop,
        s q.succ / 2 ≤ endpointSpacing (nodes m) q.succ :=
      ((hconv q.succ).eventually_const_lt (half_lt_self hright.2)).mono
        fun _ h ↦ h.le
    exact boundaryEscape_rightNeighbor d A B nodes q hzero'
      ⟨s q.succ / 2, half_pos hright.2, hevent⟩
theorem tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (s : Fin (d + 1) → ℝ)
    (hconv : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes m) g) atTop (nhds (s g)))
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop := by
  obtain ⟨q, hq⟩ := exists_coordinate_escape_of_boundarySpacingProfile
    nodes s hconv hs hzero hpos
  exact tendsto_atTop_mono
    (fun m ↦ norm_le_pi_norm (gapDifference (nodes m)) q) hq
def closedSpacingBox (d : ℕ) (A B : ℝ) : Set (Fin (d + 1) → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Icc 0 (B - A)
lemma isCompact_closedSpacingBox (d : ℕ) (A B : ℝ) :
    IsCompact (closedSpacingBox d A B) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc
lemma endpointSpacing_mem_closedSpacingBox {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    endpointSpacing nodes ∈ closedSpacingBox d A B := by
  intro g _hg
  constructor
  · exact (endpointSpacing_pos nodes g).le
  · calc
      endpointSpacing nodes g ≤ ∑ i, endpointSpacing nodes i :=
        Finset.single_le_sum
          (fun i _ ↦ (endpointSpacing_pos nodes i).le) (Finset.mem_univ g)
      _ = B - A := sum_endpointSpacing nodes
theorem exists_convergent_spacing_subsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) :
    ∃ (s : Fin (d + 1) → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) ∧
      (∀ g, 0 ≤ s g) ∧
      ∑ g, s g = B - A := by
  obtain ⟨s, hsbox, φ, hφ, hlim⟩ :=
    (isCompact_closedSpacingBox d A B).tendsto_subseq
      (fun m ↦ endpointSpacing_mem_closedSpacingBox (nodes m))
  have hcoord : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
      atTop (nhds (s g)) := by
    intro g
    have h := (tendsto_pi_nhds.mp hlim) g
    simpa only [Function.comp_apply] using h
  have hsumlim : Tendsto
      (fun m ↦ ∑ g, endpointSpacing (nodes (φ m)) g)
      atTop (nhds (∑ g, s g)) :=
    tendsto_finset_sum Finset.univ fun g _ ↦ hcoord g
  have hsumlim' : Tendsto (fun _ : ℕ ↦ B - A)
      atTop (nhds (∑ g, s g)) := by
    simpa only [sum_endpointSpacing] using hsumlim
  have hsum : ∑ g, s g = B - A :=
    tendsto_nhds_unique hsumlim' tendsto_const_nhds
  exact ⟨s, φ, hφ, hcoord, fun g ↦ (hsbox g (Set.mem_univ g)).1, hsum⟩
def HasNoConvergentEndpointSubsequence {d : ℕ} {A B : ℝ}
    (nodes : ℕ → EndpointArray d A B) : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ limit : EndpointArray d A B,
    ¬ Tendsto (fun m ↦ nodes (φ m)) atTop (nhds limit)
theorem exists_boundary_spacing_subsequence_of_noConvergentEndpointSubsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    ∃ (s : Fin (d + 1) → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) ∧
      (∀ g, 0 ≤ s g) ∧ (∃ g, s g = 0) ∧ (∃ g, 0 < s g) := by
  obtain ⟨s, φ, hφ, hconv, hs, hsum⟩ := exists_convergent_spacing_subsequence nodes
  have hzero : ∃ g, s g = 0 := by
    by_contra h
    push_neg at h
    have hspos : ∀ g, 0 < s g := fun g ↦ lt_of_le_of_ne (hs g) (Ne.symm (h g))
    let σ : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} :=
      ⟨s, hspos, hsum⟩
    have hsub : Tendsto
        (fun m ↦ ⟨endpointSpacing (nodes (φ m)),
          endpointSpacing_mem_positiveSpacingSimplex (nodes (φ m))⟩)
        atTop (nhds σ) := by
      apply tendsto_subtype_rng.mpr
      exact tendsto_pi_nhds.mpr hconv
    have hAB : AdmissibleInterval A B := (nodes 0).admissibleInterval
    have hnodes :=
      ((endpointArraySpacingHomeomorph hAB).continuous_invFun.tendsto σ).comp hsub
    have hnodes' : Tendsto (fun m ↦ nodes (φ m)) atTop
        (nhds (endpointArrayOfSpacings hAB σ)) := by
      change Tendsto
        (fun m ↦ endpointArrayOfSpacings hAB
          ⟨endpointSpacing (nodes (φ m)),
            endpointSpacing_mem_positiveSpacingSimplex (nodes (φ m))⟩)
        atTop (nhds (endpointArrayOfSpacings hAB σ)) at hnodes
      simpa only [endpointArrayOfSpacings_endpointSpacing] using hnodes
    exact hno φ hφ (endpointArrayOfSpacings hAB σ) hnodes'
  have hpos : ∃ g, 0 < s g := by
    have hp := (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (fun g _ ↦ hs g)).mp (by
        rw [hsum]
        exact sub_pos.mpr (nodes 0).endpoints_lt)
    obtain ⟨g, _hgmem, hg⟩ := hp
    exact ⟨g, hg⟩
  exact ⟨s, φ, hφ, hconv, hs, hzero, hpos⟩
theorem exists_subsequence_tendsto_norm_gapDifference_atTop
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m ↦ ‖gapDifference (nodes (φ m))‖) atTop atTop := by
  obtain ⟨s, φ, hφ, hconv, hs, hzero, hpos⟩ :=
    exists_boundary_spacing_subsequence_of_noConvergentEndpointSubsequence nodes hno
  exact ⟨φ, hφ,
    tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
      (fun m ↦ nodes (φ m)) s hconv hs hzero hpos⟩
theorem tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  by_contra hR
  have hfreq : ∃ᶠ m in atTop, ¬ R ≤ ‖gapDifference (nodes m)‖ := by
    exact Filter.not_eventually.mp hR
  obtain ⟨φ, hφ, hbound⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hnoφ : HasNoConvergentEndpointSubsequence (fun m ↦ nodes (φ m)) := by
    intro ψ hψ limit hlim
    apply hno (φ ∘ ψ) (hφ.comp hψ) limit
    simpa only [Function.comp_apply] using hlim
  obtain ⟨ψ, _hψ, hescape⟩ :=
    exists_subsequence_tendsto_norm_gapDifference_atTop
      (fun m ↦ nodes (φ m)) hnoφ
  have hevent := hescape.eventually_ge_atTop R
  obtain ⟨m, hm⟩ := hevent.exists
  exact hbound (ψ m) hm
def GapDifferenceTopologicalPropernessStatement (d : ℕ) (A B : ℝ) : Prop :=
  IsProperMap (gapDifference : EndpointArray d A B → Fin d → ℝ)
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Filter Topology
noncomputable section
lemma exists_norm_bound_of_isCompact {d : ℕ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) :
    ∃ C : ℝ, ∀ y ∈ K, ‖y‖ ≤ C :=
  (isBounded_iff_forall_norm_le (s := K)).mp hK.isBounded
theorem isCompact_preimage_gapDifference_of_continuous
    {d : ℕ} {A B : ℝ}
    (hcont : Continuous
      (gapDifference : EndpointArray d A B → Fin d → ℝ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    IsCompact
      ((gapDifference : EndpointArray d A B → Fin d → ℝ) ⁻¹' K) := by
  classical
  let S : Set (EndpointArray d A B) :=
    (gapDifference : EndpointArray d A B → Fin d → ℝ) ⁻¹' K
  by_cases hSne : S.Nonempty
  · let base : EndpointArray d A B := hSne.some
    have hAB : AdmissibleInterval A B := base.admissibleInterval
    let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
      endpointArrayLogRatioHomeomorph hAB
    have himageSeq : IsSeqCompact (e '' S) := by
      intro z hz
      let nodes : ℕ → EndpointArray d A B := fun m ↦ e.symm (z m)
      have hnodesMem : ∀ m, nodes m ∈ S := by
        intro m
        obtain ⟨x, hxS, hx⟩ := hz m
        have hnodes : nodes m = x := by
          apply e.injective
          simp only [nodes, Homeomorph.apply_symm_apply, hx]
        simpa only [hnodes] using hxS
      have hnotNo : ¬ HasNoConvergentEndpointSubsequence nodes := by
        intro hno
        have hescape :=
          tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence
            nodes hno
        obtain ⟨C, hC⟩ := exists_norm_bound_of_isCompact hK
        obtain ⟨m, hm⟩ := (hescape.eventually_ge_atTop (C + 1)).exists
        have hmem : gapDifference (nodes m) ∈ K := hnodesMem m
        linarith [hC (gapDifference (nodes m)) hmem]
      unfold HasNoConvergentEndpointSubsequence at hnotNo
      push_neg at hnotNo
      obtain ⟨φ, hφ, limit, hlim⟩ := hnotNo
      have hlimitS : limit ∈ S := by
        apply hK.isClosed.mem_of_tendsto
          ((hcont.tendsto limit).comp hlim)
        exact Eventually.of_forall fun m ↦ hnodesMem (φ m)
      refine ⟨e limit, ⟨limit, hlimitS, rfl⟩, φ, hφ, ?_⟩
      have heLim := (e.continuous.tendsto limit).comp hlim
      convert heLim using 1
      all_goals try rfl
      funext m
      exact (e.apply_symm_apply (z (φ m))).symm
    have himageCompact : IsCompact (e '' S) := himageSeq.isCompact
    have hSCompact : IsCompact S := e.isCompact_image.mp himageCompact
    exact hSCompact
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    change IsCompact S
    rw [hSempty]
    exact isCompact_empty
theorem gapDifference_isProperMap_of_continuous
    {d : ℕ} {A B : ℝ}
    (hcont : Continuous
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, ?_⟩
  intro K hK
  exact isCompact_preimage_gapDifference_of_continuous hcont hK
def GapDifferenceContinuityStatement (d : ℕ) (A B : ℝ) : Prop :=
  Continuous (gapDifference : EndpointArray d A B → Fin d → ℝ)
theorem gapDifference_topologicalProperness_of_continuity
    {d : ℕ} {A B : ℝ} :
    GapDifferenceContinuityStatement d A B →
      GapDifferenceTopologicalPropernessStatement d A B :=
  gapDifference_isProperMap_of_continuous
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Function Topology
noncomputable section
theorem isCoveringMap_of_isLocalHomeomorph_of_isProperMap
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X] {f : E → X}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsCoveringMap f := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph
  · intro x hx
    have hdisc : IsDiscrete (f ⁻¹' {x}) :=
      IsDiscrete.of_openPartialHomeomorph f Set.Subset.rfl fun e he ↦ by
        obtain ⟨φ, heφ, hφ⟩ := hloc e
        exact ⟨φ, heφ, hφ.symm⟩
    exact (hproper.isCompact_preimage isCompact_singleton).finite hdisc
  · intro e he
    obtain ⟨φ, heφ, hφ⟩ := hloc e
    exact ⟨φ, heφ, hφ⟩
theorem IsCoveringMap.isHomeomorph_of_surjective
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [Nonempty X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : E → X} (hcover : IsCoveringMap f) (hsurj : Surjective f) :
    IsHomeomorph f := by
  let x₀ : X := Classical.arbitrary X
  obtain ⟨e₀, he₀⟩ := hsurj x₀
  let fid : C(X, X) := ContinuousMap.id X
  obtain ⟨s, hs, _⟩ :=
    hcover.existsUnique_continuousMap_lifts fid x₀ e₀ (by simpa [fid] using he₀)
  obtain ⟨hs₀, hfs⟩ := hs
  have hsf : (s : X → E) ∘ f = id := by
    refine hcover.eq_of_comp_eq
      (s.continuous.comp hcover.continuous) continuous_id ?_ e₀ ?_
    · funext e
      have hright := congrFun hfs (f e)
      simpa [fid, Function.comp_def] using hright
    · simpa [he₀] using hs₀
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨hcover.continuous, s, ?_, ?_, s.continuous⟩
  · intro e
    exact congrFun hsf e
  · intro x
    have hright := congrFun hfs x
    simpa [fid, Function.comp_def] using hright
theorem fin_zero_isHomeomorph_of_isLocalHomeomorph
    {f : (Fin 0 → ℝ) → (Fin 0 → ℝ)}
    (hloc : IsLocalHomeomorph f) : IsHomeomorph f := by
  have hinj : Injective f := fun _ _ _ ↦ Subsingleton.elim _ _
  have hsurj : Surjective f := fun y ↦ ⟨0, Subsingleton.elim _ _⟩
  exact (hloc.toHomeomorphOfBijective ⟨hinj, hsurj⟩).isHomeomorph
theorem euclidean_isHomeomorph_of_isLocalHomeomorph_of_isProperMap
    {d : ℕ} {f : (Fin d → ℝ) → (Fin d → ℝ)}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsHomeomorph f := by
  cases d with
  | zero => exact fin_zero_isHomeomorph_of_isLocalHomeomorph hloc
  | succ d =>
    have hcover : IsCoveringMap f :=
      isCoveringMap_of_isLocalHomeomorph_of_isProperMap hloc hproper
    have hrangeOpen : IsOpen (Set.range f) := by
      simpa only [Set.image_univ] using hloc.isOpenMap Set.univ isOpen_univ
    have hrangeClosed : IsClosed (Set.range f) := hproper.isClosed_range
    have hrangeNonempty : (Set.range f).Nonempty :=
      ⟨f 0, 0, rfl⟩
    have hrange : Set.range f = Set.univ :=
      IsClopen.eq_univ ⟨hrangeClosed, hrangeOpen⟩ hrangeNonempty
    exact IsCoveringMap.isHomeomorph_of_surjective hcover
      (Set.range_eq_univ.mp hrange)
def transportedGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  gapDifference ∘ (endpointArrayLogRatioHomeomorph hAB).symm
theorem isLocalHomeomorph_transportedGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hloc : IsLocalHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsLocalHomeomorph (transportedGapDifference (d := d) hAB) := by
  exact hloc.comp (endpointArrayLogRatioHomeomorph (d := d) hAB).symm.isLocalHomeomorph
theorem isProperMap_transportedGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hproper : IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsProperMap (transportedGapDifference (d := d) hAB) := by
  exact hproper.comp (endpointArrayLogRatioHomeomorph (d := d) hAB).symm.isProperMap
theorem gapDifference_isHomeomorph_of_localHomeomorph_of_proper
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hloc : IsLocalHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ))
    (hproper : IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  have htransport : IsHomeomorph (transportedGapDifference (d := d) hAB) :=
    euclidean_isHomeomorph_of_isLocalHomeomorph_of_isProperMap
      (isLocalHomeomorph_transportedGapDifference hAB hloc)
      (isProperMap_transportedGapDifference hAB hproper)
  have hchart : IsHomeomorph (endpointArrayLogRatioHomeomorph (d := d) hAB) :=
    (endpointArrayLogRatioHomeomorph (d := d) hAB).isHomeomorph
  have hcomp := htransport.comp hchart
  simpa only [transportedGapDifference, Function.comp_assoc,
    Homeomorph.symm_comp_self, Function.id_comp, Function.comp_id] using hcomp
def GapDifferenceLocalHomeomorphStatement (d : ℕ) (A B : ℝ) : Prop :=
  IsLocalHomeomorph
    (gapDifference : EndpointArray d A B → Fin d → ℝ)
theorem gapDifference_homeomorphismStatement_of_localHomeomorph_of_proper
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B)
    (hproper : GapDifferenceTopologicalPropernessStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B := by
  intro hAB
  exact gapDifference_isHomeomorph_of_localHomeomorph_of_proper hAB hloc hproper
theorem gapDifference_homeomorphismStatement_of_localHomeomorph_of_continuous
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B)
    (hcont : GapDifferenceContinuityStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph_of_proper hloc
    (gapDifference_topologicalProperness_of_continuity hcont)
theorem gapDifference_homeomorphismStatement_of_localHomeomorph
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph_of_continuous
    hloc hloc.continuous
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Function Topology unitInterval
noncomputable section
def tailGapHeight {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i ↦ nodes.height i.succ
theorem equioscillates_iff_gapDifference_eq_zero
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Equioscillates nodes ↔
      gapDifference nodes = (0 : Fin d → ℝ) := by
  constructor
  · intro heq
    funext i
    simp only [gapDifference, Pi.zero_apply, sub_eq_zero]
    exact heq i.succ i.castSucc
  · intro hzero
    have hadj (i : Fin d) :
        nodes.height i.succ = nodes.height i.castSucc := by
      have hi := congrFun hzero i
      simpa only [gapDifference, Pi.zero_apply, sub_eq_zero] using hi
    have hbase (i : Fin (d + 1)) :
        nodes.height i = nodes.height (0 : Fin (d + 1)) := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
          exact (hadj i).trans ih
    intro i j
    exact (hbase i).trans (hbase j).symm
theorem existsUniqueEquioscillating_of_gapDifferenceHomeomorphism
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B) :
    ExistsUniqueEquioscillatingStatement d A B := by
  intro hAB
  let hglobal := hhomeomorph hAB
  obtain ⟨nodes, hnodes⟩ := hglobal.surjective (0 : Fin d → ℝ)
  refine ⟨nodes, (equioscillates_iff_gapDifference_eq_zero nodes).2 hnodes, ?_⟩
  intro other hother
  apply hglobal.injective
  rw [(equioscillates_iff_gapDifference_eq_zero other).1 hother, hnodes]
structure GapHeightPathRayOrientationStatement (d : ℕ) (A B : ℝ) : Prop where
  lift_increasingSegment :
    ∀ (_hd : 1 ≤ d) (s : EndpointArray d A B) (y : Fin d → ℝ),
      (∀ i, tailGapHeight s i ≤ y i) →
      y ≠ tailGapHeight s →
      ∃ g : C(I, EndpointArray d A B),
        g 0 = s ∧
        (∀ u i,
          tailGapHeight (g u) i =
            (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i) ∧
        StrictAnti (fun u : I ↦ (g u).height (0 : Fin (d + 1)))
  lift_decreasingRay_to_firstDifference :
    ∀ (hd : 1 ≤ d) (r : EndpointArray d A B) (c : ℝ),
      c < gapDifference r ⟨0, hd⟩ →
      ∃ α : ℝ, 0 < α ∧
        ∃ g : C(I, EndpointArray d A B),
          g 0 = r ∧
          (∀ u i,
            tailGapHeight (g u) i =
              tailGapHeight r i - (u : ℝ) * α) ∧
          gapDifference (g 1) ⟨0, hd⟩ = c
theorem exists_tail_eq_and_height_zero_lt_of_le_of_ne
    {d : ℕ} {A B : ℝ}
    (horient : GapHeightPathRayOrientationStatement d A B)
    (hd : 1 ≤ d) (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) :
    ∃ r : EndpointArray d A B,
      tailGapHeight r = y ∧
        r.height (0 : Fin (d + 1)) < s.height (0 : Fin (d + 1)) := by
  obtain ⟨g, hgzero, hgtail, hganti⟩ :=
    horient.lift_increasingSegment hd s y hle hne
  refine ⟨g 1, ?_, ?_⟩
  · funext i
    simpa using hgtail 1 i
  · have hzeroOne : (0 : I) < 1 := zero_lt_one
    have hstrict := hganti hzeroOne
    simpa only [hgzero] using hstrict
lemma gapDifference_eq_of_tail_eq_sub_and_zero_eq
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    {q t : EndpointArray d A B} {α : ℝ}
    (htail : ∀ i, tailGapHeight q i = tailGapHeight t i - α)
    (hzero : gapDifference q ⟨0, hd⟩ =
      gapDifference t ⟨0, hd⟩) :
    gapDifference q = gapDifference t := by
  let i₀ : Fin d := ⟨0, hd⟩
  funext i
  by_cases hi : i = i₀
  · simpa only [hi] using hzero
  · have hiVal : i.val ≠ 0 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa only [i₀] using hval
    let j : Fin d := ⟨i.val - 1, by omega⟩
    have hjsucc : j.succ = i.castSucc := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [gapDifference, gapDifference]
    have hright := htail i
    have hleft := htail j
    simp only [tailGapHeight] at hright hleft
    rw [hjsucc] at hleft
    linarith
theorem gapHeightLeRigidity_of_homeomorphism_of_pathRayOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (horient : GapHeightPathRayOrientationStatement d A B) :
    GapHeightLeRigidityStatement d A B := by
  intro s t hle
  by_cases hd : d = 0
  · subst d
    exact endpointArray_zero_unique s t
  have hdpos : 1 ≤ d := by omega
  let i₀ : Fin d := ⟨0, hdpos⟩
  by_contra hst
  have htailCases : tailGapHeight s = tailGapHeight t ∨
      tailGapHeight s ≠ tailGapHeight t := eq_or_ne _ _
  obtain ⟨r, hrtail, hrzero⟩ :
      ∃ r : EndpointArray d A B,
        tailGapHeight r = tailGapHeight t ∧
          r.height (0 : Fin (d + 1)) < t.height (0 : Fin (d + 1)) := by
    rcases htailCases with htailEq | htailNe
    · refine ⟨s, htailEq, ?_⟩
      have hzeroLe := hle (0 : Fin (d + 1))
      exact lt_of_le_of_ne hzeroLe fun heq ↦ by
        apply hst
        apply (hhomeomorph s.admissibleInterval).injective
        apply gapDifference_eq_of_tail_eq_sub_and_zero_eq
          (hd := hdpos) (α := 0)
        · intro i
          have htail := congrFun htailEq i
          simpa using htail
        · rw [gapDifference, gapDifference]
          have htail := congrFun htailEq i₀
          simp only [tailGapHeight] at htail
          change s.height i₀.succ - s.height i₀.castSucc =
            t.height i₀.succ - t.height i₀.castSucc
          have hi₀cast : i₀.castSucc = (0 : Fin (d + 1)) := by
            apply Fin.ext
            rfl
          rw [hi₀cast, heq]
          exact congrArg (fun z ↦ z - t.height (0 : Fin (d + 1))) htail
    · have htailLe : ∀ i, tailGapHeight s i ≤ tailGapHeight t i := by
        intro i
        exact hle i.succ
      obtain ⟨r, hrtail, hrs⟩ :=
        exists_tail_eq_and_height_zero_lt_of_le_of_ne
          horient hdpos s (tailGapHeight t) htailLe htailNe.symm
      exact ⟨r, hrtail, hrs.trans_le (hle (0 : Fin (d + 1)))⟩
  have hfirst : gapDifference t i₀ < gapDifference r i₀ := by
    rw [gapDifference, gapDifference]
    have htail0 := congrFun hrtail i₀
    simp only [tailGapHeight] at htail0
    have hi₀cast : i₀.castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext
      rfl
    rw [hi₀cast]
    linarith
  obtain ⟨α, hα, g, hgzero, hgtail, hgfirst⟩ :=
    horient.lift_decreasingRay_to_firstDifference hdpos r
      (gapDifference t i₀) hfirst
  let q : EndpointArray d A B := g 1
  have hqtail : ∀ i, tailGapHeight q i = tailGapHeight t i - α := by
    intro i
    have hpath := hgtail 1 i
    calc
      tailGapHeight q i = tailGapHeight r i - α := by simpa [q] using hpath
      _ = tailGapHeight t i - α := by rw [congrFun hrtail i]
  have hqzero : gapDifference q i₀ = gapDifference t i₀ := by
    simpa [q] using hgfirst
  have hqdiff : gapDifference q = gapDifference t :=
    gapDifference_eq_of_tail_eq_sub_and_zero_eq hdpos hqtail hqzero
  have hqt : q = t :=
    (hhomeomorph t.admissibleInterval).injective hqdiff
  have hshift := hqtail i₀
  rw [hqt] at hshift
  linarith
theorem comparisonPackage_of_homeomorphism_of_pathRayOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (horient : GapHeightPathRayOrientationStatement d A B) :
    ComparisonPackage d A B where
  gapHeight_le_rigidity :=
    gapHeightLeRigidity_of_homeomorphism_of_pathRayOrientation
      hhomeomorph horient
  exists_unique_equioscillating :=
    existsUniqueEquioscillating_of_gapDifferenceHomeomorphism hhomeomorph
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Filter Function Topology unitInterval
open scoped BigOperators
noncomputable section
def heightZeroCramerCoefficient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (k : Fin d) : ℝ :=
  (-1 : ℝ) ^ (k.val + 2) *
    deletedRowMinor (gapHeightJacobianModel nodes) k.succ /
      deletedRowMinor (gapHeightJacobianModel nodes) ⟨0, by omega⟩
def CoherentHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
    ∀ omitted : Fin (d + 1),
      0 < sign * (-1 : ℝ) ^ (omitted.val + 1) *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted
theorem deletedRowMinor_ne_zero_of_coherentSigns
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (hsigns : CoherentHeightMaximalMinorSigns nodes)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted ≠ 0 := by
  obtain ⟨sign, hsignValue, hsign⟩ := hsigns
  intro hzero
  have h := hsign omitted
  rw [hzero, mul_zero] at h
  linarith
theorem heightZeroCramerCoefficient_neg_of_coherentSigns
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns nodes) (k : Fin d) :
    heightZeroCramerCoefficient nodes hd k < 0 := by
  obtain ⟨sign, hsignValue, hsign⟩ := hsigns
  let D₀ : ℝ := deletedRowMinor (gapHeightJacobianModel nodes) ⟨0, by omega⟩
  let Dk : ℝ := deletedRowMinor (gapHeightJacobianModel nodes) k.succ
  let sk : ℝ := (-1 : ℝ) ^ (k.val + 2)
  have h₀ : 0 < sign * (-1 : ℝ) * D₀ := by
    simpa only [D₀, Fin.val_zero, zero_add, pow_one] using
      hsign (⟨0, by omega⟩ : Fin (d + 1))
  have hk : 0 < sign * sk * Dk := by
    simpa only [Dk, sk, Fin.val_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hsign k.succ
  have hsignSq : sign * sign = 1 := by
    rcases hsignValue with rfl | rfl <;> norm_num
  have hsignD₀ : sign * D₀ < 0 := by nlinarith
  have hsignSkDk : 0 < sign * (sk * Dk) := by
    nlinarith
  have hprod : sk * Dk * D₀ < 0 := by
    have hmul := mul_neg_of_pos_of_neg hsignSkDk hsignD₀
    calc
      sk * Dk * D₀ = (sign * (sk * Dk)) * (sign * D₀) := by
        symm
        calc
          (sign * (sk * Dk)) * (sign * D₀) =
              (sign * sign) * (sk * Dk * D₀) := by ring
          _ = sk * Dk * D₀ := by rw [hsignSq, one_mul]
      _ < 0 := hmul
  have hD₀ : D₀ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at h₀
    linarith
  have hD₀sq : 0 < D₀ ^ 2 := sq_pos_of_ne_zero hD₀
  rw [heightZeroCramerCoefficient]
  change sk * Dk / D₀ < 0
  rw [show sk * Dk / D₀ = (sk * Dk * D₀) / D₀ ^ 2 by
    field_simp]
  exact div_neg_of_neg_of_pos hprod hD₀sq
structure OrientedTailHeightChart {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) where
  chart : OpenPartialHomeomorph (EndpointArray d A B) (Fin d → ℝ)
  mem_source : nodes ∈ chart.source
  chart_eq :
    (tailGapHeight : EndpointArray d A B → Fin d → ℝ) = chart
  convex_target : Convex ℝ chart.target
  height_zero_strictAnti : ∀ {y z : Fin d → ℝ},
    y ∈ chart.target → z ∈ chart.target →
      (∀ i, y i ≤ z i) → y ≠ z →
        (chart.symm z).height (0 : Fin (d + 1)) <
          (chart.symm y).height (0 : Fin (d + 1))
def TailHeightLocalOrientationStatement (d : ℕ) (A B : ℝ) : Prop :=
  Continuous
    (fun nodes : EndpointArray d A B ↦
      nodes.height (0 : Fin (d + 1))) ∧
    ∀ (_hd : 1 ≤ d) (nodes : EndpointArray d A B),
      Nonempty (OrientedTailHeightChart nodes)
theorem tailGapHeight_isLocalHomeomorph_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hlocal : TailHeightLocalOrientationStatement d A B) (hd : 1 ≤ d) :
    IsLocalHomeomorph
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) := by
  intro nodes
  let e := (hlocal.2 hd nodes).some
  exact ⟨e.chart, e.mem_source, e.chart_eq⟩
theorem continuous_tailGapHeight_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hlocal : TailHeightLocalOrientationStatement d A B) (hd : 1 ≤ d) :
    Continuous
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) :=
  (tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd).continuous
lemma OrientedTailHeightChart.tail_mem_target
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) :
    tailGapHeight nodes ∈ e.chart.target := by
  rw [e.chart_eq]
  exact e.chart.map_source e.mem_source
@[simp]
lemma OrientedTailHeightChart.symm_tail_eq
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) :
    e.chart.symm (tailGapHeight nodes) = nodes := by
  rw [e.chart_eq]
  exact e.chart.left_inv e.mem_source
def tailLine {d : ℕ} (y z : Fin d → ℝ) (u : I) : Fin d → ℝ :=
  fun i ↦ (1 - (u : ℝ)) * y i + (u : ℝ) * z i
lemma continuous_tailLine {d : ℕ} (y z : Fin d → ℝ) :
    Continuous (tailLine y z) := by
  unfold tailLine
  fun_prop
lemma tailLine_mem_segment {d : ℕ} (y z : Fin d → ℝ) (u : I) :
    tailLine y z u ∈ segment ℝ y z := by
  rw [segment_eq_image_lineMap]
  refine ⟨(u : ℝ), u.2, ?_⟩
  funext i
  simp only [tailLine, AffineMap.lineMap_apply_module, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
def OrientedTailHeightChart.liftSegment
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) :
    C(I, EndpointArray d A B) where
  toFun u := e.chart.symm (tailLine y z u)
  continuous_toFun := by
    apply e.chart.continuousOn_invFun.comp_continuous
      (continuous_tailLine y z)
    intro u
    exact e.convex_target.segment_subset hy hz (tailLine_mem_segment y z u)
@[simp]
lemma OrientedTailHeightChart.liftSegment_zero
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) :
    e.liftSegment hy hz 0 = e.chart.symm y := by
  change e.chart.symm (tailLine y z 0) = e.chart.symm y
  congr 1
  funext i
  simp [tailLine]
@[simp]
lemma OrientedTailHeightChart.liftSegment_one
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) :
    e.liftSegment hy hz 1 = e.chart.symm z := by
  change e.chart.symm (tailLine y z 1) = e.chart.symm z
  congr 1
  funext i
  simp [tailLine]
def differenceOfBaseTail {d : ℕ} (z : ℝ × (Fin d → ℝ)) : Fin d → ℝ :=
  fun i ↦ if hi : i.val = 0 then z.2 i - z.1
    else z.2 i - z.2 ⟨i.val - 1, by omega⟩
lemma continuous_differenceOfBaseTail {d : ℕ} :
    Continuous (differenceOfBaseTail :
      ℝ × (Fin d → ℝ) → Fin d → ℝ) := by
  apply continuous_pi
  intro i
  unfold differenceOfBaseTail
  split_ifs
  · fun_prop
  · fun_prop
lemma differenceOfBaseTail_height_eq_gapDifference
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    differenceOfBaseTail
      (nodes.height (0 : Fin (d + 1)), tailGapHeight nodes) =
        gapDifference nodes := by
  funext i
  unfold differenceOfBaseTail gapDifference
  split_ifs with hi
  · have hcast : i.castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext
      exact hi
    rw [hcast]
    rfl
  · let j : Fin d := ⟨i.val - 1, by omega⟩
    have hjsucc : j.succ = i.castSucc := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    simp only [tailGapHeight]
    rw [hjsucc]
def tailHeightSlab {d : ℕ} {A B : ℝ}
    (K : Set (Fin d → ℝ)) (a b : ℝ) : Set (EndpointArray d A B) :=
  {nodes | tailGapHeight nodes ∈ K ∧
    nodes.height (0 : Fin (d + 1)) ∈ Set.Icc a b}
theorem isCompact_tailHeightSlab
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (a b : ℝ) :
    IsCompact (tailHeightSlab (A := A) (B := B) K a b) := by
  let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
    (hhomeomorph hAB).homeomorph gapDifference
  let box : Set (ℝ × (Fin d → ℝ)) := Set.Icc a b ×ˢ K
  have hbox : IsCompact box := isCompact_Icc.prod hK
  have hslabClosed :
      IsClosed (tailHeightSlab (A := A) (B := B) K a b) := by
    have htail : Continuous
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ) :=
      continuous_tailGapHeight_of_localOrientation hlocal hd
    exact (hK.isClosed.preimage htail).inter
      (isClosed_Icc.preimage hlocal.1)
  have himageClosed :
      IsClosed (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    e.isClosedMap _ hslabClosed
  have hboundContainer :=
    (hbox.image continuous_differenceOfBaseTail).isBounded
  have himageSubset :
      e '' tailHeightSlab (A := A) (B := B) K a b ⊆
        differenceOfBaseTail '' box := by
    rintro y ⟨nodes, hnodes, rfl⟩
    refine ⟨(nodes.height (0 : Fin (d + 1)), tailGapHeight nodes), ?_, ?_⟩
    · exact ⟨hnodes.2, hnodes.1⟩
    · exact differenceOfBaseTail_height_eq_gapDifference nodes
  have himageBounded :=
    hboundContainer.subset himageSubset
  have himageCompact :
      IsCompact (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨himageClosed, himageBounded⟩
  exact e.isCompact_image.mp himageCompact
theorem exists_convergent_subsequence_of_tailHeightSlab
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (a b : ℝ)
    (nodes : ℕ → EndpointArray d A B)
    (hnodes : ∀ n, nodes n ∈ tailHeightSlab K a b) :
    ∃ limit ∈ tailHeightSlab K a b, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (nodes ∘ phi) atTop (𝓝 limit) := by
  let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
    endpointArrayLogRatioHomeomorph hAB
  have hslab : IsCompact (tailHeightSlab (A := A) (B := B) K a b) :=
    isCompact_tailHeightSlab hd hAB hhomeomorph hlocal hK a b
  have himage : IsCompact (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    hslab.image e.continuous
  obtain ⟨z, hz, phi, hphi, htend⟩ := himage.isSeqCompact
    (fun n ↦ ⟨nodes n, hnodes n, rfl⟩)
  refine ⟨e.symm z, ?_, phi, hphi, ?_⟩
  · obtain ⟨limit, hlimit, rfl⟩ := hz
    simpa only [e.symm_apply_apply] using hlimit
  · have hpull := (e.symm.continuous.tendsto z).comp htend
    convert hpull using 1
    all_goals try rfl
    funext n
    simp
structure PrefixLift {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (gamma : ℝ → X) (e0 : E) (u : ℝ) where
  toFun : ℝ → E
  continuousOn : ContinuousOn toFun (Set.Icc 0 u)
  zero_eq : toFun 0 = e0
  map_eq : Set.EqOn (f ∘ toFun) gamma (Set.Icc 0 u)
namespace PrefixLift
instance {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u : ℝ} :
    CoeFun (PrefixLift f gamma e0 u) (fun _ ↦ ℝ → E) :=
  ⟨PrefixLift.toFun⟩
def zero {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} (hzero : f e0 = gamma 0) :
    PrefixLift f gamma e0 0 where
  toFun := fun _ ↦ e0
  continuousOn := continuous_const.continuousOn
  zero_eq := rfl
  map_eq := by
    intro t ht
    have ht0 : t = 0 := by exact le_antisymm ht.2 ht.1
    subst t
    exact hzero
def restrict {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v : ℝ}
    (L : PrefixLift f gamma e0 u) (_hv : 0 ≤ v) (hvu : v ≤ u) :
    PrefixLift f gamma e0 v where
  toFun := L
  continuousOn := L.continuousOn.mono fun _ ht ↦
    ⟨ht.1, ht.2.trans hvu⟩
  zero_eq := L.zero_eq
  map_eq := by
    intro t ht
    exact L.map_eq ⟨ht.1, ht.2.trans hvu⟩
def appendChart {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v : ℝ}
    (L : PrefixLift f gamma e0 u) (hu : 0 ≤ u) (_huv : u ≤ v)
    (chart : OpenPartialHomeomorph E X) (hsource : L u ∈ chart.source)
    (hchart : f = chart) (hgamma : Continuous gamma)
    (htarget : ∀ t ∈ Set.Icc u v, gamma t ∈ chart.target) :
    PrefixLift f gamma e0 v where
  toFun t := if t ≤ u then L t else chart.symm (gamma t)
  continuousOn := by
    apply ContinuousOn.if (p := fun t : ℝ ↦ t ≤ u)
    · intro t ht
      have htEq : t = u := by
        have htfront := ht.2
        change t ∈ frontier (Set.Iic u) at htfront
        simpa using htfront
      subst t
      have hmap : f (L u) = gamma u :=
        L.map_eq ⟨hu, le_rfl⟩
      calc
        L u = chart.symm (chart (L u)) := (chart.left_inv hsource).symm
        _ = chart.symm (f (L u)) :=
          congrArg chart.symm (congrFun hchart (L u)).symm
        _ = chart.symm (gamma u) := by rw [hmap]
    · apply L.continuousOn.mono
      rintro t ⟨ht, htclosure⟩
      have htu : t ≤ u := by
        change t ∈ closure (Set.Iic u) at htclosure
        rwa [closure_Iic] at htclosure
      exact ⟨ht.1, htu⟩
    · apply chart.continuousOn_invFun.comp hgamma.continuousOn
      rintro t ⟨ht, htclosure⟩
      have hut : u ≤ t := by
        rw [show {a : ℝ | ¬ a ≤ u} = Set.Ioi u by ext; simp] at htclosure
        rwa [closure_Ioi] at htclosure
      exact htarget t ⟨hut, ht.2⟩
  zero_eq := by
    simp only [if_pos hu, L.zero_eq]
  map_eq := by
    intro t ht
    by_cases htu : t ≤ u
    · simp only [Function.comp_apply, if_pos htu]
      exact L.map_eq ⟨ht.1, htu⟩
    · simp only [Function.comp_apply, if_neg htu]
      rw [hchart]
      exact chart.right_inv (htarget t ⟨le_of_not_ge htu, ht.2⟩)
@[simp]
theorem appendChart_apply_of_le
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v t : ℝ}
    (L : PrefixLift f gamma e0 u) (hu : 0 ≤ u) (huv : u ≤ v)
    (chart : OpenPartialHomeomorph E X) (hsource : L u ∈ chart.source)
    (hchart : f = chart) (hgamma : Continuous gamma)
    (htarget : ∀ r ∈ Set.Icc u v, gamma r ∈ chart.target)
    (htu : t ≤ u) :
    appendChart L hu huv chart hsource hchart hgamma htarget t = L t := by
  simp [appendChart, htu]
end PrefixLift
theorem exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {T : ℝ}
    (hloc : IsLocalHomeomorph f) (hgamma : Continuous gamma)
    (hT : 0 ≤ T) (hzero : f e0 = gamma 0)
    {K : Set E} (hK : IsSeqCompact K)
    (hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 T →
      ∀ L : PrefixLift f gamma e0 u, L u ∈ K) :
    Nonempty (PrefixLift f gamma e0 T) := by
  let Q := {u : ℝ // u ∈ Set.Icc 0 T}
  let S : Set Q := {u | Nonempty (PrefixLift f gamma e0 u.1)}
  have hSseq : IsSeqClosed S := by
    intro q p hq hp
    let L : ∀ n, PrefixLift f gamma e0 (q n).1 :=
      fun n ↦ (hq n).some
    let endpoint : ℕ → E := fun n ↦ L n (q n).1
    have hendpointK : ∀ n, endpoint n ∈ K := by
      intro n
      exact hendpoint (q n).2 (L n)
    obtain ⟨e, heK, phi, hphi, hephi⟩ := hK hendpointK
    have hqphi : Tendsto (fun n ↦ (q (phi n)).1) atTop (𝓝 p.1) := by
      exact (continuous_subtype_val.tendsto p).comp (hp.comp hphi.tendsto_atTop)
    have hmapEndpoint : ∀ n, f (endpoint n) = gamma (q n).1 := by
      intro n
      exact (L n).map_eq ⟨(q n).2.1, le_rfl⟩
    have hfe : f e = gamma p.1 := by
      have hleft := (hloc.continuous.tendsto e).comp hephi
      have hright := (hgamma.tendsto p.1).comp hqphi
      have hright' : Tendsto (fun n ↦ f (endpoint (phi n))) atTop
          (𝓝 (gamma p.1)) := by
        convert hright using 1
        all_goals try rfl
        funext n
        exact hmapEndpoint (phi n)
      exact tendsto_nhds_unique hleft hright'
    obtain ⟨chart, hesource, hchart⟩ := hloc e
    have hgammaTarget : gamma p.1 ∈ chart.target := by
      rw [← hfe, hchart]
      exact chart.map_source hesource
    have hopenPreimage : IsOpen (gamma ⁻¹' chart.target) :=
      chart.open_target.preimage hgamma
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopenPreimage
      p.1 hgammaTarget
    by_cases habove : ∃ n, p.1 ≤ (q n).1
    · obtain ⟨n, hn⟩ := habove
      exact ⟨(L n).restrict p.2.1 hn⟩
    · have hbelow : ∀ n, (q n).1 < p.1 := by
        intro n
        exact lt_of_not_ge fun h ↦ habove ⟨n, h⟩
      have heventSource : ∀ᶠ n in atTop, endpoint (phi n) ∈ chart.source :=
        hephi.eventually (chart.open_source.mem_nhds hesource)
      have heventBall : ∀ᶠ n in atTop,
          (q (phi n)).1 ∈ Metric.ball p.1 eps :=
        hqphi.eventually (Metric.ball_mem_nhds p.1 heps)
      obtain ⟨n, hnsource, hnball⟩ :=
        (heventSource.and heventBall).exists
      have htarget : ∀ t ∈ Set.Icc (q (phi n)).1 p.1,
          gamma t ∈ chart.target := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq] at hnball ⊢
        have hleft := hbelow (phi n)
        have habsLeft : |(q (phi n)).1 - p.1| = p.1 - (q (phi n)).1 := by
          rw [abs_of_nonpos (sub_nonpos.mpr hleft.le)]
          ring
        have habs : |t - p.1| = p.1 - t := by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          ring
        rw [habsLeft] at hnball
        rw [habs]
        have hqt := ht.1
        linarith
      exact ⟨(L (phi n)).appendChart (q (phi n)).2.1
        (hbelow (phi n)).le chart hnsource hchart hgamma htarget⟩
  have hSclosed : IsClosed S := hSseq.isClosed
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    let L : PrefixLift f gamma e0 q.1 := hq.some
    obtain ⟨chart, hsource, hchart⟩ := hloc (L q.1)
    have hmap : f (L q.1) = gamma q.1 :=
      L.map_eq ⟨q.2.1, le_rfl⟩
    have hgammaTarget : gamma q.1 ∈ chart.target := by
      exact hmap ▸ (congrFun hchart (L q.1)).symm ▸
        chart.map_source hsource
    have hopenPreimage : IsOpen (gamma ⁻¹' chart.target) :=
      chart.open_target.preimage hgamma
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopenPreimage
      q.1 hgammaTarget
    let V : Set Q := {r | r.1 < q.1 + eps}
    have hVopen : IsOpen V := by
      exact isOpen_lt continuous_subtype_val continuous_const
    have hqV : q ∈ V := by
      dsimp only [V]
      exact lt_add_of_pos_right q.1 heps
    apply Filter.mem_of_superset (hVopen.mem_nhds hqV)
    intro r hr
    by_cases hrq : r.1 ≤ q.1
    · exact ⟨L.restrict r.2.1 hrq⟩
    · have hqr : q.1 ≤ r.1 := le_of_not_ge hrq
      have htarget : ∀ t ∈ Set.Icc q.1 r.1,
          gamma t ∈ chart.target := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |t - q.1| = t - q.1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        rw [habs]
        have hrv : r.1 < q.1 + eps := hr
        have htr := ht.2
        linarith
      exact ⟨L.appendChart q.2.1 hqr chart hsource hchart hgamma htarget⟩
  have hSnonempty : S.Nonempty := by
    let q0 : Q := ⟨0, ⟨le_rfl, hT⟩⟩
    exact ⟨q0, ⟨PrefixLift.zero hzero⟩⟩
  letI : PreconnectedSpace Q :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSnonempty
  let qT : Q := ⟨T, ⟨hT, le_rfl⟩⟩
  have hqT : qT ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hqT
def realTailLine {d : ℕ} (y z : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i ↦ (1 - t) * y i + t * z i
lemma continuous_realTailLine {d : ℕ} (y z : Fin d → ℝ) :
    Continuous (realTailLine y z) := by
  unfold realTailLine
  fun_prop
theorem PrefixLift.heightZero_endpoint_le_of_realTailLine
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u) :
    (L u).height (0 : Fin (d + 1)) ≤
      s.height (0 : Fin (d + 1)) := by
  let H : ℝ → ℝ := fun t ↦ (L t).height (0 : Fin (d + 1))
  have hHcont : ContinuousOn H (Set.Icc 0 u) := by
    exact hlocal.1.comp_continuousOn L.continuousOn
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, ⟨le_rfl, hu.1⟩⟩ hHcont
  by_contra hnot
  have hendGt : H 0 < H u := by
    simpa only [H, L.zero_eq] using lt_of_not_ge hnot
  have htGt : H 0 < H t := hendGt.trans_le (hmax ⟨hu.1, le_rfl⟩)
  have htpos : 0 < t := by
    exact lt_of_le_of_ne ht.1 fun htzero ↦ by
      subst t
      exact (lt_irrefl _ htGt).elim
  let e := (hlocal.2 hd (L t)).some
  have hpre : L ⁻¹' e.chart.source ∈ 𝓝[Set.Icc 0 u] t :=
    (L.continuousOn t ht).preimage_mem_nhdsWithin
      (e.chart.open_source.mem_nhds e.mem_source)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let delta : ℝ := min (t / 2) (eps / 2)
  let r : ℝ := t - delta
  have hdelta : 0 < delta := by
    exact lt_min (half_pos htpos) (half_pos heps)
  have hdeltat : delta < t :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self htpos)
  have hdeltaeps : delta < eps :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self heps)
  have hrlt : r < t := by dsimp only [r]; linarith
  have hrmem : r ∈ Set.Icc 0 u := by
    constructor
    · dsimp only [r]
      linarith
    · exact hrlt.le.trans ht.2
  have hrball : r ∈ Metric.ball t eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |r - t| = delta := by
      dsimp only [r]
      rw [show t - delta - t = -delta by ring, abs_neg,
        abs_of_pos hdelta]
    rw [habs]
    exact hdeltaeps
  have hrsource : L r ∈ e.chart.source :=
    hball ⟨hrball, hrmem⟩
  have htailR : tailGapHeight (L r) =
      realTailLine (tailGapHeight s) y r :=
    L.map_eq hrmem
  have htailT : tailGapHeight (L t) =
      realTailLine (tailGapHeight s) y t :=
    L.map_eq ht
  have htailLe : ∀ i, tailGapHeight (L r) i ≤
      tailGapHeight (L t) i := by
    intro i
    rw [htailR, htailT]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hex : ∃ i, tailGapHeight s i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (h i) (hle i)
  obtain ⟨i0, hi0⟩ := hex
  have htailNe : tailGapHeight (L r) ≠ tailGapHeight (L t) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailR, htailT] at hi
    unfold realTailLine at hi
    nlinarith
  have htailEqChartR : tailGapHeight (L r) = e.chart (L r) :=
    congrFun e.chart_eq (L r)
  have htailRtarget : tailGapHeight (L r) ∈ e.chart.target := by
    exact htailEqChartR.symm ▸ e.chart.map_source hrsource
  have hdecrease := e.height_zero_strictAnti
    htailRtarget e.tail_mem_target htailLe htailNe
  have hsymmR : e.chart.symm (tailGapHeight (L r)) = L r := by
    exact (congrArg e.chart.symm htailEqChartR).trans
      (e.chart.left_inv hrsource)
  rw [hsymmR, e.symm_tail_eq] at hdecrease
  exact (not_lt_of_ge (hmax hrmem) hdecrease).elim
def PrefixLift.reparamRealTailLine
    {d : ℕ} {A B : ℝ} {s : EndpointArray d A B}
    {y : Fin d → ℝ} {u a b : ℝ}
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u)
    (ha : a ∈ Set.Icc 0 u) (hb : b ∈ Set.Icc 0 u) (hab : a ≤ b) :
    PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight (L a)) (tailGapHeight (L b)))
      (L a) 1 where
  toFun t := L ((1 - t) * a + t * b)
  continuousOn := by
    apply L.continuousOn.comp (by fun_prop)
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
  zero_eq := by simp
  map_eq := by
    intro t ht
    have hw : (1 - t) * a + t * b ∈ Set.Icc 0 u := by
      constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
    have hmain := L.map_eq hw
    have hleft := L.map_eq ha
    have hright := L.map_eq hb
    simp only [Function.comp_apply] at hmain hleft hright ⊢
    funext i
    have hmaini := congrFun hmain i
    have hlefti := congrFun hleft i
    have hrighti := congrFun hright i
    unfold realTailLine at hmaini hlefti hrighti ⊢
    rw [hmaini, hlefti, hrighti]
    ring
theorem PrefixLift.heightZero_endpoint_lt_of_realTailLine
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) {u : ℝ} (hu0 : 0 < u) (_hu1 : u ≤ 1)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u) :
    (L u).height (0 : Fin (d + 1)) <
      s.height (0 : Fin (d + 1)) := by
  let e := (hlocal.2 hd s).some
  have hpre : L ⁻¹' e.chart.source ∈ 𝓝[Set.Icc 0 u] 0 :=
    (L.continuousOn 0 ⟨le_rfl, hu0.le⟩).preimage_mem_nhdsWithin
      (e.chart.open_source.mem_nhds (by simpa [L.zero_eq] using e.mem_source))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let delta : ℝ := min (u / 2) (eps / 2)
  have hdelta : 0 < delta :=
    lt_min (half_pos hu0) (half_pos heps)
  have hdeltau : delta < u :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hu0)
  have hdeltaeps : delta < eps :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self heps)
  have hdeltamem : delta ∈ Set.Icc 0 u := ⟨hdelta.le, hdeltau.le⟩
  have hdeltaball : delta ∈ Metric.ball (0 : ℝ) eps := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdelta]
    exact hdeltaeps
  have hdeltasource : L delta ∈ e.chart.source :=
    hball ⟨hdeltaball, hdeltamem⟩
  have htailZero : tailGapHeight (L 0) = tailGapHeight s := by
    rw [L.zero_eq]
  have htailDelta : tailGapHeight (L delta) =
      realTailLine (tailGapHeight s) y delta :=
    L.map_eq hdeltamem
  have htailLe : ∀ i, tailGapHeight s i ≤ tailGapHeight (L delta) i := by
    intro i
    rw [htailDelta]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hex : ∃ i, tailGapHeight s i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (h i) (hle i)
  obtain ⟨i0, hi0⟩ := hex
  have htailNe : tailGapHeight s ≠ tailGapHeight (L delta) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailDelta] at hi
    unfold realTailLine at hi
    nlinarith
  have htailDeltaTarget : tailGapHeight (L delta) ∈ e.chart.target := by
    have heq : tailGapHeight (L delta) = e.chart (L delta) :=
      congrFun e.chart_eq (L delta)
    exact heq.symm ▸ e.chart.map_source hdeltasource
  have hfirst := e.height_zero_strictAnti e.tail_mem_target
    htailDeltaTarget htailLe htailNe
  have hsymmDelta : e.chart.symm (tailGapHeight (L delta)) = L delta := by
    have heq : tailGapHeight (L delta) = e.chart (L delta) :=
      congrFun e.chart_eq (L delta)
    exact (congrArg e.chart.symm heq).trans
      (e.chart.left_inv hdeltasource)
  rw [e.symm_tail_eq, hsymmDelta] at hfirst
  let M := L.reparamRealTailLine hdeltamem ⟨hu0.le, le_rfl⟩ hdeltau.le
  have htailU : tailGapHeight (L u) =
      realTailLine (tailGapHeight s) y u :=
    L.map_eq ⟨hu0.le, le_rfl⟩
  have hsuffixLe : ∀ i, tailGapHeight (L delta) i ≤
      tailGapHeight (L u) i := by
    intro i
    rw [htailDelta, htailU]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hsuffixNe : tailGapHeight (L u) ≠ tailGapHeight (L delta) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailU, htailDelta] at hi
    unfold realTailLine at hi
    nlinarith
  have hsuffix := M.heightZero_endpoint_le_of_realTailLine hd hlocal
    (L delta) (tailGapHeight (L u)) hsuffixLe hsuffixNe
    (u := 1) ⟨zero_le_one, le_rfl⟩
  have hfinal := hsuffix.trans_lt hfirst
  change (L ((1 - (1 : ℝ)) * delta + (1 : ℝ) * u)).height
      (0 : Fin (d + 1)) < s.height (0 : Fin (d + 1)) at hfinal
  simpa using hfinal
theorem exists_increasingSegment_lift_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) :
    ∃ g : C(I, EndpointArray d A B),
      g 0 = s ∧
      (∀ u i, tailGapHeight (g u) i =
        (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i) ∧
      StrictAnti (fun u : I ↦
        (g u).height (0 : Fin (d + 1))) := by
  letI : T2Space (EndpointArray d A B) :=
    (endpointArrayLogRatioHomeomorph s.admissibleInterval).isEmbedding.t2Space
  let gamma : ℝ → (Fin d → ℝ) := realTailLine (tailGapHeight s) y
  let K : Set (EndpointArray d A B) := tailHeightSlab
    (segment ℝ (tailGapHeight s) y) 1
      (s.height (0 : Fin (d + 1)))
  have hsegment : IsCompact (segment ℝ (tailGapHeight s) y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hKseq : IsSeqCompact K := by
    intro nodes hnodes
    exact exists_convergent_subsequence_of_tailHeightSlab hd
      s.admissibleInterval hhomeomorph hlocal hsegment 1
        (s.height (0 : Fin (d + 1))) nodes hnodes
  have hloc := tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd
  have hgamma : Continuous gamma := continuous_realTailLine _ _
  have hzero : tailGapHeight s = gamma 0 := by
    funext i
    simp [gamma, realTailLine]
  have hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 1 →
      ∀ L : PrefixLift
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
        gamma s u, L u ∈ K := by
    intro u hu L
    constructor
    · have htail : tailGapHeight (L u) = gamma u :=
        L.map_eq ⟨hu.1, le_rfl⟩
      rw [htail]
      rw [segment_eq_image_lineMap]
      refine ⟨u, hu, ?_⟩
      funext i
      simp only [gamma, realTailLine, AffineMap.lineMap_apply_module,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · constructor
      · exact one_le_height (L u) (0 : Fin (d + 1))
      · exact L.heightZero_endpoint_le_of_realTailLine hd hlocal s y hle hne hu
  obtain ⟨L⟩ := exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    hloc hgamma (T := 1) zero_le_one hzero hKseq hendpoint
  let g : C(I, EndpointArray d A B) :=
    ⟨fun u ↦ L u, continuousOn_iff_continuous_restrict.mp L.continuousOn⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · exact L.zero_eq
  · intro u i
    have hmap := L.map_eq u.2
    have hi := congrFun hmap i
    exact hi
  · intro u v huv
    have huMem : (u : ℝ) ∈ Set.Icc 0 1 := u.2
    have hvMem : (v : ℝ) ∈ Set.Icc 0 1 := v.2
    let M := L.reparamRealTailLine huMem hvMem huv.le
    have htailU : tailGapHeight (L (u : ℝ)) = gamma (u : ℝ) :=
      L.map_eq huMem
    have htailV : tailGapHeight (L (v : ℝ)) = gamma (v : ℝ) :=
      L.map_eq hvMem
    have htailLe : ∀ i, tailGapHeight (L (u : ℝ)) i ≤
        tailGapHeight (L (v : ℝ)) i := by
      intro i
      rw [htailU, htailV]
      dsimp only [gamma, realTailLine]
      have hi := hle i
      nlinarith [show (u : ℝ) < (v : ℝ) from huv]
    have hex : ∃ i, tailGapHeight s i < y i := by
      by_contra h
      push_neg at h
      apply hne
      funext i
      exact le_antisymm (h i) (hle i)
    obtain ⟨i0, hi0⟩ := hex
    have htailNe : tailGapHeight (L (v : ℝ)) ≠
        tailGapHeight (L (u : ℝ)) := by
      intro heq
      have hi := congrFun heq i0
      rw [htailU, htailV] at hi
      dsimp only [gamma, realTailLine] at hi
      nlinarith [show (u : ℝ) < (v : ℝ) from huv]
    have hstrict := M.heightZero_endpoint_lt_of_realTailLine hd hlocal
      (L (u : ℝ)) (tailGapHeight (L (v : ℝ))) htailLe htailNe
      (u := 1) zero_lt_one (by rfl)
    change (L ((1 - (1 : ℝ)) * (u : ℝ) + (1 : ℝ) * (v : ℝ))).height
      (0 : Fin (d + 1)) <
        (L (u : ℝ)).height (0 : Fin (d + 1)) at hstrict
    norm_num at hstrict
    exact hstrict
def decreasingTailRay {d : ℕ} (y : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i ↦ y i - t
lemma continuous_decreasingTailRay {d : ℕ} (y : Fin d → ℝ) :
    Continuous (decreasingTailRay y) := by
  unfold decreasingTailRay
  fun_prop
theorem exists_stopped_decreasingRay_of_prefix_endpoint_le
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (r : EndpointArray d A B) (c : ℝ)
    (hc : c < gapDifference r ⟨0, hd⟩)
    {u : ℝ} (hu : 0 ≤ u)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (decreasingTailRay (tailGapHeight r)) r u)
    (hend : gapDifference (L u) ⟨0, hd⟩ ≤ c) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∃ g : C(I, EndpointArray d A B),
        g 0 = r ∧
        (∀ v i, tailGapHeight (g v) i =
          tailGapHeight r i - (v : ℝ) * alpha) ∧
        gapDifference (g 1) ⟨0, hd⟩ = c := by
  let F : ℝ → ℝ := fun t ↦ gapDifference (L t) ⟨0, hd⟩
  have hFcont : ContinuousOn F (Set.Icc 0 u) := by
    have hdiffCont :=
      (hhomeomorph r.admissibleInterval).continuous.comp_continuousOn
        L.continuousOn
    simpa only [F, Function.comp_def] using
      (continuous_apply ⟨0, hd⟩).comp_continuousOn hdiffCont
  have hFzero : F 0 = gapDifference r ⟨0, hd⟩ := by
    simp only [F, L.zero_eq]
  have hcIcc : c ∈ Set.Icc (F u) (F 0) := by
    exact ⟨hend, by simpa only [hFzero] using hc.le⟩
  obtain ⟨alpha, halphaMem, halphaEq⟩ :=
    intermediate_value_Icc' hu hFcont hcIcc
  have halpha : 0 < alpha := by
    exact lt_of_le_of_ne halphaMem.1 fun hzero ↦ by
      subst alpha
      rw [hFzero] at halphaEq
      exact (ne_of_gt hc) halphaEq
  let g : C(I, EndpointArray d A B) :=
    ⟨fun v ↦ L ((v : ℝ) * alpha), by
      apply L.continuousOn.comp_continuous
      · fun_prop
      · intro v
        exact ⟨mul_nonneg v.2.1 halpha.le,
          (mul_le_of_le_one_left halpha.le v.2.2).trans halphaMem.2⟩⟩
  refine ⟨alpha, halpha, g, ?_, ?_, ?_⟩
  · change L ((0 : ℝ) * alpha) = r
    rw [zero_mul, L.zero_eq]
  · intro v i
    have htime : (v : ℝ) * alpha ∈ Set.Icc 0 u :=
      ⟨mul_nonneg v.2.1 halpha.le,
        (mul_le_of_le_one_left halpha.le v.2.2).trans halphaMem.2⟩
    have hmap := L.map_eq htime
    have hi := congrFun hmap i
    exact hi
  · change gapDifference (L ((1 : ℝ) * alpha)) ⟨0, hd⟩ = c
    simpa only [one_mul, F] using halphaEq
theorem exists_decreasingRay_to_firstDifference_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (r : EndpointArray d A B) (c : ℝ)
    (hc : c < gapDifference r ⟨0, hd⟩) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∃ g : C(I, EndpointArray d A B),
        g 0 = r ∧
        (∀ v i, tailGapHeight (g v) i =
          tailGapHeight r i - (v : ℝ) * alpha) ∧
        gapDifference (g 1) ⟨0, hd⟩ = c := by
  let i0 : Fin d := ⟨0, hd⟩
  let T : ℝ := tailGapHeight r i0 - c
  have hi0cast : i0.castSucc = (0 : Fin (d + 1)) := by
    apply Fin.ext
    rfl
  have honeR : 1 ≤ r.height (0 : Fin (d + 1)) :=
    one_le_height r (0 : Fin (d + 1))
  have hdiffR : gapDifference r i0 =
      tailGapHeight r i0 - r.height (0 : Fin (d + 1)) := by
    rw [gapDifference, tailGapHeight, hi0cast]
  have hT : 0 < T := by
    rw [hdiffR] at hc
    dsimp only [T]
    linarith
  by_contra hno
  push_neg at hno
  letI : T2Space (EndpointArray d A B) :=
    (endpointArrayLogRatioHomeomorph r.admissibleInterval).isEmbedding.t2Space
  let gamma : ℝ → (Fin d → ℝ) := decreasingTailRay (tailGapHeight r)
  let tailEnd : Fin d → ℝ := gamma T
  let K : Set (EndpointArray d A B) := tailHeightSlab
    (segment ℝ (tailGapHeight r) tailEnd) 1 T
  have hsegment : IsCompact (segment ℝ (tailGapHeight r) tailEnd) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hKseq : IsSeqCompact K := by
    intro nodes hnodes
    exact exists_convergent_subsequence_of_tailHeightSlab hd
      r.admissibleInterval hhomeomorph hlocal hsegment 1 T nodes hnodes
  have hloc := tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd
  have hgamma : Continuous gamma := continuous_decreasingTailRay _
  have hzero : tailGapHeight r = gamma 0 := by
    funext i
    simp [gamma, decreasingTailRay]
  have hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 T →
      ∀ L : PrefixLift
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
        gamma r u, L u ∈ K := by
    intro u hu L
    have htail : tailGapHeight (L u) = gamma u :=
      L.map_eq ⟨hu.1, le_rfl⟩
    have hdiff : gapDifference (L u) i0 =
        tailGapHeight (L u) i0 -
          (L u).height (0 : Fin (d + 1)) := by
      rw [gapDifference, tailGapHeight, hi0cast]
    have hdiffGt : c < gapDifference (L u) i0 := by
      by_contra hleDiff
      have hstopped := exists_stopped_decreasingRay_of_prefix_endpoint_le
        hd hhomeomorph r c hc hu.1 L (le_of_not_gt hleDiff)
      obtain ⟨alpha, halpha, g, hg0, hgtail, hgend⟩ := hstopped
      exact hno alpha halpha g hg0 hgtail hgend
    constructor
    · rw [htail]
      rw [segment_eq_image_lineMap]
      refine ⟨u / T, ?_, ?_⟩
      · constructor
        · exact div_nonneg hu.1 hT.le
        · exact (div_le_one hT).2 hu.2
      · funext i
        simp only [tailEnd, gamma, decreasingTailRay,
          AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        field_simp
        ring
    · constructor
      · exact one_le_height (L u) (0 : Fin (d + 1))
      · rw [hdiff, htail] at hdiffGt
        have hgammaUi : gamma u i0 = tailGapHeight r i0 - u := rfl
        rw [hgammaUi] at hdiffGt
        dsimp only [T]
        have hu0 := hu.1
        linarith
  obtain ⟨L⟩ := exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    hloc hgamma hT.le hzero hKseq hendpoint
  have htailFinal : tailGapHeight (L T) = gamma T :=
    L.map_eq ⟨hT.le, le_rfl⟩
  have hdiffFinal : gapDifference (L T) i0 =
      tailGapHeight (L T) i0 -
        (L T).height (0 : Fin (d + 1)) := by
    rw [gapDifference, tailGapHeight, hi0cast]
  have honeFinal : 1 ≤ (L T).height (0 : Fin (d + 1)) :=
    one_le_height (L T) (0 : Fin (d + 1))
  have hfinalLe : gapDifference (L T) i0 ≤ c := by
    rw [hdiffFinal, htailFinal]
    dsimp only [gamma, decreasingTailRay, T]
    linarith
  obtain ⟨alpha, halpha, g, hg0, hgtail, hgend⟩ :=
    exists_stopped_decreasingRay_of_prefix_endpoint_le
      hd hhomeomorph r c hc hT.le L hfinalLe
  exact hno alpha halpha g hg0 hgtail hgend
theorem gapHeightPathRayOrientation_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B) :
    GapHeightPathRayOrientationStatement d A B where
  lift_increasingSegment hd s y hle hne :=
    exists_increasingSegment_lift_of_homeomorphism_of_localOrientation
      hd hhomeomorph hlocal s y hle hne
  lift_decreasingRay_to_firstDifference hd r c hc :=
    exists_decreasingRay_to_firstDifference_of_homeomorphism_of_localOrientation
      hd hhomeomorph hlocal r c hc
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
noncomputable section
theorem coherentHeightMaximalMinorSigns_of_alternating
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B)
    (h : AlternatingHeightMaximalMinorSigns nodes) :
    CoherentHeightMaximalMinorSigns nodes := by
  rcases h with hneg | hpos
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro omitted
    have hstrict := neg_pos.mpr (hneg omitted)
    calc
      0 < -((-1 : ℝ) ^ omitted.val *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted) := hstrict
      _ = (1 : ℝ) * (-1 : ℝ) ^ (omitted.val + 1) *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
        rw [pow_succ]
        ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro omitted
    calc
      0 < (-1 : ℝ) ^ omitted.val *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted :=
        hpos omitted
      _ = (-1 : ℝ) * (-1 : ℝ) ^ (omitted.val + 1) *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
        rw [pow_succ]
        ring
theorem coherentHeightMaximalMinorSigns_unconditional
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    CoherentHeightMaximalMinorSigns nodes :=
  coherentHeightMaximalMinorSigns_of_alternating nodes
    (alternatingHeightMaximalMinorSigns nodes)
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Filter Function Topology
noncomputable section
def gapDifferenceJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => gapHeightJacobianModel nodes i.succ j -
    gapHeightJacobianModel nodes i.castSucc j
def GapDifferenceJacobianDeterminantCondition (d : ℕ) (A B : ℝ) : Prop :=
  ∀ nodes : EndpointArray d A B,
    Matrix.det (gapDifferenceJacobianModel nodes) ≠ 0
lemma contDiffAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    ContDiffAt ℝ 1 (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  apply contDiffAt_finset_sum_scalar
  intro k _
  exact contDiffAt_const.mul (by
    simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
    let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
      fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
    have hfac : ∀ i ∈ Finset.univ.erase k,
        ContDiffAt ℝ 1 (fac i) (u.1, x) := by
      intro i hi
      exact contDiffAt_coordinateLagrangeFactorValue hAB u
        (Finset.mem_erase.mp hi).1.symm x 1
    exact contDiffAt_finset_prod_scalar 1 (Finset.univ.erase k) fac
      (u.1, x) hfac)
lemma contDiffAt_localGapCriticalHeight_concrete {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ContDiffAt ℝ 1
      (localGapCriticalHeight hAB u hd g
        (concreteGapCoordinateDerivativesAt hAB u g)) u.1 := by
  let data := concreteGapCoordinateDerivativesAt hAB u g
  have hpair : ContDiffAt ℝ 1
      (fun v : Fin d → ℝ =>
        (v, localGapCriticalPoint hAB u hd g data v)) u.1 :=
    contDiffAt_id.prodMk
      (contDiffAt_localGapCriticalPoint hAB u hd g data)
  have hvalue : ContDiffAt ℝ 1 (coordinateGapValueMap A B g)
      (u.1, localGapCriticalPoint hAB u hd g data u.1) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact contDiffAt_coordinateGapValueMap hAB u g
      (coordinateGapArgmax hAB u g)
  exact hvalue.comp u.1 hpair
lemma contDiffAt_canonicalExtendedCoordinateGapHeight {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ContDiffAt ℝ 1
      (canonicalExtendedCoordinateGapHeight hAB u hd g) u.1 := by
  let data := concreteGapCoordinateDerivativesAt hAB u g
  apply (contDiffAt_localGapCriticalHeight_concrete hAB u hd g).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 u.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  filter_upwards [hspace,
    eventually_localGapCriticalHeight_eq_coordinateGapHeight
      hAB u hd g data] with v hv heq
  rw [canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos hv]
  exact (heq hv).symm
lemma continuous_coordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (g : Fin (d + 1)) :
    Continuous (fun u : {v : Fin d → ℝ //
      v ∈ endpointNodeSpace d A B} => coordinateGapHeight hAB u g) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hd0 : d = 0
  · subst d
    have heq : (fun v : {w : Fin 0 → ℝ //
        w ∈ endpointNodeSpace 0 A B} => coordinateGapHeight hAB v g) =
        fun _ => (1 : ℝ) := by
      funext v
      exact coordinateGapHeight_zero_dim hAB v g
    rw [heq]
    exact continuousAt_const
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hamb :=
      (hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd g).continuousAt
    have hcomp := hamb.comp continuousAt_subtype_val
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with v
    change coordinateGapHeight hAB v g =
      canonicalExtendedCoordinateGapHeight hAB u hd g v.1
    rw [canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
      dif_pos v.2]
theorem continuous_endpointArray_height_of_admissible {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (g : Fin (d + 1)) :
    Continuous (fun nodes : EndpointArray d A B => nodes.height g) := by
  let H : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → ℝ :=
    fun u => coordinateGapHeight hAB u g
  have hH : Continuous H := continuous_coordinateGapHeight hAB g
  have heq : (fun nodes : EndpointArray d A B => nodes.height g) =
      H ∘ endpointArrayHomeomorph hAB := by
    funext nodes
    change nodes.height g = coordinateGapHeight hAB
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ g
    rw [coordinateGapHeight, endpointArrayOfInterior_interior]
    rfl
  rw [heq]
  exact hH.comp (endpointArrayHomeomorph hAB).continuous
theorem continuous_endpointArray_height {d : ℕ} {A B : ℝ}
    (g : Fin (d + 1)) :
    Continuous (fun nodes : EndpointArray d A B => nodes.height g) := by
  rw [continuous_iff_continuousAt]
  intro nodes
  exact (continuous_endpointArray_height_of_admissible
    nodes.admissibleInterval g).continuousAt
def canonicalExtendedCoordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) : (Fin d → ℝ) → Fin d → ℝ :=
  fun v i =>
    canonicalExtendedCoordinateGapHeight hAB u hd i.succ v -
      canonicalExtendedCoordinateGapHeight hAB u hd i.castSucc v
def gapDifferenceDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ) -
      (concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)
theorem hasFDerivAt_canonicalExtendedCoordinateGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateGapDifference hAB u hd)
      (gapDifferenceDifferentialAt hAB u hd) u.1 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).sub
    (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc)
theorem contDiffAt_canonicalExtendedCoordinateGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    ContDiffAt ℝ 1 (canonicalExtendedCoordinateGapDifference hAB u hd) u.1 := by
  rw [contDiffAt_pi]
  intro i
  exact (contDiffAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).sub
    (contDiffAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc)
theorem gapDifferenceDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (i j : Fin d) :
    gapDifferenceDifferentialAt hAB u hd (Pi.single j 1) i =
      gapDifferenceJacobianModel (endpointArrayOfInterior hAB u) i j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) -
      ((concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).fderiv,
    ← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc).fderiv,
    canonicalCoordinateGapHeight_fderiv_basis_eq_model,
    canonicalCoordinateGapHeight_fderiv_basis_eq_model]
  rfl
theorem gapDifferenceDifferentialAt_toMatrix_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    LinearMap.toMatrix' (gapDifferenceDifferentialAt hAB u hd).toLinearMap =
      gapDifferenceJacobianModel (endpointArrayOfInterior hAB u) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact gapDifferenceDifferentialAt_basis_eq_model hAB u hd i j
theorem gapDifferenceDifferentialAt_det_ne_zero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hdet : Matrix.det
      (gapDifferenceJacobianModel (endpointArrayOfInterior hAB u)) ≠ 0) :
    (gapDifferenceDifferentialAt hAB u hd).det ≠ 0 := by
  change LinearMap.det (gapDifferenceDifferentialAt hAB u hd).toLinearMap ≠ 0
  rw [← LinearMap.det_toMatrix',
    gapDifferenceDifferentialAt_toMatrix_eq_model hAB u hd]
  exact hdet
def coordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => gapDifference (endpointArrayOfInterior hAB v)
lemma canonicalExtendedCoordinateGapDifference_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    canonicalExtendedCoordinateGapDifference hAB u hd v.1 =
      coordinateGapDifference hAB v := by
  funext i
  simp only [canonicalExtendedCoordinateGapDifference,
    canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos v.2, coordinateGapDifference, gapDifference,
    coordinateGapHeight]
  rfl
theorem isLocalHomeomorph_coordinateGapDifference_of_determinant
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B) (hd : 1 ≤ d)
    (hdet : GapDifferenceJacobianDeterminantCondition d A B) :
    IsLocalHomeomorph (coordinateGapDifference (d := d) hAB) := by
  apply IsLocalHomeomorph.mk
  intro u
  let F := canonicalExtendedCoordinateGapDifference hAB u hd
  let L := gapDifferenceDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    gapDifferenceDifferentialAt_det_ne_zero hAB u hd
      (hdet (endpointArrayOfInterior hAB u))
  let eL : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    L.toContinuousLinearEquivOfDetNeZero hLdet
  have hFderiv : HasFDerivAt F (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    change HasFDerivAt (canonicalExtendedCoordinateGapDifference hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateGapDifference hAB u hd
  have hFcont : ContDiffAt ℝ 1 F u.1 :=
    contDiffAt_canonicalExtendedCoordinateGapDifference hAB u hd
  let e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
    hFcont.toOpenPartialHomeomorph F hFderiv (by norm_num)
  have hue : u.1 ∈ e.source :=
    hFcont.mem_toOpenPartialHomeomorph_source hFderiv (by norm_num)
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨endpointNodeSpace d A B, isOpen_endpointNodeSpace d A B⟩
  have hS : Nonempty S := ⟨u⟩
  let es : OpenPartialHomeomorph S (Fin d → ℝ) := e.subtypeRestr hS
  refine ⟨es, ?_, ?_⟩
  · simpa only [es, OpenPartialHomeomorph.subtypeRestr_source,
      Set.mem_preimage] using hue
  · intro v _hv
    change coordinateGapDifference hAB v = F v.1
    exact (canonicalExtendedCoordinateGapDifference_eq_coordinate
      hAB u v hd).symm
private theorem isLocalHomeomorph_gapDifference_zero
    {A B : ℝ} (hAB : AdmissibleInterval A B) :
    IsLocalHomeomorph
      (gapDifference : EndpointArray 0 A B → Fin 0 → ℝ) := by
  let u0 : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hu0 : u0 ∈ endpointNodeSpace 0 A B := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · exact fun i => Fin.elim0 i
  let S := {u : Fin 0 → ℝ // u ∈ endpointNodeSpace 0 A B}
  letI : Unique S := {
    default := ⟨u0, hu0⟩
    uniq := fun v => Subtype.ext (Subsingleton.elim _ _) }
  let e0 : S ≃ₜ (Fin 0 → ℝ) :=
    Homeomorph.homeomorphOfUnique S (Fin 0 → ℝ)
  let e : EndpointArray 0 A B ≃ₜ (Fin 0 → ℝ) :=
    (endpointArrayHomeomorph hAB).trans e0
  have heq : (gapDifference : EndpointArray 0 A B → Fin 0 → ℝ) = e := by
    funext nodes
    exact Subsingleton.elim _ _
  rw [heq]
  exact e.isLocalHomeomorph
theorem gapDifference_localHomeomorphStatement_of_determinant
    (d : ℕ) (A B : ℝ)
    (hdet : GapDifferenceJacobianDeterminantCondition d A B) :
    GapDifferenceLocalHomeomorphStatement d A B := by
  intro nodes
  let hAB : AdmissibleInterval A B := nodes.admissibleInterval
  by_cases hd0 : d = 0
  · subst d
    exact (isLocalHomeomorph_gapDifference_zero hAB) nodes
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hcoord :=
      isLocalHomeomorph_coordinateGapDifference_of_determinant hAB hd hdet
    have hchart := (endpointArrayHomeomorph (d := d) hAB).isLocalHomeomorph
    have hcomp := hcoord.comp hchart
    have heq :
        (gapDifference : EndpointArray d A B → Fin d → ℝ) =
          coordinateGapDifference hAB ∘ endpointArrayHomeomorph hAB := by
      funext r
      change gapDifference r = gapDifference
        (endpointArrayOfInterior hAB
          ⟨r.interior, r.interior_mem_endpointNodeSpace⟩)
      rw [endpointArrayOfInterior_interior]
    rw [heq]
    exact hcomp nodes
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
noncomputable section
theorem gapDifference_jacobianDeterminantCondition
    (d : ℕ) (A B : ℝ) :
    GapDifferenceJacobianDeterminantCondition d A B := by
  intro nodes
  exact gapHeightJacobianModel_consecutiveDifference_det_ne_zero nodes
theorem gapDifference_localHomeomorphStatement
    (d : ℕ) (A B : ℝ) :
    GapDifferenceLocalHomeomorphStatement d A B :=
  gapDifference_localHomeomorphStatement_of_determinant d A B
    (gapDifference_jacobianDeterminantCondition d A B)
theorem gapDifference_homeomorphismStatement
    (d : ℕ) (A B : ℝ) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph
    (gapDifference_localHomeomorphStatement d A B)
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
open Filter Function Topology
open scoped BigOperators Matrix
noncomputable section
def canonicalExtendedCoordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) : (Fin d → ℝ) → Fin d → ℝ :=
  fun v i => canonicalExtendedCoordinateGapHeight hAB u hd i.succ v
def tailHeightDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)
theorem hasFDerivAt_canonicalExtendedCoordinateTailHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB u hd)
      (tailHeightDifferentialAt hAB u hd) u.1 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd i.succ
theorem contDiffAt_canonicalExtendedCoordinateTailHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    ContDiffAt ℝ 1 (canonicalExtendedCoordinateTailHeight hAB u hd) u.1 := by
  rw [contDiffAt_pi]
  intro i
  exact contDiffAt_canonicalExtendedCoordinateGapHeight hAB u hd i.succ
theorem tailHeightDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (i j : Fin d) :
    tailHeightDifferentialAt hAB u hd (Pi.single j 1) i =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) i.succ j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB u hd i.succ).fderiv]
  exact canonicalCoordinateGapHeight_fderiv_basis_eq_model hAB u hd i.succ j
theorem tailHeightDifferentialAt_toMatrix_eq_deletedZero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    LinearMap.toMatrix' (tailHeightDifferentialAt hAB u hd).toLinearMap =
      (gapHeightJacobianModel (endpointArrayOfInterior hAB u)).submatrix
        (0 : Fin (d + 1)).succAbove id := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  simpa using tailHeightDifferentialAt_basis_eq_model hAB u hd i j
theorem tailHeightDifferentialAt_det_eq_deletedZero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    (tailHeightDifferentialAt hAB u hd).det =
      deletedRowMinor (gapHeightJacobianModel
        (endpointArrayOfInterior hAB u)) (0 : Fin (d + 1)) := by
  change LinearMap.det (tailHeightDifferentialAt hAB u hd).toLinearMap = _
  rw [← LinearMap.det_toMatrix',
    tailHeightDifferentialAt_toMatrix_eq_deletedZero hAB u hd]
  rfl
theorem tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (tailHeightDifferentialAt hAB u hd).det ≠ 0 := by
  rw [tailHeightDifferentialAt_det_eq_deletedZero hAB u hd]
  exact deletedRowMinor_ne_zero_of_coherentSigns hsigns _
private lemma updateRow_tailMatrix_eq_permuted_deletedRow
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    (H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0) =
      (H.submatrix k.succ.succAbove id).submatrix k.cycleRange id := by
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  ext i j
  by_cases hik : i = k
  · subst i
    simp
  · by_cases hil : i < k
    · rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_lt hil]
      rw [Fin.succAbove_succ_of_le k (i + 1) (by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one_of_lt' (by omega)]
        omega)]
      apply congrArg (fun q => H q j)
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_succ,
        Fin.val_add_one_of_lt' (by omega)]
    · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hil) (Ne.symm hik)
      rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_gt hki]
      rw [Fin.succAbove_succ_of_lt k i hki]
theorem det_updateRow_tailMatrix
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    ((H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0)).det =
      (-1 : ℝ) ^ (k.val + 2) * deletedRowMinor H k.succ := by
  rw [updateRow_tailMatrix_eq_permuted_deletedRow H k, Matrix.det_permute]
  simp only [Fin.sign_cycleRange, deletedRowMinor]
  norm_num [pow_add]
def heightZeroDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  (concreteGapCoordinateDerivativesAt hAB u (0 : Fin (d + 1))).valueDifferential.comp
    (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)
theorem heightZeroDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (j : Fin d) :
    heightZeroDifferentialAt hAB u (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) 0 j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u 0).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB u hd 0).fderiv]
  exact canonicalCoordinateGapHeight_fderiv_basis_eq_model hAB u hd 0 j
private lemma continuousLinearEquiv_symm_apply_eq_nonsingInv_mulVec
    {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) (hdet : L.det ≠ 0)
    (v : Fin d → ℝ) :
    (L.toContinuousLinearEquivOfDetNeZero hdet).symm v =
      ((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v := by
  let eL := L.toContinuousLinearEquivOfDetNeZero hdet
  apply eL.injective
  change L (eL.symm v) = L
    (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v)
  rw [show L (eL.symm v) = v by
    change eL (eL.symm v) = v
    exact eL.apply_symm_apply v]
  symm
  calc
    L (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v) =
        LinearMap.toMatrix' L.toLinearMap *ᵥ
          (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v) :=
      (LinearMap.toMatrix'_mulVec L.toLinearMap _).symm
    _ = ((LinearMap.toMatrix' L.toLinearMap) *
          (LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    _ = v := by
      rw [Matrix.mul_nonsing_inv]
      · exact Matrix.one_mulVec v
      · exact isUnit_iff_ne_zero.mpr (by
          rw [LinearMap.det_toMatrix']
          exact hdet)
theorem heightZeroDifferential_comp_tailInverse_basis
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) (k : Fin d) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap
        (Pi.single k 1) =
      heightZeroCramerCoefficient (endpointArrayOfInterior hAB u) hd k := by
  let H := gapHeightJacobianModel (endpointArrayOfInterior hAB u)
  let T := H.submatrix (0 : Fin (d + 1)).succAbove id
  let L := tailHeightDifferentialAt hAB u hd
  let D := heightZeroDifferentialAt hAB u
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  have hT : LinearMap.toMatrix' L.toLinearMap = T := by
    exact tailHeightDifferentialAt_toMatrix_eq_deletedZero hAB u hd
  have hTdet : T.det ≠ 0 := by
    rw [← hT, LinearMap.det_toMatrix']
    exact hLdet
  have hTunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hTdet
  have hD : ∀ j : Fin d, D (Pi.single j 1) = H 0 j := by
    intro j
    exact heightZeroDifferentialAt_basis_eq_model hAB u hd j
  have hinv :
      (L.toContinuousLinearEquivOfDetNeZero hLdet).symm (Pi.single k 1) =
        (T⁻¹) *ᵥ Pi.single k 1 := by
    rw [continuousLinearEquiv_symm_apply_eq_nonsingInv_mulVec L hLdet]
    rw [hT]
  change D ((L.toContinuousLinearEquivOfDetNeZero hLdet).symm
    (Pi.single k 1)) = _
  rw [hinv]
  have hD_apply (v : Fin d → ℝ) : D v = H 0 ⬝ᵥ v := by
    have hv : v = ∑ i : Fin d,
        (v i) • (Pi.single i (1 : ℝ) : Fin d → ℝ) :=
      pi_eq_sum_univ' v
    calc
      D v = D (∑ i : Fin d,
          (v i) • (Pi.single i (1 : ℝ) : Fin d → ℝ)) := congrArg D hv
      _ = ∑ i, v i * H 0 i := by
        simp only [map_sum, map_smul, smul_eq_mul, hD]
      _ = H 0 ⬝ᵥ v := by
        simp only [dotProduct]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hD_apply, Matrix.dotProduct_mulVec, dotProduct_single_one]
  have hcramer := Matrix.det_smul_inv_vecMul_eq_cramer_transpose
    T (H 0) hTunit
  have hcramerK := congrFun hcramer k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_transpose_apply] at hcramerK
  rw [det_updateRow_tailMatrix H k] at hcramerK
  rw [heightZeroCramerCoefficient]
  change (H 0 ᵥ* T⁻¹) k =
    (-1) ^ (k.val + 2) * deletedRowMinor H k.succ /
      deletedRowMinor H 0
  have hTdetMinor : T.det = deletedRowMinor H 0 := rfl
  rw [← hTdetMinor]
  apply (eq_div_iff hTdet).2
  nlinarith
def coordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => tailGapHeight (endpointArrayOfInterior hAB v)
lemma canonicalExtendedCoordinateTailHeight_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    canonicalExtendedCoordinateTailHeight hAB u hd v.1 =
      coordinateTailHeight hAB v := by
  funext i
  simp only [canonicalExtendedCoordinateTailHeight,
    canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos v.2, coordinateTailHeight, tailGapHeight,
    coordinateGapHeight]
  rfl
lemma canonicalExtendedCoordinateGapHeight_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    canonicalExtendedCoordinateGapHeight hAB u hd g v.1 =
      coordinateGapHeight hAB v g := by
  simp only [canonicalExtendedCoordinateGapHeight,
    extendedCoordinateGapHeight, dif_pos v.2]
theorem hasFDerivAt_canonicalTailHeight_at_simplexPoint
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base x : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB base hd)
      (tailHeightDifferentialAt hAB x hd) x.1 := by
  apply (hasFDerivAt_canonicalExtendedCoordinateTailHeight
    hAB x hd).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 x.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds x.2
  filter_upwards [hspace] with v hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  exact (canonicalExtendedCoordinateTailHeight_eq_coordinate
    hAB base v' hd).trans
      (canonicalExtendedCoordinateTailHeight_eq_coordinate hAB x v' hd).symm
theorem hasFDerivAt_canonicalHeightZero_at_simplexPoint
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base x : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateGapHeight hAB base hd 0)
      (heightZeroDifferentialAt hAB x) x.1 := by
  apply (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB x hd 0).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 x.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds x.2
  filter_upwards [hspace] with v hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  exact (canonicalExtendedCoordinateGapHeight_eq_coordinate
    hAB base v' hd 0).trans
      (canonicalExtendedCoordinateGapHeight_eq_coordinate hAB x v' hd 0).symm
theorem heightZeroDifferential_comp_tailInverse_apply
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) (w : Fin d → ℝ) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap w =
      ∑ k, w k * heightZeroCramerCoefficient
        (endpointArrayOfInterior hAB u) hd k := by
  let C := (heightZeroDifferentialAt hAB u).comp
    ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
      (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
        hAB u hd hsigns)).symm.toContinuousLinearMap
  have hw : w = ∑ k : Fin d,
      (w k) • (Pi.single k (1 : ℝ) : Fin d → ℝ) := pi_eq_sum_univ' w
  change C w = _
  calc
    C w = C (∑ k : Fin d,
        (w k) • (Pi.single k (1 : ℝ) : Fin d → ℝ)) := congrArg C hw
    _ = ∑ k, w k * C (Pi.single k 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [heightZeroDifferential_comp_tailInverse_basis hAB u hd hsigns k]
theorem heightZeroDifferential_comp_tailInverse_neg
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u))
    {w : Fin d → ℝ} (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap w < 0 := by
  rw [heightZeroDifferential_comp_tailInverse_apply hAB u hd hsigns w]
  have hex : ∃ k, 0 < w k := by
    by_contra hn
    push_neg at hn
    apply hw0
    funext k
    exact le_antisymm (hn k) (hw k)
  obtain ⟨k0, hk0⟩ := hex
  have hnonpos : ∀ k, w k * heightZeroCramerCoefficient
      (endpointArrayOfInterior hAB u) hd k ≤ 0 := by
    intro k
    exact mul_nonpos_of_nonneg_of_nonpos (hw k)
      (heightZeroCramerCoefficient_neg_of_coherentSigns
        _ hd hsigns k).le
  have hstrict : w k0 * heightZeroCramerCoefficient
      (endpointArrayOfInterior hAB u) hd k0 < 0 :=
    mul_neg_of_pos_of_neg hk0
      (heightZeroCramerCoefficient_neg_of_coherentSigns
        _ hd hsigns k0)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k0)]
  have herase : ∑ k ∈ Finset.univ.erase k0,
      w k * heightZeroCramerCoefficient
        (endpointArrayOfInterior hAB u) hd k ≤ 0 := by
    exact Finset.sum_nonpos fun k _ => hnonpos k
  linarith
private theorem hasFDerivAt_heightZero_through_ambientInverse
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (he : (e : (Fin d → ℝ) → Fin d → ℝ) =
      canonicalExtendedCoordinateTailHeight hAB base hd)
    {y : Fin d → ℝ} (hy : y ∈ e.target)
    (hyspace : e.symm y ∈ endpointNodeSpace d A B)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB ⟨e.symm y, hyspace⟩)) :
    HasFDerivAt
      (fun q => canonicalExtendedCoordinateGapHeight hAB
        ⟨e.symm y, hyspace⟩ hd 0 (e.symm q))
      ((heightZeroDifferentialAt hAB ⟨e.symm y, hyspace⟩).comp
        (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt hAB ⟨e.symm y, hyspace⟩ hd)
            (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
              hAB ⟨e.symm y, hyspace⟩ hd hsigns)).symm.toContinuousLinearMap) y := by
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨e.symm y, hyspace⟩
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have heDeriv : HasFDerivAt e (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ)
      (e.symm y) := by
    rw [he]
    change HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB base hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalTailHeight_at_simplexPoint hAB base u hd
  have heInv : HasFDerivAt e.symm
      (eL.symm : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) y :=
    e.hasFDerivAt_symm hy heDeriv
  have hzero := hasFDerivAt_canonicalHeightZero_at_simplexPoint
    hAB u u hd
  exact hzero.comp y heInv
def ambientTailHeightChart {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) := by
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have hderiv : HasFDerivAt
      (canonicalExtendedCoordinateTailHeight hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateTailHeight hAB u hd
  exact ContDiffAt.toOpenPartialHomeomorph
    (canonicalExtendedCoordinateTailHeight hAB u hd)
    (contDiffAt_canonicalExtendedCoordinateTailHeight hAB u hd)
    hderiv (by norm_num)
@[simp]
theorem ambientTailHeightChart_coe {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (ambientTailHeightChart hAB u hd hsigns :
      (Fin d → ℝ) → Fin d → ℝ) =
      canonicalExtendedCoordinateTailHeight hAB u hd := by
  simp only [ambientTailHeightChart]
  apply ContDiffAt.toOpenPartialHomeomorph_coe
theorem mem_ambientTailHeightChart_source {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    u.1 ∈ (ambientTailHeightChart hAB u hd hsigns).source := by
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have hderiv : HasFDerivAt
      (canonicalExtendedCoordinateTailHeight hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateTailHeight hAB u hd
  simpa only [ambientTailHeightChart] using
    (ContDiffAt.mem_toOpenPartialHomeomorph_source
      (contDiffAt_canonicalExtendedCoordinateTailHeight hAB u hd)
      hderiv (by norm_num))
def simplexTailHeightChart {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    OpenPartialHomeomorph
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} (Fin d → ℝ) :=
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨endpointNodeSpace d A B, isOpen_endpointNodeSpace d A B⟩
  (ambientTailHeightChart hAB u hd hsigns).subtypeRestr
    (show Nonempty S from ⟨u⟩)
theorem mem_simplexTailHeightChart_source {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    u ∈ (simplexTailHeightChart hAB u hd hsigns).source := by
  simpa only [simplexTailHeightChart,
    OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using
      mem_ambientTailHeightChart_source hAB u hd hsigns
@[simp]
theorem simplexTailHeightChart_coe {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (simplexTailHeightChart hAB u hd hsigns :
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ) =
      coordinateTailHeight hAB := by
  funext v
  rw [show (simplexTailHeightChart hAB u hd hsigns :
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ) v =
      (ambientTailHeightChart hAB u hd hsigns) v.1 by rfl]
  rw [ambientTailHeightChart_coe]
  exact canonicalExtendedCoordinateTailHeight_eq_coordinate hAB u v hd
private theorem hasFDerivAt_coordinateHeightZero_through_simplexInverse
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB base))
    {y : Fin d → ℝ}
    (hy : y ∈ (simplexTailHeightChart hAB base hd hbase).target) :
    let uy := (simplexTailHeightChart hAB base hd hbase).symm y
    HasFDerivAt
      (fun q => coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm q) 0)
      ((heightZeroDifferentialAt hAB uy).comp
        (ContinuousLinearEquiv.toContinuousLinearMap
          (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
            (tailHeightDifferentialAt hAB uy hd)
            (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
              hAB uy hd (hsignsAll (endpointArrayOfInterior hAB uy)))).symm)) y := by
  dsimp only
  let e := ambientTailHeightChart hAB base hd hbase
  let es := simplexTailHeightChart hAB base hd hbase
  let uy := es.symm y
  have hyAmbient : y ∈ e.target := by
    exact OpenPartialHomeomorph.subtypeRestr_target_subset e
      (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hy
  have hval : uy.1 = e.symm y := by
    change (Subtype.val ∘ es.symm) y = e.symm y
    exact e.subtypeRestr_symm_apply
      (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hy
  have hyspace : e.symm y ∈ endpointNodeSpace d A B := by
    rw [← hval]
    exact uy.2
  let ue : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨e.symm y, hyspace⟩
  have hue : ue = uy := Subtype.ext hval.symm
  have hderiv := hasFDerivAt_heightZero_through_ambientInverse
    hAB base hd e (ambientTailHeightChart_coe hAB base hd hbase)
    hyAmbient hyspace (hsignsAll (endpointArrayOfInterior hAB ue))
  have hevent : ∀ᶠ q in 𝓝 y, q ∈ es.target :=
    es.open_target.mem_nhds hy
  have heq :
      (fun q => coordinateGapHeight hAB (es.symm q) 0) =ᶠ[𝓝 y]
        (fun q => canonicalExtendedCoordinateGapHeight hAB ue hd 0 (e.symm q)) := by
    filter_upwards [hevent] with q hq
    have hqval : (es.symm q).1 = e.symm q := by
      change (Subtype.val ∘ es.symm) q = e.symm q
      exact e.subtypeRestr_symm_apply
        (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hq
    rw [← hqval]
    exact (canonicalExtendedCoordinateGapHeight_eq_coordinate
      hAB ue (es.symm q) hd 0).symm
  have hout := hderiv.congr_of_eventuallyEq heq
  convert hout using 1
  all_goals try rfl
  congr 3
  exact hue.symm
  congr 2
  exact hue.symm
private theorem coordinateHeightZero_strictAntiOn_convexTarget
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB base))
    {V : Set (Fin d → ℝ)}
    (hVconvex : Convex ℝ V)
    (hV : V ⊆ (simplexTailHeightChart hAB base hd hbase).target)
    {y z : Fin d → ℝ} (hy : y ∈ V) (hz : z ∈ V)
    (hyz : ∀ i, y i ≤ z i) (hyzNe : y ≠ z) :
    coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm z) 0 <
      coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm y) 0 := by
  let es := simplexTailHeightChart hAB base hd hbase
  let φ : ℝ → ℝ := fun t =>
    coordinateGapHeight hAB (es.symm (AffineMap.lineMap y z t)) 0
  let w : Fin d → ℝ := z - y
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact sub_nonneg.mpr (hyz i)
  have hw0 : w ≠ 0 := by
    intro hwzero
    apply hyzNe
    exact (sub_eq_zero.mp hwzero).symm
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AffineMap.lineMap y z t ∈ V :=
    hVconvex.lineMap_mem hy hz ht
  have hpathDeriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt φ
        (((heightZeroDifferentialAt hAB
            (es.symm (AffineMap.lineMap y z t))).comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
              (tailHeightDifferentialAt hAB
                (es.symm (AffineMap.lineMap y z t)) hd)
              (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB
                (es.symm (AffineMap.lineMap y z t)) hd
                (hsignsAll (endpointArrayOfInterior hAB
                  (es.symm (AffineMap.lineMap y z t)))))).symm)) w) t := by
    have houter :=
      hasFDerivAt_coordinateHeightZero_through_simplexInverse
        hAB base hd hsignsAll hbase
          (hV (hline t ht))
    have hcomp := houter.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := t))
    simpa only [φ, es, Function.comp_def, w] using hcomp
  have hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hpathDeriv t ht).continuousAt.continuousWithinAt
  have hderivNeg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv φ t < 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hpathDeriv t htIcc).deriv]
    exact heightZeroDifferential_comp_tailInverse_neg hAB
      (es.symm (AffineMap.lineMap y z t)) hd
      (hsignsAll (endpointArrayOfInterior hAB
        (es.symm (AffineMap.lineMap y z t)))) hw hw0
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) 1)
    hcont hderivNeg
  have h01 := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_lt_one
  simpa only [φ, es, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using h01
theorem nonempty_orientedTailHeightChart_of_coherentSigns
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (nodes : EndpointArray d A B) :
    Nonempty (OrientedTailHeightChart nodes) := by
  let hAB : AdmissibleInterval A B := nodes.admissibleInterval
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    (endpointArrayHomeomorph hAB) nodes
  have huNodes : endpointArrayOfInterior hAB u = nodes := by
    exact (endpointArrayHomeomorph hAB).symm_apply_apply nodes
  have hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u) := by
    rw [huNodes]
    exact hsignsAll nodes
  let es := simplexTailHeightChart hAB u hd hbase
  have huSource : u ∈ es.source :=
    mem_simplexTailHeightChart_source hAB u hd hbase
  let center : Fin d → ℝ := coordinateTailHeight hAB u
  have hcenter : center ∈ es.target := by
    have hmapped := es.map_source huSource
    change coordinateTailHeight hAB u ∈ es.target
    rw [← simplexTailHeightChart_coe hAB u hd hbase]
    exact hmapped
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp es.open_target center hcenter
  let ball : Set (Fin d → ℝ) := Metric.ball center r
  let esSmall : OpenPartialHomeomorph
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} (Fin d → ℝ) :=
    (es.symm.restrOpen ball Metric.isOpen_ball).symm
  have hesSmallTarget : esSmall.target = ball := by
    change es.target ∩ ball = ball
    exact Set.inter_eq_right.mpr hball
  have hcenterBall : center ∈ ball := Metric.mem_ball_self hr
  have hcenterSmallTarget : center ∈ esSmall.target := by
    rw [hesSmallTarget]
    exact hcenterBall
  have huSmallSource : u ∈ esSmall.source := by
    have hmapped := esSmall.map_target hcenterSmallTarget
    have hinv : esSmall.symm center = u := by
      change (es.symm.restrOpen ball Metric.isOpen_ball) center = u
      change es.symm center = u
      have hcenterEq : es u = center := by
        change es u = coordinateTailHeight hAB u
        exact congrFun (simplexTailHeightChart_coe hAB u hd hbase) u
      rw [← hcenterEq]
      exact es.left_inv huSource
    rwa [hinv] at hmapped
  let chart : OpenPartialHomeomorph (EndpointArray d A B) (Fin d → ℝ) :=
    (endpointArrayHomeomorph hAB).transOpenPartialHomeomorph esSmall
  have hnodesSource : nodes ∈ chart.source := by
    change nodes ∈ (Homeomorph.transOpenPartialHomeomorph
      (endpointArrayHomeomorph hAB) esSmall).source
    rw [Homeomorph.transOpenPartialHomeomorph_source]
    change u ∈ esSmall.source
    exact huSmallSource
  have hchartEq :
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) = chart := by
    funext x
    change tailGapHeight x = esSmall ((endpointArrayHomeomorph hAB) x)
    change tailGapHeight x = es ((endpointArrayHomeomorph hAB) x)
    rw [simplexTailHeightChart_coe]
    change tailGapHeight x = tailGapHeight
      (endpointArrayOfInterior hAB ((endpointArrayHomeomorph hAB) x))
    congr 1
    exact (endpointArrayHomeomorph hAB).symm_apply_apply x |>.symm
  have hchartTarget : chart.target = ball := by
    change (Homeomorph.transOpenPartialHomeomorph
      (endpointArrayHomeomorph hAB) esSmall).target = ball
    rw [Homeomorph.transOpenPartialHomeomorph_target, hesSmallTarget]
  have hconvex : Convex ℝ chart.target := by
    rw [hchartTarget]
    exact convex_ball center r
  refine ⟨{
    chart := chart
    mem_source := hnodesSource
    chart_eq := hchartEq
    convex_target := hconvex
    height_zero_strictAnti := ?_ }⟩
  intro y z hy hz hyz hyzNe
  have hyBall : y ∈ ball := by rwa [← hchartTarget]
  have hzBall : z ∈ ball := by rwa [← hchartTarget]
  have hstrict := coordinateHeightZero_strictAntiOn_convexTarget
    hAB u hd hsignsAll hbase (convex_ball center r) hball
      hyBall hzBall hyz hyzNe
  change (chart.symm z).height 0 < (chart.symm y).height 0
  change (endpointArrayOfInterior hAB (esSmall.symm z)).height 0 <
    (endpointArrayOfInterior hAB (esSmall.symm y)).height 0
  change coordinateGapHeight hAB (esSmall.symm z) 0 <
    coordinateGapHeight hAB (esSmall.symm y) 0
  change coordinateGapHeight hAB (es.symm z) 0 <
    coordinateGapHeight hAB (es.symm y) 0
  exact hstrict
theorem tailHeightLocalOrientationStatement_of_coherentSigns
    (d : ℕ) (A B : ℝ)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes) :
    TailHeightLocalOrientationStatement d A B := by
  refine ⟨continuous_endpointArray_height (0 : Fin (d + 1)), ?_⟩
  intro hd nodes
  exact nonempty_orientedTailHeightChart_of_coherentSigns hd hsignsAll nodes
end
end Randy1153.DeBoorPinkus
namespace Randy1153.DeBoorPinkus
noncomputable section
theorem tailHeightLocalOrientationStatement (d : ℕ) (A B : ℝ) :
    TailHeightLocalOrientationStatement d A B :=
  tailHeightLocalOrientationStatement_of_coherentSigns d A B
    coherentHeightMaximalMinorSigns_unconditional
theorem gapHeightPathRayOrientationStatement (d : ℕ) (A B : ℝ) :
    GapHeightPathRayOrientationStatement d A B :=
  gapHeightPathRayOrientation_of_homeomorphism_of_localOrientation
    (gapDifference_homeomorphismStatement d A B)
    (tailHeightLocalOrientationStatement d A B)
theorem comparisonPackage (d : ℕ) (A B : ℝ) :
    ComparisonPackage d A B :=
  comparisonPackage_of_homeomorphism_of_pathRayOrientation
    (gapDifference_homeomorphismStatement d A B)
    (gapHeightPathRayOrientationStatement d A B)
theorem existsUniqueEquioscillatingStatement (d : ℕ) (A B : ℝ) :
    ExistsUniqueEquioscillatingStatement d A B :=
  (comparisonPackage d A B).exists_unique_equioscillating
end
end Randy1153.DeBoorPinkus
namespace OMA.H1Bridge
open Finset
noncomputable section
def mkArr {d : ℕ} (y : Fin (d + 2) → ℝ) (hy : StrictMono y)
    (hI : ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1)
    (h0 : y (Randy1153.DeBoorPinkus.endpointLeftIndex d) = -1)
    (hl : y (Randy1153.DeBoorPinkus.endpointRightIndex d) = 1) :
    Randy1153.DeBoorPinkus.EndpointArray d (-1) 1 where
  point := y
  injective := hy.injective
  mem_Icc := hI
  strictMono := hy
  left_endpoint := h0
  right_endpoint := hl
lemma randyL_eq {n : ℕ} (nodes : Randy1153.NodeFamily n) (t : ℝ) :
    Randy1153.lebesgueFunction nodes t = Erdos1129.lebesgueFunction nodes.point t := by
  rw [Erdos1129.lebesgueFunction_eq]
  rfl
lemma height_eq {d : ℕ} (Y : Randy1153.DeBoorPinkus.EndpointArray d (-1) 1)
    (g : Fin (d + 1)) :
    Y.height g = sSup (Erdos1129.lebesgueFunction Y.point ''
      Set.Icc (Y.point ⟨g.val, by omega⟩) (Y.point ⟨g.val + 1, by omega⟩)) := by
  have e : Randy1153.lebesgueFunction Y.toNodeFamily =
      Erdos1129.lebesgueFunction Y.point := funext fun t => randyL_eq _ t
  unfold Randy1153.DeBoorPinkus.EndpointArray.height Randy1153.gapHeight Randy1153.lebesgueOn
  rw [e]
  rfl
lemma exists_height_le_opt {d : ℕ} (Y opt : Randy1153.DeBoorPinkus.EndpointArray d (-1) 1)
    (hopt : Randy1153.DeBoorPinkus.Equioscillates opt) :
    ∃ g, Y.height g ≤ opt.height 0 := by
  by_contra h
  simp only [not_exists, not_le] at h
  have heq : opt = Y :=
    (Randy1153.DeBoorPinkus.comparisonPackage d (-1) 1).gapHeight_le_rigidity opt Y
      (fun i => (hopt i 0).le.trans (h i).le)
  have := h 0
  rw [heq] at this
  exact lt_irrefl _ this
end
end OMA.H1Bridge
namespace OMA.Can
open Finset Erdos1129
noncomputable section
lemma two_le_of_canonical {n : ℕ} {x : Fin n → ℝ} (hx : IsCanonical x) : 2 ≤ n := by
  obtain ⟨⟨hmono, -⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hx
  by_contra h
  have : i = j := by apply Fin.ext; omega
  rw [this, hj] at hi; norm_num at hi
lemma canon_endpoints {d : ℕ} {x : Fin (d + 2) → ℝ} (hx : IsCanonical x) :
    x (Randy1153.DeBoorPinkus.endpointLeftIndex d) = -1 ∧
      x (Randy1153.DeBoorPinkus.endpointRightIndex d) = 1 := by
  obtain ⟨⟨hymono, hyI⟩, ⟨k0, hk0⟩, ⟨k1, hk1⟩⟩ := hx
  have hiL : ∀ k : Fin (d + 2), Randy1153.DeBoorPinkus.endpointLeftIndex d ≤ k :=
    fun k => Fin.le_def.mpr (by simp)
  have hiR : ∀ k : Fin (d + 2), k ≤ Randy1153.DeBoorPinkus.endpointRightIndex d :=
    fun k => Fin.le_def.mpr (by simp only [Randy1153.DeBoorPinkus.endpointRightIndex_val]; omega)
  exact ⟨le_antisymm (hk0 ▸ hymono.monotone (hiL k0)) (hyI _).1,
    le_antisymm (hyI _).2 (hk1 ▸ hymono.monotone (hiR k1))⟩
def arr {d : ℕ} (x : Fin (d + 2) → ℝ) (hx : IsCanonical x) :
    Randy1153.DeBoorPinkus.EndpointArray d (-1) 1 :=
  OMA.H1Bridge.mkArr x hx.1.1 hx.1.2 (canon_endpoints hx).1 (canon_endpoints hx).2
lemma canon_of_arr {d : ℕ} (A : Randy1153.DeBoorPinkus.EndpointArray d (-1) 1) :
    IsCanonical A.point :=
  ⟨⟨A.strictMono, A.mem_Icc⟩, ⟨_, A.left_endpoint⟩, ⟨_, A.right_endpoint⟩⟩
lemma arr_point {d : ℕ} (A : Randy1153.DeBoorPinkus.EndpointArray d (-1) 1) :
    arr A.point (canon_of_arr A) = A := by
  rcases A with ⟨⟨⟨p, hi, hm⟩, hs⟩, hl, hr⟩
  rfl
lemma gapMax_eq {d : ℕ} (x : Fin (d + 2) → ℝ) (hx : IsCanonical x) (g : Fin (d + 1)) :
    gapMax x (g.val + 1) = (arr x hx).height g := by
  rw [OMA.H1Bridge.height_eq]
  unfold gapMax extendedNodes
  rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]
  rfl
lemma equiosc_iff {d : ℕ} (x : Fin (d + 2) → ℝ) (hx : IsCanonical x) :
    Equioscillates x ↔ Randy1153.DeBoorPinkus.Equioscillates (arr x hx) := by
  constructor
  · intro h i j
    rw [← gapMax_eq, ← gapMax_eq]
    exact h _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro h i hi j hj
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have e1 := gapMax_eq x hx ⟨i - 1, by omega⟩
    have e2 := gapMax_eq x hx ⟨j - 1, by omega⟩
    simp only [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega] at e1 e2
    rw [e1, e2]
    exact h _ _
lemma minInterior_eq {d : ℕ} (x : Fin (d + 2) → ℝ) (hx : IsCanonical x) :
    Erdos1130.minInteriorGapMax x = ⨅ g : Fin (d + 1), (arr x hx).height g := by
  unfold Erdos1130.minInteriorGapMax
  congr 1
  funext g
  exact gapMax_eq x hx g
theorem canonical_1130 (n : ℕ) :
    {x : Fin n → ℝ | IsCanonical x ∧
      ∀ y : Fin n → ℝ, IsCanonical y → Erdos1130.minInteriorGapMax y ≤ Erdos1130.minInteriorGapMax x} =
        {x | IsCanonical x ∧ Equioscillates x} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, hmax⟩
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by have := two_le_of_canonical hc; omega⟩
    refine ⟨hc, (equiosc_iff x hc).mpr ?_⟩
    have hAB : Randy1153.DeBoorPinkus.AdmissibleInterval (-1 : ℝ) 1 := ⟨le_rfl, by norm_num, le_rfl⟩
    obtain ⟨opt, hopt, -⟩ := Randy1153.DeBoorPinkus.existsUniqueEquioscillatingStatement d (-1) 1 hAB
    have h1 := hmax opt.point (canon_of_arr opt)
    rw [minInterior_eq _ (canon_of_arr opt), minInterior_eq x hc, arr_point] at h1
    have h2 : opt.height 0 ≤ ⨅ g : Fin (d + 1), opt.height g :=
      le_ciInf (fun g => (hopt 0 g).le)
    have hle : ∀ g, opt.height g ≤ (arr x hc).height g := by
      intro g
      rw [hopt g 0]
      exact (h2.trans h1).trans (ciInf_le (Set.finite_range _).bddBelow g)
    have heq := (Randy1153.DeBoorPinkus.comparisonPackage d (-1) 1).gapHeight_le_rigidity _ _ hle
    rw [← heq]
    exact hopt
  · rintro ⟨hc, he⟩
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 2 := ⟨n - 2, by have := two_le_of_canonical hc; omega⟩
    have hA := (equiosc_iff x hc).mp he
    refine ⟨hc, fun y hy => ?_⟩
    rw [minInterior_eq x hc, minInterior_eq y hy]
    obtain ⟨g, hg⟩ := OMA.H1Bridge.exists_height_le_opt (arr y hy) (arr x hc) hA
    refine (ciInf_le (Set.finite_range _).bddBelow g).trans (hg.trans ?_)
    exact le_ciInf (fun g' => (hA 0 g').le)
end
end OMA.Can

namespace OMA.ExteriorHeights

open Finset Erdos1129
noncomputable section

lemma bdd_L {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) :
    BddAbove (Erdos1129.lebesgueFunction x '' Set.Icc a b) := by
  refine (isCompact_Icc.image ?_).bddAbove
  unfold Erdos1129.lebesgueFunction
  exact continuous_finsetSum _ fun k _ => (Polynomial.continuous _).abs
lemma L_aff {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) (ha : a ≠ 0) (t : ℝ) :
    Erdos1129.lebesgueFunction (fun i => a * x i + b) (a * t + b) =
      Erdos1129.lebesgueFunction x t := by
  rw [Erdos1129.lebesgueFunction_eq, Erdos1129.lebesgueFunction_eq]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [show a * t + b - (a * x i + b) = a * (t - x i) by ring,
    show a * x k + b - (a * x i + b) = a * (x k - x i) by ring, mul_div_mul_left _ _ ha]

lemma exists_canonical {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    ∃ α β : ℝ, 0 < α ∧ IsCanonical (fun i => α * x i + β) := by
  obtain ⟨hxmono, hxI⟩ := hx
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨n - 1, by omega⟩
  have hi0 : ∀ k : Fin n, i0 ≤ k := fun k => Fin.le_def.mpr (Nat.zero_le _)
  have hi1 : ∀ k : Fin n, k ≤ i1 := fun k => Fin.le_def.mpr (by simp only [i1]; omega)
  set a := x i0
  set b := x i1
  have hab : a < b := hxmono (Fin.lt_def.mpr (by simp only [i0, i1]; omega))
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨2 / (b - a), -(a + b) / (b - a), by positivity, ?_⟩
  have heq : ∀ i, 2 / (b - a) * x i + -(a + b) / (b - a) = (2 * x i - (a + b)) / (b - a) := by
    intro i; field_simp; ring
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨i0, ?_⟩, ⟨i1, ?_⟩⟩
  · simp only [heq]
    apply div_lt_div_of_pos_right _ hba
    linarith [hxmono hij]
  · have h1 : a ≤ x i := hxmono.monotone (hi0 i)
    have h2 : x i ≤ b := hxmono.monotone (hi1 i)
    simp only [heq]
    rw [Set.mem_Icc, le_div_iff₀ hba, div_le_iff₀ hba]
    constructor <;> linarith
  · simp only [heq]; rw [div_eq_iff hba.ne']; ring
  · simp only [heq]; rw [div_eq_iff hba.ne']; ring
lemma gapMax_affine {n : ℕ} (x : Fin n → ℝ) {α : ℝ} (hα : 0 < α) (β : ℝ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j + 1 ≤ n) :
    gapMax (fun i => α * x i + β) j = gapMax x j := by
  unfold gapMax extendedNodes
  rw [dif_pos ⟨hj1, by omega⟩, dif_pos ⟨by omega, hjn⟩, dif_pos ⟨hj1, by omega⟩,
    dif_pos ⟨by omega, hjn⟩]
  congr 1
  rw [← Set.image_affine_Icc' hα, Set.image_image]
  congr 1
  funext t
  exact L_aff x α β hα.ne' t

end
end OMA.ExteriorHeights

/-- The interior gap heights agree, and neither exterior height falls below them.
For zero or one node every admissible array is a maximizer. -/
noncomputable def OMA.answer (n : ℕ) : Set (Fin n → ℝ) :=
  {x | Erdos1129.IsNodeSet x ∧ (n ≤ 1 ∨ (Erdos1129.Equioscillates x ∧
    Erdos1129.gapMax x 1 ≤ Erdos1129.gapMax x 0 ∧ Erdos1129.gapMax x 1 ≤ Erdos1129.gapMax x n))}

namespace OMA.ExteriorHeights

open Finset Set Erdos1129 Polynomial

private lemma total_le_gap {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) :
    Erdos1130.upsilon x ≤ gapMax x j :=
  ciInf_le (Set.finite_range _).bddBelow (⟨j, by omega⟩ : Fin (n+1))

private lemma inner_le_gap {n j : ℕ} (x : Fin n → ℝ) (hj : 1 ≤ j) (hj' : j < n) :
    Erdos1130.minInteriorGapMax x ≤ gapMax x j := by
  have h : Erdos1130.minInteriorGapMax x ≤ gapMax x ((j-1)+1) :=
    ciInf_le (Set.finite_range _).bddBelow (⟨j-1, by omega⟩ : Fin (n-1))
  rwa [Nat.sub_add_cancel hj] at h

private lemma total_le_inner {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    Erdos1130.upsilon x ≤ Erdos1130.minInteriorGapMax x := by
  let : Nonempty (Fin (n-1)) := ⟨⟨0, by omega⟩⟩
  exact le_ciInf fun i : Fin (n-1) => total_le_gap x (i.val+1) (by omega)

private lemma lower_total {n : ℕ} (x : Fin n → ℝ) {m : ℝ}
    (hi : m ≤ Erdos1130.minInteriorGapMax x) (hl : m ≤ gapMax x 0)
    (hr : m ≤ gapMax x n) : m ≤ Erdos1130.upsilon x := by
  apply le_ciInf
  intro i
  by_cases h0 : i.val = 0
  · simpa only [h0] using hl
  by_cases hn : i.val = n
  · simpa only [hn] using hr
  exact hi.trans (inner_le_gap x (by omega) (by omega))

private lemma inner_affine {n : ℕ} (x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Erdos1130.minInteriorGapMax (fun i => a*x i+b) = Erdos1130.minInteriorGapMax x := by
  apply congrArg (fun f : Fin (n-1) → ℝ => ⨅ i, f i)
  funext i
  exact gapMax_affine x ha b (by omega) (by omega)

private lemma equi_affine {n : ℕ} (x : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Equioscillates (fun i => a*x i+b) ↔ Equioscillates x := by
  have eq (j : ℕ) (hj : j ∈ Finset.Icc 1 (n-1)) :
      gapMax (fun i => a*x i+b) j = gapMax x j := by
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hj
    exact gapMax_affine x ha b lo (by omega)
  constructor
  · intro h i hi j hj
    rw [←eq i hi, ←eq j hj]
    exact h i hi j hj
  · intro h i hi j hj
    rw [eq i hi,eq j hj]
    exact h i hi j hj

private lemma inner_common {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (h : Equioscillates x) :
    Erdos1130.minInteriorGapMax x = gapMax x 1 := by
  let : Nonempty (Fin (n-1)) := ⟨⟨0, by omega⟩⟩
  refine le_antisymm (inner_le_gap x (by omega) (by omega)) (le_ciInf fun i : Fin (n-1) => ?_)
  exact (h 1 (Finset.mem_Icc.mpr ⟨by omega,by omega⟩) (i.val+1)
    (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).le

private lemma linear_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) (t : ℝ) :
    |t| ≤ lebesgueFunction x t := by
  classical
  have degree : (X : ℝ[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simp only [degree_X, Finset.card_univ, Fintype.card_fin, Nat.cast_withBot]
    exact WithBot.coe_lt_coe.mpr (show (1 : ℕ) < n by omega)
  have linear : (X : ℝ[X]) = Lagrange.interpolate Finset.univ x x :=
    Lagrange.eq_interpolate_of_eval_eq _ hx.1.injective.injOn degree (fun _ _ => eval_X)
  have idn : t = ∑ k, x k * (Lagrange.basis Finset.univ x k).eval t := by
    simpa only [eval_X,Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C]
      using congrArg (fun p : ℝ[X] => p.eval t) linear
  calc
    |t| = |∑ k, x k * (Lagrange.basis Finset.univ x k).eval t| := congrArg abs idn
    _ ≤ ∑ k, |x k * (Lagrange.basis Finset.univ x k).eval t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ lebesgueFunction x t := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr (hx.2 k))

private lemma extended_mem {n : ℕ} {x : Fin n → ℝ} (hx : IsNodeSet x) (j : ℕ) :
    extendedNodes x j ∈ Set.Icc (-1:ℝ) 1 := by
  unfold extendedNodes
  split_ifs
  · exact hx.2 _
  · constructor <;> norm_num
  · constructor <;> norm_num

private lemma at_gap {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (t : ℝ)
    (h : t ∈ Set.Icc (extendedNodes x j) (extendedNodes x (j+1))) :
    lebesgueFunction x t ≤ gapMax x j :=
  le_csSup (bdd_L x _ _) ⟨t,h,rfl⟩

private lemma realize_inner {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    ∃ z : Fin n → ℝ, IsNodeSet z ∧ Erdos1130.upsilon z = Erdos1130.minInteriorGapMax x := by
  let m := Erdos1130.minInteriorGapMax x
  let T := max 1 m
  let a := 1/T
  let z (i : Fin n) := a*x i+0
  have hT : 1 ≤ T := le_max_left _ _
  have hm : m ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  have ha : 0 < a := one_div_pos.mpr hT0
  have hal : a ≤ 1 := (div_le_one hT0).mpr hT
  have hz : IsNodeSet z := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simpa [z] using mul_lt_mul_of_pos_left (hx.1 hij) ha
    · obtain ⟨lo,hi⟩ := hx.2 i
      change -1 ≤ a*x i+0 ∧ a*x i+0 ≤ 1
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left lo ha.le,
        mul_le_mul_of_nonneg_left hi ha.le]
  have inv : a*T = 1 := by dsimp [a]; field_simp
  have l := L_aff x a 0 ha.ne' (-T)
  have r := L_aff x a 0 ha.ne' T
  have hleft : m ≤ lebesgueFunction z (-1) := by
    change m ≤ lebesgueFunction (fun i => a*x i+0) (-1)
    rw [show (-1:ℝ) = a*(-T)+0 by linarith [mul_neg a T],l]
    simpa only [abs_neg,abs_of_pos hT0] using
      (show m ≤ |-(T:ℝ)| by simpa [abs_of_pos hT0] using hm).trans (linear_bound hn x hx (-T))
  have hright : m ≤ lebesgueFunction z 1 := by
    change m ≤ lebesgueFunction (fun i => a*x i+0) 1
    rw [show (1:ℝ) = a*T+0 by linarith,r]
    exact hm.trans (by simpa only [abs_of_pos hT0] using linear_bound hn x hx T)
  have hle : m ≤ gapMax z 0 := hleft.trans (at_gap z 0 (-1)
    ⟨by simp [extendedNodes], (extended_mem hz 1).1⟩)
  have hre : m ≤ gapMax z n := hright.trans (at_gap z n 1
    ⟨(extended_mem hz n).2, by simp [extendedNodes]⟩)
  have eqn : Erdos1130.minInteriorGapMax z = m := inner_affine x ha 0
  exact ⟨z,hz,le_antisymm ((total_le_inner hn z).trans eqn.le) (lower_total z eqn.ge hle hre)⟩

private lemma all_inner_iff
    (canonical : type_of% @Erdos1130.erdos_1130.variants.canonical)
    {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : IsNodeSet x) :
    (∀ y : Fin n → ℝ, IsNodeSet y → Erdos1130.minInteriorGapMax y ≤ Erdos1130.minInteriorGapMax x)
      ↔ Equioscillates x := by
  obtain ⟨a,b,ha,hc⟩ := exists_canonical hn x hx
  let u (i : Fin n) := a*x i+b
  have e : Erdos1130.minInteriorGapMax u = Erdos1130.minInteriorGapMax x := inner_affine x ha b
  have h := Set.ext_iff.mp (canonical n) u
  change (IsCanonical u ∧ ∀ y, IsCanonical y → Erdos1130.minInteriorGapMax y ≤
      Erdos1130.minInteriorGapMax u) ↔ IsCanonical u ∧ Equioscillates u at h
  constructor
  · intro hi
    exact (equi_affine x ha b).mp (h.mp ⟨hc,fun y hy => (hi y hy.1).trans e.ge⟩).2
  · intro he y hy
    obtain ⟨c,d,hd,hv⟩ := exists_canonical hn y hy
    have bound := (h.mpr ⟨hc,(equi_affine x ha b).mpr he⟩).2 _ hv
    rw [inner_affine y hd d,e] at bound
    exact bound

private lemma one_value (x : Fin 1 → ℝ) (hx : IsNodeSet x) : Erdos1130.upsilon x = 1 := by
  classical
  have constant : lebesgueFunction x = fun _ => 1 := by
    funext t
    simp [lebesgueFunction_eq, Finset.univ_unique]
  have all (i : Fin 2) : gapMax x i.val = 1 := by
    have h0 := hx.2 0
    have h : (Set.Icc (extendedNodes x i.val) (extendedNodes x (i.val+1))).Nonempty := by
      apply Set.nonempty_Icc.mpr
      fin_cases i <;> simp [extendedNodes] <;> first | exact h0.1 | exact h0.2
    rw [gapMax,constant,h.image_const,csSup_singleton]
  unfold Erdos1130.upsilon
  simp_rw [all]
  simp

theorem characterize (canonical : type_of% @Erdos1130.erdos_1130.variants.canonical) (n : ℕ) :
    {x : Fin n → ℝ | IsNodeSet x ∧ ∀ y : Fin n → ℝ, IsNodeSet y →
      Erdos1130.upsilon y ≤ Erdos1130.upsilon x} = OMA.answer n := by
  ext x
  change (IsNodeSet x ∧ _) ↔ (IsNodeSet x ∧ _)
  by_cases hn : 2 ≤ n
  · constructor
    · rintro ⟨hx,high⟩
      have all (y : Fin n → ℝ) (hy : IsNodeSet y) :
          Erdos1130.minInteriorGapMax y ≤ Erdos1130.upsilon x := by
        obtain ⟨z,hz,eqn⟩ := realize_inner hn y hy
        rw [←eqn]
        exact high z hz
      have he := (all_inner_iff canonical hn x hx).mp
        (fun y hy => (all y hy).trans (total_le_inner hn x))
      have low := (inner_common hn x he).ge.trans (all x hx)
      exact ⟨hx,Or.inr ⟨he,low.trans (total_le_gap x 0 (by omega)),
        low.trans (total_le_gap x n le_rfl)⟩⟩
    · rintro ⟨hx,small | ⟨he,hl,hr⟩⟩
      · omega
      · have eqn := inner_common hn x he
        have low := lower_total x le_rfl (eqn.le.trans hl) (eqn.le.trans hr)
        exact ⟨hx,fun y hy => (total_le_inner hn y).trans
          (((all_inner_iff canonical hn x hx).mpr he y hy).trans low)⟩
  · constructor
    · exact fun h => ⟨h.1,Or.inl (by omega)⟩
    · rintro ⟨hx,_⟩
      refine ⟨hx, fun y hy => ?_⟩
      rcases (show n=0 ∨ n=1 by omega) with rfl | rfl
      · rw [Subsingleton.elim y x]
      · rw [one_value x hx,one_value y hy]

end OMA.ExteriorHeights


theorem OMA.ExteriorHeights.all_optimizers (n : ℕ) :
    {x : Fin n → ℝ | Erdos1129.IsNodeSet x ∧ ∀ y : Fin n → ℝ, Erdos1129.IsNodeSet y →
      Erdos1130.upsilon y ≤ Erdos1130.upsilon x} = OMA.answer n :=
  OMA.ExteriorHeights.characterize OMA.Can.canonical_1130 n

theorem OMA.solution : Erdos1130.erdos_1130.parts.ii.answer = OMA.answer →
    type_of% @Erdos1130.erdos_1130.parts.ii := by
  intro replacement n
  rw [replacement]
  exact OMA.ExteriorHeights.all_optimizers n
