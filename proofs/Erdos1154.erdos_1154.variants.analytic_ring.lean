import FormalConjectures.ErdosProblems.«1154»
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.MetricSpace.PiNat

/-!
Edgar and Miller, "Borel subrings of the reals", Lemmas 1.2–1.4 and the
analytic extension. https://people.math.osu.edu/edgar.2/preprints/subring/subringpre.pdf
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology Pointwise

namespace EdgarMiller

def coeffSum (R : Subring ℝ) {n : ℕ} (c : Fin n → ℝ) : (Fin n → R) →+ ℝ where
  toFun x := ∑ i, c i * (x i : ℝ)
  map_zero' := by simp
  map_add' x y := by
    simp [mul_add, Finset.sum_add_distrib]

@[simp] theorem coeffSum_apply (R : Subring ℝ) {n : ℕ} (c : Fin n → ℝ) (x : Fin n → R) :
    coeffSum R c x = ∑ i, c i * (x i : ℝ) := rfl

def realSum {n : ℕ} (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, c i * x i

theorem continuous_realSum {n : ℕ} (c : Fin n → ℝ) : Continuous (realSum c) := by
  unfold realSum
  fun_prop

/-- A shortest surjective coefficient sum over a subring has zero kernel. -/
theorem exists_bijective_coeffSum (R : Subring ℝ)
    (h : ∃ n : ℕ, ∃ c : Fin n → ℝ, Function.Surjective (coeffSum R c)) :
    ∃ n : ℕ, ∃ c : Fin n → ℝ, Function.Bijective (coeffSum R c) := by
  classical
  let has (n : ℕ) := ∃ c : Fin n → ℝ, Function.Surjective (coeffSum R c)
  let n := Nat.find h
  obtain ⟨c,hc⟩ : has n := Nat.find_spec h
  refine ⟨n,c,?_ ,hc⟩
  intro x y hxy
  by_contra hne
  let z : Fin n → R := x-y
  have hz : coeffSum R c z = 0 := by
    rw [show z=x-y by rfl, map_sub, hxy, sub_self]
  have hnez : ∃ i : Fin n, z i ≠ 0 := by
    by_contra! hzero
    exact hne (sub_eq_zero.mp (funext hzero))
  obtain ⟨i,hi⟩ := hnez
  have hpos : 0 < n := i.isLt.trans_le' (Nat.zero_le _)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hmin : ¬ has m := Nat.find_min h (show m < n by omega)
  apply hmin
  change ∃ c : Fin m → ℝ, Function.Surjective (coeffSum R c)
  let e : Fin n ≃ Fin (m+1) := finCongr hm
  let c' : Fin (m+1) → ℝ := c ∘ e.symm
  let b : Fin (m+1) → R := z ∘ e.symm
  let p : Fin (m+1) := e i
  have hb : (b p : ℝ) ≠ 0 := by
    simpa [b,p,Subring.coe_eq_zero_iff] using hi
  have heval (a : Fin n → R) : coeffSum R c' (a ∘ e.symm) = coeffSum R c a := by
    simp only [coeffSum_apply,c',Function.comp_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hzero : coeffSum R c' b = 0 := (heval z).trans hz
  have hs : Function.Surjective (coeffSum R c') := fun r => by
    obtain ⟨v,hv⟩ := hc r
    exact ⟨v ∘ e.symm, (heval v).trans hv⟩
  refine ⟨c' ∘ p.succAbove, fun r => ?_⟩
  obtain ⟨a, ha⟩ := hs (r / (b p : ℝ))
  let a' (j : Fin m) : R := b p * a (p.succAbove j) - a p * b (p.succAbove j)
  refine ⟨a',?_⟩
  simp only [coeffSum_apply] at hzero ha
  rw [Fin.sum_univ_succAbove _ p] at hzero ha
  have hr : r = (c' p * (a p : ℝ) + ∑ j : Fin m, c' (p.succAbove j) * (a (p.succAbove j) : ℝ)) * (b p : ℝ) :=
    (div_eq_iff hb).mp ha.symm
  change (∑ j : Fin m, c' (p.succAbove j) *
    ((b p : ℝ) * (a (p.succAbove j) : ℝ) - (a p : ℝ) * (b (p.succAbove j) : ℝ))) = r
  rw [← add_zero r, hr]
  have heq : (∑ j : Fin m, c' (p.succAbove j) *
    ((b p : ℝ) * (a (p.succAbove j) : ℝ) - (a p : ℝ) * (b (p.succAbove j) : ℝ))) =
    (b p : ℝ) * (∑ j : Fin m, c' (p.succAbove j) * (a (p.succAbove j) : ℝ)) -
    (a p : ℝ) * (∑ j : Fin m, c' (p.succAbove j) * (b (p.succAbove j) : ℝ)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  linear_combination - (a p : ℝ) * hzero

private theorem analytic_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : AnalyticSet s) (ht : AnalyticSet t) : AnalyticSet (s∩t) := by
  let A : Bool → Set X := fun b => if b then s else t
  have hA : ∀ b, AnalyticSet (A b) := fun b => by cases b <;> simp [A, hs, ht]
  convert AnalyticSet.iInter hA using 1
  ext x
  simp [A, Bool.forall_bool, and_comm]

def tuples (R : Subring ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ R}

private theorem analytic_tuples {R : Subring ℝ} (hR : AnalyticSet (R : Set ℝ))
    {n : ℕ} (hn : 0 < n) : AnalyticSet (tuples R n) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have he : tuples R n = ⋂ i : Fin n, (fun x : Fin n → ℝ => x i) ⁻¹' (R : Set ℝ) := by
    ext x
    simp [tuples]
  rw [he]
  exact AnalyticSet.iInter (fun i => hR.preimage (continuous_apply i))

/-- Analyticity makes every inverse coordinate of a bijective coefficient sum Borel. -/
theorem eq_top_of_bijective_coeffSum {R : Subring ℝ} (hR : AnalyticSet (R : Set ℝ))
    {n : ℕ} (c : Fin n → ℝ) (hc : Function.Bijective (coeffSum R c)) : R = ⊤ := by
  have hn : 0 < n := by
    by_contra! h
    have hz : n = 0 := Nat.eq_zero_of_le_zero h
    subst n
    obtain ⟨a,ha⟩ := hc.2 1
    simp at ha
  let i : Fin n := ⟨0,hn⟩
  let e : (Fin n → R) ≃+ ℝ := AddEquiv.ofBijective (coeffSum R c) hc
  let τ : ℝ →+ ℝ :=
    { toFun := fun x => ((e.symm x) i : ℝ)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have preimg_image (U : Set ℝ) :
      τ ⁻¹' U = realSum c '' (tuples R n ∩ (fun x : Fin n → ℝ => x i) ⁻¹' U) := by
    ext x
    constructor
    · intro hx
      refine ⟨fun j => ((e.symm x) j : ℝ), ⟨fun j => ((e.symm x) j).2,hx⟩,?_⟩
      exact e.apply_symm_apply x
    · rintro ⟨a,⟨ha,haU⟩,rfl⟩
      let b : Fin n → R := fun j => ⟨a j, ha j⟩
      have hb : e b = realSum c a := rfl
      change ((e.symm (realSum c a)) i : ℝ) ∈ U
      rw [← hb, e.symm_apply_apply]
      exact haU
  have analyt (U : Set ℝ) (hU : MeasurableSet U) : AnalyticSet (τ ⁻¹' U) := by
    rw [preimg_image]
    exact (analytic_inter (analytic_tuples hR hn)
      (hU.analyticSet.preimage (continuous_apply i))).image_of_continuous (continuous_realSum c)
  have hτ : Measurable τ := by
    intro U hU
    apply (analyt U hU).measurableSet_of_compl
    rw [← preimage_compl]
    exact analyt Uᶜ hU.compl
  have hcont : Continuous τ := Measure.AddMonoidHom.continuous_of_measurable τ hτ
  have hl (x : ℝ) : τ x = x * τ 1 := by
    simpa [smul_eq_mul] using map_real_smul τ hcont x (1:ℝ)
  have hne : τ 1 ≠ 0 := by
    intro hz
    let b : Fin n → R := fun _ => 1
    have hb : τ (e b) = 1 := by change ((e.symm (e b)) i : ℝ) = 1; simp [b]
    rw [hl,hz,mul_zero] at hb
    exact zero_ne_one hb
  apply top_unique
  intro x _
  have hx : τ (x/τ 1) = x := by rw [hl,div_mul_cancel₀ _ hne]
  rw [← hx]
  exact ((e.symm (x/τ 1)) i).2

/-- A positive-measure measurable subset of a coefficient-sum range gives surjectivity. -/
theorem surjective_of_positive_subset {R : Subring ℝ} {n : ℕ} {c : Fin n → ℝ}
    {S : Set ℝ} (hs : MeasurableSet S) (hpos : 0 < volume S)
    (hsub : S ⊆ range (coeffSum R c)) : Function.Surjective (coeffSum R c) := by
  let G : AddSubgroup ℝ := (coeffSum R c).range
  have hsubG : S ⊆ (G : Set ℝ) := hsub
  have h := Measure.sub_mem_nhds_zero_of_addHaar_pos (volume : Measure ℝ) S hs hpos
  have hG : (G : Set ℝ) ∈ 𝓝 0 := mem_of_superset h (by
    rintro _ ⟨x,hx,y,hy,rfl⟩
    exact G.sub_mem (hsubG hx) (hsubG hy))
  have hopen : IsOpen (G : Set ℝ) := G.isOpen_of_mem_nhds hG
  have he : (G : Set ℝ) = univ :=
    IsClopen.eq_univ ⟨G.isClosed_of_isOpen hopen,hopen⟩ ⟨0,G.zero_mem⟩
  exact range_eq_univ.mp he

/-- The algebraic and descriptive-set-theoretic part of Edgar–Miller's proof. -/
theorem eq_top_of_positive_projection {R : Subring ℝ} (hR : AnalyticSet (R : Set ℝ))
    (h : ∃ (n : ℕ) (c : Fin n → ℝ) (S : Set ℝ), MeasurableSet S ∧ 0 < volume S ∧
      S ⊆ range (coeffSum R c)) : R = ⊤ := by
  obtain ⟨n,c,S,hs,hpos,hsub⟩ := h
  obtain ⟨_,d,hd⟩ := exists_bijective_coeffSum R ⟨n,c,surjective_of_positive_subset hs hpos hsub⟩
  exact eq_top_of_bijective_coeffSum hR d hd

end EdgarMiller


open Set MeasureTheory Metric
open scoped ENNReal NNReal Topology BigOperators

namespace EdgarMillerProjection

def uniformInterval : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

instance : IsProbabilityMeasure uniformInterval where
  measure_univ := by simp [uniformInterval, Real.volume_Icc]

def directions (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => uniformInterval

instance (n : ℕ) : IsProbabilityMeasure (directions n) := by
  unfold directions
  infer_instance

def dot {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ i, a i * b i

theorem continuous_dot {n : ℕ} : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) => dot p.1 p.2) := by
  unfold dot
  fun_prop

private theorem measure_one_coordinate {v z t : ℝ} (hv : v ≠ 0) (_ht : 0 ≤ t) :
    uniformInterval {x : ℝ | |v*x+z| ≤ t} ≤ ENNReal.ofReal (2*t/|v|) := by
  let c := -z/v
  have he (x : ℝ) : v*x+z = v*(x-c) := by
    dsimp [c]
    field_simp
    ring
  have hp : 0 < |v| := abs_pos.mpr hv
  have hsub : {x : ℝ | |v*x+z| ≤ t} ⊆ closedBall c (t/|v|) := by
    intro x hx
    rw [mem_closedBall, Real.dist_eq]
    apply (le_div_iff₀ hp).mpr
    have hx' : |v*x+z| ≤ t := hx
    rw [he, abs_mul, mul_comm] at hx'
    exact hx'
  calc
    uniformInterval _ ≤ uniformInterval (closedBall c (t/|v|)) := measure_mono hsub
    _ ≤ volume (closedBall c (t/|v|)) := Measure.restrict_le_self _
    _ = ENNReal.ofReal (2*t/|v|) := by rw [Real.volume_closedBall, mul_div_assoc]

/-- With independent uniform coefficients on [0,1], a slab has mass at most
its one-coordinate width. -/
theorem slab_measure_le {n : ℕ} (v : Fin (n+1) → ℝ) (i : Fin (n+1))
    (hv : v i ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    directions (n+1) {a | |dot v a| ≤ t} ≤ ENNReal.ofReal (2*t/|v i|) := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  let A : Set (ℝ × (Fin n → ℝ)) := {p | |v i * p.1 + ∑ j : Fin n, v (i.succAbove j) * p.2 j| ≤ t}
  have hA : MeasurableSet A := by
    apply measurableSet_le
    · fun_prop
    · exact measurable_const
  have hE : MeasurePreserving E (directions (n+1)) (uniformInterval.prod (directions n)) :=
    measurePreserving_piFinSuccAbove (fun _ => uniformInterval) i
  have hpre : E ⁻¹' A = {a | |dot v a| ≤ t} := by
    ext a
    simp only [A, mem_preimage, mem_ofPred_eq, dot, Fin.sum_univ_succAbove _ i]
    rfl
  rw [← hpre, hE.measure_preimage hA.nullMeasurableSet, Measure.prod_apply_symm hA]
  calc
    _ ≤ ∫⁻ _ : Fin n → ℝ, ENNReal.ofReal (2*t/|v i|) ∂directions n := by
      refine lintegral_mono (fun a => ?_)
      change uniformInterval {x : ℝ | |v i*x + ∑ j : Fin n, v (i.succAbove j)*a j| ≤ t} ≤ _
      exact measure_one_coordinate hv ht
    _ = _ := by simp

end EdgarMillerProjection



open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace EdgarMillerEnergy

def near {X : Type*} [EDist X] (r : ℝ≥0∞) : Set (X × X) :=
  {p | edist p.1 p.2 ≤ r}

private theorem measurableSet_near {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (r : ℝ≥0∞) :
    MeasurableSet (near (X := X) r) := by
  unfold near
  exact measurableSet_le (by fun_prop) measurable_const

def dyadic (k : ℕ) : ℝ≥0∞ := (2:ℝ≥0∞)⁻¹ ^ k

private theorem dyadic_lt : (2:ℝ≥0∞)⁻¹ < 1 := by norm_num

private theorem bound_inverse (a : ℝ≥0∞) :
    a⁻¹ ≤ 1 + ∑' k : ℕ, if a ≤ dyadic k then (2:ℝ≥0∞)^(k+1) else 0 := by
  by_cases hb : 1 ≤ a
  · exact (ENNReal.inv_le_one.mpr hb).trans le_self_add
  by_cases ha : a = 0
  · subst a
    simp only [zero_le, if_true, ENNReal.inv_zero, top_le_iff]
    suffices htop : (∑' k : ℕ, (2:ℝ≥0∞)^(k+1)) = ⊤ by simp [htop]
    apply le_antisymm le_top
    calc
      ⊤ = ∑' _ : ℕ, (1:ℝ≥0∞) := by simp
      _ ≤ _ := ENNReal.tsum_le_tsum (fun k => one_le_pow₀ (by norm_num))
  have hex : ∃ k : ℕ, dyadic k < a := by
    have hlim : Tendsto dyadic atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one dyadic_lt
    exact (hlim.eventually (gt_mem_nhds (pos_iff_ne_zero.mpr ha))).exists
  let k := Nat.find hex
  have hk : dyadic k < a := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro he
    rw [he,dyadic,pow_zero] at hk
    exact hb hk.le
  let j := k-1
  have hj : j < k := by dsimp [j]; omega
  have hjk : j+1 = k := by dsimp [j]; omega
  have hja : a ≤ dyadic j := le_of_not_gt (Nat.find_min hex hj)
  calc
    a⁻¹ ≤ (dyadic k)⁻¹ := ENNReal.inv_le_inv.mpr hk.le
    _ = (2:ℝ≥0∞)^(j+1) := by rw [dyadic, ← ENNReal.inv_pow, inv_inv, hjk]
    _ ≤ ∑' l : ℕ, if a ≤ dyadic l then (2:ℝ≥0∞)^(l+1) else 0 := by
      have h := ENNReal.le_tsum (f := fun l : ℕ => if a ≤ dyadic l then (2:ℝ≥0∞)^(l+1) else 0) j
      rwa [if_pos hja] at h
    _ ≤ _ := le_add_self

/-- Integrate inverse distance using a geometric upper bound on dyadic small-ball probabilities. -/
theorem lintegral_inv_edist_lt_top {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (ν : Measure (X × X)) [IsProbabilityMeasure ν]
    {B q : ℝ≥0∞} (hB : B ≠ ⊤) (hq : 2*q < 1)
    (hnear : ∀ k : ℕ, ν (near (dyadic k)) ≤ B*q^k) :
    (∫⁻ p : X×X, (edist p.1 p.2)⁻¹ ∂ν) < ⊤ := by
  let v (k : ℕ) : X×X → ℝ≥0∞ := (near (dyadic k)).indicator (fun _ => (2:ℝ≥0∞)^(k+1))
  have hv (k : ℕ) : Measurable (v k) := measurable_const.indicator (measurableSet_near _)
  have hdom (p : X×X) : (edist p.1 p.2)⁻¹ ≤ 1 + ∑' k : ℕ, v k p :=
    (bound_inverse (edist p.1 p.2)).trans_eq (by
      congr 1
      apply tsum_congr
      intro k
      by_cases h : edist p.1 p.2 ≤ dyadic k <;> simp [v,near,h])
  refine (lintegral_mono hdom).trans_lt ?_
  rw [lintegral_add_left measurable_const, lintegral_tsum (fun k => (hv k).aemeasurable)]
  simp only [lintegral_const, measure_univ, mul_one]
  have hBd : (∑' k : ℕ, ∫⁻ p : X×X, v k p ∂ν) ≤ (2*B) * ∑' k : ℕ, (2*q)^k := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    change (∫⁻ p, (near (dyadic k)).indicator (fun _ => (2:ℝ≥0∞)^(k+1)) p ∂ν) ≤ _
    rw [lintegral_indicator_const (measurableSet_near _)]
    calc
      _ ≤ (2:ℝ≥0∞)^(k+1) * (B*q^k) := mul_le_mul_right (hnear k) _
      _ = _ := by rw [pow_succ,mul_pow]; ac_rfl
  have hfin : (2*B) * (∑' k : ℕ, (2*q)^k) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hB.lt_top)
      (tsum_geometric_lt_top.mpr hq)
  exact ENNReal.add_lt_top.mpr ⟨by norm_num, hBd.trans_lt hfin⟩

/-- Independent coordinates improve the small-ball exponent by a factor equal to their count. -/
theorem near_product_measure_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {n : ℕ}
    {r B : ℝ≥0∞} (hball : ∀ x : ℝ, μ (closedEBall x r) ≤ B) :
    ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) (near r) ≤ B^n := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  change (ν.prod ν) (near r) ≤ B^n
  rw [Measure.prod_apply (measurableSet_near r)]
  have hs (x : Fin n → ℝ) : (Prod.mk x ⁻¹' near r) = Set.pi univ (fun i => closedEBall (x i) r) := by
    ext y
    simp only [Set.mem_preimage, near, Set.mem_ofPred_eq, Set.mem_univ_pi, mem_closedEBall,
      edist_pi_le_iff]
    exact forall_congr' (fun i => by rw [edist_comm])
  calc
    _ ≤ ∫⁻ _ : Fin n → ℝ, B^n ∂ν := by
      refine lintegral_mono (fun x => ?_)
      rw [hs]
      change (Measure.pi (fun _ : Fin n => μ)) (Set.pi univ (fun i => closedEBall (x i) r)) ≤ B^n
      rw [Measure.pi_pi]
      exact (Finset.prod_le_prod' (fun i _ => hball (x i))).trans_eq (by simp)
    _ = _ := by simp [ν]

end EdgarMillerEnergy



open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace EdgarMillerSmoothing

def kernel (r : ℝ) (z y : ℝ) : ℝ≥0∞ := if dist y z ≤ r then 1 else 0

private theorem measurable_kernel (r : ℝ) :
    Measurable (fun p : ℝ × ℝ => kernel r p.1 p.2) := by
  unfold kernel
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurable_const
  · exact measurable_const

private theorem kernel_lintegral (r : ℝ) (z : ℝ) (ν : Measure ℝ) :
    (∫⁻ y, kernel r z y ∂ν) = ν (closedBall z r) := by
  change (∫⁻ y, (closedBall z r).indicator (fun _ => (1:ℝ≥0∞)) y ∂ν) = _
  rw [lintegral_indicator_const isClosed_closedBall.measurableSet, one_mul]

def smooth (ν : Measure ℝ) (r : ℝ) (z : ℝ) : ℝ≥0∞ := ∫⁻ y, kernel r z y ∂ν

theorem measurable_smooth (ν : Measure ℝ) [SFinite ν] (r : ℝ) : Measurable (smooth ν r) :=
  (measurable_kernel r).lintegral_prod_right'

def collision (ν : Measure ℝ) (r : ℝ) : ℝ≥0∞ := (ν.prod ν) {p | dist p.1 p.2 ≤ r}

private theorem measurableSet_collision (r : ℝ) : MeasurableSet {p : ℝ×ℝ | dist p.1 p.2 ≤ r} :=
  measurableSet_le (by fun_prop) measurable_const

theorem lintegral_smooth_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν] {r : ℝ}
    {O S : Set ℝ} (_hO : MeasurableSet O) (hS : ∀ᵐ y ∂ν, y ∈ S)
    (hballs : ∀ y ∈ S, closedBall y r ⊆ O) :
    (∫⁻ z, smooth ν r z ∂(volume.restrict O)) = ENNReal.ofReal (2*r) := by
  unfold smooth
  rw [lintegral_lintegral_swap (measurable_kernel r).aemeasurable]
  calc
    _ = ∫⁻ _ : ℝ, ENNReal.ofReal (2*r) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hS] with y hy
      have he : (fun z => kernel r z y) = fun z => kernel r y z := by
        funext z
        unfold kernel
        rw [dist_comm]
      rw [he, kernel_lintegral, Measure.restrict_apply isClosed_closedBall.measurableSet,
        inter_eq_left.mpr (hballs y hy), Real.volume_closedBall]
    _ = _ := by simp

theorem lintegral_smooth_sq_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℝ) (_hr : 0 ≤ r) :
    (∫⁻ z, smooth ν r z ^ (2:ℕ)) ≤ ENNReal.ofReal (2*r) * collision ν (2*r) := by
  let H (p : ℝ × (ℝ × ℝ)) := kernel r p.1 p.2.1 * kernel r p.1 p.2.2
  have hmH : Measurable H := by
    exact ((measurable_kernel r).comp (measurable_fst.prodMk measurable_snd.fst)).mul
      ((measurable_kernel r).comp (measurable_fst.prodMk measurable_snd.snd))
  have hm (z : ℝ) : Measurable (kernel r z) :=
    (measurable_kernel r).comp (measurable_const.prodMk measurable_id)
  have hleft (z : ℝ) : smooth ν r z ^ (2:ℕ) = (∫⁻ p, H (z,p) ∂(ν.prod ν)) := by
    rw [show (fun p : ℝ×ℝ => H (z,p)) = (fun p => kernel r z p.1 * kernel r z p.2) from rfl]
    rw [lintegral_prod_mul (hm z).aemeasurable (hm z).aemeasurable, pow_two, smooth]
  simp_rw [hleft]
  rw [lintegral_lintegral_swap hmH.aemeasurable]
  have hs (p : ℝ×ℝ) : (∫⁻ z, H (z,p)) =
      volume (closedBall p.1 r ∩ closedBall p.2 r) := by
    have he : (fun z => H (z,p)) =
        (closedBall p.1 r ∩ closedBall p.2 r).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext z
      simp only [H,kernel,dist_comm p.1 z,dist_comm p.2 z]
      by_cases ha : dist z p.1 ≤ r <;> by_cases hb : dist z p.2 ≤ r <;> simp [ha,hb]
    rw [he,lintegral_indicator_const (isClosed_closedBall.inter isClosed_closedBall).measurableSet,one_mul]
  simp_rw [hs, collision]
  rw [← lintegral_indicator_const (measurableSet_collision (2*r)) (ENNReal.ofReal (2*r))]
  refine lintegral_mono (fun p => ?_)
  by_cases he : dist p.1 p.2 ≤ 2*r
  · rw [indicator_of_mem (show p ∈ {p : ℝ×ℝ | dist p.1 p.2 ≤ 2*r} from he)]
    exact (measure_mono inter_subset_left).trans_eq (Real.volume_closedBall _ _)
  · rw [indicator_of_notMem (show p ∉ {p : ℝ×ℝ | dist p.1 p.2 ≤ 2*r} from he)]
    have hempty : closedBall p.1 r ∩ closedBall p.2 r = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨h1,h2⟩
      exact he ((dist_triangle_left p.1 p.2 z).trans (by
        have h1' : dist z p.1 ≤ r := h1
        have h2' : dist z p.2 ≤ r := h2
        linarith))
    simp [hempty]

/-- A collision upper bound forces positive volume in every open set that contains
the smoothing balls around the support. -/
theorem lower_volume_of_collision (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) {C : ℝ≥0∞} (_hCn : C ≠ ⊤)
    (hcollision : collision ν (2*r) ≤ C * ENNReal.ofReal (2*r))
    {O S : Set ℝ} (hO : MeasurableSet O) (hS : ∀ᵐ y ∂ν, y ∈ S)
    (hballs : ∀ y ∈ S, closedBall y r ⊆ O) :
    1 ≤ C * volume O := by
  let R := ENNReal.ofReal (2*r)
  have hR0 : R ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hRn : R ≠ ⊤ := ENNReal.ofReal_ne_top
  let u := smooth ν r
  let μ : Measure ℝ := volume.restrict O
  have hu : Measurable u := measurable_smooth ν r
  have hA : (∫⁻ z, u z ∂μ) = R := lintegral_smooth_restrict ν hO hS hballs
  have hB : (∫⁻ z, (u z)^(2:ℝ) ∂μ) ≤ C * R^2 := by
    simp only [ENNReal.rpow_ofNat]
    calc
      _ ≤ (∫⁻ z, (u z)^(2:ℕ)) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
      _ ≤ R * collision ν (2*r) := lintegral_smooth_sq_le ν r hr.le
      _ ≤ R * (C * R) := mul_le_mul_right hcollision R
      _ = _ := by rw [pow_two]; ac_rfl
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two)
    (f := u) (g := fun _ => 1) hu.aemeasurable measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hH
  have hμ : μ univ = volume O := by simp [μ]
  rw [hA,hμ] at hH
  have hH' := hH.trans (mul_le_mul_left (ENNReal.rpow_le_rpow hB (by norm_num)) _)
  have hSq := pow_le_pow_left' hH' 2
  have h0 : R^2 ≤ (C*R^2)*volume O := by
    have he : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    simpa only [mul_pow, ← ENNReal.rpow_mul_natCast, Nat.cast_ofNat, he,
      ENNReal.rpow_one] using hSq
  by_contra! hlt
  have hmul : C * volume O * R^2 < 1 * R^2 := by
    have hh := ENNReal.mul_lt_mul_right (pow_ne_zero 2 hR0) (ENNReal.pow_ne_top hRn) hlt
    simpa only [mul_comm] using hh
  exact (not_lt_of_ge h0) (by simpa [mul_comm,mul_left_comm,mul_assoc] using hmul)

end EdgarMillerSmoothing

namespace EdgarMillerProjection

open Filter
open EdgarMillerSmoothing EdgarMillerEnergy

def cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi univ (fun _ => Icc (0:ℝ) 1)

theorem isCompact_cube (n : ℕ) : IsCompact (cube n) := isCompact_univ_pi (fun _ => isCompact_Icc)

theorem ae_in_cube (n : ℕ) : ∀ᵐ a ∂directions n, a ∈ cube n := by
  have hmeas := (isCompact_cube n).isClosed.measurableSet
  have h : directions n (cube n) = 1 := by
    rw [cube,directions,Measure.pi_pi]
    simp [uniformInterval,Measure.restrict_apply measurableSet_Icc,Real.volume_Icc]
  rw [ae_iff]
  change directions n (cube n)ᶜ = 0
  rw [measure_compl hmeas (by simp), measure_univ,h,tsub_self]

private theorem dot_sub {n : ℕ} (a x y : Fin n → ℝ) :
    dot a x - dot a y = dot (x-y) a := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

private theorem slab_norm_bound {n : ℕ} (x y : Fin (n+1) → ℝ) {t : ℝ} (ht : 0<t) :
    directions (n+1) {a | dist (dot a x) (dot a y) ≤ t} ≤
      ENNReal.ofReal (2*t) * (edist x y)⁻¹ := by
  by_cases he : x = y
  · subst y
    rw [edist_self, ENNReal.inv_zero, ENNReal.mul_top (by positivity)]
    exact le_top
  obtain ⟨i,hi⟩ : ∃ i : Fin (n+1), edist (x i) (y i) = edist x y := by
    rw [edist_pi_def,Finset.sup_univ_eq_iSup]
    exact exists_eq_ciSup_of_finite
  have hv : (x-y) i ≠ 0 := by
    intro hz
    have heq : x i = y i := sub_eq_zero.mp hz
    have hz' : edist x y = 0 := by rw [← hi,heq,edist_self]
    exact he (edist_eq_zero.mp hz')
  have hset : {a | dist (dot a x) (dot a y) ≤ t} = {a | |dot (x-y) a| ≤ t} := by
    ext a
    simp only [mem_ofPred_eq,Real.dist_eq,dot_sub]
  rw [hset, ← hi, edist_dist, Real.dist_eq]
  refine (slab_measure_le (x-y) i hv ht.le).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (abs_pos.mpr hv)]
  rfl

private theorem collision_map {n : ℕ} (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν]
    (a : Fin n → ℝ) (t : ℝ) :
    collision (ν.map (dot a)) t = (ν.prod ν) {p | dist (dot a p.1) (dot a p.2) ≤ t} := by
  have hf : Measurable (dot a) := (continuous_dot.comp (continuous_const.prodMk continuous_id)).measurable
  unfold collision
  rw [Measure.map_prod_map _ _ hf hf, Measure.map_apply (hf.prodMap hf)
    (measurableSet_le (by fun_prop) measurable_const)]
  rfl

/-- Finite inverse-distance energy produces a direction with a collision bound at
each positive precision. -/
theorem exists_small_collision {n : ℕ} (ν : Measure (Fin (n+1) → ℝ)) [IsProbabilityMeasure ν]
    (henergy : (∫⁻ p : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ), (edist p.1 p.2)⁻¹ ∂ν.prod ν) < ⊤) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C ≠ ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∃ a ∈ cube (n+1), collision (ν.map (dot a)) t ≤ C * ENNReal.ofReal t := by
  let I := ∫⁻ p : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ), (edist p.1 p.2)⁻¹ ∂(ν.prod ν)
  let C := 2*I+1
  have hi : I < ⊤ := henergy
  have hC : 2*I < C := ENNReal.lt_add_right (ENNReal.mul_ne_top (by norm_num) hi.ne) (by norm_num)
  have hCn : C ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hi.ne,by norm_num⟩
  refine ⟨C, zero_le.trans_lt hC, hCn, fun t ht => ?_⟩
  let T := {p : (Fin (n+1) → ℝ) × ((Fin (n+1)→ℝ) × (Fin (n+1)→ℝ)) |
    dist (dot p.1 p.2.1) (dot p.1 p.2.2) ≤ t}
  have hT : MeasurableSet T := by
    apply measurableSet_le
    · exact ((continuous_dot.comp (continuous_fst.prodMk continuous_snd.fst)).dist
        (continuous_dot.comp (continuous_fst.prodMk continuous_snd.snd))).measurable
    · exact measurable_const
  have hA : (∫⁻ a, collision (ν.map (dot a)) t ∂directions (n+1)) ≤ ENNReal.ofReal t * (2*I) := by
    simp_rw [collision_map]
    change (∫⁻ a, (ν.prod ν) (Prod.mk a ⁻¹' T) ∂directions (n+1)) ≤ _
    rw [← Measure.prod_apply hT,Measure.prod_apply_symm hT]
    calc
      _ ≤ ∫⁻ p : (Fin (n+1)→ℝ) × (Fin (n+1)→ℝ), ENNReal.ofReal (2*t) * (edist p.1 p.2)⁻¹ ∂ν.prod ν :=
        lintegral_mono (fun p => slab_norm_bound p.1 p.2 ht)
      _ = _ := by
        rw [lintegral_const_mul'' _ (by fun_prop), ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
        simp [I,mul_comm,mul_assoc]
  by_contra! h
  have hL : C * ENNReal.ofReal t ≤ ∫⁻ a, collision (ν.map (dot a)) t ∂directions (n+1) := by
    calc
      _ = ∫⁻ _ : Fin (n+1) → ℝ, C * ENNReal.ofReal t ∂directions (n+1) := by simp
      _ ≤ _ := lintegral_mono_ae (by
        filter_upwards [ae_in_cube (n+1)] with a ha
        exact (h a ha).le)
  exact (not_lt_of_ge (hL.trans hA)) (by
    rw [mul_comm C]
    exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top hC)

/-- Uniform collision bounds at arbitrarily fine scales give a positive-measure
projection of a compact set. -/
theorem exists_positive_projection_of_energy {n : ℕ} (ν : Measure (Fin (n+1)→ℝ))
    [IsProbabilityMeasure ν] {K : Set (Fin (n+1)→ℝ)} (hK : IsCompact K) (hν : ∀ᵐ x ∂ν, x∈K)
    (henergy : (∫⁻ p : (Fin (n+1)→ℝ) × (Fin (n+1)→ℝ), (edist p.1 p.2)⁻¹ ∂ν.prod ν) < ⊤) :
    ∃ a ∈ cube (n+1), 0 < volume (dot a '' K) := by
  obtain ⟨C,hCp,hCn,hC⟩ := exists_small_collision ν henergy
  let r (k : ℕ) := (2:ℝ)⁻¹ ^ k
  have hr (k : ℕ) : 0 < r k := by unfold r; positivity
  choose a ha H using fun k : ℕ => hC (2*r k) (by positivity [hr k])
  obtain ⟨b,hbc,φ,hφ,hconv⟩ := (isCompact_cube (n+1)).isSeqCompact ha
  have hcont (x : Fin (n+1) → ℝ) : Continuous (dot x) :=
    continuous_dot.comp (continuous_const.prodMk continuous_id)
  let S := dot b '' K
  have hS : IsCompact S := hK.image (hcont b)
  refine ⟨b,hbc,?_⟩
  by_contra! hzero
  have ho : volume S < C⁻¹ := lt_of_le_of_lt hzero (ENNReal.inv_pos.mpr hCn)
  obtain ⟨O,hOS,hO,hvol⟩ := S.exists_isOpen_lt_of_lt _ ho
  obtain ⟨δ,hδ,hδO⟩ := hS.exists_thickening_subset_open hO hOS
  have hUC : UniformContinuousOn (fun p : (Fin (n+1)→ℝ) × (Fin (n+1)→ℝ) => dot p.1 p.2)
      (cube (n+1) ×ˢ K) :=
    ((isCompact_cube (n+1)).prod hK).uniformContinuousOn_of_continuous continuous_dot.continuousOn
  obtain ⟨ε,hε,hεUC⟩ := Metric.uniformContinuousOn_iff.mp hUC (δ/2) (half_pos hδ)
  have hlimr : Tendsto r atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hrsmall := (hlimr.comp hφ.tendsto_atTop).eventually (gt_mem_nhds (half_pos hδ))
  have haSmall := (tendsto_iff_dist_tendsto_zero.mp hconv).eventually (gt_mem_nhds hε)
  obtain ⟨k,hk,haK⟩ := (hrsmall.and haSmall).exists
  let ν' := ν.map (dot (a (φ k)))
  let S' := dot (a (φ k)) '' K
  have hi : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map (hcont _).measurable.aemeasurable
  have hν' : ∀ᵐ x ∂ν', x ∈ S' := by
    have hmeas : MeasurableSet S' := (hK.image (hcont _)).isClosed.measurableSet
    exact (ae_map_iff (hcont (a (φ k))).measurable.aemeasurable hmeas).mpr
      (hν.mono (fun x hx => mem_image_of_mem _ hx))
  have hbO (x : ℝ) (hx : x ∈ S') : closedBall x (r (φ k)) ⊆ O := by
    obtain ⟨y,hy,rfl⟩ := hx
    intro z hz
    apply hδO
    apply Metric.mem_thickening_iff.mpr
    refine ⟨dot b y, mem_image_of_mem _ hy,?_⟩
    have hprod : dist ((a (φ k)),y) (b,y) < ε := by
      rw [Prod.dist_eq,dist_self,max_eq_left dist_nonneg]
      exact haK
    have hh := hεUC (a (φ k),y) ⟨ha _,hy⟩ (b,y) ⟨hbc,hy⟩ hprod
    exact (dist_triangle z _ _).trans_lt (by
      have hz' : dist z (dot (a (φ k)) y) ≤ r (φ k) := hz
      change dist (dot (a (φ k)) y) (dot b y) < δ/2 at hh
      change r (φ k) < δ/2 at hk
      linarith)
  have hvol' : 1 ≤ C * volume O :=
    lower_volume_of_collision ν' (hr _) hCn (H _) hO.measurableSet hν' hbO
  apply (not_lt_of_ge hvol')
  exact (ENNReal.mul_lt_mul_right hCp.ne' hCn hvol).trans_eq (ENNReal.mul_inv_cancel hCp.ne' hCn)

end EdgarMillerProjection
namespace EdgarMillerProjection

open EdgarMillerEnergy

/-- Positive Frostman exponent on a compact real set implies that some finite
Cartesian power has a positive-volume linear image. -/
theorem positive_projection_of_frostman (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K : Set ℝ} (hK : IsCompact K) (hμ : μ K = 1)
    {s : ℝ} (hs : 0 < s) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hball : ∀ x : ℝ, ∀ k : ℕ, μ (closedEBall x (EdgarMillerEnergy.dyadic k)) ≤ B*(EdgarMillerEnergy.dyadic k)^s) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ, 0 < volume (dot a '' Set.pi univ (fun _ => K)) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/s)
  let m := n+1
  have hs' : 1 < s*(m:ℝ) := by
    have h := (div_lt_iff₀ hs).mp hn
    dsimp [m]
    push_cast
    nlinarith
  let ν := Measure.pi (fun _ : Fin m => μ)
  let Kp : Set (Fin m→ℝ) := Set.pi univ (fun _ => K)
  have hKp : IsCompact Kp := isCompact_univ_pi (fun _ => hK)
  have hνK : ν Kp = 1 := by
    unfold ν Kp
    rw [Measure.pi_pi]
    simp [hμ]
  have hν : ∀ᵐ a ∂ν, a ∈ Kp := by
    rw [ae_iff]
    change ν Kpᶜ = 0
    rw [measure_compl hKp.isClosed.measurableSet (by simp), measure_univ,hνK,tsub_self]
  let q : ℝ≥0∞ := (2:ℝ≥0∞)⁻¹ ^ (s*(m:ℝ))
  have hq : 2*q < 1 := by
    have he : 2*q = (2:ℝ≥0∞)^(1-s*(m:ℝ)) := by
      unfold q
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, sub_eq_add_neg,
        ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
    rw [he]
    calc
      _ < (2:ℝ≥0∞)^(0:ℝ) := ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
        (sub_neg.mpr hs')
      _ = 1 := ENNReal.rpow_zero
  have hnear (k : ℕ) : (ν.prod ν) (near (dyadic k)) ≤ B^m*q^k := by
    refine (near_product_measure_le μ (fun x => hball x k)).trans_eq ?_
    change (B * (((2:ℝ≥0∞)⁻¹)^k)^s)^m = B^m * (((2:ℝ≥0∞)⁻¹)^(s*(m:ℝ)))^k
    rw [mul_pow]
    congr 1
    rw [← ENNReal.rpow_mul_natCast (((2:ℝ≥0∞)⁻¹)^k) s m,
      ← ENNReal.rpow_natCast_mul ((2:ℝ≥0∞)⁻¹) k (s*(m:ℝ)),
      ← ENNReal.rpow_mul_natCast ((2:ℝ≥0∞)⁻¹) (s*(m:ℝ)) k]
    congr 1
    ring
  have en := lintegral_inv_edist_lt_top (ν.prod ν) (ENNReal.pow_ne_top hB) hq hnear
  obtain ⟨a,_,ha⟩ := exists_positive_projection_of_energy (n := n) ν hKp hν en
  exact ⟨m,a,ha⟩

end EdgarMillerProjection

namespace EdgarMiller

/-- A compact subset carrying a positive-exponent Frostman measure forces an
analytic real subring to be the whole real line. -/
theorem eq_top_of_frostman {R : Subring ℝ} (hR : AnalyticSet (R : Set ℝ))
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {K : Set ℝ} (hK : IsCompact K) (hKR : K ⊆ (R : Set ℝ)) (hμ : μ K = 1)
    {s : ℝ} (hs : 0 < s) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hball : ∀ x : ℝ, ∀ k : ℕ, μ (closedEBall x (EdgarMillerEnergy.dyadic k)) ≤ B*(EdgarMillerEnergy.dyadic k)^s) : R = ⊤ := by
  obtain ⟨n,a,ha⟩ := EdgarMillerProjection.positive_projection_of_frostman μ hK hμ hs hB hball
  let S := EdgarMillerProjection.dot a '' Set.pi univ (fun _ => K)
  have hcont : Continuous (EdgarMillerProjection.dot a) :=
    EdgarMillerProjection.continuous_dot.comp (continuous_const.prodMk continuous_id)
  have hSc : IsCompact S := (isCompact_univ_pi (fun _ => hK)).image hcont
  apply eq_top_of_positive_projection hR
  refine ⟨n,a,S,hSc.isClosed.measurableSet,ha,?_⟩
  rintro _ ⟨u,hu,rfl⟩
  exact ⟨fun i => ⟨u i,hKR (hu i (mem_univ _))⟩,rfl⟩

end EdgarMiller

/-
The analytic-set selection step of Choquet capacitability.
A bounded-coordinate recursion in Baire space gives a compact subset retaining
any strict lower bound for a capacity continuous on monotone sequences.
-/

noncomputable section

open Set MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace EdgarMillerCapacity

private structure Active {X : Type*} (c : Set X → ℝ≥0∞) (f : (ℕ → ℕ) → X) (d : ℝ≥0∞) (n : ℕ) where
  domain : Set (ℕ → ℕ)
  above : d < c (f '' domain)
  bounded : ∀ i < n, BddAbove ((fun u : ℕ → ℕ => u i) '' domain)

private structure Refinement {X : Type*} {c : Set X → ℝ≥0∞} {f : (ℕ → ℕ) → X}
    {d : ℝ≥0∞} {n : ℕ} (A : Active c f d n) where
  active : Active c f d (n+1)
  subset : active.domain ⊆ A.domain

private theorem refine_active {X : Type*} {c : Set X → ℝ≥0∞}
    (hup : ∀ s : ℕ → Set X, Monotone s → c (⋃ i, s i) = ⨆ i, c (s i))
    {f : (ℕ → ℕ) → X} {d : ℝ≥0∞} {n : ℕ} (A : Active c f d n) :
    Nonempty (Refinement A) := by
  let D (m : ℕ) := A.domain ∩ {u : ℕ → ℕ | u n ≤ m}
  have hD : Monotone D := fun _ _ h _ hx => ⟨hx.1, hx.2.trans h⟩
  have his : Monotone (fun m => f '' D m) := fun _ _ h => image_mono (hD h)
  have he : f '' A.domain = ⋃ m, f '' D m := by
    apply Subset.antisymm
    · rintro _ ⟨u,hu,rfl⟩
      exact mem_iUnion.mpr ⟨u n, ⟨u,⟨hu,show u n ≤ u n from le_rfl⟩,rfl⟩⟩
    · refine iUnion_subset (fun m => image_mono ?_)
      exact inter_subset_left
  have hcap := A.above
  rw [he,hup _ his,lt_iSup_iff] at hcap
  obtain ⟨m,hm⟩ := hcap
  refine ⟨⟨⟨D m, hm,?_⟩,inter_subset_left⟩⟩
  intro i hi
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
  · exact (A.bounded i h).mono (image_mono inter_subset_left)
  · refine ⟨m, ?_⟩
    rintro z ⟨u,hu,rfl⟩
    exact hu.2

/-- If a capacity is continuous on increasing sets and decreasing compacts, any lower bound
strictly below its value on an analytic set is attained on a compact subset. -/
theorem exists_compact_of_analytic {X : Type*} [MetricSpace X] [CompactSpace X]
    (c : Set X → ℝ≥0∞) (hmono : Monotone c) (hempty : c ∅ = 0)
    (hup : ∀ s : ℕ → Set X, Monotone s → c (⋃ i, s i) = ⨆ i, c (s i))
    (hdown : ∀ s : ℕ → Set X, Antitone s → (∀ n, IsCompact (s n)) →
      c (⋂ i, s i) = ⨅ i, c (s i))
    {S : Set X} (hS : AnalyticSet S) {d : ℝ≥0∞} (hd : d < c S) :
    ∃ K ⊆ S, IsCompact K ∧ d ≤ c K := by
  classical
  rw [AnalyticSet] at hS
  rcases hS with rfl | ⟨f,hf,hfS⟩
  · rw [hempty] at hd
    exact (not_lt_zero hd).elim
  let initial : Active c f d 0 :=
    ⟨univ, by rwa [image_univ,hfS], fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩
  let stage : (n : ℕ) → Active c f d n :=
    Nat.rec initial (fun _ A => (Classical.choice (refine_active hup A)).active)
  have hnest : Antitone (fun n => (stage n).domain) :=
    antitone_nat_of_succ_le (fun n => (Classical.choice (refine_active hup (stage n))).subset)
  let E (n : ℕ) := closure (f '' (stage n).domain)
  have hE : Antitone E := fun _ _ h => closure_mono (image_mono (hnest h))
  have hcE (n : ℕ) : IsCompact (E n) := isClosed_closure.isCompact
  let K := ⋂ n, E n
  have hcK : IsCompact K := (isClosed_iInter (fun _ => isClosed_closure)).isCompact
  have hcapK : d ≤ c K := by
    change d ≤ c (⋂ n, E n)
    rw [hdown E hE hcE]
    exact le_iInf (fun n => (stage n).above.le.trans (hmono subset_closure))
  refine ⟨K,?_,hcK,hcapK⟩
  intro x hx
  have hxn (n : ℕ) : x ∈ closure (f '' (stage n).domain) := mem_iInter.mp hx n
  have hex (n : ℕ) : ∃ u ∈ (stage n).domain, dist (f u) x < (2:ℝ)⁻¹ ^ n := by
    have hp : 0 < (2:ℝ)⁻¹ ^ n := by positivity
    obtain ⟨z,⟨u,hu,rfl⟩,hz⟩ := Metric.mem_closure_iff.mp (hxn n) _ hp
    exact ⟨u,hu,by simpa only [dist_comm] using hz⟩
  choose u hu hudist using hex
  have column_finite (i : ℕ) : (range (fun n => u n i)).Finite := by
    obtain ⟨b,hb⟩ := (stage (i+1)).bounded i (Nat.lt_succ_self _)
    refine ((finite_Iic b).union ((finite_Iic i).image (fun n => u n i))).subset ?_
    rintro _ ⟨n,rfl⟩
    by_cases h : i+1 ≤ n
    · exact Or.inl (hb ⟨u n,hnest h (hu n),rfl⟩)
    · exact Or.inr ⟨n,mem_Iic.mpr (by omega),rfl⟩
  let C := Set.pi univ (fun i => range (fun n => u n i))
  have hc : IsCompact C := isCompact_univ_pi (fun i => (column_finite i).isCompact)
  have huc (n : ℕ) : u n ∈ C := by intro i _; exact mem_range_self _
  obtain ⟨a,_,φ,hφ,hcon⟩ := hc.isSeqCompact huc
  have hfx : Tendsto (fun n => f (u n)) atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have ht : Tendsto (fun n : ℕ => (2:ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hudist n).le) ht
  have hfsub : Tendsto (fun n => f (u (φ n))) atTop (𝓝 x) :=
    hfx.comp hφ.tendsto_atTop
  have heq : f a = x := tendsto_nhds_unique (hf.continuousAt.tendsto.comp hcon) hfsub
  rw [← hfS,← heq]
  exact mem_range_self _

end EdgarMillerCapacity

/-
Dyadic cylinder content on binary sequence space.
-/

noncomputable section

open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace EdgarMillerDyadic

abbrev Binary := ℕ → Fin 2

abbrev Word := Σ n : ℕ, Fin n → Fin 2

def cylinder (p : Word) : Set Binary := {x | ∀ i : Fin p.1, x i.val = p.2 i}

def head (x : Binary) (n : ℕ) : Word := ⟨n, fun i => x i.val⟩

theorem mem_head (x : Binary) (n : ℕ) : x ∈ cylinder (head x n) := fun _ => rfl

theorem head_eq {x : Binary} {p : Word} (hx : x ∈ cylinder p) : head x p.1 = p := by
  cases p with
  | mk n p =>
    change (⟨n, fun i => x i.val⟩ : Word) = ⟨n,p⟩
    congr
    exact funext hx

theorem cylinder_nonempty (p : Word) : (cylinder p).Nonempty := by
  classical
  exact ⟨fun i => if h : i < p.1 then p.2 ⟨i,h⟩ else 0,
    fun i => by simp [i.isLt]⟩

theorem isClopen_cylinder (p : Word) : IsClopen (cylinder p) := by
  have he : cylinder p = ⋂ i : Fin p.1, (fun x : Binary => x i.val) ⁻¹' {p.2 i} := by
    ext x
    simp [cylinder]
  rw [he]
  exact ⟨isClosed_iInter (fun i => isClosed_singleton.preimage (continuous_apply _)),
    isOpen_iInter_of_finite (fun i => (isOpen_discrete _).preimage (continuous_apply _))⟩

theorem isCompact_cylinder (p : Word) : IsCompact (cylinder p) :=
  (isClopen_cylinder p).isClosed.isCompact

theorem cylinder_subset_of_overlap {p q : Word} {x : Binary}
    (h : p.1 ≤ q.1) (hp : x ∈ cylinder p) (hq : x ∈ cylinder q) :
    cylinder q ⊆ cylinder p := by
  intro y hy i
  let j : Fin q.1 := ⟨i.val,i.isLt.trans_le h⟩
  exact (hy j).trans ((hq j).symm.trans (hp i))

theorem eq_of_overlap_of_length_eq {p q : Word} {x : Binary}
    (hp : x ∈ cylinder p) (hq : x ∈ cylinder q) (h : p.1 = q.1) : p = q :=
  (head_eq hp).symm.trans (h ▸ head_eq hq)

def weight (s : ℝ) (p : Word) : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹)^(s * (p.1:ℝ))

def Covered (A : Set Binary) (C : Set Word) : Prop := A ⊆ ⋃ p : C, cylinder p.val

def cost (s : ℝ) (C : Set Word) : ℝ≥0∞ := ∑' p : C, weight s p.val

def content (s : ℝ) (A : Set Binary) : ℝ≥0∞ := ⨅ C : Set Word, ⨅ _ : Covered A C, cost s C

theorem content_mono (s : ℝ) : Monotone (content s) := by
  intro A B hAB
  exact le_iInf (fun C => le_iInf (fun hC => iInf_le_of_le C (iInf_le_of_le (hAB.trans hC) le_rfl)))

theorem content_le_cost (s : ℝ) {A : Set Binary} {C : Set Word} (hC : Covered A C) :
    content s A ≤ cost s C := iInf_le_of_le C (iInf_le _ hC)

theorem exists_cover_of_content_lt (s : ℝ) {A : Set Binary} {r : ℝ≥0∞}
    (h : content s A < r) : ∃ C : Set Word, Covered A C ∧ cost s C < r := by
  obtain ⟨C,hC,hlt⟩ := (by simpa only [content,iInf_lt_iff] using h : ∃ C, ∃ (_ : Covered A C), cost s C < r)
  exact ⟨C,hC,hlt⟩

theorem content_empty (s : ℝ) : content s ∅ = 0 :=
  le_antisymm ((content_le_cost s (C := ∅) (empty_subset _)).trans_eq (by simp [cost])) zero_le

theorem content_le_one (s : ℝ) (A : Set Binary) : content s A ≤ 1 := by
  let p : Word := ⟨0, fun i => i.elim0⟩
  refine (content_le_cost s (C := {p}) (fun x _ => mem_iUnion.mpr ⟨⟨p,rfl⟩,?_⟩)).trans_eq ?_
  · intro i
    exact i.elim0
  · simp [cost,weight,p]

theorem ediam_image_cylinder (p : Word) :
    ediam (Real.ofDigits '' cylinder p) ≤ ((2:ℝ≥0∞)⁻¹)^p.1 := by
  apply ediam_le_iff.mpr
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  have h := Real.abs_ofDigits_sub_ofDigits_le (b := 2) (x := x) (y := y) (n := p.1)
    (fun i hi => (hx ⟨i,hi⟩).trans (hy ⟨i,hi⟩).symm)
  rw [edist_dist, Real.dist_eq]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.inv_pow]
  norm_num

theorem content_preimage_pos {A : Set ℝ} (hA : A ⊆ Icc 0 1) {s : ℝ≥0}
    (hs : 0 < s) (hd : (s:ℝ≥0∞)<dimH A) :
    0 < content (s:ℝ) (Real.ofDigits (b := 2) ⁻¹' A) := by
  by_contra! hz
  have hz' := le_antisymm hz (zero_le (a := content (s:ℝ) (Real.ofDigits (b := 2) ⁻¹' A)))
  let r (k : ℕ) : ℝ≥0∞ := (2:ℝ≥0∞)⁻¹ ^ k
  have hr (k : ℕ) : 0 < (r k)^(s:ℝ)*r k := by
    have hbase : (0:ℝ≥0∞) < (2:ℝ≥0∞)⁻¹ := ENNReal.inv_pos.mpr (by norm_num)
    have hk : 0 < r k := pos_iff_ne_zero.mpr (pow_ne_zero _ hbase.ne')
    exact ENNReal.mul_pos (ENNReal.rpow_pos_of_nonneg hk s.2).ne' hk.ne'
  have hlt (k : ℕ) : content (s:ℝ) (Real.ofDigits (b := 2) ⁻¹' A) < (r k)^(s:ℝ)*r k :=
    hz'.symm ▸ hr k
  choose C hC HC using fun k => exists_cover_of_content_lt _ (hlt k)
  let U (k : ℕ) (p : C k) := Real.ofDigits (b := 2) '' cylinder p.val
  have hbound (k : ℕ) : r k ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hrad (k : ℕ) (p : C k) : ediam (U k p) ≤ r k := by
    have hg := ENNReal.le_tsum (f := fun p : C k => weight (s:ℝ) p.val) p
    have hcost : weight (s:ℝ) p.val ≤ (r k)^(s:ℝ) :=
      hg.trans ((HC k).le.trans (mul_le_of_le_one_right zero_le (hbound k)))
    have hp : ((2:ℝ≥0∞)⁻¹)^p.val.1 ≤ r k := by
      apply (ENNReal.rpow_le_rpow_iff (by exact_mod_cast hs : (0:ℝ)<s)).mp
      rw [← ENNReal.rpow_natCast_mul]
      simpa only [weight,mul_comm (p.val.1:ℝ)] using hcost
    exact (ediam_image_cylinder _).trans hp
  have hcover (k : ℕ) : A ⊆ ⋃ p, U k p := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Real.ofDigits_SurjOn (by decide : 1<2) (hA hx)
    obtain ⟨p,hp⟩ := mem_iUnion.mp (hC k hx)
    exact mem_iUnion.mpr ⟨p,⟨y,hp,rfl⟩⟩
  have hcost (k : ℕ) : (∑' p, ediam (U k p)^(s:ℝ)) ≤ r k := by
    refine (ENNReal.tsum_le_tsum (fun p => ?_)).trans ((HC k).le.trans ?_)
    · have h := ENNReal.rpow_le_rpow (ediam_image_cylinder p.val) s.coe_nonneg
      rw [← ENNReal.rpow_natCast_mul] at h
      simpa only [weight,mul_comm (p.val.1:ℝ)] using h
    · exact mul_le_of_le_one_left zero_le
        (by simpa using ENNReal.rpow_le_rpow (hbound k) s.coe_nonneg)
  have hlim : Tendsto r atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hm := Measure.hausdorffMeasure_le_liminf_tsum (s:ℝ) A r hlim U
    (Eventually.of_forall hrad) (Eventually.of_forall hcover)
  have hzero : μH[s] A = 0 := le_antisymm
    (hm.trans ((liminf_le_liminf (Eventually.of_forall hcost)).trans_eq hlim.liminf_eq)) zero_le
  exact ENNReal.top_ne_zero ((hausdorffMeasure_of_lt_dimH hd).symm.trans hzero)

private def coveredUnion (C : Set Word) : Set Binary := ⋃ p : C, cylinder p.val

private def prune (C : Set Word) : Set Word :=
  {p | p ∈ C ∧ ¬ ∃ q ∈ C, q.1 < p.1 ∧ cylinder p ⊆ cylinder q}

private theorem coveredUnion_prune (C : Set Word) : coveredUnion (prune C) = coveredUnion C := by
  classical
  apply Subset.antisymm
  · rintro x hx
    obtain ⟨p,hp⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨p.val,p.2.1⟩,hp⟩
  · intro x hx
    let S := {n : ℕ | ∃ p ∈ C, p.1=n ∧ x∈cylinder p}
    obtain ⟨p,hp⟩ := mem_iUnion.mp hx
    have hex : ∃ n, n∈S := ⟨p.val.1,p.val,p.2,rfl,hp⟩
    obtain ⟨q,hq,hqn,hxq⟩ := Nat.find_spec hex
    refine mem_iUnion.mpr ⟨⟨q,hq,?_⟩,hxq⟩
    rintro ⟨w,hw,hlt,hsub⟩
    exact Nat.find_min hex (hqn ▸ hlt) ⟨w,hw,rfl,hsub hxq⟩

private def interCuts (C D : Set Word) : Set Word :=
  {p | (p ∈ C ∧ ∃ q ∈ D, q.1 ≤ p.1 ∧ cylinder p ⊆ cylinder q) ∨
       (p ∈ D ∧ ∃ q ∈ C, q.1 ≤ p.1 ∧ cylinder p ⊆ cylinder q)}

private theorem coveredUnion_interCuts (C D : Set Word) :
    coveredUnion C ∩ coveredUnion D ⊆ coveredUnion (interCuts C D) := by
  rintro x ⟨hC,hD⟩
  obtain ⟨p,hp⟩ := mem_iUnion.mp hC
  obtain ⟨q,hq⟩ := mem_iUnion.mp hD
  rcases le_total p.val.1 q.val.1 with h | h
  · exact mem_iUnion.mpr ⟨⟨q.val,Or.inr ⟨q.2,p.val,p.2,h,cylinder_subset_of_overlap h hp hq⟩⟩,hq⟩
  · exact mem_iUnion.mpr ⟨⟨p.val,Or.inl ⟨p.2,q.val,q.2,h,cylinder_subset_of_overlap h hq hp⟩⟩,hp⟩

private theorem cost_pair (s : ℝ) (C D : Set Word) :
    cost s (prune (C∪D)) + cost s (interCuts C D) ≤ cost s C + cost s D := by
  classical
  have cost_eq (B : Set Word) : cost s B = ∑' p : Word, B.indicator (weight s) p :=
    tsum_subtype B (weight s)
  simp only [cost_eq, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum (fun p => ?_)
  have hC (h : p ∈ prune (C∪D)) : p∈C ∨ p∈D := h.1
  have hD (h : p ∈ interCuts C D) : p∈C ∨ p∈D := h.elim (fun z => Or.inl z.1) (fun z => Or.inr z.1)
  have hI (h₁ : p ∈ prune (C∪D)) (h₂ : p ∈ interCuts C D) : p ∈ C ∧ p∈D := by
    have he (q : Word) (hq : q ∈ C∪D) (hlen : q.1 ≤ p.1)
        (hsub : cylinder p ⊆ cylinder q) : p = q := by
      obtain ⟨x,hx⟩ := cylinder_nonempty p
      have heq : p.1 = q.1 := le_antisymm
        (le_of_not_gt (fun h => h₁.2 ⟨q,hq,h,hsub⟩)) hlen
      exact eq_of_overlap_of_length_eq hx (hsub hx) heq
    rcases h₂ with ⟨hp,q,hq,hl,hs⟩ | ⟨hp,q,hq,hl,hs⟩
    · exact ⟨hp,(he q (Or.inr hq) hl hs).symm ▸ hq⟩
    · exact ⟨(he q (Or.inl hq) hl hs).symm ▸ hq,hp⟩
  by_cases hc : p∈C <;> by_cases hd : p∈D <;> by_cases hp : p∈prune (C∪D) <;>
    by_cases hq : p∈interCuts C D <;> simp_all [Set.indicator]

/-- Dyadic content is strongly subadditive because intersecting cylinders are nested. -/
theorem content_union_inter_le (s : ℝ) (A B : Set Binary) :
    content s (A∪B) + content s (A∩B) ≤ content s A + content s B := by
  unfold content
  apply ENNReal.le_iInf₂_add_iInf₂
  intro C hC D hD
  have hCD : coveredUnion (C∪D) = coveredUnion C ∪ coveredUnion D := by
    ext x
    simp only [coveredUnion,mem_iUnion,Subtype.exists,exists_prop,mem_union]
    aesop
  have hU : Covered (A∪B) (prune (C∪D)) := by
    change A∪B ⊆ coveredUnion (prune (C∪D))
    rw [coveredUnion_prune,hCD]
    exact union_subset_union hC hD
  have hI : Covered (A∩B) (interCuts C D) :=
    (inter_subset_inter hC hD).trans (coveredUnion_interCuts C D)
  exact (add_le_add (content_le_cost s hU) (content_le_cost s hI)).trans (cost_pair s C D)

private theorem isOpen_coveredUnion (C : Set Word) : IsOpen (coveredUnion C) :=
  isOpen_iUnion (fun p => (isClopen_cylinder p.val).isOpen)

private theorem exists_open_cover_of_content_lt (s : ℝ) {A : Set Binary} {r : ℝ≥0∞}
    (h : content s A < r) :
    ∃ U : Set Binary, A ⊆ U ∧ IsOpen U ∧ content s U < r := by
  obtain ⟨C,hC,hlt⟩ := exists_cover_of_content_lt s h
  exact ⟨coveredUnion C,hC,isOpen_coveredUnion C,(content_le_cost s Subset.rfl).trans_lt hlt⟩

theorem content_iInter_compact (s : ℝ) (A : ℕ→Set Binary) (hA : Antitone A)
    (hK : ∀ n, IsCompact (A n)) : content s (⋂ n, A n) = ⨅ n, content s (A n) := by
  apply le_antisymm (le_iInf (fun n => content_mono s (iInter_subset _ n)))
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨U,hU,hUo,hUr⟩ := exists_open_cover_of_content_lt s hr
  obtain ⟨n,hn⟩ : ∃ n, A n ⊆ U := by
    have hEmpty : ⋂ n, A n \ U = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
      have hx' : x ∈ ⋂ n, A n := mem_iInter.mpr (fun n => (mem_iInter.mp hx n).1)
      exact (mem_iInter.mp hx 0).2 (hU hx')
    by_contra! h
    have nh : ∀ n, (A n \ U).Nonempty := fun n => not_subset.mp (h n)
    have hd : Antitone (fun n => A n \ U) := fun _ _ hh _ hx => ⟨hA hh hx.1,hx.2⟩
    have hc : ∀ n, IsCompact (A n \ U) := fun n => (hK n).diff hUo
    exact (IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      _ (fun n => hd (Nat.le_succ n)) nh (hc 0) (fun n => (hc n).isClosed)).ne_empty hEmpty
  exact (iInf_le _ n).trans ((content_mono s hn).trans hUr.le)

private def fair : Measure Binary :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin 2)).toMeasure)

private theorem fair_cylinder (p : Word) : fair (cylinder p) = ((2:ℝ≥0∞)⁻¹)^p.1 := by
  classical
  let T (i : ℕ) : Set (Fin 2) := if h : i < p.1 then {p.2 ⟨i,h⟩} else univ
  have he : cylinder p = (↑(Finset.range p.1) : Set ℕ).pi T := by
    ext x
    constructor
    · intro hx i hi
      have hi' := Finset.mem_range.mp hi
      simpa [T,hi'] using hx ⟨i,hi'⟩
    · intro hx i
      have hi' := hx i.val (Finset.mem_range.mpr i.isLt)
      simpa [T,i.isLt] using hi'
  rw [he, fair, Measure.infinitePi_pi _ (fun i _ => MeasurableSet.of_discrete)]
  rw [Finset.prod_congr rfl (fun i hi => ?_), Finset.prod_const, Finset.card_range]
  have h := Finset.mem_range.mp hi
  simp [T,h,PMF.uniformOfFintype_apply]

private theorem weight_le_descendant_cost (s : ℝ) (hs : s ≤ 1) (p : Word) (D : Set Word)
    (hD : Covered (cylinder p) D) (hl : ∀ q ∈ D, p.1 ≤ q.1) :
    weight s p ≤ cost s D := by
  have hz : ((2:ℝ≥0∞)⁻¹) ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  have ht : ((2:ℝ≥0∞)⁻¹) ≠ ∞ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hfz : fair (cylinder p) ≠ 0 := by rw [fair_cylinder]; exact pow_ne_zero _ hz
  have hft : fair (cylinder p) ≠ ∞ := by rw [fair_cylinder]; exact ENNReal.pow_ne_top ht
  apply (ENNReal.mul_le_mul_iff_left hfz hft).mp
  rw [mul_comm (weight s p),mul_comm (cost s D)]
  calc
        fair (cylinder p)*weight s p ≤ (∑' q : D, fair (cylinder q.val))*weight s p :=
          mul_le_mul' ((measure_mono hD).trans (measure_iUnion_le _)) le_rfl
        _ = ∑' q : D, fair (cylinder q.val)*weight s p := ENNReal.tsum_mul_right.symm
        _ ≤ ∑' q : D, fair (cylinder p)*weight s q.val := by
          apply ENNReal.tsum_le_tsum
          intro q
          rw [fair_cylinder, fair_cylinder, weight, weight, ← ENNReal.rpow_natCast,
            ← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hz ht, ← ENNReal.rpow_add _ _ hz ht]
          apply ENNReal.rpow_le_rpow_of_exponent_ge (by norm_num)
          have h : (p.1:ℝ) ≤ q.val.1 := by exact_mod_cast hl q.val q.2
          nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr h)]
        _ = fair (cylinder p)*cost s D := ENNReal.tsum_mul_left

private def HasAncestor (C : Set Word) (p : Word) : Prop :=
  ∃ q ∈ C, q.1 ≤ p.1 ∧ cylinder p ⊆ cylinder q

private theorem cost_partition (s : ℝ) (C D : Set Word) (hD : D ⊆ C) :
    cost s (C \ D) + cost s D = cost s C := by
  classical
  simp only [cost,tsum_subtype, ← ENNReal.tsum_add]
  apply tsum_congr
  intro p
  by_cases h' : p ∈ D
  · have h := hD h'
    simp [Set.indicator,h,h']
  · by_cases h : p ∈ C <;> simp [Set.indicator,h,h']

private theorem compress_one (s : ℝ) (hs : s ≤ 1) {A : Set Binary} {C : Set Word}
    (hC : Covered A C) (p : Word) (hp : cylinder p ⊆ A) :
    ∃ D : Set Word, Covered A D ∧ cost s D ≤ cost s C ∧ HasAncestor D p ∧
        ∀ q, HasAncestor C q → HasAncestor D q := by
  classical
  by_cases h : HasAncestor C p
  · exact ⟨C,hC,le_rfl,h,fun _ => id⟩
  let E : Set Word := {q ∈ C | p.1 ≤ q.1 ∧ cylinder q ⊆ cylinder p}
  let D : Set Word := insert p (C \ E)
  have hE : E ⊆ C := fun _ h => h.1
  have hCE : Covered (cylinder p) E := by
    intro x hx
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hC (hp hx))
    have hle : p.1 ≤ q.val.1 := by
        by_contra! hh
        exact h ⟨q.val,q.2,hh.le,cylinder_subset_of_overlap hh.le hq hx⟩
    exact mem_iUnion.mpr ⟨⟨q.val,q.2,hle,cylinder_subset_of_overlap hle hx hq⟩,hq⟩
  have hCost : weight s p ≤ cost s E := weight_le_descendant_cost s hs p E hCE (fun _ h => h.2.1)
  have hCostD : cost s D ≤ weight s p + cost s (C \ E) := by
    have he (B : Set Word) : cost s B = ∑' q : Word, B.indicator (weight s) q :=
        tsum_subtype B (weight s)
    have he' : (∑' q : Word, ({p} : Set Word).indicator (weight s) q) = weight s p :=
      (he {p}).symm.trans (by simp [cost])
    rw [he, he (C \ E), ← he', ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro q
    by_cases heq : q = p <;> simp [D,Set.indicator,heq]
  have hpD : p∈D := mem_insert p _
  refine ⟨D,?_,hCostD.trans ?_,⟨p,hpD,le_rfl,Subset.rfl⟩,?_⟩
  · intro x hx
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hC hx)
    by_cases he : q.val ∈ E
    · exact mem_iUnion.mpr ⟨⟨p,hpD⟩,he.2.2 hq⟩
    · exact mem_iUnion.mpr ⟨⟨q.val,mem_insert_of_mem _ ⟨q.2,he⟩⟩,hq⟩
  · rw [add_comm, ← cost_partition s C E hE]
    exact add_le_add_right hCost _
  · rintro q ⟨w,hw,hlen,hsub⟩
    by_cases he : w∈E
    · exact ⟨p,hpD,he.2.1.trans hlen,hsub.trans he.2.2⟩
    · exact ⟨w,mem_insert_of_mem _ ⟨hw,he⟩,hlen,hsub⟩

private theorem compress_finite (s : ℝ) (hs : s ≤ 1) {A : Set Binary} {C : Set Word}
    (hC : Covered A C) (F : Finset Word) (hF : ∀ p∈F, cylinder p ⊆ A) :
    ∃ D : Set Word, Covered A D ∧ cost s D ≤ cost s C ∧ ∀ p∈F, HasAncestor D p := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨C,hC,le_rfl,by simp⟩
  | @insert p F hp ih =>
    obtain ⟨D,hD,hDC,hDF⟩ := ih (fun q hq => hF q (Finset.mem_insert_of_mem hq))
    obtain ⟨E,hE,hED,hEp,hED'⟩ := compress_one s hs hD p (hF p (Finset.mem_insert_self _ _))
    refine ⟨E,hE,hED.trans hDC,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hEp
    · exact hED' q (hDF q hq)

private def selectWords (f : Word → Fin 2) : Set Word := {p | f p = 1}

private theorem isClosed_lowCost (s : ℝ) (b : ℝ≥0∞) :
    IsClosed {f : Word → Fin 2 | cost s (selectWords f) ≤ b} := by
  classical
  let val (f : Word → Fin 2) (p : Word) : ℝ≥0∞ := if f p = 1 then weight s p else 0
  have hval (p : Word) : Continuous (fun f => val f p) := by
    show Continuous ((fun z : Fin 2 => if z = 1 then weight s p else 0) ∘ (fun f : Word → Fin 2 => f p))
    exact continuous_of_discreteTopology.comp (continuous_apply p)
  have he : {f : Word → Fin 2 | cost s (selectWords f) ≤ b} =
      ⋂ F : Finset Word, {f | ∑ p ∈ F, val f p ≤ b} := by
    ext f
    have he' (p : Word) : (selectWords f).indicator (weight s) p = val f p := by
      by_cases h : f p = 1 <;> simp [Set.indicator,selectWords,val,h]
    simp only [mem_ofPred_eq,mem_iInter,cost,tsum_subtype,ENNReal.tsum_eq_iSup_sum,iSup_le_iff,he']
  rw [he]
  exact isClosed_iInter (fun F => isClosed_le (continuous_finsetSum _ (fun p _ => hval p)) continuous_const)

private theorem isClosed_hasAncestor (p : Word) :
    IsClosed {f : Word → Fin 2 | HasAncestor (selectWords f) p} := by
  classical
  obtain ⟨x,hx⟩ := cylinder_nonempty p
  let F := (Finset.range (p.1+1)).image (head x)
  have he : {f : Word → Fin 2 | HasAncestor (selectWords f) p} =
      ⋃ q ∈ F, {f : Word → Fin 2 | f q = 1} := by
    ext f
    change HasAncestor (selectWords f) p ↔ f ∈ ⋃ q ∈ F, {f : Word → Fin 2 | f q = 1}
    simp only [mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨q,hf,hl,hsub⟩
      exact ⟨q,Finset.mem_image.mpr ⟨q.1,Finset.mem_range.mpr (by omega),head_eq (hsub hx)⟩,hf⟩
    · rintro ⟨q,hq,hf⟩
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
      have hn' : n ≤ p.1 := by have := Finset.mem_range.mp hn; omega
      exact ⟨head x n,hf,hn',cylinder_subset_of_overlap hn' (mem_head x n) hx⟩
  rw [he]
  exact isClosed_biUnion_finset (fun q _ => isClosed_eq (continuous_apply q) continuous_const)

private def CylinderOpen (U : Set Binary) : Prop :=
  ∀ x ∈ U, ∃ p : Word, x ∈ cylinder p ∧ cylinder p ⊆ U

private theorem cylinderOpen_coveredUnion (C : Set Word) : CylinderOpen (coveredUnion C) := by
  intro x hx
  obtain ⟨p,hp⟩ := mem_iUnion.mp hx
  exact ⟨p.val,hp,subset_iUnion (fun q : C => cylinder q.val) p⟩

private theorem cylinderOpen_union {U V : Set Binary} (hU : CylinderOpen U) (hV : CylinderOpen V) :
    CylinderOpen (U∪V) := by
  rintro x (h | h)
  · obtain ⟨p,hxp,hp⟩ := hU x h
    exact ⟨p,hxp,hp.trans subset_union_left⟩
  · obtain ⟨p,hxp,hp⟩ := hV x h
    exact ⟨p,hxp,hp.trans subset_union_right⟩

private theorem exists_cylinderOpen_cover_of_content_lt (s : ℝ) {A : Set Binary} {r : ℝ≥0∞}
    (h : content s A < r) :
    ∃ U : Set Binary, A ⊆ U ∧ CylinderOpen U ∧ content s U < r := by
  obtain ⟨C,hC,hlt⟩ := exists_cover_of_content_lt s h
  exact ⟨coveredUnion C,hC,cylinderOpen_coveredUnion C,(content_le_cost s Subset.rfl).trans_lt hlt⟩

private theorem content_iUnion_cylinderOpen (s : ℝ) (hs : s ≤ 1) (U : ℕ → Set Binary)
    (hU : Monotone U) (ho : ∀ n, CylinderOpen (U n)) :
    content s (⋃ n, U n) = ⨆ n, content s (U n) := by
  classical
  apply le_antisymm ?_ (iSup_le (fun n => content_mono s (subset_iUnion _ n)))
  apply le_of_not_gt
  intro hgt
  obtain ⟨b,hb,hb'⟩ := exists_between hgt
  let I := {p : Word // ∃ n, cylinder p ⊆ U n}
  let T (p : I) : Set (Word → Fin 2) := {f | HasAncestor (selectWords f) p.val}
  let S : Set (Word → Fin 2) := {f | cost s (selectWords f) ≤ b}
  have hS : IsCompact S := (isClosed_lowCost s b).isCompact
  have hF (F : Finset I) : (S ∩ ⋂ p ∈ F, T p).Nonempty := by
    have hAll (p : I) : ∃ n, cylinder p.val ⊆ U n := p.2
    choose n hn using hAll
    let N := F.sup n
    obtain ⟨C,hC,hcb⟩ := exists_cover_of_content_lt s ((le_iSup (fun j => content s (U j)) N).trans_lt hb)
    obtain ⟨D,_,hDC,hD⟩ := compress_finite s hs hC (F.image Subtype.val) (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact (hn q).trans (hU (Finset.le_sup hq)))
    let f : Word → Fin 2 := fun p => if p∈D then 1 else 0
    have hf : selectWords f = D := by ext p; by_cases hp : p∈D <;> simp [selectWords,f,hp]
    refine ⟨f,?_⟩
    simp only [mem_inter_iff,mem_iInter,S,T,mem_ofPred_eq,hf]
    exact ⟨(hDC.trans hcb.le),fun p hp => hD p.val (Finset.mem_image_of_mem _ hp)⟩
  obtain ⟨f,hf,hAll⟩ := hS.inter_iInter_nonempty T (fun p => isClosed_hasAncestor p.val) hF
  apply (not_le_of_gt hb')
  refine (content_le_cost s (C := selectWords f) ?_).trans hf
  intro x hx
  obtain ⟨n,hxn⟩ := mem_iUnion.mp hx
  obtain ⟨p,hp,hpU⟩ := ho n x hxn
  obtain ⟨q,hq,_,hsub⟩ := mem_iInter.mp hAll ⟨p,n,hpU⟩
  exact mem_iUnion.mpr ⟨⟨q,hq⟩,hsub hp⟩

private theorem content_ne_top (s : ℝ) (A : Set Binary) : content s A ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (content_le_one s A)

set_option maxHeartbeats 2000000 in
theorem content_iUnion (s : ℝ) (hs : s ≤ 1) (A : ℕ → Set Binary) (hA : Monotone A) :
    content s (⋃ n, A n) = ⨆ n, content s (A n) := by
  classical
  apply le_antisymm ?_ (iSup_le (fun n => content_mono s (subset_iUnion _ n)))
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ (n : ℕ) : ℝ≥0 := ε * (2:ℝ≥0)⁻¹^(n+1)
  have hdpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hbase : δ 0 + δ 0 = ε := by
    dsimp [δ]
    rw [pow_one, ← mul_add]
    norm_num
  have hδ (n : ℕ) : δ (n+1) + δ (n+1) = δ n := by
    change ε * (2:ℝ≥0)⁻¹^(n+1+1) + ε * (2:ℝ≥0)⁻¹^(n+1+1) = ε * (2:ℝ≥0)⁻¹^(n+1)
    rw [pow_succ, ← mul_assoc, ← mul_add]
    norm_num
  have hδ' (n : ℕ) : (δ (n+1):ℝ≥0∞) + (δ (n+1):ℝ≥0∞) = δ n := by exact_mod_cast hδ n
  have hδne (n : ℕ) : (δ n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (hdpos n).ne'
  choose O hsub ho hl using fun n => exists_cylinderOpen_cover_of_content_lt s
    (ENNReal.lt_add_right (content_ne_top s (A n)) (hδne n))
  let U : ℕ → Set Binary := Nat.rec (O 0) (fun n S => S ∪ O (n+1))
  have hU (n : ℕ) : A n ⊆ U n := by
    cases n with
    | zero => exact hsub 0
    | succ n => exact (hsub (n+1)).trans subset_union_right
  have hUo (n : ℕ) : CylinderOpen (U n) := by
    induction n with
    | zero => exact ho 0
    | succ n ih => exact cylinderOpen_union ih (ho (n+1))
  have hUm : Monotone U := monotone_nat_of_le_succ (fun _ => subset_union_left)
  have hu (n : ℕ) : content s (U n) + δ n ≤ content s (A n) + ε := by
    induction n with
    | zero =>
      have b : (δ 0:ℝ≥0∞) + (δ 0:ℝ≥0∞) = ε := by exact_mod_cast hbase
      calc
        content s (U 0) + δ 0 ≤ content s (A 0) + δ 0 + δ 0 :=
          add_le_add_left (hl 0).le _
        _ = content s (A 0) + ε := by rw [add_assoc,b]
    | succ n ih =>
      have hAn : A n ⊆ U n ∩ O (n+1) :=
        subset_inter (hU n) ((hA (Nat.le_succ n)).trans (hsub (n+1)))
      have hUn : content s (U (n+1)) + content s (A n) ≤ content s (U n) + content s (O (n+1)) :=
        (add_le_add_right (content_mono s hAn) _).trans (content_union_inter_le s _ _)
      apply (ENNReal.add_le_add_iff_right (content_ne_top s (A n))).mp
      calc
         content s (U (n+1)) + δ (n+1) + content s (A n) =
             content s (U (n+1)) + content s (A n) + δ (n+1) := by ac_rfl
         _ ≤ content s (U n) + content s (O (n+1)) + δ (n+1) := add_le_add_left hUn _
         _ ≤ content s (U n) + (content s (A (n+1)) + δ (n+1)) + δ (n+1) :=
           add_le_add_left (add_le_add_right (hl (n+1)).le _) _
         _ = content s (U n) + δ n + content s (A (n+1)) := by rw [← hδ' n]; ac_rfl
         _ ≤ content s (A n) + ε + content s (A (n+1)) := add_le_add_left ih _
         _ = content s (A (n+1)) + ε + content s (A n) := by ac_rfl
  calc
    content s (⋃ n, A n) ≤ content s (⋃ n, U n) :=
      content_mono s (iUnion_mono hU)
    _ = ⨆ n, content s (U n) := content_iUnion_cylinderOpen s hs U hUm hUo
    _ ≤ (⨆ n, content s (A n)) + ε := by
      apply iSup_le
      intro n
      exact (le_add_of_nonneg_right zero_le).trans ((hu n).trans
        (add_le_add_left (le_iSup (fun n => content s (A n)) n) _))

private abbrev Layer (n : ℕ) := Fin n → Fin 2

private def cell (n : ℕ) (u : Layer n) : Set Binary := cylinder ⟨n,u⟩

private theorem cell_zero (u : Layer 0) : cell 0 u = univ := by
  ext x
  simp only [cell,cylinder,mem_ofPred_eq,mem_univ,iff_true]
  intro i
  exact i.elim0

private theorem cell_snoc_subset {n : ℕ} (u : Layer n) (b : Fin 2) :
    cell (n+1) (Fin.snoc u b) ⊆ cell n u := by
  intro x hx i
  simpa only [Fin.val_castSucc,Fin.snoc_castSucc] using hx i.castSucc

private theorem cell_split {n : ℕ} (u : Layer n) :
    cell n u = cell (n+1) (Fin.snoc u 0) ∪ cell (n+1) (Fin.snoc u 1) := by
  apply Subset.antisymm ?_ (union_subset (cell_snoc_subset u 0) (cell_snoc_subset u 1))
  intro x hx
  have hb : x n = 0 ∨ x n = 1 := by rcases x n with ⟨d,hd⟩; interval_cases d <;> simp
  have aux (b : Fin 2) (h : x n = b) : x∈cell (n+1) (Fin.snoc u b) := by
    change ∀ i : Fin (n+1), _
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.val_last,Fin.snoc_last] using h
    · simpa only [Fin.val_castSucc,Fin.snoc_castSucc] using hx j
  exact hb.elim (fun h => Or.inl (aux 0 h)) (fun h => Or.inr (aux 1 h))

private def cellContent (s : ℝ) (K : Set Binary) (n : ℕ) (u : Layer n) : ℝ≥0∞ :=
  content s (K ∩ cell n u)

private theorem cellContent_split (s : ℝ) (K : Set Binary) {n : ℕ} (u : Layer n) :
    cellContent s K n u ≤
      cellContent s K (n+1) (Fin.snoc u 0) + cellContent s K (n+1) (Fin.snoc u 1) := by
  unfold cellContent
  rw [cell_split u, inter_union_distrib_left]
  exact (le_add_of_nonneg_right zero_le).trans (content_union_inter_le s _ _)

private def flow (s : ℝ) (K : Set Binary) : (n : ℕ) → Layer n → ℝ≥0∞
  | 0, _ => content s K
  | n+1, u =>
    let p := Fin.init u
    let left := min (flow s K n p) (cellContent s K (n+1) (Fin.snoc p 0))
    if u (Fin.last n) = 0 then left else flow s K n p - left

private theorem flow_snoc_zero (s : ℝ) (K : Set Binary) {n : ℕ} (u : Layer n) :
    flow s K (n+1) (Fin.snoc u 0) = min (flow s K n u) (cellContent s K (n+1) (Fin.snoc u 0)) := by
  simp only [flow,Fin.init_snoc,Fin.snoc_last,ite_true]

private theorem flow_snoc_one (s : ℝ) (K : Set Binary) {n : ℕ} (u : Layer n) :
    flow s K (n+1) (Fin.snoc u 1) = flow s K n u - min (flow s K n u) (cellContent s K (n+1) (Fin.snoc u 0)) := by
  rw [flow,Fin.init_snoc,Fin.snoc_last,if_neg (by decide : (1 : Fin 2) ≠ 0)]

private theorem flow_split (s : ℝ) (K : Set Binary) {n : ℕ} (u : Layer n) :
    flow s K (n+1) (Fin.snoc u 0) + flow s K (n+1) (Fin.snoc u 1) = flow s K n u := by
  rw [flow_snoc_zero,flow_snoc_one]
  exact add_tsub_cancel_of_le (min_le_left _ _)

private theorem flow_le_cellContent (s : ℝ) (K : Set Binary) (n : ℕ) (u : Layer n) :
    flow s K n u ≤ cellContent s K n u := by
  induction n with
  | zero => simp [flow,cellContent,cell_zero]
  | succ n ih =>
    let p := Fin.init u
    have he : u = Fin.snoc p (u (Fin.last n)) := (Fin.snoc_init_self u).symm
    have hb : u (Fin.last n) = 0 ∨ u (Fin.last n) = 1 := by
      rcases u (Fin.last n) with ⟨d,hd⟩
      interval_cases d <;> simp
    rcases hb with h | h
    · rw [show u = Fin.snoc p 0 from he.trans (by rw [h]), flow_snoc_zero]
      exact min_le_right _ _
    · rw [show u = Fin.snoc p 1 from he.trans (by rw [h]), flow_snoc_one]
      rcases le_total (flow s K n p) (cellContent s K (n+1) (Fin.snoc p 0)) with H | H
      · rw [min_eq_left H,tsub_self]
        exact zero_le
      · rw [min_eq_right H]
        exact tsub_le_iff_right.mpr ((ih p).trans ((cellContent_split s K p).trans_eq (add_comm _ _)))

private theorem cellContent_le_weight (s : ℝ) (K : Set Binary) (n : ℕ) (u : Layer n) :
    cellContent s K n u ≤ weight s ⟨n,u⟩ := by
  have h : Covered (K ∩ cell n u) {⟨n,u⟩} := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨⟨n,u⟩,rfl⟩,hx.2⟩
  exact (content_le_cost s h).trans_eq (by simp [cost])

private theorem sum_snoc {n : ℕ} (f : Layer (n+1) → ℝ≥0∞) :
    ∑ u, f u = ∑ p, (f (Fin.snoc p 0) + f (Fin.snoc p 1)) := by
  let e : (Layer n × Fin 2) ≃ Layer (n+1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Fin 2))
  calc
    ∑ u, f u = ∑ p : Layer n × Fin 2, f (Fin.snoc p.1 p.2) :=
      (Fintype.sum_equiv e (fun p => f (Fin.snoc p.1 p.2)) f (fun _ => rfl)).symm
    _ = _ := by simp only [Fintype.sum_prod_type,Fin.sum_univ_two]

private theorem sum_flow (s : ℝ) (K : Set Binary) (n : ℕ) :
    ∑ u, flow s K n u = content s K := by
  induction n with
  | zero =>
    let : Unique (Layer 0) := ⟨⟨fun i => i.elim0⟩, fun _ => funext fun i => i.elim0⟩
    simp [flow]
  | succ n ih => simpa only [sum_snoc,flow_split] using ih

private theorem child_subset_iff {n : ℕ} {p : Word} (hn : p.1 ≤ n) (u : Layer n) (b : Fin 2) :
    cell (n+1) (Fin.snoc u b) ⊆ cylinder p ↔ cell n u ⊆ cylinder p := by
  refine ⟨fun h => ?_, fun h => (cell_snoc_subset u b).trans h⟩
  obtain ⟨x,hx⟩ := cylinder_nonempty ⟨n+1,Fin.snoc u b⟩
  exact cylinder_subset_of_overlap hn (h hx) (cell_snoc_subset u b hx)

open Classical in
private theorem sum_flow_prefix (s : ℝ) (K : Set Binary) (p : Word) (n : ℕ) (hn : p.1 ≤ n) :
    (∑ u : Layer n, if cell n u ⊆ cylinder p then flow s K n u else 0) = flow s K p.1 p.2 := by
  classical
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    have he (u : Layer p.1) : cell p.1 u ⊆ cylinder p ↔ u = p.2 := by
      constructor
      · intro h
        obtain ⟨x,hx⟩ := cylinder_nonempty ⟨p.1,u⟩
        have he := eq_of_overlap_of_length_eq hx (h hx) rfl
        cases p
        cases he
        rfl
      · rintro rfl
        exact Subset.rfl
    simp [he]
  | succ d ih =>
    rw [Nat.add_succ, sum_snoc]
    have hw : p.1 ≤ p.1+d := Nat.le_add_right _ _
    simp only [child_subset_iff hw]
    calc
      _ = ∑ u : Layer (p.1+d), if cell (p.1+d) u ⊆ cylinder p then flow s K (p.1+d) u else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        split <;> simp_all [flow_split]
      _ = _ := ih hw

private theorem nonempty_of_content_pos (s : ℝ) (K : Set Binary) (hK : 0 < content s K) :
    K.Nonempty := by
  by_contra! h
  rw [h, content_empty] at hK
  exact (lt_irrefl _ hK)

private theorem exists_depth_prob (s : ℝ) (K : Set Binary) (hK : 0 < content s K) (n : ℕ) :
    ∃ μ : ProbabilityMeasure K, ∀ p : Word, p.1 ≤ n →
      (μ : Measure K) (Subtype.val ⁻¹' cylinder p) ≤ weight s p / content s K := by
  classical
  obtain ⟨x0,hx0⟩ := nonempty_of_content_pos s K hK
  let x (u : Layer n) : K :=
    if h : (K ∩ cell n u).Nonempty then ⟨h.choose,h.choose_spec.1⟩ else ⟨x0,hx0⟩
  have hx (u : Layer n) (hu : (K ∩ cell n u).Nonempty) : (x u).val ∈ cell n u := by
    simpa only [x,dif_pos hu] using hu.choose_spec.2
  have hz (u : Layer n) (hu : ¬ (K ∩ cell n u).Nonempty) : flow s K n u = 0 := by
    refine le_antisymm ((flow_le_cellContent s K n u).trans_eq ?_) zero_le
    simp only [cellContent,Set.not_nonempty_iff_eq_empty.mp hu,content_empty]
  let w (u : Layer n) := flow s K n u / content s K
  have hw : ∑ u, w u = 1 := by
    simp only [w,div_eq_mul_inv]
    rw [← Finset.sum_mul,sum_flow,← div_eq_mul_inv,ENNReal.div_self hK.ne' (content_ne_top s K)]
  let P := (PMF.ofFintype w hw).toMeasure
  have hxm : Measurable x := measurable_of_countable x
  let μ : ProbabilityMeasure K :=
    ⟨P.map x, Measure.isProbabilityMeasure_map hxm.aemeasurable⟩
  refine ⟨μ,fun p hp => ?_⟩
  change (P.map x) (Subtype.val ⁻¹' cylinder p) ≤ _
  rw [Measure.map_apply hxm ((isClopen_cylinder p).isClosed.measurableSet.preimage measurable_subtype_coe)]
  change (PMF.ofFintype w hw).toMeasure _ ≤ _
  rw [PMF.toMeasure_apply_eq_tsum,tsum_fintype]
  calc
    _ ≤ ∑ u : Layer n, if cell n u ⊆ cylinder p then w u else 0 := by
      apply Finset.sum_le_sum
      intro u _
      rw [Set.indicator_apply,PMF.ofFintype_apply]
      by_cases he : (x u).val ∈ cylinder p
      · by_cases hnon : (K ∩ cell n u).Nonempty
        · have h : cell n u ⊆ cylinder p := cylinder_subset_of_overlap hp he (hx u hnon)
          simp [he,h]
        · simp [he,w,hz u hnon]
      · simp [he]
    _ = flow s K p.1 p.2 / content s K := by
      rw [show (∑ u : Layer n, if cell n u ⊆ cylinder p then w u else 0) =
          (∑ u : Layer n, if cell n u ⊆ cylinder p then flow s K n u else 0) *
            (content s K)⁻¹ from ?_,sum_flow_prefix s K p n hp, div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      split <;> simp [w,div_eq_mul_inv, *]
    _ ≤ weight s p / content s K := ENNReal.div_le_div_right
      ((flow_le_cellContent s K p.1 p.2).trans (cellContent_le_weight s K p.1 p.2)) _

/-- Construct a probability measure with cylinder mass bounded by normalized cylinder content. -/
theorem exists_cylinder_probability (s : ℝ) {K : Set Binary} (hK : IsCompact K)
    (hpos : 0 < content s K) : ∃ μ : Measure Binary, IsProbabilityMeasure μ ∧ μ K = 1 ∧
      ∀ p : Word, μ (cylinder p) ≤ weight s p / content s K := by
  classical
  let : MetricSpace Binary := PiNat.metricSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T (p : Word) : Set (ProbabilityMeasure K) :=
    {μ | (μ : Measure K) (Subtype.val ⁻¹' cylinder p) ≤ weight s p / content s K}
  have hclosed (p : Word) : IsClosed (T p) := by
    have hcont : Continuous fun μ : ProbabilityMeasure K => μ (Subtype.val ⁻¹' cylinder p) := by
      rw [continuous_iff_continuousAt]
      intro μ
      exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto tendsto_id
        ((isClopen_cylinder p).preimage continuous_subtype_val)
    have hcont' := ENNReal.continuous_coe.comp hcont
    exact isClosed_le (by simpa only [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hcont') continuous_const
  have hfin (F : Finset Word) : ((univ : Set (ProbabilityMeasure K)) ∩ ⋂ p∈F, T p).Nonempty := by
    obtain ⟨μ,hμ⟩ := exists_depth_prob s K hpos (F.sup Sigma.fst)
    exact ⟨μ,mem_univ _,mem_iInter.mpr (fun p => mem_iInter.mpr (fun hp => hμ p (Finset.le_sup hp)))⟩
  obtain ⟨μ,_,hμ⟩ := isCompact_univ.inter_iInter_nonempty T hclosed hfin
  let ν := (μ : Measure K).map Subtype.val
  refine ⟨ν,Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable,?_,?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet]
    have he : Subtype.val ⁻¹' K = (univ : Set K) := Set.eq_univ_iff_forall.mpr (fun y => y.2)
    rw [he,measure_univ]
  · intro p
    rw [Measure.map_apply measurable_subtype_coe (isClopen_cylinder p).isClosed.measurableSet]
    exact mem_iInter.mp hμ p

end EdgarMillerDyadic

namespace EdgarMiller

private theorem unit_slice_dimH (R : Subring ℝ) :
    dimH ((R : Set ℝ) ∩ Icc 0 1) = dimH (R : Set ℝ) := by
  let A : Set ℝ := (R : Set ℝ) ∩ Icc 0 1
  let shift (k : ℤ) (x : ℝ) := x + k
  have hcover : (R : Set ℝ) = ⋃ k : ℤ, shift k '' A := by
    ext x
    constructor
    · intro hx
      refine mem_iUnion.mpr ⟨⌊x⌋,x-(⌊x⌋:ℤ),⟨R.sub_mem hx (intCast_mem R _),?_,?_⟩,?_⟩
      · linarith [Int.floor_le x]
      · linarith [Int.lt_floor_add_one x]
      · exact Int.fract_add_floor x
    · intro hx
      obtain ⟨k,y,hy,rfl⟩ := mem_iUnion.mp hx
      exact R.add_mem hy.1 (intCast_mem R k)
  have hshift (k : ℤ) : Isometry (shift k) := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    simp [Real.dist_eq,shift]
  change dimH A = _
  rw [hcover,dimH_iUnion]
  simp only [fun k => (hshift k).dimH_image A,iSup_const]

theorem exists_binary_prob_of_dimH_pos {R : Subring ℝ} (hR : AnalyticSet (R : Set ℝ))
    (hdim : 0 < dimH (R : Set ℝ)) :
    ∃ (s : ℝ) (B : ℝ≥0∞) (K : Set EdgarMillerDyadic.Binary) (μ : Measure EdgarMillerDyadic.Binary),
      0 < s ∧ B ≠ ⊤ ∧ IsCompact K ∧
      K ⊆ Real.ofDigits ⁻¹' (R : Set ℝ) ∧ IsProbabilityMeasure μ ∧ μ K = 1 ∧
      ∀ p : EdgarMillerDyadic.Word, μ (EdgarMillerDyadic.cylinder p) ≤ B*EdgarMillerDyadic.weight s p := by
  let : MetricSpace EdgarMillerDyadic.Binary := PiNat.metricSpace
  let A : Set ℝ := (R : Set ℝ) ∩ Icc 0 1
  let S : Set EdgarMillerDyadic.Binary := Real.ofDigits (b:=2) ⁻¹' A
  have ha : AnalyticSet A := analytic_inter hR isClosed_Icc.analyticSet
  have hdimA : 0 < dimH A := by simpa only [A,unit_slice_dimH] using hdim
  have hsmin : (0 : ℝ≥0∞) < min (dimH A) 1 := lt_min hdimA zero_lt_one
  obtain ⟨s,hs,hsl⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hsmin
  have hs' : 0 < s := by exact_mod_cast hs
  have hsl' : (s:ℝ) ≤ 1 := by exact_mod_cast ((lt_min_iff.mp hsl).2.le)
  have hpos : 0 < EdgarMillerDyadic.content (s:ℝ) S :=
    EdgarMillerDyadic.content_preimage_pos inter_subset_right hs' (lt_min_iff.mp hsl).1
  have hS : AnalyticSet S := ha.preimage Real.continuous_ofDigits
  obtain ⟨d,hd,hds⟩ := exists_between hpos
  obtain ⟨K,hKS,hK,hdK⟩ := EdgarMillerCapacity.exists_compact_of_analytic
    (EdgarMillerDyadic.content (s:ℝ)) (EdgarMillerDyadic.content_mono _)
    (EdgarMillerDyadic.content_empty _) (fun F hF => EdgarMillerDyadic.content_iUnion _ hsl' F hF)
    (EdgarMillerDyadic.content_iInter_compact _) hS hds
  obtain ⟨μ,hμP,hμK,hμB⟩ := EdgarMillerDyadic.exists_cylinder_probability (s:ℝ) hK (hd.trans_le hdK)
  have hB := ENNReal.inv_ne_top.mpr (hd.trans_le hdK).ne'
  exact ⟨s,(EdgarMillerDyadic.content (s:ℝ) K)⁻¹,K,μ,by exact_mod_cast hs',
    hB,hK,hKS.trans (preimage_mono inter_subset_left),hμP,hμK,
    fun p => by simpa only [div_eq_mul_inv,mul_comm] using hμB p⟩

end EdgarMiller

namespace EdgarMillerDyadic

private def label : (n : ℕ) → Layer n → ℕ
  | 0, _ => 0
  | n+1, u => 2*label n (Fin.init u) + (u (Fin.last n)).val

private theorem label_injective (n : ℕ) : Function.Injective (label n) := by
  induction n with
  | zero =>
    intro u v _
    exact funext fun i => i.elim0
  | succ n ih =>
    intro u v h
    have hu := (u (Fin.last n)).isLt
    have hv := (v (Fin.last n)).isLt
    have h' : 2*label n (Fin.init u)+(u (Fin.last n)).val =
        2*label n (Fin.init v)+(v (Fin.last n)).val := h
    have he : Fin.init u = Fin.init v := ih (by omega)
    have hb : u (Fin.last n) = v (Fin.last n) := Fin.ext (by omega)
    calc
      u = Fin.snoc (Fin.init u) (u (Fin.last n)) := (Fin.snoc_init_self _).symm
      _ = Fin.snoc (Fin.init v) (v (Fin.last n)) := by rw [he,hb]
      _ = v := Fin.snoc_init_self _

private theorem label_head (x : Binary) (n : ℕ) :
    (label n (head x n).2 : ℝ) =
      (2:ℝ)^n * ∑ i ∈ Finset.range n, Real.ofDigitsTerm x i := by
  induction n with
  | zero => simp [label]
  | succ n ih =>
    change ((2*label n (head x n).2+(x n).val : ℕ) : ℝ) = _
    rw [Nat.cast_add,Nat.cast_mul,ih,Finset.sum_range_succ]
    simp only [Real.ofDigitsTerm,Nat.cast_ofNat]
    have h : (2:ℝ)^(n+1) ≠ 0 := by positivity
    field_simp
    rw [pow_succ]
    ring

private theorem label_interval (n : ℕ) (u : Layer n) {x : Binary} (hx : x ∈ cell n u) :
    (label n u : ℝ) ≤ (2:ℝ)^n * Real.ofDigits x ∧
    (2:ℝ)^n * Real.ofDigits x ≤ (label n u : ℝ)+1 := by
  have hh : (head x n).2 = u := by
    funext i
    exact hx i
  have he := label_head x n
  rw [hh] at he
  rw [Real.ofDigits_eq_sum_add_ofDigits x n, mul_add, ← he]
  have hpow : (2:ℝ)^n ≠ 0 := by positivity
  simp only [Nat.cast_ofNat]
  rw [← mul_assoc,mul_inv_cancel₀ hpow,one_mul]
  exact ⟨le_add_of_nonneg_right (Real.ofDigits_nonneg _),add_le_add_right (Real.ofDigits_le_one _) _⟩

open Classical in
private theorem count_ball_cells (n : ℕ) (c : ℝ) :
    let F := Finset.univ.filter (fun u : Layer n =>
      (cell n u ∩ Real.ofDigits ⁻¹' closedBall c ((2:ℝ)^n)⁻¹).Nonempty)
    F.card ≤ 4 := by
  classical
  intro F
  let L := F.image (label n)
  have hL (i : ℕ) (hi : i∈L) :
      (2:ℝ)^n*c-2 ≤ (i:ℝ) ∧ (i:ℝ) ≤ (2:ℝ)^n*c+1 := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨x,hx,hxb⟩ := (Finset.mem_filter.mp hu).2
    have ha := label_interval n u hx
    change Real.ofDigits x ∈ closedBall c ((2:ℝ)^n)⁻¹ at hxb
    rw [mem_closedBall,Real.dist_eq,abs_le] at hxb
    have hp : 0 < (2:ℝ)^n := by positivity
    have hmul0 := (le_div_iff₀ hp).mp (show c - Real.ofDigits x ≤ 1 / (2:ℝ)^n by
      rw [one_div]; linarith [hxb.1])
    have hmul1 := (le_div_iff₀ hp).mp (show Real.ofDigits x-c ≤ 1 / (2:ℝ)^n by
      rw [one_div]; exact hxb.2)
    constructor <;> nlinarith [ha.1,ha.2]
  have hcard : L.card = F.card := Finset.card_image_of_injective _ (label_injective n)
  rw [← hcard]
  by_cases hne : L.Nonempty
  · let j := L.min' hne
    have hj : j∈L := Finset.min'_mem _ _
    have hsub : L ⊆ Finset.Icc j (j+3) := by
      intro i hi
      rw [Finset.mem_Icc]
      refine ⟨Finset.min'_le _ _ hi,?_⟩
      exact_mod_cast (show (i:ℝ) ≤ (j:ℝ)+3 by linarith [(hL i hi).2,(hL j hj).1])
    exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    decide

theorem dyadic_ball_bound (μ : Measure Binary) (s : ℝ) (B : ℝ≥0∞)
    (hm : ∀ p : Word, μ (cylinder p) ≤ B * weight s p) (c : ℝ) (n : ℕ) :
    (μ.map Real.ofDigits) (closedEBall c (EdgarMillerEnergy.dyadic n)) ≤
      (4*B) * (EdgarMillerEnergy.dyadic n)^s := by
  classical
  let r := ((2:ℝ)^n)⁻¹
  have hr : ENNReal.ofReal r = EdgarMillerEnergy.dyadic n := by
    rw [EdgarMillerEnergy.dyadic, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.inv_pow]
    norm_num
  have hclosed : closedEBall c (EdgarMillerEnergy.dyadic n) = closedBall c r := by
    rw [← hr]
    ext x
    rw [mem_closedEBall,mem_closedBall,edist_dist,ENNReal.ofReal_le_ofReal_iff (by positivity)]
  rw [hclosed,Measure.map_apply Real.continuous_ofDigits.measurable isClosed_closedBall.measurableSet]
  let F := Finset.univ.filter (fun u : Layer n =>
    (cell n u ∩ Real.ofDigits ⁻¹' closedBall c r).Nonempty)
  have hF : F.card ≤ 4 := count_ball_cells n c
  have hcov : Real.ofDigits ⁻¹' closedBall c r ⊆ ⋃ u ∈ F, cell n u := by
    intro x hx
    let u := (head x n).2
    have hu : x ∈ cell n u := mem_head x n
    exact mem_iUnion.mpr ⟨u,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hu,hx⟩,hu⟩⟩
  refine (measure_mono hcov).trans ((measure_biUnion_finset_le F (cell n)).trans ?_)
  have hwt (u : Layer n) : weight s ⟨n,u⟩ = (EdgarMillerEnergy.dyadic n)^s := by
    rw [weight,EdgarMillerEnergy.dyadic,← ENNReal.rpow_natCast_mul,mul_comm]
  calc
    _ ≤ ∑ u ∈ F, B * (EdgarMillerEnergy.dyadic n)^s := by
      apply Finset.sum_le_sum
      intro u _
      change μ (cylinder ⟨n,u⟩) ≤ _
      rw [← hwt u]
      exact hm ⟨n,u⟩
    _ = (F.card:ℝ≥0∞) * (B * (EdgarMillerEnergy.dyadic n)^s) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 4 * (B * (EdgarMillerEnergy.dyadic n)^s) :=
      mul_le_mul' (by exact_mod_cast hF) le_rfl
    _ = _ := (mul_assoc _ _ _).symm

end EdgarMillerDyadic

/-- Edgar and Miller's analytic extension of their subring theorem.
See https://people.math.osu.edu/edgar.2/preprints/subring/subringpre.pdf. -/
theorem OMA.solution : type_of% @Erdos1154.erdos_1154.variants.analytic_ring := by
  intro R hR
  by_cases hdim : dimH (R : Set ℝ) = 0
  · exact Or.inr hdim
  · apply Or.inl
    obtain ⟨s,B,K,μ,hs,hB,hK,hKR,hμP,hμK,hμBall⟩ :=
      EdgarMiller.exists_binary_prob_of_dimH_pos hR (pos_iff_ne_zero.mpr hdim)
    let ν := μ.map Real.ofDigits
    have hνP : IsProbabilityMeasure ν :=
      Measure.isProbabilityMeasure_map Real.continuous_ofDigits.measurable.aemeasurable
    let C := Real.ofDigits '' K
    have hC : IsCompact C := hK.image Real.continuous_ofDigits
    have hCR : C ⊆ (R : Set ℝ) := image_subset_iff.mpr hKR
    have hνC : ν C = 1 := by
      apply le_antisymm ((measure_mono (subset_univ C)).trans_eq measure_univ)
      rw [Measure.map_apply Real.continuous_ofDigits.measurable hC.isClosed.measurableSet]
      exact hμK ▸ measure_mono (subset_preimage_image _ _)
    exact EdgarMiller.eq_top_of_frostman hR ν hC hCR hνC hs (ENNReal.mul_ne_top (by norm_num) hB)
      (EdgarMillerDyadic.dyadic_ball_bound μ s B hμBall)